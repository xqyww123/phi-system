(* library/syntax/procedure.ML
   Author: Qiyuan Xu

   The syntax parser for procedure specification.

It is invoked once there are anonymous values in the argument specification,
or once the return specification is not given as an explicit lambda abstraction about the return values.
For translation in argument specification, all anonymous values are replaces by a free variable
  generated automatically.
For return specification, it collects all semantic values having \<^typ>\<open>'a \<phi>arg\<close> in the spec,
  and wrap the spec by a lambda abstraction over the semantic values, using the pair encoding
  of multi-return-values (rn, ...\<^bold>, r2 \<^bold>, r1).
*)

signature PROCEDURE_SYNTAX = sig
(*
Translate a term X containing values V (including anonymous values) into (\<lambda>vs. X\<theta>),
  where vs is a tuple aggregating values V,
  \<theta> is a substitution mapping the ith value in V to the ith projection of vs.

Values of identical name are considered identical. Any anonymous value is considered unique.
*)

val package_values :
       string (*name of the lambda variable*)
        -> bool (*the order for scanning and collecting the values.
                  true for Right-to-Left; false for Left-to-Right.
                  Left-to-Right is the canonical order since \<open>Flip *-sequence to the canonical
                  order\<close> (2024-05-02), which made \<open>\<heavy_comma>\<close> right-associative and flipped the
                  machine semantics in lock-step; every live caller passes false, and the
                  \<phi>app lemma base of the primitive operations pins it.*)
        -> term list option (*values cache.
              If you run package_values by twice in the same context (of variables) and in the same scan order,
              this argument can be set to the return of the previous run to boost the performance.
              Set it to None by default*)
        -> term
        -> term (*values*) * term (*lambda abstraction*)

val package_values0 :
       string (*name of the lambda variable*)
        -> typ (*type of the return when the spec is 0*)
        -> bool (*the order for scanning and collecting the values.
                  true for Right-to-Left; false for Left-to-Right.
                  Left-to-Right is the canonical order since \<open>Flip *-sequence to the canonical
                  order\<close> (2024-05-02), which made \<open>\<heavy_comma>\<close> right-associative and flipped the
                  machine semantics in lock-step; every live caller passes false, and the
                  \<phi>app lemma base of the primitive operations pins it.*)
        -> term list option (*values cache.
              If you run package_values by twice in the same context (of variables) and in the same scan order,
              this argument can be set to the return of the previous run to boost the performance.
              Set it to None by default*)
        -> term
        -> term (*values*) * term (*lambda abstraction*)

val translate_arg : term -> term
val translate_ret : term -> term
(* Syntax translation during parse of the post-condition,
   roughly identical to (package_values "\<r>\<e>\<t>" false).
*)

val is_argT : typ -> bool
val dest_argT : typ -> typ
val mk_argT : typ -> typ
val dest_arg_prodT : typ -> typ * typ
val mk_arg_prodT   : typ * typ -> typ
val mk_arg_tupleT  : typ list -> typ
val mk_arg_tuple   : typ list -> term list -> term
val dest_arg_tuple : term -> term list
val map_argT  : (typ -> typ) -> typ -> typ

end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct

(*** Parser ***)

(*
Syntax translation during parsing of the pre-condition is simply replacing
all anonymous values by a name \<a>\<r>\<g>i for the ith value from left to right.
*)
(*Since Isabelle2025, a logical constant carrying mixfix syntax is parsed into a pre-term whose
  constant is wrapped by \<open>_type_constraint_\<close> (or \<open>_constrain\<close>) recording its source position.
  The head of an application is therefore not literally a \<^ML>\<open>Const\<close> any more, so the shapes
  below are recognized through such wrappers.*)
val head_const_name = Phi_Syntax_Constraint.head_const_name
val is_head_of = Phi_Syntax_Constraint.is_head

val is_phi_type_head = is_head_of [\<^const_name>\<open>\<phi>Type\<close>, \<^const_syntax>\<open>\<phi>Type\<close>]
val is_value_head    = is_head_of [\<^const_name>\<open>Val\<close>,  \<^const_syntax>\<open>Val\<close>,
                                   \<^const_name>\<open>Vals\<close>, \<^const_syntax>\<open>Vals\<close>]
val is_anonymous     = is_head_of [\<^const_name>\<open>anonymous\<close>, \<^const_syntax>\<open>anonymous\<close>]

(*the test comes before the shape analysis, so an \<^const>\<open>anonymous\<close> still carrying its positional
  wrapper is renamed as a whole instead of being descended into, which would leave the wrapper
  applied to the fresh \<^ML>\<open>Free\<close>*)
fun translate_arg' cnt s tm =
      if is_anonymous tm
      then (cnt, Symbol.bump_string s, Free ("\<a>\<r>\<g>" ^ s, dummyT))
      else translate_arg'' cnt s tm

and translate_arg'' cnt s (tm as C1 $ X $ (C2 $ V $ X2))
      = if is_phi_type_head C1 andalso is_value_head C2 andalso is_anonymous V
        then (cnt+1, s, C1 $ X $ (C2 $ Free ("\<a>\<r>\<g>" ^ (string_of_int (cnt+1)), dummyT) $ X2))
        else translate_arg_app cnt s tm
  | translate_arg'' cnt s (tm as _ $ _) = translate_arg_app cnt s tm
  | translate_arg'' cnt s (Abs (name,ty, X))
      = (case translate_arg' cnt s X of (cnt',s', X') =>
           (cnt', s', Abs (name,ty,X')))
  | translate_arg'' cnt s X = (cnt,s, X)

and translate_arg_app cnt s (A $ B)
      = (case translate_arg' cnt  s  A of (cnt',s', A') =>
         case translate_arg' cnt' s' B of (cnt'',s'', B') =>
          (cnt'', s'', A' $ B'))
  | translate_arg_app cnt s X = (cnt, s, X)
fun translate_arg X = #3 (translate_arg' 0 "\<a>\<r>\<g>_a" X)

(*kept in step with \<^ML>\<open>collect_vals\<close> about the object side of \<^const>\<open>\<phi>Type\<close>, and with
  \<^ML>\<open>translate_arg'\<close> about what counts as an \<^const>\<open>anonymous\<close>*)
fun need_translate_arg t =
      is_anonymous t orelse
     (case t of
        Abs (_, _, X) => need_translate_arg X
      | _ $ _ =>
         (case Phi_Syntax_Constraint.strip_comb_pos t
            of (h as Const _, [_, X]) =>
                 if is_phi_type_head h then need_translate_arg X else need_translate_app t
             | _ => need_translate_app t)
      | _ => false)

and need_translate_app (A $ B) = need_translate_arg A orelse need_translate_arg B
  | need_translate_app _ = false


fun is_argT (Type (\<^type_name>\<open>\<phi>arg\<close>, [_])) = true
  | is_argT _ = false
fun dest_argT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])) = T
  | dest_argT T = raise TYPE("Not a \<phi>arg type", [T], [])
fun mk_argT T = \<^Type>\<open>\<phi>arg \<open>T\<close>\<close>

fun dest_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [Type (\<^type_name>\<open>prod\<close>, [A, B])]))
      = (Type (\<^type_name>\<open>\<phi>arg\<close>, [A]), Type (\<^type_name>\<open>\<phi>arg\<close>, [B]))
  | dest_arg_prodT (Type ("dummy", [])) = (dummyT,dummyT)
  | dest_arg_prodT T = raise TYPE("Not a \<phi>arg type", [T], [])

fun mk_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T1]), Type (\<^type_name>\<open>\<phi>arg\<close>, [T2]))
      = Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_prodT (T1,T2)])
  | mk_arg_prodT (T1,T2) = raise TYPE("Not a \<phi>arg type", [T1,T2], [])

fun mk_arg_tupleT Ts = mk_argT (HOLogic.mk_tupleT (map dest_argT Ts))

fun map_argT f (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])) = Type (\<^type_name>\<open>\<phi>arg\<close>, [f T])
  | map_argT _ T = raise TYPE("Not a \<phi>arg type", [T], [])

fun mk_arg_tuple _ [] = \<^term>\<open>\<phi>V_none\<close>
  | mk_arg_tuple _ [tm] = tm
  | mk_arg_tuple (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])::tys) (tm::tms)
      = Const (\<^const_name>\<open>\<phi>V_pair\<close>, Type (\<^type_name>\<open>\<phi>arg\<close>, [fst (HOLogic.dest_prodT T)])
                                 --> Type (\<^type_name>\<open>\<phi>arg\<close>, [snd (HOLogic.dest_prodT T)])
                                 --> Type (\<^type_name>\<open>\<phi>arg\<close>, [T]))
          $ tm $ mk_arg_tuple tys tms
  | mk_arg_tuple tys tms = raise TYPE ("Not a \<phi>arg type", tys, tms)

fun dest_arg_tuple (Const (\<^const_name>\<open>\<phi>V_none\<close>, _)) = []
  | dest_arg_tuple (Const (\<^const_name>\<open>\<phi>V_pair\<close>, _) $ A $ B) = A :: dest_arg_tuple B
  | dest_arg_tuple X = [X]

(* fun mk_arg_prodT []  = \<^typ>\<open>unit \<phi>arg\<close>
  | mk_arg_prodT (Type ("dummy", []) :: _) = dummyT
  | mk_arg_prodT [T] = T
  | mk_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])::Ts) =
      (case mk_arg_prodT Ts of Type (\<^type_name>\<open>\<phi>arg\<close>, [Ts']) =>
          Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_arg_prodT (T,Ts')]))
  | mk_arg_prodT T = raise TYPE("bug #g4389h", T, []) *)

fun nth_project [_] 0 term = term
  | nth_project (ty::_::_) 0 term
      = Const (\<^const_name>\<open>\<phi>V_fst\<close>, ty --> fst (dest_arg_prodT ty)) $ term
  | nth_project (ty::tys::tyss) i term =
      nth_project (tys::tyss) (i-1) (Const (\<^const_name>\<open>\<phi>V_snd\<close>, ty --> tys) $ term)
  | nth_project _ _ _ = error "Internal bug #bq3 ni8op["


fun gen_collect_and_map R2L (*whether in an order from right to left or reversely*) =
let

(*The head of an application carrying mixfix syntax is wrapped in a positional constraint since
  Isabelle2025, so the heads below are recognized through \<^ML>\<open>Phi_Syntax_Constraint.strip_comb_pos\<close>
  rather than by a literal \<^ML>\<open>Const\<close> pattern.  The value terms themselves are stored and compared
  verbatim: positions are distinct per occurrence, and normalizing them would merge two occurrences
  of one value name into one entry, silently changing the arity of the procedure.  Types are
  computed through \<^ML>\<open>ex_fastype_of\<close>, which is where positions are made transparent.*)
fun collect_vals Vs t =
  if is_anonymous t then t::Vs
  else
  (case t of
     Free (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)) => insert (op = ) t Vs
   | Var (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)) => insert (op = ) t Vs
     (*a value whose type is genuinely ascribed as \<^typ>\<open>_ \<phi>arg\<close>, carrying no \<^const>\<open>Val\<close> head;
       a positional constraint can never take this shape*)
   | Const ("_type_constraint_", Type("fun", [Type(\<^type_name>\<open>\<phi>arg\<close>, _),_])) $ _
       => insert (op = ) t Vs
   | Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ _)
       => insert (op = ) t Vs
   | Abs (_,_,X) => collect_vals Vs X
   | _ =>
     (case Phi_Syntax_Constraint.strip_comb_pos t
        of (h as Const _, [_, X]) =>
             if is_phi_type_head h then collect_vals Vs X else collect_app Vs t
         | (h as Const _, [v]) =>
             if is_value_head h
             then (if is_anonymous v then v::Vs else insert (op = ) v Vs)
             else collect_app Vs t
         | _ => collect_app Vs t))

and collect_app Vs (X $ Y) =
      if R2L
      then collect_vals (collect_vals Vs X) Y
      else collect_vals (collect_vals Vs Y) X
  | collect_app Vs _ = Vs

(*\<^ML>\<open>collect_vals\<close> stores its entries verbatim, so an \<^const>\<open>anonymous\<close> in \<open>VS\<close> may still carry
  its positional wrapper.  The scan therefore has to recognize it the very same way \<^ML>\<open>collect_vals\<close>
  classified it; a literal \<^ML>\<open>Const\<close> pattern here would walk straight past the entry it just made.*)
fun jth_index_of_annoy j ans (v :: L)
      = if is_anonymous v
        then (if j = 0 then ans else jth_index_of_annoy (j-1) (ans+1) L)
        else jth_index_of_annoy j (ans+1) L
  | jth_index_of_annoy _ _ [] = raise Fail "Procedure_Syntax: Insufficient values"

fun mk_projection Tys VS i v =
  let val ret = find_index (fn x => x = v) VS
   in if ret = ~1 then v
      else nth_project Tys ret (Bound i)
  end

fun map_ret Tys i VS (j, t) =
      if is_anonymous t
      then (j + 1, nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
      else map_ret' Tys i VS (j, t)

and map_ret' Tys i VS (j, v as Const ("_type_constraint_",
                                      Type("fun", [Type(\<^type_name>\<open>\<phi>arg\<close>, _),_])) $ _)
      = (j, mk_projection Tys VS i v)
  | map_ret' Tys i VS (j, v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ _))
      = (j, mk_projection Tys VS i v)
  | map_ret' Tys i VS (j, v as Free (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)))
      = (j, mk_projection Tys VS i v)
  | map_ret' Tys i VS (j, v as Var (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)))
      = (j, mk_projection Tys VS i v)
  | map_ret' Tys i VS (j, Abs (name,ty,X))
      = (case map_ret Tys (i+1) VS (j, X) of (j',X') => (j', Abs (name, ty,X')))
  | map_ret' _ i _ (j,Bound a) = (j, Bound (if i <= a then a+1 else a))
    (*heads are recognized through their positional wrapper, but the term is rebuilt from the
      ORIGINAL head and arguments, so the wrapper -- and the source markup it carries -- survives*)
  | map_ret' Tys i VS (j, t) =
     (case Phi_Syntax_Constraint.strip_comb_pos t
        of (h as Const _, [_, _]) =>
             if is_phi_type_head h
             then (case t of HA $ B =>
                     (case map_ret Tys i VS (j, B) of (j',B') => (j', HA $ B'))
                   | _ => map_app Tys i VS (j, t))
             else map_app Tys i VS (j, t)
         | (h as Const _, [v]) =>
             if is_value_head h
             then (case t of H $ _ =>
                     if is_anonymous v
                     then (j + 1, H $ nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
                     else (j, H $ mk_projection Tys VS i v)
                   | _ => map_app Tys i VS (j, t))
             else map_app Tys i VS (j, t)
         | _ => map_app Tys i VS (j, t))

and map_app Tys i VS (j, X $ Y)
      = if R2L
        then (case map_ret Tys i VS (j,Y) of (j',Y') =>
                (case map_ret Tys i VS (j',X) of (j'',X') => (j'', X' $ Y')))
        else (case map_ret Tys i VS (j,X) of (j',X') =>
                (case map_ret Tys i VS (j',Y) of (j'',Y') => (j'', X' $ Y')))
  | map_app _ _ _ jVX = jVX
in (collect_vals, map_ret) end

val dummyT_sem = Type (\<^type_name>\<open>\<phi>arg\<close>, [dummyT])
(*this is the one place where positions are made transparent: the type of a value whose head still
  carries a positional constraint would otherwise be the encoded position rather than \<^typ>\<open>dummy\<close>,
  so the fallback below would not fire and \<^ML>\<open>mk_arg_prodT\<close> would reject it.  The value terms
  themselves are left untouched -- see the note at \<^ML>\<open>collect_vals\<close>.*)
fun ex_fastype_of TM =
  let val T = fastype_of (Phi_Syntax_Constraint.strip_pos_deep (Term_Position.strip_positions TM))
   in if T = dummyT then dummyT_sem else T end
  handle TERM _ => dummyT_sem

fun package_values name _ (SOME []) term =
      (\<^term>\<open>\<phi>V_none\<close>, Abs(name, \<^typ>\<open>unit \<phi>arg\<close>, term))
  | package_values name R2L Vs0 term =
  let
    val (collect_vals, map_ret) = gen_collect_and_map R2L
    val Vs = case Vs0 of SOME Vs => Vs | NONE => collect_vals [] term
    val Tys = fold_rev (fn T => (fn [] => [T]
                                  | L as T'::_ => mk_arg_prodT (T,T') :: L))
              (map ex_fastype_of Vs) []
    val T = if null Tys then \<^typ>\<open>unit \<phi>arg\<close> else hd Tys
  in (mk_arg_tuple Tys Vs, Abs(name, T, if null Tys then term else #2(map_ret Tys 0 Vs (0,term))))
  end

fun package_values0 name zero_ty _ _ (term as Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, _))
      = (\<^Const>\<open>\<phi>arg zero_ty\<close> $ \<^Const>\<open>unreachable zero_ty\<close>, Abs (name, \<^Type>\<open>\<phi>arg zero_ty\<close>, term))
  | package_values0 name _ R2L Vs0 term = package_values name R2L Vs0 term


fun translate_ret' (term as (Abs _)) = term
  | translate_ret' (term as (Var _)) = term
  | translate_ret' (term as (Free _)) = term
  | translate_ret' (tm as Const (\<^const_abbrev>\<open>Void\<close>, _))
      = Abs ("", \<^typ>\<open>unit \<phi>arg\<close>, tm)
  | translate_ret' (tm as Const (\<^const_name>\<open>one_class.one\<close>, _))
      = Abs ("", \<^typ>\<open>unit \<phi>arg\<close>, tm)
  | translate_ret' (term as (Const _)) = term
  | translate_ret' (Const ("_constrain", ty) $ X $ Y)
      =(case translate_ret' X of Abs (N,T,B) => Abs (N, T, Const ("_constrain", ty) $ B $ Y)
                              | B => Const ("_constrain", ty) $ B $ Y)
  | translate_ret' (Const ("_type_constraint_", ty) $ X)
      =(case translate_ret' X of Abs (N,T,B) => Abs (N, T, Const ("_type_constraint_", ty) $ B)
                              | B => Const ("_type_constraint_", ty) $ B)
  | translate_ret' (Const ("_constrainAbs", ty) $ X $ Y)
      =(case translate_ret' X of Abs (N,T,B) => Abs (N, T, Const ("_constrainAbs", ty) $ B $ Y)
                              | B => Const ("_constrainAbs", ty) $ B $ Y)
  | translate_ret' term =
      snd (package_values0 "\<r>\<e>\<t>" \<^typ>\<open>dummy\<close> false NONE term)


(* fun translate_num term =
      fold_aterms (
          fn Const (\<^const_name>\<open>val_syntax\<close>, _) => (fn n => n + 1)
           | _ => I) term 0 *)

fun need_translate_ret (Abs (_,_,_)) = false
  | need_translate_ret (Free _) = false
  | need_translate_ret (Var  _) = false
  | need_translate_ret (Const (\<^const_abbrev>\<open>Void\<close>, _)) = true
  | need_translate_ret (Const (\<^const_name>\<open>one_class.one\<close>, _)) = true
  | need_translate_ret (Const  _) = false
  | need_translate_ret (Const ("_constrain", _) $ X $ _)
      = need_translate_ret X
  | need_translate_ret (Const ("_type_constraint_", _) $ X)
      = need_translate_ret X
  | need_translate_ret (Const ("_constrainAbs", _) $ X $ _)
      = need_translate_ret X
  | need_translate_ret _ = true

fun translate_ret X = if need_translate_ret X then translate_ret' X else X

(*
The parse translation is invoked once there is an anonymous value in the argument specification,
or once the return specification is not a lambda abstraction nor an atom (a variable or a constant)
*)
(*A parse translation is dispatched on the head of the application, and \<open>ast_to_term\<close> recognizes a
  head only when it is a bare \<^ML>\<open>Ast.Constant\<close>.  Since Isabelle2025 the head of an application is
  wrapped by \<open>_constrain\<close> recording the positions of the mixfix literals whenever it is a LOGICAL
  constant carrying mixfix syntax, and the dispatch does not see through that wrapper: the whole
  application falls to the plain-application case, the arguments are applied outside, and the
  translations below are reached with an EMPTY argument list.

  The ast translations here do not repair that after the fact -- they PRE-EMPT it.  \<open>asts_of\<close>
  consults an ast translation INSTEAD OF building the wrapped head, so with one registered the
  wrapper is never constructed at all.

  The conventional remedy is to key the parse translation on a syntax constant, which is never
  wrapped -- that is how every parse translation in the Isabelle distribution is written, and how
  \<open>_Mem_synt\<close> in \<^file>\<open>~~/../phi-system/Phi_Semantics/PhiSem_Mem_C.thy\<close> is written.  It is deliberately
  not done here: \<^const>\<open>\<phi>Procedure\<close> and \<^const>\<open>\<phi>Procedure_no_exception\<close> carry four notations
  between them, two of which also print, and EVERY one of them routes to this same key -- moving
  one spelling alone would leave the others silently untranslated.  Weighed against that, the gain
  is small; see the note on markup below.

  What the wrapper carries, and what is therefore lost: a report of the constant's instantiated type
  at each mixfix literal, which Isabelle2025 shows on hover.  That report is lost under the syntax
  constant remedy just the same, since a syntax constant has no wrapper either; keeping it would
  mean giving up the parse translation altogether and matching through \<open>_type_constraint_\<close> in a term
  check below type inference.  The entity markup -- the constant's name, and its ctrl-click target --
  is reported by \<open>asts_of\<close> unconditionally, before the dispatch, and is unaffected either way.*)
val _ = Theory.setup (Sign.parse_ast_translation (
    map (fn c => (c, fn _ => fn args => Ast.mk_appl (Ast.Constant c) args))
        [\<^const_syntax>\<open>\<phi>Procedure\<close>, \<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>]))

val _ = Theory.setup (Sign.parse_translation [
    (\<^const_syntax>\<open>\<phi>Procedure\<close>, (fn _ => fn [f,Arg,Ret,E] =>
        Const (\<^const_name>\<open>\<phi>Procedure\<close>, dummyT) $ f
          $ (if need_translate_arg Arg then translate_arg Arg else Arg)
          $ (if need_translate_ret Ret then translate_ret' Ret else Ret)
          $ E)),
    (\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, (fn _ => fn [f,Arg,Ret] =>
        Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, dummyT) $ f
          $ (if need_translate_arg Arg then translate_arg Arg else Arg)
          $ (if need_translate_ret Ret then translate_ret' Ret else Ret)))
])


end