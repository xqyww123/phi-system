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

val val_T : typ
val val_list_T : typ

val package_values :
       string (*name of the lambda variable*)
        -> bool (*the order for scanning and collecting the values.
                  true for Right-to-Left (the canonical order);
                  false for Left-to-Right*)
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
                  true for Right-to-Left (the canonical order);
                  false for Left-to-Right*)
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
(*val dest_arg_prodT : typ -> typ * typ
val mk_arg_prodT   : typ * typ -> typ
val mk_arg_listT  : typ list -> typ*)
val mk_arg_list   : typ list -> term list -> term
val mk_arg_list'  : term list -> term
val dest_arg_list : term -> term list
val map_argT  : (typ -> typ) -> typ -> typ


datatype quantify_mode = No_Quantify | HOL_Quantify
datatype parameterize_proc = No_Parameterize | Tuple_Pack | Lambda_Apps

val set_proc_parse_mode : quantify_mode * parameterize_proc -> Context.generic -> Context.generic
val restore_proc_parse_mode : Context.generic -> Context.generic -> Context.generic
val translate_proc_arg : Context.generic -> term -> term

end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct

(*** Parser ***)

fun is_argT (Type (\<^type_name>\<open>\<phi>arg\<close>, [_])) = true
  | is_argT _ = false
fun dest_argT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])) = T
  | dest_argT T = raise TYPE("Not a \<phi>arg type", [T], [])
fun mk_argT T = \<^Type>\<open>\<phi>arg \<open>T\<close>\<close>

val val_list_T = \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close>
val val_T = \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close>

(*
fun dest_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [Type (\<^type_name>\<open>prod\<close>, [A, B])]))
      = (Type (\<^type_name>\<open>\<phi>arg\<close>, [A]), Type (\<^type_name>\<open>\<phi>arg\<close>, [B]))
  | dest_arg_prodT (Type ("dummy", [])) = (dummyT,dummyT)
  | dest_arg_prodT T = raise TYPE("Not a \<phi>arg type", [T], [])
*)

fun mk_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T1]), Type (\<^type_name>\<open>\<phi>arg\<close>, [T2]))
      = Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_prodT (T1,T2)])
  | mk_arg_prodT (T1,T2) = raise TYPE("Not a \<phi>arg type", [T1,T2], [])

(*
fun mk_arg_listT Ts = mk_argT (HOLogic.mk_tupleT (map dest_argT Ts))
*)

fun map_argT f (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])) = Type (\<^type_name>\<open>\<phi>arg\<close>, [f T])
  | map_argT _ T = raise TYPE("Not a \<phi>arg type", [T], [])

fun mk_arg_list' [] = \<^Const>\<open>\<phi>V_nil\<close>
  | mk_arg_list' [tm] = tm
  | mk_arg_list' (tm::tms)
      = \<^Const>\<open>\<phi>V_cons\<close> $ tm $ mk_arg_list' tms

fun mk_arg_list [] = \<^Const>\<open>\<phi>V_nil\<close>
  | mk_arg_list (tm::tms)
      = \<^Const>\<open>\<phi>V_cons\<close> $ tm $ mk_arg_list tms
  | mk_arg_list tms = raise TYPE ("Not a \<phi>arg type", [], tms)

fun dest_arg_list (Const (\<^const_name>\<open>\<phi>V_nil\<close>, _)) = []
  | dest_arg_list (Const (\<^const_name>\<open>\<phi>V_cons\<close>, _) $ A $ B) = A :: dest_arg_list B
  | dest_arg_list X = [X]


(*
Syntax translation during parsing of the pre-condition is simply replacing
all anonymous values by a name \<a>\<r>\<g>i for the ith value from left to right.
*)
fun need_translate_arg (Const (\<^const_name>\<open>anonymous\<close>, _)) = true
  | need_translate_arg (Const (\<^const_syntax>\<open>anonymous\<close>, _)) = true
  | need_translate_arg (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (Const (\<^const_syntax>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (A $ B) = need_translate_arg A orelse need_translate_arg B
  | need_translate_arg (Abs (_, _, X)) = need_translate_arg X
  | need_translate_arg _ = false

fun translate_arg' cnt s ns ( (C1 as Const (\<^const_name>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_name>\<open>Val\<close>, _))
                                       $ Const (\<^const_name>\<open>anonymous\<close>, _)
                                       $ X2))
      = let val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end
  | translate_arg' cnt s ns ( (C1 as Const (\<^const_syntax>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_syntax>\<open>Val\<close>, _))
                                       $ Const (\<^const_syntax>\<open>anonymous\<close>, _)
                                       $ X2))
      = let val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end

  | translate_arg' cnt s ns ( (C1 as Const (\<^const_name>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_name>\<open>Vals\<close>, _))
                                       $ Const (\<^const_name>\<open>anonymous\<close>, _)
                                       $ X2))
      = let val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end
  | translate_arg' cnt s ns ( (C1 as Const (\<^const_syntax>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_syntax>\<open>Vals\<close>, _))
                                       $ Const (\<^const_syntax>\<open>anonymous\<close>, _)
                                       $ X2))
      = let val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end

  | translate_arg' cnt s ns (Const (\<^const_name>\<open>anonymous\<close>, _))
      = let val s' = Symbol.bump_string s
         in (cnt, s', s'::ns, Free ("\<a>\<r>\<g>" ^ s, dummyT))
        end
  | translate_arg' cnt s ns (Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = let val s' = Symbol.bump_string s
         in (cnt, s', s'::ns, Free ("\<a>\<r>\<g>" ^ s, dummyT))
        end
  | translate_arg' cnt s ns (A $ B)
      = (case translate_arg' cnt  s  ns  A of (cnt',s',ns',A') =>
         case translate_arg' cnt' s' ns' B of (cnt'',s'',ns'',B') =>
          (cnt'', s'', ns'', A' $ B'))
  | translate_arg' cnt s ns (Abs (name,ty, X))
      = (case translate_arg' cnt s ns X of (cnt',s',ns',X') =>
           (cnt', s', ns', Abs (name,ty,X')))
  | translate_arg' cnt s ns X = (cnt,s,ns,X)

fun translate_arg X = #4 (translate_arg' 0 "\<a>\<r>\<g>_a" [] X)

datatype quantify_mode = No_Quantify | HOL_Quantify
datatype parameterize_proc = No_Parameterize | Tuple_Pack | Lambda_Apps

structure Proc_Parse_Ctxt = Generic_Data (
  type T = (quantify_mode * parameterize_proc) option
  val empty = NONE
  val merge = merge_options
)

fun set_proc_parse_mode mode = Proc_Parse_Ctxt.put (SOME mode)
fun restore_proc_parse_mode ctxt = Proc_Parse_Ctxt.put (Proc_Parse_Ctxt.get ctxt)

fun dest_proc_synt ((H as Const(\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, _)) $ p $ A $ R) = (H,p,A,R,Term.dummy)
  | dest_proc_synt ((H as Const(\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, _)) $ p $ A $ R) = (H,p,A,R,Term.dummy)
  | dest_proc_synt ((H as Const(\<^const_syntax>\<open>\<phi>Procedure\<close>, _)) $ p $ A $ R $ E) = (H,p,A,R,E)
  | dest_proc_synt ((H as Const(\<^const_name>\<open>\<phi>Procedure\<close>, _)) $ p $ A $ R $ E) = (H,p,A,R,E)

fun mk_proc_synt (H,p,A,R,E) =
      case H
        of Const(\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, _) => H $ p $ A $ R
         | Const(\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, _) => H $ p $ A $ R
         | Const(\<^const_syntax>\<open>\<phi>Procedure\<close>, _) => H $ p $ A $ R $ E
         | Const(\<^const_name>\<open>\<phi>Procedure\<close>, _)   => H $ p $ A $ R $ E

fun translate_proc_arg' (qmode, pmode) tm =
  let val (Procedure, proc, Arg, Ret, Err) = dest_proc_synt tm
      val (_, _, names, Arg') = translate_arg' 0 "\<a>\<r>\<g>_a" [] Arg
      val proc' = case pmode
                    of No_Parameterize => proc
                     | Tuple_Pack => proc $ mk_arg_list' (map (fn x => Free(x,dummyT)) (rev names))
                     | Lambda_Apps => fold_rev (fn N => fn X => X $ Free(N,dummyT) ) names proc
      val base = mk_proc_synt (Procedure, proc', Arg', Ret, Err)
      val ret = case qmode
                  of No_Quantify => base
                   | HOL_Quantify => base
                                  |> subst_atomic (map_index (fn (i,name) =>
                                                        (Free(name,dummyT), Bound i)) names)
                                  |> fold (fn name => fn X =>
                                        Const(\<^const_name>\<open>HOL.All\<close>, dummyT) $ Abs (name, dummyT, X)) names
   in ret
  end

fun translate_proc_arg ctxt tm =
  let val (_, _, Arg, _, _) = dest_proc_synt tm
   in if need_translate_arg Arg
      then case Proc_Parse_Ctxt.get ctxt
             of SOME mode => translate_proc_arg' mode tm
              | NONE => error (let open Pretty 
                    val pretty = Context.cases Syntax.pretty_term_global Syntax.pretty_term
                    fun show mode = let val tm' = translate_proc_arg' mode tm
                                     in try (Syntax.check_term (Context.proof_of ctxt)) tm'
                                     |> Option.map (fn tm'' => item [pretty ctxt tm''])
                                    end
                 in string_of (
                    chunks([block (text "Short syntax of \<open>\<v>\<a>\<l> T\<close> cannot be used here, because in this context\
                                       \ I cannot determine whether should the argument values be quantified,\
                                       \ or whether should I parameterize the procedure term using the argument values."),
                            block (text "You may clarify your formula by choosing one of the potential parses shown as follows")]
                         (*@ map_filter I
                             [show (No_Quantify, No_Parameterize),
                              show (HOL_Quantify, No_Parameterize),
                              show (No_Quantify, Tuple_Pack),
                              show (No_Quantify, Lambda_Apps),
                              show (HOL_Quantify, Lambda_Apps)]*) )
                 ) end)
      else tm
  end




(* fun mk_arg_prodT []  = \<^typ>\<open>unit \<phi>arg\<close>
  | mk_arg_prodT (Type ("dummy", []) :: _) = dummyT
  | mk_arg_prodT [T] = T
  | mk_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])::Ts) =
      (case mk_arg_prodT Ts of Type (\<^type_name>\<open>\<phi>arg\<close>, [Ts']) =>
          Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_arg_prodT (T,Ts')]))
  | mk_arg_prodT T = raise TYPE("bug #g4389h", T, []) *)

fun nth_project [_] 0 term = term
  | nth_project (ty::_::_) 0 term
      = \<^Const>\<open>\<phi>V_hd\<close> $ term
  | nth_project (ty::tys::tyss) i term =
      nth_project (tys::tyss) (i-1) (\<^Const>\<open>\<phi>V_tl\<close> $ term)
  | nth_project _ _ _ = error "Internal bug #bq3 ni8op["


fun gen_collect_and_map R2L (*whether in an order from right to left or reversely*) =
let

fun collect_vals Vs (v as Const (\<^const_name>\<open>anonymous\<close>, _)) = v::Vs
  | collect_vals Vs (v as Const (\<^const_syntax>\<open>anonymous\<close>, _)) = v::Vs
  | collect_vals Vs (v as Free (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _))) = insert (op = ) v Vs
  | collect_vals Vs (v as Var (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)))  = insert (op = ) v Vs
  | collect_vals Vs (v as Const ("_type_constraint_", Type("fun", [Type(\<^type_name>\<open>\<phi>arg\<close>, _),_])) $ _)
      = insert (op = ) v Vs
  | collect_vals Vs (v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ _))
      = insert (op = ) v Vs
  | collect_vals Vs (Const (\<^const_name>\<open>Val\<close>, _) $ (v as Const (\<^const_name>\<open>anonymous\<close>, _)))
      = v::Vs
  | collect_vals Vs (Const (\<^const_syntax>\<open>Val\<close>, _) $ (v as Const (\<^const_syntax>\<open>anonymous\<close>, _)))
      = v::Vs
  | collect_vals Vs (Const (\<^const_name>\<open>Vals\<close>, _) $ (v as Const (\<^const_name>\<open>anonymous\<close>, _)))
      = v::Vs
  | collect_vals Vs (Const (\<^const_syntax>\<open>Vals\<close>, _) $ (v as Const (\<^const_syntax>\<open>anonymous\<close>, _)))
      = v::Vs
  | collect_vals Vs (Const (\<^const_name>\<open>Val\<close>, _) $ v) = insert (op = ) v Vs
  | collect_vals Vs (Const (\<^const_syntax>\<open>Val\<close>, _) $ v) = insert (op = ) v Vs
  | collect_vals Vs (Const (\<^const_name>\<open>Vals\<close>, _) $ v) = insert (op = ) v Vs
  | collect_vals Vs (Const (\<^const_syntax>\<open>Vals\<close>, _) $ v) = insert (op = ) v Vs
  | collect_vals Vs (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = collect_vals Vs X
  | collect_vals Vs (Abs (_,_,X)) = collect_vals Vs X
  | collect_vals Vs (X $ Y) =
      if R2L
      then collect_vals (collect_vals Vs X) Y
      else collect_vals (collect_vals Vs Y) X
  | collect_vals Vs _ = Vs

fun jth_index_of_annoy j ans (Const (\<^const_name>\<open>anonymous\<close>, _) :: L)
      = if j = 0 then ans else jth_index_of_annoy (j-1) (ans+1) L
  | jth_index_of_annoy j ans (Const (\<^const_syntax>\<open>anonymous\<close>, _) :: L)
      = if j = 0 then ans else jth_index_of_annoy (j-1) (ans+1) L
  | jth_index_of_annoy j ans (_ :: L)
      = jth_index_of_annoy j (ans+1) L
  | jth_index_of_annoy _ _ [] = raise Fail "Procedure_Syntax: Insufficient values"

fun mk_projection Tys VS i v =
  let val ret = find_index (fn x => x = v) VS
   in if ret = ~1 then v
      else nth_project Tys ret (Bound i)
  end

fun map_ret Tys i VS (j, Const (\<^const_name>\<open>anonymous\<close>, _))
      = (j + 1, nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
  | map_ret Tys i VS (j, Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = (j + 1, nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
  | map_ret Tys i VS (j, v as Const ("_type_constraint_",
                                      Type("fun", [Type(\<^type_name>\<open>\<phi>arg\<close>, _),_])) $ _)
      = (j, mk_projection Tys VS i v)
  | map_ret Tys i VS (j, v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ _))
      = (j, mk_projection Tys VS i v)
  | map_ret Tys i VS (j, v as Free (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)))
      = (j, mk_projection Tys VS i v)
  | map_ret Tys i VS (j, v as Var (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)))
      = (j, mk_projection Tys VS i v)
  | map_ret Tys i VS (j, (h as Const (\<^const_name>\<open>Val\<close>, _)) $ Const (\<^const_name>\<open>anonymous\<close>, _))
      = (j + 1, h $ nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
  | map_ret Tys i VS (j, (h as Const (\<^const_syntax>\<open>Val\<close>, _)) $ Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = (j + 1, h $ nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
  | map_ret Tys i VS (j, (h as Const (\<^const_name>\<open>Vals\<close>, _)) $ Const (\<^const_name>\<open>anonymous\<close>, _))
      = (j + 1, h $ nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
  | map_ret Tys i VS (j, (h as Const (\<^const_syntax>\<open>Vals\<close>, _)) $ Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = (j + 1, h $ nth_project Tys (jth_index_of_annoy j 0 VS) (Bound i))
  | map_ret Tys i VS (j, (h as Const (\<^const_name>\<open>Val\<close>, _)) $ v)
      = (j, h $ mk_projection Tys VS i v)
  | map_ret Tys i VS (j, (h as Const (\<^const_syntax>\<open>Val\<close>, _)) $ v)
      = (j, h $ mk_projection Tys VS i v)
  | map_ret Tys i VS (j, (h as Const (\<^const_name>\<open>Vals\<close>, _)) $ v)
      = (j, h $ mk_projection Tys VS i v)
  | map_ret Tys i VS (j, (h as Const (\<^const_syntax>\<open>Vals\<close>, _)) $ v)
      = (j, h $ mk_projection Tys VS i v)
  | map_ret Tys i VS (j, (h as Const (\<^const_name>\<open>\<phi>Type\<close>, _)) $ A $ B)
      = (case map_ret Tys i VS (j, B) of (j',B') => (j', h $ A $ B'))
  | map_ret Tys i VS (j, Abs (name,ty,X))
      = (case map_ret Tys (i+1) VS (j, X) of (j',X') => (j', Abs (name, ty,X')))
  | map_ret Tys i VS (j, X $ Y)
      = if R2L
        then (case map_ret Tys i VS (j,Y) of (j',Y') =>
                (case map_ret Tys i VS (j',X) of (j'',X') => (j'', X' $ Y')))
        else (case map_ret Tys i VS (j,X) of (j',X') =>
                (case map_ret Tys i VS (j',Y) of (j'',Y') => (j'', X' $ Y')))
  | map_ret _ i _ (j,Bound a) = (j, Bound (if i <= a then a+1 else a))
  | map_ret _ _ _ jVX = jVX
in (collect_vals, map_ret) end

val dummyT_sem = Type (\<^type_name>\<open>\<phi>arg\<close>, [dummyT])
fun ex_fastype_of TM =
  let val T = fastype_of TM in if T = dummyT then dummyT_sem else T end
  handle TERM _ => dummyT_sem

fun package_values name _ (SOME []) term =
      (\<^term>\<open>\<phi>V_nil\<close>, Abs(name, val_list_T, term))
  | package_values name R2L Vs0 term =
  let
    val (collect_vals, map_ret) = gen_collect_and_map R2L
    val Vs = case Vs0 of SOME Vs => Vs | NONE => collect_vals [] term
    val Tys = fold_rev (fn T => (fn [] => [T]
                                  | L as T'::_ => mk_arg_prodT (T,T') :: L))
              (map ex_fastype_of Vs) []
    val T = if null Tys then \<^typ>\<open>unit \<phi>arg\<close> else hd Tys
  in (mk_arg_list Vs, Abs(name, T, if null Tys then term else #2(map_ret Tys 0 Vs (0,term))))
  end

fun package_values0 name zero_ty _ _ (term as Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, _))
      = (\<^Const>\<open>\<phi>arg zero_ty\<close> $ \<^Const>\<open>unreachable\<close>, Abs (name, \<^Type>\<open>\<phi>arg zero_ty\<close>, term))
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
val _ = Theory.setup (Sign.parse_translation [
    (\<^const_syntax>\<open>\<phi>Procedure\<close>, (fn ctxt => fn [f,Arg,Ret,E] =>
        (Const (\<^const_name>\<open>\<phi>Procedure\<close>, dummyT) $ f
          $ Arg
          $ (if need_translate_ret Ret then translate_ret' Ret else Ret)
          $ E)
        |> translate_proc_arg (Context.Proof ctxt))),
    (\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, (fn ctxt => fn [f,Arg,Ret] =>
        (Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, dummyT) $ f
          $ Arg
          $ (if need_translate_ret Ret then translate_ret' Ret else Ret))
        |> translate_proc_arg (Context.Proof ctxt) ))
])


end