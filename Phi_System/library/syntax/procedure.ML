(* library/syntax/procedure.ML
   Author: Authors of Submission 96

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
fun translate_arg' cnt s ( (C1 as Const (\<^const_name>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_name>\<open>Val\<close>, _))
                                       $ Const (\<^const_name>\<open>anonymous\<close>, _)
                                       $ X2))
      = (cnt+1, s, C1 $ X $ (C2 $ Free ("\<a>\<r>\<g>" ^ (string_of_int (cnt+1)), dummyT) $ X2))
  | translate_arg' cnt s ( (C1 as Const (\<^const_syntax>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_syntax>\<open>Val\<close>, _))
                                       $ Const (\<^const_syntax>\<open>anonymous\<close>, _)
                                       $ X2))
      = (cnt+1, s, C1 $ X $ (C2 $ Free ("\<a>\<r>\<g>" ^ (string_of_int (cnt+1)), dummyT) $ X2))

  | translate_arg' cnt s ( (C1 as Const (\<^const_name>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_name>\<open>Vals\<close>, _))
                                       $ Const (\<^const_name>\<open>anonymous\<close>, _)
                                       $ X2))
      = (cnt+1, s, C1 $ X $ (C2 $ Free ("\<a>\<r>\<g>" ^ (string_of_int (cnt+1)), dummyT) $ X2))
  | translate_arg' cnt s ( (C1 as Const (\<^const_syntax>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_syntax>\<open>Vals\<close>, _))
                                       $ Const (\<^const_syntax>\<open>anonymous\<close>, _)
                                       $ X2))
      = (cnt+1, s, C1 $ X $ (C2 $ Free ("\<a>\<r>\<g>" ^ (string_of_int (cnt+1)), dummyT) $ X2))

  | translate_arg' cnt s (Const (\<^const_name>\<open>anonymous\<close>, _))
      = (cnt, Symbol.bump_string s, Free ("\<a>\<r>\<g>" ^ s, dummyT))
  | translate_arg' cnt s (Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = (cnt, Symbol.bump_string s, Free ("\<a>\<r>\<g>" ^ s, dummyT))
  | translate_arg' cnt s (A $ B)
      = (case translate_arg' cnt  s  A of (cnt',s', A') =>
         case translate_arg' cnt' s' B of (cnt'',s'', B') =>
          (cnt'', s'', A' $ B'))
  | translate_arg' cnt s (Abs (name,ty, X))
      = (case translate_arg' cnt s X of (cnt',s', X') =>
           (cnt', s', Abs (name,ty,X')))
  | translate_arg' cnt s X = (cnt,s, X)
fun translate_arg X = #3 (translate_arg' 0 "\<a>\<r>\<g>_a" X)

fun need_translate_arg (Const (\<^const_name>\<open>anonymous\<close>, _)) = true
  | need_translate_arg (Const (\<^const_syntax>\<open>anonymous\<close>, _)) = true
  | need_translate_arg (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (Const (\<^const_syntax>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (A $ B) = need_translate_arg A orelse need_translate_arg B
  | need_translate_arg (Abs (_, _, X)) = need_translate_arg X
  | need_translate_arg _ = false


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