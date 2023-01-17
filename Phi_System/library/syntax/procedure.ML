(* library/syntax/procedure.ML
   Author: Qiyuan Xu

   The syntax parser for procedure specification.

It is invoked once there is an anonymous value in the argument specification,
or once the return specification is not a lambda abstraction nor an atom (a variable or a constant).
For translation in argument specification, all anonymous values are replaces by a free variable
  generated automatically.
For return specification, it collects all semantic values have \<^typ>\<open>'a \<phi>arg\<close> in the spec,
  and wrap the spec by a lambda abstraction over the semantic values, using the pair encoding
  of multi-return-values.
*)

signature PROCEDURE_SYNTAX = sig
(*
Translate a term X containing values V (including anonymous values) into (\<lambda>vs. X\<theta>),
  where vs is a tuple aggregating values V,
  \<theta> is a substitution mapping the ith value in V to the ith projection of vs.

Values of identical name are considered identical. Any anonymous value is considered unique.
*)
  val abstract_return_vals :
       string (*name of the lambda variable*)
        -> typ (*type of the return when the spec is 0*)
        -> bool (*the order of values V in tuple vs.
                  true for Right-to-Left; false for Left-to-Right*)
        -> term
        -> term (*values*) * term (*lambda abstraction*)

(* Syntax translation during parse of the post-condition,
   roughly identical to (abstract_return_vals "\<r>\<e>\<t>" true).
*)
val translate_ret : term -> term
val translate_arg : term -> term
  
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


fun dest_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [Type ("Product_Type.prod", [A, B])]))
      = (Type (\<^type_name>\<open>\<phi>arg\<close>, [A]), Type (\<^type_name>\<open>\<phi>arg\<close>, [B]))
  | dest_prodT (Type ("dummy", [])) = (dummyT,dummyT)
  | dest_prodT T = raise TYPE("bug #fsahofew", [T], [])
fun mk_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T1]), Type (\<^type_name>\<open>\<phi>arg\<close>, [T2]))
      = Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_prodT (T1,T2)])
  | mk_prodT (T1,T2) = raise TYPE("bug #geasr89", [T1,T2], [])

fun mk_tuple _ [] = \<^term>\<open>\<phi>V_none\<close>
  | mk_tuple _ [tm] = tm
  | mk_tuple (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])::tys) (tm::tms)
      = Const (\<^const_name>\<open>\<phi>V_pair\<close>, Type (\<^type_name>\<open>\<phi>arg\<close>, [fst (HOLogic.dest_prodT T)])
                                 --> Type (\<^type_name>\<open>\<phi>arg\<close>, [snd (HOLogic.dest_prodT T)])
                                 --> Type (\<^type_name>\<open>\<phi>arg\<close>, [T]))
          $ tm $ mk_tuple tys tms
  | mk_tuple tys tms = raise TYPE ("bug #vq4t4", tys, tms)

(* fun mk_prodT []  = \<^typ>\<open>unit \<phi>arg\<close>
  | mk_prodT (Type ("dummy", []) :: _) = dummyT
  | mk_prodT [T] = T
  | mk_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])::Ts) =
      (case mk_prodT Ts of Type (\<^type_name>\<open>\<phi>arg\<close>, [Ts']) =>
          Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_prodT (T,Ts')]))
  | mk_prodT T = raise TYPE("bug #g4389h", T, []) *)

fun nth_project [_] 0 term = term
  | nth_project (ty::_::_) 0 term
      = Const (\<^const_name>\<open>\<phi>V_fst\<close>, ty --> fst (dest_prodT ty)) $ term
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
  | collect_vals Vs (Const (\<^const_name>\<open>Val\<close>, _) $ v) = insert (op = ) v Vs
  | collect_vals Vs (Const (\<^const_syntax>\<open>Val\<close>, _) $ v) = insert (op = ) v Vs
  | collect_vals Vs (Abs (_,_,X)) = collect_vals Vs X
  | collect_vals Vs (X $ Y) =
      if R2L
      then collect_vals (collect_vals Vs X) Y
      else collect_vals (collect_vals Vs Y) X
  | collect_vals Vs _ = Vs

fun map_ret Tys i (j, Vs, Const (\<^const_name>\<open>anonymous\<close>, _))
      = (j + 1, Vs, nth_project Tys j (Bound i))
  | map_ret Tys i (j, Vs, Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = (j + 1, Vs, nth_project Tys j (Bound i))
  | map_ret Tys i (j, Vs, v as Const ("_type_constraint_",
                                      Type("fun", [Type(\<^type_name>\<open>\<phi>arg\<close>, _),_])) $ _)
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ _))
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, v as Free (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)))
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, v as Var (_, Type(\<^type_name>\<open>\<phi>arg\<close>, _)))
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, (h as Const (\<^const_name>\<open>Val\<close>, _)) $ Const (\<^const_name>\<open>anonymous\<close>, _))
      = (j + 1, Vs, h $ nth_project Tys j (Bound i))
  | map_ret Tys i (j, Vs, (h as Const (\<^const_syntax>\<open>Val\<close>, _)) $ Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = (j + 1, Vs, h $ nth_project Tys j (Bound i))
  | map_ret Tys i (j, Vs, (h as Const (\<^const_name>\<open>Val\<close>, _)) $ v)
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, h $ nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, h $ nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, (h as Const (\<^const_syntax>\<open>Val\<close>, _)) $ v)
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, h $ nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, h $ nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, Abs (name,ty,X))
      = (case map_ret Tys (i+1) (j, Vs, X) of (j',Vs',X') =>
            (j',Vs',Abs (name, ty,X')))
  | map_ret Tys i (j, Vs, X $ Y)
      = if R2L
        then (case map_ret Tys i (j,Vs,Y) of (j',Vs',Y') =>
                (case map_ret Tys i (j',Vs',X) of (j'',Vs'',X') =>
                    (j'',Vs'', X' $ Y')))
        else (case map_ret Tys i (j,Vs,X) of (j',Vs',X') =>
                (case map_ret Tys i (j',Vs',Y) of (j'',Vs'',Y') =>
                    (j'',Vs'', X' $ Y')))
  | map_ret _ b (j,Vs,Bound a) = (j, Vs, Bound (if b <= a then a+1 else a)) 
  | map_ret _ _ jVX = jVX
in (collect_vals, map_ret) end

val dummyT_sem = Type (\<^type_name>\<open>\<phi>arg\<close>, [dummyT])
fun ex_fastype_of TM =
  let val T = fastype_of TM in if T = dummyT then dummyT_sem else T end
  handle TERM _ => dummyT_sem

fun abstract_return_vals name zero_ty _ (term as Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, _))
      = (\<^Const>\<open>\<phi>arg zero_ty\<close> $ \<^Const>\<open>unreachable zero_ty\<close>, Abs (name, \<^Type>\<open>\<phi>arg zero_ty\<close>, term))
| abstract_return_vals name _ R2L term =
  let
    val (collect_vals, map_ret) = gen_collect_and_map R2L
    val Vs = collect_vals [] term
    val Tys = fold_rev (fn T => (fn [] => [T]
                                  | L as T'::_ => mk_prodT (T,T') :: L))
              (map ex_fastype_of Vs) []
    val T = if null Tys then \<^typ>\<open>unit \<phi>arg\<close> else hd Tys
  in (mk_tuple Tys Vs, Abs(name, T, #3(map_ret Tys 0 (0,[],term))))
  end


fun translate_ret (term as (Abs _)) = term
  | translate_ret (term as (Var _)) = term
  | translate_ret (term as (Free _)) = term
  | translate_ret (term as (Const _)) = term
  | translate_ret (Const ("_constrain", ty) $ X $ Y)
      = Const ("_constrain", ty) $ translate_ret X $ Y
  | translate_ret (Const ("_type_constraint_", ty) $ X)
      = Const ("_type_constraint_", ty) $ translate_ret X
  | translate_ret (Const ("_constrainAbs", ty) $ X $ Y)
      = Const ("_constrainAbs", ty) $ translate_ret X $ Y
  | translate_ret term =
      snd (abstract_return_vals "\<r>\<e>\<t>" \<^typ>\<open>dummy\<close> true term)


(* fun translate_num term =
      fold_aterms (
          fn Const (\<^const_name>\<open>val_syntax\<close>, _) => (fn n => n + 1)
           | _ => I) term 0 *)

fun need_translate_ret (Abs (_,_,_)) = false
  | need_translate_ret (Free _) = false
  | need_translate_ret (Var  _) = false
  | need_translate_ret (Const  _) = false
  | need_translate_ret (Const ("_constrain", _) $ X $ _)
      = need_translate_ret X
  | need_translate_ret (Const ("_type_constraint_", _) $ X)
      = need_translate_ret X
  | need_translate_ret (Const ("_constrainAbs", _) $ X $ _)
      = need_translate_ret X
  | need_translate_ret _ = true

(*
The parse translation is invoked once there is an anonymous value in the argument specification,
or once the return specification is not a lambda abstraction nor an atom (a variable or a constant)
*)
val _ = Theory.setup (Sign.parse_translation [
    (\<^const_syntax>\<open>\<phi>Procedure\<close>, (fn _ => fn [f,Arg,Ret,E] =>
        Const (\<^const_name>\<open>\<phi>Procedure\<close>, dummyT) $ f
          $ (if need_translate_arg Arg then translate_arg Arg else Arg)
          $ (if need_translate_ret Ret then translate_ret Ret else Ret)
          $ E)),
    (\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, (fn _ => fn [f,Arg,Ret] =>
        Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, dummyT) $ f
          $ (if need_translate_arg Arg then translate_arg Arg else Arg)
          $ (if need_translate_ret Ret then translate_ret Ret else Ret)))
])


end