signature PROCEDURE_SYNTAX = sig
(*
Translate a term X containing values V (including anonymous values) into (\<lambda>vs. X\<theta>),
  where vs is a tuple aggregating values V,
  \<theta> is a substitution mapping the ith value in V to the ith projection of vs.

Values of identical name are considered identical. Any anonymous value is considered unique.
*)
  val abstract_return_vals :
       string (*name of the lambda variable*)
        -> bool (*the order of values V in tuple vs.
                  true for Right-to-Left; false for Left-to-Right*)
        -> term
        -> term * term

(* Syntax translation during parse of the post-condition,
   roughly identical to (abstract_return_vals "\<r>\<e>\<t>" true).
*)
val translate_ret : term -> term
val translate_arg : term -> term
  
end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct

(*
Syntax translation during parsing of the pre-condition is simply replacing
all anonymous values by a name \<a>\<r>\<g>i for the ith value from left to right.
*)
fun translate_arg' cnt (Const (\<^const_name>\<open>anonymous\<close>, _))
      = (cnt+1, Free ("\<a>\<r>\<g>" ^ (string_of_int (cnt+1)), dummyT))
  | translate_arg' cnt (A $ B)
      = (case translate_arg' cnt  A of (cnt', A') =>
         case translate_arg' cnt' B of (cnt'', B') =>
          (cnt'', A' $ B'))
  | translate_arg' cnt (Abs (name,ty, X))
      = (case translate_arg' cnt X of (cnt', X') =>
           (cnt', Abs (name,ty,X')))
  | translate_arg' cnt X = (cnt, X)
val translate_arg = translate_arg' 0 #> snd


fun dest_prodT (Type (\<^type_name>\<open>sem_value\<close>, [Type ("Product_Type.prod", [A, B])]))
      = (Type (\<^type_name>\<open>sem_value\<close>, [A]), Type (\<^type_name>\<open>sem_value\<close>, [B]))
  | dest_prodT (Type ("dummy", [])) = (dummyT,dummyT)
  | dest_prodT T = raise TYPE("bug #fsahofew", [T], [])
fun mk_prodT (Type (\<^type_name>\<open>sem_value\<close>, [T1]), Type (\<^type_name>\<open>sem_value\<close>, [T2]))
      = Type (\<^type_name>\<open>sem_value\<close>, [HOLogic.mk_prodT (T1,T2)])
  | mk_prodT (T1,T2) = raise TYPE("bug #geasr89", [T1,T2], [])

fun mk_tuple _ [] = \<^term>\<open>\<phi>V_none\<close>
  | mk_tuple _ [tm] = tm
  | mk_tuple (Type (\<^type_name>\<open>sem_value\<close>, [T])::tys) (tm::tms)
      = Const (\<^const_name>\<open>\<phi>V_pair\<close>, Type (\<^type_name>\<open>sem_value\<close>, [fst (HOLogic.dest_prodT T)])
                                 --> Type (\<^type_name>\<open>sem_value\<close>, [snd (HOLogic.dest_prodT T)])
                                 --> Type (\<^type_name>\<open>sem_value\<close>, [T]))
          $ tm $ mk_tuple tys tms
  | mk_tuple tys tms = raise TYPE ("bug #vq4t4", tys, tms)

(* fun mk_prodT []  = \<^typ>\<open>unit sem_value\<close>
  | mk_prodT (Type ("dummy", []) :: _) = dummyT
  | mk_prodT [T] = T
  | mk_prodT (Type (\<^type_name>\<open>sem_value\<close>, [T])::Ts) =
      (case mk_prodT Ts of Type (\<^type_name>\<open>sem_value\<close>, [Ts']) =>
          Type (\<^type_name>\<open>sem_value\<close>, [HOLogic.mk_prodT (T,Ts')]))
  | mk_prodT T = raise TYPE("bug #g4389h", T, []) *)

fun nth_project [_] 0 term = term
  | nth_project (ty::_::_) 0 term
      = Const (\<^const_name>\<open>\<phi>V_fst\<close>, ty --> fst (dest_prodT ty)) $ term
  | nth_project (ty::tys::tyss) i term =
      nth_project (tys::tyss) (i-1) (Const (\<^const_name>\<open>\<phi>V_snd\<close>, ty --> tys) $ term)


fun gen_collect_and_map R2L (*whether in an order from right to left or reversely*) =
let

fun collect_vals Vs (v as Const (\<^const_name>\<open>anonymous\<close>, _)) = v::Vs
  | collect_vals Vs (v as Const (\<^const_syntax>\<open>anonymous\<close>, _)) = v::Vs
  | collect_vals Vs (v as Free (_, Type(\<^type_name>\<open>sem_value\<close>, _))) = insert (op = ) v Vs
  | collect_vals Vs (v as Var (_, Type(\<^type_name>\<open>sem_value\<close>, _)))  = insert (op = ) v Vs
  | collect_vals Vs (v as Const ("_type_constraint_", Type("fun", [Type(\<^type_name>\<open>sem_value\<close>, _),_])) $ _)
      = insert (op = ) v Vs
  | collect_vals Vs (v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>sem_value\<close>, _) $ _))
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
                                      Type("fun", [Type(\<^type_name>\<open>sem_value\<close>, _),_])) $ _)
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>sem_value\<close>, _) $ _))
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, v as Free (_, Type(\<^type_name>\<open>sem_value\<close>, _)))
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, v as Var (_, Type(\<^type_name>\<open>sem_value\<close>, _)))
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

val dummyT_sem = Type (\<^type_name>\<open>sem_value\<close>, [dummyT])
fun ex_fastype_of TM =
  let val T = fastype_of TM in if T = dummyT then dummyT_sem else T end
  handle TERM _ => dummyT_sem

fun abstract_return_vals name _ (term as Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, _))
      = (\<^term>\<open>undefined :: unreachable sem_value\<close>,
         Abs (name, \<^typ>\<open>unreachable sem_value\<close>, term))
| abstract_return_vals name R2L term =
  let
    val (collect_vals, map_ret) = gen_collect_and_map R2L
    val Vs = collect_vals [] term
    val Tys = fold_rev (fn T => (fn [] => [T]
                                  | L as T'::_ => mk_prodT (T,T') :: L))
              (map ex_fastype_of Vs) []
    val T = if null Tys then \<^typ>\<open>unit sem_value\<close> else hd Tys
  in (mk_tuple Tys Vs, Abs(name, T, #3(map_ret Tys 0 (0,[],term))))
  end

fun translate_ret (term as (Abs _)) = term
  | translate_ret (term as (Var _)) = term
  | translate_ret (term as (Free _)) = term
  | translate_ret (Const ("_constrain", ty) $ X $ Y)
      = Const ("_constrain", ty) $ translate_ret X $ Y
  | translate_ret (Const ("_type_constraint_", ty) $ X)
      = Const ("_type_constraint_", ty) $ translate_ret X
  | translate_ret (Const ("_constrainAbs", ty) $ X $ Y)
      = Const ("_constrainAbs", ty) $ translate_ret X $ Y
  | translate_ret term =
      snd (abstract_return_vals "\<r>\<e>\<t>" true term)


(* fun translate_num term =
      fold_aterms (
          fn Const (\<^const_name>\<open>val_syntax\<close>, _) => (fn n => n + 1)
           | _ => I) term 0 *)

fun need_translate_ret (Abs (_,_,_)) = false
  | need_translate_ret (Const ("_constrain", ty) $ X $ Y)
      = need_translate_ret X
  | need_translate_ret (Const ("_type_constraint_", ty) $ X)
      = need_translate_ret X
  | need_translate_ret (Const ("_constrainAbs", ty) $ X $ Y)
      = need_translate_ret X
  | need_translate_ret _ = true

fun need_translate_arg (Const (\<^const_name>\<open>anonymous\<close>, _)) = true
  | need_translate_arg (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (A $ B) = need_translate_arg A orelse need_translate_arg B
  | need_translate_arg (Abs (_, _, X)) = need_translate_arg X
  | need_translate_arg _ = false

fun need_translate (Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, _) $ _ $ Arg $ Ret) =
      need_translate_arg Arg orelse need_translate_ret Ret
| need_translate (Const (\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ Arg $ Ret $ _) =
      need_translate_arg Arg orelse need_translate_ret Ret
| need_translate (A $ B) = need_translate A orelse need_translate B
| need_translate (Abs (_, _, X)) = need_translate X
| need_translate _ = false


fun translate_procedure
  (Const (\<^const_name>\<open>\<phi>Procedure\<close>, t1) $ f $ Arg $ Ret $ E) =
    (Const (\<^const_name>\<open>\<phi>Procedure\<close>, t1)
        $ f $ translate_arg Arg $ translate_ret Ret $ E)
  | translate_procedure (Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, t1) $ f $ Arg $ Ret) =
    (Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, t1)
        $ f $ translate_arg Arg $ translate_ret Ret)
  | translate_procedure (A $ B) = (translate_procedure A $ translate_procedure B)
  | translate_procedure (Abs (name,ty,X))
      = Abs (name, ty, translate_procedure X)
  | translate_procedure X = X

val _ = Theory.setup (Sign.parse_translation [
    (\<^const_syntax>\<open>\<phi>Procedure\<close>, (fn ctxt => fn [f,Arg,Ret,E] =>
        Const (\<^const_name>\<open>\<phi>Procedure\<close>, dummyT) $ f
          $ (if need_translate_arg Arg then translate_arg Arg else Arg)
          $ (if need_translate_ret Ret then translate_ret Ret else Ret)
          $ E)),
    (\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, (fn ctxt => fn [f,Arg,Ret] =>
        Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, dummyT) $ f
          $ (if need_translate_arg Arg then translate_arg Arg else Arg)
          $ (if need_translate_ret Ret then translate_ret Ret else Ret)))
])

(*val _ = Theory.setup (
  Context.theory_map (Syntax_Phases.term_check ~10 "\<phi>variable" (fn _ =>
    map (fn term => if need_translate term
                    then translate_procedure term
                    else term)))
)*)

end