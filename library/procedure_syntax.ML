signature PROCEDURE_SYNTAX = sig
  val translate_ret : term -> term
  val abstract_return_vals : term -> term * term
end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct

fun translate_arg cnt term =
  map_aterms (
      fn Const (\<^const_name>\<open>anonymous_val\<close>, _) =>
            Free ("\<v>\<a>\<l>" ^ (string_of_int (cnt())), dummyT)
       | x => x
     ) term

fun dest_prodT (Type (\<^type_name>\<open>sem_value\<close>, [T])) = HOLogic.dest_prodT T
  | dest_prodT (Type ("dummy", [])) = (dummyT,dummyT)
  | dest_prodT T = raise TYPE("bug #fsahofew", [T], [])
fun mk_prodT (Type (\<^type_name>\<open>sem_value\<close>, [T1]), Type (\<^type_name>\<open>sem_value\<close>, [T2]))
      = Type (\<^type_name>\<open>sem_value\<close>, [HOLogic.mk_prodT (T1,T2)])
  | mk_prodT (Type ("dummy", []), _) = dummyT
  | mk_prodT (_, Type ("dummy", [])) = dummyT
  | mk_prodT (T1,T2) = raise TYPE("bug #geasr89", [T1,T2], [])

fun mk_tuple _ [] = \<^term>\<open>sem_value ()\<close>
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
      Const (\<^const_name>\<open>\<phi>V_snd\<close>, ty --> tys) $ nth_project (tys::tyss) (i-1) term

fun collect_ret Vs (v as Const (\<^const_name>\<open>anonymous_val\<close>, _)) = v::Vs
  | collect_ret Vs (v as Free (_, Type(\<^type_name>\<open>sem_value\<close>, _))) = insert (op = ) v Vs
  | collect_ret Vs (v as Var (_, Type(\<^type_name>\<open>sem_value\<close>, _)))  = insert (op = ) v Vs
  | collect_ret Vs (v as Const ("_type_constraint_", Type("fun", [Type(\<^type_name>\<open>sem_value\<close>, _),_])) $ _)
      = insert (op = ) v Vs
  | collect_ret Vs (v as Const (\<^const_name>\<open>map_sem_value\<close>, _) $ _ $ Var _) = insert (op = ) v Vs
  | collect_ret Vs (v as Const (\<^const_name>\<open>map_sem_value\<close>, _) $ _ $ Free _)= insert (op = ) v Vs
  | collect_ret Vs (Abs (_,_,X)) = collect_ret Vs X
  | collect_ret Vs (X $ Y) = collect_ret (collect_ret Vs X) Y
  | collect_ret Vs _ = Vs


fun map_ret Tys i (j, Vs, Const (\<^const_name>\<open>anonymous_val\<close>, _))
      = (j + 1, Vs, nth_project Tys j (Bound i))
  | map_ret Tys i (j, Vs, v as Const ("_type_constraint_",
                                           Type("fun", [Type(\<^type_name>\<open>sem_value\<close>, _),_])) $ _)
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
  | map_ret Tys i (j, Vs, v as Const (\<^const_name>\<open>map_sem_value\<close>, _) $ _ $ Var _)
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, v as Const (\<^const_name>\<open>map_sem_value\<close>, _) $ _ $ Free _)
      = (case AList.lookup (op =) Vs v
           of SOME k => (j, Vs, nth_project Tys k (Bound i))
            | NONE => (j + 1, (v,j)::Vs, nth_project Tys j (Bound i)))
  | map_ret Tys i (j, Vs, Abs (name,ty,X))
      = (case map_ret Tys (i+1) (j, Vs, X) of (j',Vs',X') =>
            (j',Vs',Abs (name, ty,X')))
  | map_ret Tys i (j, Vs, X $ Y)
      = (case map_ret Tys i (j,Vs,X) of (j',Vs',X') =>
          (case map_ret Tys i (j',Vs',Y) of (j'',Vs'',Y') =>
              (j'',Vs'', X' $ Y')))
  | map_ret _ b (j,Vs,Bound a) = (j, Vs, Bound (if b <= a then a+1 else a)) 
  | map_ret _ _ jVX = jVX


fun translate_ret (term as (Abs _)) = term
  | translate_ret (term as (Var _)) = term
  | translate_ret (term as (Free _)) = term
  | translate_ret (Const ("_type_constraint_", ty) $ X)
      = Const ("_type_constraint_", ty) $ translate_ret X
  | translate_ret term =
      let
        val Vs = collect_ret [] term
        val Tys = map (K dummyT) Vs
                    |> fold_rev (fn T => (fn [] => [T]
                                           | L as T'::_ => mk_prodT (T,T') :: L)) []
        val T = if null Tys then \<^typ>\<open>unit\<close> else hd Tys
        val T' = Type(\<^type_name>\<open>sem_value\<close>, [T])
      in Abs ("\<r>\<e>\<t>", T',
           if null Vs then term else #3(map_ret Tys 0 (0,[],term)))
      end

fun abstract_return_vals (term as Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, _))
      = (\<^term>\<open>undefined :: unreachable sem_value\<close>,
         Abs ("_", \<^typ>\<open>unreachable sem_value\<close>, term))
| abstract_return_vals term =
  let
   val Vs = collect_ret [] term
   fun dest_T (Type (\<^type_name>\<open>sem_value\<close>, [X])) = X
     | dest_T _ = raise Fail "BUG #dnwf87"
   val Tys = map (dest_T o fastype_of) Vs
              |> fold_rev (fn T => (fn [] => [T]
                                     | L as T'::_ => mk_prodT (T,T') :: L)) []
   val T = if null Tys then \<^typ>\<open>unit\<close> else hd Tys
   val T' = Type(\<^type_name>\<open>sem_value\<close>, [T])
  in (mk_tuple Tys Vs, Abs("\<r>\<e>\<t>", T', #3(map_ret Tys 0 (0,[],term))))
  end


(* fun translate_num term =
      fold_aterms (
          fn Const (\<^const_name>\<open>val_syntax\<close>, _) => (fn n => n + 1)
           | _ => I) term 0 *)

fun need_translate_ret (Abs (_,_,_)) = false
  | need_translate_ret _ = true

fun need_translate_arg (Const (\<^const_name>\<open>anonymous_val\<close>, _)) = true
  | need_translate_arg (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (A $ B) = need_translate_arg A orelse need_translate_arg B
  | need_translate_arg (Abs (_, _, X)) = need_translate_arg X
  | need_translate_arg _ = false

fun need_translate (Const ("local.\<phi>Procedure_no_exception", _) $ _ $ Arg $ Ret) =
      need_translate_arg Arg orelse need_translate_ret Ret
| need_translate (Const ("local.\<phi>Procedure", _) $ _ $ Arg $ Ret $ _) =
      need_translate_arg Arg orelse need_translate_ret Ret
| need_translate (A $ B) = need_translate A orelse need_translate B
| need_translate (Abs (_, _, X)) = need_translate X
| need_translate _ = false


fun translate_procedure cnt
  (Const ("local.\<phi>Procedure", t1) $ f $ Arg $ Ret $ E) =
    (Const ("local.\<phi>Procedure", t1)
        $ f $ translate_arg cnt Arg $ translate_ret Ret $ E)
  | translate_procedure cnt (Const ("local.\<phi>Procedure_no_exception", t1) $ f $ Arg $ Ret) =
    (Const ("local.\<phi>Procedure_no_exception", t1)
        $ f $ translate_arg cnt Arg $ translate_ret Ret)
  | translate_procedure C (A $ B) = (translate_procedure C A $ translate_procedure C B)
  | translate_procedure C (Abs (name,ty,X))
      = Abs (name, ty, translate_procedure C X)
  | translate_procedure _ X = X

val _ = Theory.setup (
  Context.theory_map (Syntax_Phases.term_check ~10 "\<phi>variable" (fn _ =>
    let val cnt = Counter.make ()
     in map (fn term => if need_translate term
                        then translate_procedure cnt term
                        else term) end))
)

end