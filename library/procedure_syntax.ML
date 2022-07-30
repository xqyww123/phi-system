signature PROCEDURE_SYNTAX = sig
  val translate_ret : term -> term
  val abstract_return_vals : Proof.context -> term -> term * term
end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct

fun translate_arg cnt term =
  map_aterms (
      fn Const (\<^const_name>\<open>val_syntax\<close>, _) =>
            Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ Free ("\<v>\<a>\<l>" ^ (string_of_int (cnt())), dummyT)
       | x => x
     ) term

fun list_nth 0 term = Const (\<^const_name>\<open>\<phi>V_hd\<close>, dummyT) $ term
  | list_nth i term = list_nth (i-1) (Const (\<^const_name>\<open>\<phi>V_tl\<close>, dummyT) $ term)
fun list_last 0 term = term
  | list_last i term = list_last (i-1) (Const (\<^const_name>\<open>\<phi>V_tl\<close>, dummyT) $ term)


fun map_ret _ i j (Const (\<^const_name>\<open>val_syntax\<close>, _)) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ list_nth j (Bound i))
  | map_ret _ i j (Const (\<^const_name>\<open>std.Val\<close>, _) $ Free _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ list_nth j (Bound i))
  | map_ret _ i j (Const (\<^const_name>\<open>std.Val\<close>, _) $ Var _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ list_nth j (Bound i))
  | map_ret _ i j (Const ("local.Val", _) $ Free _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ list_nth j (Bound i))
  | map_ret _ i j (Const ("local.Val", _) $ Var _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ list_nth j (Bound i))
  | map_ret N i j (Const (\<^const_name>\<open>ret_syntax\<close>, _)) = (j, list_last N (Bound i))
  | map_ret N i j (Abs (name,ty,X)) =
       map_ret N (i+1) j X |> apsnd (fn X => Abs (name, ty,X))
  | map_ret N i j (X $ Y) =
      map_ret N i j X |> (fn (j',X') => map_ret N i j' Y |> apsnd (fn Y' => X' $ Y'))
  | map_ret _ 0 j (Bound a) = (j, Bound (a+1))
  | map_ret _ _ j X = (j,X)

(* fun translate_num term =
      fold_aterms (
          fn Const (\<^const_name>\<open>val_syntax\<close>, _) => (fn n => n + 1)
           | _ => I) term 0 *)

fun translate_num_ret'' n (Const (\<^const_name>\<open>val_syntax\<close>, _)) = n + 1
  | translate_num_ret'' n (Const ("local.Val", _) $ Free _ ) = n + 1
  | translate_num_ret'' n (Const ("local.Val", _) $ Var _) = n + 1
  | translate_num_ret'' n (Const (\<^const_name>\<open>std.Val\<close>, _) $ Free _) = n + 1
  | translate_num_ret'' n (Const (\<^const_name>\<open>std.Val\<close>, _) $ Var _) = n + 1
  | translate_num_ret'' n (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = translate_num_ret'' n X
  | translate_num_ret'' n (X $ Y) =
      translate_num_ret'' (translate_num_ret'' n X) Y
  | translate_num_ret'' n (Abs (_,_,X)) = translate_num_ret'' n X
  | translate_num_ret'' n _ = n
fun translate_num_ret' (Abs (_,_,_)) = 0
  | translate_num_ret' term = translate_num_ret'' 0 term


fun need_translate_ret' (Const (\<^const_name>\<open>ret_syntax\<close>, _)) = true
  | need_translate_ret' (Const (\<^const_name>\<open>val_syntax\<close>, _)) = true
  | need_translate_ret' (Const ("local.Val", _) $ Free _ ) = true
  | need_translate_ret' (Const ("local.Val", _) $ Var _) = true
  | need_translate_ret' (Const (\<^const_name>\<open>std.Val\<close>, _) $ Free _) = true
  | need_translate_ret' (Const (\<^const_name>\<open>std.Val\<close>, _) $ Var _) = true
  | need_translate_ret' (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_ret' X
  | need_translate_ret' (A $ B) = need_translate_ret' A orelse need_translate_ret' B
  | need_translate_ret' (Abs (_, _, X)) = need_translate_ret' X
  | need_translate_ret' _ = false
fun need_translate_ret (Abs (_,_,_)) = false
  | need_translate_ret _ = true

fun need_translate_arg (Const (\<^const_name>\<open>val_syntax\<close>, _)) = true
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



fun translate_ret (term as (Abs _)) = term
  | translate_ret (term as (Var _)) = term
  | translate_ret (term as (Free _)) = term
  | translate_ret (Const ("_type_constraint_", ty) $ X)
      = Const ("_type_constraint_", ty) $ translate_ret X
  | translate_ret term =
      if need_translate_ret term
      then let
             val num = translate_num_ret' term
           in
             Abs ("\<r>\<e>\<t>", Type(\<^type_name>\<open>list\<close>,
                 [TFree ("'VAL", dummyS)]), map_ret num 0 0 term |> snd)
           end
      else term

fun collect_values' L (Const ("local.Val", _) $ v) = v::L
  | collect_values' L (Const (@{const_name std.Val}, _) $ v) = v::L
  | collect_values' L (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = collect_values' L X
  | collect_values' L (A $ B) = collect_values' (collect_values' L A) B
  | collect_values' L (Abs (_,_,X)) = collect_values' L X
  | collect_values' L _ = L
fun is_varlenT (Type(\<^type_name>\<open>list\<close>, [TFree("'VAL", _)])) = true
  | is_varlenT _ = false
fun is_varlen (Free (_,T)) = is_varlenT T
  | is_varlen (Var (_,T)) = is_varlenT T
  | is_varlen _ = false
fun collect_values X (L,R) =
  case Term.strip_comb X
    of (Free _, tms) => (L, filter is_varlen tms @ R)
     | (Var  _, tms) => (L, filter is_varlen tms @ R)
     | _ => (collect_values' L X, R)

fun abstract_return_vals ctxt term =
  let
    val valT = #VAL (PhiSyntax.get_types ctxt)
    val listT = Type(\<^type_name>\<open>list\<close>, [valT])
    fun list_nth 0 term = Const (\<^const_name>\<open>\<phi>V_hd\<close>, listT --> valT) $ term
      | list_nth i term = list_nth (i-1) (Const (\<^const_name>\<open>\<phi>V_tl\<close>, listT --> listT) $ term)
    fun list_last 0 term = term
      | list_last i term = list_last (i-1) (Const (\<^const_name>\<open>\<phi>V_tl\<close>, listT --> listT) $ term)

    val (vals, varlen') = fold collect_values (PhiSyntax.strip_separations term) ([],[])
    val N = length vals
    val varlen = case distinct (op =) varlen'
                   of [r] => SOME r
                    | [ ] => NONE
                    | Rs => raise TERM ("multiple variable-length arguments/returns.", Rs)
    fun trans 0 (i, Bound j) = (i, Bound (j+1))
      | trans k (i, Const ("local.Val", ty) $ _)
          = (i+1, Const (@{const_name std.Val}, ty) $ list_nth i (Bound k))
      | trans k (i, Const (@{const_name std.Val}, ty) $ _)
          = (i+1, Const (@{const_name std.Val}, ty) $ list_nth i (Bound k))
      | trans k (i, Const (\<^const_name>\<open>\<phi>Type\<close>, t1) $ x $ T)
          = trans k (i, T) |> apsnd (fn T' => Const (\<^const_name>\<open>\<phi>Type\<close>, t1) $ x $ T')
      | trans k (i, A $ B)
          = (case trans k (i, A) of (i',A')  =>
             case trans k (i',B) of (i'',B') => (i'', A' $ B'))
      | trans k (i, Abs (name,ty,X))
          = (case trans (k+1) (i,X) of (i',X') => (i',Abs (name,ty,X')))
      | trans _ (i, X) = (i, X)
    fun trans_varlen term =
      if is_varlen term then list_last N (Bound 0) else term
    fun trans' X =
      case Term.strip_comb X
        of (Free a, tms) => Term.list_comb (Free a, map trans_varlen tms)
         | (Var a, tms) => Term.list_comb (Var a, map trans_varlen tms)
         | _ => trans 0 (0,X) |> snd
    val instance = 
          the_default (Const(\<^const_name>\<open>Nil\<close>, listT)) varlen
            |> fold_rev (fn V => fn L =>
                  Const (\<^const_name>\<open>Cons\<close>, valT --> listT --> listT) $ V $ L) vals
  in (instance, Abs("\<r>\<e>\<t>", Type(\<^type_name>\<open>list\<close>, [TFree("'VAL", dummyS)]), trans' term))
  end

 
    


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