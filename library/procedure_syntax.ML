signature PROCEDURE_SYNTAX = sig
  val translate_ret : term -> term
  val abstract_return_vals : term -> term
end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct

fun translate_arg cnt term =
  map_aterms (
      fn Const (\<^const_name>\<open>val_syntax\<close>, _) =>
            Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ Free ("\<v>\<a>\<l>" ^ (string_of_int (cnt())), dummyT)
       | x => x
     ) term

fun tuple_proj n 0 term =
      (if n <= 1 then term else Const (\<^const_name>\<open>fst\<close>, dummyT) $ term)
  | tuple_proj n i term =
      tuple_proj (n-1) (i-1) (Const (\<^const_name>\<open>snd\<close>, dummyT) $ term)

fun map_ret N i j (Const (\<^const_name>\<open>val_syntax\<close>, _)) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ tuple_proj N j (Bound i))
  | map_ret N i j (Const (\<^const_name>\<open>std.Val\<close>, _) $ Free _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ tuple_proj N j (Bound i))
  | map_ret N i j (Const (\<^const_name>\<open>std.Val\<close>, _) $ Var _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ tuple_proj N j (Bound i))
  | map_ret N i j (Const ("local.Val", _) $ Free _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ tuple_proj N j (Bound i))
  | map_ret N i j (Const ("local.Val", _) $ Var _) =
      (j + 1, Const (\<^const_name>\<open>std.Val\<close>, dummyT) $ tuple_proj N j (Bound i))
  | map_ret N i j (Abs (name,ty,X)) =
       map_ret N (i+1) j X |> apsnd (fn X => Abs (name, ty,X))
  | map_ret N i j (X $ Y) =
      map_ret N i j X |> (fn (j',X') => map_ret N i j' Y |> apsnd (fn Y' => X' $ Y'))
  | map_ret _ 0 j (Bound a) = (j, Bound (a+1))
  | map_ret _ _ j X = (j,X)

fun translate_num term =
      fold_aterms (
          fn Const (\<^const_name>\<open>val_syntax\<close>, _) => (fn n => n + 1)
           | _ => I) term 0

fun translate_num_more' n (Const (\<^const_name>\<open>val_syntax\<close>, _)) = n + 1
  | translate_num_more' n (Const ("local.Val", _) $ Free _ ) = n + 1
  | translate_num_more' n (Const ("local.Val", _) $ Var _) = n + 1
  | translate_num_more' n (Const (\<^const_name>\<open>std.Val\<close>, _) $ Free _) = n + 1
  | translate_num_more' n (Const (\<^const_name>\<open>std.Val\<close>, _) $ Var _) = n + 1
  | translate_num_more' n (X $ Y) =
      translate_num_more' (translate_num_more' n X) Y
  | translate_num_more' n (Abs (_,_,X)) = translate_num_more' n X
  | translate_num_more' n _ = n
fun translate_num_more (Abs (_,_,_)) = 0
  | translate_num_more term = translate_num_more' 0 term


fun translate_ret (term as (Abs _)) = term
  | translate_ret (term as (Var _)) = term
  | translate_ret (term as (Free _)) = term
  | translate_ret (Const ("_type_constraint_", ty) $ X)
      = Const ("_type_constraint_", ty) $ translate_ret X
  | translate_ret term =
      let
        val num = translate_num_more term
      in
        if num > 0 orelse (case term of Const (\<^const_name>\<open>times\<close>, _) $ _ $ _ => true
                                      | Const ("local.COMMA", _) $ _ $ _ => true
                                      | Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => true
                                      | Const (\<^const_name>\<open>ExSet\<close>, _) $ _ => true
                                      | Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _ => true
                                      | _ => false)
        then Abs ("\<r>\<e>\<t>", (if num = 0 then \<^typ>\<open>unit\<close> else dummyT), map_ret num 0 0 term |> snd)
        else term
      end

fun collect_values L (Const ("local.Val", _) $ v) = v::L
  | collect_values L (Const (@{const_name std.Val}, _) $ v) = v::L
  | collect_values L (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = collect_values L X
  | collect_values L (A $ B) = collect_values (collect_values L A) B
  | collect_values L (Abs (_,_,X)) = collect_values L X
  | collect_values L _ = L

fun is_value_type (Type (\<^type_name>\<open>list\<close>, [TFree ("'VAL", _)])) = true
  | is_value_type _ = false

fun collect_values' X =
  case Term.strip_comb X
    of (Free _, L) =>
          filter (fn x => is_value_type (fastype_of x)) L
     | (Var _, L) =>
          filter (fn x => is_value_type (fastype_of x)) L
     | _ => collect_values [] X


fun abstract_return_vals term =
  let
    val vals = maps collect_values' (PhiSyntax.strip_separations term)
             |> distinct (op =)
    val num = length vals
    val term' = subst_free (map_index (fn (i,v) => (v, tuple_proj num  i (Bound 0))) vals) term
  in Abs("\<r>\<e>\<t>", HOLogic.mk_tupleT (map fastype_of vals), term')
  end
    


fun need_translate 
  (Const ("local.\<phi>Procedure_no_exception", _) $ _ $ _ $ _) = true
| need_translate  (Const ("local.\<phi>Procedure", _) $ _ $ _ $ _ $ _) = true
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
  Context.theory_map (Syntax_Phases.term_check ~10 "\<phi>variable" (fn ctxt =>
    let val cnt = Counter.make ()
     in map (fn term => if need_translate term
                        then translate_procedure cnt term
                        else term) end))
)

end