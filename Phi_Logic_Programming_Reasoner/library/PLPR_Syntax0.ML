signature PLPR_SYNTAX = sig

val merge_guards (*if the rule contains multiple guards, move them into the beginning and
                   consolidate them into one*) : Proof.context -> thm -> thm

end

structure PLPR_Syntax : PLPR_SYNTAX = struct

val merge_guard_rule = @{lemma \<open>(\<g>\<u>\<a>\<r>\<d> P \<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Q \<Longrightarrow> PROP R) \<equiv> (\<g>\<u>\<a>\<r>\<d> P \<and>\<^sub>\<r> Q \<Longrightarrow> PROP R)\<close>
                            by (unfold \<r>Guard_def Ant_Seq_imp)}

fun merge_guards ctxt rule =
  fold_index (fn (i,prem) => fn (meet, rule) =>
    case Logic.strip_assums_concl prem
      of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _) =>
          if meet = 0
          then (1, Thm.permute_prems 0 i rule)
          else Thm.permute_prems 1 (i-meet) rule
                |> Conv.fconv_rule (Conv.rewr_conv merge_guard_rule)
                |> Thm.permute_prems 1 (~ (i-meet))
                |> pair (meet + 1)
       | _ => (meet, rule)
  ) (Thm.prems_of rule) (0, rule)
  |-> (fn meet =>
    if meet = 0 then I
    else Conv.gconv_rule (Conv.top_rewrs_conv @{thms' Ant_Seq_assoc} ctxt) 1)

(*n merge_guards ctm *)

end