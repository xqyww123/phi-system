signature PHI_SYS_REASONERS = sig

val is_user_dependent_antecedent : term -> bool
val is_proof_obligation : term -> bool

end

structure Phi_Sys_Reasoner : PHI_SYS_REASONERS = struct

fun is_user_dependent_antecedent (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Argument\<close>, _) $ _ ) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Do\<close>, _) $ _ ) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>ParamTag\<close>, _) $ _ ) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (\<^Const>\<open>Pure.all ty\<close> $ X) =
      is_user_dependent_antecedent (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, _, X)) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (\<^Const>\<open>HOL.All ty\<close> $ X) =
      is_user_dependent_antecedent (\<^Const>\<open>HOL.All ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Labelled\<close>, _) $ _ $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Technical\<close>, _) $ X) = is_user_dependent_antecedent X
(*  | is_user_dependent_antecedent (Const(\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ Abs (_, _, X)) = is_user_dependent_antecedent X *)
  | is_user_dependent_antecedent _ = false

fun is_proof_obligation (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_proof_obligation X
  | is_proof_obligation (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>default\<close>, _) $ _) = true
  | is_proof_obligation (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _) = true
  | is_proof_obligation _ = false

end


