signature PHI_SYNTAX = sig

val is_elim_rule : term -> bool

end

structure Phi_Syntax : PHI_SYNTAX = struct

fun is_elim_rule term =
  let val \<^const>\<open>Trueprop\<close> $ C = Logic.strip_imp_concl term
      val (\<^const>\<open>Trueprop\<close> $ _) :: Ps = Logic.strip_imp_prems term
   in is_Free C andalso forall (fn P => Logic.strip_imp_concl P = C) Ps
  end
  handle Bind => false

end
