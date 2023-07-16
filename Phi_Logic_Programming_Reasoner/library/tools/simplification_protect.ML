signature SIMPLIFICATION_PROTECT = sig

val protect : Proof.context -> thm -> thm
val unprotect : Proof.context -> thm -> thm

structure Protections : NAMED_THMS

end

structure Simplification_Protect : SIMPLIFICATION_PROTECT = struct

structure Protections = Named_Thms (
  val name = \<^binding>\<open>simplification_protect\<close>
  val description = "Rewrite rules applied before simplification in order to protect any specific\
                    \ assertion forms. The rules must be in meta rewrite form, i.e. \<open>LHS \<equiv> RHS\<close>."
)

fun protect ctxt = Raw_Simplifier.rewrite_rule ctxt (Protections.get ctxt |> map Thm.symmetric)
fun unprotect ctxt = Raw_Simplifier.rewrite_rule ctxt (Protections.get ctxt)

val _ = Theory.setup Protections.setup

end