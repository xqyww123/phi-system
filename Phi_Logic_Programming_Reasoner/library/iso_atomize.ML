signature PHI_HELPER_CONV = sig

val atomize_conv : Proof.context -> conv
val rulify_conv  : Proof.context -> conv
val atomize : Proof.context -> thm -> thm
val rulify  : Proof.context -> thm -> thm

end

structure Phi_Helper_Conv : PHI_HELPER_CONV = struct

structure Atomize = Named_Thms(
  val name = \<^binding>\<open>iso_atomize_rules\<close>
  val description = "Isomorphic atomiz rules"
)

structure Rulify = Named_Thms(
  val name = \<^binding>\<open>iso_rulify_rules\<close>
  val description = "Isomorphic rulify rules"
)

val _ = Theory.setup (fn thy => thy
|> Atomize.setup
|> Rulify.setup
)

fun atomize_conv ctxt = Raw_Simplifier.rewrite ctxt true (Atomize.get ctxt);
fun rulify_conv  ctxt = Raw_Simplifier.rewrite ctxt true (Rulify.get ctxt);
val atomize = Conv.fconv_rule o atomize_conv
val rulify  = Conv.fconv_rule o rulify_conv

end
