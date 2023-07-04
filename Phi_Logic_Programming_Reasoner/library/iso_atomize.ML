signature PHI_CONV = sig
include PHI_CONV

val atomize_conv : Proof.context -> conv
val rulify_conv  : Proof.context -> conv
val atomize : Proof.context -> thm -> thm
val rulify  : Proof.context -> thm -> thm

end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

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

fun chk rule =
  case Thm.prop_of rule
    of _ (*Pure.eq*) $ _ $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ _) => rule
     | _ (*Pure.eq*) $ LHS $ _ => raise TERM ("atomize or rulify fails", [LHS])
     | _ => error "Internal bug"

fun atomize_conv ctxt ctm = chk (Raw_Simplifier.rewrite ctxt true (Atomize.get ctxt) ctm)
fun rulify_conv  ctxt = Raw_Simplifier.rewrite ctxt true (Rulify.get ctxt)
val atomize = Conv.fconv_rule o atomize_conv
val rulify  = Conv.fconv_rule o rulify_conv

end
