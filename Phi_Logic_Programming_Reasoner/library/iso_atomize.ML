signature PHI_CONV = sig
include PHI_CONV

val iso_atomize_conv : Proof.context -> conv
val iso_rulify_conv  : Proof.context -> conv
val iso_atomize : Proof.context -> thm -> thm
val iso_rulify  : Proof.context -> thm -> thm

val atomize_conv : Proof.context -> conv
val atomize : Proof.context -> thm -> thm
val atomize_term : Proof.context -> term -> term
val rulify : Proof.context -> thm -> thm

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
     | _ => raise CTERM ("Fail to atomize", [Thm.dest_arg1 (Thm.cprop_of rule)])

fun chk_term (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = X
  | chk_term X = case Term.fastype_of X
                        of \<^Type>\<open>bool\<close> => X
                         | _ => raise TERM ("Fail to atomize", [X])

fun iso_atomize_conv ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ctm
     | _ => chk (Raw_Simplifier.rewrite ctxt true (Atomize.get ctxt) ctm)
fun iso_rulify_conv  ctxt = Raw_Simplifier.rewrite ctxt true (Rulify.get ctxt)
val iso_atomize = Conv.fconv_rule o iso_atomize_conv
val iso_rulify  = Conv.fconv_rule o iso_rulify_conv

fun atomize_conv ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ctm
     | _ => chk (Object_Logic.atomize ctxt ctm)
val atomize = Conv.fconv_rule o atomize_conv
val atomize_term = chk_term oo Object_Logic.atomize_term
val rulify = Object_Logic.rulify

end
