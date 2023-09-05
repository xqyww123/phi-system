signature SIMPLIFICATION_PROTECT = sig

val protect : Proof.context -> thm -> thm
val unprotect : Proof.context -> thm -> thm

structure Protectors : SIMPSET
structure Un_Protectors : SIMPSET

end

structure Simplification_Protect : SIMPLIFICATION_PROTECT = struct

structure Protectors = Simpset (
  val initial_ss = Simpset_Configure.Give_SS (
        Raw_Simplifier.simpset_of (
          Context.the_local_context ()
            |> Raw_Simplifier.clear_simpset
            |> Simplifier.set_mksimps ( map Thm.symmetric
                                     oo Simpdata.mksimps Simpdata.mksimps_pairs)))
  val binding = NONE
  val comment = "Rewrite rules applied before simplification in order to protect any specific assertion forms"
  val attribute = NONE
  val post_merging = I
)

structure Un_Protectors = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = NONE
  val comment = "Rewrite rules applied after simplification to recovery the protected form"
  val attribute = NONE
  val post_merging = I
)

fun protect ctxt = Simplifier.full_simplify (Protectors.equip ctxt)
fun unprotect ctxt = Simplifier.full_simplify (Un_Protectors.equip ctxt)

fun add_simps thms ctxt = ctxt
      |> Protectors.add_simps thms
      |> Un_Protectors.add_simps thms

fun del_simps thms ctxt = ctxt
      |> Protectors.del_simps thms
      |> Un_Protectors.del_simps thms

val add = Thm.declaration_attribute (fn th => add_simps [th])
val del = Thm.declaration_attribute (fn th => del_simps [th])

val binding = \<^binding>\<open>simplification_protect\<close>
val comment = "Rewrite rules applied before simplification in order to protect any specific\
              \ assertion forms"

fun ss_setup ctxt = ctxt addsimprocs [\<^simproc>\<open>NO_MATCH\<close>]


val _ = Theory.setup (
    Attrib.setup binding (Attrib.add_del add del) comment
 #> Global_Theory.add_thms_dynamic (binding, Protectors.simp_rules o Context.proof_of)
 #> Context.theory_map (
    Protectors.map ss_setup
 #> Un_Protectors.map ss_setup
))

end