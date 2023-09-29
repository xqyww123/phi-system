signature PLPR_RULE_GEN = sig

structure Template_Inst_SS : SIMPSET (*simpset for generating reasoning rules*)
structure Template_Inst_SS_Post_Merging : HOOKS

val pass_generated_rule : {simp: bool, masks: IN_Arg.mask list option (*can be None by default*)}
                       -> Proof.context -> thm -> thm

end

structure PLPR_Rule_Gen : PLPR_RULE_GEN = struct

structure Template_Inst_SS_Post_Merging = Hooks (
  type arg = unit
  type state = Proof.context
)

structure Template_Inst_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>simp_for_\<phi>TA_rule_generation\<close>
  val comment = "Rules simplifying the reasoning rules instantiated from templates."
  val attribute = NONE
  fun post_merging ctxt = ctxt
        |> Simplifier.del_cong @{thm' if_weak_cong}
        |> Simplifier.add_cong @{thm' if_cong}
        |> Template_Inst_SS_Post_Merging.invoke (Context.Proof ctxt) ()
)

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes

fun pass_generated_rule {simp, masks} ctxt rule =
  let val rule'1 = case Thm.concl_of rule
                     of Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ _ => rule
                      | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ _) => rule
                      | _ => rule RS' (ctxt, @{thm' NO_SIMP'_I})
      val ((_, [rule'2]), ctxt'1) = Variable.import false [rule'1] ctxt
      val ctxt's = Template_Inst_SS.enhance ctxt'1
                |> Simplifier.del_cong @{thm' HOL.if_weak_cong}
      val rule'3 = rule'2
                |> simp ? ( Simplification_Protect.protect ctxt's
                         #> Phi_Reasoners.asm_lr_simplify true ctxt's
                         #> Simplification_Protect.unprotect ctxt's )
                |> singleton (Variable.export ctxt'1 ctxt)
                |> Phi_Help.unique_flexflex ctxt
   in (case Phi_Help.instantiate_higher_order_schematic_var_for_rule_guess' (~1, the_default [] masks) ctxt rule'3
         of SOME th => simplify ctxt th
          | NONE => rule'3)
   |> Simplifier.rewrite_rule ctxt @{thms' NO_SIMP_def NO_SIMP'_def template_NO_SIMP_USE_def}
   |> PLPR_Syntax.merge_guards {merge_cond=true} ctxt
   |> normalize
  end

val _ = Theory.setup (
  let fun rule_attribute f (x, th) =
              if Thm.is_free_dummy th
              then (NONE, NONE)
              else (SOME x, SOME (f x th))
   in Attrib.setup \<^binding>\<open>\<phi>simplify_reasoning_rule\<close> (
      Scan.succeed (rule_attribute (pass_generated_rule {simp=true, masks=NONE} o Context.proof_of)))
    "Simplify a reasoning rule, using the same process as that in template instantiation.\n\
    \The conclusion of the rule is remained untouched and any antecedents are simplified and reduced\
    \if possible. \<open>NO_SIMP\<close> tag is recognized and supresses the simplification on the protected terms."
  end
)

end