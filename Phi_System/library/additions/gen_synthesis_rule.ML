signature PHI_SYNTHESIS = sig

val gen_rule : Proof.context -> thm -> thm
val declare_rule : Position.T -> int -> term list * term list
                -> thm -> Context.generic -> Context.generic

end

structure Phi_Synthesis : PHI_SYNTHESIS = struct

fun gen_rule ctxt proc_thm0 =
  let val proc_thm = case Thm.concl_of proc_thm0
                       of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>All\<close>, _) $ _) => proc_thm0
                        | _ => Procedure_Syntax.package_argument ctxt proc_thm0
      val idx = Thm.maxidx_of proc_thm + 1
      val rule = Thm.instantiate (TVars.empty,
                                  Vars.make [((("G",0),\<^typ>\<open>prop\<close>), Thm.cprop_of proc_thm),
                                             ((("R",0),\<^typ>\<open>prop\<close>), Thm.var (("R", idx), \<^ctyp>\<open>prop\<close>))])
                     @{thm Gen_Synthesis_Rule}
   in (ctxt, Thm.implies_elim rule proc_thm)
   |> Phi_Reasoner.reason NONE
   |> (fn SOME (_, sequent) => sequent
        | NONE => Phi_Reasoner.error "Fail to extract the synthesis rule.")
   |> Raw_Simplifier.rewrite_rule ctxt @{thms conjunction_imp PURE_TOP_imp}
   |> Thm.solve_constraints
   |> (fn sequent => (
            Phi_Reasoner.info_pretty ctxt (fn () => Pretty.chunks [
                  Pretty.para "Obtain synthesis rule:",
                  Thm.pretty_thm ctxt sequent
                ]);
            sequent))
  end

structure Pattern = Pattern_Translation(
  val multi_translation_err_msg = "Bad configure in \<open>generate_pattern_of_synthesis_rule\<close>: \
        \Clash of multiple translation"
)

val _ = Theory.setup (Pattern.setup_attribute \<^binding>\<open>generate_pattern_of_synthesis_rule\<close>
    "generated_rule &&& TERM user_given_pattern\<close> \<Rightarrow> \<open>pattern of the antecedents that the reasoner binds on\<close>")

fun declare_rule pos priority (patterns0,blacklist0) proc_thm0 ctxt0 =
  let val ctxt = Context.proof_of ctxt0
      val proc_thm = Drule.zero_var_indexes (gen_rule ctxt proc_thm0)
      val concl = Thm.concl_of proc_thm
      fun pat_of P =
            case Pattern.translate ctxt0 (Logic.mk_conjunction (concl, Logic.mk_term P))
              of SOME pattern => pattern
               | NONE => error "Cannot infer the pattern of the antecedent to be bound.\n\
                  \Some translation rule for giving the pattern may be required, and can be decalred\
                  \ by \<open>declare [[generate_pattern_of_synthesis_rule \<dots> \<Rightarrow> \<dots>]].\<close>"
      val patterns = map pat_of (if null patterns0 then [\<^term>\<open>()\<close>] else patterns0)
      val blacklist = map pat_of blacklist0
      val _ = Phi_Reasoner.debug_pretty ctxt (fn () => Pretty.chunks ([
                Pretty.str "The rule is bound on pattern(s):",
                Pretty.chunks (map (fn X => Pretty.item [Syntax.pretty_term ctxt X]) patterns)] @
                (if null blacklist then [] else [
                Pretty.str "excluding pattern(s):",
                Pretty.chunks (map (fn X => Pretty.item [Syntax.pretty_term ctxt X]) blacklist)
          ])))
   in Phi_Reasoner.add_intro_rule pos priority (patterns,blacklist) NONE [proc_thm] ctxt0
  end



end