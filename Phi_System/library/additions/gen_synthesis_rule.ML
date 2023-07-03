signature PHI_SYNTHESIS = sig

datatype pattern = Arg_and_Ret of term * term | Ret_only of term | No_Pattern

val gen_rule : Proof.context -> thm -> thm
val declare_rule : Position.T
                -> Phi_Reasoner.priority
                -> (pattern * Phi_Reasoner.priority option) list * pattern list
                -> thm -> Context.generic -> Context.generic

end

structure Phi_Synthesis : PHI_SYNTHESIS = struct

fun gen_rule ctxt proc_thm0 =
  let val proc_thm = case Thm.concl_of proc_thm0
                       of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>All\<close>, _) $ _) => proc_thm0
                        | _ (*Trueprop*) $ (Const (\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _)
                            => Procedure_Syntax.package_argument ctxt proc_thm0
                        | _ => proc_thm0
      val idx = Thm.maxidx_of proc_thm + 1
      val rule = Thm.instantiate (TVars.empty,
                                  Vars.make [((("G",0),\<^typ>\<open>prop\<close>), Thm.cprop_of proc_thm),
                                             ((("R",0),\<^typ>\<open>prop\<close>), Thm.var (("R", idx), \<^ctyp>\<open>prop\<close>))])
                     @{thm Gen_Synthesis_Rule}
   in Thm.implies_elim rule proc_thm
   |> Phi_Reasoner.reason1 (fn () => "Fail to extract the synthesis rule.") NONE ctxt
   |> Raw_Simplifier.rewrite_rule ctxt @{thms conjunction_imp PURE_TOP_imp}
   |> Thm.solve_constraints
   |> (fn sequent => (
            Phi_Reasoner.info_pretty ctxt 1 (fn () => Pretty.chunks [
                  Pretty.para "Obtain synthesis rule:",
                  Thm.pretty_thm ctxt sequent
                ]);
            sequent))
  end

structure Pattern = Pattern_Translation(
  val parse_pattern = Syntax.parse_prop
  val check_pattern = Syntax.check_props
  val multi_translation_err_msg = "Bad configure in \<open>generate_pattern_of_synthesis_rule\<close>: \
        \Clash of multiple translation"
)

val _ = Theory.setup (Pattern.setup_attribute \<^binding>\<open>generate_pattern_of_synthesis_rule\<close>
    "generated_rule &&& TERM user_given_pattern\<close> \<Rightarrow> \<open>pattern of the antecedents that the reasoner binds on\<close>")

datatype pattern = Arg_and_Ret of term * term | Ret_only of term | No_Pattern

(*  Procedure_Syntax.package_values ""  *)

fun pack _    f (Abs (N,TY,X)) = Abs (N,TY, f X)
  | pack flag f term =
      case Phi_Help.safe_fastype_of term
        of \<^Type>\<open>fun T _\<close> => Abs ("", T, f (term $ Bound 0))
         | _ => if flag
                then snd (Procedure_Syntax.package_values "" true NONE (f term))
                else f term

fun encode_pattern _    No_Pattern = \<^term>\<open>TERM ()\<close>
  | encode_pattern _    (Ret_only term) = Logic.mk_term (pack true I term)
  | encode_pattern flag (Arg_and_Ret (arg,ret)) =
      let val idx = Int.max (maxidx_of_term arg, maxidx_of_term ret) + 1
          val R = Var(("R",idx), \<^typ>\<open>assn\<close>)
          fun prepend_R ((H as Const (\<^const_name>\<open>times\<close>, _)) $ A $ B) = H $ prepend_R A $ B
            | prepend_R X = Const(\<^const_name>\<open>times\<close>, \<^typ>\<open>assn \<Rightarrow> assn \<Rightarrow> assn\<close>) $ R $ X
       in Logic.mk_conjunction (Logic.mk_term (pack flag prepend_R arg),
                                Logic.mk_term (pack true I ret))
      end

fun declare_rule pos priority (patterns0,blacklist0) proc_thm0 ctxt0 =
  let val ctxt = Context.proof_of ctxt0
      val proc_thm = Drule.zero_var_indexes (gen_rule ctxt proc_thm0)
      val concl = Thm.concl_of proc_thm
      fun pat_of P =
            case Pattern.translate ctxt0 (Logic.mk_conjunction (concl, encode_pattern false P))
              of h::L => h::L
               | [] => (
            case Pattern.translate ctxt0 (Logic.mk_conjunction (concl, encode_pattern true P))
              of h::L => h::L
               | [] => error "Cannot infer the pattern of the antecedent to be bound.\n\
                  \Some translation rule for giving the pattern may be required, and can be decalred\
                  \ by \<open>declare [[generate_pattern_of_synthesis_rule \<dots> \<Rightarrow> \<dots>]].\<close>")
      val patterns = maps (fn (P,prio) => map (rpair prio) (pat_of P))
                          (if null patterns0 then [(No_Pattern, NONE)] else patterns0)
      val blacklist = maps pat_of blacklist0
      val _ = Phi_Reasoner.info_pretty ctxt 1 (fn () => Pretty.chunks ([
                Pretty.str "The rule is bound on pattern(s):",
                Pretty.chunks (map (fn (X,N) => Pretty.item [
                      Pretty.str "(", Pretty.str (string_of_int (the_default priority N)), Pretty.str "): ",
                      Syntax.pretty_term ctxt X
                    ]) patterns)] @
                (if null blacklist then [] else [
                Pretty.str "excluding pattern(s):",
                Pretty.chunks (map (fn X => Pretty.item [Syntax.pretty_term ctxt X]) blacklist)
          ])))
   in Phi_Reasoner.add_intro_rule pos (Phi_Reasoner.default_mode_of priority) priority
                                  (patterns, blacklist) NONE [proc_thm] ctxt0
  end



end