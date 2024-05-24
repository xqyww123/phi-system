signature PHI_SYS = sig

  val move_lemmata : Position.T -> context_state -> context_state
  structure Lemmata_Processors : HOOKS
  val add_lemmata : Position.T -> thm list -> Proof.context -> Proof.context

end

structure Phi_Sys : PHI_SYS = struct

structure Lemmata_Processors = Hooks (
  type arg = Position.T
  type state = {
        input   : thm list,
        lemmata : thm list,
        useful  : thm list,
        rules   : Phi_Reasoner.add_rule_param list,
        ctxt    : Proof.context
    }
)

fun add_lemmata pos lemmas ctxt =
  let fun filter_lemma th =
        case Thm.prop_of th
          of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>USELESS\<close> $ _) => NONE
           | \<^const>\<open>Trueprop\<close> $ \<^const>\<open>True\<close> => NONE
           | _ => SOME th
      val lemmas = lemmas
                |> maps PLPR_Syntax.elim_ant_sequence_or_HOL_conj
                |> map_filter filter_lemma
                |> maps (Phi_Envir.process_useful_lemmata true ctxt)
      val {lemmata, useful, rules, ctxt, ...} =
                Lemmata_Processors.invoke (Context.Proof ctxt) pos
                  {input=lemmas, lemmata=[], useful=[], rules=[], ctxt=ctxt}
   in ctxt
   |> not (null lemmata) ? Context.proof_map (fold (Named_Theorems.add_thm \<^named_theorems>\<open>\<phi>lemmata\<close>) lemmas)
   |> not (null useful)  ? Context.proof_map (fold Useful_Thms.add_thm lemmas)
   |> not (null rules)   ? Context.proof_map (Phi_Reasoner.add_rules rules)
  end

val _ = Theory.setup (Context.theory_map (Lemmata_Processors.add 1000 (
  fn _ => fn {input, lemmata, useful, rules, ctxt} =>
    let fun is_useful (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_useful X
          | is_useful (Const(\<^const_name>\<open>Satisfiable\<close>, _) $ _) = false
          | is_useful _ = true
        val useful = filter (is_useful o Thm.concl_of) input @ useful
        val lemmata = input @ lemmata
     in {input=[], lemmata=lemmata, useful=useful, rules=rules, ctxt=ctxt}
    end
)))

fun move_lemmata' pos (ctxt, sequent) =
      (add_lemmata pos [sequent RS @{thm conjunct2}] ctxt,
       sequent RS @{thm conjunct1})

fun move_lemmata pos (ctxt, sequent) =
  case Thm.prop_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>conj\<close> $ _ $ _) => move_lemmata pos (move_lemmata' pos (ctxt, sequent))
     | _ => (ctxt, sequent)


end
