signature PHI_REASONERS = sig
include PHI_REASONERS

val conv_GE_to_plain_conjunction : Proof.context -> thm -> thm list
val extract_elim_rule : Proof.context -> thm list -> thm -> thm

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

(*If no  disjunction: split the conjunction into a list
  If has disjunction: convert to Disjunctive Normal Form*)
fun conv_GE_to_plain_conjunction ctxt thm =
  let
    val V = case Thm.concl_of thm
      of (\<^const>\<open>Trueprop\<close> $ Var V) => V
       | _ => raise THM ("Not a Generalized Elimination rule", 0, [thm])
    val thm' = Thm.instantiate (TVars.empty, Vars.make [(V, \<^cterm>\<open>CONV_GE\<close>)]) thm
  in
    thm'
      |> Raw_Simplifier.rewrite_rule ctxt @{thms atomize_all atomize_imp atomize_eq atomize_conj CONV_GE_phase_1}
      |> Raw_Simplifier.rewrite_rule ctxt @{thms CONV_GE_Ex_def CONV_GE_phase_2}
      |> Raw_Simplifier.rewrite_rule ctxt @{thms CONV_GE_Ex_def CONV_GE_phase_3}
      |> Conjunction.elim_conjunctions
  end

fun pred_V (SOME V) V' = (V = V') | pred_V NONE _ = true

fun is_elim_rule' V' (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ P $ X)
      =(case Logic.strip_assums_concl P
          of Const (\<^const_name>\<open>Trueprop\<close>, _) $ Var V
               => pred_V V' V andalso is_elim_rule' (SOME V) X
           | _ => false)
  | is_elim_rule' V' (Const (\<^const_name>\<open>Trueprop\<close>, _) $ Var V) = pred_V V' V
  | is_elim_rule' _ _ = false

fun is_elim_rule (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ _) $ X)
      = is_elim_rule' NONE X
  | is_elim_rule _ = false

fun extract_elim_rule ctxt erules thm =
  if is_elim_rule (Thm.prop_of thm)
  then thm
  else (
    Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.chunks [
        Pretty.str "Going to extract elimination rule from:",
        Syntax.pretty_term ctxt (Thm.prop_of thm)
    ]);
    (ctxt, Drule.compose (thm, 1, @{thm Do_Extract_Elimination_Rule}))
      |> Phi_Reasoner.reason NONE
      |> (fn SOME (ctxt', ret) =>
            let val ret' = Tactical.REPEAT_DETERM (Thm.biresolution (SOME ctxt') false
                              (map (pair true) erules) 2) ret
                        |> Seq.pull
                        |> (fn SOME (x, _) => x
                             | NONE => error "Internal bug!#q3f4j89[")
                val _ = Phi_Reasoner.info_pretty ctxt (fn _ => Pretty.chunks [
                      Pretty.str "Obtained the following elimination rule:",
                      Syntax.pretty_term ctxt (Thm.prop_of ret')
                  ])
             in ret' end
           | NONE => Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
                Pretty.str "Fail to extract elimination rule from:",
                Syntax.pretty_term ctxt (Thm.prop_of thm)
               ])))
)


end