signature PHI_REASONERS = sig
include PHI_REASONERS

val extract_elim_rule : Proof.context -> thm list -> thm -> thm

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

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

fun extract_elim_rule ctxt0 erules thm0 =
  if is_elim_rule (Thm.prop_of thm0)
  then thm0
  else
    let val ((_,[thm]),ctxt) = Variable.import true [thm0] ctxt0
        val _ = Phi_Reasoner.info_pretty ctxt 1 (fn _ => Pretty.chunks [
                  Pretty.str "Going to extract elimination rule from:",
                  Syntax.pretty_term ctxt0 (Thm.prop_of thm0)
              ])
     in (ctxt, Drule.compose (thm, 1, @{thm Do_Extract_Inhabitance_Rule}))
      |> Phi_Reasoner.reason NONE
      |> (fn SOME (ctxt', ret) =>
            let val ret' = Tactical.REPEAT_DETERM (Thm.biresolution (SOME ctxt') false
                              (map (pair true) erules) 2) ret
                        |> Seq.pull
                        |> (fn SOME (x, _) => x
                             | NONE => error "Internal bug!#q3f4j89[")
                        |> singleton (Variable.export ctxt' ctxt0)
                        |> Drule.zero_var_indexes
                val _ = Phi_Reasoner.info_pretty ctxt' 1 (fn _ => Pretty.chunks [
                      Pretty.str "Obtained the following elimination rule:",
                      Syntax.pretty_term ctxt' (Thm.prop_of ret')
                  ])
             in ret' end
           | NONE => Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
                Pretty.str "Fail to extract elimination rule from:",
                Syntax.pretty_term ctxt0 (Thm.prop_of thm0)
               ])))
    end


end