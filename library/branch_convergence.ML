structure Nu_BrCon_Simplify = struct

fun simp_ex _ _ tm =
  (case Thm.term_of tm of (_ $ _
          $ (Const(@{const_name ExSet}, Type("fun",[Type("fun",[ty1,_]),_])) $ _)
          $ (Const(@{const_name ExSet}, Type("fun",[Type("fun",[ty2,_]),_])) $ _))
        => SOME (Conv.rewrs_conv (if ty1 = ty2 then @{thms ExSet_if_simu}
              else @{thms ExSet_if_right ExSet_if_left}) tm)
    | _ => SOME (Conv.rewrs_conv @{thms ExSet_if_right ExSet_if_left} tm))
  handle CTERM _ => NONE

val simp_ex_proc = Raw_Simplifier.cert_simproc @{theory} "ExSet_BrCon"
    {lhss = map Logic.varify_global
            [@{term "if P then (ExSet A) else B"},
             @{term "if P then A else (ExSet B)"}], proc = simp_ex}

fun simp_subj _ _ tm =
  (case Thm.term_of (@{print} tm) of (_ $ _
          $ (Const(@{const_name Subjection}, _) $ _ $ Q1)
          $ (Const(@{const_name Subjection}, _) $ _ $ Q2))
        => SOME (Conv.rewrs_conv (if Q1 aconv Q2 then @{thms Subj_simu}
              else @{thms Subj_left Subj_right}) tm)
    | _ => SOME (Conv.rewrs_conv @{thms Subj_left Subj_right} tm))
  handle CTERM _ => NONE

val simp_subj_proc = Raw_Simplifier.cert_simproc @{theory} "Subjection_BrCon"
    {lhss = map Logic.varify_global
            [@{term "if P then Subjection A Q else B"},
             @{term "if P then A else Subjection B Q"}], proc = simp_subj}

end
