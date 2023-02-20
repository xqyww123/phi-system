signature PLPR_RECURSION_GUARD = sig
val reason : context_state -> context_state Seq.seq
end

structure PLPR_Recursion_Guard : PLPR_RECURSION_GUARD = struct

fun reason (ctxt,sequent) = Seq.make (fn () =>
  let val _ (*Pure.imp*) $ Ant0 $ Remains = Thm.prop_of sequent
      val _ $ X $ _ = Logic.strip_assums_concl (Envir.beta_eta_contract Ant0)
      fun chk (Const (\<^const_name>\<open>\<r>Recursion_Residue\<close>, _) $ Y) =
            not (Envir.beta_eta_contract Y aconv X)
        | chk (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ A $ B) =
            chk A andalso chk B
        | chk (Const (\<^const_name>\<open>Pure.all\<close>, _) $ B) = chk B
        | chk (Abs (_,_,B)) = chk B
        | chk (Const (\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk X
        | chk _ = true
   in if chk Remains
      then SOME ((ctxt, @{thm Do_\<r>Recursion_Guard} RS sequent), Seq.empty)
      else (Phi_Reasoner.debug_print ctxt (fn () =>
              "\<r>Recursion_Guard: Cut because of infinite recursion!");
            NONE)
  end)

end