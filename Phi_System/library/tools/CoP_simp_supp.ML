signature PHI_COP_SIMP_FWD = sig
include PHI_COP_SIMP

(* invoke the simplification if needed *)

val invoke_when_needed : Phi_Working_Mode.working_mode -> context_state -> context_state option
val force_invoke : Phi_Working_Mode.working_mode -> context_state -> context_state (*no matter if is needed*)

end

structure Phi_CoP_Simp : PHI_COP_SIMP_FWD = struct
open Phi_CoP_Simp

(* invoke the simplification if needed *)

fun force_invoke mode (ctxt, sequent) =
  let val sequent' = @{thm' \<A>simp_invoke} RS (sequent RS' (ctxt, #transformation_rule mode))
   in Phi_Reasoner.reason1 (fn () => "Simplification fails") NONE (SOME 1) (ctxt, sequent')
  end

fun invoke_when_needed mode (s as (ctxt, sequent)) =
  let val assertion = #spec_of mode (Thm.prop_of sequent)
   in if is_simp_needed (Context.Proof ctxt) [] assertion
   then (Phi_Reasoner.info_print ctxt 2 (fn () => "Invoking transformation-based simplification...");
         SOME (force_invoke mode s))
   else NONE
  end

end