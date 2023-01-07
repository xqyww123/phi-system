signature NU_PROCESSORS = sig
  type proc = NuProcessor.proc
  val simplifier :   proc

  (* it loads all aux facts and codeblocks in the spec thm *)
  (* val open_spec : proc -> proc *)
end

structure NuProcessors : NU_PROCESSORS = struct
open Phi_Basics Phi_Help NuProcessor

val simplifier = almost_safe (fn (ctxt, sequent) =>
  Scan.succeed (fn _ => let
    val simps = Named_Theorems.get ctxt \<^named_theorems>\<open>useful\<close>
    val simps'= Named_Theorems.get ctxt \<^named_theorems>\<open>\<phi>programming_simps\<close>
    val ctxt' = Raw_Simplifier.addsimps (ctxt, simps @ simps')
    in raise Bypass (SOME (ctxt, Simplifier.full_simplify ctxt' sequent))
    end))

end
