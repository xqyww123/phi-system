signature NU_PROCESSORS = sig
  type proc = NuProcessor.proc
  val simplifier : thm list (*simp cong*) -> proc

  (* it loads all aux facts and codeblocks in the spec thm *)
  (* val open_spec : proc -> proc *)
end

structure NuProcessors : NU_PROCESSORS = struct
open NuBasics NuHelp NuProcessor

fun simplifier cong = almost_safe (fn (ctxt, sequent) =>
  Scan.succeed (fn _ => let
    val simps = Named_Theorems.get ctxt \<^named_theorems>\<open>useful\<close>
    val simps'= Named_Theorems.get ctxt \<^named_theorems>\<open>\<phi>programming_simps\<close>
    val ctxt' = Raw_Simplifier.addsimps (ctxt, simps @ simps')
    in (ctxt,
        Simplifier.full_simplify ctxt' sequent
          |> (fn th2 => if Thm.eq_thm_prop (sequent, th2) then raise Bypass NONE else th2))
    end))

end
