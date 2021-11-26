signature NU_PROCESSORS = sig
  type proc = NuProcessor.proc
  val simplifier : thm list (*simp cong*) -> proc

  (* it loads all aux facts and codeblocks in the spec thm *)
  (* val open_spec : proc -> proc *)
end
structure NuProcessors : NU_PROCESSORS = struct
open NuBasics NuHelp NuProcessor
fun simplifier cong = almost_safe (fn ctx => fn sequent =>
  Scan.succeed (fn _ => let
    val simps = Named_Theorems.get ctx "NuSys.used"
    val ctx = Raw_Simplifier.addsimps (ctx, simps)
    in (Simplifier.full_simplify ctx sequent
        |> (fn th2 => if Thm.eq_thm_prop (sequent, th2) then raise Bypass NONE else th2)
       , ctx) |> @{print}
    end))

end
