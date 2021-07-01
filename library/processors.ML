signature NU_PROCESSORS = sig
  type proc = NuProcessor.proc
  val simplifier : proc
end
structure NuProcessors : NU_PROCESSORS = struct
open NuProcessor
val simplifier = almost_safe (fn ctx => fn th =>
  Simplifier.simplify ctx th |> (fn th2 =>
    if Thm.eq_thm_prop (th, th2) then raise Bypass else Scan.succeed th2))
end
