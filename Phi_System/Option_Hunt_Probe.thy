(*TEMPORARY (`exception Option` hunt, 2026-08-14, user-approved).  Delete this
  file and its ROOT entry when the hunt is over.  See
  OPTION_EXCEPTION_IN_PROOF_REPLAY.md.

  Two jobs:

  (1) Positive control for the instrumentation.  The hunt only works if this
      session's `ML_debugger = true` really reaches ML compilation; without it
      Poly/ML has no stack and every trace comes out empty, which is
      indistinguishable from "the bug did not fire".  The chain below raises on
      purpose and prints its own trace, so every build says out loud whether
      instrumentation is live.  `warning` rather than `tracing`: a batch build
      echoes messages only for a failing command, and warnings besides.

  (2) Round marker.  Bumping the number below changes this session's sources,
      which is what makes the next build actually re-run the session.  Do NOT
      use `isabelle build -f` for that -- `-f` rebuilds the whole dependency
      chain including Pure and HOL, not just the selected session.*)

theory Option_Hunt_Probe
  imports Main
begin

ML \<open>
(*hunt round: 023*)

structure Option_Hunt_Probe =
struct

exception PROBE

fun probe_level3 (_: int) = raise PROBE
fun probe_level2 x = probe_level3 x + 1
fun probe_level1 x = probe_level2 x * 2

end

(*Two API notes, both established by experiment:
  - the mechanism that works here is the ML debugger's exit-exception hook,
    which is what the ML_exception_debugger option drives.  Exn.trace (i.e.
    PolyML.Exception.traceException, driven by ML_exception_trace) never fires
    its handler in this Poly/ML build.
  - write to a file rather than warning/tracing: a batch build echoes neither
    for a session that SUCCEEDS.  The real hunt is unaffected -- when the bug
    fires the session fails, and a failing command's messages are echoed.*)
val _ =
  let val (trace, _) =
        Exn_Debugger.capture_exception_trace (fn () => Option_Hunt_Probe.probe_level1 0)
   in File.write (Path.explode
        "/tmp/claude-1002/-home-qiyuan-Current-MLML/56cf938b-46d8-427e-820a-4029f66b2669/scratchpad/option_hunt/probe_trace.txt")
        (cat_lines ("frames = " ^ string_of_int (length trace) ::
                    map (fn (name, _) => "  " ^ name) trace))
  end
\<close>

end
