(*Probe (2026-09-09, code review 1, FCT-FASTFORCE-GOAL-ONE): the on-the-spot
  obligation instance must accept an obligation the "G.simpcut" pass discharges
  outright -- a zero-premise state, on which fast_force_tac 1 used to fail -- and one
  that fastforce must actually prove.  The zero-premise state needs a guard that
  oblg_template's own rewrite cannot close (else the TrueI exit takes it) but the
  pass can, once the aux facts are inserted: an axiom-like fact declared [useful].*)
theory Solve_Obligation_Now_Probe
  imports Phi_Logic_Programming_Reasoner.PLPR
begin

consts f :: \<open>nat \<Rightarrow> nat\<close>
axiomatization where f0: \<open>f 0 = 1\<close>
declare f0[useful]

ML \<open>
local
  val ctxt = \<^context>
  fun state prop = Thm.trivial (Thm.cterm_of ctxt prop)
  fun probe name prop =
    case Seq.pull (solve_obligation_now ctxt (state prop)) of
      SOME (th, _) => if Thm.no_prems th then writeln (name ^ ": solved")
                      else error (name ^ ": premises left")
    | NONE => error (name ^ ": empty")
  (*the pre-fix instance: fast_force_tac on subgoal 1 only*)
  val pre_fix = Phi_Reasoners.guard_condition_solver (K ()) (fn _ => fn ctxt => fn _ => fn (ctxt0, th) =>
      Phi_Reasoners.try_prove_or_give_up NONE (fn ctxt => Clasimp.fast_force_tac ctxt 1)
          (Phi_Guard_Cache.Guard_Simp_SS.enhance ctxt) th
      |> Seq.map (pair ctxt0)) {can_inst = true}
  val simp_closes = \<^prop>\<open>\<premise> (f 0 = 1)\<close>
  (*simp cannot close this one (no rule instantiates the witness); classical
    reasoning can*)
  val needs_fastforce = \<^prop>\<open>\<premise> (p (a::nat) \<longrightarrow> (\<exists>x. p x))\<close>
  (*the same factory with a solving tactic that does nothing: solved iff the
    pass had already closed the guard*)
  val pass_only = Phi_Reasoners.guard_condition_solver (K ()) (fn _ => fn ctxt => fn _ => fn (ctxt0, th) =>
      Phi_Reasoners.try_prove_or_give_up NONE (K all_tac) ctxt th |> Seq.map (pair ctxt0)) {can_inst = true}
in
(*"G.simpcut" closes this one only after the aux fact is inserted: the state reaching
  the solving function has no premises*)
val _ = probe "simp-closes" simp_closes
(*fastforce has to work*)
val _ = probe "fastforce-needed" needs_fastforce
(*the controls: the defect the review found, and that the second guard really
  reaches the solving function unsolved*)
val _ = case Seq.pull (pre_fix (ctxt, state simp_closes)) of
          NONE => writeln "control 1: the pre-fix instance is empty, as the review said"
        | SOME _ => error "control 1: the pre-fix instance solved it after all"
val _ = case Seq.pull (pass_only (ctxt, state needs_fastforce)) of
          NONE => writeln "control 2: the pass alone leaves the second guard open"
        | SOME _ => error "control 2: the pass alone closed the second guard"
end
\<close>

end
