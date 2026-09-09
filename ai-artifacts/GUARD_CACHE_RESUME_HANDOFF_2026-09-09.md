# Handoff: guard cache implementation — steps P, 0, 1 done and ACCEPTED after code review (2026-09-09, 14:10 UTC+8)

Supersedes the 09-08 handoff.  "开工" was given 2026-09-09.  The plan is
`contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` **rev 23**; §26 records
step P's acceptance ("验收通过") and step 0's anchor re-verification; §27 records
step 1; §28 the first code review's fixes; §29 the re-review: ACCEPTED.  Archive `.rev22.md` beside it.

## State
- **Step P (preparatory phase)**: DONE and accepted.  ssymb.ML in Pure; `MESSAGE_PACK`;
  `RPC_Term_Codec` functor in `Isabelle_RPC/Tools/pretty.ML`; `RPC_Pretty_Bytes`;
  Isa-Mini's `agent_packer.ML` applies the functor; `Isabelle_RPC/test/Test_Term_Codec.thy`
  in `Isabelle_RPC_Test`.  Heaps rebuilt by the author.
- **Step 0**: DONE — ~220 anchors re-verified by three agents + drafter; 15 corrected.
- **Step 1**: DONE, code-reviewed (wf_d8746808-6c8: 1 MAJOR + 6 MINOR fixed; relaxations A `Tactic_Configures.invoke`, B `Seq.take 1` on "G.simpcut" accepted by the author), re-reviewed ACCEPTED (wf_61cf82c2-9ce).  Rebuild from Performant_Isabelle_HOL up done 2026-09-09 (the author approved the drafter running builds for this).  Files: `auto_sledgehammer/library/Hasher.ML`
  (`terms`), `sledgehammer_solver.ML` (interrupt clause; `auto_sledgehammer_trace_replay`),
  `phi-system/Phi_Logic_Programming_Reasoner/PLPR.thy` (`Guard_Budget`, `ML_file
  library/guard_cache.ML` after `reasoner.ML`, method `\<phi>guard_P_auto`, the two
  `\<condition>` registrations on `guard_condition_judge … o snd`, `defer_premise` on
  `solve_obligation_now`, `hide_const (open) Guard_Budget`), NEW `library/guard_cache.ML`
  (`Phi_Guard_Cache`), `library/guard_refute.ML` (`Nitpick_Refute_SS`),
  `library/reasoners.ML` (factory `guard_condition_solver digest_of solve {can_inst}
  (ctxt0, th)`, `guard_condition_judge`, `prove_or_refute` in its final type wrapping
  the TRANSITIONAL race `guard_race`, `apply_tac prj …`, `head_only'`, `oblg_template …
  {inj, on_thm}`, `enhance_for_guard`, `simpcut_tac`, `p_auto_body`,
  `try_prove_or_give_up`, `guard_classic_prover_timeout`/`_bound`, the two warning
  functions).  Evidence: PLPR.thy clean under MCP on Performant_Isabelle_HOL; author's
  rebuild `isabelle build -b Minilang_AoA Phi_System_Base` passed; PhiTest_Arithmetic.thy
  clean under MCP on Phi_System_Base with 175 guard_race records through the new factory.
- The MCP prover is on `Phi_System_Base` (session_dirs /home/qiyuan/Current/MLML).

## Drafter decisions (reported; the author raised no objection)
`auto_sledgehammer_trace_replay`; structure `Phi_Guard_Cache`; internal names
`enhance_for_guard`, `simpcut_tac`, `solve_obligation_now`, `p_auto_solving`, `guard_race`;
hook priority 200; the loud warning's text; `prj` only on `apply_tac` and `oblg_template`
taking `{inj, on_thm}`; the digest step typed `thm -> 'd` (judge: `guard_digest`; others `K ()`).

## Next: step 2 (plan §10)
`prove_or_refute` over `context_state` with the sequential protocol of §5 and an
in-memory table (test-injected `Symtab`) in place of the store; `guard_decision`
record behind `\<phi>log_guard_decision` (rename of `\<phi>log_guard_race`; delete the
`\<phi>log_guard_race = true` clause at PLPR.thy's `declare [[…]]`, keep
`\<phi>log_guess_inst = true`); remove `Race.race`, the racers, `\<phi>guard_race_timeout`,
the 35 ms gate; rewrite the `nitpick_params` note ("inside a racer body");
`Test/Guard_Race_Smoke.thy` reshaped around `guard_decision` (its :79 call migrates);
every path of §5 exercised.  Steps 1 and 4 needed rebuild approvals; step 2 changes
only phi-system files (loaded from source under Phi_System_Base) — no rebuild.

## Rules (unchanged)
No `isabelle build` without approval (the author runs them); edit source with the Edit
tool (author 2026-09-09: "建议你最好用 Edit tool 去编辑源码"); plan docs by hand; never
coin words; explain in Chinese, essence first; commit only when told, push origin only;
memory writes need approval; probes never load phi-system theories under new names.

## Uncommitted
Everything above plus the plan + archives rev11–rev22, ai-artifacts, Hasher.ML comment
deletion, Semantic_Embedding cleanup scripts.  Other agents' uncommitted edits exist in
Performant_Isabelle_ML (`accounted_timeout.ML`, `race.ML`) and Isa-Mini.
