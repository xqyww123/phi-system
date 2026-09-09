# Handoff: guard cache implementation — steps P, 0, 1 done, reviewed, ACCEPTED, COMMITTED; step 2 next (2026-09-09, 14:30 UTC+8)

Supersedes the 09-08 handoff.  Plan: `contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md`
**rev 23** — §1 glossary authoritative; §3 architecture; §4 where things live; §5 one
`prove_or_refute` call (THE spec of step 2); §6 refuters/judge; §7 honest costs; §8
persistence (step 4); §9 phase-1 enablers; §10 order + drafter decisions; §26 step P
accepted + step 0; §27 step 1; §28 first code review's fixes; §29 re-review ACCEPTED.

## Committed (2026-09-09; NOT pushed — push only when told, only to origin)
Performant_Isabelle_ML `4e850dd`, Isabelle_RPC `65cdbaa`, Isa-Mini `1ce791f`,
auto_sledgehammer `1360b21`, phi-system `d19e4521`, root MLML submodule bump (HEAD).
Others' uncommitted tracked edits were swept in and named in the messages (race.ML,
accounted_timeout.ML, config.ML, agent_hint.ML, aux.ML, Readme, unicode mirror, proof
stores).  Left untracked on purpose: others' scratch (Isabelle_RPC docs/tests, `local`,
`list`; Performant_Isabelle_ML ai-artifacts/sort_*; Isa-Mini ai-artifacts; `.o`, `.swn`).

## State of the code (all heaps rebuilt 2026-09-09 from Performant_Isabelle_HOL up)
- Factory `Phi_Reasoners.guard_condition_solver digest_of solve {can_inst} (ctxt0, th)`
  (reasoners.ML ~:1634-1750): quick_cut; head_only' (inj = pair ctxt0, on_thm = apsnd):
  pre; case split; `d = digest_of th`; ALLGOALS insert aux; `simpcut_tac ctxt_g`
  (enhance_for_guard, Seq.take 1, Timeout = state unchanged); is_F arm (250 ms
  auto_search, paired with ctxt0) or `solve can_inst ctxt_g d (ctxt0, th)`.
  `guard_condition_judge = guard_condition_solver guard_digest prove_or_refute`.
  `prove_or_refute can_inst ctxt d (ctxt0, th)` is TRANSITIONAL: wraps `guard_race`
  (today's Race.race with P-auto/R-conv/R-nitpick racers, 35 ms gate,
  `\<phi>guard_race_timeout`, `\<phi>log_guard_race`, guard_race Event_Log category).
- `Phi_Guard_Cache` (guard_cache.ML): tier/lemma/verdict/entry; `\<phi>guard_cache`;
  `\<phi>guard_lemma_apply_limit`; `budget_of_tier`; `Guard_Simp_SS`; `get_lemmas`,
  `add_lemma ctxt0 (th, budget)` (canonicalises), `replace_lemmas ctxt0 new`;
  `enhance_with_lemmas`; export hook priority 200.  UNEXERCISED so far (no lemma
  producer): enhance_with_lemmas on a non-empty list, add_lemma, the hook.
- Helpers: `try_prove_or_give_up bound tac ctxt th`, `p_auto_body`, `enhance_for_guard`,
  `guard_classic_prover_timeout` (400 ms) / `_bound`, `undecided_guard_warning ctxt goals`
  (used by guard_race), `loud_guard_warning ctxt goals results` (no caller yet),
  `timed_tac` exported; method `\<phi>guard_P_auto`; `solve_obligation_now` in PLPR.thy
  (`ALLGOALS (fast_force_tac)`).  `Nitpick_Refute_SS` (was Guard_Refute_SS).
- auto_sledgehammer: `Hasher.terms`; eval_prf_str0 interrupt clause;
  `auto_sledgehammer_trace_replay`.
- Probes: phi-system/ai-artifacts/Solve_Obligation_Now_Probe.thy (imports PLPR; run
  under MCP on Phi_System_Base).

## Next: STEP 2 (plan §10 step 2; spec §5, §6, §1)
1. Replace `guard_race`'s body: the sequential protocol of §5 — step 0 lookup (an
   in-memory table, test-injected `Symtab` keyed `"PLPRGUARD" ^ Hasher.compact d`, in
   place of the store until step 4; gated by `\<phi>guard_cache`); step 1 enable lemmas
   (`Thm.cterm_of ctxt0`, `Thm.trivial`, `eval_prf_str` n=1 under
   `Phi_Proof_Store.replay_limits` of times floored by the classic bound; failures =
   drop + dropped-lemma warning; `add_lemma ctxt0` into ctxt0→ctxt1 and ctxt→ctxt_g);
   step 2 P-auto = `timed_tac (guard_classic_prover_bound ctxt) (p_auto_body ctxt_g)`;
   steps 3-4 by the entry's verdict (Refuted silent; Unknown → judge or warning;
   NONE → R-conv → R-nitpick → judge → warning+write Unknown; Proved → refuters →
   judge → LOUD warning); step 6 the judge ref (`judge_arg`, `judgement`,
   standard_time on receipt, `replace_lemmas`, P-auto again, errors).  R-conv = today's
   r_conv_racer body under `Timeout.apply` of the classic bound; R-nitpick = today's
   screen + calls, outer net `refute_timeout + 5 s × n`, inner `refute_timeout + 5 s`
   per subgoal, sequential.  Delete Race.race, the racers, the protocol var, the 35 ms
   gate, `\<phi>guard_race_timeout`, p_auto_probe/nitpick_probe categories (check with
   the author before deleting probe categories).
2. `guard_decision` Event_Log record behind `\<phi>log_guard_decision` (rename of
   `\<phi>log_guard_race`): verdict, path (hit kind, refuter, judge asked), elapsed,
   `Hasher.hex` digest, n_goals, #lemmas enabled.  Delete `\<phi>log_guard_race = true`
   from PLPR.thy's `declare [[…]]` (keep `\<phi>log_guess_inst = true`).
3. Rewrite the `nitpick_params` comment ("inside a racer body").
4. `Test/Guard_Race_Smoke.thy` reshaped around `guard_decision` (its :79 call migrates to
   `guard_condition_judge`); exercise every §5 path with injected entries and a test
   judge: hits of each verdict, lemma enabling, a looping lemma cut off by its budget,
   the judge replacing lemmas, both warnings, both errors.
5. Verify: PLPR.thy + PhiTest_Arithmetic.thy under MCP on Phi_System_Base (no rebuild:
   phi-system files only); then the same review shape (workflow, Opus, English,
   interrogators → more fresh defenders → judge; harsh rebuttal; report in Chinese; no
   code changes before the author agrees).  Record in the plan (§30) and rev-bump.

## Rules (the author's, all binding)
Edit source with the Edit tool; plan docs by hand; never coin words (fixed terms:
record/entry/store/the lemma list/the lemma budget/ctxt_g/ctxt1/the canonical form/the
preparatory phase/"G.simpcut"); explain in Chinese, essence first, full context, exact
file:line; `isabelle build` only with approval (the author approved the drafter running
the rebuilds of 2026-09-09; ask again for new ones); after `.ML` edits restart/re-evaluate;
never git stash/checkout/reset/clean; commit on the repo's current branch, push origin
only, only when told; memory writes need approval; probes must not load phi-system
theories under NEW names (importing PLPR under its own name is fine); do not relay
agent progress ticks.
