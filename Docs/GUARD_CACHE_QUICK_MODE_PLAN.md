# PLPR Guard Cache — prove_or_refute rework

Status: rev 11 (2026-09-04).  After the eighth review (NOT_READY, 19
upheld) the author redesigned the solver: **no asynchrony at all** —
`prove_or_refute` is a synchronous function that gives a final verdict on
the spot and writes it to its slot; the priority chain of hooks is replaced
by ONE optional judge in a global `Unsynchronized.ref` [author 2026-09-04
03:04 "整体不再采用异步, 而是只保留缓存. 取消 the hooks 设计, 改为 a single
`hook option Unsynchronized.ref`"].  Everything about Futures, groups,
joins, merges and judge-crash classification is gone; §14 records the
rulings.  This document states the FINAL design only.  History lives in
`GUARD_CACHE_QUICK_MODE_PLAN.rev7-full.md`, `.rev9.md` and `.rev10.md`
(archived beside this file); consult them for history, never for the
design.  Every behavioral decision carries its provenance: [author
YYYY-MM-DD HH:MM "quote"] is the author's own ruling (transcript timestamp,
UTC), [drafter] is a drafting decision the author may veto; §10 lists every
[drafter] decision that changes behavior.

Predecessor: `GUARD_NITPICK_FALSIFY_PLAN.md` (the guard race this plan
dismantles).  Line anchors into `reasoners.ML`, `cache_file.ML`,
`mlmsgpack.sml` and `pretty.ML` are as of 2026-09-04 and are re-verified at
implementation start (§10.0); §8's again at step (4).  No code has been
written.

Submitted for a ninth review, scoped to §4, §5, §6 and §8.

---

## 1. Glossary

Each entry gives the term, its meaning, and where the term comes from: the
author's own words, an existing name in the code, or a plain descriptive
phrase.  No other name is used for any of these concepts anywhere in this
document.

- **guard**: a premise of the `\<condition>` family (`Premise mode P`, mode
  `MODE_GUARD` or `NO_INST`; `is_guard_mode`, `reasoners.ML:1582-1584`),
  discharged inside a run by the reasoners registered at `PLPR.thy:1983`,
  `:1986`.  [code]
- **a `prove_or_refute` call**: one invocation of `prove_or_refute` run
  through its whole protocol (§5).  Its ML type is unchanged from today:
  `bool -> Proof.context -> Proof.context -> thm -> thm Seq.seq`
  (`can_inst`, the guard-side ctxt, the outer ctxt, the goal state).  It is
  synchronous: its verdict is final when it returns [author 2026-09-04
  03:04].  [descriptive]
- **the goal state**: the thm `prove_or_refute` receives — the PLPR sequent
  after `guard_condition_solver`'s `Goal.protect 1` (`head_only`,
  `reasoners.ML:385-388`): the guard's subgoals visible, the rest of the
  sequent wrapped in `Pure.prop` (`#(rest ⟹ C)`) as the conclusion; case
  split and the "G.simpcut" pass may have turned one guard into several
  subgoals.  A **solved** goal state has no premises and is NOT
  `Goal.conclude`d — `head_only` concludes it afterwards [author 2026-09-04
  03:14].  [descriptive]
- **`guard_condition_solver`**: from now on a FACTORY — the existing
  preprocessing template (`oblg_template`, the `is_F` shortcut, case split,
  `apply_tac`'s fact insertion, the "G.simpcut" simp pass) parameterised by
  the solving tactic it ends with, whose type is `prove_or_refute`'s
  [type: drafter].  Three instances (§3): **`guard_condition_judge`** = the
  factory applied to `prove_or_refute`, used by the in-run `\<condition>`
  reasoners; the existing **`guard_condition_solver'`** /
  **`guard_condition_solver1`** = the factory applied to
  `try_prove_or_give_up` over P-auto, used by the out-of-run callers; and
  the factory applied to `try_prove_or_give_up` over `fastforce` for
  `defer_premise`'s solve-now case.  The two degenerate instances ignore
  `can_inst` and the outer ctxt.  [author 2026-09-03 09:44; 11:11]
- **`try_prove_or_give_up`**: `Time.time option -> (Proof.context -> tactic)
  -> Proof.context -> thm -> thm Seq.seq` — run the tactic once, under the
  bound if given, keep only a solved state; otherwise `Seq.empty`.  Out of
  a run: `SOME \<phi>guard_classic_prover_timeout` over P-auto [author
  2026-09-03 09:44]; for obligations: `fastforce` in a
  `Guard_Simp_SS`-enhanced ctxt, no bound by default [author 2026-09-03
  11:15; 12:53].
- **verdict**: the value stored for one guard —
  `Proved of Phi_Proof_Store.proof_cache | Unprovable of {refuter : string}`,
  `Phi_Proof_Store.proof_cache = Time.time * string` (`cache_file.ML:149`:
  standard-machine time, method text) [author 2026-09-02 12:03; 2026-09-03
  11:00; `Refuted` renamed `Unprovable` 2026-09-04 03:23].  A guard proved
  by P-auto stores the method text `\<phi>guard_P_auto`.  `refuter` names
  who decided: `"R-conv"`, `"R-nitpick"`, `"judge"`, or `"assum"` (nobody
  refuted and no judge: the guard is ASSUMED not to hold, with a warning)
  [author 2026-09-03 04:58; `"default"` renamed `"assum"` 2026-09-04 03:23].
  The run-time answer of a `prove_or_refute` call IS its verdict: a solved
  goal state for `Proved`, `Seq.empty` (the engine backtracks) for
  `Unprovable`.
- **P-auto**: `p_auto_body ctxt = solved_states (p_auto_search_tac
  (Guard_Simp_SS.enhance ctxt))`, and P-auto = `timed_tac
  \<phi>guard_classic_prover_timeout o p_auto_body` — the one proof attempt
  a `prove_or_refute` call makes first, no gate [author 2026-09-02 07:11;
  400 ms provisional 08:49].  Exposed as the proof method
  **`\<phi>guard_P_auto`** [author 2026-09-03 11:11]; the body is named
  separately so that a replay can put its OWN bound around it (§5) [drafter,
  eighth review].
- **R-conv**, **R-nitpick**: the two refuters, run in that order after
  P-auto fails, each bounding itself [author 2026-09-03 12:36 "每个 hook
  自行决定是否 timeout"]: R-conv = today's `r_conv_racer` body
  (`reasoners.ML:1329-1360`, negate and search) under
  `\<phi>guard_classic_prover_timeout` in a `Guard_Simp_SS`-enhanced ctxt
  [author 2026-09-04 03:23 "复用"]; R-nitpick = today's Nitpick screen and
  calls (`reasoners.ML:1656-1675`) under one `Timeout.apply` of
  `\<phi>guard_refute_timeout + 5000 ms × n_goals`, subgoals tried one after
  another [author 2026-09-03 13:05; order: drafter].  Both catch their own
  `TIMEOUT` and report "not refuted".  They always run — with or without a
  judge — so that a guard R-conv or R-nitpick can refute is refuted
  silently instead of warned about [author 2026-09-04 03:23 "在 warning 前
  要跑 R-conv R-nitpick 的, 以此来减少 warning"].
- **the judge**: ONE optional function in a process-global ref,
  `judge : (judge_arg -> judgement) option Unsynchronized.ref`, default
  `NONE`, installed by ML code (phase 2: the LLM judge) [author 2026-09-04
  03:04].  Consulted only after P-auto, R-conv and R-nitpick have all
  failed; its answer is final.
  ```
  type judge_arg = {ctxt : Proof.context, outer_ctxt : Proof.context,
                    can_inst : bool, thm : thm}      (* thm = the goal state *)
  datatype judgement =
      Provable of {lemmas : (term * Phi_Proof_Store.proof_cache) list,
                   proof  : Phi_Proof_Store.proof_cache,
                   thm    : thm}                     (* the SOLVED goal state, not concluded *)
    | Unprovable
  ```
  [author 2026-09-04 03:11–03:12 (`thm` in, `goals` out; `Provable` carries
  lemmas, proof and the proven goal state); 03:14 (`th` → `thm`; not
  concluded); 03:15 "就不用做任何检查" — the returned state is used as it
  is: the proof may instantiate schematic variables, and a wrong shape
  fails loudly at `head_only`'s `Goal.conclude`.]  The judge measures the
  times in `lemmas` and `proof` itself [author 2026-09-03 12:54].  An
  exception escaping the judge (or a refuter) propagates through
  `prove_or_refute` like any other exception of the run [author 2026-09-03
  12:31 "hook 的崩溃应该视作 PLPR 推理链的崩溃"].
- **`Guard_Simp_SS`**, attribute **`\<phi>guard_simp`**: the simpset that
  strengthens guard proving — an instance of the repository's `Simpset`
  functor (`library/tools/simpset.ML`) [author 2026-09-03 11:15].  Applied
  by an `enhance` inside each consumer and nowhere else [author 2026-09-03
  13:26–13:27]: the "G.simpcut" preprocessing pass (`reasoners.ML:1802-1803`),
  `p_auto_body` (so `\<phi>guard_P_auto` and the P-auto replay), R-conv,
  the obligation instance's `fastforce`, and [drafter] the `eval_prf_str`
  replay of a stored script.  Not R-nitpick (it stacks only
  `Nitpick_Refute_SS`, today's `Guard_Refute_SS` renamed [author 2026-09-03
  11:15]), not the ctxt built at `reasoners.ML:1829`, not `judge_arg.ctxt`.
- **the undecided-guard warning**: the message printed over a guard's
  subgoals when neither a proof nor a refutation was found and no judge is
  installed — today's text at `reasoners.ML:1605-1616`, factored into one
  function of the ctxt and the subgoals, called at the two places that
  print it (§5).  [descriptive]
- **env**: the record (§4) in a `Proof_Data` slot of type `env option
  Unsynchronized.ref option`: outer `NONE` = this ctxt was never given a
  cell; the cell's `SOME env` = the run is open, `NONE` = it has ended
  [author 2026-09-03 08:08 / 08:11].  "No record" is `previous_final =
  NONE` [author 2026-09-03 16:00, 16:34].
- **the run**: everything between one `gen_reason'` invocation installing
  an env and that same invocation finishing.  The invocation that installs
  the env is **the topmost `gen_reason'` invocation** [author 2026-09-02
  15:45]; nested invocations inherit.  What it does when the run ends (§4)
  is **the end-of-run steps**.  Only the run's own thread ever touches the
  env.
- **run failure**: the topmost `gen_reason'` invocation returning `NONE`,
  or ending with a non-interrupt exception (`Interrupt_Family.contains_interrupt`
  false, `reasoners.ML:1635`) [author 2026-09-03 07:35].  A nested
  `\<r>BEGIN` reasoning whose nested run returns `NONE` raises an ERROR
  (`nested.ML:33`); `gen_reason`'s step limit raises too
  (`reasoner.ML:794-799`).
- **`Guard_Record_Stale`**: the exception a run WITH a record raises the
  first time the record fails to reproduce — at a `prove_or_refute` call:
  slot absent, stored digest different, or a `Proved` hit whose replay
  fails; at installation: a run lemma that fails to certify or replay.  It
  passes through every nested `gen_reason'` (they catch only `Success`,
  `Global_Cut`, `Explorative_Backtrack`, `reasoner.ML:802-809`, `:917`) to
  the topmost invocation, which tombstones the record and runs again
  without the cache (§4) [author 2026-09-03 15:01; 16:01; 16:55].  Name:
  drafter.
- **call index**: the position of a `prove_or_refute` call within its run,
  0, 1, 2, …, from the env's counter [author 2026-09-02 07:11; 2026-09-03
  07:59].
- **guard digest**: the `Hasher` digest (`Word64.word`) of the goal
  state's subgoals — `Thm.cprems_of thm`, each with its parameters and
  premises; not the ctxt's assumptions, not the theory name [author
  2026-09-03 07:48].  Computed by a new `Hasher.terms : term list ->
  digest`.  `Word64` in memory [author 2026-09-03 07:58].
- **table**, **slot**: the run's `(digest * verdict) Inttab.table` keyed by
  call index [author 2026-09-02 07:11; 2026-09-03 02:18].  A **hit** is
  slot `i` present with the stored digest equal to this call's guard
  digest; anything else is a **miss**; a **replay** is re-running the
  method text a `Proved` slot recorded.
- **record**, **record key**: the one proof-store item holding a whole
  run's `{final, lemmas, entries}` (§8).  Key: `"PLPRGUARD" ^
  Hasher.compact (Hasher.goal (ctxt, initial))` of the run's first pulled
  initial state (`Hasher.goal`, `Hasher.ML:243-246`, salts the theory short
  name and the ctxt's assumptions) [author 2026-09-03 02:18; 08:33; 08:44].
  `Hasher.compact` (`Hasher.ML:76`) never appears in a log line.  Stability
  caveat: `Hasher.goal` is the formula `cache_file.ML:898-901` calls not
  invariant under fork/promise discharge; a moved record key costs one
  `Guard_Record_Stale` at call 0 and one no-cache run, never a wrong
  verdict.
- **final digest**: `Hasher.goal (ctxt', th')` of the run's resulting state
  [author 2026-09-02 07:11].  Same caveat; a final digest that is not
  reproducible at all costs one R3 re-run on EVERY run — §10 step (4)'s
  gate measures this before persistence lands.
- **tombstone**: the proof store's own per-key deletion (`TOMB`,
  `cache_file.ML:76`; `encode_tombstone`, `:108`), written by
  `Phi_Guard_Store.invalidate_proof_cache` with `warn = false` [author
  2026-09-03 13:19].
- **the no-cache re-run**: after the record has been tombstoned, the
  topmost invocation calls `gen_reason'` again with its own arguments
  [author 2026-09-04 03:04 "A 批准" — eighth review relaxation 1].  The
  tombstone's in-memory half has removed the record (`cache_file.ML:258-260`
  via `:779-789`) and `get_cached_proof` reads that table (`:712-713`), so
  the new invocation installs an env with `previous_final = NONE`, an empty
  table and no run lemmas by the ORDINARY installation rule, performs its
  own end-of-run steps, and — having no record — can neither raise
  `Guard_Record_Stale` nor fire R2/R3: it is always a leaf.  Residual: a
  second "Time spent by \<phi>-LPR reasoning" line when `count_performance`
  is on.
- **run lemmas**: `(term * Phi_Proof_Store.proof_cache) list` — (statement,
  (replay time, method text)) that strengthen `Guard_Simp_SS` for one run.
  They live in the record and the env; at installation each is re-proved
  by replaying its method text under `tolerant_time` of its recorded time,
  in the ctxt `gen_reason'` was given — its own simpset, without
  `\<phi>guard_simp` and without the other run lemmas — and the thms are
  put into `Guard_Simp_SS` of every initial state's ctxt (§4) [author
  2026-09-02 07:39; 2026-09-03 10:53; 12:54; 13:27].  Phase 1 has no
  producer; the judge's `Provable` produces them.  One that fails to
  certify or replay raises `Guard_Record_Stale` [author 2026-09-03 16:55].
- **R1–R4**: the four rules of §7.

Retired names — never used below: "owner" = the topmost `gen_reason'`
invocation; "scope" = the run; "determination" = a `prove_or_refute` call;
"the proving stage" = P-auto; "store key" / `cache_key` = record key;
"exit protocol" = the end-of-run steps; "defensive rule" / "no-env case" =
the out-of-run entry points; "blob" = the record value; "Guard_Fails" /
"refutable" = unprovable (the answer is now the verdict); "quick mode" =
(no modes); "aux" = the fields of `Provable`; "evidence" = (deleted);
"`NONE` = P-auto" = `\<phi>guard_P_auto`; "Actually_Provable" =
`Provable`; "Refuted" = `Unprovable`; "default" (refuter) = `"assum"`;
"judge" as "one Future per unprovable answer", "async judge", "the chain",
"hooks", "refutation hook chain", `PLPR_Guard_Refuters`, `Handlers`
registry, priorities, `chain_verdict`, `Refutable`, `judge_group`,
`judges`, "judge crash", "merge", "join" = (deleted: no asynchrony);
"Chain_Ran" / "Chain_Answered" / `judge_outcome` / `add_refuter` /
`run_chain` / `PLPR_Refuters` / `bound` = (deleted); "the control-flow
classifier" / `is_control_flow` = (deleted); "not landed" = replay failed;
`\<phi>guard_prove_timeout` / `\<phi>guard_rconv_timeout` =
`\<phi>guard_classic_prover_timeout`; "the auxiliary-lemma slot" =
`Guard_Simp_SS`; "Guard_Refute_SS" = `Nitpick_Refute_SS`; "type proof" =
`Phi_Proof_Store.proof_cache`; `th` (in `judge_arg`) = `thm`.

## 2. Motivation

~88 % of the corpus's `prove_or_refute` calls end with the guard not
holding (median refuted 607 ms, undecided 2367 ms).  The cache removes
that cost from every run after the first: a recorded `Unprovable` is
answered at once, a recorded `Proved` is replayed under a generous bound,
and the whole record is validated end to end per run (§7).  Soundness is
untouched: verdicts only select which rules PLPR tries; a wrong
`Unprovable` yields a different but valid derivation, never a wrong
theorem.  Guards are load-bearing for phi-system — an over-refuted guard
fails the whole reasoning — so the judge (phase 2's LLM judge) is the
mechanism that corrects over-refutation, and its answer is final [author
2026-09-03 12:27; 2026-09-04 03:04].

## 3. Architecture

Three entry points, distinguished statically by which factory instance a
caller uses — no run-time "is there an env" test anywhere:

```
IN A RUN   (\<condition> ?P, \<condition>[NO_INST] ?P reasoners, PLPR.thy:1983/1986)
  gen_reason' (reasoner.ML:910), on entry:
    slot check on the first pulled state's ctxt —
      no cell, or a cell holding NONE  → install a fresh env: this is the
                                          topmost invocation; it alone
                                          performs the end-of-run steps
      a cell holding SOME env           → inherit; nothing at the end
    … reasoning …
      guard_condition_judge = guard_condition_solver prove_or_refute
        prove_or_refute (env read from its ctxt argument):
          i := next call index; d := this guard's digest
          WITH A RECORD (previous_final = SOME _):
            slot i = (d, Unprovable {refuter}) → Seq.empty (warn again if "assum")
            slot i = (d, Proved (t, script))  → replay script under its bound;
                                                 replay failed → raise Guard_Record_Stale
            slot i absent or digest ≠ d       → raise Guard_Record_Stale
          WITHOUT A RECORD (previous_final = NONE), synchronous, verdict written at once:
            P-auto proves                     → slot i := Proved (elapsed, "\<phi>guard_P_auto")
            else R-conv refutes               → slot i := Unprovable {"R-conv"}, silent
            else R-nitpick refutes            → slot i := Unprovable {"R-nitpick"}, silent
            else judge = SOME j:
                 j answers Provable {lemmas, proof, thm}
                                              → slot i := Proved proof; lemmas appended;
                                                 return thm
                 j answers Unprovable         → slot i := Unprovable {"judge"}, silent
            else (no judge)                   → the undecided-guard warning;
                                                 slot i := Unprovable {"assum"}
    end-of-run steps (topmost invocation only):
      close (cell := NONE) → classify the run's outcome (§4):
        Guard_Record_Stale, R2 (NONE), R3    → tombstone; call gen_reason' again; its result
        R2 (exception)                       → tombstone; re-raise
        failure without a record, interrupt  → nothing written; propagate
        success without a record             → persist if the table is non-empty
        success with a record                → final digest = previous_final → nothing written

OUT OF A RUN   (guard_condition_solver' / guard_condition_solver1: four
                command-level callers in Phi_System — local_value.ML:168,
                toplevel0.ML:364, generic_variable_access2.ML:181, :264;
                application.ML:133 is commented out — solving proof
                obligations, `Premise default P` / `Premise MODE_COLLECT P`)
  guard_condition_solver (fn _ => fn ctxt => fn _ =>
      try_prove_or_give_up (SOME \<phi>guard_classic_prover_timeout) p_auto_body ctxt):
    same preprocessing, then P-auto once; not proved → Seq.empty → the
    caller's error continuation.  A deliberate narrowing: today these sites
    also get a 35 ms auto_search_tac gate (reasoners.ML:1602) and a 2000 ms
    P-auto budget (:1618, :1701); all four sites raise `error` on failure,
    so §10 step (5) surfaces any regression as a build failure.

OBLIGATIONS SOLVED ON THE SPOT   (defer_premise, PLPR.thy:1974/1975, when
                Phi_Reasoner_solve_obligation_and_no_defer is 1 or 2 — set
                by the user's prove_obligations_in_time and internally by
                SE_Trim_Empty.ML:54, :114, rule_generation.ML:443)
  guard_condition_solver (fn _ => fn ctxt => fn _ =>
      try_prove_or_give_up NONE fastforce (Guard_Simp_SS.enhance ctxt)):
    same preprocessing, then fastforce, unbounded by default; not proved →
    Seq.empty → backtrack.  No table, no warning.
```

Removed: the `Race.race` call, the three racer wrappers, the in-race
`protocol` var, `\<phi>guard_race_timeout`, the 35 ms gate, and everything
asynchronous.  Reused: `Hasher`, the proof store (as a functor instance,
§8), `eval_prf_str`, `Phi_Reasoners.wrap` (registrations unchanged [author
2026-09-02 12:08]), `Simpset`, the R-conv/R-nitpick bodies (screens
verbatim), `RPC_Pretty`'s raw term codec (functorised, §8).

Every caller of the old `guard_condition_solver` must migrate, and the
factory's changed type makes a missed one a compile error.  Known callers
(2026-09-03): `PLPR.thy:1983`, `:1986` → `guard_condition_judge`;
`PLPR.thy:1974`, `:1975` (`defer_premise`) → the `fastforce` instance
[author 2026-09-03 11:15]; `Test/Guard_Race_Smoke.thy:79` → migrated at
§10 step (2).

## 4. The env

```
type env =
  {record_key     : string,
   previous_final : Hasher.digest option,            (* NONE = no record *)
   lemmas         : (term * Phi_Proof_Store.proof_cache) list Unsynchronized.ref,
   counter        : int Unsynchronized.ref,
   entries        : (Hasher.digest * verdict) Inttab.table Unsynchronized.ref}
```

[author 2026-09-03 16:00 "原本的 type env 就已经足够了"; 16:34; the two
asynchrony fields removed 2026-09-04 03:04.]  Plain refs; only the run's
own thread touches them.  In a run with a record `entries` and `lemmas`
hold the record as read and are never written (§5); in a run without a
record they start empty and are built in place.

- **Installation**, in this order [order: drafter, eighth review]:
  1. `gen_reason'` reads the slot of the FIRST PULLED initial state's ctxt
     (`reasoner.ML:813`).  No cell, or a cell holding `NONE` → this
     invocation is the topmost one; a cell holding `SOME env` → inherit,
     nothing more.  ONLY `gen_reason'` installs [author 2026-09-02 15:45;
     14:54].
  2. Compute `record_key`; read the record (§8's decode is catch-all and
     cannot raise).  Record found and `\<phi>guard_cache` true →
     `previous_final := SOME final`, `entries := its table`, `lemmas := its
     lemmas`; otherwise `previous_final := NONE`, `entries := Inttab.empty`,
     `lemmas := []`.  Eagerly [author 2026-09-03 05:38].  `counter := 0`.
  3. Put the env into a fresh cell.  `gen_reason'` keeps one decision ref
     per invocation and maps `apfst install` lazily over the initial
     states; `install` consults the ref — undecided (the first pulled
     state) → decide as in 1–2 and record the cell (and, after 4, the lemma
     thms); already decided → put the recorded cell and thms.  One
     invocation mints at most one env [drafter, seventh review U22; every
     live caller passes a single-element sequence].
  4. Re-prove each run lemma: `Thm.cterm_of` on its statement,
     `eval_prf_str` of its method text under `tolerant_time` of its
     recorded time, in `gen_reason'`'s own ctxt (§1 run lemmas); a lemma
     that fails to certify or replay raises `Guard_Record_Stale` [author
     2026-09-03 16:55], which the frame now catches as an ordinary run
     outcome (step 2 below).  The thms are put into `Guard_Simp_SS` of
     EACH initial state's ctxt by `install` (`Guard_Simp_SS.add_simps'` is
     functional and `gen_reason'`'s own ctxt reaches no tactic —
     `reasoner.ML:910-918`, `:779-781`; tactics see the per-state ctxt via
     `Phi_Reasoners.wrap`, `tools/helpers1.ML:19`) [drafter, eighth review].
- **Nesting**: a nested `gen_reason'` (`\<r>Call`, `\<r>BEGIN`,
  `ToR_Entry_Point` via `internal_reason`) inherits: one table, one
  counter, one lemma list; no end-of-run steps.  Its `NONE` is ordinary
  backtracking for `\<r>Call` and `ToR_Entry_Point` (`nested.ML:42-45`);
  `\<r>BEGIN` converts it to an ERROR (`nested.ML:33`).
  `Guard_Record_Stale` passes through all of them.  [author 2026-09-02
  15:45, 16:02]
- **End-of-run steps** (topmost invocation only).  They wrap the RESULT of
  the topmost `gen_reason'` — outside its own `handle Success ret => SOME
  ret` (`reasoner.ML:917`), so PLPR's control-flow exceptions are
  structurally unreachable here [drafter, seventh review U20].  Nothing
  here defers interrupts: there is no join, and the store's own
  `with_file_lock` keeps its blocking wait interruptible only when entered
  with ordinary attributes (`cache_file.ML:383-405`).  In order:
  1. `cell := NONE` [author 2026-09-03 08:08].
  2. **`Guard_Record_Stale` escaped** (only possible with a record):
     tombstone; the no-cache re-run (§1: call `gen_reason'` again); return
     its result [author 2026-09-03 15:01, 16:01; 2026-09-04 03:04].
  3. **Run failure WITH a record**: `NONE` → R2 with re-run: tombstone,
     call `gen_reason'` again, return its result.  Non-interrupt exception
     → R2 without re-run: tombstone, re-raise [author 2026-09-03 07:35].
  4. **Run failure WITHOUT a record**, or an **interrupt** from any run:
     nothing written, nothing deleted; return the `NONE` / re-raise
     [author 2026-09-03 14:56].
  5. **Success WITHOUT a record**: compute the final digest; persist
     `{final, lemmas = !lemmas, entries = !entries}` (§8) if `entries` is
     non-empty AND `\<phi>guard_cache` is true [author 2026-09-03 08:04;
     12:52; 2026-09-04 03:23 "无论是否配置了 judge, 在无缓存下正常运行结束
     后都一定要写缓存"].
  6. **Success WITH a record** (`entries` unchanged): compute the final
     digest; `<> previous_final` → R3: tombstone, call `gen_reason'` again,
     return its result.  Equal → nothing written [author 2026-09-03 16:55
     "(b) 不写"].

## 5. One `prove_or_refute` call

Inside a run only.  `i := !counter; counter := i + 1`; `d := Hasher.terms
(map Thm.term_of (Thm.cprems_of thm))` on the goal state as received.  Then
by `previous_final`:

**With a record** (`SOME _`) — the run tolerates no miss [author 2026-09-03
15:01, 16:01]:

1. Slot `i` is `(d', Unprovable {refuter})` with `d' = d` → return
   `Seq.empty`.  Silent unless `refuter = "assum"`, which prints the
   undecided-guard warning again [author 2026-09-03 04:46; 2026-09-04
   03:23 "要打警告的"].  Never re-judged [author 2026-09-02 10:40].
2. Slot `i` is `(d', Proved (t, script))` with `d' = d` → replay, under
   `Exn.capture_body`.  `script = "\<phi>guard_P_auto"` → run `p_auto_body`
   — the BODY, so that the method's own 400 ms bound is not nested inside
   the replay bound [drafter, eighth review] — under `Time.max
   (tolerant_time t, \<phi>guard_classic_prover_timeout)` (`Time.max`,
   `Pure/General/time.ML:24`), `tolerant_time t = 1.5t + 1 s`
   (`cache_file.ML:875-876`) [floor: author 2026-09-02 13:01; summand and
   `tolerant_time`: 2026-09-03 02:10, 13:03].  Any other `script` →
   `eval_prf_str` under `tolerant_time t`, `n = Thm.nprems_of thm`,
   keywords `Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)`, in
   a `Guard_Simp_SS`-enhanced ctxt; on success the returned `(ctxt', thm')`
   gives `Seq.single thm'` and `ctxt'` is discarded.  Replay succeeded →
   return the solved state.  Replay failed → raise `Guard_Record_Stale`
   [author 2026-09-03 15:46, 16:01]: "failed" is `Timeout.TIMEOUT` or an
   exhausted sequence on the P-auto arm, and `Phi_Sledgehammer_Solver.Auto_Fail
   _` on the `eval_prf_str` arm (how it reports timeout, an unsolved goal,
   a failed method and an unparsable script alike,
   `sledgehammer_solver.ML:610-631`).  Catch exactly those — never a
   catch-all; the interrupt family passes untouched [drafter, eighth
   review].
3. Slot `i` absent, or `d' <> d` → raise `Guard_Record_Stale`.

**Without a record** (`NONE`) — synchronous, the verdict written at once
[author 2026-09-04 03:04, 03:23]:

4. P-auto.  Proves → `entries := Inttab.update (i, (d, Proved (elapsed,
   "\<phi>guard_P_auto")))`, `elapsed` measured around the `Seq.pull` of
   the P-auto sequence (`timed_tac` only builds a `Seq.make`,
   `reasoners.ML:926-931`) and normalised through `standard_time`
   (`cache_file.ML:855`) [author 2026-09-03 12:52; where the bracket goes:
   drafter]; return the solved state.
5. Else R-conv (§1).  Refutes → `entries := Inttab.update (i, (d,
   Unprovable {refuter = "R-conv"}))`; return `Seq.empty`, silently.
6. Else R-nitpick (§1).  Refutes → likewise with `"R-nitpick"`.
7. Else, if `!judge = SOME j`: `j {ctxt, outer_ctxt, can_inst, thm}`.
   `Provable {lemmas = new, proof, thm = solved}` → `entries :=
   Inttab.update (i, (d, Proved proof))`; `lemmas := !lemmas @ new` (they
   are persisted with the record and take effect at the next run's
   installation [drafter]); return `Seq.single solved`, no check on
   `solved` [author 2026-09-04 03:15].  `Unprovable` → `Unprovable
   {refuter = "judge"}`; return `Seq.empty`, silently — the judge decided,
   no warning [author 2026-09-04 03:04].
8. Else (`!judge = NONE`): print the undecided-guard warning; `entries :=
   Inttab.update (i, (d, Unprovable {refuter = "assum"}))`; return
   `Seq.empty`.

Any exception escaping P-auto, a refuter or the judge propagates out of
`prove_or_refute` unchanged and becomes the run's own exception (§4 step
3/4) [author 2026-09-03 12:31; 2026-09-04 03:04].  Two calls in one run
that meet the same guard occupy two slots and are decided twice: the slot,
not the guard, is the identity [author 2026-09-03 07:54].

## 6. The refuters and the judge

There is no registry and no priority.  `prove_or_refute` calls three
things in a fixed order — R-conv, R-nitpick, the judge — each a plain
function that bounds itself:

| step | what | its own bound |
|---|---|---|
| R-conv | today's `r_conv_racer` body: negate each subgoal, search with `auto_search_tac` in a `Guard_Simp_SS`-enhanced ctxt, export through `outer_ctxt` as today (`reasoners.ML:1303-1312`, `:1329-1360`) | `Timeout.apply \<phi>guard_classic_prover_timeout`; `TIMEOUT` → not refuted [author 2026-09-04 03:23] |
| R-nitpick | today's screen and Nitpick calls (`reasoners.ML:1656-1675`), subgoals one after another, each Nitpick call with its 2000 ms parameter as today; R-nitpick's own preprocessing simpset `Nitpick_Refute_SS` | one `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms × length goals`; `TIMEOUT` → not refuted [author 2026-09-03 13:05; sequential: drafter] |
| the judge | `!judge`, if `SOME` (§1) | its own |

The undecided-guard warning is printed by `prove_or_refute` itself
(§5 step 8) and on an `"assum"` hit (§5 step 1) — the two call sites of
one function.  No `Position` juggling is needed: everything runs on the
run's own thread.

## 7. Rules

Stated of one run (§1).

- **R1 recording** [author 2026-09-02 12:03]: in a run without a record,
  every completed `prove_or_refute` call writes its slot before returning.
  At the end of such a run whose table is non-empty, the topmost
  invocation writes the WHOLE table as the record (never a delta — the
  store is last-write-wins) [author 2026-09-02 07:11; empty table exempt
  2026-09-03 08:04; always, with or without a judge, 2026-09-04 03:23].  A
  failed run records nothing [author 2026-09-02 11:40]; an interrupted run
  writes and deletes nothing [2026-09-03 14:56]; a run with a record never
  writes (§5; an unchanged record is not rewritten [2026-09-03 16:55]).
- **R2 run failure against a record** [author 2026-09-02 11:48, 11:54;
  widened 2026-09-03 07:35; first-miss 15:01/16:01]: a run with a record is
  stale, and the record is tombstoned, when it (a) returns `NONE` → the
  no-cache re-run; (b) ends with a non-interrupt exception → no re-run, the
  exception is re-raised; (c) raises `Guard_Record_Stale` → the no-cache
  re-run.  The re-run records under R1 by performing its own end-of-run
  steps.
- **R3 validation** [author 2026-09-02 07:11]: a run with a record that
  succeeds compares its final digest with `previous_final`; mismatch →
  tombstone, the no-cache re-run.
- **R4 faithful hits** [author 2026-09-02 10:40]: a hit is never re-judged.

Recorded honestly, with no rule answering it:

- Staleness that leaves the final outcome unchanged (an `Unprovable` whose
  countermodel rests on a changed definition; an `"assum"` slot for a guard
  a new simp lemma would now prove — it warns on every hit) is reproduced
  faithfully forever.
- Load can permanently demote a guard.  A run without a record that misses
  the P-auto budget under load records `Unprovable` (`"R-conv"` /
  `"R-nitpick"` / `"judge"` / `"assum"`), and R3 structurally cannot fire
  on it.  A record does not protect against this: one replay that overruns
  its budget is a miss (§5 step 2), the record is tombstoned and the whole
  run repeats without the cache; if the load persists, every guard that
  previously proved can be recorded `Unprovable` in the new record, and R4
  never re-judges those slots.  `\<phi>guard_cache = false` and deleting
  the file are the escape hatches.
- An edit that gains or loses one `prove_or_refute` call early shifts every
  later call index: the run raises `Guard_Record_Stale` at the first
  shifted slot whose digest differs and repeats without the cache.  A
  shifted slot that happens to hold the SAME guard is a hit and delivers
  the verdict another call site earned — nothing unsound follows (a
  `Proved` hit is re-proved by replay, an `Unprovable` hit only prunes),
  and if the outcome changes R3 re-runs.  One re-run's cost.
- Two runs in one theory whose first pulled initial states agree in
  sequent and assumptions share a record key and clobber each other's
  record.  §10's gate before step (4) measures whether record keys repeat
  across corpus runs at all.
- A stale slot can steer a run down a branch that raises where the
  cache-free run would have succeeded (the step limit, `reasoner.ML:793-799`;
  a nested `\<r>BEGIN` failure, `nested.ML:33`).  R2 (b) tombstones and
  re-raises without a re-run, so that build fails once and succeeds on the
  next invocation — PROVIDED the tombstone reaches disk.  The store's write
  path is best-effort by design (`append_record`, `cache_file.ML:569-580`,
  skips the write on an unwritable location and swallows an I/O failure
  inside `\<^try>`), so where the tombstone cannot land (another user's
  mode-0644 `<thy>.guard-cache` in a shared checkout; a full or failing
  filesystem) the record is re-read by every fresh process and the failure
  repeats; R2 (a)/R3/`Guard_Record_Stale` degrade only to one extra
  no-cache run per process.  `\<phi>guard_cache = false` is the escape
  hatch [eighth review relaxation 2 not adopted: author 2026-09-04 03:04
  "B 赞同不采纳"].
- The judge's `Provable` writes a `Proved` whose script the next run
  replays through `eval_prf_str` (§5 step 2) while the judge verified it
  by whatever means it chose; if the replay fails, the record is
  tombstoned and the run repeats without the cache, the judge is consulted
  again, and the same record can be written again — one no-cache run per
  run for that guard until the judge's script and the replay agree.
- The obligation instance's `fastforce` is unbounded by default, as is the
  template's own "G.simpcut" pass on that path today [author 2026-09-03
  12:53].
- There is NO user-facing invalidation feature [author 2026-09-03 04:55];
  the file is regenerable and deleting it is the reset.

## 8. Persistence

- **Store functor** [within §11.10's delegation; shape: seventh review U6].
  `cache_file.ML`'s store body becomes a functor over `{ext, migrates,
  marks_writes, describe, switch}`; `Phi_Proof_Store` is instantiated in
  `cache_file.ML` with `{ext = "proof-store", migrates = true, marks_writes
  = true, describe = ("Proof cache", "cached proofs"), switch = <the
  existing enable_proof_store binding>}` — unchanged name, signature and
  callers — and **`Phi_Guard_Store`** is instantiated in PLPR with `{ext =
  "guard-cache", migrates = false, marks_writes = false, describe = ("Guard
  cache", "cached guard verdicts"), switch = \<phi>guard_cache}`, where
  `\<phi>guard_cache` and the record codec are also declared (`RPC_Pretty`
  is not visible from Auto_Sledgehammer, `Auto_Sledgehammer.thy:2`; it
  reaches PLPR via `PLPR_error_msg.thy:7` → `Minilang_AoA.thy:2`).  Every
  module-level piece of state (`append_locks`, `warned_dirs`,
  `openning_stores`, the `Theory.at_end`) is per instance; the guard
  instance is ascribed a narrower signature without the by-hash surface;
  the honest cost is one unused by-hash index compiled per instance.
  `switch` is a functor argument only because `Attrib.setup_config_bool`
  (`cache_file.ML:229`) cannot declare one binding twice; it gates NOTHING
  inside the store (the only `Config.get` of a switch, `:885`, is in the
  by-hash surface) — the guard switch is enforced by PLPR at the record
  read (§4 installation 2) and at the write (§4 step 5) [eighth review].
  Per-kind behavior: `migrates = false` → no legacy `.proof-cache`
  fallback, an absent file is an empty table; `marks_writes = false` → no
  `written`/`proof_mark` collision alarm (a guard record is legitimately
  rewritten); `describe` feeds `warn_not_writable` ("Guard cache for theory
  … is not writable (…); cached guard verdicts will be read but not
  recorded." [author 2026-09-03 11:22]) and `report_cache_is_outdated`.
  The shared `at_end` becomes `if File.is_file (store_path thy) then
  <today's body> else close_store thy` — otherwise every theory in the
  build gets a `<thy>.guard-cache.lock` created by `with_file_lock`'s
  `Posix.FileSys.createf` (`:394-396`) plus a writability probe at its end;
  measured today as 85 `*.proof-store.lock` files against 38
  `*.proof-store` files in `contrib/phi-system` [drafter, seventh review
  U14 / eighth review].  The dead `bool` in `openning_stores`'s value
  triple (`:632`; six writers, no readers) is dropped in the same pass.
- **Three entry points of `Phi_Guard_Store`**, no new ones [author
  2026-09-03 13:19]: read = `get_cached_proof thy record_key : proof_cache
  option`, the record value being its string half; write =
  `update_cached_proof thy {id = record_key, hash = NONE} (Time.zeroTime,
  value)` (the time half unused); tombstone = `invalidate_proof_cache false
  record_key thy` (`:779-789`: in-memory `store_invalidate_proof`, then
  `append_record` of `encode_tombstone`).  The store's locking
  (`store_append_lock`, `with_file_lock`, lock order v → fcntl →
  `openning_stores`, `:530-533`, `:693-697`) is inherited unchanged.
- Guard records live in `<thy>.guard-cache`, GITIGNORED [author 2026-09-02
  13:01]: `*.guard-cache`, `*.guard-cache.lock`, `*.guard-cache.tmp*`
  (`write_state_new`, `:365-373`) in `contrib/phi-system/.gitignore`
  [author 2026-09-03 14:57].
- **Record value**: `{final : digest, lemmas : (term *
  Phi_Proof_Store.proof_cache) list, entries : (int * digest * verdict)
  list}` (written from `Inttab.dest`, ascending) packed with the mlmsgpack
  packers through a `BytesIO` outstream and taken as a string
  (`encode_record`'s shape, `cache_file.ML:94-99`) [author 2026-09-03
  05:42].  Digests through `packWord64` / `unpackWord64` [author 2026-09-03
  07:58]; a `proof_cache`'s `Time.time` as `packInt (Time.toMilliseconds t)`
  / `Time.fromMilliseconds`, the store's own convention (`:277-279`,
  `:271-273`); `verdict` tagged by an int like `PUT`/`TOMB` [author
  2026-09-03 13:19]; a lemma's `term` through `RPC_Pretty.pack_raw_term` /
  `unpack_raw_term` (`Isabelle_RPC/Tools/pretty.ML:323-366`, the
  constructor-tagged structural codec) made available on `BytesIO` by
  turning that codec into a functor over the `MessagePack` result signature
  (`mlmsgpack.sml:1`; naming its result signature is a mechanical
  extraction of `mlmsgpack.sml:8-106`, no logic change) and instantiating it
  twice; the `MessagePackBinIO` instance keeps `RPC_Pretty`'s names.  The
  functor stays in `Isabelle_RPC` for now and moves to
  `Performant_Isabelle_ML` after this plan [author 2026-09-03 13:19; 13:27;
  14:19].  NO format version [author 2026-09-03 03:02]: the decode is
  wrapped `\<^try>\<open>SOME (decode v) catch _ => NONE\<close>` —
  catch-ALL, because a truncated payload raises `Subscript` out of
  `BytesIO.inputN` (`mlmsgpack.sml:918-924`); `\<^try>` re-raises
  interrupts.  Any exception means "there is no record".
- Written at most once per run, at the end of a run without a record, only
  when the table is non-empty and `\<phi>guard_cache` is true.
- `\<phi>guard_cache` (default true) is the one debugging switch [author
  2026-09-02 10:41]; off = the record is neither read nor written, the run
  behaves as one without a record [author 2026-09-03 12:52].

## 9. Phase 2 (deferred) and phase-1 enablers

Phase 1 lands: the `eval_prf_str` tracing line behind a verbosity gate
[author 2026-09-02 10:29]; `Guard_Simp_SS` with its attribute and its
consumers (§1); the `Nitpick_Refute_SS` rename; the judge ref (default
`NONE`) and its types.  Nothing else outside PLPR is touched [author
2026-09-03 12:59–13:01].  Phase 2 is the LLM judge: a function of
`judge_arg -> judgement` installed into the ref, answering `Provable` with
lemmas, a script and the proven goal state, or `Unprovable` [author
2026-09-02 07:39; 2026-09-04 03:04–03:15].

## 10. Configuration, drafter decisions, implementation order

| option | default |
|---|---|
| `\<phi>guard_classic_prover_timeout` | 400 ms, provisional — P-auto's and R-conv's budget, and the floor of a P-auto replay [author 2026-09-04 03:23 "直接重命名为 \<phi>guard_classic_prover_timeout"; replaces `\<phi>guard_prove_timeout` and `\<phi>guard_rconv_timeout`] |
| `\<phi>guard_refute_timeout` | 2000 ms (Nitpick's parameter; R-nitpick's own net is this + 5 s per subgoal) |
| `\<phi>guard_cache` | true |
| `\<phi>log_guard_race` → `\<phi>log_guard_decision` | false (renamed) |

Names approved [author 2026-09-03 04:58, 11:11, 11:15; 2026-09-04 03:23];
ML identifiers not named by the author are the drafter's under the 11:24
delegation (among them the judge ref's name and module, and
`Guard_Record_Stale`).

Nothing is pending the author.

**Drafter decisions that change behavior**, each vetoable: U22 (one env
per `gen_reason'` invocation via a decision ref — §4); U20 (the
end-of-run steps sit outside `gen_reason'`'s `handle Success` — §4); the
installation order (§4); the lemma thms carried into each initial state's
ctxt by `install` (§4); `p_auto_body` named apart from its bound, so a
replay bounds the body (§1, §5); the exact exceptions a replay converts
into `Guard_Record_Stale` (§5 step 2); `elapsed` measured around the
`Seq.pull` (§5 step 4); the judge's returned lemmas taking effect at the
next run's installation, not in the current run (§5 step 7); U3 (the
factory parameter's type — §1); the sequential order of R-nitpick's
subgoals inside its one net (§6); `Time.zeroTime` / `hash = NONE` in the
record write (§8); the `eval_prf_str` replay as a `Guard_Simp_SS` consumer
(§1); the catch-all decode (§8); the store functor's argument list and
the narrowed guard signature (§8); the `at_end` gate (§8); `Hasher.goal`
as the exported spelling of both digests (§1).

Instrumentation is temporary measurement code [author 2026-09-03 04:01]:
one permanent record, guard_decision (verdict token, refuter, replay
field, elapsed, `Hasher.hex` of the digest, call index, n_goals), behind
`\<phi>log_guard_decision`; `Hasher.hex` appears in exactly that log line.

Order:

0. Re-verify line anchors; `Hasher.terms`; the tracing gate.
1. The factory: `guard_condition_solver` parameterised;
   `try_prove_or_give_up`; `p_auto_body` and `\<phi>guard_P_auto`'s
   `method_setup`; `Guard_Simp_SS` with its attribute and its `enhance`
   sites; the `Nitpick_Refute_SS` rename; `guard_condition_solver'`/`1` on
   P-auto; the `fastforce` instance for `defer_premise`; the undecided-guard
   warning as a function.
2. `prove_or_refute` synchronous over P-auto → R-conv → R-nitpick → the
   judge ref → the warning, with no table (every call takes the
   without-a-record path and writes nothing); `guard_condition_judge`;
   migrate every caller (§3) and `Test/Guard_Race_Smoke.thy`;
   guard_decision.
3. The env and the in-memory table: installation, the call index, both
   paths of §5 (the record-side path fed from a table injected by the
   test: hits, the two replays, `Guard_Record_Stale`), the end-of-run steps
   with the no-cache re-run, R4.
4. Persistence, gated: proceeds only if step (3)'s temporary
   instrumentation shows record keys repeating across two consecutive
   corpus runs AND the final digest of a repeated key reproducing.  Then:
   the store functor and `Phi_Guard_Store`, the raw-term codec functor and
   its `BytesIO` instance, the gitignore entries, the record read at
   installation (`previous_final`, `entries`, `lemmas`, lemma replay), R1's
   write, R2, R3.
5. Corpus acceptance: a cache-on and a cache-off leg, a concurrent Isa-REPL
   leg, a consecutive-run leg with a hit-rate floor; measure wall time,
   verdict flips per call index cache-on vs cache-off, first-call latency
   at the direct call sites, refuter distribution, `Guard_Record_Stale` /
   R2 / R3 fire counts, digest cost, store I/O; re-measure 400 ms.  Testing
   via Isa-REPL against `Phi_System_Base` sources — never `isabelle build`.

After this plan: move the raw-term codec functor to
`Performant_Isabelle_ML` [author 2026-09-03 14:19].

## 11. Archaeology rulings (2026-09-03; all CLOSED)

1. ~~The 35 ms gate~~ — CLOSED 05:20: no gate.
2. ~~Judge spawn after a failed `Proved` replay~~ — CLOSED 10:29/10:31;
   SUPERSEDED 16:01: a failed replay raises `Guard_Record_Stale`.
3. ~~`guard_condition_solver` installing its own env~~ — CLOSED 15:45,
   14:54; superseded in shape by the factory.
4. ~~`Lazy`~~ — CLOSED 05:38.
5. ~~Conditional persistence~~ — CLOSED 07:11; refined 08:04 (empty table
   not written) and 16:55 (an unchanged record not rewritten).
6. ~~`final = NONE`~~ — CLOSED 11:39.
7. ~~The record value's shape~~ — CLOSED 05:42.
8. ~~The `\<phi>guard_judge` switch~~ — CLOSED 05:47.
9. ~~The 1.5× multiplier~~ — CLOSED; reconfirmed 2026-09-03 13:03.
10. ~~Store-kind refactor extent~~ — CLOSED 13:01 "好": implementation; now
    a functor (§8).
11. ~~Phase-1 enablers~~ — the "(A) 赞同" covered only the empty simpset
    slot (now `Guard_Simp_SS`); the control-flow classifier is DELETED
    [author 2026-09-03 12:59–13:01].
12. ~~Implementation-order details~~ — CLOSED: work plan.

## 12. Sixth-review rulings (2026-09-03, 07:35–11:25)

Recorded verbatim in `GUARD_CACHE_QUICK_MODE_PLAN.rev9.md` §12.  After
the synchronous redesign the following are MOOT (they concerned
asynchrony): 6 (the env's groups), 10 (cancelling judges on R2/R3), 13
(`judge_group`), 22 (`Chain_Answered` / `judge_outcome`).  Still in force:
1–5, 7–9, 11–12, 14–21, 23, with 2's word "refutable" now read as
"unprovable" and 15's `Refutable of string` gone with the chain.

## 13. Seventh-review and provenance-audit rulings (2026-09-03, 12:23–16:55)

Recorded verbatim in `GUARD_CACHE_QUICK_MODE_PLAN.rev10.md` §13.  MOOT
after the synchronous redesign: 1–4 as mechanisms (a judge's abnormal exit
is now simply an exception in the run; no crash error format, no
`Handlers` instance), 5's third item (nothing to refresh), 13's C5 (no
fork priority), 18 (no judges to spawn).  Still in force: the rest,
including 5 (`\<phi>guard_cache` off semantics; `Proved` time = the whole
call), 6 (obligation `fastforce` unbounded), 7 (lemmas carry
`proof_cache`; replay in `gen_reason'`'s own simpset), 8 (classifier
deleted), 9, 10 (R-nitpick's net), 11 (replay failed = miss), 12
(`Guard_Simp_SS` precise), 13's C6/C7/C8, 14 (one miss raises), 15
(`judge_arg` without `assms`), 16, 17 (env shape), 19, 20.

## 14. Eighth-review and synchronous-redesign rulings (2026-09-04, 03:04–03:23)

1. **No asynchrony; one optional judge in a global ref; R-conv and
   R-nitpick run inline; the judge's answer is final; no warning after a
   judge** [03:04].  Eighth-review U-INTERRUPT, U-CRASH-CLASSIFY,
   U-STEP4-PRECEDENCE, U-WORKER-SUBGROUP, U4 ("judges see no env") are
   dissolved.
2. **Relaxation A accepted** (the no-cache re-run is a recursive
   `gen_reason'` call) [03:04 "A 批准"]; U-RERUN-STEPS dissolved.
   **Relaxation B not adopted** (gate the record read on writability)
   [03:04 "B 赞同不采纳"]; the honest bullet stands (§7).
3. **`judge_arg` carries the goal state `thm`, not `goals`**; **`Provable`
   carries `lemmas`, `proof` and the proven goal state `thm`** [03:11,
   03:12]; the state is the protected, not-concluded one [03:14]; **no
   check on the returned state** [03:15 "the proof 是可以 instantiate
   schematic variables 的, 我建议就不用做任何检查"].  U-JUDGE-ARG-TH
   dissolved.
4. **R-conv and R-nitpick always run before the warning, with or without
   a judge**; **a run without a record always writes its record on normal
   completion** [03:23].
5. **`\<phi>guard_prove_timeout` → `\<phi>guard_classic_prover_timeout`**,
   shared by P-auto and R-conv; `\<phi>guard_rconv_timeout` dropped
   [03:23].
6. **`"default"` → `"assum"`, still warning on a hit** [03:23].
7. **`Refuted` → `Unprovable`** everywhere [03:23].

Eighth-review drafter fixes applied: U-REPLAY-BOUND (`p_auto_body`),
U-REPLAY-IFACE (`Auto_Fail` / `TIMEOUT` → `Guard_Record_Stale`, no
catch-all), U-LEMMA-CTXT (thms into each initial state's ctxt),
U-SWITCH-WRITE (the write gated by the switch; the store gates nothing),
U-INSTALL-ORDER, U-ELAPSED, U-DEMOTION-HONESTY, U-UNWRITABLE-HONESTY,
U-AT-END, U-TIME-CODEC, U-ANCHORS (the judge's claim that `Time.max` does
not exist is wrong — `Pure/General/time.ML:24` — and is not applied),
U-WARNING-SITES, U-INSTANTIATION-SITE.
