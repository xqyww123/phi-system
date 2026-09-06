# PLPR Guard Cache & Quick Mode — prove_or_refute rework

Status: DRAFT rev 7 (2026-09-03).  Five two-round adversarial reviews so far
(runs `wf_d6288f97-b48`, `wf_f45e300d-195`, `wf_7f84dd1e-7e0`,
`wf_2d2da81f-696`, `wf_063a55e8-e00`), every upheld finding adjudicated by
the author.  Rev 3 repaired rev 2's vocabulary defect (an undefined
"failure" conflating a run-level notion with the verdict of a guard — §1
fixes the vocabulary); rev 4 applied the third review's amendments; rev 5
applied the fourth review's amendments AND abolished a scope taxonomy
("engine scope"/"solver scope") that had accumulated across revisions
without ever being a ruled concept — the rules are one uniform set (§7),
and the per-hook exits sink is replaced by the three-valued chain verdict
(§1.2, §6).  Rev 6 applies the fifth review's 23 amendments (verdict
READY_WITH_AMENDMENTS — no further re-review required) and lands the
author's ownership ruling of 2026-09-03: scope ownership is DEFINED by
§4's slot check — the invocation whose check finds no open env and
installs one is the owner; a nested run finds the env in place, inherits
it, and owns nothing.  Rev 7 (same day) executes a batch of author
rulings that strip the drafting's accretions back to the original
design: the exit join is COMPLETE (the drafted deadline is rejected);
the verdict is `Proved | Refuted {refuter}` and the DEFAULT REFUTER is
an ordinary hook whose verdict enters the cache like any other (the
drafted provenance labels are rejected); the no-evidence warning is the
default refuter's own; the replay bound's summand is fixed at 1 s; the
blob carries no format version; instrumentation is temporary code
outside the design.  The adjudication ledger is §14.  No code has been
written.

Predecessor document: `GUARD_NITPICK_FALSIFY_PLAN.md` (the guard race this
plan dismantles).  Measurement evidence comes from
`ai-archive/cslh19-guard-race-archives-2026-09-01.tar.zst`; those runs predate
the 2026-09-02 switch of the race's prover to `p_auto_search_tac`, so timeout
defaults derived from them are marked provisional.  NOTE: `reasoners.ML` is
under active edit in the shared tree — its line anchors below are as of this
revision and §13.0 re-verifies all of them at implementation start.

---

## 1. Glossary (authoritative; use these names and no others)

### 1.1 The vocabulary rule this document lives under

A **verdict** — the answer of one guard determination — is never described
with success/failure vocabulary.  `Guard_Fails` is an ANSWER ("this guard does
not hold"), on exactly the same footing as `Proved`.  The words
"success"/"failure" are reserved for the run level (§1.3), and the words
"cold"/"warm" do not appear in this document at all.  In particular: the guard
solver returning an **empty result sequence** is the tactic-interface
*encoding* of a `Guard_Fails` verdict — it is not a failure of anything.

### 1.2 The machinery

- **guard condition** (or **guard**): a premise of the `\<condition>` family
  — `Premise mode P` with mode `MODE_GUARD` or `NO_INST`, selected by
  `is_guard_mode` (`reasoners.ML:1582-1584`) — discharged by
  `guard_condition_solver` → `prove_or_refute`
  (`Phi_Logic_Programming_Reasoner/library/reasoners.ML:1581`, `:1392`).
  Registrations that reach the solver: `PLPR.thy:1982` (`\<condition>`) and
  `:1985` (`\<condition>[NO_INST]`); `Normal_Premise` (`:1979`) reaches it
  only at nonzero values of `Phi_Reasoner_solve_obligation_and_no_defer`,
  and the two `\<safe>` sites (`:1988`, `:1991`) register
  `safe_obligation_solver`, which never calls prove_or_refute and is out of
  scope.  (`\<r>Guard` is a DIFFERENT mechanism — the cut-rule marker,
  `PLPR.thy:102` — and plays no part in this design.)
- **prove_or_refute**: the guard solver tactic.  Today: a 35 ms gate ORELSE a
  three-way race (P-auto, R-conv, per-subgoal R-nitpick).  This plan replaces
  its internals entirely.
- **determination**: one prove_or_refute invocation run through its whole
  protocol — cache lookup, the proving stage on a miss, judge spawn, entry
  write.  A determination is **completed** when that protocol ran to the end
  (whatever its verdict), and **aborted** when an exception or cancellation
  cut it short.
- **the gate**: `timed_tac 35ms (solved_states auto_search_tac)`
  (`reasoners.ML:1405`; tactic at `:957` — safe_tac + bounded-depth search).
- **P-auto**: the prover `p_auto_search_tac` (`reasoners.ML:978`): an
  asm_full_simp + quick_cut opening over the SAME depth-10 `nodup_depth_tac`
  kernel the gate uses, without the gate's closing safe pass (a fastforce
  variant was measured 4x slower and rejected; the kernel is shared).  Also
  exposed as a named public proof method (standalone value; not load-bearing
  for the cache).
- **the proving stage**: the gate ORELSE the P-auto leg.  The P-auto leg's
  bound is supplied by the CALLER: `\<phi>guard_prove_timeout` on a miss
  (§5.6), the replay bound on a `Proved (NONE, _)` hit (§5.3).  The one
  synchronous proof attempt of a determination.  Author ruling 2026-09-02:
  the gate is KEPT (the two openings/closings admit different populations
  even over the shared kernel).
- **lands** (of a replay): a replay LANDS when it yields a solved state
  within its bound.  Not landing takes one shape per arm: on the
  `SOME script` arm (§5.4), `eval_prf_str` raises `Auto_Fail`
  (`sledgehammer_solver.ML:607-627` — subgoals left open, the method not
  applying, or the bound expiring); on the `NONE` arm (§5.3), the re-run
  proving stage yields no solved state — one shape for both causes
  (`solved_states` filters to `Thm.no_prems`, `reasoners.ML:1031`;
  `timed_seq` absorbs a bound overrun into the same empty sequence,
  `:926-930`).  An empty sequence produced INSIDE a replay is a replay
  outcome, not §1.1's verdict encoding — §1.1 speaks of the guard solver's
  return, and the verdict is decided afterwards by §5.3/§5.4.  This is the
  only word used for that outcome, in both `Proved` arms.
- **R-conv**: the conversion/simplification-based refuter (today
  `r_conv_racer`, `reasoners.ML:1132`).
- **R-nitpick**: the model-finding refuter (pinned Nitpick over the external
  Kodkod process; today `r_nitpick_racer`, `reasoners.ML:1320`).
- **quick mode**: the execution discipline of the new prove_or_refute — the
  only mode.  Synchronously: cache lookup, then at most the proving stage.  A
  guard the proving stage cannot prove receives the verdict `Guard_Fails`
  immediately (the guard is **assumed false**); refutation evidence is
  gathered asynchronously by a judge.
- **verdict** (the value of a cache entry):
  `Proved of string option * Time.time | Refuted of {refuter : string}`
  (author ruling 2026-09-03 on the encoding, restoring the original
  design's two outcomes — "provable 就记录证明和时间, refuted 就记录
  refuted").  Every determination ends in exactly one of the two: the
  proving stage proves, or the judge's chain refutes — and the chain
  ALWAYS refutes, because its lowest-priority hook is the default
  refuter (author ruling 2026-09-03: "the default warner is just an
  ordinary hook"), which warns the user and answers `Refutable
  ("default", ())`.  The run-time answer `Guard_Fails` (§1.1) is the
  solver's immediate return on the refuting side; the entry it earns is
  written when the judge settles (§6.2).
  - In `Proved (src, t)`: `src = NONE` means "proved by the built-in proving
    stage" — its replay re-runs the proving stage directly, never through
    method-text parsing.  `src = SOME text` is a genuine Isar proof script,
    replayed by `eval_prf_str`
    (`auto_sledgehammer/library/sledgehammer_solver.ML:632`).  An empty
    script is unrepresentable by construction.  Cross-reference:
    `sledgehammer_solver.ML:598-604` retired the empty string as a proof
    text in the proof store for exactly the ambiguity this encoding removes;
    a guard entry must never be populated from a proof-store record without
    minding that stock `""` records exist there.  `t` is the proof's
    measured execution time in standard-machine time
    (`Phi_Proof_Store.standard_time`, `cache_file.ML:799`).
  - In `Refuted {refuter}`: the name of the hook that answered — an
    evidence-bearing refuter (`"R-conv"`, `"R-nitpick"`) or the default
    (`"default"`); the datatype has no way to claim refutation without
    naming the refuter, and the name is what later decides silence
    versus warning on a hit (§5.5).  The drafted provenance labels
    (`Assumed_Unreviewed`, `Reviewed_Silent`) are REJECTED (author ruling
    2026-09-03): the default's verdict is a verdict like any other.
- **refutation hook chain**: the priority-ordered registry of refuters, held
  in a `Handlers` instance (`library/tools/Hook.ML:116`; smaller priority
  runs first, `Hook.ML:10`) and populated ONLY through `add_refuter` (§6),
  which bounds and classifies every hook body at registration.  Its
  lowest-priority member is the **default refuter** (the author's
  original design; an earlier drafting proposal to drop it was
  withdrawn 2026-09-03): an ordinary hook like the others, which prints
  today's warning and answers `Refutable ("default", ())`, so
  `Handlers.invoke` never returns `NONE` in practice.
- **chain verdict** (author ruling 2026-09-02, replacing the fourth
  review's exits-sink machinery): what one invocation of the refutation
  hook chain can say —
  `datatype chain_verdict = Actually_Provable of aux | Refutable of
  string (*hook name*) * evidence`.  `Actually_Provable` is phase 2's LLM
  judge finding that the guard is in fact provable, carrying auxiliary
  lemmas; phase 1 has no producer of it.  Hooks return
  `chain_verdict option`, so with `Handlers.invoke`'s first-`SOME`-wins
  fold a judge's outcome space is exactly three-valued:
  `SOME (Actually_Provable _)` | `SOME (Refutable _)` | `NONE` — and
  `NONE` is reached only if the default refuter is absent (a registry
  defect, §6), never in normal operation.
- **evidence**: the payload a refutation hook may return beside its name;
  `unit` in phase 1 — dropped at the merge, only the hook name surviving
  into `Refuted` (§6).  Phase 2's LLM judge and the Nitpick countermodel
  are the reserved first inhabitants.
- **async judge** (or **judge**): one `Future` task per determination that
  took §5.6's `Guard_Fails` arm — a miss, or a `Proved` hit whose replay
  did not land (§5.3/§5.4); a `Refuted` hit spawns nothing (§5.5).
  Its body runs the refutation hook chain for that guard and returns a
  `judge_outcome` on every path (§6).  Judges never write the cache;
  they return values, and the owner writes the returned `Refuted` into
  the table at the merge (§6.2).  Warning is not the judge's job either:
  it is the default refuter's, the last hook of the chain (§6.3).
- **run-scoped environment** (**env**): the record shared by one scope;
  its seven fields (§4): `run_id`, `cache_key` (the lazy store key),
  `recorded` (the lazily read blob), `consumed`,
  `state` ({closed, entries, judges} — one var, so closedness gates the
  `Proved` entry write and the judge registration by one decision, §4),
  `probe_group`, `work_group`.  It lives in a `Proof_Data` slot and flows
  through the scope inside the ctxts of the engine's states (§4).
- **scope owner**: the invocation whose §4 slot check found no open env
  and installed one — ownership is DEFINED by that one structural act
  (author ruling 2026-09-03), and the owner alone runs §4's exit
  protocol.  An invocation whose check finds the slot occupied by an
  open env INHERITS it and owns nothing.  WHO opens is a mechanism fact,
  never a rule category (author ruling 2026-09-02: there is ONE uniform
  rule set and no scope taxonomy): `gen_reason'`
  (`library/reasoner.ML:910`) when reasoning starts,
  `guard_condition_solver` itself when it is called with no env open (its
  direct call sites), and §4's defensive rule for a foreign ctxt.
- **guard digest**: the ENTRY key of one determination (its key in a
  scope's entry table; never referred to as just "the key") —
  `Hasher.all_goals (ctxt, th)` (`auto_sledgehammer/library/Hasher.ML:224`):
  the FNV-1a structural digest of the state's subgoals only
  (conclusion-free), salted with the theory name and every assumption of
  ctxt via `hash_in_context'` (`Hasher.ML:200`).  Taken IN CONTEXT, never of
  a bare term.  (The whole-proposition formula rev 1 used is the one this
  repository retired as not fork/promise-invariant, `cache_file.ML:856-859`.)
- **store key**: the key of one scope's blob in the guard cache —
  `"plpr-guard-cache:" ^ Hasher.hash_in_context ctxt (Thm.prop_of initial)`
  of the scope's first pulled initial state (§8).  This is its ONLY name in
  this document; R2/R3's tombstone granularity is one store key.
- **final outcome** (carrying the **final digest**): what a scope's
  reasoning ended with, as an option — `SOME` the final digest
  (`Hasher.hash_in_context ctxt' (Thm.prop_of th')`, `Hasher.ML:210`) of
  the resulting state, or `NONE` when the scope completed with no
  resulting state (a determination whose verdict was `Guard_Fails`).  The
  digest is deliberately a different formula from the guard digest: it
  must carry the conclusion.  Validation (§7.R3) compares final outcomes
  option-wise at EVERY cache-consuming scope's exit; the digest's known
  fork/promise instability is tolerated — a mismatch costs one no-cache
  re-run and never a wrong result.
- **run id**: a process-wide serial int allocated when a scope opens; stamped
  on every event-log record of the scope (§10).  Identity, not content.
- **the exit join**: at scope exit the owner joins EVERY outstanding
  judge, with no set-level bound (author ruling 2026-09-03: a drafted
  deadline-cut design was REJECTED — gathering the evidence is the
  system's purpose, so the owner waits for all of it).  Per-judge
  bounding is `add_refuter`'s job and is the only time bound; external
  cancellation of the scope (§4's exception path) is the only thing
  that stops the wait.
- **control-flow classifier**: the extensible predicate identifying PLPR's
  control-flow exceptions, hosted in Performant_Isabelle_ML (§9).
- **LLM judge / re-run loop / verdict var**: phase 2 (deferred, §9).

### 1.3 Run-level vocabulary

- **run success / run failure**: `gen_reason'` returning `SOME` is
  success; returning `NONE` — the search exhausted without deriving the
  goal — is failure, and this is the ONLY failure event in the design.
  Stated of the OWNER's run: a nested inheriting `gen_reason'` run
  returning `NONE` is consumed by the enclosing engine as ordinary
  backtracking (`reasoner.ML:628-641`, `:1262`; `nested.ML:42-45`) and is
  a run-failure event for no rule in this document.
  Callers treat `NONE` as a first-class answer (`reasoner.ML:947`); only
  `reason1` turns it into an error.  A guard receiving `Guard_Fails`
  during a run does NOT make the run fail — the engine backtracks to
  other rules; verdicts and run outcomes are orthogonal.
- An invocation of the guard solver outside any reasoning run (its direct
  call sites: `local_value.ML:168`, `generic_variable_access2.ML:181`,
  `:264`, `toplevel0.ML:364`) has NO run to fail: its question is "prove
  or refute this guard", and both verdicts answer it.  It completes and
  exits normally either way; with a `Guard_Fails` verdict it returns the
  empty result sequence, and the callers' error continuations
  (`guard_condition_solver1` / `guard_condition_solver'`) raise their
  errors AFTER the env's exit protocol has completed.  Its recording and
  validation follow the same uniform rules as everything else (§7).
- **aborted** (any scope): the protocol was cut short by an exception or
  cancellation before the exit protocol ran.  Aborted scopes write nothing
  and delete nothing (§7).
- **cache-consuming scope** (the single name; §7.R2 and §7.R3 use no
  other): a scope in which at least one lookup hit an entry that came
  from the scope's `recorded` blob — operationally, a scope whose env's
  `consumed` flag is set (§4).  An entry the same scope wrote is an
  in-scope reuse, not cache consumption: it consults nothing that could
  be stale.
- **no-cache re-run**: the single re-run performed after a stale record was
  deleted (§7.R2/R3); nothing is left to consult, and its result is recorded
  under the normal rules.

## 2. Motivation

Two facts from the corpus measurements drive this rework:

1. Refutation work dominates guard-race wall time: ~88 % of the corpus's
   determinations end with the verdict that the guard does not hold (median
   refuted 607 ms, undecided 2367 ms), while that verdict is behaviourally
   identical to assuming the guard false — `refuted` and `undecided` both
   yield the empty result (`reasoners.ML:1526,1530`); only diagnostics
   differ.  (These determinations sit overwhelmingly inside reasoning runs
   that themselves succeed — the statistic is about verdicts, not about
   run outcomes.)
2. Refutation results are inherently uncacheable item-by-item: there is no
   cheap validity check for "a countermodel existed".

The design responds by (a) issuing `Guard_Fails` immediately when the proving
stage cannot prove (quick mode), (b) moving all refutation work off the
critical path into async judges, and (c) recording every completed
determination's verdict — `Proved` or `Refuted {refuter}` (author's
original design), backstopped by an end-to-end validity check per scope
(§7).

Soundness note: none of this can produce an unsound theorem.  Every PLPR step
is a legal inference; a verdict only selects which rules apply.  A wrong
`Guard_Fails` yields a different-but-valid derivation or a visible run
failure — never a wrong theorem.  (Author-accepted frame, 2026-09-02.)

## 3. Architecture overview

```
scope owner (gen_reason' | guard_condition_solver), on entry:
  ├─ slot check: the ctxt of the first pulled initial state carries no
  │  open env?  → create env, install it into the ctxts handed onward
  │    (gen_reason': lazy Seq.map over the initial states;
  │     guard_condition_solver: into the ctxt it hands to oblg_template).
  │  Occupied by an OPEN env → INHERIT: no ownership, no exit
  │  protocol (§4).
  │  This one check DEFINES the owner (§1.2).
  ├─ … reasoning …
  │     └─ prove_or_refute (reads the env from its ctxt parameter,
  │        which Phi_Reasoners.wrap hands it — registrations unchanged)
  │           ├─ lookup by guard digest
  │           │    ├─ hit Proved (NONE, t)   → re-run the proving stage under
  │           │    │                           §5.3's floored replay bound;
  │           │    │                           if it does not land, take the
  │           │    │                           Guard_Fails arm of step 6 (§5.3)
  │           │    ├─ hit Proved (SOME s, t) → eval_prf_str replay under the
  │           │    │                           replay bound; if the replay
  │           │    │                           does not land, treat as a miss
  │           │    ├─ hit Refuted {refuter} → pure read: return Guard_Fails;
  │           │    │                           silent if refuter carries
  │           │    │                           evidence, the default's
  │           │    │                           warning if "default" (§5.5);
  │           │    │                           spawn NOTHING, write nothing
  │           │    └─ miss ↓
  │           ├─ the proving stage (gate 35 ms ORELSE P-auto ≤ 400 ms)
  │           │    ├─ proves → entry Proved (NONE, measured std time)
  │           │    └─ does not prove → spawn a judge; return Guard_Fails
  │           │                        (the judge's Refuted {refuter} is
  │           │                        written at the merge)
  ├─ at exit (owner only; §4's order): close → snapshot the judge list →
  │  join ALL outstanding judges (complete, §6.1) → cancellation probe →
  │  merge judge outcomes → validation (§7) → [R2/R3 event:
  │  tombstone → one no-cache re-run → adopt its result] → otherwise
  │  persist (§8)
  └─ clear the slot in the returned state, where one is returned (§4)

async judge (Future task, one per determination that took the
             Guard_Fails arm of step 6 — §1.2's judge entry), body:
  refutation hook chain, ascending priority — every hook bounded and
  protected by add_refuter at registration (§6):
    100  R-conv     (\<phi>guard_rconv_timeout, default 300 ms)
    200  R-nitpick  (inner \<phi>guard_refute_timeout = 2000 ms;
                     hang net = that + 5 s = 7000 ms, reasoners.ML:1494)
    1000 (reserved: LLM judge, phase 2)
    1000000 default refuter: warn the user, answer Refutable "default"
    — chain verdict: SOME Actually_Provable | SOME Refutable
      (NONE only if the default is missing)
    — the body returns judge_outcome on every path (Chain_Ran of the
      chain verdict option | Judge_Aborted of exn, §6), so an escaping
      exception can never cancel the shared work group
```

What disappears: the `Race.race` call and the three racer wrappers in
prove_or_refute (`reasoners.ML:1503-1508`; `Race.race` has no other caller;
the `Race` module stays in Performant_Isabelle_ML), the in-race `protocol`
var (`:1441`), and `\<phi>guard_race_timeout` (`:1361`).  The gate stays.

What is reused, not reinvented: `Hasher` (`all_goals`/`hash_in_context`),
`Phi_Proof_Store` (everything below a new narrow blob-writer trio, §8),
`eval_prf_str` for `SOME`-script replays, `Phi_Reasoners.wrap` (kept — it is
precisely the read-only shape that hands prove_or_refute its ctxt,
`helpers1.ML:19`; the `PLPR.thy` registrations are unchanged), the
`Handlers` functor as the priority registry, the racer bodies of
R-conv/R-nitpick re-shaped into hooks (screens and soundness rules kept
verbatim: TVar screens, `can_inst` discipline, `extract_fixed_frees`,
once-derived assumptions), the two-group fork/join/cancel discipline of
`Performant_Isabelle_ML/library/race.ML` (GROUPS), and the `checked_io`
diagnostics discipline (`reasoners.ML:1430-1439`).

## 4. The run-scoped environment

The env stays in a `Proof_Data` slot and flows through ctxts (author ruling
2026-09-02; a thread-local variant was considered and rejected — scope
follows the data, like every other scoping mechanism in PLPR).  What rev 1
got wrong was not the slot but the initialization discipline: LAZY creation
required writing a ctxt back, and the guard solver's return path discards
contexts by construction.  Rev 2/3 remove the write-back need entirely:

- **Eager creation by the scope owners.**  `gen_reason'` inspects the ctxt of
  the FIRST PULLED initial state (that is where the engine hands reasoners
  their context, `reasoner.ML:813`; `gen_reason'`'s own ctxt parameter
  supplies configs — trace, step_limit, the performance and statistics
  wrappers — and the reasoner table via `Reasoners.get`
  (`reasoner.ML:910-916`), but never reaches the states — which is why
  the slot check reads the state's ctxt: check and installation act on
  the same ctxt and cannot disagree): slot empty → create an env and
  install it via a lazy `Seq.map (apfst install)` over the
  initial state sequences, re-consing the pulled state; slot occupied by
  an OPEN env → inherit (the nesting bullet below).  This one check
  DEFINES ownership (author ruling 2026-09-03): the invocation that
  installed is the owner, and every rule that speaks of "the run" means
  the owner's run (§7).  Every live call site passes a
  singleton state family (`reasoner.ML:932`, `:973`); should several
  alternatives ever be passed, the first pulled state keys the scope.
  `guard_condition_solver` does the same for its direct callers: it installs
  the env into the ctxt it hands to `oblg_template` (`reasoners.ML:336`) —
  internal to reasoners.ML, no registration site changes.  For a
  `guard_condition_solver`-opened env, the exit protocol attaches at the
  end of `oblg_template`'s `f` callback, after
  its `Seq.take 1 |> Seq.pull` (`reasoners.ML:1700-1705`), on both the SOME
  and the NONE branch; `oblg_template`'s three f-free paths (`TrueI` and the
  two `fast_inst` hits) never call `f`, so the env created for the call
  is never consulted, neither `Lazy` is forced, no exit protocol runs,
  and the env dies with the ctxt.
  "Clear the slot in the returned state" applies wherever a state carrying
  the slot is returned; an env opened by `guard_condition_solver` lives in
  a locally built context that `Phi_Reasoners.wrap` never returns
  (`helpers1.ML:19`), so there is no slot to clear there.  Creation
  allocates a record of refs; the on-disk read AND the store key are inside
  `Lazy` (the key costs a fold over every assumption of the ctxt plus the
  initial proposition, `Hasher.ML:200-210`, and a scope that never reaches a
  determination must not pay it).  The `entries` table starts EMPTY and is
  SEEDED from `recorded.entries` at the FIRST lookup — that is what forces
  the `Lazy`; the forced `recorded` value is retained unmodified for the
  whole scope as R1's baseline.  `consumed` is set by a lookup exactly when
  the entry found was among those seeded from `recorded`, so a scope whose
  `recorded` is `NONE` ends with `consumed = false` by construction.
  (Instrumentation never forces either `Lazy`, §10.)
- **Access is read-only on the ctxt path.**  prove_or_refute reads the env
  from the ctxt parameter that `Phi_Reasoners.wrap` already hands it
  (`helpers1.ML:9,19` — `wrap` feeds the incoming ctxt to the tactic and
  re-pairs that same ctxt with each result; it is the read-only shape this
  design needs, which is why the registrations stay).  All mutation goes
  through the env's `Synchronized.var` fields.  Nothing ever writes a ctxt
  back, so the 17 known ctxt-modifying reasoners cannot disturb the slot.
- **Nesting = inheritance.**  A nested `gen_reason'` (via `internal_reason`:
  `\<r>Call`, `\<r>BEGIN`, `ToR_Entry_Point`) receives a ctxt descending from
  the outer scope's states, finds the slot occupied by an OPEN env, and
  inherits it: one entry table, one judge list, one run id.  An
  inheriting run owns nothing: it runs no exit protocol, and its
  determinations write into the shared table exactly as the owner's do —
  that is all inheritance grants.  Its returning `NONE` is engine
  backtracking (§1.3) and triggers no rule; R2/R3, persistence and the
  no-cache re-run belong to the owner alone (§7).  (`chk_guard` calls the
  enclosing `loop` directly, `reasoner.ML:848`, and needs no treatment.)
- **Openness, the entry write and registration are one atomic decision.**
  The env holds ONE `Synchronized.var` containing `{closed : bool,
  entries : verdict Symtab.table (*keyed by guard digest*),
  judges : (guard digest * judge_outcome future) list}` — the entry table
  lives INSIDE the same var, so a closed env structurally refuses a
  determination's `Proved` write and its judge registration by the same
  test: each is ONE `Synchronized.change_result` (test `closed` → write
  the `Proved` entry, or test `closed` → `Future.forks` → append the
  judge), never a step a close could land between.  The test gates
  DETERMINATION-side operations; the owner's exit-step-5 merge — which
  writes the judges' `Refuted` verdicts — is the one `entries` write it
  does not gate: the owner's own protocol step, performed after close on
  a judge snapshot no determination can still extend.  Two separate
  arguments make this hold.
  Lock order (the deadlock argument): holding the env mutex across the
  fork is safe because the fork takes no lock this design ever holds
  while touching the env var.  Interruptibility (what §12.6 actually
  rests on): the `change_result` body, `Future.forks` included, runs
  inside `Thread_Attributes.uninterruptible_body` —
  `Multithreading.synchronized` RESTORES the caller's attributes for the
  body it runs (`multithreading.ML:92-115`) and `Future.forks`' own
  `SYNCHRONIZED "enqueue"` is interruptible for the same reason
  (`future.ML:463-489`), so without the wrapper an interrupt between the
  enqueue and the var update would orphan an enqueued judge.  Together: a
  judge without a joiner is unrepresentable, even against the
  repository's real never-joined fork (`hammer_or_AoA` under Async,
  `reasoners.ML:893-895`, whose forked body may reach nested reasoning
  after the outer scope ended: it then finds the env closed and opens its
  own scope, which is bounded and correct).
  A determination that finds its env CLOSED at that atomic step (the race
  window: an inheriting thread gets there just after the owner closed)
  opens NOTHING — contrast §4's defensive rule below, which DOES open a
  one-determination scope and DOES run the chain.  Here the verdict is
  returned to its caller, nothing is recorded, and a short LOCAL message
  states that this guard was assumed false with no review because its
  scope had already closed — printed locally because no judge will ever
  speak for this determination.
  Under §10 it emits a
  guard_decision record (§10).  §12.6 cites this
  operation; it is R1's fourth qualification (§7).
- **Exit order** (owner only; §3's diagram repeats it):
  1. close FIRST (flip `closed` atomically);
  2. take the judge list ONCE — a closed env structurally refuses further
     registration, so that snapshot is complete;
  3. join it IN FULL — every judge, no set-level bound (§6.1);
  4. CANCELLATION PROBE, before anything is merged, validated or
     persisted: if `Task_Queue.is_canceled probe_group` (route one —
     `cancel_group` mutates only the given group's status while
     `is_canceled` walks ancestors, `task_queue.ML:83-101`) OR any
     judge's `judge_outcome` recorded an owner-thread absorbed
     cancellation (route two — §6's classifier, race.ML:246-254), take
     the exception path below and end it with
     `Isabelle_Thread.raise_interrupt ()` (race.ML:281-297 is this
     probe's precedent and states why: the interrupt was consumed on
     absorption).  Route two is not redundant with route one: an
     enclosing `Timeout.apply` delivers exactly ONE interrupt
     (`timeout.ML:38-43`), so an absorbed one defeats it permanently.
     This step is what makes "aborted scopes write nothing" true for a
     scope owned on a worker thread;
  5. merge (§6.2), validate (§7.R3) — no warning step: the default
     refuter already warned inside any chain that reached it (§6.3);
  6. on an R2 or R3 event: tombstone the record, issue the SINGLE
     no-cache re-run, adopt the re-run's result as the scope's result,
     and let the re-run record under R1 — the firing scope itself
     persists nothing (R1's third qualification, §7).  The re-run needs
     no disable flag: it opens its own fresh scope, and the record having
     just been tombstoned, its `Lazy` read finds nothing to consult —
     §8's one-critical-section invalidation is what makes that true.
     Mechanism at a `gen_reason'`-opened scope: the owner re-invokes its
     own body on the original state sequences (every live entry path
     passes a pure `Seq.single` initial state, `reasoner.ML:932`, `:973`,
     so re-pulling re-executes nothing effectful).  Mechanism at a
     `guard_condition_solver`-opened scope: the re-run's option REPLACES
     the value produced by `Seq.take 1 |> Seq.pull` inside
     `oblg_template`'s `f` callback (`reasoners.ML:1700-1705`), so
     nothing stale has left the callback when the substitution happens;
  7. otherwise persist under R1;
  8. clear the slot in the returned state (where one is returned — see
     the eager-creation bullet).
  On the exception path (an exception or cancellation reaching the owner,
  or step 4 firing): cancel the work group, re-join it under
  `Thread_Attributes.uninterruptible` (race.ML:150-157's shape — it
  terminates because the group is cancelled), close if not already
  closed, persist nothing, re-raise (from step 4: raise the interrupt).
  This is what "aborted scopes write nothing" means operationally.
- **Both task groups** (the never-cancelled probe parent and the work child
  holding the judges) are created and parented at scope open, independently
  of which thread later forks a judge.
- **Defensive rule** (the only transient shape left): if prove_or_refute
  ever runs with no open env — a genuinely foreign ctxt from an unknown
  path — it opens a scope around that single determination: spawn, join,
  and R1 followed with nothing to read or write.  The defensive scope has
  NO store key (§8 derives the key from the scope's first pulled initial
  state, which a foreign mid-search ctxt does not supply), so its
  consultation and persistence are VACUOUS, not exempted — no rule
  branches on the opener.  Unreachable by design; stated so the
  behaviour is defined.

Env fields (phase 1):
`{run_id : int,
  cache_key : string Lazy.lazy,
  recorded : {final : string option, entries : verdict Symtab.table} option Lazy.lazy,
  consumed : bool Synchronized.var (*any hit yet?*),
  state : {closed : bool,
           entries : verdict Symtab.table (*keyed by guard digest*),
           judges : (string (*guard digest*) * judge_outcome future) list}
          Synchronized.var,
  probe_group : Future.group (*never cancelled by us*),
  work_group : Future.group (*holds the judges*)}`

## 5. prove_or_refute: one determination

Per determination (the state `th` may carry several subgoals, as today; the
external interface of `guard_condition_solver` and variants is unchanged):

1. `d := Hasher.all_goals (ctxt, th)` (the guard digest) — taken in
   prove_or_refute's goal-side `ctxt` (the imported context whose assumption
   set the refuters consume, `reasoners.ML:1116-1117`), never in the outer
   `ctxt0`: the digest must be salted with exactly the assumptions the
   determination reasons under.
2. Look `d` up in the env's entry table — the lookup consults `entries`
   only; `recorded` is reached solely through §4's seeding, never as a
   fall-back at lookup time.  The author's original design: a
   determination that PROVES writes `Proved` with its proof source and
   time; a determination that ends `Guard_Fails` gets `Refuted {refuter}`
   written by the owner at the merge (§6.2) — the refuter being whichever
   hook answered, the default included (a `Proved` entry whose replay did
   not land is DELETED from the table first, §5.3/§5.4).  (One
   qualification, §4: a determination that finds its env CLOSED completes
   normally, returns its verdict, and records nothing — R1's fourth
   qualification.)
3. **Hit, `Proved (NONE, t)`** — THE single normative statement of this
   rule; §7.R4, §12.2 and §12.4 cite it.  Re-run the proving stage ONCE,
   with the P-auto leg bounded by
   `Time.max (Time.scale 1.5 t + Time.fromMilliseconds 1000)
             \<phi>guard_prove_timeout`
   — the bound's additive summand is FIXED at 1 s, not a config (author
   ruling 2026-09-03, retiring the drafted `\<phi>guard_replay_delta`),
   and the miss budget is the bound's FLOOR (author ruling 2026-09-02):
   a replay is never granted less than a fresh search would be, so a
   `Proved` entry cannot be demoted by a timing accident.  `1.5t + 1 s`
   is exactly `Phi_Proof_Store.tolerant_time` (`cache_file.ML:832-834`),
   so the implementation REUSES it rather than restating the formula.
   The fixed 1 s summand makes the bound structurally ≥ 1 s, so the
   sub-1 ms `Timeout.apply` ignore hazard (`timeout.ML:25`; in-tree
   clamp precedent `reasoners.ML:1484-1485`) cannot arise on this arm —
   the fifth review's 1 ms clamp is subsumed.  The recorded time is not
   refreshed when the replay lands.  If it does not land, DELETE the
   `Proved` entry from the table and take the `Guard_Fails` arm of step 6
   (rationale: this replay was itself one full search — one search per
   determination, never two; the judge's `Refuted` then replaces the
   deleted entry at the merge).
4. **Hit, `Proved (SOME script, t)`**: replay via `eval_prf_str` under
   the bound `Phi_Proof_Store.tolerant_time t` = `1.5t + 1 s` (author
   ruling 2026-09-03; structurally ≥ 1 s, so `timeout.ML:25`'s sub-1 ms
   ignore hazard cannot arise) — no miss-budget floor (a script replay
   is not a search, so §5.3's floor does not apply).  The state reaching the replay is `Goal.protect 1`'d by
   `head_only` (`reasoners.ML:385-388`) and may carry k > 1 subgoals from
   the case split at `:1627-1629`; the replay passes `eval_prf_str`
   `n = Thm.nprems_of th` — a landing must close ALL k subgoals; `n = 1`
   would let closing the first alone read as landed — and the keywords
   clause every in-tree call site uses:
   `Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)`
   (`sledgehammer_solver.ML:668`, `:1508`, `:1804-1805`, `:1913`,
   `:2003`).  `eval_prf_str`
   protects/concludes internally (`sledgehammer_solver.ML:607-622`) and its
   returned ctxt' is discarded — a recorded script must be free of context
   effects.  If the replay does not land, DELETE the entry and fall to
   the miss arm (step 6 — search; a replay never substitutes for one).  Phase 1 has no producer of
   `SOME` scripts; the branch is exercised by hand-crafted entries in the
   smoke test, including a k > 1 one.
5. **Hit, `Refuted {refuter}`**: a pure read — return `Guard_Fails` (the
   empty result sequence) at the cost of the digest and the lookup,
   SILENTLY: evidence is on record, exactly as today's evidence-backed
   refutations are silent (`reasoners.ML:1526`) — UNLESS `refuter =
   "default"`: then the entry records that the guard was assumed false
   without evidence, and the hit prints the default's warning again,
   exactly as today's re-run would (the default hook's own text; nothing
   cache-specific — the entry only spares the chain).  Author ruling
   (final): the hit path spawns nothing and writes nothing; a hit is
   never re-judged (R4).
6. **Miss**: run the proving stage —
   `timed_tac 35 (solved_states auto_search_tac) ORELSE
    timed_tac \<phi>guard_prove_timeout (solved_states p_auto_search_tac)`
   (default 400 ms, provisional: measured p99 = 258 ms / observed family max
   293 ms, but on the pre-switch tactic; re-measure at §13.7).
   - It proves: write `Proved (NONE, measured elapsed through
     standard_time)` — the elapsed of the WHOLE proving stage, gate leg
     included: the same quantity §5.3's replay bound scales; return the
     solved states.  (Future providers — auto_sledgehammer, AoA — slot in
     here as further search fallbacks emitting `SOME` scripts.)
   - It does not prove: write NOTHING; spawn a judge (§4 — one
     `Synchronized.change_result` tests closedness and forks) carrying
     everything it needs captured now (ctxt, goals, screened
     assumptions — the once-derived discipline of `reasoners.ML:1444-1478`),
     and return `Guard_Fails` immediately.  The owner writes the judge's
     `Refuted {refuter}` at the merge (§6.2).  No warning here: warning
     is the default refuter's job, at the end of the chain (§6.3),
     mirroring today's split where evidence-backed refutations are silent
     and only the default warns.

## 6. The refutation hook chain and the async judges

**Registration.**  Hooks are never registered into the `Handlers` table
directly and never invoked through a raw fold.  The single route is

`add_refuter : priority -> {name : string, bound : Proof.context -> Time.time} ->
               (judge_arg -> chain_verdict option) -> Context.generic -> Context.generic`

(There is no `Time.time Config.T` in Isabelle — `Config.value` is
bool/int/real/string, which is why every timeout in this tree is an
int-milliseconds option read through `Time.fromMilliseconds`.  The `bound`
function is the driver's `Timeout.apply` budget; hook bodies are forbidden
their own.  R-conv registers a reader of `\<phi>guard_rconv_timeout`;
R-nitpick registers the DERIVED hang net `refute_timeout + seconds 5.0`,
keeping §11's "hang net stays derived" true.)

with

`type judge_arg = {ctxt : Proof.context, outer_ctxt : Proof.context,
                   can_inst : bool, goals : cterm list, assms : term list}`
`datatype chain_verdict = Actually_Provable of aux | Refutable of string * evidence`
`type evidence = unit  (*phase 1; see the glossary*)`
`type aux  (*phase 2: the LLM judge's auxiliary lemmas; abstract and
            uninhabited in phase 1 — no producer exists*)`

`outer_ctxt` is the direction-sensitive second argument of R-conv's
`Variable.export ctxt outer_ctxt` (the "do not swap the two" rule at
`reasoners.ML:1113`, N1 ruling at `:1120-1130`); `can_inst` selects between
its freeze and export refutation disciplines.  The two fields exist so §3's
"racer bodies kept verbatim" is actually satisfiable.

`add_refuter` builds the registered function itself, with PROTECTIVE duties
only (author ruling 2026-09-02, replacing the fourth review's exits-sink
scheme): `Exn.capture_body` around `Timeout.apply` around the body.  An
interrupt re-raises (cancellation is never a hook outcome — the rule
race.ML and `sledgehammer_solver.ML`'s interrupt re-raise already share);
`Timeout.TIMEOUT` → the hook answers `NONE` and the chain proceeds to
the next hook (a timeout IS the ordinary "nothing found" for most
guards, exactly as in today's race); any other exception → recorded via
`Exception_Log` (that write itself under the `checked_io` discipline §3
reuses — diagnostic I/O never decides an outcome), then the hook answers
`NONE` and the chain proceeds — a crashing hook is a BUG SIGNAL that
lives in the exception log, not an operating condition; the chain then
simply reaches the default refuter, and nothing about HOW it got there
is recorded.  The driver bounds hooks; self-bounding is not a contract
anyone must remember.
No per-hook outcome flows anywhere: the chain's only channel is
`Handlers.invoke`'s `chain_verdict option` return.  Per-hook timings and
outcomes, where wanted, are TEMPORARY instrumentation written inside the
hook bodies themselves (the `nitpick_probe` precedent) or emitted by the
wrapper under §10's `log_guard_decision` gate — absent or disabled in
production.

**Judge body** (fifth review; race.ML:226-259 is the shape).
`add_refuter`'s wrapper protects one HOOK; the judge body — the one
function forked per judge — wraps the whole chain invocation and RETURNS
a value on every path: `Thread_Attributes.uninterruptible_body` around
`Exn.capture_body` around `run (Handlers.invoke ...)`, classifying its
own outcome as

`datatype judge_outcome = Chain_Ran of chain_verdict option
                        | Judge_Aborted of exn`

with the classifier distinguishing our own work-group cancellation, an
owner-thread absorbed cancellation (race.ML:246-254 — what §4's
cancellation-probe route two reads), and a foreign interrupt.  WHY it
must return rather than raise: `Future`'s `assign_result` reacts to ANY
`Exn.Exn` result by cancelling the task's group (`future.ML:422-437`) —
here the SHARED work group — and a cancelled group is permanently dead
(`worker_exec`'s valid test, `future.ML:222-226`): one escaping exception
would kill every sibling judge and poison the scope for every judge
forked after it.  Per-judge child groups are NOT an alternative:
`Task_Queue.cancel` collects running threads only from tasks in the
cancelled group itself (`task_queue.ML:294-301`), so the owner's single
`cancel_group work_group` would then stop interrupting running judges.
The env's judge field is `(guard digest * judge_outcome future) list`
(§4).

**Chain content** (priority bands: 1–99 future cheap refuters, 100 cheap
refuters, 200 heavy model search, 1000 judges; bands order correctly across
theories, while the per-theory unique-priority constraint (`Hook.ML:127-128`)
makes the reserved 1000 band a convention, not a reservation):

| priority | hook | bound | notes |
|---|---|---|---|
| 100 | R-conv | `\<phi>guard_rconv_timeout`, default 300 ms (author ruling 2026-09-02) | today's `r_conv_racer` body minus the race protocol; in a sequential chain its bound is the delay R-nitpick pays on every guard it cannot refute |
| 200 | R-nitpick | inner `\<phi>guard_refute_timeout` (2000 ms); hang net = +5 s = 7000 ms | today's `r_nitpick_racer` body; subgoals tried SERIALLY within the one judge task (deliberate trade of today's per-subgoal racers, `reasoners.ML:1444-1478`, for lower pool pressure; corpus n_goals is almost always 1 — flip back if §13.7's tail measurement objects) |
| 1000 | *(reserved: LLM judge, phase 2)* | own mandatory bound | |
| 1000000 | **default refuter** | trivial | the author's original design, an ORDINARY hook: prints today's warning text (`reasoners.ML:1486-1489`) and answers `Refutable ("default", ())`; the value 1000000 reads as "floor" and matches PLPR's GLOBAL_CUT priority threshold |

The default refuter is registered through `add_refuter` like every other
hook and enjoys no special treatment anywhere — its `Refuted
{refuter = "default"}` enters the cache exactly as R-nitpick's does
(author ruling 2026-09-03).  `Handlers.invoke` returning `NONE` is
therefore a registry defect (the default missing), handled at the
judge's call site by warning and recording nothing — never a normal
outcome.  Invariant §12.1 stays type-level: `Refuted` cannot be
produced without a hook name.

**Carrier** (author ruling: Future tasks).  One task per determination
that took §5.6's `Guard_Fails` arm — a miss, or a `Proved` hit whose
replay did not land (§5.3/§5.4); a `Refuted` hit spawns nothing
(§5.5) — `Future.forks` into the env's work group — a fresh child of
the scope's never-cancelled probe group (race.ML GROUPS; both groups made at
scope open).  Consequences: PIDE/command cancellation reaches judges free
through group ancestry; the owner can cancel judges alone without touching
the command; the pool caps how many judges EXECUTE at once (not how many
are outstanding); queued judges never leak (the exit protocol always
settles them).  The fork, spelled out because two of its fields are
load-bearing: `Future.forks {name = "PLPR.guard_judge", group = SOME
work_group, deps = [], pri = ~1, interrupts = true}`.  `pri = ~1` keeps
diagnostic work strictly below reasoning; `interrupts = true` is what
makes every per-hook bound and the owner's group cancellation effective —
a job's attributes are fixed at fork time (`future.ML:473-476`) and
`Timeout.apply` runs its body under the attributes in effect on entry
(`timeout.ML:44`), so an uninterruptible judge would defeat both
(race.ML:260-263 and cache_file.ML:790 set it for the same reason).  Each
outstanding judge retains its captured ctxt/goals/assumptions until scope
exit — where today each capture dies with its race.

**Join** (owner exit, §4 order; the join must not run with interrupts
already deferred — obligation inherited from race.ML:60-71):

1. Join EVERY outstanding judge (author ruling 2026-09-03: the owner
   waits for ALL of them; an earlier drafted deadline that cut
   stragglers was rejected as defeating the purpose of the review
   machinery — no `\<phi>guard_judge_deadline` exists).  Each judge is
   individually bounded (≈ 300 ms + 7000 ms worst) by `add_refuter`'s
   per-hook `Timeout.apply` budgets — those are the ONLY time bounds.
   MECHANISM: one `Future.join_results` over the whole snapshot, with
   interrupts enabled (the header's race.ML:60-71 obligation — precisely
   so that external cancellation can still interrupt the owner and take
   §4's exception path: cancel the work group, uninterruptible re-join,
   persist nothing).  On a worker thread `join_results` executes
   still-queued judges INLINE on the owner's thread
   (`future.ML:510-527`) — under the complete join this is a feature,
   not a hazard: the owner drains its own queue instead of waiting on
   pool scheduling of `pri = ~1` tasks.  Off a worker thread each judge
   is awaited (`Single_Assignment.await`, `future.ML:530-541`) until the
   pool runs it.  TERMINATION: every judge, once running, finishes
   within its per-hook budgets (`{physical = false}`, i.e. elapsed minus
   GC time), and every queued judge is either executed inline by this
   very join (worker) or scheduled by a pool that makes progress (off
   worker).  `join_results` and never `join`/`joins`, so no judge's
   settlement re-raises here.  The exit-join wall time is a first-class
   §13.7 measurement — the number to watch under the complete join.
2. Merge outcomes into the entry table (the scope owner's thread only).
   The join uses
   `Future.join_results` and never `join`/`joins`, so the merge is defined
   over `judge_outcome Exn.result`, and it is a four-row table
   (author ruling 2026-09-02 on its shape — this table IS the whole
   rule; no witness clauses, no per-hook data):
   - `Exn.Res (Chain_Ran (SOME (Refutable (hook, _))))` → write
     `Refuted {refuter = hook}` under the guard's digest (the evidence
     payload is dropped; only the name survives) — the normal outcome of
     every judge, `hook = "default"` included;
   - `Exn.Res (Chain_Ran NONE)` → nothing: the default refuter was
     missing (a registry defect; the judge warned at its call site);
   - `Exn.Res (Chain_Ran (SOME (Actually_Provable _)))` → phase 2's
     re-run trigger (unreachable in phase 1 — no producer);
   - `Exn.Res (Judge_Aborted _)` or `Exn.Exn _` (a judge killed before
     it started — its body never ran) → nothing, without aborting the
     scope HERE: whether the SCOPE aborts is §4's cancellation probe's
     decision, which reads `Judge_Aborted`'s absorbed-cancellation
     classification in the step before this merge.
   Scopes opened off worker threads
   need no extra rule: with no ancestor tie for a group cancellation to
   travel (race.ML:132-146), external cancellation arrives as an interrupt
   on the owner's own thread, takes §4's exception path, and the scope
   persists nothing.
3. Warnings are NOT an owner step (author ruling 2026-09-03, restoring
   the original design).  The warning for a guard no evidence-bearing
   hook could refute IS the default refuter's body (§6's table): it runs
   last in the chain, on the judge's thread, prints today's text
   (`reasoners.ML:1486-1489`), and answers `Refutable ("default", ())`.
   Attribution is no concern: `future_job` captures the forking thread's
   `Position.thread_data` and restores it when the task runs
   (`future.ML:441-452`), so the warning lands on the same command an
   owner-thread warning would.  A chain that found evidence never reaches
   the default and prints nothing (today's silent refutation); an
   aborted judge prints nothing (it was killed).  A later hit on a
   `"default"` entry re-prints the same warning (§5.5) — today's per-run
   behaviour for undecided guards, unchanged.

**A scope containing exactly one determination** (mechanically: the guard
solver called with no env open — a mechanism note, not a rule category):
the same protocol as everywhere, stated for its measurable consequences.  A `Proved` verdict
spawns no judge and the exit costs nothing extra.  A `Guard_Fails`
verdict joins its one judge synchronously (bounded only by that judge's
own `add_refuter` budgets) before the
empty result reaches the caller and the caller's error continuation
fires; so the first such determination pays the sequential chain where
today's race runs the refuters in parallel — §13.7 measures that
difference.  Later determinations of the same guard hit the record and
return immediately.  Store granularity: one store key and, when the table
changed, one locked append per determination (§8).

## 7. Recording, validation, invalidation

R1–R4 are stated of a SCOPE and, where they speak of a run, of the run
of the invocation that OWNS that scope.  Ownership is not a wording
convention but §4's one structural decision (author ruling 2026-09-03):
the invocation whose slot check found no open env and installed one is
the owner.  A nested inheriting `gen_reason'` run returning `NONE` is
engine backtracking (§1.3; `reasoner.ML:628-641`, `:1262`;
`nested.ML:42-45`) and is a run-failure event for NO rule below.

- **R1 (recording — the author's original design).**  Every COMPLETED
  determination ends with its verdict entry in its scope's table (§5) —
  `Proved` written by the determination, `Refuted {refuter}` by the
  owner at the merge once its judge has settled (§6.2).  At
  scope exit, the table is persisted iff the `recorded` Lazy was FORCED
  and `entries` differs from the retained `recorded.entries` baseline
  (§4; forced-and-`NONE` counts as an empty baseline, so such a scope
  persists iff `entries` is non-empty).  A scope that performed no
  lookup forces nothing, computes no store key and persists nothing —
  the test cannot be read as forcing the Lazy at every exit.  What is
  written is the WHOLE seeded table, never a delta: the store is
  last-write-wins per key, and a partial blob would destroy every entry
  the scope did not revisit.  The recorded `final` is the scope's final
  outcome (§1.2): `SOME` the resulting state's digest, `NONE` when the
  scope completed with none.  Four qualifications, none a scope category
  — and exactly ONE of them is the rule set's ruled exception, the one
  §14's canary counts: (1) the scope-owning `gen_reason'` run FAILED —
  the scope records nothing; there is no trustworthy account of what it
  learned (author ruling 2026-09-02; §7.R2 — THE ruled exception);
  (2) an ABORTED scope writes nothing and deletes nothing (a state any
  scope can be in, not a category); (3) a scope that fired R2 or R3
  persists nothing of its own table — the tombstone stands and only the
  no-cache re-run records (a consequence of those rules' own
  tombstone-and-re-run semantics, not a new exception); (4) a
  determination that found its env CLOSED records nothing (§4 — a state:
  the scope was already sealed).  §4's defensive rule is NOT on this
  list: it follows R1
  with no store key (§8 derives the key from the scope's first pulled
  initial state, which a foreign ctxt does not supply), so there is
  nothing to read and nothing to write.
- **R2 (run failure against a record — author ruling 2026-09-02).**
  The scope-owning `gen_reason'` run of a cache-consuming scope (§1.3)
  FAILS: that failure has proven the record stale — the record exists
  only because a previous run succeeded, and now the same reasoning does
  not.  Durably delete the record (tombstone, §8), then re-run once with
  no cache.  The re-run's result is what is reported, and it records
  under R1: success → a fresh record; failure → nothing written, and the
  deletion stands.  (One doubled run per staleness event, on BOTH
  branches: a re-run that recorded was itself a run that consulted
  nothing, so a later failure against ITS record is a NEW staleness
  event, not a continuation of this one; a re-run that also fails writes
  nothing, and later attempts find no record and run singly.  A scope
  with `recorded = NONE` is never cache-consuming (§1.3), so R2 cannot
  fire on it — there is no record to tombstone; in particular, an
  ordinary failing owner run that only reused entries it wrote itself
  never reaches R2, and a nested inheriting run's `NONE` reaches no rule
  at all — this section's head.)
- **R3 (validation — the same rule at every scope).**  Every
  cache-consuming scope compares, at exit, its final outcome with the
  recorded one, option-wise: `SOME d` matches `SOME d'` iff the digests
  are equal; `NONE` matches `NONE`; every other combination is a
  MISMATCH.  Match → accept (persist under R1 if changed).  Mismatch →
  the record is stale: tombstone, one no-cache re-run, reported and
  recorded under R1.  (A scope with `recorded = NONE` is never
  cache-consuming and validates nothing; a failed owner run is
  R2's business — failure is not an outcome and matches nothing.)  This
  one comparison also arbitrates every replay discrepancy THAT CHANGES
  THE SCOPE'S FINAL OUTCOME: a `Proved` hit whose replay does not land
  ends its determination with a `Guard_Fails` verdict (§5.3/§5.4),
  usually the scope's final outcome then differs from the recorded one,
  and the mismatch deletes the record and re-determines everything fresh
  — one uniform mechanism, no per-arm or per-scope special case.  The
  residual — a deletion that leaves the final outcome unchanged — is
  the outcome-invisible staleness class below.
- **R4 (hits are faithful — author ruling: hits obey the cache; a hit is
  never re-judged).**  A `Refuted` hit returns `Guard_Fails` (silently,
  or with the default's warning when `refuter = "default"`, §5.5);
  nothing is spawned, nothing written.  A `Proved` hit replays under
  §5.3 (the `NONE` arm) or §5.4 (the `SOME` arm) — those are the rules'
  single normative statements; either way a replay that does not land
  DELETES the entry from the scope's table (an in-table removal, no
  tombstone) and the determination proceeds as a miss; whether the
  RECORD survives is then R3's business at the scope's exit (§7.R3).
- **Outcome-invisible staleness (recorded honestly; no rule and no
  product feature answers it — author ruling 2026-09-03).**  A stale
  `Refuted` entry — the countermodel rested on a definition since
  changed, without changing the goal or the assumptions, hence without
  changing the digest — is reproduced faithfully (R4), steers the run
  onto the RECORDED derivation, and the final digests match; R2/R3 can
  structurally never fire on it.  The self-limiting property of R3
  covers entries whose staleness changes the outcome, not this class.
  A `Refuted {refuter = "default"}` entry is the largest member: "a
  simp lemma added later would now prove it" reproduces faithfully and
  warns on every hit.  (A replay-induced entry deletion USUALLY changes
  the scope's final outcome, and R3 then deletes the record at that very
  exit — but membership in this class is not structurally excluded: the
  final outcome is a digest of the resulting STATE (`Hasher.ML:200-210`)
  and says nothing about the derivation, so when the engine backtracks
  onto another rule that reaches the same resulting state, the digests
  are equal and R3 does not fire.)  A third member, named honestly:
  `Refuted {refuter = R-nitpick}` rests on Nitpick models the pipeline
  cannot certify genuine (the quasi_genuine handling at
  `reasoners.ML:1291-1305`); the run-time answer is unaffected — a judge
  never decides one — but a wrong model refutation permanently silences
  the guard's warning on later hits.  The drafted "R5" — a user-facing
  invalidation command/entry point — is REJECTED as a product feature:
  the `.guard-cache` file is gitignored and regenerable, and any
  invalidation tooling is development-only code outside this design.
- **Residual collision class**, recorded honestly: two determinations in one
  theory with identical subgoals and identical assumptions but different
  simpsets/clasets share an entry (the digest ignores simpsets).  When the
  shared entry changes the outcome, R3 catches it for one no-cache re-run;
  when it is outcome-invisible, it stays.
- Entries are keyed by guard digest alone — no positional counter (author
  ruling, adopting the first review's relaxation): the digest already
  carries what a counter was for (theory name, all assumptions, each
  subgoal with its premises), and this repository documents allocation-order
  keys as destabilised by prove_or_refute's wall-clock gates
  (`<repo root>/docs/PHI_VC_SOLVER_PLAN_V2.md` §8c; one such gate is still
  live at `reasoners.ML:1607`).  With per-digest keys, a timing flip at the
  proving-stage boundary re-runs one guard instead of misaligning a scope.

## 8. Persistence via Phi_Proof_Store

- **Writer**: a new narrow trio in `PHI_PROOF_STORE` —
  `get_cached_blob : theory -> string -> string option`,
  `update_cached_blob : theory -> string * string -> unit`,
  `invalidate_cached_blob : theory -> string -> unit` — with the work
  behind them stated honestly (fourth review: "verbatim reuse" is not
  achievable, since every touch point is keyed to the one `.proof-store`
  file per theory): `cache_file.ML` gains a STORE KIND
  (`Proof_Store | Guard_Cache`) threaded through `store_path`, `lock_path`,
  `store_file_key`, `probe_writable`, `load_store_raw`, `append_record`,
  `compact_store` and `invalidate_store` (unparameterised, a guard append
  would land in `<thy>.proof-store` under the proof-store mutex);
  `openning_stores` is re-keyed by (theory long name, store kind), and
  that re-key's closure is the module's whole entry-point surface, not
  eight functions: `force_reload` (`:599`), `get_entry_i` (`:610`),
  `get_store_i` (`:616`), `get_store` (`:619`), `register_async_task`
  (`:623`), `close_store` (`:637` — the sharp case: its
  `Symtab.delete_safe` on the bare theory name would compile unchanged
  and silently drop the wrong kind's in-memory table mid-theory),
  `invalidate_store` (`:653`), `update_cached_proof` (`:693`),
  `invalidate_proof_cache` (`:731`), plus the path-derived
  `try_write`/`store_is_writable`/`warn_not_writable` (`:455-465`) and
  `ensure_new_format` (`:510`) — §13.5 is scoped to that surface;
  `async_tasks` is always empty for the guard kind (its only writers are
  sledgehammer proof paths), so the guard file's `Theory.at_end` hook
  always takes the null-tasks branch;
  `migrate_legacy` runs for `Proof_Store` only; a SECOND `Theory.at_end`
  registration compacts and closes the guard file — without it nothing
  ever compacts it and the bounded-growth claim below is void; and the
  writability warning names its store kind and file, with `warned_dirs`
  keyed by (directory, store kind).  The trio still SKIPS the `written`
  collision table and `proof_mark` (`cache_file.ML:554-580`, `:669-680`):
  a scope blob is not a proof text, its key is not a proof id, and its
  value legitimately changes across runs — routing it through
  `update_cached_proof` would fire the collision alarm on correct
  operation and destroy the evidence that alarm preserves.
- **Storage and versioning policy (author ruling 2026-09-02, third review
  F7)**: guard blobs live in their OWN file, `<thy>.guard-cache`
  (`store_path` parameterised by extension), and that extension is
  GITIGNORED (`*.guard-cache`, `*.guard-cache.lock` — a §13.5 step).  The
  committed `.proof-store` files stay committed: a proof text is
  self-validating (a replay that does not land deletes it), but a
  `Refuted` entry rests on a countermodel search that is not re-run on a
  hit, and a default-true cache must not ship one developer's machine-
  and load-dependent verdicts to every checkout and CI.
- **Honest costs**: first touch of a theory's guard-cache file reads and
  CRC-scans the whole file (it is per-theory and starts small — unlike the
  38 MB committed proof stores, which this design never touches on the
  guard path); each write goes through the per-file append mutex, the
  deliberately unmemoised `probe_writable` probe, and a blocking `setlkw`
  file lock, then one `File.append` — one such write per changed scope (at
  a scope containing exactly one determination: per determination whose
  table changed).  §13.7 measures
  first-touch read cost and append counts/latency; whether to batch
  guard-blob writes above some latency threshold is a FUTURE author
  decision, taken (if ever) against those measurements — batching would
  trade away the "between scope exits nothing mutates a record"
  property below, so it is not a free knob and is NOT committed to here.
- **Store discipline**: last-write-wins per key (the store's own semantics);
  deletion via tombstone.  The guard cache writes at most once per scope, at
  exit, after the join has merged every judge outcome the scope will ever
  contribute — so between scope exits nothing mutates a record, and the
  only deletions are R2/R3 staleness tombstones.
  `invalidate_cached_blob` (internal — R2/R3's tombstone writer, not a
  user entry point) drops the in-memory `openning_stores` entry in
  the same critical section as its tombstone append —
  `invalidate_store`'s discipline (`cache_file.ML:653-665`): ONE
  `Synchronized.change (store_append_lock (store_file_key thy))` section
  with `store_append_lock` OUTERMOST, preserving the documented
  v → fcntl → openning_stores lock order (`:485-487`, `:649-650`); NOT
  `invalidate_proof_cache`'s two-section shape (`:731-741`), which would
  leave a window between the tombstone and the in-memory drop.  So a
  no-cache re-run cannot re-read what the run just invalidated.
- **Store key** (glossary §1.2): `"plpr-guard-cache:" ^
  Hasher.hash_in_context ctxt (Thm.prop_of initial)` of the scope's first
  pulled initial state (inside the env's `Lazy`).  Already theory- and assumption-salted (`hash_in_context'`,
  `Hasher.ML:200-208`).  Tolerance, stated as §1.2 states it for the final
  digest — this is the same conclusion-bearing formula, and no stability is
  claimed: the key can be moved by fork/promise discharge of an enclosing
  obligation, by the `head_only` protection state at the scope-open point,
  and by any change to the assumption set.  A moved key costs a miss and
  one extra record, never a wrong verdict; growth is bounded (one record
  per distinct key, last-write-wins, compaction dedupes by key).
- **Value**: one MessagePack-encoded string — `{final : digest option,
  entries : (guard digest, verdict) list}` — built with the same
  mlmsgpack packers `Proof_Store_Format` already uses
  (`MessagePackBytesIO.Pack`/`Unpack`, `cache_file.ML:69-70`), riding as
  the string value of an ordinary `PUT (key, time_ms, value)` record
  (`cache_file.ML:66`): the store's value type is a plain string, so the
  guard kind changes nothing at the store layer.  NO format-version
  field (author ruling 2026-09-03): a blob the unpacker cannot decode is
  simply discarded — the read path already treats undecodable as
  "nothing to consult" — and a shape-compatible layout change bumps the
  store-key prefix instead, orphaning old records until compaction drops
  them.  Proof sources inline in the blob (`Proved`'s `string option` is
  one tag byte plus the script when present).  The record's `time_ms`
  field carries the scope's elapsed through `standard_time`
  (informational).
- **No user-facing invalidation** (author ruling 2026-09-03): the
  drafted command/entry point is rejected as a product feature.  The
  file is gitignored and regenerable; deleting `<thy>.guard-cache` is
  the only sanctioned reset, and whatever the developer writes to poke
  the store during development is not part of this design.
- **Enable switch** (author ruling): `\<phi>guard_cache`, DEFAULT TRUE — a
  debugging/measurement knob only; the cache is always on in normal use.  A
  `\<phi>guard_cache = false` run neither consults NOR persists — a triage
  session must not overwrite the records it is inspecting.  Its sibling
  `\<phi>guard_judge = false` makes every scope persist nothing
  (consultation unaffected): a session that suppresses judges must not
  durably record a table missing the `Refuted` entries they would have
  earned.  Deliberately
  not `enable_proof_store`: the two govern different risks, and §13.7 must
  measure the guard cache in isolation.
- Read path: on env creation, `get_cached_blob` (inside the `Lazy`); a
  missing or undecodable record simply means there is nothing to consult.

## 9. Phase 2 (DEFERRED — author ruling) and what lands now

Landed in phase 1, both cheap and orthogonal:

- **The control-flow classifier**, hosted in Performant_Isabelle_ML beside
  `Interrupt_Family` (it cannot live in PLPR: `sledgehammer_solver.ML` sits
  strictly below phi-system in the session graph —
  `auto_sledgehammer/ROOT` → Isa-Mini → `Phi_Logic_Programming_Reasoner/
  ROOT`).  Shape: an extensible predicate defaulting to `K false`, to which
  PLPR appends `Success`, `Global_Cut`, `Explorative_Backtrack` (and later
  `Rerun_Request`) at load time — the lightweight appended-classifier
  precedent, not a new registry.  `Phi_Sledgehammer_Solver.normalise`
  (`sledgehammer_solver.ML:566-570`) and `eval_prf_str0`'s catch-all
  (`:625-627`) gain a re-raise-before-classify FIRST clause testing it,
  beside their existing interrupt re-raise; `reason_record`
  (`reasoner.ML:939-945`) is redefined in terms of the same predicate.
  House rule, documented at the definition: an interrupt is cancellation,
  never a hook or proof outcome; a PLPR control-flow exception is
  navigation, never a proof outcome.
- **The auxiliary-lemma simpset slot**: a `Proof_Data` simpset, declared
  empty, always merged into the proving stage's context — the LLM judge's
  future payload target.
- The `eval_prf_str` tracing line (`sledgehammer_solver.ML:608`) goes
  behind a verbosity gate (a small auto_sledgehammer patch) before any
  per-determination replay lands.

Deferred (built when the LLM judge exists).  The shape below is DRAFTED,
not ruled — only the deferral itself is an author ruling; every phase-2
behavior is re-submitted for rulings when phase 2 starts:

- The re-run loop is a loop AROUND the owner's scope: run to completion,
  join, read the verdict var, merge the judge's auxiliary lemmas into the
  slot, invalidate the entries the judge named, re-enter.  ZERO engine
  changes — no parameter threading through `gen_reason`/`apply_tactic`
  (the env is reachable wherever a poll could live), and phase 1 does not
  poll at all.  Mid-run abort is added only if a measured LLM-judge latency
  profile against measured scope lengths shows it pays; the poll's true
  cost is `Synchronized.value` = an uninterruptible section plus a mutex
  round trip, not a plain read.
- Work-group lifecycle, unbreakable by shape: iteration renewal goes
  through one `start_new_iteration` that allocates a fresh child of the
  probe group and empties the judge list in the same atomic step (a
  cancelled group is permanently dead — tasks forked into it yield
  interrupts, never execution).
- Iteration cap: a small constant (3); overrun = warn and accept.
- Convergence: each iteration either proves a named guard or the LLM
  judge names nothing new (to be designed with phase 2).

## 10. Instrumentation

Instrumentation is TEMPORARY measurement code, not a designed surface
(author ruling 2026-09-03; the pattern is the `nitpick_probe` precedent
and §6's already-ruled temporary per-hook timings).  The design commits
to exactly ONE permanent record:

- **guard_decision** (synchronous side, EXACTLY one per determination;
  the successor of today's guard_race record, `reasoners.ML:1562-1572`):
  verdict token ∈ `proved | assumed | cache_proved | cache_refuted`, a
  replay field ∈ `no_replay | landed | not_landed`, elapsed, the guard
  digest, the run id, n_goals, and — on the MISS path only, so §12.2's
  hit-cost claim survives with logging on — the full goals/assms/tvars
  payload today's record carries (what makes per-family corpus analyses,
  this plan's own evidence base, repeatable).  `assumed` is a distinct
  token — never `refuted` (label honesty).  Emitted only when
  `log_guard_decision` is set (today's `log_guard_race`,
  `reasoners.ML:154,1363`, renamed — the gate the guard_race record
  already carries, `:1541-1543`), under `checked_io`.

Everything else §13.7's acceptance runs need — per-judge settlements and
evidence rates, per-scope hit/write/R2/R3 counts and store keys, the
exit-join wall time, digest cost, store I/O costs — is temporary
instrumentation written for those runs and stripped or left dormant
afterwards.  It has no permanent fields, is not specified here, and must
not change system behavior — in particular it must not force the env's
`Lazy` fields on a path that would not force them anyway.
`nitpick_probe` recording stays inside the R-nitpick body, unchanged.

## 11. Configuration summary

| option | status | default |
|---|---|---|
| `\<phi>guard_prove_timeout` | NEW | 400 ms (provisional — evidence predates the P-auto tactic switch; re-measure at §13.7) |
| `\<phi>guard_rconv_timeout` | NEW | 300 ms (author ruling 2026-09-02) |
| `\<phi>guard_refute_timeout` | kept | 2000 ms; hang net stays derived (+5 s = 7000 ms) |
| *(no join deadline)* | — | author ruling 2026-09-03: the exit join is complete; the drafted `\<phi>guard_judge_deadline` is REJECTED (§6.1, §14) |
| *(no replay-delta config)* | — | author ruling 2026-09-03: the replay bound's additive summand is FIXED at 1 s — the bound is `Phi_Proof_Store.tolerant_time` (§5.3) |
| `\<phi>guard_cache` | NEW | true — debugging/measurement knob only; off = neither consult nor persist |
| `\<phi>guard_judge` | NEW | true — debugging/measurement knob only (disables judge spawning; off = the scope persists nothing, §8; §13.7's A/B needs it) |
| `\<phi>guard_race_timeout` | RETIRED with the race | — |
| `\<phi>log_guard_race` → `\<phi>log_guard_decision` | renamed | false, as today (`reasoners.ML:1437`) |

Naming batch — APPROVED by the author 2026-09-03: the option names
above; the refuter-name strings written into `Refuted {refuter}`
(`"R-conv"`, `"R-nitpick"`, `"default"`); the two module names
(`PLPR_Guard_Cache`, `PLPR_Refuters`).  Still pending: §4's closed-env
local message text.

## 12. Invariants (the elegance criterion: structural wherever possible)

1. Every `Refuted` entry names its refuter: `Refuted` cannot be
   constructed without a hook name, and the default refuter signs as
   `"default"` — so an evidence-less refutation is never mistaken for an
   evidence-bearing one.
2. A `Refuted` hit spawns nothing, writes nothing, and is never
   re-judged; its cost is one guard digest and one table lookup.  A
   `Proved` hit re-executes a bounded replay; a replay that does not land
   is resolved by §5.3 / §5.4 (one search per determination, never two).
3. Store writes happen only at the exit of completed scopes, and never
   from a failed scope-owning `gen_reason'` run; aborted scopes touch
   nothing; deletions happen only through R2/R3 staleness.
4. Every replay is bounded, per §5.3 / §5.4 (`1.5t + 1 s` =
   `tolerant_time`, floored at the miss budget on the `NONE` arm; the
   fixed 1 s summand makes both bounds structurally ≥ 1 s, so
   `timeout.ML:25`'s sub-1 ms ignore hazard cannot arise); a
   `Proved (NONE, _)` replay that does not land never triggers a second
   search.
5. The driver bounds and protects every hook (`add_refuter`); a hook
   author cannot break the join barrier's termination, and a hook crash
   is an `Exception_Log` entry, never a chain abort.
6. Ownership is total: the invocation whose §4 slot check finds no open
   env installs one and owns the scope (§1.2); a determination that
   meets a CLOSED env at the atomic write step is not making that check
   and opens nothing (§4).
   Openness, the entry write and judge registration are one atomic
   decision whose body runs uninterruptibly (§4 — the uninterruptible
   wrapper, not lock order, is what this rests on), so a judge without a
   joiner is unrepresentable and a closed env structurally refuses BOTH
   writes from a determination (the owner's post-close merge, §4 exit
   step 5, is its own protocol step).
7. Only the scope owner's thread merges the entry table; judges return
   values, and the only printing in the chain is the default refuter's
   warning (§6.3); every shared MUTABLE env field is a `Synchronized.var`
   (the task groups are immutable values; the `Lazy` fields synchronize
   internally).
8. The only route by which a `Guard_Fails` answer produces a cache entry
   is a judge settling `Exn.Res (Chain_Ran (SOME (Refutable _)))` and
   the owner writing `Refuted` at the merge (§6.2's four-row table).
9. Soundness is untouchable: verdicts only select which rules PLPR tries.
10. A record shown stale — an R3 final-outcome mismatch, or an R2 run
    failure against it — is not on disk after the run that discovered it.

## 13. Implementation order

0. Mechanical pre-work: re-verify every line anchor (the shared tree is
   under active edit); land the control-flow classifier in
   Performant_Isabelle_ML + the two normaliser clauses + the
   `reason_record` redefinition; the `eval_prf_str` verbosity gate.
1. The refutation hook chain module: the `Handlers` instance,
   `add_refuter` (protective wrapper only — no per-hook outcome channel),
   the `chain_verdict` datatype, R-conv and R-nitpick bodies re-shaped
   (screens kept verbatim), and the default refuter (today's warning
   text, `Refutable ("default", ())`) — independently testable.
2. prove_or_refute rework WITHOUT cache/judges (the chain invoked
   synchronously in place of the race, temporary — landed in the SAME
   session as step 3, never left standing in the shared tree: in this
   interim worst-case guard latency is the SUM of the hook bounds where
   today it is their max): corpus equivalence check
   against archived baselines (expected verdict flips only in the known
   noisy classes); migrate `Test/Guard_Race_Smoke.thy` (it drives
   guard_condition_solver directly and asserts on the guard_race record
   kind and exit columns) to the guard_decision record — it stays the
   probe battery.
3. The run-scoped environment + async judges + join/merge/warn + the
   guard_decision record (plus this step's temporary instrumentation,
   §10).  GATE, one leg per step, both measured from a
   step-3-instrumented corpus run: step 4 proceeds only if guard digests
   repeat WITHIN a scope (group guard_decision records on (run id, guard
   digest) and report the fraction of determinations that are not the
   first for their digest in their run; a scope containing exactly one
   determination contributes zero); step 5 proceeds only if STORE KEYS
   repeat ACROSS
   two consecutive corpus runs (from that run's temporary scope-level
   instrumentation, §10, over runs A and B — the same condition §13.7's
   fifth leg tests).
4. The in-memory cache + R1–R4.
5. Blob persistence, in order: the store-kind parameterisation of
   `cache_file.ML` (§8), the re-keyed `openning_stores` — an edit to the
   module's whole entry-point surface; §8 enumerates it — the second
   `Theory.at_end` registration, the store-kind-aware writability warning;
   then the trio (`get_cached_blob`/`update_cached_blob`/
   `invalidate_cached_blob`) + the `\<phi>guard_cache`
   and `\<phi>guard_judge` switches + the `*.guard-cache`/
   `*.guard-cache.lock` .gitignore entries — with a smoke test asserting a
   guard append never touches `<thy>.proof-store` and that theory end
   compacts both files.
6. The auxiliary-lemma simpset slot.
7. Corpus acceptance runs, with the store RESET or isolated between legs
   (each leg gets its own store path): the four cache × judges legs, a
   concurrent Isa-REPL leg (judges now share the pool with reasoning
   instead of blocking inside a race), and a FIFTH leg — a second
   consecutive corpus run against the store the first leg persisted, the
   only leg where a persisted hit can occur — with a hit-rate floor as a
   named acceptance criterion.  Measure: wall time and verdict flips,
   the first-determination latency at the guard solver's direct call
   sites vs today's race, the
   evidence rate — per pass, the fraction of that pass's own
   `Guard_Fails` determinations refuted by an evidence-bearing hook
   rather than the default — the exit-join
   wall time distribution (the cost of the complete join, per scope and
   at the guard solver's direct call sites), the R2/R3 fire count
   and the fraction of scopes that paid a no-cache re-run (making
   §7.R2's "one doubled run per staleness event" falsifiable in the
   field), the outstanding-judge high-water mark, the guard digest's
   computation time (on the gate-proved population in particular — the
   one path this design newly taxes), first-touch store read cost, and
   append counts/latency (all via the run's temporary instrumentation,
   §10).
   Re-measure the
   provisional default (400 ms); update
   `GUARD_NITPICK_FALSIFY_PLAN.md` with a dated pointer to this plan.

Testing throughout via Isa-REPL against `Phi_System_Base`-loaded sources
(never `isabelle build`); the PhiEx corpus run is the acceptance harness.

## 14. Adjudication ledger (2026-09-02/03; everything below is CLOSED)

Vocabulary (this revision's central repair):
- Verdicts are answers; success/failure vocabulary is run-level only
  (§1.1/§1.3).  Rev 2's §7 "failure" rules and the second review's
  amendment built on them (the all-`Guard_Fails`-hits / ≥1-`Proved`-hit
  split) are SUPERSEDED by the author's rules R1–R3.

Author rulings:
- Recording: `Proved` with proof source and time, `Refuted` with the
  refuter's name — the original design ("provable 就记录证明和时间,
  refuted 就记录 refuted", 2026-09-02 12:03); the intervening drafting
  reading that split the refuting side into provenance labels was
  REJECTED on 2026-09-03 (see below).
- `gen_reason'` run failure: record nothing; a cache-consuming failed run
  deletes its record and re-runs once with no cache; the re-run records on
  success and the deletion stands regardless (R2).
- One rule set for every scope, regardless of which entry point opened it;
  the callers' error continuations fire after the scope exits and are not
  the scope's concern.
- Hits obey the cache faithfully; a hit is never re-judged (R4).  (The
  "explicit invalidation" R5 once paired with it was REJECTED as a
  product feature on 2026-09-03 — see below.)
- `Proved of string option * Time.time`; `NONE` = the built-in proving
  stage (replacing rev 2's reserved `""`, same behaviour, misuse now
  unrepresentable).
- `Phi_Reasoners.wrap` and the `PLPR.thy` registrations stay: `wrap` is the
  read-only ctxt conduit the design needs; the earlier de-registration
  wording is withdrawn.
- Uniform replay for `Proved` entries from day one (the future
  auto_sledgehammer/AoA providers emit `SOME` scripts into the same slot);
  replay bounds on the guard scale (§5.3), never `tolerant_time`
  (SUPERSEDED on the tolerant_time half by the 2026-09-03 replay-bound
  ruling below: the fixed 1 s summand makes the bound coincide with
  `tolerant_time`, which is now reused).
- The gate is kept; P-auto is `p_auto_search_tac`; the 400 ms default is
  provisional.
- R-conv default 300 ms, as a named config.
- No floor hook; `NONE` handled at the judge call site (REVERSED
  2026-09-03: the default refuter is an ordinary hook and its verdict
  enters the cache like any other — see the verdict-encoding ruling).
- Phase 2 deferred; phase 1 lands the control-flow classifier (in
  Performant_Isabelle_ML — layering verified) and the empty lemma slot,
  plus the two phase-1 enablers the author ruled separately: the
  `eval_prf_str` tracing gate (2026-09-02 10:29, "不需要 eval_prf_str
  里一行无条件的 tracing") and — as the classifier's whole point — the
  re-raise-before-classify clauses in `normalise`/`eval_prf_str0`.
- `\<phi>guard_cache` default true, debugging/measurement only; dedicated
  switch, not `enable_proof_store`; likewise `\<phi>guard_judge`.
- Guard digest `Hasher.all_goals` in context; no positional counter; blob
  writer trio bypasses the proof-text collision machinery; scripts inline
  in the blob.
- R-nitpick subgoals serial within a judge (drafted deliberate trade — flip
  back if §13.7's tail measurement objects).

Third-review rulings (2026-09-02, run `wf_7f84dd1e-7e0`; all 24 amendments
applied in this revision):
- The `Proved (NONE, _)` replay bound is FLOORED at the miss budget
  (`Time.max (1.5t + delta) \<phi>guard_prove_timeout`, §5.3) — a `Proved`
  entry cannot be demoted by a timing accident (author-approved; the
  delta was later FIXED at 1 s by the 2026-09-03 ruling, retiring the
  config).
- Guard blobs live in their own gitignored `<thy>.guard-cache` file; the
  committed `.proof-store` policy is unchanged (author-approved).
- The central-noun correction: guards are the `\<condition>` family, not
  `\<r>Guard`; P-auto shares the gate's depth-10 kernel (no fastforce) —
  the glossary now states the code's truth.
- `add_refuter` takes `bound : Proof.context -> Time.time`; `judge_arg`
  carries `outer_ctxt` and `can_inst`.
- (The rev-4 exits-sink and multi-clause witness are SUPERSEDED by the
  fourth-review ruling below.)
- The join deadline is owner-observed (RETIRED by the author ruling of
  2026-09-03: there is NO join deadline — the exit join is complete,
  §6.1; the fifth-review narrowing and rev-6 drafting choice (ii) fall
  with it).
- `\<phi>guard_judge = false` scopes persist nothing.
- A third record kind, guard_scope, gives hit rate a denominator
  (guard_scope was later WITHDRAWN with the 2026-09-03 instrumentation
  ruling — hit rate's denominator now comes from the acceptance run's
  temporary instrumentation); §13.7
  gains the fifth (consecutive-run) leg and §13.4-5 are gated on measured
  key repetition.

Fourth-review rulings (2026-09-02, run `wf_2d2da81f-696`; verdict
READY_WITH_AMENDMENTS — no further re-review required):
- The per-hook exits sink and the multi-clause `Reviewed_Silent` witness
  are DELETED (author ruling): hooks return `chain_verdict option`
  (`Actually_Provable | Refutable`; `NONE` = unknown), and the merge is
  §6.2's four-row table over `Exn.result` — a judge's settlement and its
  chain verdict are the only inputs the merge needs.  A crashed hook
  answers `NONE` through its wrapper and is recorded in `Exception_Log`
  (the "does not block `Reviewed_Silent`" trade is MOOT since the
  2026-09-03 verdict-encoding ruling: no such label exists).  Per-hook timings
  and outcomes are temporary instrumentation in hook bodies, absent or
  gated off in production.
- `cache-consuming` counts only hits on entries seeded from the recorded
  blob; `entries` is seeded at first lookup; the retained `recorded` value
  is R1's persistence baseline; blobs are whole tables, never deltas.
- The join is stepped, with an owner-observed clock (the stepping and
  the clock are RETIRED with the deadline, author ruling 2026-09-03);
  the judge fork is `{pri = ~1, interrupts = true}` under the work group
  (unchanged).
- `cache_file.ML` gains a store kind threaded through its file machinery,
  a re-keyed `openning_stores`, and a second `Theory.at_end` registration
  for the guard file.
- "store key" is a defined glossary term and the only name for it; the
  guard digest is the ENTRY key; `evidence = unit` in phase 1.
- §13's gate splits per step (within-scope digest repetition for step 4,
  cross-run store-key repetition for step 5); all three record kinds sit
  behind `log_guard_decision` (two of the three record kinds later
  WITHDRAWN by the 2026-09-03 instrumentation ruling).
- Amendment 19 of the fourth review: WITHDRAWN AS MOOT — see the
  fifth-round rulings below.

Fifth-round author rulings (2026-09-02; these ordered the fifth review):
- The scope taxonomy ("engine scope" / "solver scope") is ABOLISHED.  It
  was drafting residue accumulated across review rounds, never a ruled
  concept.  The rules are ONE uniform set for every scope — R1 recording,
  R3 option-wise final-outcome validation at every cache-consuming
  scope's exit, R4 faithful hits, R5 explicit invalidation (R5 later
  REJECTED as a product feature, 2026-09-03) — with the
  single ruled exception that a failed `gen_reason'` run records nothing
  and deletes what it consumed (R2).  Which entry point opened an env is
  a mechanism fact; no rule branches on it.
- Amendment 19 of the fourth review (`Proved (SOME _, _)` never demoted;
  entry removed instead) is WITHDRAWN AS MOOT: under uniform R3, an
  in-scope demotion makes the final outcome mismatch the record at that
  very exit, the whole record is deleted and re-determined fresh —
  overwrite and removal converge to the same end state.
- A fresh full review of the entire revised document was ordered.

Fifth-review rulings (2026-09-03, run `wf_063a55e8-e00`; verdict
READY_WITH_AMENDMENTS — no further re-review required; all 23 amendments
applied in rev 6):
- OWNERSHIP IS STRUCTURAL (author ruling 2026-09-03): `gen_reason'`
  reads the Proof_Data slot of the first pulled state's ctxt — empty →
  install a fresh env and own the scope; occupied by an open env →
  inherit and own nothing.  That one check defines the owner, and
  R1–R5's subject follows from it (§7's head).  A considered alternative
  — hoisting the facility one level up, to `gen_reason'`'s three callers
  (`internal_reason`; the dead `internal_reason_s`/`reason_sXXX` pair;
  the caller-less `reason_tac`) — was researched and rejected by the
  author in favour of this check.
- The judge body returns `judge_outcome` on every path (race.ML:226-259's
  shape): an `Exn.Exn` judge result would cancel the shared work group,
  so for a body that ran it is made unrepresentable.
- The exit protocol gains the cancellation probe (both routes) and an
  explicit R2/R3 re-run step; a scope that fired R2/R3 persists nothing
  of its own table.  R1's qualification list closes at FOUR, of which
  only the first — the failed owner run — is the rule set's single ruled
  exception (the canary above stays absolute); the defensive scope
  FOLLOWS R1 with no store key and is not on the list.
- Replay bounds carry a 1 ms clamp on both arms (SUBSUMED 2026-09-03:
  the fixed 1 s summand makes both bounds structurally ≥ 1 s); the
  keywords clause is
  `Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)`; §8's
  atomicity discipline is `invalidate_store`'s (cache_file.ML:653-665);
  the `openning_stores` re-key closure is the module's whole entry-point
  surface; R5's exemption and R2's convergence parenthetical are stated
  honestly; "cache-consuming scope" and "a scope containing exactly one
  determination" replace the earlier phrasings.
- Rev 6 drafting choices, each within an alternative the fifth review's
  judge explicitly offered (delegated by the author to drafting, flagged
  for the verification pass): (i) `entries` folded INTO the
  `{closed, entries, judges}` var — the structural option — rather than
  a flag test on every write; (ii) [MOOT — the 2026-09-03 complete-join
  ruling removed the deadline this step served] the OFF-worker join step
  bounded by `Timeout.apply`; (iii) the closed-env refusal message printed
  locally (the "named exception" framing is MOOT since the 2026-09-03
  warning ruling — any thread may print);
  (iv) R1's list worded as four QUALIFICATIONS of which only the failed
  owner run is a ruled exception — resolving the review's own tension
  between "add a fourth exception" (amendments 3/9) and "the canary
  stays absolute" (amendment 22).
- A rev-6 verification pass (run `wf_dbd23480-8b1`, four verifiers + a
  judge) confirmed every amendment's landing site individually and ruled
  all four drafting choices SOUND; its five upheld wording repairs (all
  edit residue, none design) are applied in this revision: the §6.1/§14
  `Timeout.apply` narrowing annotated, "main thread" unified to "the
  scope owner's thread" (§6.2/§6.3/§12.7), §12.6 restating ownership
  with both conjuncts, §3's inherit branch keyed on an OPEN env, and the
  owner's post-close merge exempted from the closedness gate (§4/§12.6).

Author ruling (2026-09-03, the exit join):
- THE EXIT JOIN IS COMPLETE.  The drafted deadline design
  (`\<phi>guard_judge_deadline`, the stepped clock-observed join, the
  expiry `cancel_group`, the deadline-cut settlement class, the
  pre-cancel `is_finished` snapshot) was an UNAUTHORIZED drafting
  deviation from the author's original design ("join all async judges")
  and is REJECTED in full: cutting judges and persisting their entries
  as `Assumed_Unreviewed` defeats the purpose of the review machinery.
  The owner waits for every judge; `add_refuter`'s per-judge budgets are
  the only time bounds; external cancellation of the scope (§4's
  exception path and cancellation probe) is the only thing that stops
  the wait.  Consequences: every judge of a COMPLETED scope settles, so
  every `Guard_Fails` determination of such a scope gets its `Refuted
  {refuter}` written (the default's included, per the verdict-encoding
  ruling below); a judge can fail to settle only through the
  foreign-interrupt residual; rev-6 drafting choice (ii) is moot; §11
  loses `\<phi>guard_judge_deadline`.

Author ruling (2026-09-03, the verdict encoding — the largest correction
of this revision):
- `verdict = Proved of string option * Time.time | Refuted of {refuter :
  string}` — the original design's two outcomes, verbatim.  The drafted
  provenance labels (`Assumed_Unreviewed` / `Reviewed_Silent` attached
  to a persisted `Guard_Fails`) were the drafter's 2026-09-02 proposal,
  never approved, and are REJECTED as 胡闹.  Second half of the same
  ruling: THE DEFAULT REFUTER IS AN ORDINARY HOOK ("the default warner
  is just an ordinary person") — the chain's lowest-priority member,
  warning the user and answering `Refutable ("default", ())`, and its
  `Refuted {refuter = "default"}` enters the cache exactly like
  R-nitpick's.  This REVERSES the 2026-09-02 "no floor hook" ruling,
  which had been the drafter's proposal (the first review's finding 14)
  and the seed of the whole provenance detour.  Consequences, all
  applied: every determination ends `Proved` or `Refuted {refuter}`;
  `Guard_Fails` is the run-time answer only; the miss arm spawns and the
  owner's merge writes; a hit on a `"default"` entry re-prints the
  default's warning (today's per-run behaviour), an evidence-bearing hit
  is silent; a `Proved` entry whose replay did not land is DELETED, not
  demoted; `Chain_Timed_Out` and B2 are moot; §12.1 and §12.8 restated.

Author ruling (2026-09-03, the warning):
- The no-evidence warning is the DEFAULT REFUTER's own body, printed at
  the end of the chain on the judge's thread — the author's original
  design RESTORED.  The drafted relocation to the owner's exit ("judges
  never print", justified by PIDE attribution) is withdrawn:
  `future_job` restores the forking thread's Position data
  (`future.ML:441-452`), so the concern was unfounded.  Consequences:
  no warning step in the exit protocol; no per-scope count message for
  aborted judges; §12.7's "owner-only Output" and its named exception
  are gone.

Author ruling (2026-09-03, instrumentation):
- Instrumentation is TEMPORARY measurement code, not a designed surface.
  One permanent record survives — guard_decision, the successor of
  today's guard_race record, behind the one existing gate.  The drafted
  three-kind record system (guard_judge, guard_scope) and the fifth
  review's added measurement fields (settle timestamp, digest-elapsed,
  first-touch read, append latency) are WITHDRAWN as over-design —
  several had already lost their consumers to the complete-join and
  no-batching rulings.  Whatever §13.7 needs is temporary, stripped
  after acceptance, and may not change system behavior (no `Lazy`
  forcing).

Rev 7 drafter decisions under the author's 2026-09-03 delegation
(peripheral matters decided by drafting; each independently vetoable):
- [MOOT since the verdict-encoding ruling] `Chain_Timed_Out`: was to
  keep a timed-out chain from minting `Reviewed_Silent`; a timed-out
  chain now simply reaches the default refuter, and the variant is
  removed.
- Warning conditions mirror today's split (evidence → silent, no
  evidence → warn, once per guard per scope), per the author's "warn
  the user, as today" instruction; WHO prints is the author's warning
  ruling above (the drafted §5.5 hit warning is gone with the
  verdict-encoding ruling — no evidence-less hit exists).
- §5.4's not-landing script replay falls to the miss arm — NOT a
  drafter decision: it is the proof store's standard replay semantics,
  adopted by the author's 2026-09-02 10:29 ruling ("统一成全部走重放")
  and restated to the author at 10:31 ("非空脚本重放失败 → 落回搜索路径,
  这是 proof store 的标准语义; `""` 重放失败不得再落回搜索") without
  objection; §5.3/§5.6's shapes unchanged.
- Kept: goal-side digest ctxt, whole-proving-stage elapsed as `t`, no
  refresh of `t` on a landed replay, `\<phi>guard_cache` off also
  persists nothing, judge `pri = ~1`, R-nitpick subgoals serial (its
  §13.7 revert trigger stands), undecodable blob = nothing to consult
  (now doubly anchored by the blob-format ruling), a `Proved` hit whose
  replay did not land spawns a judge (§1.2's judge entry), the aux
  simpset slot merged into the proving stage's context (empty in phase
  1, so a no-op merge).
- §13.2's synchronous-chain interim lands in the same session as step 3
  and never stands alone in the shared tree.

Author ruling (2026-09-03, "R5"):
- The drafted user-facing invalidation route (an Isar command and/or a
  public ML entry point, at store-key or whole-theory granularity) was
  never approved and is REJECTED as a product feature.  The rule set is
  R1–R4; the outcome-invisible staleness class stays recorded honestly
  in §7 with no rule answering it.  `invalidate_cached_blob` survives
  only as R2/R3's internal tombstone writer.  Any invalidation tooling
  the developer writes is development-only code outside this design.

Author ruling (2026-09-03, the blob format):
- NO format-version field.  A blob the unpacker cannot decode is
  discarded — the read path treats it as nothing to consult; a
  shape-compatible layout change bumps the store-key prefix instead.
  The cache is regenerable; simplicity wins over versioning.

Author ruling (2026-09-03, the replay bound):
- The additive summand of the replay bound is FIXED at 1 s — no
  `\<phi>guard_replay_delta` config.  `1.5t + 1 s` coincides with
  `Phi_Proof_Store.tolerant_time` (`cache_file.ML:832-834`), which the
  implementation reuses; rev 5's "would drown `t`" differentiation from
  tolerant_time is superseded by this ruling, and the fifth review's
  1 ms clamps are subsumed (both bounds are structurally ≥ 1 s).
