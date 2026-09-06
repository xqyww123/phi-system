# PLPR Guard Cache — prove_or_refute rework

Status: rev 10 (2026-09-04).  Rev 9 went through a seventh adversarial
review (NOT_READY, 23 upheld) and a provenance audit that found five
mis-attributed and thirteen drafter-decided behaviors.  Everything was put
to the author on 2026-09-03 12:23–16:34; §13 records those rulings.  They
changed the design in six places: hooks and judges are first-class (a hook
decides its own timeout; any exception escaping a hook crashes the run with
an error carrying the original message; the `Handlers` functor is used
directly); a run that has a record raises on its FIRST miss and is re-run
without the cache, so such a run never spawns a judge and never writes; the
verdict, lemma and chain types are settled; `Guard_Simp_SS` is applied at
exactly four consumers; the "control-flow classifier" and everything built
on it is deleted (its premise was false); persisted terms use a functorised
MessagePack term codec.  This document states the FINAL design only.
History lives in `GUARD_CACHE_QUICK_MODE_PLAN.rev7-full.md`; consult it for
history, never for the design.  Every behavioral decision carries its
provenance: [author YYYY-MM-DD HH:MM "quote"] is the author's own ruling
(transcript timestamp, UTC), [drafter] is a drafting decision the author may
veto.  §10 lists every [drafter] decision that changes behavior, so none is
hidden.

Predecessor: `GUARD_NITPICK_FALSIFY_PLAN.md` (the guard race this plan
dismantles).  Line anchors into `reasoners.ML` are as of 2026-09-03 and are
re-verified at implementation start (§10.0).  No code has been written.

Submitted for an eighth review, scoped to §4 (end-of-run steps), §5, §6
and §8 — the places every substantive change lands.

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
  (`can_inst`, the guard-side ctxt, the outer ctxt, the thm).  [descriptive]
- **`guard_condition_solver`**: from now on a FACTORY — the existing
  preprocessing template (`oblg_template`, the `is_F` shortcut, case split,
  `apply_tac`'s fact insertion, the "G.simpcut" simp pass) parameterised by
  the solving tactic it ends with.  The parameter has `prove_or_refute`'s
  type above and is applied at the template's solving position (today
  `prove_or_refute can_inst ctxt ctxt0`, `reasoners.ML:1807`) [type:
  drafter, seventh review U3].  Three instances (§3): **`guard_condition_judge`**
  = the factory applied to `prove_or_refute`, used by the in-run
  `\<condition>` reasoners; the existing **`guard_condition_solver'`** /
  **`guard_condition_solver1`** = the factory applied to
  `try_prove_or_give_up` over P-auto, used by the out-of-run callers; and
  the factory applied to `try_prove_or_give_up` over `fastforce` for
  `defer_premise`'s solve-now case.  The two degenerate instances ignore
  `can_inst` and the outer ctxt at the instance site.  [author 2026-09-03
  09:44 "把原有的 guard_condition_solver 改成一个 factory 允许去选用不同的
  prove_or_refute"; third instance 11:11]
- **`try_prove_or_give_up`**: `Time.time option -> (Proof.context -> tactic)
  -> Proof.context -> thm -> thm Seq.seq` — run the tactic once, under the
  bound if one is given, keep only a solved state; otherwise `Seq.empty`.
  No table, no judge, no chain.  Out of a run: `SOME \<phi>guard_prove_timeout`
  over P-auto [author 2026-09-03 09:44]; for obligations: `fastforce` in a
  `Guard_Simp_SS`-enhanced ctxt, **no bound by default** [author 2026-09-03
  11:15 "限时是可选的, 也可以不限时"; 12:53 "义务实例 fastforce 默认无超时"].
- **verdict**: the value stored for one guard —
  `Proved of Phi_Proof_Store.proof_cache | Refuted of {refuter : string}`,
  where `Phi_Proof_Store.proof_cache = Time.time * string`
  (`cache_file.ML:149`: standard-machine time, method text) [author
  2026-09-02 12:03; `Proved of Phi_Proof_Store.proof_cache` 2026-09-03 11:00;
  no alias for it: seventh review U17].  The method text is what
  `eval_prf_str` replays; a guard proved by P-auto stores
  `\<phi>guard_P_auto` and is short-circuited on replay.  `Refuted
  {refuter}` names the hook: `"R-conv"`, `"R-nitpick"`, or `"default"`
  [author 2026-09-03 04:58].
- **refutable**: the RUN-TIME answer of a `prove_or_refute` call, "treat
  this guard as not holding" — it returns `Seq.empty` and the engine
  backtracks.  Not a stored value.  The chain's `Refutable name` (§6) is
  the same answer with the hook's signature; the stored `Refuted {refuter}`
  is its record.  No evidence travels with it [author 2026-09-03 10:59].
  [author 2026-09-02 08:54 "warn the user 然后返回 refutable"]
- **P-auto**: `timed_tac \<phi>guard_prove_timeout (solved_states
  p_auto_search_tac)` — the one proof attempt a `prove_or_refute` call
  makes, alone, no gate [author 2026-09-02 07:11; 400 ms provisional
  08:49; reconfirmed 2026-09-03 05:20].  Exposed as the proof method
  **`\<phi>guard_P_auto`** (one `method_setup` in `PLPR.thy`), whose body
  enhances its ctxt with `Guard_Simp_SS` [author 2026-09-03 10:59, 11:11
  "批准"; 13:26].
- **`Guard_Simp_SS`**, attribute **`\<phi>guard_simp`**: the simpset that
  strengthens guard proving — an instance of the repository's `Simpset`
  functor (`library/tools/simpset.ML`), like `Nitpick_Refute_SS`
  [author 2026-09-03 11:15].  Applied PRECISELY, by an `enhance` inside each
  consumer and nowhere else [author 2026-09-03 13:26 "我希望这个 simpset 的
  应用要精准"; 13:27 "赞同"]:
  | consumer | `Guard_Simp_SS` |
  |---|---|
  | the template's "G.simpcut" preprocessing pass (`reasoners.ML:1802-1803`) | yes |
  | `\<phi>guard_P_auto` (so also the P-auto replay of a hit) | yes |
  | R-conv's hook body | yes |
  | the obligation instance's `fastforce` | yes |
  | `eval_prf_str` replay of a stored script (phase 2) | yes [drafter: the judge verified the script with these lemmas in the simpset, so its replay sees the same simpset — listed in §10] |
  | R-nitpick (it stacks only `Nitpick_Refute_SS`) | no |
  | the ctxt built at `reasoners.ML:1829` and handed to `prove_or_refute`, `judge_arg.ctxt`, `outer_ctxt` | no |
  `Nitpick_Refute_SS` is today's `Guard_Refute_SS` (attribute
  `\<phi>guard_refute_simp`), renamed [author 2026-09-03 11:15]: R-nitpick's
  preprocessing simpset.
- **There are no modes** [author 2026-09-02 07:39; 2026-09-03 05:48].
- **the chain**: `structure PLPR_Guard_Refuters = Handlers (type arg =
  judge_arg  type ret = chain_verdict)` — the repository's `Handlers`
  functor (`Hook.ML:116`) used DIRECTLY: `PLPR_Guard_Refuters.add priority
  hook` registers, `PLPR_Guard_Refuters.invoke` runs hooks by ascending
  priority until one answers `SOME` [author 2026-09-02 08:54 "在框架上就直接
  使用带有优先级的 Hooks 机制实现"; 2026-09-03 12:37 "你直接用 the Hooks
  functor 不行吗"; 12:39 "直接 structure PLPR_Guard_Refuters = Handlers ..."].
  No wrapper, no `add_refuter`, no `run_chain`, no `bound` field.  Its
  lowest-priority member is the **default refuter**, an ordinary hook that
  warns and answers `Refutable "default"` [author 2026-09-02 08:54;
  2026-09-03 04:42].
- **hooks are first-class**: a hook decides its own timeout inside its own
  body and catches its own `TIMEOUT` if it wants to answer `NONE`; ANY
  exception that escapes a hook — an uncaught `TIMEOUT`, an error, an
  interrupt of any origin — escapes the judge and crashes the run (§6)
  [author 2026-09-03 12:23 "一个 racer 异常退出的话, gen_reason' 就是应该走
  异常路径"; 12:31 "hook 也是整个 PLPR 的重要一部分, hook 的崩溃应该视作 PLPR
  推理链的崩溃"; 12:36 "hook 是一等公民啊, 你应该信任 hook 啊"].
- **judge**: one `Future` task per `prove_or_refute` call that answered
  refutable, in a run WITHOUT a record; its body is exactly
  `PLPR_Guard_Refuters.invoke (Context.Proof ctxt) arg` [author 2026-09-02
  09:13 / 09:29].  Judges never write the env; the topmost `gen_reason'`
  invocation copies their answers in at the end of the run.  A run WITH a
  record never spawns one (§5).
- **judge crash**: a judge's `Future` result is `Exn.Exn exn` with `exn`
  not an interrupt.  The run ends with `error (header ^ "\n" ^
  Runtime.exn_message exn)` — the header names the call index and the
  guard, the original message is kept verbatim — nothing written, no
  tombstone [author 2026-09-03 12:31 "赞同乙"; 12:33 "原始的异常信息必须被
  抛出! 你可以在异常前加一点 header"; 12:35 "以 ERROR 形式抛出 header + \"\\n\"
  + the message of exn"].  An interrupt result is re-raised as the
  interrupt it is.
- **env**: the record (§4) holding one run's table, judges and
  bookkeeping, in a `Proof_Data` slot of type `env option
  Unsynchronized.ref option`: outer `NONE` = this ctxt was never given a
  cell; the cell's `SOME env` = the run is open, `NONE` = it has ended
  [author 2026-09-03 08:08 / 08:11].  "No record" is `previous_final = NONE`
  [author 2026-09-03 16:00 "原本的 type env 就已经足够了, 不需要再变了";
  16:34 "确认"].
- **the run**: everything between one `gen_reason'` invocation installing
  an env and that same invocation finishing.  The invocation that installs
  the env is **the topmost `gen_reason'` invocation** [author 2026-09-02
  15:45]; nested invocations inherit.  What the topmost invocation does
  when the run ends (§4) is **the end-of-run steps**.  The run's thread is
  the only writer of the env's refs.
- **run failure**: the topmost `gen_reason'` invocation returning `NONE`,
  or ending with a non-interrupt exception (`Interrupt_Family.contains_interrupt`
  false, the test at `reasoners.ML:1635`) [author 2026-09-03 07:35].  A
  nested `\<r>BEGIN` reasoning whose nested run returns `NONE` raises an
  ERROR (`nested.ML:33`); `gen_reason`'s step limit raises too
  (`reasoner.ML:794-799`).  Verdicts are answers, never successes or
  failures.
- **`Guard_Record_Stale`**: the exception a run WITH a record raises the
  first time the record fails to reproduce — at a `prove_or_refute` call:
  slot absent, stored digest different, or a `Proved` hit whose replay
  fails; at installation: a run lemma that fails to certify or replay.  It
  passes through every
  nested `gen_reason'` (they catch only `Success`, `Global_Cut`,
  `Explorative_Backtrack`, `reasoner.ML:802-809`, `:917`) to the topmost
  invocation, which tombstones the record and re-runs without the cache
  (§4) [author 2026-09-03 15:01 "但凡一次缓存 miss 就直接 raise a specific
  exception 让 gen_reason' 去清除缓存然后重跑"; 16:01 "采纳这条规则 …
  命中 Proved 但重放失败算 miss"].  Name: drafter, under the 11:24
  delegation.
- **call index**: the position of a `prove_or_refute` call within its run,
  0, 1, 2, …, from the env's counter [author 2026-09-02 07:11 "key 是
  guard_counter"; 2026-09-03 07:59].
- **guard digest**: the `Hasher` digest (`Word64.word`) of the guard's own
  subgoals — `Thm.cprems_of th` as `prove_or_refute` receives them, each
  with its parameters and premises; not the ctxt's assumptions, not the
  theory name [author 2026-09-03 07:48].  Computed by a new `Hasher.terms :
  term list -> digest` (fold of `hash_term`).  `Word64` everywhere in memory
  [author 2026-09-03 07:58].
- **table**, **slot**: the run's `(digest * verdict) Inttab.table` keyed by
  call index [author 2026-09-02 07:11; 2026-09-03 02:18].  A **hit** is
  slot `i` present with the stored digest equal to this call's guard
  digest; anything else is a **miss**; a **replay** is re-running the
  method text a `Proved` slot recorded.
- **record**, **record key**: the one proof-store item holding a whole
  run's `{final, lemmas, entries}` (§8).  Key: `"PLPRGUARD" ^
  Hasher.compact (Hasher.goal (ctxt, initial))` of the run's first pulled
  initial state — the whole initial sequent, salted with the ctxt's
  assumptions and the theory short name inside `Hasher.goal`
  (`Hasher.ML:230-246`) [author 2026-09-03 02:18; 08:33; 08:44 "采用
  PLPRGUARD"; `Hasher.goal` is the exported name: seventh review U8].
  `Hasher.compact` is the 8-byte raw rendering (`Hasher.ML:76`); it never
  appears in a log line.  Stability caveat: `Hasher.goal` is the formula
  `cache_file.ML:891-895` calls not invariant under fork/promise discharge;
  a moved record key costs a total miss for that run (one
  `Guard_Record_Stale` at call 0, one re-run) plus one extra record, never
  a wrong verdict.
- **final digest**: `Hasher.goal (ctxt', th')` of the run's resulting state
  [author 2026-09-02 07:11].  Same caveat; a final digest that moves once
  costs one R3 re-run, one that is not reproducible at all costs one on
  EVERY run — §10 step (5)'s gate measures this before persistence lands.
- **tombstone**: the proof store's own per-key deletion (`TOMB`,
  `encode_tombstone`, `cache_file.ML:66`, `:93`), written by the guard
  store's `invalidate_proof_cache` with `warn = false` [author 2026-09-03
  13:19 "C6 采纳"].
- **no-cache re-run**: re-entering the reasoning body on the ORIGINAL
  `states` argument of the topmost invocation with a fresh env whose
  `previous_final = NONE`, `entries = Inttab.empty`, `lemmas = []` [author
  2026-09-03 14:56 "R2/R3 重跑时 run lemma 也清空: 赞同"].
- **run lemmas**: `(term * Phi_Proof_Store.proof_cache) list` — (statement,
  (replay time, method text)) triples that strengthen `Guard_Simp_SS` for
  one run.  They live in the record and the env; at installation each is
  re-proved by replaying its method text under `tolerant_time` of its
  recorded time, in the ctxt `gen_reason'` was given — its own simpset,
  without `\<phi>guard_simp` and without the other run lemmas — and the
  thms are added to `Guard_Simp_SS` [author 2026-09-02 07:39; 2026-09-03
  10:53; 12:54 "lemmas 所携带的证明也是需要给重放时间的, 所以类型也是
  Phi_Proof_Store.proof_cache. 是 judge 要返回重放时间的"; 13:27 "是当时
  gen_reason' 的 ctxt 中的 simpset, 即, 没有任何改动. 也不看
  \<phi>guard_simp"].  Phase 1 has no producer; phase 2's LLM judge
  produces them.  A run lemma whose certification (`Thm.cterm_of` raises)
  or replay fails at installation is the record failing to reproduce: the
  run raises `Guard_Record_Stale` — tombstone, no-cache re-run [author
  2026-09-03 16:55 "(a) 赞同. 要清除 cache 重跑的"].
- **R1–R4**: the four rules of §7.

Retired names — never used below: "owner" = the topmost `gen_reason'`
invocation; "scope" = the run; "determination" = a `prove_or_refute` call;
"the proving stage" = P-auto; "store key" / `cache_key` = record key;
"exit protocol" = the end-of-run steps; "defensive rule" / "no-env case" =
the out-of-run entry points; "blob" = the record value; "async judge" =
judge; "Guard_Fails" = refutable; "quick mode" = (no modes); "aux" = the
fields of `Provable`; "evidence" = (deleted); "`NONE` = P-auto" =
`\<phi>guard_P_auto`; "Actually_Provable" = `Provable`; "Chain_Ran" /
"Chain_Answered" / `judge_outcome` / `Judge_Aborted` = (deleted: a judge's
Future carries `chain_verdict option` and exceptions escape); "the
auxiliary-lemma slot" = `Guard_Simp_SS`; "Guard_Refute_SS" =
`Nitpick_Refute_SS`; "not landed" = replay failed; `add_refuter` /
`run_chain` / `PLPR_Refuters` / `bound` = (deleted); "the control-flow
classifier" / `is_control_flow` = (deleted); "type proof" = written out as
`Phi_Proof_Store.proof_cache`.

## 2. Motivation

~88 % of the corpus's `prove_or_refute` calls end with the guard not
holding (median refuted 607 ms, undecided 2367 ms), and that answer is
behaviourally identical to assuming the guard false; refutation evidence
cannot be validated item by item.  So: answer refutable immediately,
gather evidence off the critical path (judges), record every verdict, and
validate end to end per run (§7).  Soundness is untouched: verdicts only
select which rules PLPR tries; a wrong refutable answer yields a different
but valid derivation, never a wrong theorem.  Guards are load-bearing for
phi-system — an over-refuted guard fails the whole reasoning — so the
judges are the mechanism that corrects over-refutation (phase 2's LLM
judge answers `Provable`), and a judge's failure is the run's failure, not
a lost vote [author 2026-09-03 12:27 "必须有 judge 能在 guard condition 被
过度 refuted 的时候出来纠正"].

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
            slot i = (d, Refuted {refuter}) → refutable (warn again if "default")
            slot i = (d, Proved (t, script))→ replay script under its bound;
                                             replay failed → raise Guard_Record_Stale
            slot i absent or digest ≠ d    → raise Guard_Record_Stale
          WITHOUT A RECORD (previous_final = NONE):
            P-auto: proves → slot i := Proved (elapsed, "\<phi>guard_P_auto")
                    else   → spawn judge i, answer refutable
    end-of-run steps (topmost invocation only):
      close (cell := NONE) → classify the run's outcome (§4):
        Guard_Record_Stale, or R2/R3      → tombstone; no-cache re-run; adopt
        failure without a record          → join ALL judges (warnings print); classify
                                             judge results; nothing written; propagate
        success without a record          → join ALL judges → judge crash? → error
                                             → merge → persist if the table is non-empty
        success with a record             → final digest = previous_final? else R3

OUT OF A RUN   (guard_condition_solver' / guard_condition_solver1: four
                command-level callers in Phi_System — local_value.ML:168,
                toplevel0.ML:364, generic_variable_access2.ML:181, :264;
                application.ML:133 is commented out — solving proof
                obligations, `Premise default P` / `Premise MODE_COLLECT P`)
  guard_condition_solver (fn _ => fn ctxt => fn _ =>
      try_prove_or_give_up (SOME \<phi>guard_prove_timeout) p_auto_search_tac ctxt):
    same preprocessing, then P-auto once; not proved → Seq.empty → the
    caller's error continuation.  A deliberate narrowing: today these sites
    also get a 35 ms auto_search_tac gate (reasoners.ML:1602) and a 2000 ms
    P-auto budget (:1618, :1701); all four sites raise `error` on failure,
    so §10 step (6) surfaces any regression as a build failure.

OBLIGATIONS SOLVED ON THE SPOT   (defer_premise, PLPR.thy:1974/1975, when
                Phi_Reasoner_solve_obligation_and_no_defer is 1 or 2 — set
                by the user's prove_obligations_in_time and internally by
                SE_Trim_Empty.ML:54, :114, rule_generation.ML:443)
  guard_condition_solver (fn _ => fn ctxt => fn _ =>
      try_prove_or_give_up NONE fastforce (Guard_Simp_SS.enhance ctxt)):
    same preprocessing, then fastforce, unbounded by default; not proved →
    Seq.empty → backtrack.  No table, no judge, no chain, no warning.

judge (Future, one per refutable answer in a run without a record):
  PLPR_Guard_Refuters.invoke, ascending priority
    100      R-conv     (own bound: \<phi>guard_rconv_timeout, 300 ms)
    200      R-nitpick  (own bound: \<phi>guard_refute_timeout + 5000 ms × n_goals)
    1000     (reserved: LLM judge, phase 2)
    1000000  default    (no bound; warn; Refutable "default")
```

Removed: the `Race.race` call, the three racer wrappers, the in-race
`protocol` var, `\<phi>guard_race_timeout`, the 35 ms gate.  Reused:
`Hasher`, the proof store (as a functor instance, §8), `eval_prf_str`,
`Phi_Reasoners.wrap` (registrations unchanged [author 2026-09-02 12:08
"保留 Phi_Reasoners.wrap — 赞同"]), `Handlers`, `Simpset`, the
R-conv/R-nitpick bodies (screens verbatim), `RPC_Pretty`'s raw term codec
(functorised, §8).

Every caller of the old `guard_condition_solver` must migrate, and the
factory's changed type makes a missed one a compile error.  Known callers
(2026-09-03): `PLPR.thy:1983`, `:1986` → `guard_condition_judge`;
`PLPR.thy:1974`, `:1975` (`defer_premise`) → the `fastforce` instance
[author 2026-09-03 11:15 "(b) 赞同"]; `Test/Guard_Race_Smoke.thy:79` →
migrated at §10 step (2).

## 4. The env

```
type env =
  {record_key     : string,
   previous_final : Hasher.digest option,            (* NONE = no record *)
   lemmas         : (term * Phi_Proof_Store.proof_cache) list Unsynchronized.ref,
   counter        : int Unsynchronized.ref,
   entries        : (Hasher.digest * verdict) Inttab.table Unsynchronized.ref,
   judges         : (int * Hasher.digest * chain_verdict option future) list Unsynchronized.ref,
   judge_group    : Future.group}
```

[author 2026-09-03 16:00 "那原本的 type env 就已经足够了, 不需要再变了啊";
16:34 "对的. 确认".  Plain refs, no `Synchronized`, no `Lazy`; the four refs
are written by the run's thread only.]  In a run with a record `entries`
and `lemmas` are never written (§5): they hold the record as read.  In a
run without a record they start empty and are built in place.

- **Installation**: `gen_reason'` reads the slot of the FIRST PULLED
  initial state's ctxt (`reasoner.ML:813`).  No cell, or a cell holding
  `NONE` → create the env in a fresh cell; a cell holding `SOME env` →
  inherit.  `gen_reason'` allocates one decision ref per invocation and
  maps `apfst install` lazily over the initial states; `install` consults
  that ref — undecided (the first pulled state) → perform the slot check on
  THIS state's ctxt and record the outcome; already decided → put the
  recorded cell.  One invocation mints at most one env [drafter, seventh
  review U22; today every live caller passes a single-element sequence].
  ONLY `gen_reason'` installs [author 2026-09-02 15:45; 14:54].  At
  installation: `record_key`; the record is read (§8) — `previous_final :=
  SOME final`, `entries := its table`, `lemmas := its lemmas` — or, with no
  record, an undecodable one, or `\<phi>guard_cache = false`,
  `previous_final := NONE`, `entries := Inttab.empty`, `lemmas := []`;
  eagerly [author 2026-09-03 05:38].  Each run lemma is then re-proved:
  `Thm.cterm_of` on its statement, `eval_prf_str` of its method text under
  `tolerant_time` of its recorded time, in `gen_reason'`'s own ctxt
  (§1 run lemmas); the thms go into `Guard_Simp_SS` via `add_simps'`; a
  lemma that fails to certify or replay raises `Guard_Record_Stale` (§4
  step 2) [author 2026-09-03 16:55].
  `counter := 0`; `judge_group := Future.new_group (SOME (Task_Queue.group_of_task
  task))` for the current worker task, or `Future.new_group NONE` off a
  worker thread — the difference only decides whether an ancestor's
  cancellation reaches the judges; a judge that absorbs an interrupt
  cancels `judge_group` itself either way (`assign_result`,
  `future.ML:430-435`).
- **Judges see no env**: the two contexts handed to a judge are built with
  the slot emptied — `Env_Slot.put NONE ctxt`, `Env_Slot.put NONE outer_ctxt`,
  a functional `Proof_Data.put` of the OUTER `NONE`, never `cell := NONE`.
  A hook that reasons therefore becomes its own topmost invocation with its
  own env, record key and `judge_group`; the run's refs stay single-writer
  by construction [drafter, seventh review U4 — listed in §10].
- **Nesting**: a nested `gen_reason'` (`\<r>Call`, `\<r>BEGIN`,
  `ToR_Entry_Point` via `internal_reason`) inherits: one table, one
  counter, one judge list; no end-of-run steps.  Its `NONE` is ordinary
  backtracking for `\<r>Call` and `ToR_Entry_Point` (`nested.ML:42-45`);
  `\<r>BEGIN` converts it to an ERROR (`nested.ML:33`) that reaches the
  topmost invocation as an exception.  `Guard_Record_Stale` passes through
  all of them.  [author 2026-09-02 15:45, 16:02]
- **End-of-run steps** (topmost invocation only).  They wrap the RESULT of
  the topmost `gen_reason'` — outside its own `handle Success ret => SOME
  ret` (`reasoner.ML:917`), so PLPR's control-flow exceptions are
  structurally unreachable here [drafter, seventh review U20] — and run
  inside one `Thread_Attributes.uninterruptible_body (fn run => …)` whose
  `run` re-enables interrupts for the joins only, so that a raise out of a
  join cannot leave `judge_group` alive: `case Exn.capture_body (fn () => run
  Future.join_results futures) of Exn.Res rs => … | Exn.Exn exn =>
  (Future.cancel_group judge_group; ignore (Future.join_results futures);
  Exn.reraise exn)` (race.ML:266-279's shape) [drafter, seventh review U2].
  In order:
  1. `cell := NONE` [author 2026-09-03 08:08].
  2. **`Guard_Record_Stale` escaped** (only possible with a record; no
     judge exists): tombstone the record; no-cache re-run (§1) on the
     ORIGINAL `states`; adopt its result.  The re-run has no record, so it
     cannot raise `Guard_Record_Stale` and cannot fire R2/R3: it is always
     a leaf [author 2026-09-03 15:01, 16:01].
  3. **Run failure WITH a record** (no judge exists): `NONE` → R2 with
     re-run: tombstone, re-run, adopt.  Non-interrupt exception → R2
     without re-run: tombstone, re-raise [author 2026-09-03 07:35].
  4. **Run failure WITHOUT a record**: join ALL judges in full (the default
     refuter's warnings print — they are the diagnostic that explains the
     failure); classify the judge results as in step 6 (a crash or an
     interrupt among them takes precedence and ends the run that way);
     otherwise nothing is written, no tombstone (there is no record), the
     `NONE` is returned / the exception re-raised [seventh review U1: R2 is
     a rule about a record].
  5. **Interrupt** reaching this frame from the run body: `Future.cancel_group
     judge_group`, re-join (the cancelled judges exit promptly), re-raise;
     nothing written or deleted [author 2026-09-03 14:56 "被中断的 run 不写
     不删: 赞同"].
  6. **Success WITHOUT a record**: join ALL judges in full, no bound
     [author 2026-09-03 01:56].  Classify every judge's result:
     - `Exn.Exn exn`, `exn` an interrupt (`Interrupt_Family.contains_interrupt`)
       → the run was cancelled, whether from outside (an ancestor group, or
       the run's own thread absorbing the interrupt while executing a judge
       job during the join) or by a judge's own nested machinery
       (`race.ML:91-103`): re-raise the interrupt; nothing written [author
       2026-09-03 12:23].  No group probe is needed: `Task_Queue.cancel`
       gives every queued or running job of a cancelled group an interrupt
       result, so cancellation always shows up in the results.
     - `Exn.Exn exn`, not an interrupt → judge crash (§1): `error (header ^
       "\n" ^ Runtime.exn_message exn)`; nothing written, no tombstone.  If
       several judges crashed, the header lists all and the messages follow
       in call-index order.
     - `Exn.Res NONE` → a registry defect (no hook answered; the default
       refuter always does): error, as a crash.
     - `Exn.Res (SOME (Refutable name))` → `entries := Inttab.update (i, (d,
       Refuted {refuter = name}))`.
     - `Exn.Res (SOME (Provable {lemmas = new, proof}))` → `entries :=
       Inttab.update (i, (d, Proved proof))`, `lemmas := !lemmas @ new`
       (phase 2; the re-run that lets the engine use the new `Proved` is
       phase 2's loop).
     Then compute the final digest and persist `{final, lemmas = !lemmas,
     entries = !entries}` (§8) if `entries` is non-empty [author 2026-09-03
     08:04].
  7. **Success WITH a record** (no judge exists, `entries` unchanged):
     compute the final digest; `<> previous_final` → R3: tombstone,
     no-cache re-run, adopt.  Equal → the record is byte-identical to what
     is on disk; nothing is written [author 2026-09-03 16:55 "(b) 不写"].

## 5. One `prove_or_refute` call

Inside a run only.  `i := !counter; counter := i + 1`; `d := Hasher.terms
(map Thm.term_of (Thm.cprems_of th))` on the thm as received.  Then by
`previous_final`:

**With a record** (`SOME _`) — the run tolerates no miss [author 2026-09-03
15:01, 16:01]:

1. Slot `i` is `(d', Refuted {refuter})` with `d' = d` → answer refutable.
   Silent when the refuter is R-conv or R-nitpick (today's silent
   refutation, `reasoners.ML:1526`); when `"default"`, print the default's
   warning again [author 2026-09-03 04:46].  Never re-judged [author
   2026-09-02 10:40].
2. Slot `i` is `(d', Proved (t, script))` with `d' = d` → replay.  `script
   = "\<phi>guard_P_auto"` → run the method's tactic directly (no
   `Method.parser`) under `Time.max (tolerant_time t) \<phi>guard_prove_timeout`,
   `tolerant_time t = 1.5t + 1 s` (`cache_file.ML:869-870`) [floor: author
   2026-09-02 13:01 "好"; summand and `tolerant_time`: 2026-09-03 02:10,
   reconfirmed 13:03 "B4 没问题"].  Any other `script` → `eval_prf_str`
   under `tolerant_time t`, `n = Thm.nprems_of th`, keywords
   `Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)`, in a
   `Guard_Simp_SS`-enhanced ctxt; the returned ctxt' is discarded.  Replay
   succeeded → return the solved states.  Replay failed (timeout, or the
   goal not closed) → raise `Guard_Record_Stale` [author 2026-09-03 15:46
   "命中 Proved 但重放失败算 miss … 我们已经 x1.5 + 1s 了已经很大的宽限了"].
3. Slot `i` absent, or `d' <> d` → raise `Guard_Record_Stale`.

**Without a record** (`NONE`):

4. Run P-auto (`\<phi>guard_P_auto`'s tactic, which enhances
   `Guard_Simp_SS`).  Proves → `entries := Inttab.update (i, (d, Proved
   (elapsed of the whole `timed_tac` call through `standard_time`,
   "\<phi>guard_P_auto")))` [author 2026-09-03 12:52 "2. 批准"].  Does not
   prove → fork judge `i` (§6), `judges := (i, d, future) :: !judges`,
   answer refutable.

Two calls in one run that meet the same guard occupy two slots and, without
a record, get two judges: the slot, not the guard, is the identity [author
2026-09-03 07:54].

## 6. Hooks and judges

```
type judge_arg = {ctxt : Proof.context,        (* the guard-side ctxt, env slot emptied *)
                  outer_ctxt : Proof.context,  (* guard_condition_solver's ctxt0, env slot emptied;
                                                  R-conv's export direction, reasoners.ML:1303-1312 *)
                  can_inst : bool,
                  goals : cterm list}          (* Thm.cprems_of th *)
datatype chain_verdict =
    Provable of {lemmas : (term * Phi_Proof_Store.proof_cache) list,
                 proof : Phi_Proof_Store.proof_cache}
  | Refutable of string
structure PLPR_Guard_Refuters = Handlers (type arg = judge_arg  type ret = chain_verdict)
```

[`judge_arg` without `assms`: author 2026-09-03 14:53 "赞同 C12" — R-nitpick
screens `Assumption.all_assms_of ctxt` inside its own body as today
(`reasoners.ML:1656-1670`); `Provable` fields: 10:59, 11:01, 12:54.]
`Provable` is a VERIFIED answer: the hook replayed each lemma's method text
and the guard's `proof` on the judge's thread and measured the times.  Phase
1 has no hook that answers `Provable`.

**Hooks**, registered with `PLPR_Guard_Refuters.add`; each bounds itself:

| priority | hook | its own bound |
|---|---|---|
| 100 | R-conv | `Timeout.apply \<phi>guard_rconv_timeout` (300 ms) around its search, in a `Guard_Simp_SS`-enhanced ctxt; catches its own `TIMEOUT` → `NONE` [author 2026-09-02 10:37 "R-conv 预算默认 300ms"] |
| 200 | R-nitpick | one `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms × length goals` (2000 ms + 5 s per subgoal) around the whole body; inside it the subgoals are tried one after another, each Nitpick call carrying its own 2000 ms parameter as today (`reasoners.ML:1656-1675`); any subgoal refuted → `SOME (Refutable "R-nitpick")`; catches its own `TIMEOUT` → `NONE` [author 2026-09-03 13:05 "C1 超时应该是 2000ms + 5000ms * the number of the goals"; sequential order inside: drafter] |
| 1000 | (reserved: LLM judge, phase 2) | its own |
| 1000000 | **default refuter** | none — prints today's warning (`reasoners.ML:1605-1616`), answers `SOME (Refutable "default")` [author 2026-09-02 08:54] |

Priorities [author 2026-09-02 08:58].  A hook that lets ANY exception
escape — an uncaught `TIMEOUT`, an error, an interrupt — has crashed (§1).

**Judge body and fork.**  `fn () => PLPR_Guard_Refuters.invoke (Context.Proof
(#ctxt arg)) arg` — nothing around it [author 2026-09-03 12:37, 12:39].
Forked as `Future.forks {name = "PLPR.guard_judge", group = SOME
judge_group, deps = [], pri = p, interrupts = true}` where `p` is the
forking task's own priority (`Task_Queue.pri_of_task` of
`Future.worker_task ()`, 0 off a worker), so the end-of-run join does not
drain a fleet of lowest-priority tasks serially on the run's own thread
(`task_queue.ML:167-168`) [author 2026-09-03 13:19 "C5 采纳"].
`interrupts = true` is what makes the hooks' own `Timeout.apply` calls
live (`Timeout.apply'` captures the attributes at its call site,
`timeout.ML:33-47`).  An exception escaping the body is stored as the
future's result and cancels `judge_group` (`assign_result`,
`future.ML:430-435`); the end-of-run steps read the results (§4 step 6).

**Warning** is the default refuter's own body, printed at the end of the
chain on the judge's thread [author 2026-09-03 04:14]; `future_job`
restores the forking thread's Position data (`future.ML:441-452`), so it
lands on the right command.

## 7. Rules

Stated of one run (§1).

- **R1 recording** [author 2026-09-02 12:03]: in a run without a record,
  every completed `prove_or_refute` call ends with its slot filled —
  `Proved` by the call itself when P-auto proves, otherwise by the topmost
  invocation at the merge from the judge's answer.  At the end of such a
  run whose table is non-empty, the topmost invocation writes the WHOLE
  table as the record (never a delta — the store is last-write-wins)
  [author 2026-09-02 07:11; empty table exempt 2026-09-03 08:04].  A failed
  run records nothing [author 2026-09-02 11:40]; an interrupted run writes
  and deletes nothing [2026-09-03 14:56]; a run with a record never writes
  (§5: its table is unchanged, and an unchanged record is not rewritten
  [author 2026-09-03 16:55 "(b) 不写"]).
- **R2 run failure against a record** [author 2026-09-02 11:48, 11:54;
  widened 2026-09-03 07:35; first-miss 15:01/16:01]: a run with a record is
  stale, and the record is tombstoned, when it (a) returns `NONE` → one
  no-cache re-run; (b) ends with a non-interrupt exception → no re-run, the
  exception is re-raised; (c) raises `Guard_Record_Stale` on a miss or a
  failed replay → one no-cache re-run.  The re-run records under R1.
- **R3 validation** [author 2026-09-02 07:11]: a run with a record that
  succeeds compares its final digest with `previous_final`; mismatch →
  tombstone, one no-cache re-run, recorded under R1.
- **R4 faithful hits** [author 2026-09-02 10:40]: a hit is never re-judged.

Recorded honestly, with no rule answering it:

- Staleness that leaves the final outcome unchanged (a `Refuted` whose
  countermodel rests on a changed definition; a `"default"` slot for a guard
  a new simp lemma would now prove — it warns on every hit; an R-nitpick
  model the pipeline cannot certify genuine) is reproduced faithfully
  forever.
- A cold run under load can turn a guard that once proved inside the
  P-auto budget into a permanent `Refuted {"default"}`; R3 structurally
  cannot fire on it.
- An edit that gains or loses one `prove_or_refute` call early shifts every
  later call index: the run raises `Guard_Record_Stale` at the first
  shifted slot whose digest differs, and is re-run without the cache.  A
  shifted slot that happens to hold the SAME guard is a hit and delivers
  the verdict another call site earned — nothing unsound follows (a
  `Proved` hit is re-proved by replay, a `Refuted` hit only prunes), and if
  the outcome changes R3 re-runs.  One re-run's cost, not a permanent one.
- Two runs in one theory whose first pulled initial states agree in
  sequent and assumptions share a record key and clobber each other's
  record.  §10's gate before step (5) measures whether record keys repeat
  across corpus runs at all.
- A stale slot can steer a run down a branch that raises where the
  cache-free run would have succeeded (the step limit, `reasoner.ML:793-799`;
  a nested `\<r>BEGIN` failure, `nested.ML:33`).  R2 (b) tombstones and
  re-raises without a re-run, so that build fails once and succeeds on the
  next invocation; `\<phi>guard_cache = false` is the escape hatch.
- A merged `Provable` (phase 2 only) writes a `Proved` into a record whose
  `final` came from the derivation that treated the same guard as
  refutable; the next run's replay moves the final digest, R3 fires, and
  the re-run — empty table, no run lemmas — reproduces the same record.
  Until phase 2's re-run loop lands, every merged `Provable` costs one R3
  re-run per run and is never consumed.
- The obligation instance's `fastforce` is unbounded by default, as is the
  template's own "G.simpcut" pass on that path today [author 2026-09-03
  12:53].
- There is NO user-facing invalidation feature [author 2026-09-03 04:55];
  the file is regenerable and deleting it is the reset.

## 8. Persistence

- **Store functor** [within §11.10's delegation; shape: seventh review U6].
  `cache_file.ML`'s store body becomes a functor over `{ext, migrates,
  marks_writes, describe, switch}`; `Phi_Proof_Store` is instantiated with
  `{ext = "proof-store", migrates = true, marks_writes = true, describe =
  ("Proof cache", "cached proofs"), switch = <the existing
  enable_proof_store binding>}` — unchanged name, signature and callers —
  and **`Phi_Guard_Store`** with `{ext = "guard-cache", migrates = false,
  marks_writes = false, describe = ("Guard cache", "cached guard
  verdicts"), switch = \<phi>guard_cache}`.  Every module-level piece of
  state (`append_locks`, `warned_dirs`, `openning_stores`, the
  `Theory.at_end` compaction) is per instance, so the two stores cannot see
  each other's state; the guard instance is ascribed a narrower signature
  without the by-hash surface; the honest cost is one unused by-hash index
  compiled per instance.  The config switch is a functor ARGUMENT because
  `Attrib.setup_config_bool` at `cache_file.ML:227` cannot declare one
  binding twice.  Per-kind behavior: `migrates = false` → no legacy
  `.proof-cache` fallback, an absent file is an empty table; `marks_writes
  = false` → no `written`/`proof_mark` collision alarm (a guard record is
  legitimately rewritten every run); `describe` feeds `warn_not_writable`
  ("Guard cache for theory … is not writable (…); cached guard verdicts
  will be read but not recorded." [author 2026-09-03 11:22 "批准"]) and
  `report_cache_is_outdated`.  The guard instance's `at_end` compacts only
  if the file exists, and closes unconditionally (`get_store` has already
  created the `openning_stores` entry) [drafter, seventh review U14].  The
  dead `bool` in `openning_stores`'s value triple (six writers, no readers,
  `:627`) is dropped in the same pass [seventh review U16].
- **Three entry points of `Phi_Guard_Store`**, no new ones [author
  2026-09-03 13:19 "C7 好"]: read = `get_cached_proof thy record_key :
  proof_cache option`, the record value being its string half; write =
  `update_cached_proof thy {id = record_key, hash = NONE} (Time.zeroTime,
  value)` (the time half is unused for this kind); tombstone =
  `invalidate_proof_cache false record_key thy` (`:731-741`: in-memory
  `store_invalidate_proof`, then `append_record` of `encode_tombstone`)
  [author 2026-09-03 13:19 "C6 采纳"].  The store's locking (`store_append_lock`,
  `with_file_lock`, lock order v → fcntl → `openning_stores`, `:486`) is
  inherited unchanged.
- Guard records live in `<thy>.guard-cache`, GITIGNORED [author 2026-09-02
  13:01]: `*.guard-cache`, `*.guard-cache.lock`, `*.guard-cache.tmp*`
  (compaction's temp file, `write_state_new`, `:319-328`) in
  `contrib/phi-system/.gitignore` beside `*.proof-store.lock` [author
  2026-09-03 14:57 "好的"].
- **Record value**: `{final : digest, lemmas : (term *
  Phi_Proof_Store.proof_cache) list, entries : (int * digest * verdict)
  list}` packed with the mlmsgpack packers through a `BytesIO` outstream
  and taken as a string (`BytesIO.mkOutstream` → pack → `BytesIO.toString`,
  `encode_record`'s shape, `cache_file.ML:76-82`) [author 2026-09-03 05:42].
  Digests through `packWord64` / `unpackWord64` [author 2026-09-03 07:58];
  `verdict` tagged by an int like `PUT`/`TOMB` [author 2026-09-03 13:19 "C8"];
  a lemma's `term` through **`RPC_Pretty.pack_raw_term` /
  `unpack_raw_term`** (`Isabelle_RPC/Tools/pretty.ML:323-357`, the
  constructor-tagged structural codec) made available on `BytesIO` by
  turning that codec into a functor over the `MessagePack` result
  signature (`mlmsgpack.sml:1` — its anonymous result signature gets a
  name, one line) and instantiating it twice; the `MessagePackBinIO`
  instance keeps `RPC_Pretty`'s existing names.  The functor stays in
  `Isabelle_RPC` for now and moves to `Performant_Isabelle_ML` after this
  plan [author 2026-09-03 13:19 "如果是 a functor 就好了"; 13:27 "赞同";
  14:19 "C8 先放在方便的地方, 但这个计划之后我们会移动到
  Performant_Isabelle_ML. 请记一笔"].  NO format version [author 2026-09-03
  03:02]: the decode is wrapped `\<^try>\<open>SOME (decode v) catch _ =>
  NONE\<close>` — catch-ALL, because a truncated payload raises `Subscript`
  out of `BytesIO.inputN` (`mlmsgpack.sml:917-923`); `\<^try>` re-raises
  interrupts.  Any exception means "there is no record".
- Written at most once per run, at the end of a run without a record, after
  the merge, only when the table is non-empty.
- `\<phi>guard_cache` (default true) is the one debugging switch [author
  2026-09-02 10:41]; off = the record is neither read nor written, the run
  behaves as one without a record, judges as usual [author 2026-09-03 12:52
  "1. 批准"].  There is no judge switch [author 2026-09-03 05:47].

## 9. Phase 2 (deferred) and phase-1 enablers

Phase 1 lands: the `eval_prf_str` tracing line behind a verbosity gate
[author 2026-09-02 10:29 "不需要 eval_prf_str 里一行无条件的 tracing"];
`Guard_Simp_SS` with its attribute and its four consumers (§1); the
`Nitpick_Refute_SS` rename.  Nothing else outside PLPR is touched: the
"control-flow classifier", the re-raise clauses in
`Phi_Sledgehammer_Solver.normalise` / `eval_prf_str0` and the
`reason_record` redefinition are DELETED — their premise (a PLPR reasoning
running inside those functions) is impossible, PLPR is self-contained and
`Success` never escapes `gen_reason'` [author 2026-09-03 12:59 "不可能的!
PLPR 是 self-contained"; 13:01 "请删除 is_control_flow 这种傻逼玩意儿";
"B2 完全消失了是吗? — 是"].  The LLM judge, its re-run loop and the
consumer of a merged `Provable` are phase 2 [author 2026-09-02 07:39].

## 10. Configuration, drafter decisions, implementation order

| option | default |
|---|---|
| `\<phi>guard_prove_timeout` | 400 ms, provisional (P-auto's budget; also the floor of a P-auto replay) |
| `\<phi>guard_rconv_timeout` | 300 ms (R-conv's own bound) |
| `\<phi>guard_refute_timeout` | 2000 ms (Nitpick's parameter; R-nitpick's own net is this + 5 s per subgoal) |
| `\<phi>guard_cache` | true |
| `\<phi>log_guard_race` → `\<phi>log_guard_decision` | false (renamed) |

Names approved [author 2026-09-03 04:58, 11:11, 11:15]; ML identifiers not
named by the author are the drafter's under the 11:24 delegation.

Nothing is pending the author (2026-09-03 16:55): (a) a run lemma that
fails to certify or replay at installation raises `Guard_Record_Stale`
[author "(a) 赞同. 要清除 cache 重跑的"]; (b) a run with a record that
succeeds with `final = previous_final` writes nothing [author "(b) 不写"].

**Drafter decisions that change behavior**, each vetoable, none hidden
elsewhere: U2 (the end-of-run joins inside one `uninterruptible_body` with
`run`, cancel-and-rejoin on a raise out of the join — §4); U4 (a judge's
contexts carry no env cell — §4); U22 (one env per `gen_reason'`
invocation via a decision ref — §4); U20 (the end-of-run steps sit outside
`gen_reason'`'s `handle Success` — §4); U3 (the factory parameter's type —
§1); the sequential order of R-nitpick's subgoals inside its one net (§6);
`Time.zeroTime` / `hash = NONE` in the record write (§8); the phase-2
`eval_prf_str` replay of a stored script as a fifth `Guard_Simp_SS`
consumer (§1 — the author named four); the catch-all
decode (§8); the store functor's argument list and the narrowed guard
signature (§8); the compaction-only-if-file-exists gate (§8); `Hasher.goal`
as the exported spelling of both digests (§1); the header wording of the
judge-crash error (§1: "guard judge crashed at call <i> on guard <goal>").

Instrumentation is temporary measurement code [author 2026-09-03 04:01]:
one permanent record, guard_decision (verdict token, replay field,
elapsed, `Hasher.hex` of the digest, call index, n_goals, miss-side
payload), behind `\<phi>log_guard_decision`; `Hasher.hex` appears in exactly
that log line.

Order:

0. Re-verify line anchors; `Hasher.terms`; the tracing gate.
1. `PLPR_Guard_Refuters` (the `Handlers` instance, `judge_arg`,
   `chain_verdict`), the three hooks with their own bounds (R-conv,
   R-nitpick with the `+ 5 s × n` net, the default refuter), the
   `Nitpick_Refute_SS` rename.
2. The factory: `guard_condition_solver` parameterised;
   `try_prove_or_give_up`; `guard_condition_solver'`/`1` on P-auto;
   `Guard_Simp_SS` with its attribute and four `enhance` sites;
   `\<phi>guard_P_auto`'s `method_setup`; the `fastforce` instance for
   `defer_premise`; `prove_or_refute` over the chain, no table, judges
   awaited inline (interim; same session as 3); `guard_condition_judge`;
   migrate every caller (§3) and `Test/Guard_Race_Smoke.thy`.
3. The env, the judges, the end-of-run steps for runs without a record
   (join, classification, crash error, merge), guard_decision.
4. In-memory table: the call index, the record-side path of §5 fed from a
   table injected by the test (hits, the two replays, `Guard_Record_Stale`,
   the re-run), R4.
5. Persistence, gated: proceeds only if step (3)'s temporary
   instrumentation shows record keys repeating across two consecutive
   corpus runs AND the final digest of a repeated key reproducing.  Then:
   the store functor and `Phi_Guard_Store`, the raw-term codec functor and
   its `BytesIO` instance, the gitignore entries, the record read at
   installation (`previous_final`, `entries`, `lemmas`, lemma replay), R1's
   write, R2, R3.
6. Corpus acceptance: a cache-on and a cache-off leg, a concurrent Isa-REPL
   leg, a consecutive-run leg with a hit-rate floor; measure wall time,
   verdict flips per call index cache-on vs cache-off, first-call latency
   at the direct call sites, evidence rate, end-of-run join wall time,
   `Guard_Record_Stale` / R2 / R3 fire counts, digest cost, store I/O;
   re-measure 400 ms.  Testing via Isa-REPL against `Phi_System_Base`
   sources — never `isabelle build`.

After this plan: move the raw-term codec functor to
`Performant_Isabelle_ML` [author 2026-09-03 14:19].

## 11. Archaeology rulings (2026-09-03; all CLOSED)

1. ~~The 35 ms gate~~ — CLOSED 05:20: no gate.
2. ~~Judge spawn after a failed `Proved` replay~~ — CLOSED 10:29/10:31;
   SUPERSEDED 16:01: a failed replay in a run with a record raises
   `Guard_Record_Stale`; no judge is spawned in such a run.
3. ~~`guard_condition_solver` installing its own env~~ — CLOSED 15:45,
   14:54; superseded in shape by the factory (§13).
4. ~~`Lazy`~~ — CLOSED 05:38.
5. ~~Conditional persistence~~ — CLOSED 07:11; refined 08:04 (empty table
   not written) and 16:55 (an unchanged record not rewritten).
6. ~~`final = NONE`~~ — CLOSED 11:39.
7. ~~The record value's shape~~ — CLOSED 05:42.
8. ~~The `\<phi>guard_judge` switch~~ — CLOSED 05:47.
9. ~~The 1.5× multiplier~~ — CLOSED; reconfirmed 2026-09-03 13:03 "B4 没问题".
10. ~~Store-kind refactor extent~~ — CLOSED 13:01 "好": implementation; now
    a functor (§8).
11. ~~Phase-1 enablers~~ — the "(A) 赞同" of 2026-09-02 10:37 covered only
    "is_control_flow 谓词和空引理化简集槽"; the two re-raise clauses and the
    `reason_record` redefinition were never approved, and the whole
    classifier is DELETED [author 2026-09-03 12:59–13:01].  The empty
    simpset slot is `Guard_Simp_SS`.
12. ~~Implementation-order details~~ — CLOSED: work plan.

## 12. Sixth-review rulings (2026-09-03, 07:35–11:25)

The 23 rulings are recorded verbatim in
`GUARD_CACHE_QUICK_MODE_PLAN.rev9.md` §12 (archived beside this file); they
stand, with these supersessions: 1 (R2's exception
arm: still no re-run; first-miss rule added, §13.14); 6 (the reason given
for deleting `probe_group` was false — any judge's exception cancels
`judge_group` — but the design no longer probes the group at all: results
are classified, §4 step 6); 10 (cancelling judges on R2/R3: moot, a run
with a record has no judges); 11 (`aux`: superseded by 14, inlined into
`Provable`); 13 (`judge_group` kept, one level); 18 (the obligation
instance: unbounded BY DEFAULT, 12:53); 22 (`Chain_Answered` /
`judge_outcome`: deleted, a judge's future carries `chain_verdict option`).
Unchanged: 2, 3, 4, 5, 7, 8, 9, 12, 14–17, 19–21, 23.

## 13. Seventh-review and provenance-audit rulings (2026-09-03, 12:23–16:34)

1. **A judge's abnormal exit is the run's failure** [12:23 "一个 racer 异常
   退出的话, gen_reason' 就是应该走异常路径"; 12:27 "judge … 是真的要纠正
   quick mode 下 guard refutation 的问题的 … 必须有 judge 能 … 出来纠正"].
   Judges are first-class; the drafter's "judge is an optional evidence
   collector" framing is withdrawn.
2. **Judge crash = error with the original message** [12:31 "hook 的崩溃应该
   视作 PLPR 推理链的崩溃, 赞同乙"; 12:33; 12:35 "以 ERROR 形式抛出 header +
   \"\\n\" + the message of exn"].  No tombstone.  Seventh-review U5 is
   dissolved: no group probe, results are classified (§4 step 6).
3. **Hooks decide their own timeouts; no wrapper** [12:36].  The rev-9
   wrapper was tagged "[author 2026-09-02]" on the strength of "R-conv 预算
   默认 300ms" alone — a mis-attribution (audit B1).  `bound` deleted.
4. **`Handlers` used directly** [12:37; 12:39 "直接 structure
   PLPR_Guard_Refuters = Handlers ..."].  `add_refuter`, `run_chain`,
   `PLPR_Refuters` deleted as over-design.
5. **`\<phi>guard_cache = false`** = neither read nor written, judges as
   usual [12:52 "1. 批准"].  **`Proved` time = the whole `timed_tac` call**
   [12:52 "2. 批准"].  **Not refreshed on a hit** [12:52 "3. 好"; 14:19
   "C11 否决, 不需要为此更新 proof store"] — moot in a run with a record
   (nothing is written) but recorded.
6. **Obligation `fastforce` unbounded by default** [12:53].  Seventh-review
   U9 rejected.
7. **Run lemmas carry `Phi_Proof_Store.proof_cache`; the judge measures
   the time** [12:53–12:54]; the drafter's reuse of `\<phi>guard_prove_timeout`
   for lemma replay is withdrawn (audit C3).  Lemma replay in
   `gen_reason'`'s own simpset [13:27].
8. **The control-flow classifier and its two re-raise clauses deleted**
   [12:59, 13:01]; its "(A) 赞同" tag was a mis-attribution (audit B2).
9. **B4, B5 fine** [13:03]: `tolerant_time` reuse; the bare-date tags are
   now `[author 2026-09-02 12:08]` and `[13:01 "好"]`.
10. **R-nitpick's net = 2000 ms + 5000 ms × n_goals** [13:05].
11. **Replay failed = miss** [15:46, 16:01]; "not landed" retired [13:10].
12. **`Guard_Simp_SS` precisely at four consumers**, not at `reasoners.ML:1829`
    [13:26–13:27]; the 1801/1829 sites are not duplicates (looper vs.
    solver), and one ctxt flows from 1829 into `prove_or_refute` [13:16].
13. **C5 judge priority, C6 tombstone via `invalidate_proof_cache warn=false`,
    C7 the three store entry points, C8 msgpack term codec via a functor**
    [13:19; 13:27; 14:19 "先放在方便的地方 … 之后 … 移动到
    Performant_Isabelle_ML"].
14. **One miss raises** [15:01; 16:01].  Relaxation A (skip the re-run when
    nothing was consumed) superseded.  Relaxation B (collapse R2's arms) not
    adopted: the author's asymmetry stands.
15. **`judge_arg` without `assms`** [14:53].  **`outer_ctxt`** is
    `guard_condition_solver`'s original ctxt (R-conv's export direction);
    with `fix_level = 1` only premise-only and `LPR_ctrl`-annotated
    variables are fixed [14:43–14:50 discussion].
16. **C13**: re-run lemmas cleared; interrupted run writes and deletes
    nothing; gitignore in `contrib/phi-system/.gitignore` [14:56–14:57].
17. **env shape unchanged** [16:00 "原本的 type env 就已经足够了"; 16:34];
    "no record" = `previous_final = NONE`; the drafter's `record option`,
    `proved`, `new_entries` proposals withdrawn.
18. **A run with a record spawns no judge** (a consequence of 14 the author
    confirmed at 16:34): R2/R3 need no cancellation; §5's two replay arms
    are one rule.
19. **A run lemma that fails to certify or replay at installation raises
    `Guard_Record_Stale`** [16:55 "(a) 赞同. 要清除 cache 重跑的"].
20. **An unchanged record is not rewritten** [16:55 "(b) 不写"].

Seventh-review drafter fixes applied (listed in §10 where they change
behavior): U1 (step 2 reads the record; now structural), U2, U3, U4, U8
(`Hasher.goal`, anchors, the gate's second leg), U13, U14, U16, U17, U18
(rewritten for the first-miss rule), U19, U20, U21, U22, U23.  Moot: U7
(lemma replay is now (a) in §10), U10/U11 (no wrapper), U12 (a
sub-attempt's exception is a crash), U15 (functor).
