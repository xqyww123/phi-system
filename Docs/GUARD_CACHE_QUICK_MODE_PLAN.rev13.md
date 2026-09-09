# PLPR Guard Cache — prove_or_refute rework

Status: rev 13 (2026-09-08).  The tenth review (NOT_READY: 0 blockers,
2 majors — the replay ran in a weaker ctxt than the recording; the factory
contract was partial — and 22 one-sentence fixes, §16) is folded in, with
the author's rulings of 2026-09-08 02:02–02:43.  The design is synchronous
with a cache:
`prove_or_refute` gives a final verdict on the spot and writes it to its
slot; ONE optional judge lives in a global `Unsynchronized.ref` [author
2026-09-04 03:04 "整体不再采用异步, 而是只保留缓存. 取消 the hooks 设计, 改为
a single `hook option Unsynchronized.ref`"].  The ninth review (NOT_READY,
26 upheld, 2 structural) and the author's rulings of 2026-09-04 04:16–04:35
and 2026-09-07 12:34–15:10 (§15) changed four things: (1) run lemmas are
bound to the slot whose judge produced them and, once enabled, travel in
the ctxt to every later call and — through a `PLPR_Context_Export` hook of
the stateful PLPR reasoning — to the following phi statements; (2) without
a judge, `prove_or_refute` answers `Unprovable` as soon as P-auto fails and
runs R-conv, R-nitpick and the warning in one unjoined `Future.fork` (the
refutation future); (3) the no-cache re-run is an internal
`use_cache = false` call; (4) the judge must not re-enter PLPR (a contract,
no check).  This document states the FINAL design only.  History lives in
`GUARD_CACHE_QUICK_MODE_PLAN.rev7-full.md`, `.rev9.md`, `.rev10.md`,
`.rev11.md` and `.rev12.md` (archived beside this file); consult them for history, never
for the design.  Every behavioral decision carries its provenance: [author
YYYY-MM-DD HH:MM "quote"] is the author's own ruling (transcript timestamp,
UTC), [drafter] is a drafting decision the author may veto; §10 lists every
[drafter] decision that changes behavior.

Predecessor: `GUARD_NITPICK_FALSIFY_PLAN.md` (the guard race this plan
dismantles).  Prerequisite, already implemented: the stateful PLPR
reasoning (`ai-artifacts/STATEFUL_PLPR_REASONING_PLAN.md`,
`library/context_export.ML`): `Phi_Reasoner.reason`/`reason1` return a
`context_state`, and registered `PLPR_Context_Export.Hooks` carry hook-owned
data across run and block boundaries.  Line anchors into `reasoners.ML`,
`cache_file.ML`, `mlmsgpack.sml` and `pretty.ML` are as of 2026-09-04
(`PLPR.thy` and `reasoner.ML` anchors re-taken 2026-09-07 after the
stateful-PLPR commits) and are re-verified at implementation start (§10.0);
§8's again at step (4).  No code has been written.

Submitted for an eleventh review, scoped to §1, §3, §4, §5, §6 and §8.

---

## 1. Glossary

Each entry gives the term, its meaning, and where the term comes from: the
author's own words, an existing name in the code, or a plain descriptive
phrase.  No other name is used for any of these concepts anywhere in this
document.

- **guard**: a premise of the `\<condition>` family (`Premise mode P`, mode
  `MODE_GUARD` or `NO_INST`; `is_guard_mode`, `reasoners.ML:1779-1781`),
  discharged inside a run by the reasoners registered at `PLPR.thy:1984`,
  `:1987`.  [code]
- **a `prove_or_refute` call**: one invocation of `prove_or_refute` run
  through its whole protocol (§5).  Its ML type becomes `bool ->
  Proof.context -> context_state -> context_state Seq.seq` (`can_inst`, the
  guard-side ctxt, then the run's state: the run's ctxt `ctxt0` and the
  goal state) [author 2026-09-04 04:19 "我们要把 prove_or_refute 的类型改成
  context_state -> context_state, 我们要改 context, 且要一路改下去一直到
  gen_reason' 的返回"].  The ctxt it returns is `ctxt0` with the slot's run
  lemmas added to `Guard_Simp_SS`, and nothing else changed.  It is
  synchronous: its verdict is final when it returns [author 2026-09-04
  03:04]; without a judge that verdict is `Unprovable` the moment P-auto
  fails (the refutation future does the rest, §6).  [descriptive]
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
  the solving function it ends with, whose type is `prove_or_refute`'s
  [type: drafter].  The factory's contract, total [drafter, tenth review]:
  `oblg_template` (`reasoners.ML:336-380`) is SHARED — four live callers,
  `defer_obligation` `:819`, `hammer_obligation_solver` `:850`,
  `guard_condition_solver` `:1788`, `safe_obligation_solver` `:1850` — and
  becomes polymorphic in the solving function's result type `'a` through
  two extra parameters, `inj : thm -> 'a` (how a thm that never reached the
  solving function becomes a result) and `on_thm : (thm -> thm) -> 'a ->
  'a` (how a thm-to-thm post-pass reaches the result); the three
  thm-returning callers pass `I` and `I`, the guard path passes `pair
  ctxt0` and `apsnd`.  Every exit of the template that bypasses the solving
  function goes through `inj` — the `TrueI` exit `:344-345`, the two
  `fast_inst` exits `:346-347` and `:369-370`, and `guard_condition_solver`'s
  own `is_F` arm `:1804-1806` — so each such result is paired with the ctxt
  the factory was CALLED on, `ctxt0`, never with `oblg_template`'s imported
  `ctxt'` (`:364`, whose fresh frees would make the export hook drop the
  very lemmas the design carries); the `Variable.export_inst` post-pass
  `:375-378` and `head_only`'s `Goal.conclude` (`:385-388`; its
  zero-premise arm `:386` returns the state unchanged) go through `on_thm`,
  i.e. act on the thm half; `apply_tac`'s `SOLVED'` filter likewise.
  Invariant: the state leaving a guard reasoner is `ctxt0` plus that slot's
  run lemmas, and only the solving function may replace the ctxt.
  Three instances (§3): **`guard_condition_judge`** = the factory applied
  to `prove_or_refute`, `{can_inst : bool} -> context_state ->
  context_state Seq.seq`, registered on the state by the in-run
  `\<condition>` reasoners as `guard_condition_judge {can_inst = …} o snd`
  (at `PLPR.thy:1984`, `:1987` only `Phi_Reasoners.wrap` goes — it re-pairs
  the incoming ctxt and would drop the lemmas; `o snd` stays because
  `apply_tactic`, `reasoner.ML:688`, hands an ML reasoner `(backtrack_mode,
  context_state)`); the existing **`guard_condition_solver'`** /
  **`guard_condition_solver1`** = the factory applied to
  `try_prove_or_give_up` over P-auto, used by the out-of-run callers; and
  the factory applied to `try_prove_or_give_up` over `fastforce` for
  `defer_premise`'s solve-now case.  The two degenerate instances ignore
  `can_inst`, return the ctxt they were given, and keep their thm-returning
  entry points.  [author 2026-09-03 09:44; 11:11]
- **`try_prove_or_give_up`**: `Time.time option -> (Proof.context -> tactic)
  -> Proof.context -> thm -> thm Seq.seq` — run the tactic once, under the
  bound if given, keep only a solved state; otherwise `Seq.empty`.  Out of
  a run: `SOME \<phi>guard_classic_prover_timeout` over P-auto [author
  2026-09-03 09:44]; for obligations: `fastforce` in a
  `Guard_Simp_SS`-enhanced ctxt, no bound by default [author 2026-09-03
  11:15; 12:53].
- **verdict**: the value stored for one guard —
  ```
  datatype verdict =
      Proved of {proof : Phi_Proof_Store.proof_cache,
                 lemmas : (term * Phi_Proof_Store.proof_cache) list}
    | Unprovable of {refuter : string}
  ```
  `Phi_Proof_Store.proof_cache = Time.time * string` (`cache_file.ML:149`:
  standard-machine time, method text) [author 2026-09-02 12:03; 2026-09-03
  11:00; `Refuted` renamed `Unprovable` 2026-09-04 03:23; `lemmas` moved
  from the record into the slot: author 2026-09-04 04:19 "我们要把 lemmas
  记录绑定到 the goal 上"].  A guard proved by P-auto stores `{proof =
  (elapsed, "\<phi>guard_P_auto"), lemmas = []}`.  `refuter` names who
  decided: `"R-conv"`, `"R-nitpick"`, `"judge"` (these three only with a
  judge installed, §5), or `"quickcut"` (no judge: the answer was given
  without waiting for the refuters, which ran in the refutation future;
  nothing about their outcome is recorded) [author 2026-09-03 04:58;
  2026-09-04 04:26 "建议给槽一个特殊的名字, 比如 `bypass` or `quickcut`";
  2026-09-07 15:10 "赞同 quickcut"].  The run-time answer of a
  `prove_or_refute` call IS its verdict: a solved goal state for `Proved`,
  `Seq.empty` (the engine backtracks) for `Unprovable`.  `verdict` is
  declared in `guard_cache.ML` (§4); `judgement` (below) in `reasoners.ML`
  beside the judge — two `Unprovable` constructors in two structures.
The five protocol stages that follow — P-auto, R-conv, R-nitpick, the
judge, the refutation future — describe a call WITHOUT a record; in a run
with a record every call is a hit or `Guard_Record_Stale` (§5) and none of
them runs.

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
  another, EACH under its own inner `Timeout.apply` of
  `\<phi>guard_refute_timeout + 5000 ms` so that one subgoal's overrun
  moves on to the next instead of eating the whole net [author 2026-09-03
  13:05; inner bound 2026-09-07 13:00 "3. 采纳"; order: drafter].  Both
  catch their own `TIMEOUT` and report "not refuted".  They always run: with
  a judge, inline before the judge; without a judge, in the refutation
  future (§6) after `prove_or_refute` has already answered — so that a guard
  R-conv or R-nitpick can refute is refuted silently instead of warned about
  [author 2026-09-04 03:23 "在 warning 前要跑 R-conv R-nitpick 的, 以此来减少
  warning"; 04:16].
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
  is: the proof may instantiate schematic variables.]  What the absence of
  a check means, stated as the code has it: `Goal.conclude` strips the `#`
  by the CURRENT premise count (`Pure/goal.ML:74`; Pure keeps
  `check_finished` apart, `:79-85`), so a returned state that is not
  solved passes `head_only` and is dropped silently by `apply_tac`'s
  `SOLVED'` (`reasoners.ML:222`, `Pure/tactical.ML:297-298`) — an ordinary
  reasoner failure, after the slot was already written `Proved`; the next
  run's replay then fails and the run repeats without the cache (§7).  Only
  a conclusion that is no longer `#…` fails loudly (`THM` from
  `Drule.comp_no_flatten`).  `judge_arg.ctxt` is the guard-side ctxt,
  `outer_ctxt` is `ctxt0`, the run's ctxt.  The judge measures the times in
  `lemmas` and `proof` itself [author 2026-09-03 12:54], as RAW elapsed
  time; `prove_or_refute` applies `Phi_Proof_Store.standard_time` to
  `proof`'s time and to every lemma's time at the single write point (§5
  step 8), so normalisation happens exactly once.  It is called on
  each run's own thread, concurrently across runs, and must be re-entrant.
  Its obligations, a contract with no run-time check [author 2026-09-07
  13:21 "定一条规约, judge 不能重入 PLPR"; 13:24 "如果你偏执, 你可以写到规约
  里"]: (a) it must not invoke PLPR reasoning, neither itself nor through
  the method text of `proof` or of any lemma — a re-entering run would
  share this run's counter (§4 Nesting) and, being replayed differently
  later, shift every later call index; (b) each lemma is a closed statement
  certifiable by `Thm.cterm_of` and provable by its own method text in
  `ctxt0` — without `oblg_template`'s fixes, the inserted aux facts and the
  guard-side assumptions (§1 run lemmas).  An exception escaping the judge
  (or a refuter run inline) propagates through `prove_or_refute` like any
  other exception of the run [author 2026-09-03 12:31 "hook 的崩溃应该视作
  PLPR 推理链的崩溃"].
- **`Guard_Simp_SS`**, attribute **`\<phi>guard_simp`**: the simpset that
  strengthens guard proving — an instance of the repository's `Simpset`
  functor (`library/tools/simpset.ML`) [author 2026-09-03 11:15].  Applied
  by an `enhance` inside each consumer and nowhere else [author 2026-09-03
  13:26–13:27]: the "G.simpcut" preprocessing pass (`reasoners.ML:1802-1803`),
  `p_auto_body` (so `\<phi>guard_P_auto` and the P-auto replay), R-conv,
  the obligation instance's `fastforce`, and [drafter] the `eval_prf_str`
  replay of a stored script (on the guard-side ctxt, §5 step 2).  Not
  R-nitpick (it stacks only `Nitpick_Refute_SS`, today's `Guard_Refute_SS`
  renamed [author 2026-09-03 11:15]), not the ctxt built at
  `reasoners.ML:1829` as such, not `judge_arg.ctxt`.  `enhance` is a merge
  (`simpset.ML:79-81`); each consumer enhances the ctxt it hands to its
  simplifier and never rebinds `auto_tac`'s `ctxt`, which would carry the
  simpset into R-nitpick and `judge_arg.ctxt`.  A `Simpset` instance holds
  two `Generic_Data` slots (`simpset.ML:69-73`, `:90-93`): the simpset
  itself, which `enhance` merges, and a `Named_Thms` net of the theorems as
  declared, which `simp_rules` returns — a simpset cannot give back the
  theorems it was built from.  Every write goes through `add_simps` /
  `del_simps` (`:97-103`), which update both slots.  Its proof-context-level
  half is also the carrier of run lemmas (below): they are added with
  `Guard_Simp_SS.add_simps'` to the ctxt a `prove_or_refute` call returns,
  and the guard-cache export hook carries them onward.
- **the guard-cache export hook**: one `PLPR_Context_Export.Hooks` entry
  (priority: drafter) registered by `guard_cache.ML`.  At every run and
  block boundary it takes `Guard_Simp_SS.simp_rules inner`, passes each
  theorem through `PLPR_Context_Export.export_aux_lemma inner outer` (a
  theorem mentioning a variable fixed inside is dropped, one an assumption
  frame refuses — `UNEXPORTABLE` — is dropped, the rest are exported), and
  OVERWRITES the proof-context-level half of `outer`'s `Guard_Simp_SS` with
  the result: `del_simps` of `simp_rules outer`, then `add_simps'` of the
  exported list — no equality check [author 2026-09-04 07:33 "直接覆写是最快
  的"; 2026-09-07 12:34 "启用进 ctxt 的 lemma 要流到后续语句. 是的,
  Guard_Simp_SS"].  It satisfies the hook contract of the stateful PLPR
  plan (H1 one theorem at a time through `export_aux_lemma`, H2
  re-exportable — `context_export.ML:16` names overwriting as satisfying
  it, H3 own data only).  Through it a lemma enabled at slot `i` reaches
  every later call of the run, the run's returned ctxt, and the following
  phi statements of the block — unless a block frame refuses it.
- **the undecided-guard warning**: the message printed over a guard's
  subgoals when neither a proof nor a refutation was found and no judge is
  installed — today's text at `reasoners.ML:1605-1616`, factored into one
  function of the ctxt and the subgoals; printed, as today, through
  `Phi_Reasoner.warn_pretty … 1` (`reasoner.ML:337-340`), i.e. only where
  `\<phi>trace_reasoning >= 1` (the corpus sets it: `IDE_CP_App2.thy:256`).
  Printed by the refutation future only (§6); never on a hit [author
  2026-09-07 12:58 "赞同 (a) 反对 (b) 不要再跑反驳或警告"].  [descriptive]
- **the refutation future**: the one `Future.fork` a `prove_or_refute` call
  without a judge spawns after P-auto fails, running R-conv, R-nitpick and
  — if neither refutes — the undecided-guard warning, in that order, on the
  values the call captured (`can_inst`, the guard-side ctxt, `ctxt0`, the
  goal state) [author 2026-09-04 04:16 "先返回 unprovable 并启动一个 future
  work 去跑 R-conv, R-nitpck 以及最后的 warning"; `Future.fork`: 2026-09-07
  15:10].  Never joined; never touches the env or the store.  Its body is
  wrapped in one handler: an interrupt is re-raised, any other exception
  is printed as an error message (`Runtime.exn_message`; raising it again
  would vanish, an unjoined future's exception is seen by nobody) [author
  2026-09-07 12:34 "加个大 handler 捕获所有非 interrupt 异常然后 error 报
  告"].  Measured 2026-09-04: an unjoined `Future.fork` task completes in a
  batch build (`Session.finish` waits in `Future.shutdown`), and its
  warning and error messages reach the command that spawned it even after
  that command finished (`Position.thread_data` is snapshotted at fork).
  `Future.fork` puts the task in a child group of the spawning thread's
  group WHEN that thread is a Future worker — PIDE command execution,
  forked proofs — so that in PIDE an edit of the command cancels it (the
  warning is moot then) and the theory's `consolidated` state
  (`Execution.join`) waits for it; for an ordinary theory-level command on
  the batch path nothing at the theory level waits, only `Session.finish`;
  and under Isa-REPL, whose commands run on an `Isabelle_Thread.fork`ed
  worker, no command-level cancel reaches it.
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
  env.  `gen_reason'` is the public face of an internal function
  `gen_reason_i : bool (*use_cache*) -> …` (name: drafter): `gen_reason' =
  gen_reason_i true`; the no-cache re-run is `gen_reason_i false` [author
  2026-09-07 15:01 "把 use_cache : bool 作为参数给进去"].  `use_cache` gates
  the record READ only; the write (§4 step 5) does not consult it.
- **run failure**: the topmost `gen_reason'` invocation returning `NONE`,
  or ending with a non-interrupt exception (`Interrupt_Family.contains_interrupt`
  false, `reasoners.ML:1635`) [author 2026-09-03 07:35].  A nested
  `\<r>BEGIN` reasoning whose nested run returns `NONE` raises an ERROR
  (`nested.ML:33`); `gen_reason`'s step limit raises too
  (`reasoner.ML:789-793`).
- **`Guard_Record_Stale`**: the exception a run WITH a record raises the
  first time the record fails to reproduce — always at a `prove_or_refute`
  call: slot absent, stored digest different, a `Proved` hit one of whose
  lemmas fails to certify or replay, or a `Proved` hit whose proof replay
  fails.  It
  passes through every nested `gen_reason'` (they catch only `Success`,
  `Global_Cut`, `Explorative_Backtrack`, `reasoner.ML:798-805`, `:913`) to
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
  run's `{final, entries}` (§8).  Key: `"PLPRGUARD" ^ Hasher.compact
  (Hasher.goal (ctxt, initial))` of the run's first pulled initial state
  (`Hasher.goal`, `Hasher.ML:243-246`, salts the theory short name and the
  ctxt's assumptions) [author 2026-09-03 02:18; 08:33; 08:44; `compact`
  kept over `hex`: 2026-09-07 13:09 "我坚持用 compact"].  `Hasher.compact`
  (`Hasher.ML:71-74`, `:111-118`) is the 8-byte big-endian rendering; the
  key is therefore not text and is never printed — `guard_decision` (§10)
  prints `Hasher.hex` of the guard digest, not the key.  Stability caveat:
  `Hasher.goal` is the formula `cache_file.ML:898-901` calls not invariant
  under fork/promise discharge; a moved record key is not a
  `Guard_Record_Stale` (no record is found: the ordinary no-record path)
  but a permanent miss plus one more record in the file under the new key,
  never a wrong verdict.
- **final digest**: `Hasher.goal (ctxt', th')` of the run's resulting state
  [author 2026-09-02 07:11]; it includes the conclusion.  Same caveat; a
  final digest that is not reproducible at all costs one R3 re-run on
  EVERY run — §10 step (4)'s gate measures this before persistence lands.
- **tombstone**: the proof store's own per-key deletion (`TOMB`,
  `cache_file.ML:76`; `encode_tombstone`, `:108`), written by
  `Phi_Guard_Store.invalidate_proof_cache` with `warn = false` [author
  2026-09-03 13:19].
- **the no-cache re-run**: after the record has been tombstoned, the
  topmost invocation calls `gen_reason_i false` with its own arguments
  [recursive call: author 2026-09-04 03:04 "A 批准" — eighth review
  relaxation 1; the parameter: 2026-09-07 15:01].  With `use_cache =
  false` installation skips the record read and builds the no-record env
  (`previous_final = NONE`, empty table); the new invocation performs its
  own end-of-run steps and writes its record under R1, and — having no
  record — can neither raise `Guard_Record_Stale` nor fire R2/R3: it is a
  leaf by construction, whatever the tombstone's timing and whatever
  another process writes under the key meanwhile (the tombstone is still
  written, for the next process).  Residual: a second "Time spent by
  \<phi>-LPR reasoning" line when `count_performance` is on.
- **run lemmas**: the `lemmas` of a `Proved` verdict —
  `(term * Phi_Proof_Store.proof_cache) list`, (statement, (replay time,
  method text)) — produced by the judge's `Provable` and bound to the slot
  the judge answered [author 2026-09-04 04:19 "在某个 goal 上给的 lemmas
  只在证明那个 goal 上启用, 但启用后 … 要改 context, 且要一路改下去"].  They
  are ENABLED at that slot, after the slot's digest has been taken: in the
  run that consults the judge, right after its answer; in a run with a
  record, at the hit of that slot (§5) — the same point in both, so every
  later guard's digest is computed under the same `Guard_Simp_SS` in both
  runs.  Enabling = for each lemma, `Thm.cterm_of ctxt0` on its statement
  ("fails to certify" = `TYPE` or `TERM` out of it, caught with an explicit
  `handle`, the interrupt family untouched), `Thm.trivial` of the cterm as
  the goal, `eval_prf_str` of its method text with `n = 1` under
  `tolerant_time` of its recorded time, in `ctxt0` (the run's ctxt: its own
  simpset, without `\<phi>guard_simp`) [author 2026-09-03 10:53; 12:54;
  13:27] — `eval_prf_str`'s own `Goal.conclude` then hands back the plain
  theorem — then `Guard_Simp_SS.add_simps'` of the thms into `ctxt0`,
  giving the ctxt the call returns, and into the guard-side ctxt the replay
  runs in (§5 step 2).  From `ctxt0` they reach every later call of the run
  and, through the guard-cache export hook, the following statements
  [author 2026-09-07 12:34].  One that fails to certify or replay: in a run
  with a record, `Guard_Record_Stale` [author 2026-09-03 16:55]; in the run
  that consulted the judge, an `error` naming the lemma — the judge broke
  contract (b) — propagating as the run's exception [drafter].  Phase 1 has
  no producer.
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
`judges`, "judge crash", "merge", "join" = (deleted: the only asynchrony
left is the unjoined refutation future);
"Chain_Ran" / "Chain_Answered" / `judge_outcome` / `add_refuter` /
`run_chain` / `PLPR_Refuters` / `bound` = (deleted); "the control-flow
classifier" / `is_control_flow` = (deleted); "not landed" = replay failed;
`\<phi>guard_prove_timeout` / `\<phi>guard_rconv_timeout` =
`\<phi>guard_classic_prover_timeout`; "the auxiliary-lemma slot" =
`Guard_Simp_SS`; "Guard_Refute_SS" = `Nitpick_Refute_SS`; "type proof" =
`Phi_Proof_Store.proof_cache`; `th` (in `judge_arg`) = `thm`; `"assum"`
(refuter) = (retired: never written — without a judge the slot is
`"quickcut"`, with a judge the judge decides); "bypass" = `"quickcut"`;
`read_record` = `use_cache`; "the env cell blanked for the judge" =
(rejected 2026-09-07 13:21: a contract instead); the record's `lemmas`
field = (moved into `Proved`).

## 2. Motivation

~88 % of the corpus's `prove_or_refute` calls end with the guard not
holding (median refuted 607 ms, undecided 2367 ms).  The cache removes
that cost from every run after the first: a recorded `Unprovable` is
answered at once, a recorded `Proved` is replayed under a generous bound,
and the whole record is validated end to end per run (§7).  Without a
judge even the first run pays only P-auto's budget on the run's thread:
the refuters and the warning go to the refutation future [author
2026-09-04 04:16].  Soundness is
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
IN A RUN   (\<condition> ?P, \<condition>[NO_INST] ?P reasoners, PLPR.thy:1984/1987)
  gen_reason' = gen_reason_i true   (reasoner.ML:906), on entry:
    slot check on the first pulled state's ctxt —
      no cell, or a cell holding NONE  → install a fresh env: this is the
                                          topmost invocation; it alone
                                          performs the end-of-run steps;
                                          the record is read only if use_cache
      a cell holding SOME env           → inherit; nothing at the end
    … reasoning …  (state = (ctxt, thm); the ctxt flows from call to call)
      guard_condition_judge = guard_condition_solver prove_or_refute
        prove_or_refute can_inst ctxt (ctxt0, thm)   (env read from ctxt0):
          i := next call index; d := this guard's digest
          WITH A RECORD (previous_final = SOME _):
            slot i = (d, Unprovable _)        → Seq.empty, silent
            slot i = (d, Proved {proof, lemmas})
                                              → enable lemmas into ctxt0 → ctxt1 and into
                                                 the guard-side ctxt → ctxt_g
                                                 (a lemma fails → raise Guard_Record_Stale);
                                                 replay proof under its bound in ctxt_g;
                                                 replay failed → raise Guard_Record_Stale;
                                                 else return (ctxt1, solved)
            slot i absent or digest ≠ d       → raise Guard_Record_Stale
          WITHOUT A RECORD (previous_final = NONE), verdict written at once:
            P-auto proves                     → slot i := Proved {(elapsed, "\<phi>guard_P_auto"), []};
                                                 return (ctxt0, solved)
            else judge = NONE                 → slot i := Unprovable {"quickcut"};
                                                 spawn the refutation future
                                                 (R-conv → R-nitpick → the warning);
                                                 return Seq.empty at once
            else (judge = SOME j), inline:
                 R-conv refutes               → slot i := Unprovable {"R-conv"}, silent
                 else R-nitpick refutes       → slot i := Unprovable {"R-nitpick"}, silent
                 else j answers Provable {lemmas, proof, thm}
                                              → enable lemmas into ctxt0 → ctxt1
                                                 (a lemma fails → error);
                                                 slot i := Proved {proof, lemmas};
                                                 return (ctxt1, thm)
                 else j answers Unprovable    → slot i := Unprovable {"judge"}, silent
    end-of-run steps (topmost invocation only):
      close (cell := NONE) → classify the run's outcome (§4):
        Guard_Record_Stale, R2 (NONE), R3    → tombstone; gen_reason_i false; its result
        R2 (exception)                       → tombstone; re-raise
        failure without a record, interrupt  → nothing written; propagate
        success without a record             → persist if the table is non-empty
        success with a record                → final digest = previous_final → nothing written
    the run's resulting ctxt leaves gen_reason' with the thm (stateful PLPR);
    at the run boundary the guard-cache export hook carries Guard_Simp_SS

OUT OF A RUN   (guard_condition_solver' / guard_condition_solver1: four
                command-level callers in Phi_System — local_value.ML:169,
                toplevel0.ML:387, generic_variable_access2.ML:182, :272;
                application.ML:137 is commented out — solving proof
                obligations, `Premise default P` / `Premise MODE_COLLECT P`)
  guard_condition_solver (fn _ => fn ctxt => fn (ctxt0, th) =>
      try_prove_or_give_up (SOME \<phi>guard_classic_prover_timeout) p_auto_body ctxt th
      |> Seq.map (pair ctxt0)):
    same preprocessing, then P-auto once; not proved → Seq.empty → the
    caller's error continuation.  A deliberate narrowing: today these sites
    also get a 35 ms auto_search_tac gate (reasoners.ML:1602) and a 2000 ms
    P-auto budget (:1618, :1701); all four sites raise `error` on failure,
    so §10 step (5) surfaces any regression as a build failure.

OBLIGATIONS SOLVED ON THE SPOT   (defer_premise, PLPR.thy:1975/1976, when
                Phi_Reasoner_solve_obligation_and_no_defer is 1 or 2 — set
                by the user's prove_obligations_in_time and internally by
                SE_Trim_Empty.ML:54, :114, rule_generation.ML:443)
  guard_condition_solver (fn _ => fn ctxt => fn (ctxt0, th) =>
      try_prove_or_give_up NONE fastforce (Guard_Simp_SS.enhance ctxt) th
      |> Seq.map (pair ctxt0)):
    same preprocessing, then fastforce, unbounded by default; not proved →
    Seq.empty → backtrack.  No table, no warning.
```

Removed: the `Race.race` call, the three racer wrappers, the in-race
`protocol` var, `\<phi>guard_race_timeout`, the 35 ms gate, and every
asynchronous piece except the refutation future.  Reused: `Hasher`, the
proof store (as a functor instance, §8), `eval_prf_str`, `Simpset`,
`PLPR_Context_Export` (the hook), the R-conv/R-nitpick bodies (screens
verbatim), `RPC_Pretty`'s raw term codec (functorised, §8).
`Phi_Reasoners.wrap` stays at every registration except the two guard
reasoners, which now take the state directly (§1
`guard_condition_solver`) [2026-09-02 12:08 "registrations unchanged"
superseded for these two by 2026-09-04 04:19].

Every caller of the old `guard_condition_solver` must migrate, and the
factory's changed type makes a missed one a compile error.  Known callers
(2026-09-07): `PLPR.thy:1984`, `:1987` → `guard_condition_judge` on the
state; `PLPR.thy:1975`, `:1976` (`defer_premise`) → the `fastforce`
instance [author 2026-09-03 11:15]; `Test/Guard_Race_Smoke.thy:79` →
migrated at §10 step (2).  `oblg_template`'s two new parameters (§1) make
its other three callers compile errors too: `defer_obligation`
`reasoners.ML:819`, `hammer_obligation_solver` `:850`,
`safe_obligation_solver` `:1850` each pass `I` and `I`.

## 4. The env

```
type env =
  {record_key     : string,
   previous_final : Hasher.digest option,            (* NONE = no record *)
   counter        : int Unsynchronized.ref,
   entries        : (Hasher.digest * verdict) Inttab.table Unsynchronized.ref}
```

[author 2026-09-03 16:00 "原本的 type env 就已经足够了"; 16:34; the two
asynchrony fields removed 2026-09-04 03:04; the `lemmas` field gone with
the lemmas into `Proved` 2026-09-04 04:19.]  Plain refs; only the run's
own thread touches them (the refutation future never does).  In a run
with a record `entries` holds the record as read and is never written
(§5); in a run without a record it starts empty and is built in place.
The env, its cell, `verdict`, `Guard_Record_Stale`, `Guard_Simp_SS`,
`\<phi>guard_cache`, the export hook, the store instance and the record
codec are declared in a new `library/guard_cache.ML`, loaded by `PLPR.thy`
between `context_export.ML` (`:542`) and `reasoner.ML` (`:543`) —
`gen_reason'` needs all of them, and `reasoners.ML` (`:1960`) comes 1400
lines later [drafter, ninth review].  Everything it needs is in scope
there: `Hasher`, the proof store, `Phi_Sledgehammer_Solver` and
`RPC_Pretty` arrive through PLPR's imports.  `Hasher.terms` is NOT here:
`Hasher : HASHER` (`Hasher.ML:81`) hides its accumulator, so `terms` is
added to `HASHER` and to `Hasher.ML` itself (§10 step 1); its only caller
is `prove_or_refute`.

- **Installation**, in this order [order: drafter, eighth review]:
  1. `gen_reason_i use_cache` reads the slot of the FIRST PULLED initial
     state's ctxt (`reasoner.ML:809`).  No cell, or a cell holding `NONE`
     → this invocation is the topmost one; a cell holding `SOME env` →
     inherit, nothing more.  ONLY `gen_reason'` installs on the production
     path; installation is an exported function whose only other caller
     is §10 step (3)'s test [author 2026-09-02 15:45; 14:54].
  2. Compute `record_key`.  If `use_cache` and `\<phi>guard_cache` (read
     once from `gen_reason'`'s own ctxt argument; step 5's write uses the
     same reading) → read the record (§8's decode is catch-all and cannot
     raise); found → `previous_final := SOME final`, `entries := its
     table`.  Otherwise — `use_cache = false`, switch off, or no record —
     `previous_final := NONE`, `entries := Inttab.empty`.  Eagerly [author
     2026-09-03 05:38].  `counter := 0`.
  3. Put the env into a fresh cell.  `gen_reason_i` keeps one decision ref
     per invocation and maps `apfst install` lazily over the initial
     states; `install` consults the ref — undecided (the first pulled
     state) → decide as in 1–2 and record the cell; already decided → put
     the recorded cell.  One invocation mints at most one env [drafter,
     seventh review U22; every live caller passes a single-element
     sequence].  Nothing else is installed: run lemmas enter the ctxt at
     their slot (§5), not here.  Putting the cell makes the ctxt physically
     new, so `export_context`'s `pointer_eq` short-circuit
     (`context_export.ML:54`) never fires for a run that installs an env:
     the export hooks run at every such run boundary (§10 step 5 measures
     the guard-cache hook).
- **Nesting**: a nested `gen_reason'` (`\<r>Call`, `\<r>BEGIN`,
  `ToR_Entry_Point` via `internal_reason`) inherits: one table, one
  counter; no end-of-run steps.  Its `NONE` is ordinary backtracking for
  `\<r>Call` and `ToR_Entry_Point` (`nested.ML:42-45`); `\<r>BEGIN`
  converts it to an ERROR (`nested.ML:33`).  `Guard_Record_Stale` passes
  through all of them.  [author 2026-09-02 15:45, 16:02]  The judge's
  contract (§1) keeps the judge, its proof texts and its lemma proofs out
  of this rule; P-auto, R-conv and R-nitpick never re-enter PLPR
  (`auto_search_tac` / `p_auto_search_tac`, `reasoners.ML:1154-1185`, are
  Classical/Simplifier pipelines; R-nitpick calls Nitpick).
- **End-of-run steps** (topmost invocation only).  They wrap the RESULT of
  the topmost `gen_reason_i` — outside its own `handle Success ret => SOME
  ret` (`reasoner.ML:913`), so PLPR's control-flow exceptions are
  structurally unreachable here [drafter, seventh review U20].  If the
  initial-state sequence is empty `gen_reason_i` pulls nothing and returns
  `NONE` (`reasoner.ML:779-783`): no env, nothing here runs.  Nothing here
  defers interrupts: there is no join, and the store's own
  `with_file_lock` keeps its blocking wait interruptible only when entered
  with ordinary attributes (`cache_file.ML:383-405`).  In order:
  1. `cell := NONE` [author 2026-09-03 08:08].
  2. **`Guard_Record_Stale` escaped** (only possible with a record):
     tombstone; the no-cache re-run (`gen_reason_i false`); return its
     result [author 2026-09-03 15:01, 16:01; 2026-09-04 03:04; 2026-09-07
     15:01].
  3. **Run failure WITH a record**: `NONE` → R2 with re-run: tombstone,
     `gen_reason_i false`, return its result.  Non-interrupt exception →
     R2 without re-run: tombstone, re-raise [author 2026-09-03 07:35].
  4. **Run failure WITHOUT a record**, or an **interrupt** from any run:
     nothing written, nothing deleted; return the `NONE` / re-raise
     [author 2026-09-03 14:56].
  5. **Success WITHOUT a record**: compute the final digest; persist
     `{final, entries = !entries}` (§8) if `entries` is non-empty AND
     `\<phi>guard_cache` is true (the reading of step 2) [author 2026-09-03
     08:04; 12:52; 2026-09-04 03:23 "无论是否配置了 judge, 在无缓存下正常运行
     结束后都一定要写缓存"].  `use_cache` is not consulted: the re-run writes.
  6. **Success WITH a record** (`entries` unchanged): compute the final
     digest; `<> previous_final` → R3: tombstone, `gen_reason_i false`,
     return its result.  Equal → nothing written [author 2026-09-03 16:55
     "(b) 不写"].

## 5. One `prove_or_refute` call

Inside a run only.  `prove_or_refute can_inst ctxt (ctxt0, thm)`: `i :=
!counter; counter := i + 1`; `d := Hasher.terms (map Thm.term_of
(Thm.cprems_of thm))` on the goal state as received — BEFORE any lemma of
this slot is enabled.  Then by `previous_final`:

**With a record** (`SOME _`) — the run tolerates no miss [author 2026-09-03
15:01, 16:01]:

1. Slot `i` is `(d', Unprovable _)` with `d' = d` → return `Seq.empty`,
   silently, whatever the refuter — a `"quickcut"` hit runs no refuter and
   prints no warning [author 2026-09-07 12:58 "赞同 (a) 反对 (b) 不要再跑
   反驳或警告"].  Never re-judged [author 2026-09-02 10:40].
2. Slot `i` is `(d', Proved {proof = (t, script), lemmas})` with `d' = d`
   → first enable `lemmas` (§1 run lemmas): certified and replayed in
   `ctxt0`, the thms added to BOTH `ctxt0` — giving `ctxt1`, the ctxt the
   call returns — and the guard-side ctxt `ctxt` the call received — giving
   `ctxt_g`, the ctxt the replay runs in; a lemma that fails to certify or
   replay → raise `Guard_Record_Stale`.  The replay runs in `ctxt_g`, not
   `ctxt1`, because the verdict was earned there: the recording run's
   P-auto ran on `p_auto_search_tac ctxt` (`reasoners.ML:1590-1591`), and
   that `ctxt` carries `Guess_Instantiate.add_guess_inst_looper` (`:1801`)
   over `add_guess_inst_solver … addsimps Premise_def` (`:1829`), installed
   nowhere else since 2026-08-29 (`guess_instantiate.ML:305-311`);
   `Guard_Simp_SS.enhance` restores neither, so a `Proved` slot whose proof
   needed a guessed instantiation would never replay from `ctxt1` [drafter,
   tenth review].  Then replay `script`.  `script = "\<phi>guard_P_auto"` →
   run `p_auto_body ctxt_g` — the BODY, so that the method's own bound is
   not nested inside the replay bound [drafter, eighth review] — under
   `Time.max (tolerant_time t, \<phi>guard_classic_prover_timeout)` read
   from `ctxt_g` (`Time.max`, `Pure/General/time.ML:24`), `tolerant_time t =
   1.5t + 1 s` (`cache_file.ML:875-876`) [floor: author 2026-09-02 13:01;
   summand and `tolerant_time`: 2026-09-03 02:10, 13:03; two arms kept and
   the floor read from the option, never a literal: 2026-09-07 13:16 "我建
   议就两条臂, 但 … 不要写死 400ms 还是读那个 \<phi>guard_classic_prover_timeout"].
   Under the default option the floor is inactive (`tolerant_time`'s 1 s
   summand already exceeds 400 ms); it matters only once §10 step (5)
   raises the option above 1 s, and is kept so as not to rely on that
   coincidence.  Any other `script` → `eval_prf_str` under `tolerant_time
   t`, `n = Thm.nprems_of thm`, keywords `Keyword.no_major_keywords
   (Thy_Header.get_keywords' ctxt_g)`, in `Guard_Simp_SS.enhance ctxt_g`;
   on success the returned `(ctxt', thm')` gives `thm'` and `ctxt'` is
   discarded (the enhanced ctxt is the replay's own).  Replay succeeded →
   return `Seq.single (ctxt1, solved)`.  Replay failed → raise
   `Guard_Record_Stale` [author 2026-09-03 15:46, 16:01]: "failed" is
   `Timeout.TIMEOUT` or an exhausted sequence on the P-auto arm, and
   `Phi_Sledgehammer_Solver.Auto_Fail _` on the `eval_prf_str` arm (how it
   reports timeout, an unsolved goal, a failed method and an unparsable
   script alike, `sledgehammer_solver.ML:610-631`).  Catch exactly those
   with an explicit `handle` — never a catch-all and never
   `Exn.capture_body` (it captures interrupts too,
   `Pure/Concurrent/isabelle_thread.ML:162-164`); the interrupt family
   passes untouched on both arms: on the P-auto arm `Timeout.apply`
   releases a non-proper exception unchanged
   (`Pure/Concurrent/timeout.ML:49-56`), on the `eval_prf_str` arm
   `eval_prf_str0`'s catch-all re-raises an exception in which
   `Interrupt_Family.contains_interrupt` finds an interrupt (a `Par_Exn`
   wrapping one) instead of relabelling it `Auto_Fail (Unknown …)` — the
   one-clause change of §9 [drafter, eighth and ninth reviews; the clause:
   author 2026-09-08 02:37].
3. Slot `i` absent, or `d' <> d` → raise `Guard_Record_Stale`.

**Without a record** (`NONE`) — the verdict written at once [author
2026-09-04 03:04, 03:23]:

4. P-auto.  Proves → `entries := Inttab.update (i, (d, Proved {proof =
   (elapsed, "\<phi>guard_P_auto"), lemmas = []}))`, `elapsed` measured
   around the `Seq.pull` of the P-auto sequence (`timed_tac` only builds a
   `Seq.make`, `reasoners.ML:926-931`) and normalised through
   `standard_time` (`cache_file.ML:855`) [author 2026-09-03 12:52; where
   the bracket goes: drafter]; return `Seq.single (ctxt0, solved)`.
5. Else, if `!judge = NONE` — the quickcut path: `entries := Inttab.update
   (i, (d, Unprovable {refuter = "quickcut"}))`; spawn the refutation
   future (§6); return `Seq.empty` at once [author 2026-09-04 04:16; 04:26;
   2026-09-07 15:10].  The run's thread never learns what the future found.
6. Else (`!judge = SOME j`) R-conv (§1), inline.  Refutes → `entries :=
   Inttab.update (i, (d, Unprovable {refuter = "R-conv"}))`; return
   `Seq.empty`, silently.
7. Else R-nitpick (§1), inline.  Refutes → likewise with `"R-nitpick"`.
8. Else `j {ctxt, outer_ctxt = ctxt0, can_inst, thm}`.  `Provable {lemmas,
   proof, thm = solved}` → enable `lemmas` into `ctxt0`, giving `ctxt1` (a
   lemma that fails → `error`, §1 run lemmas); `entries := Inttab.update
   (i, (d, Proved {proof, lemmas}))` with `standard_time` applied to
   `proof`'s time and to each lemma's time here, the one write point;
   return `Seq.single (ctxt1, solved)`, no check on `solved` [author
   2026-09-04 03:15].  `Unprovable` →
   `Unprovable {refuter = "judge"}`; return `Seq.empty`, silently — the
   judge decided, no warning [author 2026-09-04 03:04].

The `Int.max (1, …)` clamp of today's budget (`reasoners.ML:1617-1618`)
stays on every `Timeout.apply` here: a bound below 1 ms installs no timer
at all (`Pure/Concurrent/timeout.ML:26, 33-34`).  Any exception escaping
P-auto, an inline refuter, lemma enabling or the judge propagates out of
`prove_or_refute` unchanged and becomes the run's own exception (§4 step
3/4) [author 2026-09-03 12:31; 2026-09-04 03:04]; an exception inside the
refutation future is printed there (§1).  Two calls in one run that meet
the same guard occupy two slots and are decided twice: the slot, not the
guard, is the identity [author 2026-09-03 07:54].

## 6. The refuters and the judge

There is no registry and no priority.  Three plain functions, each
bounding itself, in a fixed order — R-conv, R-nitpick, the judge:

| step | what | its own bound |
|---|---|---|
| R-conv | today's `r_conv_racer` body: negate each subgoal, search with `auto_search_tac` in a `Guard_Simp_SS`-enhanced ctxt, with both of its `can_inst` branches as today — the `can_inst = false` one exporting through `outer_ctxt` (`reasoners.ML:1303-1312`, `:1329-1360`) | `Timeout.apply \<phi>guard_classic_prover_timeout`; `TIMEOUT` → not refuted [author 2026-09-04 03:23] |
| R-nitpick | today's screen and Nitpick calls (`reasoners.ML:1656-1675`), subgoals one after another, each Nitpick call with its 2000 ms parameter as today; a `genuine` or `quasi_genuine` answer refutes (`guard_refute.ML:280-281`); R-nitpick's own preprocessing simpset `Nitpick_Refute_SS` | one outer `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms × length goals`, and inside it one `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms` per subgoal — a subgoal's `TIMEOUT` moves to the next, the outer `TIMEOUT` ends R-nitpick; either way → not refuted [author 2026-09-03 13:05; inner bound 2026-09-07 13:00; sequential: drafter] |
| the judge | `!judge`, if `SOME` (§1) | its own |

Where they run depends on the judge:

- **A judge is installed**: R-conv and R-nitpick run inline on the run's
  thread before the judge (§5 steps 6–8).  No warning exists on this
  path: the judge's answer is final.
- **No judge**: `prove_or_refute` has already answered `Unprovable`
  (`"quickcut"`, §5 step 5).  The refutation future (§1) runs R-conv, then
  R-nitpick, then — if neither refuted — the undecided-guard warning, on
  its own worker thread; the position it prints under is the spawning
  command's.  It records nothing: the slot is complete.

The undecided-guard warning therefore has ONE call site, inside the
refutation future.  On the run's thread no `Position` juggling is needed.

## 7. Rules

Stated of one run (§1).

- **R1 recording** [author 2026-09-02 12:03]: in a run without a record,
  every completed `prove_or_refute` call writes its slot before returning.
  At the end of such a run whose table is non-empty, the topmost
  invocation writes the WHOLE table as the record, if `\<phi>guard_cache`
  is true (never a delta — the store is last-write-wins) [author
  2026-09-02 07:11; empty table exempt 2026-09-03 08:04; always, with or
  without a judge, 2026-09-04 03:23].  A
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
  countermodel rests on a changed definition; a `"quickcut"` slot for a
  guard a new simp lemma would now prove) is reproduced faithfully
  forever, and silently: the undecided-guard warning is printed once, by
  the recording run's refutation future, and never on a hit [author
  2026-09-07 12:58].
- A `"quickcut"` slot says nothing about whether R-conv or R-nitpick
  refuted the guard; that is known only to the future, which prints the
  warning or stays silent and records nothing.  Refuter distribution is
  therefore measured from the future's `guard_decision` line (§10), not
  from the record.
- Load can permanently demote a guard.  A run without a record that misses
  the P-auto budget under load records `Unprovable` (`"quickcut"` /
  `"R-conv"` / `"R-nitpick"` / `"judge"`), and R3 structurally cannot fire
  on it.  Likewise a guard R-conv or R-nitpick refutes — including on a
  `quasi_genuine` answer, which `reasoners.ML:1494-1503` records can be
  wrong — is cached `Unprovable` and, by R4, is never shown to the judge.
  A record does not protect against this: one replay that overruns
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
  cache-free run would have succeeded (the step limit, `reasoner.ML:789-793`;
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
  run for that guard until the judge's script and the replay agree.  The
  same holds for a returned `thm` that is not solved (§1 the judge): the
  slot is `Proved`, the run fails at that reasoner, and the next run's
  replay decides.
- A `Proved` slot whose replay SUCCEEDS with a different instantiation
  (`can_inst = true` leaves the guard's conclusion variables schematic)
  leaves a different sequent; every later slot's digest differs,
  `Guard_Record_Stale` fires at the first such slot — attributed to that
  slot, not to slot `i` — and the run repeats without the cache, once per
  run until the two instantiations agree.  No digest of the solved state
  is stored to catch it at slot `i` [author 2026-09-08 02:02 "大多数时候
  inst 是一样的. 我觉得不用了"; tenth review relaxation 1 not adopted].
- Run lemmas that reach later statements make their records depend on the
  earlier statement's judge: if that statement's record goes stale and its
  re-run obtains different lemmas from the judge, the ctxt flowing into
  the following statements changes, their guard digests change, and their
  records go stale in turn — one cascade of no-cache runs.  Inherent in
  [author 2026-09-07 12:34]; recorded, not prevented.
- Deleting `Race.race` deletes its crash absorption: today an exception
  in P-auto or a refuter is that racer's `Crashed` exit; now, with a judge
  installed, it is the run's exception (two known instances: the
  undiagnosed `Option` exception; `nitpick_params` holding a bad value).
  Without a judge the refuters run in the refutation future and their
  exceptions are printed, not raised.  §10 step (5) counts hard failures
  attributable to guard-side exceptions.
- The warning of a run without a record arrives after that command's
  sequent output, not before, and only where `\<phi>trace_reasoning >= 1`
  (§1); in PIDE, editing the command while the future runs cancels it and
  the warning is never printed; under Isa-REPL (§10 step 5's harness) the
  spawning thread is not a Future worker, so a REPL command's timeout or
  interrupt does not reach the refutation futures it spawned (§1).
- A run that ends inside a forked proof ends after `Theory.at_end` has run
  (`Pure/theory.ML:207` → `Isar/toplevel.ML:306` → `Thy/thy_info.ML:332`;
  forked proofs join at `:342`): its write is compacted only by the next
  build and leaves an `openning_stores` entry for the process's lifetime.
  Whether it happens depends on `parallel_proofs`; §10 step (5) measures
  it (`<thy>.guard-cache` size, frame count, process RSS).  The guard's
  write is deliberately not registered as an async task.
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
  cache", "cached guard verdicts"), switch = \<phi>guard_cache}` — in
  `library/guard_cache.ML` (§4), where `\<phi>guard_cache` and the record
  codec are also declared (`RPC_Pretty` is not visible from
  Auto_Sledgehammer, `Auto_Sledgehammer.thy:2`; it reaches PLPR via
  `PLPR_error_msg.thy:7` → `Minilang_AoA.thy:2`).  Every
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
  In the shared `at_end` only the `compact_store` call is gated by `if
  File.is_file (store_path thy)`; the branch that waits for registered
  async tasks before compacting (`cache_file.ML:830-851`) stays — otherwise
  every theory in the build gets a `<thy>.guard-cache.lock` created by
  `with_file_lock`'s `Posix.FileSys.createf` (`:394-396`) plus a
  writability probe at its end; measured today as 85 `*.proof-store.lock`
  files against 38 `*.proof-store` files in `contrib/phi-system` [drafter,
  seventh review U14 / eighth and ninth reviews].  The dead `bool` in
  `openning_stores`'s value triple (`:632`; six writers, no readers) is
  dropped in the same pass.
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
- **Record value**: `{final : digest, entries : (int * digest * verdict)
  list}` (written from `Inttab.dest`, ascending; a `Proved` entry carries
  its `lemmas`) packed with the mlmsgpack packers through a `BytesIO`
  outstream and taken as a string (`encode_record`'s shape,
  `cache_file.ML:94-99`) [author 2026-09-03 05:42; lemmas per slot
  2026-09-04 04:19].  Digests through `packWord64` / `unpackWord64` [author
  2026-09-03 07:58]; a `proof_cache`'s `Time.time` as `packInt
  (Time.toMilliseconds t)` / `Time.fromMilliseconds`, the store's own
  convention (`:277-279`, `:271-273`); `verdict` tagged by an int like
  `PUT`/`TOMB` [author 2026-09-03 13:19]; a lemma's `term` through
  `RPC_Pretty.pack_raw_term` / `unpack_raw_term`
  (`Isabelle_RPC/Tools/pretty.ML:323-366`, the constructor-tagged structural
  codec) made available on `BytesIO` by turning that codec into a functor
  over the `MessagePack` result signature (`mlmsgpack.sml:1`): that
  signature is named `MESSAGE_PACK` by extracting `mlmsgpack.sml:8-106`
  with `type instream` / `type outstream` of its own in place of the
  `S.`-qualified occurrences (`:11`, `:60`, `:62`, `:64`), and the functor's
  ascription at `:8` becomes `:> MESSAGE_PACK where type instream =
  S.instream and type outstream = S.outstream`, so `Pack.packer` /
  `Unpack.unpacker` stay transparent for the existing instantiations at
  `:1002-1004`, which are untouched; then instantiating the term-codec
  functor twice; the `MessagePackBinIO` instance keeps `RPC_Pretty`'s
  names.  The functor stays in `Isabelle_RPC` for now
  and moves to `Performant_Isabelle_ML` after this plan [author 2026-09-03
  13:19; 13:27; 14:19].  Kept over Pure's `Term_XML.Encode.term_raw` +
  YXML (ninth review relaxation 2) [author 2026-09-07 13:15 "否决. 那个性能
  很慢的"]; measured 2026-09-07 on `Phi_System_Base` (5000 theorem
  propositions; the 500 largest): msgpack encodes 1.6–2.3× faster and in
  half the bytes; its decode through today's `BinIO.StreamIO` lazy instream
  measured slower, which the `BytesIO` instance removes (`ai-artifacts/
  Term_Codec_Bench.thy`).  NO format version [author 2026-09-03 03:02]: the decode is
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
consumers (§1); the guard-cache export hook; the `Nitpick_Refute_SS`
rename; the judge ref (default `NONE`) and its types; the whole lemma path
(slot lemmas in the record, enabling at the slot, the export) exercised by
§10 step (3)'s injected table — phase 1 has no producer, and everything
must be ready before the LLM judge [author 2026-09-07 13:15 "在做 LLM judge
前一切都要就绪"; ninth review relaxation 1 vetoed].  Phase 1 adds exactly
ONE change outside PLPR — the exception to [author 2026-09-03 12:59–13:01]:
in `eval_prf_str0`'s catch-all clause (`sledgehammer_solver.ML:629-631`),
`| err => if Interrupt_Family.contains_interrupt err then Exn.reraise err
else <today's body>`, so that a `Par_Exn` wrapping an interrupt is no
longer relabelled `Auto_Fail (Unknown …)`; every `eval_prf_str` caller
(the proof store's replay, AoA) thereby propagates such an interrupt
instead of starting a fresh search on it [author 2026-09-08 02:37 "我认为这
挺好的, 为什么不采纳呢?"; tenth review relaxation 4].  The store-side work
is §8's, at §10 step (4).  Phase 2 is the LLM judge: a function of
`judge_arg -> judgement` installed into the ref, answering `Provable` with
lemmas, a script and the proven goal state, or `Unprovable` [author
2026-09-02 07:39; 2026-09-04 03:04–03:15], under the contract of §1.
Installing a judge requires deleting every existing `<thy>.guard-cache`
first: records written without a judge hold `"quickcut"` slots, which §5
step 1 answers without ever consulting one [author 2026-09-08 02:02 "反
对. 别采纳" on discarding such records at installation; tenth review
relaxation 2 not adopted].

## 10. Configuration, drafter decisions, implementation order

| option | default |
|---|---|
| `\<phi>guard_classic_prover_timeout` | 400 ms, provisional — P-auto's and R-conv's budget, and the floor of a P-auto replay [author 2026-09-04 03:23 "直接重命名为 \<phi>guard_classic_prover_timeout"; replaces `\<phi>guard_prove_timeout` and `\<phi>guard_rconv_timeout`] |
| `\<phi>guard_refute_timeout` | 2000 ms (Nitpick's parameter; R-nitpick's outer net is `\<phi>guard_refute_timeout + 5000 ms × length goals`, and each subgoal inside it is bounded by `\<phi>guard_refute_timeout + 5000 ms`) |
| `\<phi>guard_cache` | true |
| `\<phi>log_guard_race` → `\<phi>log_guard_decision` | false (renamed) |

Names approved [author 2026-09-03 04:58, 11:11, 11:15; 2026-09-04 03:23;
`"quickcut"`, `use_cache` 2026-09-07 15:01, 15:10]; ML identifiers not
named by the author are the drafter's under the 11:24 delegation (among
them the judge ref's name and module, `Guard_Record_Stale`, `gen_reason_i`,
`guard_cache.ML`).

Nothing is pending the author.

**Drafter decisions that change behavior**, each vetoable: U22 (one env
per `gen_reason_i` invocation via a decision ref — §4); U20 (the
end-of-run steps sit outside `gen_reason_i`'s `handle Success` — §4); the
installation order (§4); the file `guard_cache.ML` and what it holds (§4);
the shape of the ctxt threading through the factory — `oblg_template`
polymorphic through `inj` and `on_thm`, bypass exits paired with `ctxt0`,
`head_only` and `SOLVED'` on the thm half (§1); the replay of a `Proved`
slot in the guard-side ctxt plus the slot's lemmas, `ctxt_g` (§5 step 2);
the export hook's priority and its overwrite of the proof-context-level
half only (§1);
`p_auto_body` named apart from its bound, so a replay bounds the body (§1,
§5); the exact exceptions a replay converts into `Guard_Record_Stale` (§5
step 2); `elapsed` measured around the `Seq.pull` (§5 step 4); a lemma
that fails to enable in the run that consulted the judge being an `error`
(§1 run lemmas); lemmas enabled AFTER the slot's digest is taken (§5);
U3 (the factory parameter's type — §1); the sequential order of
R-nitpick's subgoals inside its net (§6); `Time.zeroTime` / `hash = NONE`
in the record write (§8); the `eval_prf_str` replay as a `Guard_Simp_SS`
consumer (§1); the catch-all decode (§8); the store functor's argument
list and the narrowed guard signature (§8); the `at_end` gate on
`compact_store` only (§8); `Hasher.goal` as the exported spelling of both
digests (§1); the `guard_decision` record's fields, and that it is a
permanent record rather than temporary measurement code (below); the
refutation future's own `guard_decision` line (below).

Instrumentation is temporary measurement code [author 2026-09-03 04:01].
One record is permanent: `guard_decision` (verdict token, refuter, replay
field, elapsed, `Hasher.hex` of the guard digest, call index, n_goals),
behind `\<phi>log_guard_decision`, written by `prove_or_refute` — and,
for the quickcut path, a second line by the refutation future when it
ends (which refuter refuted, or "undecided", and its elapsed time), the
only place the future's outcome is observable [drafter].  `Hasher.hex`
appears in exactly those lines of the permanent code.

Order:

0. Re-verify every line anchor individually — §1's and §3's included, the
   `Phi_System` caller list among them (`reasoner.ML` and `PLPR.thy` moved
   with the stateful-PLPR commits of 2026-09-05/06); the tracing gate.
1. `Hasher.terms : term list -> digest` in `HASHER` and
   `contrib/auto_sledgehammer/library/Hasher.ML` (the `hash_term`
   accumulator chained from the FNV basis over the list); the one clause in
   `eval_prf_str0` (§9); `library/guard_cache.ML` (`verdict`,
   `Guard_Record_Stale`, `Guard_Simp_SS` with its attribute, the export
   hook, `\<phi>guard_cache`, the `env` type and its cell — the store
   instance and the codec wait for step 4); the factory:
   `guard_condition_solver` parameterised, `oblg_template` with `inj` and
   `on_thm` and its three other callers; `try_prove_or_give_up`;
   `p_auto_body` and `\<phi>guard_P_auto`'s `method_setup`; the
   `Guard_Simp_SS` `enhance` sites; the `Nitpick_Refute_SS` rename;
   `guard_condition_solver'`/`1` on P-auto; the `fastforce` instance for
   `defer_premise`; the undecided-guard warning as a function; the
   obsolete comment at `reasoners.ML:1415-1421` rewritten.
2. `prove_or_refute` over `context_state`: P-auto → (no judge: the
   quickcut answer and the refutation future | judge: R-conv → R-nitpick →
   the judge ref), with no table (every call takes the without-a-record
   path and writes nothing); `guard_condition_judge` registered on the
   state; migrate every caller (§3) and `Test/Guard_Race_Smoke.thy` (its
   assertions become `guard_decision`'s, driven through the installation
   function of step 3 once that exists); `guard_decision`, and with the
   rename of its switch the clause `\<phi>log_guard_race = true` is
   DELETED from `PLPR.thy:1965` (`\<phi>log_guess_inst = true` on that line
   is another subsystem and stays), so `\<phi>log_guard_decision` keeps its
   default `false`; step 5's harness enables it itself.
3. The env and the in-memory table: `gen_reason_i use_cache`,
   installation, the call index, both paths of §5 (the record-side path
   fed from a table injected by the test: hits, the two replays, slot
   lemmas enabled at a hit and exported by the hook to the following
   statement, `Guard_Record_Stale`), the end-of-run steps with the no-cache
   re-run, R4.
4. Persistence, gated: proceeds only if step (3)'s temporary
   instrumentation shows record keys repeating across two consecutive
   corpus runs AND the final digest of a repeated key reproducing.  Then:
   the store functor and `Phi_Guard_Store`, the raw-term codec functor and
   its `BytesIO` instance, the gitignore entries, the record read at
   installation (`previous_final`, `entries`), R1's write, R2, R3.
5. Corpus acceptance: a cache-on and a cache-off leg, a concurrent Isa-REPL
   leg, a consecutive-run leg with a hit-rate floor; measure wall time,
   verdict flips per call index cache-on vs cache-off, first-call latency
   at the direct call sites, refuter distribution (from the future's
   line), `Guard_Record_Stale` / R2 / R3 fire counts, hard failures
   attributable to guard-side exceptions, digest cost, store I/O, the
   forked-proof write (§7), the guard-cache export hook's cost per run
   boundary; re-measure 400 ms.  Testing via Isa-REPL against
   `Phi_System_Base` sources — never `isabelle build` (so nothing here
   observes `Session.finish`; §1's 2026-09-04 measurement stands for
   that).

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
   judge** [03:04] — "inline" now holds with a judge installed; without
   one they run in the refutation future (§15.2), the single asynchronous
   piece left.  Eighth-review U-INTERRUPT, U-CRASH-CLASSIFY,
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
6. **`"default"` → `"assum"`, still warning on a hit** [03:23] —
   superseded by §15.2: without a judge the slot is `"quickcut"` and a hit
   is silent; `"assum"` is never written.
7. **`Refuted` → `Unprovable`** everywhere [03:23].

Eighth-review drafter fixes applied: U-REPLAY-BOUND (`p_auto_body`),
U-REPLAY-IFACE (`Auto_Fail` / `TIMEOUT` → `Guard_Record_Stale`, no
catch-all), U-LEMMA-CTXT (superseded in rev 12: lemmas enter at their
slot), U-SWITCH-WRITE (the write gated by the switch; the store gates
nothing), U-INSTALL-ORDER, U-ELAPSED, U-DEMOTION-HONESTY,
U-UNWRITABLE-HONESTY, U-AT-END, U-TIME-CODEC, U-ANCHORS (the judge's claim
that `Time.max` does not exist is wrong — `Pure/General/time.ML:24` — and
is not applied), U-WARNING-SITES, U-INSTANTIATION-SITE.

## 15. Ninth-review and lemma-binding rulings (2026-09-04 04:16–04:35; 2026-09-07 12:34–15:10)

The ninth review (`wf_427edb4a-4a8`, scoped to §4/§5/§6/§8): NOT_READY,
26 upheld (2 structural), 3 relaxation proposals, 14 discarded; every code
claim verified true.  Rulings:

1. **Run lemmas bound to the slot; `prove_or_refute` over
   `context_state`; the ctxt flows to `gen_reason'`'s return and on to
   the following statements** [2026-09-04 04:19 "我们要把 lemmas 记录绑定到
   the goal 上. 在某个 goal 上给的 lemmas 只在证明那个 goal 上启用, 但启用后
   … 我们要把 prove_or_refute 的类型改成 context_state -> context_state,
   我们要改 context, 且要一路改下去一直到 gen_reason' 的返回"; 2026-09-07
   12:34 "启用进 ctxt 的 lemma 要流到后续语句 / 是的, Guard_Simp_SS"].
   Dissolves the structural finding LEMMA-DIGEST (records with lemmas
   self-invalidating) and spawned the stateful PLPR reasoning, now in
   place.  The record's `lemmas` field and §4 installation step 4 are gone.
2. **The quickcut path** [2026-09-04 04:16 "在 the judge not given 时 …
   先返回 unprovable 并启动一个 future work 去跑 R-conv, R-nitpck 以及最后的
   warning"; 04:26 "建议给槽一个特殊的名字, 比如 `bypass` or `quickcut`";
   2026-09-07 15:10 "赞同 quickcut / 赞同 Future.fork"].  A hit is silent:
   no refuter, no warning [2026-09-07 12:58 "赞同 (a) 反对 (b) 不要再跑反驳
   或警告"].  The future's handler [12:34 "建议在这个 future 中加个大 handler
   捕获所有非 interrupt 异常然后 error 报告"].  `"assum"` is retired (§1).
3. **R-nitpick: an inner bound per subgoal inside the net** [2026-09-07
   13:00 "3. 采纳"].
4. **Record key stays `Hasher.compact`** [13:09 "我坚持用 compact"]; the
   in-process-only comment on `Hasher.compact` was deleted from
   `Hasher.ML` on the author's order [13:05 "删掉这个瞎写的契约. 现在就删"].
   Relaxation `Hasher.hex` not adopted.
5. **Relaxation 1 (phase-1 records without lemmas) vetoed** [13:15 "否决.
   在做 LLM judge 前一切都要就绪"].
6. **Relaxation 2 (`Term_XML` + YXML for lemma terms) vetoed** [13:15 "否
   决. 那个性能很慢的"]; measurement in §8.
7. **Relaxation 3 (one replay arm) vetoed; two arms; the replay floor read
   from `\<phi>guard_classic_prover_timeout`, never a literal** [13:16].
8. **No env-cell blanking for the judge; a contract instead: the judge
   must not re-enter PLPR, and — on the drafter's insistence, allowed —
   neither may its proof texts** [13:21 "不用做. 相反, 定一条规约, judge 不能
   重入 PLPR"; 13:24 "不可能发生的. 如果你偏执, 你可以写到规约里"].
   Finding F1-ENV-VISIBLE dissolved.
9. **The no-cache re-run passes `use_cache = false` to an internal
   function** [15:01 "我赞同你的方案. 把 use_cache : bool 作为参数给进去"];
   it gates the read only, the re-run still writes.  Finding
   RERUN-LEAF-BY-SIDE-EFFECT dissolved.
10. `Phi_System_Base` rebuilt on the author's order for the codec
    measurement [13:23 "批准重建 Phi_System_Base"].

Ninth-review drafter fixes applied: P1-ORDERING (`guard_cache.ML` before
`reasoner.ML`), the `Goal.conclude` sentence corrected (§1 the judge), the
judge's obligations and re-entrancy (§1), `judgement`/`verdict` in two
structures (§1), the switch read once before the record read (§4), the
`Int.max (1, …)` clamp (§5), explicit `handle` instead of
`Exn.capture_body` (§5), `genuine`/`quasi_genuine` (§6), R1's write gated
by the switch spelled out (§7), the honesty bullets on `Race.race`'s crash
absorption, the unsolved judge state, the forked-proof write and the
lemma cascade (§7), the `at_end` gate narrowed to `compact_store` (§8),
the `Guard_Simp_SS` exclusion reason (§1), the empty-sequence note (§4),
the installation function's callers (§4), the smoke test's new shape
(§10), `guard_decision` as a permanent record (§10), the record-key
stability sentence corrected (§1), the final digest's conclusion (§1).
Discarded, with the review: a `Thm.no_prems` check on the judge's state
(03:15), restoring `Race.race`'s crash absorption (12:23–12:36), keying
records on `Hasher.all_goals`, dropping unreplayable lemmas instead of
re-running (16:55), `record_key option` in the env (16:00), removing
`Time.max`, reordering installation.

## 16. Tenth-review rulings (2026-09-08, 02:02–02:43)

The tenth review (`wf_4044f0e2-769`, scoped to §1/§4/§5/§6/§8): NOT_READY,
24 upheld (0 blockers — both collapsed as misreadings of `Simpset`'s
`add_simps`/`del_simps`; 2 majors; 22 one-sentence fixes), 4 relaxation
proposals, 16 discarded, 4 dirty hacks; every code claim re-verified by
the drafter.  Rulings:

1. **No digest of the solved state in `Proved`** (relaxation 1) [02:02
   "我觉得不是很重要. 大多数时候 inst 是一样的. 我觉得不用了"]; §7 records
   the mis-attributed miss instead.
2. **No discarding of `"quickcut"` records when a judge is installed**
   (relaxation 2) [02:02 "反对. 别采纳. 这个问题我甚至之前回答过"]; §9 says
   to delete the files first.
3. **R-nitpick's subgoals stay sequential** (relaxation 3) [02:02 "别采纳"].
4. **The one clause in `eval_prf_str0` is adopted** (relaxation 4) [02:37
   "我认为这挺好的, 为什么不采纳呢?"] — the single phase-1 change outside
   PLPR (§9); §5's "the interrupt family passes untouched" holds on both
   replay arms.
5. Reviews are to rebut hard [02:43 "评审时候一定要严厉驳斥"].

Tenth-review drafter fixes applied: REPLAY-CTXT-WEAKER-THAN-RECORDING
(the replay in `ctxt_g`, §5 step 2), FACTORY-CONTRACT-INCOMPLETE
(`oblg_template` with `inj`/`on_thm`, the bypass exits, the three other
callers — §1, §3), LOG-SWITCH-FORCED-ON (`PLPR.thy:1965`, §10 step 2),
HASHER-TERMS-WRONG-FILE (§4, §10 step 1), the `Simpset` slots and the
hook's write operation (§1), `export_aux_lemma`'s three outcomes (§1),
`wrap` vs `o snd` (§1), the `is_guard_mode` and `Phi_System` anchors (§1,
§3, §10 step 0), the judge's raw times normalised at the write point (§1,
§5 step 8), the interrupt sentence made true arm by arm (§5), the
`"quickcut"` records outliving judge installation (§9), the divergent
successful replay (§7), the protocol stages scoped to a call without a
record (§1), the warning's trace gate (§1, §7), the child-group property's
scope and the `consolidated` sentence (§1, §7), `can_inst` in the future's
capture list and R-conv's two branches (§1, §6), `Session.finish` dropped
from step 5 (§10), the lemma replay seam (§1), the `MESSAGE_PACK`
signature extraction (§8), `Hasher.hex` "of the permanent code" (§10), the
`pointer_eq` short-circuit (§4), the refuted guard never reaching the
judge (§7), the R-nitpick net stated once (§10).  Discarded, with the
review: `put_simps` widening the shared `SIMPSET` signature; the
hook-overwrite "impossible" claim; the hook-cost arithmetic; moving the
judge ahead of the refuters (re-litigation of 03:04); gating the fork on
the log switches; the `cache_file.ML:149` / `Hasher.ML:244` "corrections"
(the plan was right); `Goal.init` for the lemma seam.
