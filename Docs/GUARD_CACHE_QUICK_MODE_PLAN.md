# PLPR Guard Cache — prove_or_refute rework

Status: rev 28 (2026-09-15) — **THE QUICKSORT REGRESSION DIAGNOSED AND
RULED, implemented, verified, reviewed three times — the first review
MET_ON_CONDITION (MD1 → ruling 8, D1–D12 applied, P1/P2 → rulings 9 and
10), the re-review MET_ON_CONDITION (nine text conditions, applied), the
final round MET_ON_CONDITION (seven text conditions, applied) — ready to
commit** (§39): P-auto no longer simplifies; the
guard-side simplification is `guard_simp_tac`, run by the solving
functions that simplify — in `prove_or_refute` on the context that carries
the entry's delta and again, from the state the call was given, after the
judge's delta; once in `p_auto_solving` — under 60 s of thread CPU (from
5 s: the Quicksort guards' simplification measured at 7–13 s); the `is_F`
shortcut is deleted.  Before that: the
preparatory phase, steps 0–2 (§26–§32), step 3's first
half (§34) and step 4 (§35, redone on the author's design) are done; the
entry became a delta and the canonical form was withdrawn (§36); the
provenance audit's items were gone through one by one and ruled (§37);
step 5's legs ran on Isa-REPL (§38: the floors met; two observations
outside the guard cache, both ruled; its acceptance is still pending).  The
revision history below (rev 18–24) narrates the canonical form as it
stood then; it no longer exists.
Rev 22 was **READY** by the nineteenth review (rev 21:
two one-sentence fixes, no blocker, no major; §25), applied there.  Rev
21 folded in the eighteenth review (rev 20: NOT_READY,
one major — the canonical form's `Variable.exportT ctxt0 ctxt0`
generalised the type variables `ctxt0` does not declare, but the
boundary's export generalises those the OUTER ctxt does not declare, a
superset, since declaration only grows inward; and four one-sentence
fixes) is folded in (§24): the canonical form now over-generalises —
every type variable of the proposition that occurs in no hyp becomes
schematic — which is a fixed point of any later `Thm.generalize`
whatever ctxt replayed the lemma.  Rev 20 folded in the seventeenth
review (rev 19: NOT_READY,
three majors — the export's TYPE-variable generalisation still escaped
the canonical form, so a lemma carrying an undeclared type variable
regrew the list by one copy per boundary; §5 step 6 could install a
judge lemma at another entry's tier and then blame the judge; the judge
contract never said in WHICH `ctxt0` a method text must replay, though
the digest excludes the ctxt by ruling — and five one-sentence fixes) is
folded in (§23): the canonical form gained type generalisation (rev 20's
shape, `Variable.exportT ctxt0 ctxt0`, superseded by rev 21's), on
`Provable` the lemma list becomes exactly the judge's list, and a method
text may cite theory-level facts only.  Rev 19 folded in the sixteenth
review (rev 18: NOT_READY,
one major — `Proof_Context.export` hhf-normalises and `Variable.gen_all`s
every theorem it carries, so a lemma stated with an outer `⋀` came back
`aconv`-distinct from its next replay and the lemma list's one-entry-per-
statement invariant broke at every boundary; and seven one-sentence
fixes) is folded in (§22): §5 step 1 now appends and compares a canonical
form closed under the export.  Every `reasoners.ML` anchor is re-taken
after commit `8c26c3b4` (2026-09-08 15:01 UTC, the `exception Option` hunt
instrumentation removed: −199 lines from `:943` on), which also deleted
the `option_hunt` probe whose label named the "G.simpcut" pass.  Rev 18
folded in the fifteenth review (rev 17: NOT_READY, one blocker — step P
deleted Isa-Mini's copy of the raw-term codec in favour of `RPC_Pretty`'s
monomorphic one while the functor that could replace it was scheduled at
step 4; and eight one-sentence fixes; §21): the `MESSAGE_PACK`
extraction, the term-codec functor and its `BytesIO` instance moved from
step 4 into the preparatory phase, since `mlmsgpack.sml` lives in the
same root heap `ssymb.ML` moves into.
Rev 17 folded in the fourteenth review (rev 16: NOT_READY, three majors —
the digest's third cause of key movement named the wrong mechanism for
the `can_inst = true` reasoner (the schematic INDEX, not the import's
fresh names); the judge's raw times were fed to `replay_limits`, which
expects standard-machine times; a lemma's term was persisted through a
codec with no runtime-symbol clause, against `SSymb.thy`'s invariant —
and five one-sentence fixes) together with the author's rulings of
2026-09-08 15:00–15:12 (§20): a
**preparatory phase** moves `Phi_Tool_Symbol`'s ML to the Pure half of
`Performant_Isabelle_ML` and gives `RPC_Pretty`'s raw-term codec its
symbol clause, so the codec functor stays parameterised by `MESSAGE_PACK`
alone; and the schematic index is NOT normalised either — the whole of
PLPR is deterministic, so the index is.  The rulings of §19 stand: the
"G.simpcut" pass has a wall-clock bound, and the digest is not normalised
against the names `oblg_template`'s import invents.  The lemma budget
(§18) stands: every lemma becomes conditional rewrite rules
`… ⟹ Guard_Budget \<r>BUDGET<i> ⟹ lhs ≡ rhs` — extracted by `mksimps`
FIRST, the budget premise added LAST — and one context-local simproc
discharges the premise while counting; nothing global is touched and
`Simplifier_Trace` is untouched; the guard digest is taken after the case
split and before the aux facts are inserted.  The design itself is that of
rev 14 [author 2026-09-08 05:36–08:45, §17]: **the cache stores advice,
never a verdict.**  Every `prove_or_refute` call decides its guard itself,
by P-auto, on every run; the store keeps, per guard, the lemmas the judge
once proposed and whether the guard was last found `Proved`, `Refuted` or
`Unknown` — advice that makes P-auto stronger or lets a warning be skipped,
never a decision taken on trust.  A wrong entry costs at most one P-auto
budget or one spurious warning, so nothing needs validating: no run-level
state, no digest of the reasoning path, no tombstones, no re-runs, no
`Guard_Record_Stale`, no notion of a run failing [author 05:36 "但我意识到一
个问题是. 在没有 judge 的情况下, 一旦一个 refutation 被错误的进入 cache 中, 即
便之后增强了 Guard SS 后也无法纠正这个错误了 … 或者我们要不这样修改设计: 即便
是对于 refuted 也要跑 400ms 的 P-auto 以检查是否 refutation 依旧有效"; 05:53
"如此一来, 整个缓存失效机制也不需要了. 因为 the cache 并不记录裁决. 一切裁决都
是取决于 P-auto 的, 所谓 cache 只是提供 the additional lemmas"].  The
refuters run inline and in sequence [author 05:53 "此外我提议撤销异步 warning
的那个机制"].  `gen_reason'` is not touched at all.  This document states
the FINAL design only.  History lives in `GUARD_CACHE_QUICK_MODE_PLAN.rev7-full.md`,
`.rev9.md`, `.rev10.md`, `.rev11.md`, `.rev12.md`, `.rev13.md`, `.rev14.md`,
`.rev15.md`, `.rev16.md`, `.rev17.md`, `.rev18.md`, `.rev19.md`,
`.rev20.md` and `.rev21.md` (archived beside this file); consult them
for history, never for the design.  §11–§25 record earlier rulings; §17
says which of §11–§16 are superseded, §18 which of §17 (the `trace_ops`
hook, the `iNet` counter), §19 which of §11–§18 (the unbounded
"G.simpcut" pass), §20 which of §19 (nothing — it adds the preparatory
phase), §21–§25 which of §20 (nothing — drafter fixes only).  Every
behavioral decision carries its provenance: [author
YYYY-MM-DD HH:MM "quote"] is the author's own ruling (transcript timestamp,
UTC), [drafter] is a drafting decision the author may veto; §10 lists every
[drafter] decision that changes behavior.

Predecessor: `GUARD_NITPICK_FALSIFY_PLAN.md` (the guard race this plan
dismantles).  Prerequisite, already implemented: the stateful PLPR
reasoning (`ai-artifacts/STATEFUL_PLPR_REASONING_PLAN.md`,
`library/context_export.ML`): `Phi_Reasoner.reason`/`reason1` return a
`context_state`, and registered `PLPR_Context_Export.Hooks` carry hook-owned
data across run and block boundaries — this is how lemmas enabled at one
call reach the following calls and statements.  Line anchors are as of
2026-09-09 for `reasoners.ML` (after commit `8c26c3b4`; lines up to
`:942` unchanged, `:1168`–`:1798` moved by −197, `:1811` onward by −199),
2026-09-04 for `mlmsgpack.sml` and `pretty.ML`, 2026-09-07
for `PLPR.thy` (the §1 and §3 anchors of the two `\<condition>` reasoners,
`solve_obligation_now`, `defer_premise` and `prove_obligations_in_time`
re-taken 2026-09-15), `reasoner.ML` and the `Phi_System` callers, 2026-09-08
for `sledgehammer_solver.ML`, `raw_simplifier.ML`, `simpset.ML`,
`accounted_timeout.ML`, and 2026-09-08 evening for `cache_file.ML` — that
file changed under the plan during the day (commit `7615fe5` and
uncommitted edits: `proof_cache` became `times * string`), so every one of
its anchors was re-taken by symbol, and §10 step 0 says to do so again by
symbol, never by offset.  All were re-verified at implementation start,
2026-09-09 (§10 step 0, §26), and the step-P files (`ssymb.ML`,
`SSymb.thy`, `mlmsgpack.sml`, `pretty.ML`, `agent_packer.ML`,
`Performant_Isabelle_ML.thy`) re-anchored after their change.

READY after the nineteenth review (§25); "开工" given 2026-09-09; the
status line at the top of this document is the current one.

---

## 1. Glossary

Each entry gives the term, its meaning, and where the term comes from: the
author's own words, an existing name in the code, or a plain descriptive
phrase.  No other name is used for any of these concepts anywhere in this
document.

- **guard**: a premise of the `\<condition>` family (`Premise mode P`, mode
  `MODE_GUARD` or `NO_INST`, `PLPR.thy:187`, `:189`; until 2026-09-15 also
  the predicate `is_guard_mode`, deleted with the `is_F` shortcut, §39),
  discharged inside a run by the reasoners registered at
  `PLPR.thy:2005-2006`, `:2008-2009`.  [code]
- **a `prove_or_refute` call**: one invocation of `prove_or_refute` run
  through its whole protocol (§5).  Its ML type becomes `bool ->
  Proof.context -> Hasher.digest -> context_state -> context_state Seq.seq`
  (`can_inst`, the guard-side ctxt, the guard digest computed by the
  factory, then the run's state: the run's ctxt `ctxt0` and the goal state)
  [author 2026-09-04 04:19 "我们要把 prove_or_refute 的类型改成 context_state
  -> context_state, 我们要改 context, 且要一路改下去一直到 gen_reason' 的返回"].
  The ctxt it returns is `ctxt0` with this guard's delta applied to the lemma
  list, and nothing else changed.  Its verdict is decided on the spot, by P-auto,
  on every call [author 2026-09-08 05:53 "一切裁决都是取决于 P-auto 的"] — unless
  `guard_simp_tac` refuted the guard at step 1½, where the verdict is the
  simplifier's and P-auto does not run (§5 step 1½, §39 ruling 10).
  [descriptive]
- **the goal state**: the thm `prove_or_refute` receives — the PLPR sequent
  after `gen_guard_condition_solver`'s `Goal.protect 1` (`head_only`,
  `reasoners.ML:385-388`): the guard's subgoals visible, the rest of the
  sequent wrapped in `Pure.prop` (`#(rest ⟹ C)`) as the conclusion; the
  case split and the aux-fact insertion have already acted on it, no
  simplification has — `guard_simp_tac` is the solving function's own
  first step (§5 step 1½; until 2026-09-15 the factory's pass had acted
  on it too).  A **solved** goal state has no premises and is NOT
  `Goal.conclude`d — `head_only` concludes it afterwards [author 2026-09-04
  03:14].  [descriptive]
- **`guard_simp_tac`** (until 2026-09-15 the "G.simpcut" pass — that name
  was this plan's, inherited from the label of the `option_hunt` probe
  that used to wrap the pass and that commit `8c26c3b4` removed; it stays
  only inside quotations and in §11–§38 [author 2026-09-15 "赞同
  guard_simp_tac"]): the guard-side simplification —
  `ALLGOALS (Simplifier.asm_full_simp_tac (enhance_for_guard ctxt)
  THEN_ALL_NEW quick_cut)` (`quick_cut` `:960-963` fails a subgoal whose
  conclusion simplified to `False`) — standard `asm_full_simp` in the
  guard-side simpset with the refutation cut and a bound, nothing else
  [author 2026-09-15 "这不就是标准的 simp 吗？"].  The bound is **60 s of
  THREAD CPU, fixed in the code, no option** (`Time.fromSeconds 60`;
  `Thread_CPU.apply` scales it by `timeout_scale` itself; thread CPU with
  no wall limit, an error where the thread has no CPU clock — every
  guard-side bound is thread CPU, so that machine load cannot flip a
  verdict; only R-nitpick, which waits on an external process, keeps wall
  clock [author 2026-09-09 "400ms 时限改成线程 CPU 时间. 如果相关库没加载直接
  报错"]); several times the slowest simplification measured — 13 s, a
  Quicksort slice-bound guard with 26 premises under
  `linarith_split_limit = 20` (§39) — so a timeout means the simplifier is
  looping [author 2026-09-15 "赞同" (60 s); supersedes the 5 s of
  2026-09-11, ten times the 437 ms that was then the corpus maximum, which
  §39 found below the cost of a terminating simplification]; the bound
  exists to catch a loop, which any finite value catches, while a bound
  below a terminating simplification's cost turns a provable guard into
  `Unknown` and the reasoning into a wrong branch — the Quicksort
  regression.  On a timeout the function prints, unconditionally,
  the warning `The system simplifier probably loops on:` followed by the
  visible subgoals, and yields the state it was given, unchanged; its
  sequence is cut to its first state (`Seq.take 1`) and pulled inside the
  bound, so the one bound covers the whole simplification; a failure —
  `quick_cut` finding `False` — stays `Seq.empty` [author 2026-09-11 "把
  G.simpcut 的超时改为 5s"; "直接定死 5s x the scale"; "超时并警告之后, 保持现状"
  (superseding the `\<phi>guard_classic_prover_timeout` bound of
  2026-09-08 12:51 / 2026-09-09, which §33 found too tight); the timeout
  shape: drafter; the first state only: author 2026-09-09 "B. 赞同" — a
  deliberate narrowing, since a simpset solver could in principle make the
  pass multi-valued].  Not `timed_tac`, whose timeout is an empty sequence
  and would read as that refutation by simplification.
  Since 2026-09-15 it is a TOP-LEVEL function of `reasoners.ML`, not a
  pass of the factory: it is the ONE simplification of a guard, and it
  must run on the context that carries the entry's delta — `ctxt_g`,
  which only the solving function has — so the solving functions that
  simplify call it themselves: `prove_or_refute` (§5 steps 1½ and 6) and
  `p_auto_solving`, as does the `\<phi>guard_P_auto` method; the obligation
  instance does not (§39 ruling 6).  P-auto no longer simplifies (§1
  P-auto), and after the judge replaces the delta it runs again, on
  `ctxt_g'` and from the state the call was given (§5 step 6) [author
  2026-09-15 "显然，simpcut 得用 enhance_for_guard(guard_ctxt +
  delta) 但这样的话，注意 judge 是会修改 delta 的，于是在修改后我们必须重新跑
  simpcut 对吗？" — yes; §39].  Its output is what P-auto, R-conv, R-nitpick
  and the judge all see — it is not a part of P-auto [author 2026-09-15
  "你考虑过别的 refuter 吗？R-conv, R-nitpick 吗？？"].  Supersedes the
  2026-09-11 ruling that made it a local function of the factory ("建议挪
  动进 gen_guard_condition_solver 里", §33), whose premise — used nowhere
  else — no longer holds: two solving functions, `prove_or_refute` and
  `p_auto_solving`, and the `\<phi>guard_P_auto` method call it.  [code]
- **`gen_guard_condition_solver`** (until 2026-09-11 `guard_condition_solver`;
  renamed as the factory [author 2026-09-11]): from now on a FACTORY — the existing
  preprocessing template (`oblg_template`, case split, `apply_tac`'s fact
  insertion) parameterised by the solving function it ends with, whose
  type is `prove_or_refute`'s [type: drafter], and which receives the
  guard UNSIMPLIFIED: the factory knows nothing of entries, deltas or
  simplification [author 2026-09-15 "现在的 gen_guard_condition_solver is a
  generation. The parameter `solve` can be anything. So
  `gen_guard_condition_solver` doesn't assume the presence of the delta,
  the entry records"].  Its `is_F` shortcut (a 250 ms `auto_search_tac`
  on a guard that is literally `\<condition> False`) is DELETED, with
  `is_false` and `is_guard_mode` if nothing else uses them [author
  2026-09-15 "建议直接删除 is_F 分支"]: §33 item 3 had found its search never
  runs, and with `guard_simp_tac` inside the solving function such a guard
  ends as the shortcut ended it — closed by simp (`Proved`, no entry
  written on a first decision) or its conclusion rewritten to `False` by
  `quick_cut` (until 2026-09-15 no state and no verdict; since P2 of the
  same day a refutation by the simplifier: `Refuted` written, the record,
  the loud guard warning over a `Proved` entry — §5 step 1½); the other
  visible differences for the closed case are `prove_or_refute`'s trace
  line (at `\<phi>trace_reasoning` ≥ 2) and, under `ML_debugger`, a
  `guard_decision` record.  Its pipeline (`reasoners.ML:1625-1635`), in order:
  `quick_cut`; under `head_only`: the configured pre-tactic `pre`; the
  case split of the leading subgoal (`case_split_by_annotations_leading_subgoal`,
  `:1628`); **the guard digest** (below), taken on the whole state at this
  point — the split subgoals, nothing inserted yet [author 2026-09-08
  11:52 "赞同. 批准"]; `Method.insert_tac ctxt aux` on every subgoal
  (`:1629`; `aux` is the hook fold's aux component, seeded with
  `aux_thms ctxt` by `apply_tac`, `:226`, and extended by the registered
  `Tactic_Configures` hooks — today `Phi_Envir.ML:336-338`, which prepends
  `IDE_CP_Core.\<phi>implication`); then the solving function, on the
  state as inserted (until 2026-09-15: `auto_tac`, the "G.simpcut" pass
  and then the solving function, `:1603-1608`).  The
  `HEADGOAL (case_split THEN_ALL_NEW insert)` of `:1627-1629` therefore
  becomes `HEADGOAL case_split THEN <the digest step> THEN ALLGOALS insert`,
  the same thing with one whole-state step between; the digest step is an
  optional parameter that only the `guard_condition_judge` instance passes
  [drafter].  The factory's contract, total [drafter, tenth review]:
  `oblg_template` (`reasoners.ML:336-380`) is SHARED — four live callers,
  `defer_obligation` `:819`, `hammer_obligation_solver` `:850`,
  `gen_guard_condition_solver` `:1591`, `safe_obligation_solver` `:1651` — and
  becomes polymorphic in the solving function's result type `'a` through
  three extra parameters, `inj : thm -> 'a` (how a thm that never reached
  the solving function becomes a result), `on_thm : (thm -> thm) -> 'a ->
  'a` (how a thm-to-thm post-pass reaches the result) and `prj : 'a -> thm`
  (how a filter reads the thm out of a result); the three thm-returning
  callers pass `I`, `I` and `I`, the guard path passes `pair ctxt0`,
  `apsnd` and `snd`.  Every exit of the template that bypasses the solving
  function goes through `inj` — the `TrueI` exit `:344-345`, the two
  `fast_inst` exits `:346-347` and `:369-370` (until 2026-09-15 also
  `gen_guard_condition_solver`'s own `is_F` arm), and `head_only`'s
  zero-premise arm `:386-387`
  (`all_tac th`, which never calls the tactic and so becomes `Seq.single
  (inj th)`) — so each such result is paired with the ctxt the factory was
  CALLED on, `ctxt0`, never with `oblg_template`'s imported `ctxt'`
  (`:364`, whose fresh frees would make the export hook drop the very
  lemmas the design carries); the `Variable.export_inst` post-pass
  `:375-378` and `head_only`'s `Goal.conclude` arm (`:388`) go through
  `on_thm`, i.e. act on the thm half; `apply_tac`'s `SOLVED'` filter
  (`:222-228`, `Thm.nprems_of st' < Thm.nprems_of st` on the OUTPUT state)
  reads the output through `prj`: it keeps `st'` iff `Thm.nprems_of (prj
  st') < Thm.nprems_of th`.  `apply_tac` itself (`:222-228`; three
  callers, `:854`, `:1625`, `:1658`) is on the guard path and changes
  shape: today it puts the body's tactic into the `tactic` slot of
  `Tactic_Configures`'s hook state (`:217-220`, `type state = thm list *
  tactic * Proof.context`; `invoke_until_success`, `Hook.ML:109-111`,
  folds the registered hooks over the state and then applies the given
  fallback to it) and runs `#2` of the result; a body returning
  `context_state Seq.seq` cannot go into that slot.  So `apply_tac` runs
  the hook fold (`Tactic_Configures.invoke`, `Hook.ML:100-107`, the
  entry point every other hook table in the repository uses; it also
  honours a hook's `Return` and `ReEntry`, which no registration raises
  [author 2026-09-09, the first code review's first relaxation proposal,
  verified safe]) to obtain the configured `(aux,
  pre, ctxt')` and calls the body on them OUTSIDE the hook; the hook's
  `state` type and its one registration outside PLPR
  (`Phi_System/library/system/Phi_Envir.ML:336-338`, which only adds aux
  theorems) are untouched.  The one behaviour that changes: a hook
  raising `Hooks.Success` with a tactic of its own used to REPLACE the
  body; now its state is used like the fold's result and the body runs.
  No registration does that today [drafter; §10].  Invariant: the state
  leaving a guard reasoner is `ctxt0` with this guard's delta applied, and
  only the solving function may replace the ctxt.
  Three instances (§3): **`guard_condition_judge`** = the factory applied
  to `prove_or_refute`, `{can_inst : bool} -> context_state ->
  context_state Seq.seq`, registered on the state by the in-run
  `\<condition>` reasoners as `guard_condition_judge {can_inst = …} o snd`
  (at `PLPR.thy:2005`, `:2008` only `Phi_Reasoners.wrap` goes — it re-pairs
  the incoming ctxt and would drop the lemmas; `o snd` stays because
  `apply_tactic`, `reasoner.ML:688`, hands an ML reasoner `(backtrack_mode,
  context_state)`); the existing **`guard_condition_solver'`** /
  **`guard_condition_solver1`** = the factory applied to `p_auto_attempt`
  (§1 P-auto, §3, §39 ruling 9), used by the out-of-run
  callers; and the factory applied to `try_prove_or_give_up` over
  `fastforce` for `defer_premise`'s solve-now case — with NO
  `guard_simp_tac` before it: `fastforce` is `fast_force_tac` =
  `Classical.fast_tac o addss`, so its `asm_full_simp_tac` runs inside the
  search, on the whole goal, in the same simpset (the guard-side ctxt plus
  `Guard_Simp_SS`), so the pass the factory used to run there was one more
  duplicate; the
  entry lemmas it incidentally brought to that instance's simplification
  end with it — the obligation instance was never a consumer of the lemma
  list (§1 the lemma list) [author 2026-09-15 "你都用 fastforce 了为什么还要用
  guard_simp_tac？"].  The two degenerate instances ignore
  `can_inst`, take no digest, return the ctxt they were given, keep their
  thm-returning entry points, and never touch the store — the cache is
  `prove_or_refute`'s alone [author 2026-09-03 09:44; 11:11; 2026-09-08
  07:34 "不要. 我们现在只是给 prove_or_refute 做, 不是给 guard_condition_solver
  做"].
- **`try_prove_or_give_up`**: `Time.time option -> (Proof.context -> tactic)
  -> Proof.context -> thm -> thm Seq.seq` — run the tactic once, under the
  bound if given, keep only a solved state; otherwise `Seq.empty`.  Its one
  caller since 2026-09-15 (§39 ruling 9 gave the out-of-run instance
  `p_auto_attempt`): for obligations, `fastforce` in a
  `Guard_Simp_SS`-enhanced ctxt, no bound by default [author 2026-09-03
  11:15; 12:53].
- **lemma**, **tier**, **delta**, **entry**, **verdict**: what the store holds
  for one guard —
  ```
  datatype tier = Only_Once | Rarely | Normal | Frequent   (* 3 / 30 / 300 / 1000 applications *)
  type lemma = term * Phi_Proof_Store.proof_cache * tier   (* statement, (replay times, method text), budget *)
  type delta = {added : lemma list, deleted : term list}   (* what the guard does to the lemma list *)
  datatype verdict = Proved | Refuted | Unknown
  type entry = {delta : delta, verdict : verdict}
  ```
  A guard's entry is a DELTA to the lemma list of the context the guard is
  met in — the lemmas it adds and the statements it deletes: every lemma of
  the list whose proposition is `Pattern.equiv` to a deleted statement
  leaves, whichever guard added it, then its lemmas go in by the one append
  rule (§1 the lemma list) — applied on every call (§5 step 1); the judge's
  answer replaces the delta whole (§5 step 6) [author 2026-09-12 "我建议我们
  修改一下设计, 每个 guard condition 的 judge lemmas 实际上是一个 pair: 新增的
  lemmas, 与要删除的 lemmas (term list). 增量的去做"; "当然是当前 context 的
  lemma list 里的所有 aconv 的, 包括别的 guard 带进来的"; "每个 condition 的
  slot 永远是相对于之前的 ctxt 的增量. judge 的输出永远是对 the condition's
  slot 的完全替换"; "删除是持久的, 添加也是持久的"; §36].
  `Phi_Proof_Store.proof_cache = Phi_Proof_Store.times * string` with
  `times = {thread_cpu : Time.time, wall : Time.time}` (`cache_file.ML:168`,
  `:176` in the signature; `:274`, `:285` in the body): two independent
  standard-machine measurements of the replay, thread CPU and wall, and
  the method text.  `Proved` = P-auto proved the guard
  with the lemmas; `Refuted` = a refuter found a countermodel, the judge
  answered `Unprovable`, or `guard_simp_tac` rewrote the guard to `False`
  at step 1½ (§39 ruling 10) — a reliable negative, silent on a hit except
  the simplifier's refutation over a `Proved` entry, which prints the loud
  guard warning; `Unknown` =
  nobody could decide — a hit warns again [author 2026-09-08 06:10 "3. 好
  的, 那么赞同 Proved of lemmas | Refuted | Unknown"; "4. 对"].  The tier is
  the judge's estimate of how often the lemma will be applied in one
  P-auto call; the numbers are constants of §10 [author 08:19 "我打算给
  judge 几个选项: Only_Once, 很少 (30 次以内), 一般 (300 以内), 频繁 (1000)";
  08:20 "Only_Once 给 3"].  A guard with NO entry that P-auto proves gets
  none written [author 06:27 "1. 不用写"]; a guard whose entry is
  `Refuted` or `Unknown` and that P-auto then proves gets `{delta,
  Proved}` (§5 step 3), so a `Proved` entry with an empty delta is
  reachable (§7).  `Refuted` is the constructor's name again; `Unprovable`
  names only the judge's answer [supersedes 2026-09-04 03:23].  `verdict`,
  `tier`, `lemma`, `delta`, `entry` are declared in `guard_cache.ML` (§4);
  `judgement` in `reasoners.ML` beside the judge.
- **guard digest**: the `Hasher` digest (`Word64.word`) of the WHOLE goal
  state and of the context's assumptions: one `Hasher.terms` over
  `Thm.prop_of th :: map Thm.prop_of (Assumption.all_prems_of ctxt)`, on
  the state the factory holds right after the case split and BEFORE the
  aux facts are inserted (`gen_guard_condition_solver`'s digest step;
  `guard_digest : Proof.context -> thm -> digest`).  `Thm.prop_of th` under
  `head_only`'s `Goal.protect` is the guard's subgoals — each with its
  parameters and its own premises — followed by the protected rest of the
  sequent with its conclusion; the assumptions are the ctxt's at that
  step.  Not the aux facts, which are derivable; not the theory name
  [author 2026-09-11 "我说的是整个 sequent 包括 Goal.protect 中的结论";
  "不需要加 aux 事实, aux 全是 derivable 的, 我们只考虑 the sequent and the
  contextual assumptions"; "确定: state + contextual assumptions 的方案" —
  after the measurement of §33 item 4].  CORRECTION of the record: from
  2026-09-03 to 2026-09-11 this bullet, step 1 and step 2 keyed the store
  by the guard's own subgoals only (`Thm.cprems_of`); that scope was the
  drafter's, written under the author's citations on the digest's TIMING
  ("2. 不掺" — the ctxt's simpset and lemmas not mixed in; "digest 取在这道
  化简之前"; "赞同. 批准" — before the insertion), which never said
  "subgoals only"; the author meant the whole sequent throughout
  ("我从来说的都是整个 sequent"; "我从来没有批准过只给 guard 子目标做 digest").
  Computed by a new
  `Hasher.terms : term list -> digest` added to `HASHER` and
  `contrib/auto_sledgehammer/library/Hasher.ML` (the `hash_term`
  accumulator chained from the FNV basis over the list; `Hasher : HASHER`,
  `Hasher.ML:81`, hides the accumulator, so it cannot live in
  `guard_cache.ML`).  The key moves when the goal state's text changes —
  the guard's, the rest of the sequent's or its conclusion's — or the
  context's assumptions do; when `oblg_template`'s normalisation of the
  guard does (`:341-342`, the ctxt's simpset on the tag); and, for a state
  that still carries schematic variables when it reaches the factory, when
  those variables' names or INDICES do.  On the `\<condition> ?P` reasoner
  (`PLPR.thy:2005`, `can_inst = true`) the factory runs `oblg_template` at
  `fix_level = 1` (`reasoners.ML:1591`; `:332-334`), whose fixing targets
  are the variables of the leading antecedent's own premises that its
  conclusion does not mention, plus the `LPR_ctrl`-annotated ones of the
  conclusion (`:354-360`, `:244-247`); `Variable.import_inst` runs iff
  that list is non-empty (`:362-367`) and turns exactly those variables
  into fresh Frees whose names `Name.variant` takes from the ambient
  context's declared-name pool (`:364`; `variable.ML:601-609`), hashed by
  that name (`Hasher.ML:191-192`; the TFrees of `importT_inst` likewise,
  `:171-172` — and `Thm.instantiate` (`:366`) substitutes those TFrees
  throughout the state, so a variable the import did not fix is hashed
  with an ambient-named TFree whenever its type shares a type variable
  with a target); every other schematic variable of the guard — for a
  guard whose antecedent has no premises of its own and whose conclusion
  carries no `LPR_ctrl` annotation, all of them — reaches the digest as
  `Var`/`TVar` and is hashed by its name AND its index (`Hasher.ML:193-199`,
  `:173-179`), an index that moves with the sequent's `maxidx`.  Only on
  the `NO_INST` reasoner (`:2008`, `fix_level = 2`) does the import run
  over every variable of the antecedent (`:359`).  Not when a lemma is
  enabled, not when an upstream
  statement adds a useful fact.  A statement replayed as it was gets the
  same key every time: the whole of PLPR is deterministic, so the indices
  and the fresh names are [author 2026-09-08 15:12 "整个 PLPR 是确定性的
  啊, schematic 的 index 也是确定性的啊"]; only the same guard reached from
  two statements at different indices, or under different declared names,
  gets two keys.  The digest is normalised against NEITHER [author
  2026-09-08 12:57 "好的, 赞同不做归一化" (the fresh names); 15:12 "B. 否
  决 … 为什么要放宽呢?" (the indices)]; the cost of the divergent keys is
  recorded in §7.  Two calls with the same goal state and the same
  assumptions share one entry, in one run or across runs and builds — the
  same statement replayed, or an identical state reached twice: the entry
  is advice, not a decision, so sharing is right [author 06:10 "1. 同意",
  on sharing as such]; its cost is recorded in §7.  Measured on the corpus
  (§33 item 4, 2026-09-11): 355 decisions resolve to 261 keys under this
  digest (144 under the former subgoals-only key), and among the 162
  decisions that hit the store no key repeats within one run; the digest
  costs 77 us per decision (5 us before), 0.12 % of the guard time.
- **the store**: the theory's proof store, `<thy>.proof-store` of
  `auto_sledgehammer` (`Phi_Proof_Store`), in which a guard's entry is one
  record under a key no proof obligation uses (§8); read at the start of a
  `prove_or_refute` call, written at the points §5 names, never validated.
  Key: `"PLPRGUARD" ^
  Hasher.compact digest` [author 2026-09-03 02:18; `compact` kept over
  `hex`: 2026-09-07 13:09 "我坚持用 compact"; `Hasher.compact`
  (`Hasher.ML:74`, `:113`) is the 8-byte big-endian rendering, not text,
  never printed].  Concurrent runs may write one entry; the store is
  last-write-wins, and two runs deciding the same guard write the same
  thing in the common case.  `\<phi>guard_cache` off = no entry is read
  and no entry is written; every call decides as if it had none [author
  2026-09-02 10:41; 2026-09-03 12:52]; the switch gates nothing inside the
  proof store itself (§8).

The five protocol stages that follow — P-auto, R-conv, R-nitpick, the
judge, the two warnings — describe what one call does AFTER it has read
its entry and enabled the entry's lemmas (§5).

- **P-auto**: `p_auto_tac ctxt` = the solved states of the depth-10
  classical search (`main_tac i = CHANGED (nodup_depth_tac (addss ctxt) 10
  i)`, `REPEAT_DETERM (FIRSTGOAL main_tac)`, first state only) in
  `enhance_for_guard ctxt` — the search step alone; and P-auto =
  `cpu_bounded_tac \<phi>guard_classic_prover_timeout o p_auto_tac` (thread
  CPU) — the one proof attempt every call that reaches step 2 makes, hit
  or no hit, with the entry's lemmas enabled, and its outcome IS the call's
  verdict — unless `guard_simp_tac` refuted the guard at step 1½, where the
  verdict is the simplifier's and P-auto does not run (§5 step 1½, §39
  ruling 10) [author
  2026-09-02 07:11; 400 ms provisional 08:49; on every call: 2026-09-08
  05:36 "即便是对于 refuted 也要跑 400ms 的 P-auto 以检查是否 refutation 依旧有
  效"; the steady-state cost of one P-auto budget per unprovable guard per
  run accepted without measurement: 06:10 "值的. 不需要测量. 相信我是值的"].
  Until 2026-09-15 P-auto was `p_auto_search_tac`: one `asm_full_simp` +
  `quick_cut` pass and THEN the search — so the simplification the
  factory's pass had just completed was done a second time inside the 400
  ms, and on a guard whose simplification costs hundreds of milliseconds
  the second pass ate the budget and the search never ran (§39, the
  Quicksort regression).  From now on P-auto does not simplify: it runs
  on the state `guard_simp_tac` produced, and its 400 ms is the search's
  [author 2026-09-15 "我们现在可以按你推荐的，取消 P-auto 中的重复 simp"]; 400
  ms is a safe budget for the search (§32: every proved guard's P-auto at
  most 204 ms of thread CPU over 341 decisions) [author 2026-09-15 "400ms
  是很安全的啊"].  `p_auto_tac` replaces both `p_auto_search_tac` and
  `p_auto_body` [`p_auto_body`: author 2026-09-15 "这个名字很难听"; the new
  name: author 2026-09-15 "批准 p_auto_tac"].  Exposed as the proof method
  **`\<phi>guard_P_auto`** [author 2026-09-03 11:11], whose body is
  **`p_auto_attempt`**: `guard_simp_tac` then P-auto — the whole attempt,
  both steps, one definition shared with the out-of-run instance
  `p_auto_solving` so that the two cannot drift apart [author 2026-09-15
  "P1 赞同"; the name: drafter].
- **R-conv**, **R-nitpick**: the two refuters, run in that order, inline
  on the run's thread, after P-auto fails and only on the paths §5 names,
  each bounding itself [author 2026-09-03 12:36 "每个 hook 自行决定是否
  timeout"; sequential and inline: 2026-09-08 05:53 "在 P-auto 后依旧要跑
  R-conv 和 R-nitpick, 串行地跑"]: R-conv = today's `r_conv_racer` body
  (`reasoners.ML:1132-1163`, negate and search) under
  `\<phi>guard_classic_prover_timeout` in a `Guard_Simp_SS`-enhanced,
  lemma-enhanced ctxt [author 2026-09-04 03:23 "复用"]; R-nitpick = today's
  Nitpick screen and calls (`reasoners.ML:1459-1478`) under one
  `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms × n_goals`,
  subgoals tried one after another, EACH under its own inner
  `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms` so that one
  subgoal's overrun moves on to the next instead of eating the whole net
  [author 2026-09-03 13:05; inner bound 2026-09-07 13:00; order: drafter].
  Both catch their own `TIMEOUT` and report "not refuted".  A refutation
  by either refuter, or by `guard_simp_tac` at step 1½ (§39 ruling 10), is
  what makes an entry `Refuted`.
- **the judge**: ONE optional function in a process-global ref,
  `judge : (judge_arg -> judgement) option Unsynchronized.ref`, default
  `NONE`, installed by ML code (phase 2: the LLM judge) [author 2026-09-04
  03:04].
  ```
  type judge_arg = {ctxt : Proof.context, outer_ctxt : Proof.context,
                    can_inst : bool, thm : thm,      (* thm = the goal state *)
                    delta : delta}                   (* this entry's delta, as step 1 left it *)
  datatype judgement = Provable of delta | Unprovable
  ```
  [author 2026-09-04 03:11–03:14 (`thm` in); `Provable` reduced to lemmas:
  2026-09-08 06:14 "赞同" (no `proof`, no returned state — P-auto proves the
  guard with the lemmas, on the spot, so the recording run and every
  later run behave alike); `Provable` of a delta, and the entry's delta
  passed beside the ctxt: 2026-09-12 "传入 judge 的应该是两个参数, guard_ctxt
  和 delta"].  `judge_arg.ctxt` is the guard-side ctxt as
  it was BEFORE this entry's delta was applied (§5 step 1's `ctxt`, whose
  lemma list holds the lemmas of earlier guards and statements — the
  theorems the judge may name for deletion, by their propositions),
  `outer_ctxt` is `ctxt0`, `delta` this entry's delta with step 1's
  replay failures dropped and its times converted to this machine's clock
  (`Phi_Proof_Store.machine_time`), the clock the judge's own RAW times
  are on — so a lemma handed back as received is measured, not scaled
  twice.  Its answer REPLACES this entry's delta whole,
  relative to that same list: a lemma of the old delta the judge wants
  kept it states again, a bad one disappears by the judge not stating it,
  an earlier guard's lemma stays unless the judge deletes it, and a lemma
  the judge adds whose proposition is already in the list takes the
  judge's budget [author 08:34 "LLM judge 那里, 是无视 the prove_or_refute
  point 上已有的的 lemmas. 得到的 lemmas 是直接替换, 而不是继承已有的 lemmas,
  以允许把坏的 lemmas 移除掉" — "已有的 lemmas" = this entry's, as the author
  confirmed on 2026-09-09 ("是你之前写计划的时候误解了我了"; the judge's ctxt
  "的确是不带本 entry 的 lemmas 的", "还是带了之前的 lemmas 的"; a collision
  "更新 the budget"); 2026-09-12 "judge 的输出永远是对 the condition's slot
  的完全替换"].  Its obligations, a contract with no run-time check beyond what
  §5 does anyway: each lemma is a closed statement of type `prop`
  (`Trueprop`-wrapped for a HOL proposition) [drafter], certifiable by
  `Thm.cterm_of ctxt0` and provable by its own method text in `ctxt0`.
  The method text MAY cite the context's facts, the contextual
  assumptions included, by name: the digest covers the goal state and the
  contextual assumptions, and PLPR reasoning is deterministic, so every
  replay of the entry happens in the same `ctxt0`, rebuilt with the same
  facts under the same names [author 2026-09-14 "我认为必须可引用 contextual
  assumptions 这是很重要的!"; "复现是同一个 ctxt 具有相同的 fact names"].  (Rev
  18–25 said the opposite — "theory-level facts only, never a fact local
  to the recording call's context" — under a citation of "2. 不掺", which
  had ruled the assumptions OUT of the digest and was reversed on
  2026-09-11; the clause was the drafter's, corrected here.)  The replay
  runs without `oblg_template`'s fixes and the inserted aux facts; the
  lemmas together must make P-auto prove the guard; its
  times are RAW measured times (`Phi_Proof_Store.times`, thread CPU and
  wall) [drafter], which `prove_or_refute` normalises with
  `Phi_Proof_Store.standard_time` (`cache_file.ML:238`, `:914`) once, ON
  RECEIPT — before the replay of §5 step 6, because `replay_limits` takes
  standard-machine times and `Thread_CPU.apply` re-scales them by this
  machine's `timeout_scale` (`cache_file.ML:224-227`, `:791-796`;
  `thread_cpu.ML:331`), so feeding it raw times would give the same lemma
  a different real budget in step 6 than in step 1 — and the write then
  copies them unchanged; and the times a judge declares must not
  UNDER-STATE its lemma's replay cost, because §5 step 1's replay bound is
  derived from them and §5 step 6 makes an overrun of it an `error` — the
  plain way to honour this is to run the proof once and report that
  measurement.  A lemma that fails to certify or replay, or a `Provable`
  after which P-auto still fails, is an `error` naming the judge as
  broken, propagating as the run's exception [author 08:45 "我建议直接 error
  说内部错误: the judge 有问题"; "2. 我建议此时也 error"].  The judge is called
  on each run's own thread, concurrently across runs, and must be
  re-entrant [drafter].  The judge must not re-enter PLPR, and neither may
  its proof texts [author 2026-09-07 13:21 "定一条规约, judge 不能重入 PLPR";
  §17 item 8].  (Rev 18–25 said here "It may re-enter PLPR — nothing
  counts calls any more, supersedes 13:21": the drafter's reversal of that
  rule, never ruled — audit A4, 2026-09-12; withdrawn 2026-09-14.  The
  author's 2026-09-08 11:44 "你不用担心嵌套的问题. 你可以 leave a comment"
  concerned the lemma budget's nesting, which therefore stays unhandled
  and commented.)  An exception escaping the judge or a
  refuter propagates through `prove_or_refute` like any other exception of
  the run [author 2026-09-03 12:31 "hook 的崩溃应该视作 PLPR 推理链的崩溃"].
- **`Guard_Simp_SS`**, attribute **`\<phi>guard_simp`**: the simpset of
  USER-declared rules that strengthen guard proving — an instance of the
  repository's `Simpset` functor (`library/tools/simpset.ML`) [author
  2026-09-03 11:15].  Applied by an `enhance` inside each consumer and
  nowhere else [author 2026-09-03 13:26–13:27]: `guard_simp_tac`,
  `p_auto_tac` (so `\<phi>guard_P_auto`), R-conv, the obligation
  instance's `fastforce`.  Not R-nitpick (it stacks only
  `Nitpick_Refute_SS`, today's `Guard_Refute_SS` renamed [author 2026-09-03
  11:15]), not `judge_arg.ctxt` as such, not the lemma replay (§5 step 1).
  `enhance` is a merge (`simpset.ML:79-81`); each consumer enhances the
  ctxt it hands to its simplifier and never rebinds `auto_tac`'s `ctxt`,
  which would carry the simpset into R-nitpick.  It holds no lemmas of the
  judge.
- **the lemma list**, **`Guard_Lemmas`**: a `Proof_Data` slot of type
  `(thm * int) list` — each judge lemma of the current guard, and of
  earlier guards of the run and of earlier statements of the block, as the
  theorem its replay produced, with its tier's budget — initially empty
  [author 2026-09-08 07:44 "我建议新建一个 … 专门去存储 the proposed lemmas";
  07:48 "只要 a Proof Data storing a list of thms 就够了"].  Written by §5
  step 1 (the entry's delta applied: deletions, then appends) and step 6
  (the judge's delta applied) inside a call, and by the guard-cache
  export hook, which replaces the whole outer list at every run and
  block boundary; read by `enhance_with_lemmas`, by the hook itself and
  by the judge.  A theorem's identity in the list — for a deletion and
  for the append's duplicate check — is its proposition, compared by
  `Pattern.equiv` (equal up to renaming of schematic variables) [author
  2026-09-12 "删除去重等可以直接看 the lemmas 的 prop 吗？反正这些 lemmas as
  thms 也会发给 the judge"; "the judge 始终是在这一刻删除那个 thm 对吗？一切重放
  都是确定性的对吗？"; 2026-09-13 "用 Pattern.equiv 去做相同性比较"].  An
  append whose proposition is already there gives that theorem the budget
  of the delta being applied — the one rule for an entry's delta and for
  the judge's, so a replayed entry rebuilds the list the recording call
  returned [author 2026-09-13 "SEM-2 (a)"].  It travels with the ctxt and
  is what the guard-cache export hook carries.  Its consumers are
  `guard_simp_tac`, `p_auto_tac` and R-conv — each through
  `enhance_with_lemmas`, and nothing else.
- **`enhance_with_lemmas`**, **the lemma budget**: `enhance_with_lemmas :
  Proof.context -> Proof.context`, the ONE function through which a
  consumer gets the lemmas into its simplifier, and the whole mechanism
  that keeps a bad lemma from making the simplifier loop [author 07:08 "超
  过 1K 就不准再用这个 simplification rule 了"; 08:34 "就别移除了. 改为超过后就禁
  止使用此 rule"; the shape 2026-09-08 10:53–11:46].  Given a ctxt whose
  lemma list holds `(P_i, budget_i)`, `i = 0..k-1` — at most one entry per
  statement, §5 step 1 — it: (1) declares `k` fresh fixed variables
  `\<r>BUDGET<i> :: ind` with `Variable.add_fixes` (the returned internal
  names, `\<r>BUDGET<i>__` in a proof-body ctxt, are the keys of
  everything below; `\<r>` is PLPR's own symbol, so no user variable
  collides; the pattern follows `Subgoal_Env.allocate_subgoal`'s
  `\<r>GOAL<n>`, `Subgoal_Env.ML:54`) [author 11:32 "赞同 \<r>BUDGET"];
  (2) extracts the rewrite rules of each lemma FIRST, with the ctxt's own
  extractor, `Raw_Simplifier.mksimps ctxt P_i` (`raw_simplifier.ML:835`;
  HOL's is `simpdata.ML:118`: `Variable.gen_all`, then the `mksimps_pairs`
  splitting of conjunctions and the like, then `mk_eq`) — so a lemma
  stated with an outer `⋀` or as a conjunction yields exactly the rules it
  would yield as an ordinary simp rule; (3) weakens EACH extracted rule
  with the budget premise placed LAST: `Thm.implies_intr` of the certified
  `Guard_Budget \<r>BUDGET<i>` puts it first, and `Drule.rotate_prems 1`
  (`drule.ML:261-262`, `Thm.permute_prems 0 1`; the identity when it is
  the only premise) rotates it behind the rule's own premises, giving
  `A_1 ⟹ … ⟹ A_n ⟹ Guard_Budget \<r>BUDGET<i> ⟹ lhs ≡ rhs`; (4) builds a
  `Strhashtab` (`Performant_Isabelle_ML`) from the internal name to the
  remaining budget, `budget_i` [author 11:46 "要不直接用 Strhashtab 吧"; the
  decimal `<i>` is not parsed, the name is only a key: 11:40 "赞同十进制"];
  (5) adds ONE simproc on the pattern `Guard_Budget ?v`
  (`Simplifier.make_simproc` + `Raw_Simplifier.add_proc`, context-local,
  no theory-level declaration) whose closure holds that table: on
  `Guard_Budget (Free (n, _))` it looks `n` up — found with a positive
  remainder → decrement and return `Guard_Budget n ≡ True` (from
  `Guard_Budget_def`); found at zero, or not found → `NONE`; (6) adds the
  weakened rules to the ctxt's simpset with `addsimps`.  That add runs
  `mksimps` again, which is the identity on them (`simpdata.ML:47-52`:
  `mk_eq` returns a `Pure.eq`-concluded theorem unchanged; `:98-116`: a
  non-`Trueprop` conclusion is left alone; `gen_all` finds no outer
  parameter), and it warns "Ignoring duplicate rewrite rule" for no
  ambient rule and for no other lemma's rule: a weakened rule's
  proposition carries its own fresh variable, so it is
  `Thm.eq_thm_prop`-equal (`raw_simplifier.ML:166-167`) to neither; two
  propositionally identical rules extracted from ONE lemma (a repeated
  conjunct) collapse with that stock warning, exactly as an ordinary simp
  declaration of the same statement does.  (Rev 15 built a separate simpset on
  `Raw_Simplifier.clear_simpset ctxt` and `merge_ss`ed it in, so that the
  ctxt's `mksimps` would do the extraction; with the extraction done by
  hand in step (2) that detour is gone [drafter]; §18.6's point stands —
  Pure's bare `empty_ss` keeps only Pure equations and is never used
  here.)  **`Guard_Budget :: ind ⇒ bool`** is `definition Guard_Budget
  x ≡ True` in `PLPR.thy`, declared to no simpset, and `hide_const (open)
  Guard_Budget` at the end of `PLPR.thy` [author 10:53 "那个前件得是
  Guard_Budget :: ind => bool … 最后要在 PLPR.thy 的末尾 hide_const (open)
  Guard_Budget"]: `ind` has no simp rules, numerals or arithmetic
  procedures, so the premise reaches the simproc unchanged.  What this
  buys, against the code: the simplifier proves a conditional rule's
  premises with its own prover, in order, before applying the rule
  (`raw_simplifier.ML:1070-1086`; the prover attacks subgoal 1 first, so
  the budget premise, being last, is reached only after the rule's own
  premises are proved) — the prover simplifies `Guard_Budget
  \<r>BUDGET<i>__`, no rule matches, the simproc answers — so one unit of
  budget is spent when the rule's own premises have all been proved and
  the rewrite is about to be applied; the one residue is `check_conv`
  (`:1079-1080`), which can still reject the rewrite after every premise
  is proved and then costs a unit without rewriting — a rare arm.  A
  lemma at zero simply stops matching for the rest of that consumer's
  run, nothing is removed and nothing is written, and the lemma is
  enabled again, with a fresh budget, by the next `enhance_with_lemmas`;
  every property of a rewrite rule is kept (`mksimps` splitting,
  orientation, ordered rewriting of permutative rules, the "Applying
  instance of rewrite rule" trace, `Simplifier_Trace`'s `trace_rrule`);
  nothing global exists — no
  `Theory_Data`, no `trace_ops`, `Simplifier_Trace` untouched; and every
  lemma being conditional, the `simp_depth_limit` guard of `:1071-1073`
  applies to it.  The one behavioural difference: on a redex several rules
  match, `sort_rrules` (`:1093-1104`) tries unconditional rules first, so
  a lemma yields to an unconditional rule of the ambient simpset that also
  applies there (`:1088-1091`, first success wins) — rewriting continues on
  the result and the lemma is tried again on it.  Cost: one premise proof
  per application, i.e. one simproc call on a one-constant redex.  Nesting
  — a `prove_or_refute` call re-entered from inside the judge on top of
  `judge_arg.ctxt` — enables a second batch of variables and a second
  simproc on the same chain; each simproc answers only the names in its
  own table, but this case is not designed for and only commented in the
  code [author 11:44 "你不用担心嵌套的问题 … simproc 是不会回调 PLPR 的"].
  Alternatives measured and rejected on 2026-09-08 (`ai-artifacts/
  Simp_Loop_Probe.thy`, `Lemma_Simproc_Probe.thy`, `simp_count_report.txt`):
  Isabelle's simplifier detects no loop of an unconditional rewrite rule
  (`f x = f x`, `g x = g (g x)`, `a = b` with `b = a` rewrite until an
  external timeout: 100 000–500 000 rewrites in 2–3 s); a
  `Raw_Simplifier.trace_ops` hook is `Theory_Data` kept by the FIRST parent
  on a merge (`Pure/context.ML:786-791`), which in `Phi_Preliminary.thy:6-9`
  is `Main`, so a hook installed in PLPR is lost where phi-system proves
  guards, and installing it per call through a derived theory makes
  sibling theories whose certificates cannot be joined (`:663-669`); making
  every lemma itself a simproc works but is tried only after every rewrite
  rule (`raw_simplifier.ML:1130-1135`), loses ordered rewriting and the
  `mk_eq_True` fallback (`:974`, `:971-973`), is invisible to `Simplifier_Trace`, costs
  ~1.6× per application and re-implements `decomp_simp`/`rew` by hand
  [author 10:53 "好吧, 我赞同你的方案"].  Measured on real phi-system reasoning
  (`simp_count_report.txt`, the second, accumulated report; one top-level
  simplifier invocation is the unit): legitimate HOL normalisation rules
  reach 100–445 applications in 4.8 % of invocations, `Phi_Preliminary.Big_def`
  895, and only `Nat.One_nat_def` exceeds 1000 (31 639, pathological); the
  budget is spent over a whole consumer run, which makes many invocations,
  so the tiers 3 / 30 / 300 / 1000 are an order-of-magnitude reference that
  §10 step 3 confirms.
- **the guard-cache export hook**: one `PLPR_Context_Export.Hooks` entry
  (priority: drafter) registered by `guard_cache.ML`.  At every run and
  block boundary it takes the inner ctxt's lemma list, passes each theorem
  through `PLPR_Context_Export.export_aux_lemma inner outer` (a theorem
  mentioning a variable fixed inside is dropped, one an assumption frame
  refuses — `UNEXPORTABLE` — is dropped, the rest are exported, keeping
  their budgets), and OVERWRITES the outer ctxt's lemma list with the
  result — no equality check [author 2026-09-04 07:33 "直接覆写是最快的";
  2026-09-07 12:34 "启用进 ctxt 的 lemma 要流到后续语句"].  It satisfies the
  hook contract of the stateful PLPR plan (H1 one theorem at a time through
  `export_aux_lemma`, H2 re-exportable — `context_export.ML:16` names
  overwriting as satisfying it, H3 own data only).  Through it a lemma
  enabled at one call reaches, along the branch the search keeps, every
  later call of the run, the run's returned ctxt, and the following phi
  statements of the block — unless a block frame refuses it; a call that
  returns `Seq.empty` contributes no successor state (an ML reasoner's
  sequence IS its set of successor states, `reasoner.ML:688`), so its
  `ctxt1` and the lemmas it replayed are abandoned with that branch.  The
  list changes by §5 step 1 (this entry's deletions, then its appends),
  by §5 step 6 (the judge's delta) and at a run or block boundary by the
  theorems `export_aux_lemma` refuses.  A theorem is stored as its replay
  produced it — no normalisation — and §5 step 1's append gives one whose
  proposition is already in the list (`Pattern.equiv`) the delta's budget
  instead of appending it (§1 the lemma list).  `Proof_Context.export` may change a
  carried theorem's proposition — `Assumption.export_` discharges the
  assumptions of the frames it crosses (a phi block frame turns a theorem
  whose hyps hold the block's `Premise` assumption into `C ⟹ th`,
  `Phi_Working_Mode.ML:226-232`) and hhf-normalises, so a statement's
  outer `⋀n` becomes `?n` (`assumption.ML:153-156`; the replay itself keeps
  the binder), and `Variable.export` generalises the
  type variables the outer ctxt has not declared (`variable.ML:515-529`);
  a plain replay of the same lemma at a later call then sits in the list
  beside its exported copy, each with its own budget variable and its own
  rules.  Accepted: replay is deterministic, so at one call site every
  hit sees the same list; the copies cost budget headroom and simplifier
  time, never soundness [author 2026-09-12 "这个去重仅仅是为了性能优化, 为了
  重用是吗? 其实不做这个去重, 就老老实实全都丢掉, 然后全都去证明新的 lemmas 也
  没有问题, 对吗?" — the drafter's answer: yes, the only effects are a
  budget per copy and one conditional rule per copy; "终于可以删除
  canonical_form 这傻玩意儿了"].  The canonical form of revs 18–20 (§22–
  §24) — `norm_hhf_protect`, type generalisation, `Drule.zero_var_indexes`
  before storing — is withdrawn (§36).
- **the undecided-guard warning**: the message printed over a guard's
  subgoals when neither a proof nor a refutation was found and no judge is
  installed — today's text at `reasoners.ML:1408-1419`, factored into one
  function of the ctxt and the subgoals; printed, as today, through
  `Phi_Reasoner.warn_pretty … 1` (`reasoner.ML:337-340`), i.e. only where
  `\<phi>trace_reasoning >= 1` (the corpus sets it: `IDE_CP_App2.thy:256`).
  Printed when a call ends `Unknown`, on a first decision and on every
  `Unknown` hit alike [author 2026-09-08 05:53 "对于 reliable = false 的,
  我们直接 warning 不再跑 R-conv, R-nitpick"], a call from a `Proved`
  entry included; the two warnings are decided at one site from the final
  verdict [author 2026-09-09 "spec-3 赞同 (a)"; 2026-09-14].  [descriptive]
- **the loud guard warning**: the message printed when a guard whose entry
  said `Proved` could not be proved by P-auto with the entry's lemmas,
  neither R-conv nor R-nitpick refuted it, and the judge answered
  `Unprovable` — printed through `warning` unconditionally, not
  trace-gated; its text is the line
  `A guard condition proved before is now refuted by the LLM judge:`
  followed by the guard's subgoals [author 2026-09-14] — and, since
  2026-09-15, also when `guard_simp_tac` rewrote such a guard's conclusion
  to `False` at step 1½ (§5), with `the simplifier` in place of `the LLM
  judge` in that line [author 2026-09-15 "P2 可以写 Refuted、出记录、entry 原是
  Proved 时响亮报警"; the wording: drafter].  Every other ending
  of a call from a `Proved` entry reports as a call without an entry
  does: a refuter's verdict is silent (the refuters are trusted), `Unknown`
  gets the undecided-guard warning [author 2026-09-14 "只有在 previously
  proven but the LLM judge now refutes 的时候说"; "R-conv/R-nitpick 都是靠谱
  的, 都是可信的, 此时就不用报警"].  (Until 2026-09-14 the warning fired on
  every non-`Proved` ending and carried the refuters' and the judge's
  results in a three-arm text the author had not seen; §17 item 13 and
  §31 item 6 record that state.)  [descriptive]
- **`Guard_Record_Stale`**, **the env**, **the run**, **run failure**,
  **record**, **record key**, **final digest**, **tombstone**, **the
  no-cache re-run**, **run lemmas**, **R1–R4**, **the refutation future**,
  **`"quickcut"`**, **`use_cache`**, **`has_record`**, **the lemma counter
  (`trace_ops`, `Guard_Lemma_Counter`, the `iNet`)**: deleted with the
  redesigns (§17, §18).  A guard is decided per call; there is no run-level
  cache state at all, and `gen_reason'` is unchanged.

Retired names — never used below: "owner", "scope", "determination", "the
proving stage", "store key" / `cache_key`, "exit protocol", "defensive
rule" / "no-env case", "blob", "Guard_Fails" / "refutable", "quick mode",
"aux", "evidence", "`NONE` = P-auto", "Actually_Provable", "Refuted" (as the
name of rev 11–13's `Unprovable` verdict), "default" / `"assum"` (refuter
names), "judge" as "one Future per unprovable answer", "async judge", "the
chain", "hooks", "refutation hook chain", `PLPR_Guard_Refuters`,
`Handlers` registry, priorities, `chain_verdict`, `Refutable`,
`judge_group`, `judges`, "judge crash", "merge", "join", "Chain_Ran" /
"Chain_Answered" / `judge_outcome` / `add_refuter` / `run_chain` /
`PLPR_Refuters` / `bound`, "the control-flow classifier" /
`is_control_flow`, "not landed", `\<phi>guard_prove_timeout` /
`\<phi>guard_rconv_timeout` = `\<phi>guard_classic_prover_timeout`, "the
auxiliary-lemma slot", "Guard_Refute_SS" = `Nitpick_Refute_SS`, "type
proof" = `Phi_Proof_Store.proof_cache`, `th` (in `judge_arg`) = `thm`,
"bypass" / `"quickcut"`, `read_record` / `use_cache`, "the env cell blanked
for the judge", `tolerant_time` (never existed in the code; the bound is
`Phi_Proof_Store.replay_limits`), `Guard_Lemma_SS` = `Guard_Lemmas`,
`rejected` (no lemma is ever removed for running away), "reliable" (a flag;
now the `Refuted` / `Unknown` distinction), "Enhancing Simpset" = the lemma
list, `refuter` (the string field; gone with the verdict shape), "the lemma
counter" / `Guard_Lemma_Counter` / the `trace_ops` hook / the `iNet` of
refs (rev 14's mechanism) = the lemma budget, "lemmas as simprocs" (measured
and rejected), `Simplifier_Trace` "displaced" (it is not), `Extern` /
`dest` / `mk` (the codec functor's symbol parameter, withdrawn — §20.2).

## 2. Motivation

~88 % of the corpus's `prove_or_refute` calls end with the guard not
holding (median refuted 607 ms, undecided 2367 ms under today's race).
The redesign pays P-auto's budget — up to `\<phi>guard_classic_prover_timeout`,
400 ms — on every call, hit or not [author 2026-09-08 06:10 "值的"], and
saves the rest: a guard once refuted is answered after P-auto fails, with
no refuters and no warning; a guard once undecided skips the refuters and
only warns (or, with a judge, goes straight to the judge); a guard the
judge once rescued is proved by P-auto with the judge's lemmas.  The first
decision of a guard is slower than today's race: sequential P-auto,
R-conv, R-nitpick — a projected median around 2.8 s for an undecided
guard, and a worst case of `\<phi>guard_classic_prover_timeout` × 2 +
`\<phi>guard_refute_timeout` + 5000 ms × n_goals (~7.8 s at one subgoal at
the §10 defaults); every later run pays P-auto only.  Because P-auto runs
every time, a wrong `Refuted` corrects itself as soon as the guard becomes
provable (a new simp lemma, a changed definition): the store can delay a
proof by at most one P-auto budget, never deny it [author 05:36].
Soundness is untouched: verdicts only select which rules PLPR tries; a
wrong `Refuted` yields a different but valid derivation, never a wrong
theorem.  Guards are load-bearing for phi-system — an over-refuted guard
fails the whole reasoning — so the judge (phase 2's LLM judge) is the
mechanism that corrects over-refutation [author 2026-09-03 12:27;
2026-09-04 03:04].

## 3. Architecture

Three entry points, distinguished statically by which factory instance a
caller uses — no run-time "is there a cache" test anywhere:

```
IN A RUN   (\<condition> ?P, \<condition>[NO_INST] ?P reasoners, PLPR.thy:2005/2008)
  gen_reason' (reasoner.ML:906) — UNCHANGED
    … reasoning …  (state = (ctxt, thm); the ctxt flows from call to call)
      guard_condition_judge = gen_guard_condition_solver guard_digest prove_or_refute
        the factory (§1): quick_cut; under head_only: pre; HEADGOAL case_split;
                     digest d of the whole goal state and the context's assumptions
                     (§1 guard digest); ALLGOALS (insert aux); then, UNSIMPLIFIED,
        prove_or_refute can_inst ctxt d (ctxt0, thm): steps 0–6 of §5 — the entry
             read, its delta applied (ctxt1 returned, ctxt_g the provers' base),
             guard_simp_tac on ctxt_g (enhances internally: Guard_Simp_SS, then
             the lemmas; 60 s of thread CPU — TIMEOUT = warned, state unchanged),
             P-auto (the search, 400 ms), the refuters, the judge (then
             guard_simp_tac again on ctxt_g' and P-auto), the writes.  §5 is the
             one description; nothing is repeated here.
    the run's resulting ctxt leaves gen_reason' with the thm (stateful PLPR);
    at the run boundary the guard-cache export hook carries the lemma list

OUT OF A RUN   (guard_condition_solver' / guard_condition_solver1: four
                command-level callers in Phi_System — local_value.ML:169,
                toplevel0.ML:387, generic_variable_access2.ML:182, :272;
                application.ML:137 is commented out — solving proof
                obligations, `Premise default P` / `Premise MODE_COLLECT P`)
  gen_guard_condition_solver (fn _ => fn ctxt => fn _ => fn (ctxt0, th) =>
      p_auto_attempt ctxt th |> Seq.map (pair ctxt0)):
    same preprocessing (no digest step), then p_auto_attempt — guard_simp_tac
    under its bound and P-auto once, the one definition the method
    \<phi>guard_P_auto also runs — no store; not proved → Seq.empty →
    the caller's error continuation.  A deliberate narrowing: today these
    sites also get a 35 ms auto_search_tac gate (reasoners.ML:1405) and a
    2000 ms P-auto budget (:1421, :1504); all four sites raise `error` on
    failure, so §10 step (5) surfaces any regression as a build failure.

OBLIGATIONS SOLVED ON THE SPOT   (solve_obligation_now, PLPR.thy:1982/1983, from
                defer_premise at :1990 when
                Phi_Reasoner_solve_obligation_and_no_defer is 1 or 2 — set
                by the user's prove_obligations_in_time (PLPR.thy:2017, :2019)
                and internally by rule_generation.ML:443, the only internal
                setter left since SE_Trim_Empty.ML was deleted, commit 11499285)
  gen_guard_condition_solver (fn _ => fn ctxt => fn _ => fn (ctxt0, th) =>
      try_prove_or_give_up NONE fastforce (Guard_Simp_SS.enhance ctxt) th
      |> Seq.map (pair ctxt0)):
    same preprocessing (no digest step), then fastforce — which simplifies
    itself, so no guard_simp_tac before it (§39) — unbounded by default,
    no store; not proved → Seq.empty → backtrack.  No warning.
```

Removed: the `Race.race` call, the three racer wrappers, the in-race
`protocol` var, `\<phi>guard_race_timeout`, the 35 ms gate, and every
asynchronous piece.  Reused: `Hasher`, the proof store (§8),
`eval_prf_str`, `Simpset` (for `Guard_Simp_SS`),
`PLPR_Context_Export` (the hook), `Simplifier.make_simproc`,
`Raw_Simplifier.mksimps` and `addsimps` (the lemma budget), `Strhashtab` of
`Performant_Isabelle_ML`, the R-conv/R-nitpick bodies (screens verbatim),
`RPC_Pretty`'s raw term codec (functorised, §8).  `Phi_Reasoners.wrap`
stays at every registration except the two guard reasoners, which now
take the state directly (§1 `gen_guard_condition_solver`) [2026-09-02 12:08
"registrations unchanged" superseded for these two by 2026-09-04 04:19].

Every caller of the old `guard_condition_solver` must migrate, and the
factory's changed type makes a missed one a compile error.  Known callers
(2026-09-07; re-anchored 2026-09-15): `PLPR.thy:2005`, `:2008` → `guard_condition_judge` on the
state; `PLPR.thy:1982`, `:1983` (`solve_obligation_now`, from `defer_premise` at `:1990`) → the `fastforce`
instance [author 2026-09-03 11:15]; `Test/Guard_Race_Smoke.thy:79` →
migrated at §10 step (2).  `oblg_template`'s three new parameters (§1)
make its other three callers compile errors too: `defer_obligation`
`reasoners.ML:819`, `hammer_obligation_solver` `:850`,
`safe_obligation_solver` `:1651` each pass `I`, `I` and `I`; and
`apply_tac` (`:222-228`), reshaped to run the body outside
`Tactic_Configures`'s hook fold (§1), keeps its three callers `:854`,
`:1625`, `:1658` — the two thm-returning ones pass `I` for `prj` — and
leaves the hook's `state` type and the registration in
`Phi_Envir.ML:336-338` untouched.

## 4. The store, the lemma list, the lemma budget — where they live

Everything new lives in a new `library/guard_cache.ML`, loaded by
`PLPR.thy` immediately after `reasoner.ML` (between `:543` and `:544`) and
before `reasoners.ML` (`:1960`), its only consumer [placement: drafter,
twelfth review — before `reasoner.ML` the name `Phi_Reasoner` is still
`reasoner_decl.ML`'s forward structure, without `info_pretty` and
`\<phi>trace_reasoning`]: the types of §1 (`tier`, `lemma`, `delta`,
`verdict`, `entry`), `Guard_Simp_SS` with its attribute, `Guard_Lemmas`,
`enhance_with_lemmas` with its simproc, the guard-cache export hook,
`\<phi>guard_cache`, the two store functions and the entry codec.  `Guard_Budget`
is a `definition` in `PLPR.thy` before that `ML_file`, hidden at the end
of `PLPR.thy`.  Everything the file needs is in scope there: `Hasher`, the
proof store, `Phi_Sledgehammer_Solver`, `RPC_Pretty` and `Strhashtab`
arrive through PLPR's imports, `Phi_Reasoner` is complete.  `reasoners.ML`
keeps `prove_or_refute`, the factory, the refuters, the judge ref and
`judgement`, `Nitpick_Refute_SS`.

- **Reading**: step 0 of every `prove_or_refute` call, `get_cached_proof
  thy (key d)` decoded by the catch-all decoder (§8); any failure to decode
  is "no entry".  Gated by `\<phi>guard_cache` (read once per call from
  `ctxt0`).
- **Writing**: at the points §5 names, `update_cached_proof thy {id = key
  d, hash = NONE, rewrites = true} (Phi_Proof_Store.zero_times, encode entry)`
  (`cache_file.ML:169`, `:275`) — the whole entry, last write wins; gated
  by the same reading of the switch.  There is no deletion and no
  tombstone: an entry is only ever overwritten [descriptive].
- **Concurrency**: parallel runs (forked proofs, Isa-REPL sessions on one
  theory) read and write the same file; the store's locking
  (`store_append_lock` `cache_file.ML:495`, `with_file_lock` `:445`, lock
  order v → fcntl → `openning_stores`, `:506`, `:585`, `:749-750`) is
  inherited unchanged; two writers of one entry in the same instant produce the same
  content in the common case, and a lost update costs one re-decision.
  Nothing in a call holds mutable state beyond the budget tables of its
  own `enhance_with_lemmas` calls.
- **The lemma list** is `Proof_Data`; it is per ctxt and needs no locking.
  Its writers are §5 step 1 (and step 6's replacement) inside a call and
  the export hook at a run or block boundary; its readers are
  `enhance_with_lemmas` and the hook.  Putting a lemma into it
  makes the ctxt physically new, so `export_context`'s `pointer_eq`
  short-circuit (`context_export.ML:54`) no longer fires for that run and
  the export hooks run at its boundary; the short-circuit stands only for
  a run that returned the incoming context itself — the two short
  circuits of `internal_reason` (`ai-artifacts/STATEFUL_PLPR_REASONING_PLAN.md:286-289`)
  — so a run that allocated or solved a PLPR subgoal (`Subgoal_Env.ML:54`,
  `:62-65`, `:110-113`) fires the hooks whether or not a lemma was
  enabled, and the hook then overwrites the outer list with the exported
  inner one — the inner list minus whatever `export_aux_lemma` refuses
  (§1 the export hook), never longer than it.
- **The lemma budget** lives in the ctxt `enhance_with_lemmas` returns
  and nowhere else: the weakened rules and the simproc with its table in
  that ctxt's simpset, the `\<r>BUDGET` variables among its fixes
  (`Variable.add_fixes`, `variable.ML:480`); no slot of this design and
  no theory data holds any of it.  That ctxt is handed to exactly one
  consumer run and discarded; `ctxt_g`, the ctxt every prover of this call
  starts from, `ctxt1`, which the call returns, and `ctxt`, which the judge
  receives, carry a lemma list and no budget.
  The call is made INSIDE each consumer and nowhere else — `p_auto_tac`
  (§1 P-auto), the R-conv body (§6) and `guard_simp_tac` (§1) each
  call `enhance_with_lemmas` on the ctxt they are handed, once per
  consumer run — so `prove_or_refute` hands the consumers `ctxt_g` and
  never an enhanced ctxt, and a lemma's allowance per consumer run is the
  tier of the entry that first put its statement into the list (§1 the
  export hook).  Nothing global is installed and no theory is derived.
- **Nesting** is nothing special for the store: a nested `gen_reason'`
  inside a call (through the judge, or a reasoner that re-enters PLPR)
  makes its own `prove_or_refute` calls against the same store, and its
  lemma list is the ctxt's.  For the budget, nesting is not designed for
  (§1).

## 5. One `prove_or_refute` call

`prove_or_refute can_inst ctxt d (ctxt0, thm)`, with `ctxt` the guard-side
ctxt (`reasoners.ML:1615`'s, carrying `Guess_Instantiate`'s looper and
solver), `d` the guard digest and `thm` the goal state.

0. **Lookup.**  If `\<phi>guard_cache` is false, `entry := NONE`; else
   `entry := decode (get_cached_proof thy (key d))`.
1. **Apply the entry's delta.**  For each `(stmt, (t, script), tier)` of
   the entry's `added`, in order: `Thm.cterm_of ctxt0 stmt` ("fails to certify" =
   `TYPE`, `TERM` or `THM` — the last from `Goal.init` on a non-`prop` —
   caught with one explicit `handle`, the interrupt family untouched);
   `Goal.init` of the cterm as the goal, `Goal.conclude` on what comes
   back — the standard pair, each layer of protection removed by whoever
   added it; `eval_prf_str`'s own `protect`/`conclude` works on the layer
   it adds [author 2026-09-14 "Goal.init/protect 与 Goal.conclude 是成对的
   啊! 这才是标准做法"; before: `Thm.trivial`]; `eval_prf_str` of `script` with
   `n = 1` under `Phi_Proof_Store.replay_limits t'` (`cache_file.ML:228-230`,
   `:935-939`), where `t'` is the stored `times` `t` with each of its two
   components raised by `Time.max` to at least
   `\<phi>guard_classic_prover_timeout` — the replay floor, read from the
   option, never a literal [author 2026-09-07 13:16, §15.7]; the bound is
   then a thread-CPU budget of `1.5 · #thread_cpu t' + 1 s`, which
   `Thread_CPU.apply` re-scales, and a wall cap of `2 · #wall t' + 3 s`;
   overrunning either, or `Auto_Fail`, is "fails to replay".  The replay
   runs in `ctxt0` exactly as `gen_reason'` holds it — with neither
   `Guard_Simp_SS` nor any lemma of this or an earlier entry enabled, so a
   lemma's replay never depends on the list's order [author 2026-09-03
   13:27] — and `eval_prf_str`'s `Goal.conclude` hands back the plain
   theorem.  A lemma that fails to certify or replay is DROPPED from the
   entry (store write) with **the dropped-lemma warning**: printed through
   `warning` unconditionally, like the loud guard warning, naming the
   lemma's statement and which of the two failures occurred — the theory
   changed under it, or the method text broke the contract of §1 and
   cites a fact this `ctxt0` does not have [author 2026-09-08 06:16 "除非
   a lemma 重放失败, 此时就已经移除并报警"; the gate: drafter].  Then, on
   the lemma list of `ctxt0` — giving `ctxt1`, the ctxt the call returns
   — and on that of `ctxt` — giving `ctxt_g`, the ctxt every prover of
   this call starts from: first every theorem whose proposition is
   `Pattern.equiv` to a statement of the entry's `deleted` is removed,
   whichever guard added it; then the surviving theorems, each with
   `budget tier`, are appended as their replay produced them, one whose
   proposition is already in the list taking this delta's budget instead
   — the one rule of step 1 and step 6 (§1 the lemma list, the export
   hook) [author 2026-09-12; 2026-09-13; §36].  (`ctxt_g`, not `ctxt1`, because the
   guard-side ctxt is where the verdict is earned: `guard_simp_tac` and
   `p_auto_tac` (`reasoners.ML:1074`, `:1088`; until 2026-09-15
   `p_auto_search_tac`) run under
   `Guess_Instantiate.add_guess_inst_looper` (`:1616`) over
   `add_guess_inst_solver … addsimps Premise_def` (`:1615`), installed
   nowhere else since 2026-08-29 (`guess_instantiate.ML:305-311`)
   [drafter, tenth review].)
1½. **`guard_simp_tac` on `ctxt_g`**, once: the simplification of the
   guard with the entry's lemmas enabled (its own `enhance_for_guard`
   call, fresh budgets), under its 60 s (§1 `guard_simp_tac`).  No state
   left (`quick_cut` found `False`) → the simplifier refuted the guard:
   write `{delta, Refuted}`, the decision record with refuter
   `guard_simp_tac`, the loud guard warning if the entry said `Proved`
   (naming the simplifier), return `Seq.empty`; nothing else runs [author
   2026-09-15 "P2 可以写 Refuted、出记录、entry 原是 Proved 时响亮报警";
   until then this ending yielded no verdict, no record and nothing
   written, as the factory's pass had ended such a call].
   Otherwise the state it produced is THE goal state of
   the rest of the call: `goals`, P-auto, both refuters, the judge's
   `thm` and the record's `subgoals` all read it [author 2026-09-15; §39].
   The decision timer starts before it, so `elapsed_ms` includes it from
   now on [drafter].
2. **P-auto** on `ctxt_g` — the search step only, `p_auto_tac`, which
   calls `enhance_for_guard` itself, so the budgets are fresh for this
   consumer run (§4) — under `\<phi>guard_classic_prover_timeout` of
   thread CPU (the `Int.max (1, …)` clamp stays: a bound below 1 ms is
   ignored, `Thread_CPU.apply` as `Timeout.apply`); no simplification
   here (§1 P-auto) [author 2026-09-15];
   `elapsed` is not recorded — nothing stores P-auto's time any more.
3. **P-auto proved** (`solved`): `entry = NONE` or `verdict = Proved` →
   nothing written; `verdict = Refuted | Unknown` → write `{delta, Proved}`
   silently [author 05:53 "当 cached 记录的是 Refuted 但实际 P-auto 跑成功了,
   那么直接静默更新 the store 为 Proved"].  Return `Seq.single (ctxt1,
   solved)`.
4. **P-auto failed**, by the entry:
   - `Refuted` → return `Seq.empty`, silently; no refuter, no judge [author
     05:53 "对于 reliable = true, 我们直接返回 refuted 不报警"].
   - `Unknown` → a judge is installed → step 6; else print the
     undecided-guard warning, return `Seq.empty`, nothing written [author
     05:53; 06:10 "5. 好"].
   - `NONE` → R-conv (on `ctxt_g`; its body enhances itself, fresh
     budgets) refutes → write `{empty delta, Refuted}`, return `Seq.empty`
     silently; else R-nitpick refutes → likewise; else a judge is
     installed → step 6; else print the undecided-guard warning, write
     `{empty delta, Unknown}`, return `Seq.empty`.
   - `Proved` — the lemmas did not suffice → R-conv; else R-nitpick; else
     a judge is installed → step 6 [author 06:10 "补充一点 … 如果 R-conv,
     R-nitpick 都失败了, 还要跑 LLM judge, 然后响亮报警"; "6. 要的"].  The
     loud guard warning belongs to the call's FINAL verdict, and to two
     paths only: a call that started from a `Proved` entry and ends with
     the judge's `Unprovable` (step 6) prints it [2026-09-14], as does one
     that the simplifier refuted at step 1½ [2026-09-15, ruling 10 of §39];
     a refuter's `Refuted` here is silent and `Unknown` (nobody, no judge)
     gets the undecided-guard warning, as without an entry [author
     2026-09-14]; either way write
     `{delta, Refuted | Unknown}` — the delta stays [author 06:16 "lemmas
     始终是不丢的"] — and return `Seq.empty`; when step 6 ends `Proved`, no
     warning [author 08:45].
5. **Writes** are those named above and in step 6, each the whole entry
   under `key d`.
6. **The judge**: `j {ctxt = ctxt, outer_ctxt = ctxt0, can_inst, thm,
   delta}` — `ctxt` the guard-side ctxt as it was before step 1 applied
   this entry's delta, `delta` this entry's delta as step 1 left it, on
   this machine's clock (§1 the judge).
   - `Provable new` → the times of `new`'s `added` are normalised with
     `Phi_Proof_Store.standard_time` first (§1 the judge); then THIS
     ENTRY's delta is REPLACED by `new`, applied as in step 1 (the replay
     floor and `replay_limits` on the normalised times) onto the lemma
     lists of the moment before step 1 — `ctxt0` giving `ctxt1'`, `ctxt`
     giving `ctxt_g'`: `new`'s deletions first, then its lemmas, a
     statement already present taking the judge's budget (the one rule of
     step 1; §1 the judge, author 2026-09-09) — so this entry's survivors of step
     1 are gone unless `new` states them again, an earlier guard's lemma
     stays unless `new` deletes it; a replay failure is an `error` naming
     the judge (§1); then `guard_simp_tac` again, on the rebuilt `ctxt_g'`
     — the judge's lemmas are simp rules, and the one simplification must
     see them — from the state the call was given, NOT from step 1½'s
     result: a rewrite made at step 1½ by a lemma of the old delta would
     otherwise survive the judge's deletion of that lemma, P-auto could
     prove on its strength, and the `Proved` entry written would not
     reproduce on a later call, which simplifies the raw state under the
     new delta alone [author 2026-09-15 "MD1 step 6 从进入 prove_or_refute
     时的原始状态重新化简"; the review's MD1, §39] (no state left → `error`
     "the judge is broken": its lemmas rewrote the guard to `False`)
     [author 2026-09-15 "注意 judge 是会修改 delta 的，于是在修改后我们必须重新
     跑 simpcut 对吗？"]; the judge itself was handed step 1½'s state, the
     one every other consumer of the call sees; then P-auto again, with a fresh time budget and —
     `p_auto_tac` enhancing again — fresh lemma
     budgets.  Proved → write `{new, Proved}` with the normalised times as
     they are, return `Seq.single (ctxt1', solved)` — and no loud warning,
     whatever the entry said [author 08:45].  Failed → `error` "the judge
     is broken" [author 08:45].
   - `Unprovable` → write `{delta, Refuted}` (the delta stays); if the
     entry said `Proved`, print the loud guard warning (step 4); return
     `Seq.empty` — the judge decided [author 2026-09-04 03:04; 06:10 "4.
     对"].

Any non-interrupt exception escaping P-auto, a refuter, lemma enabling or
the judge propagates out of `prove_or_refute` unchanged and becomes the
run's own exception [author 2026-09-03 12:31; 2026-09-04 03:04]; the two
`error`s of step 6 are such exceptions.  An interrupt passes untouched on
every path, with one conversion the plan does not undo: every
`Timeout.apply` in scope — `Performant_Isabelle_ML`'s shadow
(`accounted_timeout.ML:113-133`, `:142-147`) over Pure's — reports as
its own `TIMEOUT` any interrupt in flight once its bound has expired: a
proper interrupt by Pure's rule (`Pure/Concurrent/timeout.ML:48-56`,
`was_timeout andalso was_interrupt`), a flagless cancellation by the
shadow's witness (`:113-133`).  P-auto's bound then reads as "failed" and
the call continues; §6's refuters swallow their own `TIMEOUT` and so
swallow a cancellation landing after their bound; the scheduler's
re-cancellation is what ends the run.  (`accounted_timeout.ML:36-39`
records the accepted residuals, among them a genuine resource failure
after the witness fired being reported as `TIMEOUT`, which a prover reads
as "failed".)  And `eval_prf_str0`'s catch-all re-raises an exception in
which `Interrupt_Family.contains_interrupt` finds an interrupt (the
one-clause change of §9).  Two calls in one run
that meet the same guard share one entry (§1 guard digest) and each
decides it by P-auto [supersedes 2026-09-03 07:54].

## 6. The refuters and the judge

There is no registry and no priority.  Three plain functions, each
bounding itself, in a fixed order — R-conv, R-nitpick, the judge — all on
the run's thread:

| step | what | its own bound |
|---|---|---|
| R-conv | today's `r_conv_racer` body: negate each subgoal, search with `auto_search_tac` in a `Guard_Simp_SS`- and lemma-enhanced ctxt (its own `enhance_with_lemmas`, fresh budgets), with both of its `can_inst` branches as today — the `can_inst = false` one exporting through `outer_ctxt` (`reasoners.ML:1106-1115`, `:1132-1163`) | `Thread_CPU.apply` of `\<phi>guard_classic_prover_timeout` of thread CPU, no wall limit (§1 `guard_simp_tac`); `TIMEOUT` → not refuted [author 2026-09-04 03:23; thread CPU 2026-09-09] |
| R-nitpick | today's screen and Nitpick calls (`reasoners.ML:1459-1478`), subgoals one after another, each Nitpick call with its 2000 ms parameter as today; a `genuine` or `quasi_genuine` answer refutes (`guard_refute.ML:280-281`); R-nitpick's own preprocessing simpset `Nitpick_Refute_SS`; no lemmas | one outer `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms × length goals`, and inside it one `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms` per subgoal — a subgoal's `TIMEOUT` moves to the next; the outer bound normally ends R-nitpick INSIDE the running subgoal and is a real cap: the running subgoal's own request has not fired, so its `Timeout.apply` cancels it, finds `was_timeout` false and releases the interrupt unchanged (`Pure/Concurrent/timeout.ML:48-56`; the shadow re-raises for the same reason, `accounted_timeout.ML:123-131`), the per-subgoal handler does not catch it, and the outer application, whose request did fire, converts it to its `TIMEOUT`; only when an inner timer and the outer fire together does the inner claim the one interrupt and the outer's request get consumed (the accepted residual, `accounted_timeout.ML:36-38`), and from then on the remaining subgoals run under their inner bounds alone, so the total can exceed the net by those bounds; either way → not refuted [author 2026-09-03 13:05; inner bound 2026-09-07 13:00; sequential: drafter] |
| the judge | `!judge`, if `SOME` (§1) | its own |

Where they run: on the `NONE` and `Proved` paths of §5 step 4 the
refuters run before the judge; on the `Unknown` path neither refuter runs
again (they already failed once for this guard) and only the judge is
consulted; on the `Refuted` path nothing runs.  The two warnings have one
call site each, both on the run's thread.  R-conv's and R-nitpick's
bodies, and every hook they reach (`Phi_Guard_Refute.Preprocess_Hooks`,
`Simpset_Hooks`, `guard_refute.ML:179`, `:183`), may re-enter PLPR like
the judge may — a nested call is an ordinary call against the store.

## 7. Recorded honestly, with no rule answering it

- **P-auto runs on every call.**  The steady-state cost of an unprovable
  guard is `guard_simp_tac`'s time (up to its 60 s of thread CPU) and
  P-auto's own, up to `\<phi>guard_classic_prover_timeout`, on every run;
  the store saves the refuters and the warning, not the simplification or
  P-auto [author 2026-09-08 06:10 "值的"].
- **A `Refuted` entry is trusted for what it suppresses, not for the
  verdict.**  The guard is re-tried by P-auto every time, so a guard that
  becomes provable is proved; but a refutation that was wrong from the
  start — R-nitpick's `quasi_genuine`, which `reasoners.ML:1292-1306`
  records can be wrong — suppresses the refuters, the judge and the
  warning until P-auto proves the guard, if ever.  The escape hatches:
  delete the file, or `\<phi>guard_cache = false` [author 2026-09-03
  04:55: no user-facing invalidation feature].
- **An `Unknown` entry warns on every run** where no judge is installed,
  as the first decision did; it never re-runs the refuters.  With a judge
  installed it is the judge's cue: a later-installed judge takes over
  every undecided guard without any file being deleted.
- **A `Proved` entry with an empty lemma list is reachable** (§5 step 3's
  silent promotion), and a `Proved` entry is treated by its verdict, not
  by its lemmas.  So a guard that was once undecided or refuted and then
  proved, and later fails P-auto again, runs the whole refuter chain and
  consults the judge; the loud guard warning is printed only if the judge
  overturns it (§1, 2026-09-14).  Two contexts sharing a digest with
  different provability would flip such an entry back and forth; since
  2026-09-11 the digest includes the contextual assumptions (§1; "2. 不掺"
  had excluded them and was reversed), so two calls share a key only when
  their whole goal state and their assumptions agree, and the aux facts
  stay out because they are derivable.
- **The same guard can get more than one key.**  For a guard that still
  carries schematic variables at the factory, the key includes their
  indices, and — for the variables `oblg_template`'s import fixed, every
  variable on `NO_INST`, only the premise-local and `LPR_ctrl`-annotated
  ones on `\<condition> ?P`, plus any variable whose type mentions one
  of their type variables — the names the import invents from the
  ambient declared-name pool (§1 guard digest); the same guard reached from
  two statements at different indices or under different names gets two
  entries, each paying its own first decision.  Never a wrong verdict,
  only a miss; normalised against neither [author 2026-09-08 12:57;
  15:12].
- **A carried lemma may come back changed.**  A lemma that crosses a phi
  block boundary with the block's `Premise` assumption among its hyps
  returns as `C ⟹ L`, one carrying a type variable the outer ctxt has
  not declared returns with it schematic (§1 the export hook); either
  stays in the list beside the plain `L` the next call replays: two
  rules, two budgets, the conditional one discharging `C` before it
  rewrites.  Accepted (§1 the export hook, §36).
- **Lemmas replayed on every call.**  Each call of a guard with lemmas
  pays their replay (`eval_prf_str`, one per lemma) before P-auto; the
  export hook carries the theorems to later calls along the branch the
  search keeps (a call ending `Seq.empty` takes its `ctxt1` with it), and
  the same call site pays again in every run.
- **A lemma that reaches its budget is cut off, not removed**, so a bad
  lemma costs its budget of rewrites in every consumer run of every guard
  call downstream of the one that enabled it — the rest of the run, the
  following statements of the block, and the out-of-run instance
  `p_auto_solving`, whose `guard_simp_tac` and P-auto enhance with the
  list (the obligation instance stopped being a consumer on 2026-09-15,
  §39 ruling 6) — until a guard's
  delta deletes it (any guard's: the judge names it by its proposition
  AS THE LIST HOLDS IT, read off `get_lemmas` of the judge's ctxt — the
  replay keeps a `⋀n. …` statement as written, a run or block boundary's
  export generalises the binder to `… ?n …`, and the two shapes are not
  `Pattern.equiv` [author 2026-09-13: no special handling, `Pattern.equiv`
  as it is]; §5 step 6) or its own entry's delta no longer adds it.
  Since 2026-09-15 the simplification runs inside `prove_or_refute` on
  `ctxt_g`, after the delta: a call that APPLIES an entry's deleting delta
  at step 1 no longer pays the deleted lemma at step 1½; the call in which
  the JUDGE issues the deletion still pays it at step 1½ (its step 1
  applied the old delta, which added it) and re-simplifies from the state
  the call was given, on `ctxt_g'`, at step 6 (§5).  Until 2026-09-15 the
  factory's pass ran before `prove_or_refute`, on the list before the
  delta, and paid it (measured 2026-09-13 with the looping lemma: the goal
  reached `prove_or_refute` already rewritten).  A lemma met only in a
  subgoal the classical search creates is used by the searches — P-auto's,
  and R-conv's, on the same `ctxt_g` (`Test/Guard_Decision_Smoke.thy`,
  `RR`).  A
  growth rule (`g x = g (g
  x)`) that is cut off after `budget` applications leaves the term it
  grew; P-auto then works on that term and usually fails or runs to its
  timeout — this call ends as a P-auto failure.  A reflexive or
  oscillating pair leaves the term unchanged.  The budget sees applied
  rewrite rules only: a lemma that loops through a simproc, a congruence
  rule, or the classical reasoner is stopped by a clock — in
  `p_auto_tac` and R-conv by `\<phi>guard_classic_prover_timeout`, and in
  `guard_simp_tac` by its 60 s (§1; the 2026-09-08 12:51 bound was
  superseded on 2026-09-11, §33, and the 5 s of that day on 2026-09-15,
  §39).  A conditional lemma
  is charged after its own premises are proved (the budget premise is
  last, §1) — a failed own premise costs nothing; only a `check_conv`
  rejection after all premises are proved costs a unit without rewriting.
  Phase 1 has no producer of lemmas (§9): the exposure begins with §10
  step 2's injected entries and the phase-2 judge.
- **The budget's unit is one consumer run** (one P-auto, one
  `guard_simp_tac`, one R-conv), while the 2026-09-08 measurement counted
  per top-level simplifier invocation; §10 step 3 confirms the tiers on
  that unit.
- **The digest is taken after the case split and before the aux-fact
  insertion**, so a guard `guard_simp_tac` solves outright becomes a
  zero-premise state at step 1½, P-auto succeeds trivially,
  and nothing is written unless the shared entry already says `Refuted`
  or `Unknown`, which §5 step 3 then promotes to `Proved`.
- **Last-write-wins.**  Two runs deciding one guard at once may write
  different entries (one proved with lemmas, one refuted); the later write
  stands and the next call re-decides.
- **The obligation instance's `fastforce`** is unbounded by default
  [author 2026-09-03 12:53]; `guard_simp_tac` — the factory's pass until
  2026-09-15, unbounded until 2026-09-09 — is bounded (60 s of thread CPU)
  wherever it runs, in `prove_or_refute` and `p_auto_solving`; the
  obligation path has no guard-side simplification (§1) — a behaviour
  change on every guard, inside PLPR, not only on the cache path [author
  2026-09-08 12:51].
- Deleting `Race.race` deletes its crash absorption: today an exception in
  P-auto or a refuter is that racer's `Crashed` exit; now it is the run's
  exception (two known instances: the `Option` exception of Pure's
  `assign_result` — `Isabelle2025-2/src/Pure/Concurrent/future.ML:422-432`
  discards a non-`Fail` exception before `the (Single_Assignment.peek
  result)`; root-caused 2026-09-08, `OPTION_EXCEPTION_IN_PROOF_REPLAY.md`;
  the one-line fix is not in this checkout, so the instance is live — and
  `nitpick_params` holding a bad value).  §10 step (5) counts hard failures
  attributable to guard-side exceptions.
- **`Phi_Preliminary.Big_def`** accounted for 66 % of all rewriting in the
  2026-09-08 measurement (a `Big` tower re-unfolded one level deeper on
  every round of some outer loop) — a phi-system performance issue outside
  this plan, recorded here because the measurement found it.

## 8. Persistence

- **The store IS the proof store of `auto_sledgehammer`** — the theory's
  `<thy>.proof-store`, `Phi_Proof_Store` in `cache_file.ML`, unchanged
  [author 2026-09-03 02:18 "我设计的是 proof store 只有一个 entry…"; 03:02
  "proof store 应该只接受 string 对吗？"; 04:33 "Unknown 根本就不应该进 proof
  store"; 04:42 "the default warnner 给的 refuted 应当被一视同仁, 而且应该进
  store"; 10:53 "proof store 中…要多一个字段记录 the lemmas"; 16:00
  `record_key = "PLPRGUARD" ^ Hasher.compact …`; 2026-09-12 "我的本意是你利用
  auto_sledgehammer 的 proof store 啊, 用统一的 .proof-store 文件啊"].  The
  entries therefore live in the tracked `*.proof-store` files beside the
  theories and are committed and shared with the proofs [author 2026-09-12
  "1. 好"]; nothing is gitignored for them.  CORRECTION of the record: from
  2026-09-03 to 2026-09-12 this section described a functor over the store
  body and a second instance writing a gitignored `<thy>.guard-cache`; that
  was a review agent's shape (seventh review U6) adopted by the drafter under
  citations that answered narrower questions (the "gitignore 放
  contrib/phi-system/.gitignore  好的" of 14:57 approved only where a gitignore
  line would go), never the author's design; step 4 implemented it, the
  author rejected it on 2026-09-12 ("纯粹是胡闹…必须撤回这些"), and it was
  reverted (`auto_sledgehammer` commit `316f143` reverted by `5ac4877`;
  `cache_file.ML` is byte-identical to before).  The other two changes that
  revert carried away — the dead `bool` of `openning_stores`'s value triple
  and `compact_store` skipping a missing store file (no `<thy>.proof-store.lock`
  behind a theory that never wrote) — were the drafter's as well and are NOT
  adopted unless the author asks for them.
- **Two entry points**, no new ones [author 2026-09-03 13:19]: read =
  `Phi_Proof_Store.get_cached_proof thy key : proof_cache option`, the entry
  being its string half; write = `Phi_Proof_Store.update_cached_proof thy
  {id = key, hash = NONE, rewrites = true} (Phi_Proof_Store.zero_times, value)`
  (the times half unused).  `invalidate_proof_cache` is not used: nothing is deleted.  The
  key is `"PLPRGUARD" ^ Hasher.compact d`, an id no proof obligation
  produces.  The store's locking, migration, compaction and `at_end` are the
  proof store's, untouched.
- **The proof store's key-collision alarm and guard entries.**  The store
  marks, per session, what it wrote under each key (`written`, the
  `Hasher.string` digest of the text — a `Word64`, SHA1 until 2026-09-13
  [author: "建议用已有的 hash 机制去算而不是用 SHA1, 会更快. 而且只要计算出一个
  Word64, 存储更经济"]) and warns when a second, different write lands under
  a key this session already wrote — built to expose two obligations sharing
  one proof id.  A guard entry is rewritten under its own key by design (the
  drop write and a later write in one call; Unknown → Proved; a judge's
  delta), so `write_entry` says so: `update_cached_proof`'s key record
  carries `rewrites = true`, and such a write is neither checked against
  the marks nor marked; every proof-obligation writer passes `rewrites =
  false` and keeps the alarm [author 2026-09-13 "好的, 赞同, 赞同 rewrites";
  §36 ruling 9].  With the whole-state digest a key repeats within one
  linear run only through a hash collision of the 64-bit digest (the
  author, 2026-09-13: a second statement meeting the same guard has a
  different state, hence a different key; the drafter's contrary example
  was wrong) — and that the alarm could not tell from a rewrite either.
  The store also drops a theory's marks whenever the theory is begun again
  in the process (a re-executed header, a changed import, a reload), not
  only at its end [author 2026-09-13; §36]; a PIDE evaluation
  cancelled mid-theory and resumed does not begin the theory again, so one
  stale mark can survive there and cost at most one spurious warning
  [review 2026-09-13; the author: old and new PIDE versions of one theory
  are to be ignored].  The whole mechanism is a debugging aid for the
  key mint and runs only under `ML_debugger`, read at each write — a normal
  build computes no digest and keeps no marks [author 2026-09-13 "这个撞键警
  告建议仅在 ML_debugger 设置为 true 时激活"; "注意是运行时的 ML_debugger 取值而
  非编译时"]; its warning is the four lines the author fixed that day ("Proof
  store: two different proofs were written under one proof id in this
  session." / id / first / now — "就够了, 底下的全都不用").
- **Entry value**: `{delta = {added : (term * proof_cache * tier) list,
  deleted : term list}, verdict}` packed as the triple (added, deleted,
  verdict) with the mlmsgpack packers through a `BytesIO` outstream and
  taken as a string (`encode_record`'s shape, `cache_file.ML:104-111`)
  [author 2026-09-03 05:42; the shape 2026-09-08 06:16, 08:20, 08:37; the
  delta 2026-09-12].  A
  `proof_cache`'s `times` as `packPair (packInt, packInt)` of
  `Phi_Proof_Store.ms_of_times t` and back through `times_of_ms` (`:172-173`,
  `:279-281`) — the store's own one-slot convention, `(cpu_ms, wall_ms)`
  (`:326`, `:332`), and the order only those two functions spell out
  (`:167`); `tier` and `verdict` each as an int tag like `PUT`/`TOMB` [author
  2026-09-03 13:19]; a lemma's `term` through the term-codec functor
  `RPC_Term_Codec (MP : MESSAGE_PACK)` (`Isabelle_RPC/Tools/pretty.ML:42-101`,
  the constructor-tagged structural codec; name: drafter) — which, since
  the preparatory phase (§10 step P, done 2026-09-09), carries a runtime
  symbol as its identifier (tag 9, `Phi_Tool_Symbol.dest_symbol` on the
  way out at `:68-71`, `mk_symbol` on the way in at `:97`), honouring
  `SSymb.thy:19-21`'s invariant that a symbol's per-process numeral is
  never persisted, exactly as `Hasher.hash_term` does (`Hasher.ML:184-186`);
  the functor takes NO symbol parameter, since `Phi_Tool_Symbol` is
  visible where the codec lives [author 2026-09-08 15:12 "很好" to the
  drafter's withdrawal of that parameter].  Its two instances:
  `RPC_Pretty` applies it to `MessagePackBinIO` (`pretty.ML:392-393`) and
  keeps its names and signature (`:7-10`); `RPC_Pretty_Bytes` [name:
  drafter] is the `MessagePackBytesIO` instance (`:105`).  `MESSAGE_PACK`
  is the `MessagePack` functor's result signature, extracted with `type
  instream` / `type outstream` of its own (`mlmsgpack.sml:3-103`); the
  functor is ascribed `:> MESSAGE_PACK where type instream = S.instream
  and type outstream = S.outstream` and realises both types first
  (`:105-117`), so `Pack.packer` / `Unpack.unpacker` stay transparent for
  the three instantiations (`:1013-1015`), untouched.  `mlmsgpack.sml` and
  `ssymb.ML` are both loaded by `Performant_Isabelle_ML.thy` (`:42`, `:34`).
  The functor stays in `Isabelle_RPC` for now and moves to
  `Performant_Isabelle_ML` after this plan [author 2026-09-03 13:19;
  13:27; 14:19].  Kept over Pure's
  `Term_XML.Encode.term_raw` + YXML [author 2026-09-07 13:15 "否决. 那个性
  能很慢的"]; measured 2026-09-07 on `Phi_System_Base` (5000 theorem
  propositions; the 500 largest): msgpack encodes 1.6–2.3× faster and in
  half the bytes; its decode through today's `BinIO.StreamIO` lazy
  instream measured slower, which the `BytesIO` instance removes
  (`ai-artifacts/Term_Codec_Bench.thy`).  NO format version [author
  2026-09-03 03:02]: the decode is wrapped `\<^try>\<open>SOME (decode v)
  catch Subscript => NONE | U.Unpack => NONE\<close>` — a truncated payload
  raises `Subscript` out of `BytesIO.inputN` (`mlmsgpack.sml:929-935`), a
  foreign or outdated one `Unpack`; both mean "there is no entry" and the
  call decides afresh and overwrites the key; any other exception is a
  bug and propagates [author 2026-09-14 "赞同 (a) + (c)": silent, and the
  handler narrowed from the drafter's catch-all].
- `\<phi>guard_cache` (default true) is the one debugging switch [author
  2026-09-02 10:41]; off = no entry is read and no entry is written, every
  call decides as if it had no entry [author 2026-09-03 12:52]; the
  store's `at_end` still loads and compacts an existing file, because the
  switch gates nothing inside the store (above).

## 9. Phase 2 (deferred) and phase-1 enablers

Phase 1 lands: the `eval_prf_str` tracing line behind a verbosity gate
[author 2026-09-02 10:29]; `Guard_Simp_SS` with its attribute and its
consumers (§1); the lemma list, `enhance_with_lemmas` with the lemma
budget, `Guard_Budget`, and the guard-cache export hook; the
`Nitpick_Refute_SS` rename; the judge ref (default `NONE`) and its types;
the whole lemma path (the entry's delta, enabling, the budget, the
export, the judge's delta) exercised by §10 step (2)'s injected
entries and a test judge — phase 1 has no producer of lemmas, and
everything must be ready before the LLM judge [author 2026-09-07 13:15 "在
做 LLM judge 前一切都要就绪"].  Phase 1 makes exactly TWO behaviour-changing
changes to existing code outside PLPR: (a) the exception to [author
2026-09-03 12:59–13:01] — in `eval_prf_str0`'s catch-all clause
(`sledgehammer_solver.ML:634-636`), `| err => if
Interrupt_Family.contains_interrupt err then Exn.reraise err else <today's
body>`, so that a `Par_Exn` wrapping an interrupt is no longer relabelled
`Auto_Fail (Unknown …)`; every `eval_prf_str` caller (the proof store's
replay, AoA) thereby propagates such an interrupt instead of starting a
fresh search on it [author 2026-09-08 02:37 "我认为这挺好的, 为什么不采纳
呢?"]; (b) the `at_end` gate on `compact_store` (§8, drafter, vetoable in
§10), which also affects the existing proof-store instance.  The purely
additive changes outside PLPR are `Hasher.terms` (§1), the store functor
at §10 step (4), and the preparatory phase's `MESSAGE_PACK` extraction
and term-codec functor.  Before phase 1, the **preparatory phase** (§10
step P) changes three repositories below phi-system on the author's
order [2026-09-08 15:05 "我们能否把 Symbol 的 ML code 挪动进 Pure 上, 而只是把
逻辑定义在 HOL 上"; 15:06 "我建议把这个设置为一个准备阶段先去做"]:
`Phi_Tool_Symbol`'s ML moved from the HOL half of `Performant_Isabelle_ML`
to its Pure half, `RPC_Pretty`'s raw-term codec became the functor of
§8 with the symbol clause, and Isa-Mini's copy of the codec became an
instance of it (done and accepted 2026-09-09, §26).  None of this changes any behaviour PLPR sees, and the
symbol clause alters no live protocol: `pack_raw_term`'s callers outside
`pretty.ML` are `Isa-REPL/library/REPL_serializer.ML:41-42`, a re-export
whose one consumer is `tasks/extraction/theorem-relevance/extraction.ML:244-245`
(a wire whose Python end stores the payload and hands it back to ML
unread), and `evaluation/MLML_Verify/verify_proof_app.ML:33`, `:36`
(likewise carried back unread); Isabelle_RPC's Python side decodes no raw
term; and on both wires a term holding a runtime symbol — which by
`SSymb.thy:19-21` must not cross a process as a numeral anyway — now
packs as its identifier or, if its numeral is unregistered in this
process, raises from `revert_symbol1` (`ssymb.ML:71-74`) instead of
silently shipping the numeral.  Phase 2 is the LLM judge: a function of `judge_arg -> judgement`
installed into the ref, answering `Provable` with lemmas and their tiers,
or `Unprovable` [author 2026-09-02 07:39; 2026-09-04 03:04; 2026-09-08
06:14, 08:19, 08:34], under the contract of §1; installing it needs no
file to be deleted — `Unknown` entries consult it, `Proved` entries that
stop proving reach it, `Refuted` entries never do.

## 10. Configuration, drafter decisions, implementation order

| option / constant | default |
|---|---|
| `\<phi>guard_classic_prover_timeout` | 400 ms of thread CPU, provisional — P-auto's and R-conv's budget [author 2026-09-04 03:23 "直接重命名为 \<phi>guard_classic_prover_timeout"] and the replay floor of §5 step 1 [author 2026-09-07 13:16]; NOT `guard_simp_tac`'s bound — that is 60 s of thread CPU fixed in the code, no option (§1 `guard_simp_tac`, §39) [author 2026-09-15 "赞同", superseding the 5 s of 2026-09-11 and the 2026-09-08 12:51 bound]; thread CPU, never wall clock, an error without a CPU clock [author 2026-09-09]; the `is_F` shortcut is deleted (§39) |
| `\<phi>guard_refute_timeout` | 2000 ms (Nitpick's parameter; R-nitpick's outer net is `\<phi>guard_refute_timeout + 5000 ms × length goals`, and each subgoal inside it is bounded by `\<phi>guard_refute_timeout + 5000 ms`) |
| `\<phi>guard_cache` | true |
| `\<phi>log_guard_race` → `\<phi>log_guard_decision` → deleted | the `guard_decision` record is written under the runtime `ML_debugger` option, no option of its own [author 2026-09-14 "建议用 ML_debugger 这个 configuration option 来控制"]; `\<phi>log_guess_inst` the same way |
| `\<phi>guard_lemma_apply_limit` | 1000 — the budget of `Frequent`, the ceiling of every tier [author 2026-09-08 07:44 "我们只给一个 1000 的上限"] |
| the tier budgets (ML constants) | `Only_Once` 3, `Rarely` 30, `Normal` 300, `Frequent` = the option [author 08:19, 08:20] |

Names approved [author 2026-09-03 04:58, 11:11, 11:15; 2026-09-04 03:23;
2026-09-08 07:45 "赞同" (the naming table), 07:48 (`Guard_Lemmas` in place
of a simpset), 10:53, 11:32 (`Guard_Budget`, `\<r>BUDGET`)]; ML identifiers not
named by the author are the drafter's under the 11:24 delegation (among
them the judge ref's name and module, `guard_cache.ML`,
`enhance_with_lemmas`).

Pending the author: nothing of this plan's design (the provenance audit's
items were ruled one by one on 2026-09-14, §37).  Deferred by ruling: the
tier measurement (§33; "(a)" — after step 5), the `\<check> \<hypothesis>
\<consistency>` follow-up (§33; a plan of its own after step 5), phase-2
point 2 (`Frequent` = the ceiling; §37).  Next: step 5.  (Rev 18–25 said
"Nothing is pending the author" while §35 and §8 held open items —
audit A10.)

**Drafter decisions that change behavior**, each vetoable (those ruled on
2026-09-14 are marked; §37): the file
`guard_cache.ML` and what it holds (§4); the shape of the ctxt threading
through the factory — `oblg_template` polymorphic through `inj`, `on_thm`
and `prj`, bypass exits (the zero-premise arm of `head_only` among them)
paired with `ctxt0`, `head_only`'s `Goal.conclude` on the thm half,
`SOLVED'` through `prj`, and `apply_tac` running the body outside
`Tactic_Configures`'s hook fold, so a hook's `Success` no longer replaces
the body (§1); the digest step as an optional factory parameter, passed
by `guard_condition_judge` only (§1); the `guard_simp_tac` timeout yielding
the state unchanged (§1); the provers run from `ctxt_g`, the guard-side
ctxt plus the lemmas (§5 step 1); the lemma replay in `ctxt0` with
nothing enhanced (§5 step 1); the append skipping a proposition already
present (§1, §5 step 1); the dropped-lemma warning's gate
(`warning`, unconditional — §5 step 1) [ruled 2026-09-14 "可以保留无条件"];
`enhance_with_lemmas` extracting
rules with `mksimps` first, rotating the budget premise last, and adding
by `addsimps`, with fresh budgets per consumer run (§1); the one simproc
per `enhance_with_lemmas` and its `Strhashtab` (§1); the export hook's
priority and its overwrite (§1) [priority 200 ruled 2026-09-14 "200 可以
的"; the overwrite was ruled 2026-09-04]; the exact exceptions of "fails to
certify" and "fails to replay" (§5 step 1); U3 (the factory parameter's
type — §1); the sequential order of R-nitpick's subgoals inside its net
(§6); `zero_times` / `hash = NONE` in the entry write (§8); the catch-all
decode (§8) [ruled 2026-09-14: silent, narrowed to `Subscript` and
`Unpack`]; the `SSymb.thy` certification assertion over
`Phi_Tool_Symbol.constants`, the tag number of the symbol clause, the
name `RPC_Pretty_Bytes`, and the codec functor with its `MESSAGE_PACK`
extraction done in step P rather than step 4 (§8, §10); the store functor's
argument list and the narrowed guard signature (§8); the `at_end` gate on
`compact_store` only (§8, §9); the `guard_decision` record's fields, and
that it is a permanent record rather than temporary measurement code
(below).

Instrumentation is temporary measurement code [author 2026-09-03 04:01].
One record is permanent: `guard_decision` (the verdict, the path taken —
hit kind, which refuter, judge asked — elapsed, `Hasher.hex` of the guard
digest and n_goals; no lemma count — the drafter's "number of lemmas
enabled" was deleted [author 2026-09-09 "(2)"], and how many reached
their budget lives in the simprocs' closures, which no channel §4
permits carries out), written by `prove_or_refute` under the runtime
`ML_debugger` option — its own switch `\<phi>log_guard_decision` deleted
[author 2026-09-14 "建议用 ML_debugger 这个 configuration option 来控制, 可以保留
为永久"; the fields, chosen by the drafter, shown to the author and kept].
`Hasher.hex` appears in exactly that line of the permanent code.

Order:

P. **The preparatory phase** — DONE 2026-09-09 and accepted by the author
   ("验收通过"; §26 records the acceptance evidence) before step 0, and
   reviewed with this plan [author 2026-09-08 15:06 "我建议把这个设置为一个
   准备阶段先去做"; 15:12 "先把它写进 rev 17, 随第十五轮评审一起过一遍"].
   What was done, with the anchors as they stand now:
   (a) `Performant_Isabelle_ML/library/ssymb.ML` is loaded by
   `Performant_Isabelle_ML.thy:34` (the Pure session) instead of
   `HOL/SSymb.thy`; its nine antiquotation occurrences became the literal
   strings and type they resolved to — `symbolT = Type ("SSymb.symbol",
   [])`, the six digit names and `zero = Const ("SSymb.Z", symbolT)`
   (`ssymb.ML:34-36`), the shape `ssymb_syntax.ML:12` already used —
   since the file builds and inspects terms structurally and consults no
   theory; the process-global table (`:54-57`) is unchanged.  `decode`'s
   first clause (`:45-46`) tests `t aconv zero` instead of repeating the
   name in a pattern (a val-bound name in an ML pattern would bind, not
   match), so every constant name occurs exactly once, in a constant the
   file builds.  `ssymb_syntax.ML` (`\<^term>\<open>0::nat\<close>` and
   HOL's numerals) stays in `SSymb.thy` (`:97`).  The logical definitions
   (`typedef symbol`, `Z`, `A` … `F`, the three simp groups,
   `symbol_digit_eval`) stay in `SSymb.thy`, which gained, after them and
   before its `hide_const` (`:105`), one ML assertion (`:103`) that
   certifies with `Thm.cterm_of` every constant `ssymb.ML` builds —
   `ssymb.ML` exports them as `Phi_Tool_Symbol.constants` (`:37`; name:
   drafter): `zero` and the six digit constants over `symbolT -->
   symbolT` — so a renamed or retyped constant fails where it is defined,
   which with the names occurring only in those constants is the check
   the antiquotations used to give at ML compile time; state-free, unlike
   a probe through `mk_symbol`, which on a fresh table builds only `Z`.
   (b) The codec: the `MESSAGE_PACK` extraction from `mlmsgpack.sml` and
   the term-codec functor `RPC_Term_Codec` over it, both exactly as §8
   records, with the runtime-symbol clause in the functor body:
   `dest_symbol` answers `SOME id` → tag 9 with `id`; tag 9 → `mk_symbol`
   — the clause Isa-Mini's copy already carried; the two instances
   `RPC_Pretty` (`MessagePackBinIO`, keeping its names and the signature
   `pretty.ML:7-10`) and `RPC_Pretty_Bytes` (`MessagePackBytesIO`,
   `:105`).  Isa-Mini's copy lived inside `functor MiniLang_Agent_Pack(S)`
   (`agent_packer.ML:23-31`, `structure MP = MessagePack(S)` at `:31`),
   instantiated at both `BinIO.StreamIO` and `BytesIO` (`:315-316`), so
   no monomorphic codec could replace it: the copy was deleted and the
   functor body applies the term-codec functor to its own `MP`
   (`structure Codec = RPC_Term_Codec(MP)` at `:32`, opened at `:43`),
   which matches `MESSAGE_PACK` by §8's `where type` ascription; the
   `MINILANG_AGENT` signature and every caller are unchanged.  The third
   transcription,
   `Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML:30-73`,
   sits inside the block comment opened at `:29` and closed at `:74`: it
   compiles nothing and persists nothing, and `RPC_Pretty` is already in
   scope there (`Semantic_Embedding.thy:2` imports
   `Isabelle_RPC.Remote_Procedure_Calling`), so nothing was done to it.
   (c) Acceptance, all passed (§26): `Isabelle_RPC_Test`, which gained the
   permanent theory `test/Test_Term_Codec.thy` — a round trip of a term
   through each instance, and one of a term holding a symbol whose decoded
   `dest_symbol` is the original identifier and whose wire holds the
   identifier and no `SSymb` constant name; Isa-Mini's packer round trip
   as a no-regression check, on the rebuilt `Minilang_AoA` heap.  Cost as
   observed: `Performant_Isabelle_ML` and `Isabelle_RPC` have no heap of
   their own under Isabelle2025-2 — every session above reaches them by a
   `sessions` clause and loads their theories from source — so the
   rebuild (on the author's approval, 2026-09-09) covered
   `Performant_Isabelle_HOL`, `Auto_Sledgehammer`, `Minilang`,
   `Minilang_AoA`, `Isabelle_RPC_Test` and `Phi_System_Base` in 1 m 44 s.
0. Re-verify every line anchor individually — §1's and §3's included, the
   `Phi_System` caller list among them; the tracing gate.  `cache_file.ML`
   moved after the plan's first anchor date and may move again: re-anchor
   it by symbol lookup, never by offset.
1. `Hasher.terms : term list -> digest` in `HASHER` and
   `contrib/auto_sledgehammer/library/Hasher.ML`; the one clause in
   `eval_prf_str0` (§9); `Guard_Budget` in `PLPR.thy` and its `hide_const`;
   `library/guard_cache.ML` (the types, `Guard_Simp_SS` with its attribute,
   `Guard_Lemmas`, `enhance_with_lemmas` with the simproc and the budget
   table, the export hook, `\<phi>guard_cache` — the store instance and
   the codec wait for step 4); the factory: `gen_guard_condition_solver`
   parameterised, the digest step between the case split and the
   insertion, the `guard_simp_tac` bound, `oblg_template` with `inj`, `on_thm`
   and `prj` and its three other callers, `apply_tac` reshaped around the
   `Tactic_Configures` fold with its two other callers;
   `try_prove_or_give_up`; `p_auto_body` (since renamed `p_auto_tac`, §39
   ruling 5) and `\<phi>guard_P_auto`'s
   `method_setup`; the `Guard_Simp_SS` and `enhance_with_lemmas` sites; the
   `Nitpick_Refute_SS` rename; `guard_condition_solver'`/`1` on P-auto; the
   `fastforce` instance for `defer_premise`; the two warnings as functions;
   the obsolete comment at `reasoners.ML:1218-1224` (the `nitpick_params`
   note that assumes a racer body) rewritten.  The
   `Hasher.ML` and `sledgehammer_solver.ML` edits are inside the
   `Phi_System_Base` heap: this step needs the author's explicit approval
   to rebuild `Phi_System_Base` before it can be exercised (as §15.10
   records was done once).
2. `prove_or_refute` over `context_state` with an in-memory table in place
   of the store (a test-injected `Symtab`, so that every path of §5 —
   hits of each verdict, lemma enabling, a looping lemma cut off by its
   budget, the judge replacing lemmas, both warnings, both `error`s — is
   exercised by `Test/Guard_Race_Smoke.thy` reshaped around
   `guard_decision`); `guard_condition_judge` registered on the state;
   migrate every caller (§3); `guard_decision`, and with the rename of its
   switch the clause `\<phi>log_guard_race = true` is DELETED from
   `PLPR.thy`'s `declare` (the `\<phi>log_guess_inst = true` clause beside
   it was then left as another subsystem's and was deleted on 2026-09-11,
   §33; the switch itself went with §37 item 1), so `\<phi>log_guard_decision`
   keeps its default `false`; step 5's harness enables it itself.
3. The export hook end to end: a lemma enabled at one call reaching the
   next call and the next statement (the V2 smoke test of the stateful
   PLPR plan as the model); the budget measured on the corpus with
   test-injected lemmas at each tier to confirm the tier numbers on the
   budget's own unit (one consumer run), not only on the 2026-09-08
   per-invocation sample.
4. Persistence: entries as records of the theory's proof store (§8), the
   entry codec (over `RPC_Pretty_Bytes` from step P), the read at step 0
   and the writes of §5 replacing the table of step 2.
   (The gate of rev 11–13 — proceed only if record keys repeat across
   runs — is deleted: the key is the guard's own digest and repeats by
   construction [author 2026-09-08 07:38 "赞同删掉"].)  The
   `cache_file.ML` edit is inside the `Phi_System_Base` heap: this step,
   like step 1, needs the author's explicit approval to rebuild
   `Phi_System_Base` before step 5 can run.
5. Corpus acceptance: a cache-on and a cache-off leg, a concurrent Isa-REPL
   leg, a consecutive-run leg with a hit-rate floor; measure wall time,
   verdict flips per guard cache-on vs cache-off, first-decision latency,
   the path distribution (hit kinds, refuters, judge), lemma replay cost,
   budget cut-offs, hard failures attributable to guard-side exceptions,
   digest cost, store I/O, the forked-proof write, the guard-cache export
   hook's cost per run boundary; re-measure 400 ms.  Testing via Isa-REPL
   against `Phi_System_Base` sources — no `isabelle build` beyond the two
   approved rebuilds of steps 1 and 4.  (Rev 18–26 added "with AoA
   escalation disabled in the harness": the drafter's assumption that the
   AoA gate is closed under Isa-REPL, which it is not — by design [author
   2026-09-14 "AoA 应该在 Isa-REPL 下工作的, 这是 expected"]; a corpus whose
   obligations are all in their stores never reaches the gate, and the
   2026-09-08 probe cost money only by copying a theory under a new name
   and defeating its store.)

After this plan: move the raw-term codec functor to
`Performant_Isabelle_ML` [author 2026-09-03 14:19].

§11–§19 below are the rulings of the earlier designs.  §17 supersedes the
run-level rulings of §11–§16; §18 supersedes §17's `trace_ops`-hook counter
and its `iNet`; §19 supersedes the unbounded "G.simpcut" pass [author
2026-09-03 12:53, §7]; §20 adds the preparatory phase and supersedes
nothing; §21–§25 are drafter fixes only; the rest stand.

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

## 17. Redesign rulings — the cache stores advice (2026-09-08, 05:07–08:45)

The eleventh review (`wf_4df2634b-443`, rev 13) returned NOT_READY with
three majors: `tolerant_time` does not exist (`Phi_Proof_Store.replay_limits`
is the bound); `Thm.trivial`'s `THM` was unclassified; and runs of
`PLPR_Exhaustive.reason_exhaustively` (`exhaustive.ML:66-73`, the deriver
path) end `NONE` on success, so the run-level cache was structurally dead
for them.  Explaining the third led the author to redesign:

1. **Per-call validation first** [05:07 "我认为我们的方案需要大改 … 需要放在每个
   prove_or_refute 内"; 05:12 "整条 run 的成功的定义可以简化为每次 prove_or_refute
   上的 digest 检验都通过"] — then superseded within the hour by:
2. **The cache stores advice, never a verdict; P-auto decides on every
   call** [05:36; 05:53 "如此一来, 整个缓存失效机制也不需要了 … 所谓 cache 只是
   提供 the additional lemmas"].  Every digest of the reasoning path, the
   env, `Guard_Record_Stale`, tombstones, the no-cache re-run, R1–R4,
   `use_cache`, `has_record` and run failure are deleted; `gen_reason'` is
   untouched; the exhaustive-run finding is moot.
3. **No asynchrony at all: the refutation future and `"quickcut"` are
   withdrawn; R-conv and R-nitpick run inline, in sequence** [05:53 "此外我
   提议撤销异步 warning 的那个机制"].
4. **The hit protocol** [05:53; supplemented 06:10]: cached `Proved` whose
   lemmas no longer suffice → R-conv → R-nitpick → the judge → the loud
   guard warning; cached `Refuted` and P-auto fails → silent; cached
   `Unknown` and P-auto fails → the judge if installed, else the warning
   only; cached `Refuted`/`Unknown` and P-auto succeeds → silently
   `Proved`.  Lemmas are never lost by a verdict change [06:16].
5. **The steady-state cost — P-auto on every unprovable guard — accepted
   without measurement** [06:10 "值的. 不需要测量. 相信我是值的"].
6. **The store is keyed by the guard's digest, not by run** [06:10 "1. 同
   意"]; **no ctxt assumptions in the digest** [06:10 "2. 不掺"] — REVERSED
   2026-09-11: the digest is the whole goal state plus the contextual
   assumptions (§1, §33 item 4); **the
   digest is taken before "G.simpcut"** [07:05 "赞同"]; the out-of-run
   instances never touch the store [07:34]; the persistence gate of §10
   step 4 deleted [07:38 "赞同删掉"].
7. **`Proved | Refuted | Unknown`** [06:10 "3. 好的"]; `Refuted` = a refuter
   or the judge's `Unprovable` [06:10 "4. 对"]; no entry for a guard P-auto
   proves without lemmas [06:27 "1. 不用写"].
8. **The judge returns lemmas only** — no `proof`, no returned state; P-auto
   is re-run with them on the spot [06:14 "赞同"]; the judge ignores the
   entry's lemmas and its list replaces them [08:34]; a lemma of the judge
   that fails to replay, or a `Provable` after which P-auto still fails,
   is an `error` naming the judge [08:45].  Lemma accumulation and
   `Pattern.equiv` deduplication [06:16, 06:19] are thereby withdrawn.
9. **A lemma has an application budget, chosen by the judge from four
   tiers** — `Only_Once` 3, `Rarely` 30, `Normal` 300, `Frequent` 1000 —
   under a ceiling option [07:44; 08:19; 08:20 "Only_Once 给 3"].  Measured
   basis: `ai-artifacts/simp_count_report.txt` (legitimate rules 100–895
   per invocation; only `One_nat_def` beyond 1000).
10. **A lemma that reaches its budget is simply not applied any more in
    that P-auto call; nothing is removed, nothing is written** [07:08;
    08:34 "就别移除了. 改为超过后就禁止使用此 rule"].  The `rejected` field,
    `judge_arg.rejected` and the re-proposal rule are withdrawn.
11. **The counting hook may displace `Simplifier_Trace`** [07:05].
12. **The lemmas live in a `Proof_Data` theorem list, not a simpset**
    [07:44 "新建一个 … 专门去存储 the proposed lemmas"; 07:48 "只要 a Proof
    Data storing a list of thms 就够了"]; the naming table approved [07:45
    "赞同"], `Guard_Lemma_SS` replaced by `Guard_Lemmas`.
13. **The loud guard warning** is unconditional (`warning`, not
    trace-gated), carries the refuters' and the judge's results, and fires
    only when the call finally ends `Refuted` or `Unknown` [07:45 "好";
    08:45] — narrowed 2026-09-14 to the judge's `Unprovable` alone, the
    results sentence dropped (§1, §37).
14. Process: the drafter must not relay an agent's progress ticks [07:41,
    07:46]; the 2026-09-08 rewrite-count probe cost ≈ $23 in LLM calls by
    defeating the proof store of a copied theory, and its semantic-DB
    residue (126 records of `Draft.Simp_Count_Probe` and
    `PhiSem_Aggregate_Tuple`) was removed on the author's order [08:23];
    the file residue stays [08:23 "没事, 别管"].

Eleventh-review findings folded in where they survive the redesign:
`replay_limits` in place of `tolerant_time` (§5 step 1); `THM` in the
certify class (§5 step 1); `Timeout` is the `Performant_Isabelle_ML` shadow
(§5); `Guard_Lemmas` holds theorems as given (the `simp_rules` finding is
moot); `Hasher.terms` outside PLPR named honestly (§9); the `MESSAGE_PACK`
body realizations (§8); the judge's raw times normalised at the write (§5
step 6); the refuters may re-enter PLPR (§6).  Moot with the redesign:
`install` and the sequent, the nested-`NONE` third outcome, the
`pointer_eq` note as a cost, the lemma bound raw-vs-standard at recording
(one write point, §5 step 6).  Discarded with the review: the two attacks
on the factory contract (misreading "the template" as `oblg_template`
alone), the R-nitpick arithmetic, the R-conv freeze-branch and clamp
claims, `Par_Exn` "cannot wrap an interrupt", step 1 "breaks PLPR" (the
compile error is the migration mechanism).

## 18. Twelfth-review rulings — the budget inside the simpset (2026-09-08, 09:34–11:52)

The twelfth review (`wf_1b490152-585`, rev 14, scoped to §1/§3/§4/§5/§6/§8):
NOT_READY, 17 upheld (2 blockers, 6 majors, 9 one-sentence fixes; all
DRAFTER_FIX), 1 relaxation proposal, 16 discarded, 2 dirty hacks; the two
blockers re-verified by the drafter (`Pure/context.ML:786-791`,
`raw_simplifier.ML:346-352`).  Rulings:

1. **The lemma budget is enforced by weakening each lemma to a conditional
   rewrite rule `Guard_Budget \<r>BUDGET<i> ⟹ P` and discharging the premise
   with one context-local counting simproc** — no `trace_ops` hook, no
   theory data, no derived theory [10:53 "好吧, 我赞同你的方案"].  Basis:
   the hook is `Theory_Data` kept by the FIRST parent on a merge and lost
   under `Phi_Preliminary`; a per-call derived theory makes sibling
   theories whose certificates cannot be joined (`context.ML:483-495`,
   `:663-669`); "all lemmas as simprocs" measured and rejected
   (`ai-artifacts/Lemma_Simproc_Probe.thy`: tried after every rewrite rule,
   loses ordered rewriting and `mk_eq_True`, invisible to
   `Simplifier_Trace`, ~1.6× per application, re-implements
   `decomp_simp`/`rew`) [09:34 "我以为这个钩子只是临时作用于 prove_or_refute 中的, 可以实现这个临时
   吗?"; 09:39 "与其这么麻烦还不如所有的 lemmas 全部变 simproc / run an agent
   看一下" → 10:53 the alternative accepted].
2. **`Guard_Budget :: ind ⇒ bool`; the index is a fresh fixed variable
   whose name is the key; `hide_const (open) Guard_Budget` at the end of
   `PLPR.thy`** [10:53 "那个前件得是 Guard_Budget :: ind => bool … 我们直接使用
   the variable 的名字来做 index … hide_const (open) Guard_Budget"].
3. **The prefix `\<r>BUDGET`**, after `Subgoal_Env`'s `\<r>GOAL` [11:32 "赞
   同 \<r>BUDGET"]; **decimal indices** [11:40 "赞同十进制"]; **the budget
   table keyed by the returned internal name in a `Strhashtab`, held by the
   simproc's closure, not parsed and not stored in the ctxt** [11:46 "要不直
   接用 Strhashtab 吧"; 11:40 "那个数组是作为闭包参数给进 simproc 的, 是不进
   ctxt 的"].
4. **Nesting is not handled; a comment suffices** [11:44 "你不用担心嵌套的问
   题. 你可以 leave a comment 但 simproc 是不会回调 PLPR 的"].
5. **The guard digest is taken after the case split and before the
   aux-fact insertion**, `reasoners.ML` between `:1827` and `:1828`, in
   the `guard_condition_judge` instance [11:48 (the line asked for); 11:52
   "确定一下, 实际上是我们当初提议的那个 guard_condition_judge 里, 对吗?" /
   "赞同. 批准"; relaxation
   proposal of the twelfth review adopted, refining 07:05].
6. The `empty_ss` blocker was the drafter's, not the repository's: the
   `Simpset` functor's `Empty_SS`/`Minimal_SS` configurations exist for
   exactly this [09:41 "我记得当时我设计的 empty_ss 和 minimal_ss 之所以有这两
   个区分就是为了要解决这个的"]; the lemma simpset is built on
   `Raw_Simplifier.clear_simpset ctxt`.

Twelfth-review drafter fixes applied: TRACE-OPS-MERGE-LOSES-HOOK and
EMPTY-SS-DROPS-EVERY-LEMMA (both dissolved by ruling 1 and 6);
COUNTER-NOT-ARMED-AT-G-SIMPCUT (every consumer goes through
`enhance_with_lemmas`, §1); LOUD-WARNING-UNREACHABLE-AFTER-JUDGE (the
warning attached to the final verdict, §5 steps 4 and 6);
DIGEST-INCLUDES-AUX-FACTS (ruling 5); BUDGET-CHARGED-ON-FAILED-ATTEMPTS
(the premise proof is the application, §1); PROVED-ENTRY-WITHOUT-LEMMAS
(§1 verdict, §7); REPLAY-CTXT-CONTRADICTION (the replay in bare `ctxt0`,
§5 step 1); STAGE-ORDER-REVERSED (§3); GUARD-CACHE-ML-PLACEMENT (after
`reasoner.ML`, §4); NET-KEYED-ON-MKSIMPS-NOT-RRULES (moot: no net);
TIER-UNIT-MISMATCH (§1, §7, §10 step 3); LEMMA-LIST-DUPLICATES (§1 export
hook, §5 step 6); COUNTER-NET-SCOPE-IN-CTXT-G (§4 the lemma budget);
FIRST-DECISION-LATENCY (§2); BEHAVIOUR-CHANGE-COUNT (§9); STALE-ANCHORS
(`cache_file.ML` `:241`, `:291`/`:285`, `:377`, `:406-408`, `:543`,
`:705-707`, `:644-645`, `:849-861`, `:903`; `sledgehammer_solver.ML:632-634`).
Discarded, with the review: step 1 "breaks PLPR" (closed, §17); the
counting-only step 3 "counts nothing"; the `eval_prf_str0` re-raise
"names the wrong mechanism" (`Pure/Concurrent/timeout.ML:48-55` makes
`TIMEOUT` the outcome once the bound's timer fired — recorded in §5's
interrupt sentence); the R-nitpick-sees-lemmas half; the `Pattern.equiv`
deduplication (withdrawn, §17.8); the loud-warning trigger by lemma
count; deleting the entry on promotion; resetting the counter per
invocation (a fresh budget per invocation would hand a looping lemma a new
budget each time); the `put_simps` widening; the canary probe.

## 19. Thirteenth-review rulings — the "G.simpcut" clock, the digest not normalised (2026-09-08, 12:51–12:57)

The thirteenth review (`wf_d0bf5d11-dba`, rev 15, scoped to
§1/§3/§4/§5/§6/§8): NOT_READY, 17 upheld (8 majors, 9 one-sentence fixes;
all DRAFTER_FIX), 2 relaxation proposals, 6 discarded, 3 dirty hacks; the
drafter re-verified every upheld finding against the code before
reporting.  Rulings:

1. **The "G.simpcut" pass runs under a wall-clock bound of
   `\<phi>guard_classic_prover_timeout`, on every path; a timeout leaves
   the state unchanged** [12:51 "赞同" — the first relaxation proposal].
   Supersedes the "unbounded … as is the template's own 'G.simpcut' pass"
   half of [2026-09-03 12:53]; the obligation instance's `fastforce` stays
   unbounded.  The timeout shape (`Seq.single st`, not `timed_tac`'s empty
   sequence) is the drafter's (§1, §10).
2. **The guard digest is NOT normalised against the fresh names of
   `oblg_template`'s `Variable.import_inst`** [12:57 "好的, 赞同不做归一化";
   the author's question 12:51 "整个 PLPR 回放的话 the instantiations 也应该
   是一致的对吗?" — answered yes: a statement replayed as it was declares
   the same names and meets the same schematic names, so its keys are
   stable; only the same guard reached from differently-named statements
   diverges, and closing that would thread the import's substitution to
   the digest step].  The second relaxation proposal is not adopted; the
   text correction it came with is (§1 guard digest, §7).
3. **Reviews from here on are rebutted harshly** [12:57 "这次评审的时候一定
   要增加驳斥者的数目一定要尽可能驳斥"; 12:09 "从现在开始我们对牛角尖评审的驳
   斥必须非常严厉"]: more defenders per finding, each told to refute; after
   a review returns the drafter re-verifies every upheld finding in the
   code and drops the nitpicks before reporting.

Thirteenth-review drafter fixes applied: DUP-LEMMAS-NOT-COLLAPSED (§5
step 1's append skips a statement already present, `Thm.eq_thm_prop`; one
budget per statement; the false `merge_ss` claim gone — §1 the export
hook); PROOF-CACHE-IS-A-TIMES-RECORD (`times * string`; the codec packs
`ms_of_times` as a pair; `zero_times` in the writes — §1, §4, §8);
BUDGET-CHARGED-BEFORE-THE-REWRITE-IS-DECIDED and
WEAKENING-BEFORE-MKSIMPS-DEFEATS-GEN-ALL (`mksimps` first, then each rule
weakened with the budget premise rotated last, added by `addsimps`; the
`clear_simpset` + `merge_ss` detour removed — §1, §7);
ENHANCE-WITH-LEMMAS-HAS-TWO-OWNERS (the call lives inside each consumer;
§3, §4, §5 steps 2/4/6 say "on `ctxt_g`"); SIMPCUT-HAS-NO-WALL-CLOCK
(ruling 1); DIGEST-DEPENDS-ON-AMBIENT-NAMES (ruling 2; the third cause of
key movement named in §1, the cost in §7);
FACTORY-CONTRACT-NEEDS-A-PROJECTION (`prj`; `SOLVED'` through it;
`head_only`'s zero-premise arm through `inj`; `apply_tac` reshaped around
the `Tactic_Configures` fold — §1, §3, §10);
REPLAY-FLOOR-MISSING-AND-JUDGE-TIMES-UNCONSTRAINED (the floor from the
option per §15.7; the judge's times must not under-state — §1, §5 step
1); R-NITPICK-OUTER-NET-IS-NOT-A-CAP (§6: the net bounds when the next
subgoal may start); INTERRUPT-SENTENCE-CARVE-OUT-TOO-NARROW (§5: both
conversions, right anchors); SEVEN-SAYS-NO-ENTRY-WRITTEN-FIVE-SAYS-OTHERWISE
(§7 qualifier); JUDGE-NOT-TOLD-VERSUS-JUDGE-GIVEN-CTXT-G (§1: no lemmas
field, must ignore the ctxt's); DROPPED-LEMMA-WARNING-HAS-NO-STATED-GATE
(§5 step 1: `warning`, unconditional, statement and failure kind);
CACHE-FILE-ANCHORS-ALL-STALE (every `cache_file.ML` anchor re-taken by
symbol; §10 step 0); HEAP-REBUILD-NOT-IN-THE-ORDER (§10 steps 1 and 4
name the `Phi_System_Base` rebuild approvals);
SWITCH-OFF-STILL-TOUCHES-THE-FILE (§1, §8 scoped to entries).
Discarded, with the review: restoring §10 step 4's key-repetition gate
(closed twice, §17.6); a real cap on R-nitpick's net by a single deadline
(a change to a bound the author set); the `bicompose` premise-order
argument as stated (the judge found the budget premise lands last for a
HOL implication split by `mp` and first for a Pure conditional — moot
once the premise is rotated by hand); the four duplicate submissions of
the duplicate-lemma defect; the attack on step 1 "breaking PLPR" (closed,
§17).

## 20. Fourteenth-review rulings — the preparatory phase, the index not normalised (2026-09-08, 15:00–15:12)

The fourteenth review (`wf_41266915-e4b`, rev 16, scoped to
§1/§3/§4/§5/§6/§7/§8/§10; five interrogators, THREE fresh defenders per
lens told to rebut as hard as possible, one judge under the rule that a
finding two defenders refute is presumptively out): NOT_READY, 8 upheld
(3 majors, 5 one-sentence fixes; all DRAFTER_FIX), 1 relaxation proposal,
10 discarded, 3 dirty hacks; the drafter re-verified every upheld finding
against the code before reporting.  Rulings:

1. **`Phi_Tool_Symbol`'s ML moves to the Pure half of
   `Performant_Isabelle_ML`; the logical definitions stay in HOL** [15:05
   "我们能否把 Symbol 的 ML code 挪动进 Pure 上, 而只是把逻辑定义在 HOL 上" —
   yes: `ssymb.ML` touches the theory through eight antiquotations only;
   15:00 "我们不是已经把 Symbol 集体挪动到 Performant_ML 仓库里了?" — it is
   there, in the HOL session `Performant_Isabelle_HOL`, which the
   Pure-based `Isabelle_RPC` does not see].  **Done as a preparatory
   phase before step 0, written into the plan first and reviewed with
   it** [15:06 "我建议把这个设置为一个准备阶段先去做"; 15:12 "先把它写进 rev 17,
   随第十五轮评审一起过一遍"] — §10 step P.
2. **The codec functor takes no symbol parameter** [15:12 "很好", on the
   drafter's withdrawal of the `Extern` (`dest`/`mk`) parameter proposed
   at 15:03 "这个 symbol 参数实际是通用的, 对吗?" — it was generic, and the
   move makes it unnecessary]: `RPC_Pretty.pack_raw_term` itself carries
   the symbol clause, every instance is symbol-safe, and the "both ends
   use one instance" contract disappears with the parameter.
3. **The schematic index is NOT normalised in `Hasher.terms`** [15:12
   "B. 否决. 整个 PLPR 是确定性的啊, schematic 的 index 也是确定性的啊, 为什么
   要放宽呢?"] — the relaxation proposal (renumber `Var`/`TVar` by first
   occurrence inside the new function) is refused; §1 states the index
   as the third cause of key movement and §7 its cost.

Fourteenth-review drafter fixes applied: GFD-DIGEST-VAR-INDEX-IS-A-FOURTH-CAUSE
(§1 guard digest, §7: on `\<condition> ?P` no import runs — `fix_level =
1` targets only premise-local variables — and the index is what moves;
the import's fresh names are the `NO_INST` cause);
GFD-JUDGE-RAW-TIMES-FED-TO-REPLAY-LIMITS (§1 the judge, §5 step 6:
`standard_time` on receipt, before the replay; the write copies);
PO-SYMBOL-NUMERAL-PERSISTED (ruling 1 and 2; §8, §9, §10 step P);
LEMMA-LIST-ONLY-EVER-GROWS (§1 the export hook: grows by step 1, shrinks
by step 6); lemma-budget-EXPORT-CHANGES-THE-PROPOSITION (§1 the export
hook, §7: identity is the proposition a theorem has now; a block frame
returns `C ⟹ th`, `Phi_Working_Mode.ML:226-232`; such a copy coexists
with the plain replay); lemma-budget-SHARED-LEMMA-KEEPS-THE-FIRST-TIER
(§1, §4: the tier of the entry that first put the statement into the
list); RJH-1-NITPICK-NET-SEMANTICS-INVERTED (§6: the outer bound ends
R-nitpick inside the running subgoal — `timeout.ML:48-56` — and is a real
cap; the coincidence case leaves the remaining subgoals under their
inner bounds); PO-DEAD-BOOL-READERS-MISCOUNTED (§8: `:821` sets it;
`:717`, `:728`, `:852` bind it).  Discarded, with the review: the
BLOCKER on step 6's `error` (§1's P-auto carries its bound by
definition); "the store can deny a proof" (§7's own bullet and its two
escape hatches); the judge's replacement "evicting another guard's
lemma" (the ruling of 08:34 is to replace what is present at the
`prove_or_refute` point, and every guard's entry re-installs its lemmas
at step 1); first-come tier "missing a tie-break" (stated twice); the
undecided-guard warning "firing twice or never" (its two arms are
enumerated); an exhausted lemma "not stopping matching" (the two
sentences before the attacked one); a grown term reaching the
obligation instance's `fastforce` (recorded in both halves of §7); an
`Unknown` entry "freezing a timeout" (the bullet's second half); the
tracing gate "unscheduled" (§10 step 0 names it); and a duplicate of the
"only ever grows" finding.  Dirty hacks refused: keying the dedupe on the
entry's `stmt` instead of the theorem's proposition (would suppress the
plain replay behind an exported `C ⟹ L`); a second P-auto on the
`Refuted` arm on a lemma-free ctxt (records `Proved` for lemmas that did
not prove, doubles the cost of 06:10); canonicalising indices inside the
shared `hash_term` accumulator (moves every other `Hasher` caller's
digest).

## 21. Fifteenth-review drafter fixes (2026-09-08)

The fifteenth review (`wf_3e08f335-610`, rev 17, scoped to
§1/§4/§5/§6/§7/§8/§9/§10 with a new lens on the preparatory phase; six
interrogators, three defenders per lens, one judge): NOT_READY, 9 upheld
(1 blocker, 8 one-sentence fixes; all DRAFTER_FIX), no relaxation
proposal, 9 discarded (2 of them duplicates), 3 dirty hacks; the drafter
re-verified every upheld finding against the code.  No author ruling was
needed; the fixes:

PREP-BYTESIO-TWIN-BREAKS-STEP-P (the blocker): step P deleted Isa-Mini's
codec in favour of `RPC_Pretty`'s, but that copy lives inside `functor
MiniLang_Agent_Pack(S)` (`agent_packer.ML:23-31`) instantiated at
`BinIO.StreamIO` and `BytesIO` (`:365-366`), and `RPC_Pretty`'s codec is
monomorphic (`pretty.ML:7-8`, `:320`) until the term-codec functor exists
— which the plan scheduled at step 4.  Fix: the `MESSAGE_PACK` extraction,
the term-codec functor and both instances move INTO step P — `mlmsgpack.sml`
is loaded by `Performant_Isabelle_ML.thy:37`, the same root heap
`ssymb.ML` moves into, so the one rebuild covers both — and Isa-Mini's
functor body applies the term-codec functor to its own `MP`; step 4
keeps only the store functor and the entry codec (§8, §9, §10 step P and
4).  GFD-IMPORT-RUNS-ON-CAN-INST-TRUE (§1 guard digest, §7: at `fix_level
= 1` the import runs iff the fixing targets — premise-only variables of
the antecedent and `LPR_ctrl`-annotated ones of its conclusion — are
non-empty; those become fresh Frees, the rest stay `Var`/`TVar`; both
causes can act on either reasoner).  PREP-PROBE-CERTIFIES-ONLY-Z (§10
step P (a): the assertion certifies every constant `ssymb.ML` builds,
exported as `Phi_Tool_Symbol.constants`; a `mk_symbol` probe on a fresh
table builds only `Z`).  PREP-SEMEMB-PENDING-IS-MOOT (§10 step P (b): the
third transcription is inside a block comment, `:29`–`:74`, and
`RPC_Pretty` is already in scope through `Semantic_Embedding.thy:2`;
nothing pending).  PREP-PACK-RAW-TERM-HAS-CALLERS (§9: `REPL_serializer.ML:41-42`
re-exports it, `verify_proof_app.ML:33`, `:36` use it on a wire whose
Python end carries the payload back unread).  GFD-SEVEN-SCOPES-THE-BAD-LEMMA-TO-ONE-GUARD
(§7: a cut-off lemma costs its budget in every consumer run downstream
of the call that enabled it, degenerate instances' "G.simpcut" included).
LB-EXPORT-HOOK-IS-AN-UNDECLARED-WRITER-AND-SHRINKER (§1 the lemma list, §4,
the export hook's evolution sentence: the hook writes the outer list and
drops what `export_aux_lemma` refuses).  CP-FAILING-CALLS-CARRY-NOTHING
(§1, §7: a lemma travels along the branch the search keeps; a call
returning `Seq.empty` abandons its `ctxt1`, `reasoner.ML:688`).
PO-DEAD-BOOL-ENUMERATION-STILL-INCOMPLETE (§8: constructed at six sites,
destructured at six, `:842` in both).
Discarded, with the review: "G.simpcut" "defined by a deleted probe"
(defined by its code text, which stands); the exported copy
"unremovable and accumulating" (`Phi_Working_Mode.ML:227` returns a
theorem unchanged when its hyps lack the frame's assumption);
`simp_depth_limit` as "a second behavioural difference" (stated one
clause earlier); the replay-timeout clause "preceding the §9 guard"
(closed in §18); "which lemmas after the drop" (the entry is the record);
the R-nitpick "×2 worst case" (arithmetic checked); the judge re-entry
contract "silently lifted" (the 11:44 ruling presupposes re-entry);
the judge's `Unprovable` "self-lockout" (§9 says which entries reach it);
the exported copy "surviving judge replacement" (§1 says identity is
the current proposition); the rebuild count "contradicting step P"
(step 5's clause constrains the acceptance run only).  Dirty hacks
refused: keying the removal on the entry's `stmt` (refused by name in
§20); stamping list elements with the owning digest (widens the slot of
07:48 and drops shared statements against 06:16); exempting every replay
overrun from "fails to replay" (destroys the judge's times contract of
08:45).

## 22. Sixteenth-review drafter fixes (2026-09-09)

The sixteenth review (`wf_6121f42f-d25`, rev 18, scoped to
§1/§4/§7/§8/§9/§10; six interrogators, three defenders per lens, one
judge; interrupted once by the session limit and resumed from the
journal): NOT_READY, 8 upheld (1 major, 7 one-sentence fixes; all
DRAFTER_FIX), 1 optional relaxation proposal, 12 discarded, 3 dirty
hacks; the drafter re-verified every upheld finding against the code.
The fixes:

LB-EXPORT-GEN-ALL-BREAKS-THE-DEDUPE (the major): `Proof_Context.export`
hhf-normalises and `Variable.gen_all`s every theorem it carries
(`assumption.ML:153-156`, `raw_simplifier.ML:1556-1561`,
`variable.ML:510-514`), so a lemma stated with an outer `⋀` came back
`aconv`-distinct from its next replay and §5 step 1's dedupe missed at
every boundary.  Fix: §5 step 1 (and step 6) stores and compares the
canonical form `Drule.zero_var_indexes (Raw_Simplifier.norm_hhf_protect
ctxt0 th)`, on which the export's normalisation is the identity (§1 the
export hook); "nothing is lost and nothing is double-counted" restricted
to the two proposition-changing cases the canonical form does not absorb.
The relaxation proposal — dedupe again inside the export hook — is not
taken: the append-side canonical form alone closes the defect, and the
hook's plain overwrite [author 2026-09-04 07:33] stands.
PREP-THIRD-PACK-RAW-TERM-CALLER (§9: `REPL_serializer.ML:41-42`'s consumer
is `tasks/extraction/theorem-relevance/extraction.ML:244-245`; what the
symbol clause does on those wires).  PREP-ASSERTION-MISSES-THE-MATCHING-LITERAL
(§10 step P (a): `decode`'s first clause tests `t aconv zero` instead of
repeating the name in a pattern, so the assertion over
`Phi_Tool_Symbol.constants` covers every occurrence).
PREP-SYMBOLT-LITERAL-IS-A-TYP (§10 step P (a): `\<^typ>\<open>symbol\<close>`
becomes `Type ("SSymb.symbol", [])`; nine antiquotation occurrences).
gfd-import-retypes-variables-it-did-not-fix (§1 guard digest, §7:
`Thm.instantiate` substitutes `importT_inst`'s TFrees throughout the
state).  gfd-no-premise-guard-can-still-be-imported (§1: the parenthetical
restricted to a conclusion without `LPR_ctrl`).
RJH-SEVEN-IMPORT-PARENTHETICAL-CONTRADICTS-ITSELF (§7: the rev-16 residue
"where no import runs" gone).  LB-FIXES-ARE-NOT-IN-THE-SIMPSET (§4: the
`\<r>BUDGET` variables are fixes of the enhanced ctxt, not simpset
content).
Re-anchoring, outside the review: commit `8c26c3b4` (2026-09-08 15:01
UTC) removed the `exception Option` hunt instrumentation from
`reasoners.ML` (−199 lines from `:943`), so every `reasoners.ML` anchor
from `:978` on was re-taken by symbol, and the `option_hunt` probe whose
label named "G.simpcut" is gone (§1); `sledgehammer_solver.ML`'s
catch-all clause moved to `:634-636`.
Discarded, with the review: the digest "cannot reach the solving
function" (it is a curried argument of the solving function's type, §1);
the "G.simpcut" bound "absent from §2's worst case" (§2 sums the three
stages it names; the bound lowers a today-unbounded pass); the exhausted
lemma "still matching" (discarded by name in §20); the drop's store write
(the author's 06:16 carve-out); the clamp "only at P-auto" (today's code
reads and clamps once, `reasoners.ML:1420-1421`, for both racers); §2's
"P-auto only"; the loud warning "a one-shot" (§7's `Refuted` and `Unknown`
bullets); the degenerate instances "scoped to G.simpcut only" (the
governing clause is universal); two `Phi_Tool_Symbol` bindings on a
sibling join (`Context.make_parents` drops an import that is an ancestor
of another, `context.ML:531-533`); the dead `bool` "still misclassified"
(third pass, nothing missed); the `eval_prf_str0` anchor (two-line drift,
re-anchored above); a duplicate of the third-caller finding.  Dirty hacks
refused: wrapping the codec's symbol clause in `try` so an unregistered
numeral falls back to the structural encoding (that encoding IS the
per-process numeral `SSymb.thy:19-21` forbids); gating the dropped-lemma
warning on `\<phi>trace_reasoning` (against 06:16 "移除并报警" and §19);
a `val`-bound name used as an ML pattern (binds, does not match).

## 23. Seventeenth-review drafter fixes (2026-09-09)

The seventeenth review (`wf_1e577497-341`, rev 19, scoped to
§1/§4/§5/§7/§9/§10 with a lens on the canonical form; six
interrogators, three defenders per lens, one judge): NOT_READY, 8 upheld
(3 majors, 5 one-sentence fixes; all DRAFTER_FIX), no relaxation
proposal, 10 discarded, 4 dirty hacks; the drafter re-verified every
upheld finding against the code.  No author ruling was needed; the
fixes:

CF-EXPORT-TVAR-REGROWS-THE-LIST (major): rev 19's canonical form was a
fixed point of the export's `gen_all` but not of its type generalisation
(`variable.ML:515-529`, `:565-572`), so a lemma carrying a type variable
the outer ctxt does not declare came back as `L[?'a.i]` at every
boundary, distinct from its next replay, and the list grew by one copy —
one budget variable, one duplicate rule — per boundary, without bound.
Fix: the canonical form also generalises every type variable `ctxt0` has
not declared, `Variable.exportT ctxt0 ctxt0`, which is the set the
boundary's export would generalise for a closed statement; the carve-out
sentence and §7's carried-lemma bullet now name one case that settles at
two copies (§1, §5 step 1, §7, §10).  CP-JUDGE-TIER-SILENTLY-DOWNGRADED-THEN-BLAMED
(major): §5 step 6 removed only this entry's statements and re-used the
"already present keeps its budget" rule, so a judge lemma colliding with
another entry's statement ran at that entry's tier and a resulting P-auto
failure blamed the judge.  Fix: on `Provable` the lemma list becomes
exactly the judge's list at the judge's tiers, every statement present
leaving — the 08:34 replacement as §20 read it (§5 step 6).
CP-REPLAY-CTXT-QUANTIFIER-UNSTATED (major): the judge contract said
"provable … in `ctxt0`" without saying which; the digest excludes the
ctxt by ruling and the entry is shared.  Fix: provable in ANY `ctxt0`
that can reach the digest — theory-level facts only; §5 step 1's
dropped-lemma warning names both causes (§1, §5).
CF-CANONICAL-FORM-CHANGES-MKSIMPS (§1: `norm_hhf_eqs` on top of
`gen_all` — the rule set an Isar-proved lemma would give).
CF-POINTER-EQ-SHORTCIRCUIT-DOES-NOT-STAND (§4: the short-circuit stands
only for a run returning the incoming ctxt itself; a subgoal allocation
fires the hooks).  gfd-aux-is-not-aux-thms (§1: `aux` at `:1629` is the
hook fold's output, seeded by `aux_thms`, extended by `Phi_Envir.ML:336-338`).
LB-DUPLICATE-RULE-WARNING-JUSTIFIED-BY-A-VARIABLE-THAT-IS-NOT-PER-RULE
(§1 step (6): "never warns" scoped to ambient and other lemmas' rules; a
repeated conjunct of one lemma collapses with the stock warning).
RJH-2-OPTION-EXCEPTION-IS-NEITHER-UNDIAGNOSED-NOR-RACE-ABSORBED (§7: the
`Option` exception is root-caused — `future.ML:422-432`,
`OPTION_EXCEPTION_IN_PROOF_REPLAY.md` — and live in this checkout).
Discarded, with the review: `ctxt'`'s export reason "false" (stated
twenty lines below); `prj` "attached to `oblg_template`" (true and
harmless); the budget "per lemma but calibrated per rule" (§1's tier
bullet defines the unit); `ctxt1` "physically new without a lemma" (§5
step 1 iterates per lemma); the judge "cannot correct over-refutation"
(§2 defines the term); a bad lemma "without terminating event on a
`Refuted` entry" (§7 scopes the cost downstream); the R-nitpick citation
"holding no Nitpick call" (§3's Reused sentence); the symbol clause
"altering two live wires" (`ssymb.ML:14-18`'s own specification); step
P (a) "contradicting its own `decode` fix" (a rule and its named
exception); step P "consuming anchors never re-verified" (checked, they
hold).  Dirty hacks refused: a deduplication pass to silence a stock
diagnostic; gating the export hook on `pointer_eq` of the list slot;
widening step 6's removal to implications whose conclusion is a removed
statement (the `stmt`-keyed family refused in §20 and §21); an
acceptance test that could only pass by persisting a per-process
numeral.

## 24. Eighteenth-review drafter fixes (2026-09-09)

The eighteenth review (`wf_dea7bb03-b3d`, rev 20, scoped to
§1/§4/§5/§7/§10; six interrogators, three defenders per lens, one
judge): NOT_READY, 5 upheld (1 major, 4 one-sentence fixes; all
DRAFTER_FIX), no relaxation proposal, 13 discarded, 4 dirty hacks; the
drafter re-verified every upheld finding against the code.  The fixes:

CF-EXPORTT-TESTS-THE-WRONG-CONTEXT (major): rev 20's `Variable.exportT
ctxt0 ctxt0` generalised the type variables `ctxt0` does not declare,
but the boundary's `Variable.export` generalises those the OUTER ctxt
does not declare (`variable.ML:516-518`), and declaration only grows
inward (`:216-224`), so the canonical form covered a SUBSET of the
boundary's set and a type variable declared inside the run or block
still regrew the list.  Fix: the canonical form over-generalises —
`Thm.generalize` of every type variable of the proposition that occurs
in no hyp — which no later `Thm.generalize` can touch, whichever ctxt
replayed the lemma (§1, §5 step 1, §10).  The export-to-a-global-ctxt
alternative was refused: it would drop the hyps carve-out and raise at
`thm.ML:1823-1824`.  JCP-EXPORT-BULLET-STILL-SAYS-THIS-ENTRY (§1 the
export hook, §3's pseudocode, §7's cut-off bullet: rev 20's total
replacement propagated).  CF-BOUNDARY-COPIES-DO-NOT-SETTLE-AT-TWO (§1,
§7: one weaker copy per block crossing whose `Premise` the replay's hyps
hold — `block_export` discharges one frame per export).
GFD-SE-TRIM-EMPTY-ANCHOR-IS-A-DELETED-FILE (§3: `SE_Trim_Empty.ML` was
deleted in commit `11499285`; `rule_generation.ML:443` is the only
internal setter).  PPO-GUARD-DECISION-BUDGET-FIELD-UNREACHABLE (§10: the
budget-exhaustion count dropped from `guard_decision`; it lives in the
simprocs' closures and §4 permits no channel out).
Discarded, with the review: the judge contract "not position-closed"
and "theory-level facts do not suffice" (the obligation IS the
any-`ctxt0` quantifier; the facts clause is derived); step 6 "evicts
then blames" (discarded by name in §20); "G.simpcut" "not handed
`ctxt_g`" (§4's operative rule is right); the exhausted rule "still
paying premise proofs" (closed twice); judge nesting "without a second
batch" (§6 allows re-entry); the digest "without a channel" (closed in
§22); `aux` "a retired name in use" (the list retires senses); step 1
"not loading" (closed three times); §8 "naming the BinIO instance" (the
sentence names `RPC_Pretty_Bytes`); the replay catch-all "turning a live
Pure defect into a permanent drop" (the root-cause document says the
exception does not arise inside `eval_prf_str0`'s `try`); three
duplicates.  Dirty hacks refused: dropping from the hook any theorem the
export changed; exporting to `Proof_Context.init_global`; splitting
"fails to replay" by `Auto_Fail` reason; narrowing step 6 back to this
entry's statements.

## 25. Nineteenth review — READY (2026-09-09)

The nineteenth review (`wf_95747529-38f`, rev 21, scoped to
§1/§3/§5/§7/§10; six interrogators, three defenders per lens, one
judge): **READY** — 19 findings, 2 upheld (both MINOR one-sentence
fixes, applied in rev 22), 17 discarded, 5 dirty hacks, no relaxation
proposal, no author decision.  The two fixes:
CF-CANON-DEPENDS-ON-THE-REPLAY-HYPS (downgraded from MAJOR by the judge):
the canonical form's type generalisation depends on the replay's hyps,
so a statement whose replays pin different type variables of it can
hold more than one entry — bounded by those type variables, each entry a
fixed point of the boundary; the dedupe's consequences are now stated
per canonical proposition (§1, §5 step 1, §7).
LB-FOUR-CLAIMS-THE-HOOK-PRESERVES-LENGTH (§4: the hook's write is the
inner list minus what `export_aux_lemma` refuses, never longer).
Discarded, with the review: the export "raising `THM`" (`gen_fixesT`
has two exclusions, `variable.ML:526-529`, and the canonical form
removes exactly the type variables that could trigger the hyps check;
`export_state` already exports the run's own sequent without a handler,
`reasoner.ML:948`, `:960`); `pre` "breaking the `ALLGOALS` rewrite" (the
only registration passes `tac` through, `pre = all_tac`); the step-1
tier collision "paid on every run" (the `Proved` arm writes `Refuted |
Unknown`, so the chain is paid once); the replay caps billed as
steady-state cost (a limit, `cache_file.ML:218-227`); the returned
ctxt "replaced by step 6" filed twice (§1 licenses it: "only the
solving function may replace the ctxt"); `ssymb.ML` "losing its check
in a session" (one loader today, `SSymb.thy:98`; the acceptance sits
above `Performant_Isabelle_HOL`); `t aconv zero` "narrowing" (the type
is nullary); and five re-submissions of items §20/§22/§24 closed by
name.  Dirty hacks refused: not storing a hyp-pinned theorem at all
(breaks step 6's total replacement, 08:34); dropping a theorem on any
`THM` from the export (silent loss against §1's two named drop causes);
raising an installed statement's budget to the maximum (runs an
`Only_Once` lemma at 1000); catching the judge's `TIMEOUT` into the
no-judge arm (against 2026-09-03 12:31); a budget-count sink in
`enhance_with_lemmas` (against §4 and §18.3).

## 26. The preparatory phase done; step 0 anchors re-verified (2026-09-09)

**Step P** (§10) was implemented on the author's "开工" (2026-09-09) and
accepted ("验收通过") after two rounds of evidence.  Files: `ssymb.ML`,
`Performant_Isabelle_ML.thy`, `HOL/SSymb.thy`, `contrib/mlmsgpack/mlmsgpack.sml`
(Performant_Isabelle_ML); `Tools/pretty.ML`, `ROOT`, the new
`test/Test_Term_Codec.thy` (Isabelle_RPC); `Agent/agent_packer.ML`
(Isa-Mini).  Names the drafter chose: the functor `RPC_Term_Codec`, the
instance structure `Codec` inside `RPC_Pretty` and inside
`MiniLang_Agent_Pack` (both invisible outside).  Evidence: (1) before any
build, the changed ML compiled on the Pure heap under a Pure theory
context (`isabelle ML_process`) with only pre-existing warnings, and the
four round trips passed; (2) the author's build
`isabelle build -b -d … Isabelle_RPC_Test Performant_Isabelle_HOL
Minilang_AoA Phi_System_Base` passed; (3) under Isabelle-MCP, `SSymb.thy`
(session HOL-Library) evaluated clean with the certification assertion
silent and `SYMBOL(xxx)` still `Const ("SSymb.Z", "symbol")`,
`Test_Term_Codec.thy` evaluated clean, and `Minilang_AoA.thy` (session
Minilang) evaluated clean with `agent_packer.ML` compiled from source;
(4) on the rebuilt `Minilang_AoA` heap, `MiniLang_Agent.pack_raw_term` /
`unpack_raw_term` round-trip a term and a symbol, and produce bytes
identical to `RPC_Pretty_Bytes`'s for the same term.  `HOL/SSymb.unicode.thy`
(a mirror) was left as it was [author 2026-08-18: mirror staleness is
not raised].

**Step 0** (§10): every line anchor of §1–§10 was re-verified against the
sources as of 2026-09-09 — three readers by file group (phi-system,
auto_sledgehammer, the Isabelle distribution and Performant_Isabelle_ML),
each stale row re-checked by the drafter — about 220 anchors, none
missing.  Corrections applied in rev 23: `reasoners.ML` `:1650` → `:1651`
(the `oblg_template` call of `safe_obligation_solver`, twice) and `:386`
→ `:386-387` (`head_only`'s zero-premise arm); `Subgoal_Env.ML:61-64` →
`:62-65`; `Phi_Preliminary.thy:6-9`'s first parent is `Main`, not
`SSymb` (the conclusion — the hook installed in PLPR is lost — stands);
`raw_simplifier.ML:975` → `:974` and `:1556-1561` → `:1556-1563`, and
the bare `:1130-1135` now names its file; `proof_context.ML:921-923` →
`:920-924`; `cache_file.ML:892-905` → `:892-906`; `PLPR_error_msg.thy:7`
→ `:8`; `Minilang_AoA.thy:2` → `:2-3`; and the step-P anchors of §8, §9
and §10 (`pretty.ML`, `mlmsgpack.sml`, `ssymb.ML`, `SSymb.thy`,
`agent_packer.ML`, `Performant_Isabelle_ML.thy`) re-taken after the
change.  Also confirmed, not by line: the four `Phi_System` callers
(§3) and `application.ML:137` inside its comment; `rule_generation.ML:443`
the only internal setter; `oblg_template`'s four callers and
`apply_tac`'s three; the one `Tactic_Configures` registration outside
PLPR; the guess-inst looper installed only at `reasoners.ML:1604` (the
SOLVER `add_guess_inst_solver` is also live at `:1655`, inside
`safe_obligation_solver`; §5 speaks of the looper); `RPC_Pretty` not
visible from Auto_Sledgehammer; `cache_file.ML`'s one `Config.get`, the
dead `bool`, `proof_cache`/`times`, `replay_limits`, `standard_time`,
`at_end`, `compact_store`'s `File.is_file`, `createf`, and the `.tmp`
naming.  The tracing gate (§7) is unchanged.  Step 1 is next.

## 27. Step 1 done (2026-09-09) — pending the author's acceptance

Files: `auto_sledgehammer/library/Hasher.ML` (`terms`),
`sledgehammer_solver.ML` (the interrupt clause; the replay trace behind
`auto_sledgehammer_trace_replay`, default off — the verbosity gate of §9, name:
drafter); `PLPR.thy` (`Guard_Budget` after `reasoner.ML`, `ML_file
library/guard_cache.ML` next, the method `\<phi>guard_P_auto` after
`reasoners.ML`, the two `\<condition>` registrations on
`guard_condition_judge … o snd`, `defer_premise`'s cases 1 and 2 on the
`fastforce` instance `solve_obligation_now` (name: drafter), `hide_const
(open) Guard_Budget` at the end); the new `library/guard_cache.ML` (structure
`Phi_Guard_Cache` — name: drafter — with §1's types, the two options,
`budget_of_tier`, `Guard_Simp_SS`, `Guard_Lemmas`, `canonical_form`,
`add_lemma`, the export hook at priority 200, `enhance_with_lemmas`);
`library/guard_refute.ML` (`Nitpick_Refute_SS`); `library/reasoners.ML`
(`apply_tac prj ctxt body mode th` outside the hook fold; `head_only'`;
`oblg_template … {inj, on_thm}` and its four callers; `guard_race` — today's
race, renamed; `prove_or_refute` in its final type wrapping it;
`guard_classic_prover_timeout`/`_bound`; `enhance_for_guard`, `simpcut_tac`,
`p_auto_body`, `try_prove_or_give_up`, `undecided_guard_warning`,
`loud_guard_warning`, `is_guard_mode`, the factory `gen_guard_condition_solver
digest_of solve`, `guard_digest`, `guard_condition_judge`, `p_auto_solving`,
`guard_condition_solver'` — internal names: drafter; the P-auto and R-conv
racers now search in `enhance_for_guard`ed contexts).

Two departures from the letter of §1, both the drafter's: `prj` is a
parameter of `apply_tac` only, where the `SOLVED'` filter lives, and
`oblg_template` takes `{inj, on_thm}` — it never reads a result's theorem
itself, so a third parameter would be unused; and the factory's digest step
is typed `thm -> 'd` with `solve : bool -> Proof.context -> 'd -> …`, so the
judge instance passes `guard_digest` and `prove_or_refute` while the two
degenerate instances pass `K ()` — no digest is computed for them and no
dummy digest exists.

Transitional, until step 2: `prove_or_refute`'s body is the race
(`guard_race`), its digest argument unused; `\<phi>guard_race_timeout`,
`\<phi>log_guard_race`, the 35 ms gate and the `Race.race` call stay; the two
warning functions have no call site yet (two "not referenced" ML warnings);
the `nitpick_params` note (§10 step 1's last item) is rewritten with the
race's removal, since today it is still true.

Evidence: `PLPR.thy` evaluated clean under Isabelle-MCP on
`Performant_Isabelle_HOL` (the auto_sledgehammer edits loaded from source)
before any build; the author's rebuild `isabelle build -b Minilang_AoA
Phi_System_Base` passed (Auto_Sledgehammer, Minilang, Minilang_AoA,
Phi_System_Base; 1 m 31 s); then `Phi_Test/PhiTest_Arithmetic.thy` evaluated
clean under Isabelle-MCP on the rebuilt `Phi_System_Base` with the whole of
phi-system loaded from source, the run logging 175 `guard_race` records
through the new factory (24 proved, 145 refuted, 6 undecided) and one
`guard-racer R-conv` `Interrupt_Breakdown` exception record of the kind the
race has logged since 2026-08-30 (45 earlier records) — the engine
cancelling the loser.

## 28. First code review (2026-09-09) — fixes applied

The first adversarial CODE review (`wf_d8746808-6c8`; six interrogators, four
fresh defenders per lens, one judge, Opus): NOT_ACCEPTED — one MAJOR and six
MINORs upheld, all DRAFTER_FIX; two relaxation proposals; fifteen discarded.
Fixes applied (the author: "请你现在动手吧"):
1. MAJOR, `PLPR.thy` `solve_obligation_now`: `Clasimp.fast_force_tac ctxt 1`
   attacked subgoal 1 only, so a state the "G.simpcut" pass had already closed
   (zero premises — `fast_tac`'s `atomize_prems_tac` is a `CONVERSION`, which is
   `Seq.empty` on a missing subgoal, `tactical.ML:320-321`) and a state the case
   split had split into several subgoals both failed `try_prove_or_give_up`'s
   whole-state test.  Now `ALLGOALS (Clasimp.fast_force_tac ctxt)`.  Evidence:
   `ai-artifacts/Solve_Obligation_Now_Probe.thy` — a guard closed only after the
   `[useful]` fact is inserted (the TrueI exit cannot take it) is solved by the
   fixed instance, and so is `p a ⟶ (∃x. p x)`, which simp cannot close; two
   controls: the pre-fix instance is empty on the first guard, and the factory
   with a do-nothing solving tactic leaves the second guard open, so fastforce
   is what solved it (the re-review's one MINOR, §29, asked for this control).
2. The undecided-guard warning existed twice in `reasoners.ML`; `guard_race`'s
   inline copy now calls `undecided_guard_warning`, defined above it.
3. `guard_cache.ML`: `add_lemma ctxt0 (th, budget)` canonicalises itself;
   `canonical_form` left the signature; `put_lemmas` replaced by
   `replace_lemmas ctxt0 new = put [] #> fold (add_lemma ctxt0) new` (the
   judge's replacement of §5 step 6); `Guard_Lemmas.put` stays internal to the
   hook.  The signature comment says "one canonical proposition is stored once".
4. `ssymb.ML` (step P, accepted): `digit_consts` built once, shared by
   `constants` and `encode`, so `SSymb.thy` certifies the terms `encode` emits.
5. `Test_Term_Codec.thy` (step P): the round trips compare with `=`, which sees
   the `Abs` binder name `aconv` ignores.
Relaxation proposals, both accepted by the author (2026-09-09; A verified
safe by an independent agent: the only registration, `Phi_Envir.ML:336-338`,
raises nothing): A. `apply_tac` runs `Tactic_Configures.invoke` instead of
`invoke_until_success` with an identity fallback (§1 updated); B. the
"G.simpcut" pass is cut to its first state, `Seq.take 1`, so one bound covers
the whole pass and the solving function runs once per call (§1 updated; the
code comment records the deliberate narrowing).
Evidence after the fixes: `PhiTest_Arithmetic.thy` clean under Isabelle-MCP on
`Phi_System_Base` (176 guard decisions: 25 proved, 145 refuted, 6 undecided;
the one R-conv `Interrupt_Breakdown` record as before); the probe above clean;
`SSymb.thy` and `Test_Term_Codec.thy` clean under HOL-Library.  Note: the
`ssymb.ML` edit sits inside every heap from `Performant_Isabelle_HOL` up, so
the next rebuild (the author's) must start there.
Discarded, with the judge, among others: the `pair ctxt0` "written thrice"
nitpick (three lenses; its motivation contradicts §1's invariant); the
`Thm.cprems_of` "re-certification" cost (thm.ML:556-558 reuses the theorem's
cert); the nesting comment (a transcription of §1 under §18.4); "the simproc
never checks the head constant" (raw_simplifier.ML:1108 matches `lhss`
first); `serial ()` in a fixed variable's name (a dirty hack); the stale hunt
markers (another line's uncommitted residue in six files of five repositories,
to be swept into the commit and named there, not deleted).
Re-review: one lens over the diff of PLPR.thy, reasoners.ML, guard_cache.ML,
ssymb.ML, Test_Term_Codec.thy (§29).

## 29. Re-review — step P and step 1 ACCEPTED (2026-09-09)

The re-review (`wf_61cf82c2-9ce`; two interrogators over the fix diff, three
fresh defenders each, one judge, Opus): **ACCEPTED** — the seven fixes and the
two relaxations of §28 verified applied exactly (the judge re-derived the
MAJOR fix's correctness from `ALLGOALS`'s definition, `tactical.ML:236-240`: at
one premise the new instance is the old one, at zero and at k>1 it is strictly
wider under the whole-state test); one MINOR, a wording matter: the probe's
second guard (`∃x::nat. x + 3 = 5`) was one simp could close in the pass, so
"solved" did not show fastforce ran.  Fixed by replacing that guard with
`p a ⟶ (∃x. p x)` and adding the do-nothing-solver control (§28 item 1); the
probe re-evaluated clean with all four lines.  The author approved and the
drafter ran the rebuild from `Performant_Isabelle_HOL` up
(`Isabelle_RPC_Test`, `Performant_Isabelle_HOL`, `Auto_Sledgehammer`,
`Minilang`, `Minilang_AoA`, `Phi_System_Base`; 1 m 55 s, all passed).
Step 2 is next.

## 30. Step 2 done (2026-09-09) — pending review and the author's acceptance

What was done, against §10 step 2 (phi-system files only; no heap rebuilt):

1. **`prove_or_refute` is the sequential protocol of §5** (`reasoners.ML`, the
   "Guard decision" section): step 0 reads the entry through
   `Phi_Guard_Cache.lookup_entry`, gated by `\<phi>guard_cache` read once from
   `ctxt0`; step 1 replays each lemma in `ctxt0` (`replay_lemma`: `Thm.cterm_of
   ctxt0`, `Thm.trivial`, `eval_prf_str` with `n = 1` under
   `Phi_Proof_Store.replay_limits` of the recorded times, each component floored
   by `guard_classic_prover_bound ctxt0` with `Time.max`; the keywords
   `Keyword.no_major_keywords (Thy_Header.get_keywords thy)` as
   `sledgehammer_solver.ML`'s `replay_store` takes them), drops a failing lemma
   with **the dropped-lemma warning** and rewrites the entry without it, and
   appends the survivors to the lemma list of `ctxt0` (`ctxt1`) and of `ctxt`
   (`ctxt_g`) through `add_lemma ctxt0` with `budget_of_tier`; step 2 is
   `cpu_bounded_tac (guard_classic_prover_bound ctxt0) (p_auto_body ctxt_g)`,
   first solved state (thread CPU, §1 "G.simpcut"); steps 3–4 follow the
   entry's verdict exactly as §3's tree draws them (`Refuted` silent;
   `Unknown` → the judge or `Unknown`, nothing rewritten; `NONE` → R-conv →
   R-nitpick → the judge → `{lemmas, Unknown}` written; `Proved` → the same
   with the loud guard warning); step 6 (`consult`) hands the judge `ctxt`
   — the guard-side ctxt without this entry's lemmas — normalises the
   judge's times with `standard_time` on receipt, replays each of `new` — a
   failure is `error "The judge is broken: its lemma …"` — adds them through
   `update_lemma ctxt0` to the lists of `ctxt0` and of `ctxt` as they were
   before step 1 (`ctxt1'`, `ctxt_g'`: this entry's lemmas replaced, an
   earlier guard's kept, a re-proposed one at the judge's budget), runs
   P-auto again on `ctxt_g'`, writes `{new, Proved}` and returns `(ctxt1',
   solved)`, or raises `error "The judge is broken: P-auto cannot prove …"`;
   `Unprovable` writes `{lemmas, Refuted}`.  The two warnings are decided at
   one site from the final verdict, mutually exclusive: the loud guard
   warning when a call from a `Proved` entry ends otherwise, with the
   refuters' and the judge's results in one sentence ("the judge was not
   consulted" when a refuter answered first); the undecided-guard warning
   when a call from any other entry ends `Unknown` [author 2026-09-09 "spec-3
   赞同 (a)"].
2. **R-conv** is `r_conv can_inst ctxt ctxt0 goals : bool`, the former racer
   body verbatim under `cpu_bounded (guard_classic_prover_bound ctxt)` —
   `Thread_CPU.apply` with no wall limit — `TIMEOUT` = not refuted;
   **R-nitpick** is `r_nitpick ctxt goals : bool`, the former screen and calls,
   the subgoals one after another, each under `Timeout.apply
   (\<phi>guard_refute_timeout + 5 s)`, the whole under
   `\<phi>guard_refute_timeout + 5 s × the number of subgoals` (§6; the first
   draft had the net at `n × (…)`, the review's one MAJOR, §31), either
   `TIMEOUT` = not refuted; wall clock, since it waits on an external process;
   it receives the guard-side `ctxt` without the lemmas (§1 `Guard_Simp_SS`:
   not R-nitpick).
3. **The judge ref**: `type judge_arg`, `datatype judgement = Provable of lemma
   list | Unprovable`, `val judge : (judge_arg -> judgement) option
   Unsynchronized.ref` (= `NONE`), all in `PHI_REASONERS`; names: drafter
   under the 11:24 delegation.
4. **The store's stand-in** (§10 step 2's "in-memory table"): `guard_cache.ML`
   gained `lookup_entry : theory -> Hasher.digest -> entry option` and
   `write_entry : theory -> Hasher.digest -> entry -> unit` over one
   process-global `Synchronized.var` holding an `entry Symtab.table` keyed by
   `"PLPRGUARD" ^ Hasher.compact d` (§1 the store); the `theory` argument is
   ignored until step 4 swaps `Phi_Guard_Store` in behind the same two names.
   Not gated by the switch; `prove_or_refute` gates its read and writes (§4).
5. **`guard_decision`**, the permanent record (§10): fields `verdict`
   (proved/refuted/unknown), `hit` (the entry's verdict or `none`), `refuter`
   (`R-conv`/`R-nitpick`/`-`), `judge` (`Provable`/`Unprovable`/`-`),
   `elapsed_ms`, `digest` (`Hasher.hex`), `subgoals` (the first draft's
   `lemmas` count was ambiguous — this entry's survivors or the whole list —
   and is deleted [author 2026-09-09]); switch `\<phi>log_guard_decision`,
   default false; the clause
   `\<phi>log_guard_race = true` left `PLPR.thy`'s `declare` (`\<phi>log_guess_inst
   = true` stays).  One level-2 trace line per call remains, as the race had.
6. **Deleted**: `Race.race` and its racers, the protocol var, the 35 ms gate,
   `\<phi>guard_race_timeout`, `\<phi>log_guard_race` and the `guard_race`
   category, `race_result`, `checked_io`, and the two TEMPORARY probes
   `p_auto_probe` and `nitpick_probe` (they lived inside the racer bodies; §10:
   instrumentation is temporary — vetoable: their measurement, P-auto's own
   timing and R-nitpick's per-subgoal answer, is now only in the trace line);
   `guard_classic_prover_timeout` moved above the provers.  Comments: the
   `nitpick_params` note rewritten (a malformed value errors inside R-nitpick
   and propagates as the run's exception); every racer/race/ledger/hang-net
   sentence rewritten or removed in `reasoners.ML`, `guard_refute.ML` and
   `Phi_System/library/system/processor.ML` (the first draft missed nine
   such lines and claimed a clean `grep`; the review caught it, §31).
7. **`Test/Guard_Race_Smoke.thy` reshaped around `guard_decision`** (name kept
   as §10 names it; a rename to match its content is proposed below): one
   engine `decide` that computes the guard digest THROUGH THE FACTORY (a solving
   function that records what the digest step handed it — `guard_digest` is
   exported for it), writes an injected entry, installs a test judge in the
   ref (restored on every exit), drives the guard through
   `guard_condition_judge`, and asserts on the projection `(verdict, hit,
   refuter, judge, lemmas)` of the record carrying this guard's digest and on
   the entry left in the store; `decide_error` asserts an `error`'s text
   (markup stripped) by prefix.  Every guard carries a fresh numeral (`serial
   ()`), since the table outlives a re-evaluation and has no deletion.  New
   constructs `LOOP` (`LOOP n = n`, no simp rule) and `PP` with
   `PP_I[intro!]: PP (LOOP (LOOP (LOOP (LOOP x))))`: `PP (LOOP k)` is provable
   ONLY with the looping judge lemma `⋀n. LOOP n = LOOP (LOOP n)` enabled and
   cut off by its budget — the unit probe shows `enhance_with_lemmas` at budget
   3 rewrites `LOOP 0` to `LOOP (LOOP (LOOP (LOOP 0)))` and stops.  Probes, all
   passing: no entry proved / refuted by R-conv / refuted by R-nitpick /
   undecided with the undecided-guard warning and `Unknown` written / vacuous
   hypothesis proved; hits: `Refuted` silent (no refuter), `Refuted` promoted
   to `Proved`, `Unknown` warning only, `Proved` refuted by R-conv with the loud
   warning, `Proved` undecided with the loud warning; lemmas: `Unknown` entry
   with the looping lemma → proved through it (the returned context carries
   it at budget 3), `Proved` entry with it proved again under a fresh budget,
   an uncertifiable and an unreplayable lemma both dropped with the
   dropped-lemma warning and the entry rewritten, an insufficient lemma kept
   through a refutation; the judge: `Provable` replacing a seeded lemma and
   P-auto proving, `Unprovable` on no entry / on an `Unknown` hit (no refuter
   ran) / on a `Proved` hit (loud warning), both errors; `\<phi>guard_cache =
   false` ignoring an injected entry; the can_inst branches, the schematic type
   variable, `nitpick_params` pollution immunity.
8. **Evidence**: `PLPR.thy` clean under Isabelle-MCP on `Phi_System_Base` (no
   new ML warnings); the test theory clean; `PhiTest_Arithmetic.thy` clean with
   `\<phi>log_guard_decision` on: 355 decisions — 199 proved with no entry,
   120 `Refuted` hits, 23 refuted by R-nitpick, 6 `Unknown` hits, 1 undecided,
   and the §7 flips of a shared entry: 2 `Unknown` and 1 `Refuted` promoted to
   `Proved`, 2 `Proved` hits proved, 1 `Proved` hit refuted by R-nitpick — the
   loud guard warning fired once in a plain corpus load; P-auto's proofs all
   under 100 ms but one, the whole 49.6 s of guard time; no lemma anywhere
   (phase 1 has no producer).  Compared per theory with the old `guard_race`
   records, no statement decides differently.  A third load in the same
   process, the table warm from the second: the same 355 decisions, 143 of
   them `Refuted` hits and none reaching a refuter, 22.0 s of guard time —
   what the store saves is the refuters, as §7 says.
9. **An incident, recorded honestly.**  The FIRST corpus load after step 2,
   run under Isabelle-MCP while the machine was swapping (55 GB of swap in
   use, the prover's CPU time frozen for ten minutes), stalled at
   `Phi_System/Phi_Types.thy:2608` (`\<semicolon> Tr`) and spawned the AoA
   agent — an obligation there missed the proof store, Sledgehammer failed
   and the AoA gate (`aoa_allowed`: an interactive frontend, which Isabelle-MCP
   is) was open; cancelled after about six minutes of agent time.  Not
   reproduced: the second load, with the agent on its deterministic `test`
   driver, passed that statement and everything else with the decisions
   above.  The most plausible cause is the wall-clock bounds themselves —
   P-auto and R-conv now have 400 ms where the race had 2000, and under a
   ten-fold stall a guard that proves in 100 ms fails P-auto, the reasoning
   takes another branch, its obligation misses the store.  Two proposals for
   the author (§31 will carry the review's view): (a) measure the bounds in
   thread CPU (`Thread_CPU.apply`, as the proof store's replay does) rather
   than wall clock, so load cannot flip a verdict; (b) until step 5's
   re-measurement, keep every corpus load under Isabelle-MCP on the `test`
   driver — the two TEMPORARY `declare`s the drafter added to `PLPR.thy` for
   the diagnosis (`\<phi>log_guard_decision = true, AoA_driver = "test",
   AoA_write_proof_store = false`) are reverted before the commit.
10. **Proposal**: rename `Test/Guard_Race_Smoke.thy` to
    `Test/Guard_Decision_Smoke.thy` — there is no race in it any more.

## 31. Step 2's code review (2026-09-09) — rulings and fixes applied

The review (`wf_22eefcb5-61e`; six interrogators, two fresh defenders per
finding, one judge, Opus; 33 findings): **NOT ACCEPTED** — one MAJOR, one
AUTHOR_DECISION, sixteen DRAFTER_FIX (with duplicates), six rejected, no
relaxation.  Rulings, all applied, and three corrections of the plan the
discussion with the author uncovered:

1. MAJOR — `r_nitpick`'s outer net was `n × (\<phi>guard_refute_timeout + 5 s)`,
   the drafter's misreading of §6's `\<phi>guard_refute_timeout + 5 s × n`;
   restored, with the margin named once so the two bounds cannot drift
   (§30 item 2 corrected).
2. AUTHOR_DECISION (spec-3): a call from a `Proved` entry that ends `Unknown`
   printed both warnings.  The author chose (a): the loud guard warning alone;
   the two warnings are now decided at one site from the final verdict,
   mutually exclusive (§1 the undecided-guard warning; §30 item 1).
3. Three corrections of the plan, found while explaining the findings [author
   2026-09-09 "是你之前写计划的时候误解了我了"]: (i) the judge's `Provable`
   replaces THIS ENTRY's lemmas only — an earlier guard's lemma in the list
   stays; the drafter had read 08:34's "已有的 lemmas" as the whole list
   (§1 the judge, §3, §5 step 6; `replace_lemmas` deleted, `update_lemma`
   added); (ii) the judge's `ctxt` carries the list as it was BEFORE this
   entry's lemmas were added (§1, §5 step 6); (iii) a judge lemma whose
   canonical proposition is already in the list takes the judge's budget
   (`update_lemma`), where step 1's append keeps the first budget (the
   drafter's rule, unchanged for step 1 — stated as an assumption).
4. The 400 ms classic bound is THREAD CPU from now on, on every guard-side
   consumer — P-auto, R-conv, "G.simpcut", `try_prove_or_give_up`, the
   `is_F` shortcut's 250 ms — through `Thread_CPU.apply` with no wall limit,
   an error where the thread has no CPU clock; R-nitpick keeps wall clock
   [author 2026-09-09 "400ms 时限改成线程 CPU 时间. 如果相关库没加载直接报错"]
   (§1 "G.simpcut", §5 step 2, §6, §10).  `cpu_bounded`, `cpu_bounded_seq`,
   `cpu_bounded_tac` in `reasoners.ML`; `\<phi>guard_P_auto` uses the last.
5. `guard_decision`'s `lemmas` field deleted [author "(2)"] — its two
   readings (this entry's survivors, the whole list) had no consumer that
   needed either (§10, §30 item 5).
6. DRAFTER_FIX, applied: the loud warning's results text in three arms ("the
   judge was not consulted" when a refuter answered); `failure_text
   Fails_To_Certify` states the observation, not a cause; the drop write is a
   `case` on the entry, no `the`; the factory's local `ctxt_g` renamed
   `guard_ctxt` and `p_auto`'s parameter `ctxt'`, so `ctxt_g` names one
   object; the stale race/racer/ledger/hang-net/gate sentences in
   `reasoners.ML` (four), `guard_refute.ML` (three) and `processor.ML`
   (one) rewritten or removed.
7. The test theory: the cache-off probe injects `Unknown`, the verdict its call
   cannot reach; a `Refuted`-hit probe with one replayable and one
   unreplayable lemma pins step 1's drop write as the store's final state;
   `BADT` lost its elim rule so the schematic-type-variable probe reaches
   R-nitpick's screen and expects `unknown` — the control the review asked
   for was run once: with the screen disabled the probe goes red ("Nitpick
   cannot handle goals with schematic type variables"), screen restored;
   `BAD ∧ SPIN` witnesses the fixed refuter order; a `Proved` hit whose lemma
   the judge replaces, proved with no warning; every test judge is wrapped
   by `contract`, which asserts on each call that `ctxt` and `outer_ctxt`
   carry the probe context's list (not this entry's lemmas), that
   `can_inst` is the probe's and the goal state has subgoals; the
   replacement probe seeds an earlier guard's lemma, gives the entry
   `useless`, and asserts the returned list is the seeded lemma at its own
   budget followed by the judge's; a further probe re-proposes the seeded
   statement at `Only_Once` and asserts its budget became 3.  Projection now
   `(verdict, hit, refuter, judge)`.
8. Rejected with the judge (the drafter agrees): asserting warning text in
   the test theory (needs the process-global `warning_fn`; the asserted tuple
   already determines each warning's firing condition); the canonical form
   computed once per target context (pure, and the remedy re-opens the door
   §28 item 3 closed); a comment on R-nitpick's un-enhanced context (lemmas
   reach a prover only through `enhance_for_guard`, which R-nitpick never
   calls); `th` shadowing (the repository's idiom); the digest captured by a
   second factory run (checked by name on every probe); `subgoals`
   unasserted (a measurement of the bounded pass).
Verification after the fixes: PLPR.thy clean (no new ML warning); the
test theory clean; `PhiTest_Arithmetic.thy` clean on a COLD table (the table
lives in `guard_cache.ML` and a reload of it empties the table — §30's
"cold" second load had in fact inherited the entries of the theories
the cancelled first load had passed): 366 decisions — 202 proved with no
entry, 71 refuted by R-nitpick and 4 by R-conv on first decision, 75
`Refuted` hits, 8 undecided and 2 `Unknown` hits, the §7 flips 2 + 1 + 1;
102.5 s of guard time, of which R-nitpick's first decisions are the bulk
(~1.4 s each); no loud guard warning in this load.  The re-review's
record follows.

## 32. Step 2's re-review (2026-09-09) — fixes applied, pending acceptance

The re-review (`wf_59c9d545-ddb`; three interrogators over the fixes of §31 and
the new rulings, three fresh defenders per finding, one judge, Opus; 14
findings): **NOT ACCEPTED "but only just"** — the judge re-derived every
load-bearing claim and found nothing behaviourally wrong; one gap failed the
acceptance condition, eight cheap fixes, one question for the author, five
opinions deleted.  Applied:
1. The replacement probe could not fail: its entry lemma `useless` stated
   `CHAIN []`, the very proposition the seeded earlier-guard lemma carries, so
   `add_lemma` merged the two and a step 6 rooted on step 1's contexts — the
   mistake §31 item 3 (i) forbids — would have passed.  The entry lemma is now
   `useless_other` (`CHAIN [1]`), with the comment that stops anyone tidying it
   back; `contract` compares the judge's two lists with the probe context's
   statement for statement, not by length.
2. `timed_seq` and `timed_tac`, the wall-clock pair step 2 orphaned, deleted
   with `timed_tac`'s export; the "G.simpcut" comment names the shape (a bound
   whose timeout is an empty sequence) instead of the deleted function.
3. `add_lemmas` is pair-valued over the call's two base contexts `(ctxt0,
   ctxt)`: `val (ctxt1, ctxt_g) = add_lemmas add_lemma replayed` and `val
   (ctxt1', ctxt_g') = add_lemmas update_lemma replayed'` — step 6 can no longer
   be written on step 1's result.
4. The R-nitpick comment's "strictly below the sum of the bounds per subgoal"
   was false at one subgoal (equal there); it now says "below … from two
   subgoals on, equal to it at one — so the net normally ends R-nitpick inside
   the running subgoal".
5. "knife" (a coined word for a bound) removed from `guard_refute.ML`'s two
   rewritten comments; §4's "`ctxt_g` itself, which the judge receives" corrected
   to `ctxt`; the four contract labels in one grammar; the test theory's two engines
   share one `run_guard` seam, so the judge ref is installed and restored in
   exactly one place.
6. Deleted with the judge: `pair ctxt0` bound once (a re-filing of the nitpick
   §28 discarded); the warning site as one `case` (weaker than the `if`'s
   structural exclusion); the trace line through `info_pretty` (`warn_pretty`
   is the trace-gated channel, four sibling sites); the dead `timed` of
   `guard_refute.ML` (pre-existing, inside a block marked TEMPORARY); a
   claimed `expect` shadowing (none exists).
The author's answers (2026-09-10): `timed1_tac` confirmed dead (its
definition is its only occurrence in the repository) and deleted; the
test theory renamed **`Test/Guard_Decision_Smoke.thy`** (§10 step 2's
`Guard_Race_Smoke.thy` is this file); the probe categories `p_auto_probe`
and `nitpick_probe` stay deleted, and with them the last piece of the race
era's scaffolding, `guard_refute.ML`'s TEMPORARY `refuter_probe` category
with its `plain_term`, `probe_lock` and the timing inside `nitpick` — the
function is now the preprocessing and the one Nitpick call.  Not touched:
`\<phi>log_guess_inst = true` in `PLPR.thy` and the `guess_inst` category
(`guess_instantiate.ML`), another subsystem's instrumentation, left for the
author to rule on.  One measurement worth recording: with the corpus
imports reloading alongside the test theory, the `CHAIN`-of-1000 probe once
missed the 400 ms bound although it proves in ~220 ms on a quiet machine —
thread CPU excludes waiting but not the slowdown contention inflicts on
the work itself; the construct is now 700 elements, well inside the bound.
Rulings of 2026-09-11: the 400 ms bound stays at 400 ms; it is P-auto's, and
R-conv, "G.simpcut" and the `is_F` shortcut — all searches on the calling
thread — keep thread CPU as implemented ("没问题. 就这样继续"); R-nitpick keeps
wall clock, since Nitpick's work is not this thread's CPU.  The flip of §30.9
is shelved until it recurs ("等这个问题又再次出现了我们再说").  A measurement made
before the shelving, with a TEMPORARY probe (P-auto's thread CPU per decision,
the bound raised to 10 s; both reverted; the load was ~12 on 14 cores): over
341 decisions every proved guard's P-auto took at most 204 ms of thread CPU
(p99 133 ms); guards P-auto cannot prove burn CPU until the bound; and the two
guards that flipped at `Phi_Types.thy:2608` proved in 0 ms — so that flip was
NOT a bound miss: P-auto returned empty at once, cause unknown (the drafter's
one hypothesis: an in-flight cancellation of a PIDE re-evaluation converted
to `TIMEOUT` by `accounted_timeout.ML`'s shadow and read as "failed").
Verification after these fixes: PLPR.thy clean (the same four pre-existing ML
warnings, `timed1_tac` among them; three after its deletion); the test theory clean; `PhiTest_Arithmetic.thy`
clean on a warm table (355 decisions, 145 `Refuted` hits, no first
refutation, 22.1 s of guard time; one loud guard warning on a §7 flip); the
TEMPORARY diagnostic declare reverted and PLPR.thy re-evaluated clean.

## 33. The `Phi_Types.thy:2608` flip diagnosed (2026-09-11) — pending the author's fix

The flip of §30.9 recurred on the close-out corpus run and the author lifted
the shelving ("你再跑一下？会不会是 digest 碰撞？"; "你可以随意加临时探针调查此事件").
Diagnosed with TEMPORARY probes, all reverted (`reasoners.ML` and
`Phi_Types.thy` restored; the analysis scripts in the session scratchpad):

1. **Not a digest collision.** The decision record's `subgoals` field
   separated the two guards' 42 decisions cleanly: every 0-subgoal decision
   was `proved` in 0 ms, every 1-subgoal decision ran to the 400 ms bound.
   The digest is taken BEFORE the "G.simpcut" pass and the subgoal count
   AFTER it, so the same guard reached P-auto in two shapes: fully
   simplified away (nothing to prove) or untouched.  The pre-pass goal texts
   under one digest were identical.
2. **The cause: the "G.simpcut" pass's 400 ms thread-CPU bound is too tight
   for these guards.** With the pass's own thread CPU recorded per decision:
   under the 400 ms bound, of 368 corpus decisions the 19 "G.simpcut"
   timeouts all belonged to the six guards of `Phi_Types.thy:2591–2611` and
   `:2690–2734` (the `len_intvl` arithmetic guards; `linarith_split_limit`
   traces); every other guard's pass stayed under the bound (proved p99
   359 ms, max 384 ms; refuted max 359 ms).  With the bound raised to 4000 ms
   on that segment alone, at load 2.0, the pass took 437 ms and 420 ms for
   the two flipping guards (`45bdcdbe2e68b82b`, `cb5b59ba802ff7ed`) and
   371–400 ms for the twin calls in the second lemma; the segment was clean.
   Back at 400 ms, at load 1.5, both timed out again and the statement
   failed — so the flip is not load: the guards' cost straddles the bound
   (371–437 ms across calls and runs) and the run-to-run variance decides.
   The pass's timeout is silent and yields the unsimplified state, and P-auto
   then repeats the same work under its own 400 ms and fails.  §32's "not a
   bound miss" was wrong: the 0 ms P-auto figures were the good runs, and
   the decision timer (`prove_or_refute`'s) starts after the pass.
   Before step 1 (`5103d7b6`) this pass ran unbounded inside the old
   `auto_tac`; the bound is step 1's [author 2026-09-09].  Wall/CPU of the
   pass was 100–118 %: the CPU clock is honest.
3. **Side finding — the `is_F` shortcut's search never runs.** For a guard
   that is literally `\<condition> False` (the idiom of `Phi_BI.thy`
   `ToA_case_sum_src`, `ToA_case_sum_src_R`: prove the contextual premises
   inconsistent, cut the chain), `simpcut_tac` either closes the goal (simp
   finds the contradiction) or `quick_cut` drops the state on the `False`
   conclusion — so the 250 ms `auto_search_tac` of the shortcut only ever
   sees a state with no visible subgoal, or is not entered.  Measured with
   `ai-artifacts/Guard_False_Probe.thy`: useful facts `x = None`, `x = Some y`
   → PROVED in 1 ms; `∃x. ∀y. RR x y`, `∀x. ¬ RR x x` → FAILED in 1 ms
   (empty; `blast` and `auto` prove it, `asm_full_simp` and `p_auto_body` do
   not).  The idiom is therefore simp-only; the search was dead in the
   2024-05-15 original too (`9d3bd92c`: the same simp-and-quick_cut before
   the `is_F` split).  Not unsound: an undetected contradiction leaves the
   inconsistent branch unpruned.
4. **Side finding — the loud guard warning fires by design on a shared
   entry.** Digest `3d7696d10790e4a8` (`\<condition>[\<no>-\<inst>] x = None`)
   is reached from two call sites with different aux facts: with `x = None`
   among them simp closes it (0 subgoals, `Proved` written), without it
   R-nitpick refutes it (`Refuted` written); every warm run flips the entry
   and warns once.  The consequence of §1's sharing ruling ("the entry is
   advice"); the warning is a false alarm there.  Not a digest collision:
   the two calls' digested subgoals are the same text, so the key is the
   same by construction [drafter, on the author's question 2026-09-11].
   RESOLVED 2026-09-11 by the author's ruling on the digest itself: the key
   is the whole goal state plus the context's assumptions (§1 guard digest,
   with the correction of the record there — the subgoals-only key was the
   drafter's narrowing, never the author's ruling).  Measured first, on the
   author's instruction, with TEMPORARY probes by an Opus agent (both
   reverted; the same 355 corpus decisions each time): (i) subgoals +
   aux facts + assumptions — hashing 40 us more per decision, keys 144 →
   200; (ii) whole state + assumptions, aux excluded — the digest 76.8 us
   per decision against 4.8 us (0.12 % of the 22.5 s of guard time; the
   state is the payload, mean size 182 against the subgoals' 14), keys
   144 → 261 over all 355 decisions (repeat rate 59.4 % → 26.5 %), and over
   the 162 decisions that hit the store 84 → 162, no repeat at all; the
   whole state alone gives 259 of the 261 keys, the assumptions 2 more.
   The author chose (ii) ("确定: state + contextual assumptions 的方案");
   the aux facts stay out because they are derivable.  With it the two
   call sites of this item get different keys and the warning no longer
   fires for that reason.
5. **Rename applied** [author 2026-09-11]: the factory `guard_condition_solver`
   is `gen_guard_condition_solver` (`reasoners.ML` `:94`, `:1582`, `:1616`,
   `:1625`; `PLPR.thy:1995`; `Test/Guard_Decision_Smoke.thy:71`;
   `guess_instantiate.ML:307`).  The instances `guard_condition_solver'` /
   `guard_condition_solver1` keep their names.  This document now uses the
   new name wherever it means the factory ("更新一下"); the old name stays
   only inside quotations of the author and where it means the pre-factory
   function of before step 1 (§1's migration note, §11 item 3).

**Rulings of 2026-09-11 on item 2, applied**: the "G.simpcut" pass's bound
is 5 s of thread CPU, fixed in the code with no option ("直接定死 5s x the
scale" — `Thread_CPU.apply` applies `timeout_scale` itself); on its timeout
the pass warns, unconditionally, `The system simplifier probably loops on:`
with the visible subgoals, then behaves as before (the unsimplified state
to the solving function: "超时并警告之后, 保持现状"); P-auto and R-conv stay
at `\<phi>guard_classic_prover_timeout`'s 400 ms (a refuted guard burns
P-auto's whole bound before R-nitpick: 900–2300 ms at a 4000 ms bound, so
P-auto's bound must not grow with the pass's).  `simpcut_tac`, used
nowhere else, is now a local function of `gen_guard_condition_solver`
("建议挪动进 gen_guard_condition_solver 里").  §1 "G.simpcut" and the §10
option table carry the ruling.  [The last sentence is superseded on
2026-09-15, §39: the pass is `guard_simp_tac`, top level again, called by
`prove_or_refute` on the context that carries the entry's delta and by
`p_auto_solving`, not by the obligation instance;
"P-auto then repeats the same work" above was left standing on
2026-09-11 and is what broke `Quicksort.thy`.]

**Rulings of 2026-09-11 on the rest**: the `is_F` shortcut stays as it is
and its repair is left to the follow-up below ("留给 \<check> \<hypothesis>
\<consistency> 后续"); the `\<phi>log_guess_inst = true` declare of
`PLPR.thy` (the guess_inst experiments' instrumentation of 2026-08-30) is
deleted ("删除"); item 4 is explained to the author, decision open.

**Follow-up proposed by the author (2026-09-11), after the current work**: a
new antecedent constant `\<check> \<hypothesis> \<consistency>`, defined as
`False`, and reasoners dedicated to it and to `\<condition> False` — at a
priority above the condition solver — whose one job is proving the
contextual premises inconsistent, replacing the `is_F` shortcut as the home
of that idiom.

**The tier measurement (§10 step 3, second half) — brainstormed, SHELVED
[author 2026-09-11 "先记录结果, 搁置这个问题, 这是我们之后才要处理的"].**
An Opus panel (four proposals, eight critiques, one judge; the dossier in
`ai-artifacts/TIER_MEASUREMENT_BRAINSTORM_2026-09-11.md`) produced a
three-stage plan: A — capacity (how many charges one consumer run can
afford under its own thread-CPU bound; no corpus run; plus the `mksimps`
arity per lemma); B — one instrumented corpus run counting applied
rewrite rules per consumer run, the run boundary being the four
`enhance_for_guard` call sites (each call of `enhance_with_lemmas` makes a
fresh budget table, so "one consumer run" is one such call), reporting the
invocations-per-run multiplier of §7 and the per-(run, rule) demand
against 3 / 30 / 300 / the ceiling, with the bounds raised tenfold on the
measurement legs because the probe's CPU is charged to the clock that
decides verdicts; C — the starvation counterfactual (real rules deleted
from the guard-side simpset and re-injected as budgeted lemmas; perturbs
the corpus).  The drafter's decision when the work resumes: A and B, not
C unless the author allows the perturbation.  Structural facts the judge
verified, to be settled with the judge's design in phase 2: a budgeted
lemma's rules are always CONDITIONAL, so `sort_rrules` tries them after
every unconditional rule at the same redex and `simp_depth_limit` (40)
refuses them deep in a simplification; `Frequent` is an alias of the
ceiling (`budget_of_tier` returns `limit`), so `Normal >= limit` merges
the top two rungs; the "duplicate rule is ignored" story of the drafter
was wrong (`eq_rrule` compares propositions, and the budget premise makes
them differ).  Semantics ruled [author 2026-09-11 "我认为是 整条 lemma 一次
run 内合计 3 次"]: a budget counts the rewrites of ALL rules derived from
one lemma, accumulated over the whole consumer run — the code's present
semantics; the value of `Only_Once` under it is the product of the
lemma's `mksimps` arity and the number of times one run re-rewrites the
same redex (P-auto's search backtracks past the rewrite), to be read off
stages A and B; 3 stays until then.  The judge's two proposed permanent
changes (per-lemma charge fields on `guard_decision`; retrying once at a
raised limit before the "judge is broken" error) are not adopted; open.

## 34. Step 3, first half done (2026-09-11) — the export hook end to end

`Test/Guard_Export_Smoke.thy` (not in any ROOT; evaluated on demand on
Phi_System_Base like the other smoke theories; test design the drafter's,
by the author's delegation "与测试相关的事项可以由你自主决定").  Two guard
families `GX`, `GY` with no rule at all, so a guard of theirs ends with the
judge (P-auto cannot prove it, R-conv cannot refute a truth, R-nitpick
finds no countermodel); a test judge in the ref answers the family's lemma
(`\<And>n. GX n` by `(simp add: GX_def)`, `Normal`) on its FIRST consultation
per family and raises on any later one — the failure signal "the lemma did
not arrive".  A trigger reasoner (`\<phi>reasoner_ML`, highest priority,
no cut, on `PROP ?P`, like `Stateful_Reasoning_Smoke`'s marker) decides,
when armed, a fresh guard of the armed family through the real machinery
(`guard_condition_judge` on the run's context) and continues the run in
the context that call returns.  Every guard argument is a process serial:
the in-memory store outlives a re-evaluation.  Verified clean:
(a) one run, two guards — `GX2_rule`'s `\<condition> GX a \<Longrightarrow>
\<condition> GX b \<Longrightarrow> GX2 a b` driven by `Phi_Reasoner.reason`:
the judge consulted once, the second guard proved with the lemma, and the
context the run returns (through the hook at the run boundary) carries it;
(b) a `proc` block: the lemma enabled by statement 1's run is in the block
context after the statement and the next statement's guard is proved with
it (the judge still at one consultation);
(c) a nested block — the FIRST branch of an `if` — enabling `GY`: the
second branch starts from the enclosing context as the first branch's
close left it (`GY` present at its entry), the enclosing block holds the
lemma after the `if`, and the statement after the `if` proves its `GY`
guard with it.  CORRECTION: the drafter first wrote here that the two
branches are sibling blocks from one starting context, so that the
second branch's close — the hook OVERWRITES the enclosing list (§1, H2) —
would lose a lemma enabled in the first branch; the author doubted it
("第二个分支应该是继承了第一个分支写入到 the outer context 的内容的, 对吗?")
and the measurement (this test, 2026-09-12) proves the author right:
each branch's close writes the enclosing context, the next branch starts
from that context, and overwriting loses nothing.
One fact worth the record: a theory that imports `PhiSem_Machine_Integer`
next to `PhiSem_Int_ArbiPrec` cannot open the branch of an `if` on a
`\<val> \<nat>` (`Thm.cprem_of` on a goal without premises in
`toplevel0.ML`'s block open — the `@{print}` at `:267` is a leftover) — a
pre-existing phi-system matter outside this plan, avoided by importing what
`PhiTest_Arithmetic` imports.

## 35. Step 4 done (2026-09-12) — the persistent store, redone on the author's design

**What was done** (§8, §10 step 4).  `guard_cache.ML`: a guard's entry is
one record of the theory's proof store, `<thy>.proof-store`, written and
read through `Phi_Proof_Store.update_cached_proof thy {id = "PLPRGUARD" ^
Hasher.compact d, hash = NONE} (zero_times, payload)` and
`get_cached_proof thy key`; the entry codec over `MessagePackBytesIO` — a
statement through `RPC_Pretty_Bytes.pack_raw_term`, a lemma's times as
the `(cpu_ms, wall_ms)` pair, tier and verdict as int tags, no format
version, `decode_entry` a catch-all `\<^try>` answering `NONE`; the
in-memory table of step 2 deleted.  Nothing in `auto_sledgehammer`
changes; nothing is gitignored: the entries live in the tracked
`*.proof-store` files beside the proofs [author 2026-09-12 "1. 好"].
`Test/Guard_Decision_Smoke.thy` and `Test/Guard_Export_Smoke.thy`: `fresh`
is a wall-clock run tag plus the process serial, since the store outlives
the process (a repeated numeral would meet an earlier run's entry).

**CORRECTION of the record.**  The first implementation of this step
(auto_sledgehammer `316f143`, phi-system `1cc4e95e`) made the proof
store's body a functor and wrote guard entries through a second instance
into a gitignored `<thy>.guard-cache`; that shape came from a review round
(seventh review U6) and was filed under author citations that answered
narrower questions (§8).  The author rejected it on 2026-09-12 ("纯粹是胡
闹…必须撤回这些"); auto_sledgehammer `5ac4877` reverted `cache_file.ML`
byte for byte to `1360b21`, and the review of that implementation is
void.  The `guard_decision` record, the digest, the test theories' `fresh` and
the corpus figures below are unaffected by the store's shape.

**Verification** (`Phi_System_Base` rebuilt on the author's approval of
2026-09-12): PLPR.thy clean; both test theories clean; the corpus clean cold in
one process (355 decisions, every one a miss, 129 s of guard time, entries
written into the tracked proof stores of seven theories) and in a NEW
process (146 `Refuted` and 5 `Unknown` hits read from the proof stores,
21 s).

**Review** (an Opus panel: four interrogators, more fresh defenders, a
judge): accepted on condition.  Two items are the author's: the proof
store's key-collision alarm (§8; ruled 2026-09-13, §36 ruling 9) — it
fired on every legitimate rewrite of a guard entry, e.g. `Unknown` →
`Proved` under one key; and which of the new `*.proof-store` files to
track (ruled: the test theories' are not).  Rejected, with reasons in
`ai-artifacts/STEP4_REDO_REVIEW_2026-09-12.md`: a digest-vs-text alarm,
content-key accumulation, `Hasher.hex` for the key, an FNV soundness note,
a single end-of-call write, "Unknown freezes R-nitpick", a `cpu_bounded_seq`
rewrite.

## 36. The delta redesign (2026-09-12) — an entry is a delta; the canonical form withdrawn

**Rulings**, in the author's words, in the order given.  The occasion was
the provenance audit's finding that the canonical form (§22–§24) had been
shaped by three review rounds with no ruling; asked what it was and why it
existed, the author found the problem it solved not worth a mechanism
("这个去重仅仅是为了性能优化, 为了重用是吗? 其实不做这个去重, 就老老实实全都丢掉,
然后全都去证明新的 lemmas 也没有问题, 对吗?" — the drafter confirmed: the copies
cost a budget each and one conditional rule each, never soundness, and
replay is paid on every call regardless) and redesigned the entry:

1. "我建议我们修改一下设计, 每个 guard condition 的 judge lemmas 实际上是一个
   pair: 新增的 lemmas, 与要删除的 lemmas (term list). 增量的去做" — and the
   reason the old "replace" existed is weaker now: "我当时说替换掉坏的 lemmas
   是担心坏的 lemmas 太多, 但现在每个 lemma 是有 bound number of applications,
   所以我感觉问题应该不会很大".
2. What a deletion targets: "当然是当前 context 的 lemma list 里的所有 aconv
   的, 包括别的 guard 带进来的".
3. "每个 condition 的 slot 永远是相对于之前的 ctxt 的增量.  judge 的输出永远是对
   the condition's slot 的完全替换" (the slot = the entry); "删除是持久的, 添加
   也是持久的".
4. The judge's input, resolving the drafter's objection that "judge sees the
   list after the delta" and "the judge's answer replaces the delta" cannot
   both hold: "传入 judge 的应该是两个参数, guard_ctxt 和 delta".
5. "终于可以删除 canonical_form 这傻玩意儿了".
6. Identity for deletion and for the append's duplicate check: the drafter
   first proposed the judge's statement kept beside the theorem, since
   export changes a theorem's proposition; the author: "删除去重等可以直接看
   the lemmas 的 prop 吗? 反正这些 lemmas as thms 也会发给 the judge 对吗" and
   "the judge 始终是在这一刻删除那个 thm 对吗? 一切重放都是确定性的对吗? 那为什么
   会变呢?" — right: at one call site every hit sees the same list, so the
   proposition, compared by `aconv`, is the identity (§1 the lemma list);
   the residual case (one digest reached from two sites whose boundary
   histories differ) only makes a deletion not fire there.
   Beforehand the author asked whether the statement could be exported in
   step with the theorem ("我们可以把 the stmt 也导出吗? 导出后理想情况下应该是
   同步的, 对吗?"); an Opus agent measured it (`ai-artifacts/Export_Sync_Probe.thy`,
   14 cases under `Main`): no — `Assumption.export_term` is the identity for
   every export rule in the tree, `Variable.gen_all` exists for theorems
   only, and the type-variable index and set differ between the two paths;
   the two agree only when the boundary is a no-op on the theorem.
7. From the code review of this redesign (2026-09-13, below): the append's
   collision rule.  Step 1 kept the existing budget (the drafter's
   assumption of 2026-09-09 11:35, never ruled) while step 6 took the
   judge's, so an entry written by step 6 did not rebuild, on replay, the
   list the recording call returned.  Ruled: "SEM-2 (a), 用 Pattern.equiv 去
   做相同性比较" — ONE rule, the delta being applied wins, and the identity
   is `Pattern.equiv` (equal up to renaming of schematic variables), for
   the append's check and for a deletion alike.  `update_lemma` is gone.
8. Also from that review: a replay that overruns its recorded time budget
   is dropped from the entry like a broken lemma (the wall limb of
   `replay_limits`, 2·wall + 3 s, is wall clock — `Thread_CPU.apply`
   enforces it with `Timeout.apply`, scaled by `timeout_scale` like the
   thread-CPU limb; both limbs are first floored to the classic bound, so
   the cap is at least 3.8 s).  Ruled: "P3 维持现状。… 2×wall + 3s 已经很高了"
   — the status quo.
9. The proof store's key-collision alarm on guard entries (§8).  The
   author first corrected the drafter's picture: "整个推理是线性无环的, 为什
   么第二条语句会再命中 S? 第二条语句哪怕是再遇到相同的 guard condition 也应
   该具有不同的 key 啊!" — right: with the whole-state digest the only
   repeated key inside one evaluation is a deliberate rewrite of a guard's
   own entry (the drop write then a verdict write in one call; a test
   theory's injected entry then the decision) or a 64-bit hash collision.
   Then: "对于我们知道要改变判决的时候, 可以显示地 suppress 那一刻的防撞探针
   吗?" → the write says it rewrites its own key: `update_cached_proof
   thy {id, hash, rewrites}`, `rewrites = true` from `write_entry` only —
   "好的, 赞同, 赞同 rewrites".  And the marks are dropped at theory begin as
   well as at theory end ("同一次改 cache_file.ML 时是否顺手把 written 表在
   Theory.at_begin 也清掉" — "好的"), restoring the author's 2026-09-12
   objection that a process-global `Synchronized.var` survives a
   re-evaluation in jEdit.  `auto_sledgehammer` (`cache_file.ML`,
   `sledgehammer_solver.ML`, its test theory), `Isa-Mini` (three writers
   and its test theory) and `guard_cache.ML` changed together.

**What changed** (`guard_cache.ML`, `reasoners.ML`, the two test theories;
plan: the status lines, §1 lemma/entry, the judge, the lemma list, the
export hook, §3 — its pipeline block collapsed to a pointer at §5, the one
description, §4 — the file manifest gains `delta`, §5 steps 1, 3, 4, 6,
§7, §8, §9, §10).  `type delta = {added : lemma list, deleted : term list}`,
`type entry = {delta : delta, verdict : verdict}`, `empty_delta`;
`delete_lemmas : term list -> Proof.context -> Proof.context`;
`add_lemma` takes the theorem and its budget only (no `ctxt0`: nothing is
normalised) and is the one append rule (ruling 7; `update_lemma` gone);
`canonical_form` deleted.  The codec packs
the triple (added, deleted, verdict); an entry of the previous shape does
not decode and is no entry (§8), so the corpus's first run after the change
is cold.  `judge_arg` gains `delta`; `judgement = Provable of delta |
Unprovable`.  `prove_or_refute`: `apply_delta` puts a delta — deletions,
then replayed lemmas — onto `ctxt0` and `ctxt` (step 1 with the entry's,
step 6 with the judge's, both from the lists of the moment before step 1)
and returns the delta it applied, which is what every write stores; the
delta handed to the judge has its times converted to this machine's
clock (§1 the judge).  `Test/Guard_Decision_Smoke.thy`: the judge
contract also checks `delta`; probes added — an entry deleting the seeded
lemma of an earlier guard, a deletion naming nothing (the seeded lemma
survives: the over-deletion check), a replayed
entry giving the seeded lemma its budget, an entry with a deletion under
a judge (the judge's delta replaces it whole), the judge deleting the
seeded lemma (the deletion written), a deletion carried through a
refutation.  `Test/Guard_Export_Smoke.thy`:
the judge answers a delta; `fresh` as in the other test theory (the review's
open item).

**Verification** (Isabelle-MCP on the `Phi_System_Base` heap of 2026-09-12):
PLPR.thy clean; both test theories clean; the corpus (`PhiTest_Arithmetic.thy`
and its imports) clean in the same process, cold — 355 decisions, 261
digests, every one a miss (the old entries do not decode), 204 proved, 146
refuted (142 R-nitpick, 4 R-conv), 5 unknown, 136 s of guard time — the
distribution of §35.  Then, the heap rebuilt by the author (it had gone
stale under other sessions' changes), the warm run in a NEW process: the
corpus clean, 355 decisions, 146 `Refuted` and 5 `Unknown` hits read from
the proof stores, 20.6 s of guard time.  The proof store's key-collision
alarm fired on the test theories' legitimate `Unknown` → `Proved` rewrites
(§35, OPEN).

**Review** (2026-09-13, two rounds, each a workflow of Opus interrogators,
three fresh defenders per finding and a judge; the reports in
`ai-artifacts/DELTA_REDESIGN_REVIEW_2026-09-13.md` and
`…_REREVIEW_2026-09-13.md`).  Round one, 96 agents, 30 findings:
ACCEPTED_ON_CONDITION — the author ruled SEM-2 (ruling 7) and P3 (ruling
8); the drafter applied SEM-1 (the clock conversion), the identity fix,
the documentation residue, the over-deletion probe and the others listed
above.  Round two, 65 agents, 20 findings: ACCEPTED_ON_CONDITION, no
defect in executable behaviour; the author ruled that the identity stays
plain `Pattern.equiv` — no handling of outer binders ("别这么专门处理") — and
that the judge contract does not constrain `deleted` beyond `same_prop`
being total (an ill-formed statement is the proposition of no theorem);
the drafter corrected its own false sentence about the replay (it keeps a
`⋀n.` binder; the boundary export generalises it), collapsed the five
identical writes into `keep`, and added the `RR` probe (a deletion
observed in the provers' context), the `Pattern.equiv`-vs-`aconv` probe
and the delete-before-add probe.  Rejected findings, with the rebuttals,
in the two reports.  P5 ruled: the two test theories' `.proof-store` files
are not tracked and not ignored.  After the round-two fixes: PLPR.thy,
both test theories and the corpus clean again (355 decisions, 146
`Refuted` and 5 `Unknown` hits).

## 37. The provenance audit gone through (2026-09-14) — rulings

The audit of 2026-09-12 (`ai-artifacts/PROVENANCE_AUDITS_2026-09-12.md`)
listed designs that had reached the code without a ruling.  The author
went through them one at a time; each item was explained (essence first,
then the mechanism, with `file:line`) and ruled in the author's words
below.  Items of other repositories are recorded here too, since this is
where the audit lives.  No code changed before its ruling.

**The guard cache (audit B2).**
1. `guard_decision`: "建议用 ML_debugger 这个 configuration option 来控制, 可以保留
   为永久" — the record is permanent; its switch `\<phi>log_guard_decision`
   is deleted and the write is gated on the runtime value of `ML_debugger`
   ("对": it replaces the option, the two do not stack).  Fields unchanged.
2. The loud guard warning: "A guard condition proved before is now refuted
   by the LLM judge:" is the whole text, followed by the subgoals ("'The
   refuters and the judge answered:' 为什么两个主语? … 我感觉甚至不需要这句话");
   it fires only when the judge overturns a `Proved` entry ("只有在
   previously proven but the LLM judge now refutes 的时候说 … R-conv/R-nitpick
   都是靠谱的, 都是可信的, 此时就不用报警"); a refuter's verdict over a `Proved`
   entry is silent and an `Unknown` ending gets the undecided-guard
   warning, as without an entry (the drafter's reading, confirmed).
3. The dropped-lemma warning stays unconditional ("我认为可以保留无条件").
4. `\<phi>log_guess_inst`: "赞同 (a)" — the `guess_inst` record stays, the
   option is deleted, the write is gated on `ML_debugger` like item 1.
5. The export hook's priority 200 stays ("我觉得 200 可以的"; 0 is the
   highest priority, `Hook.ML:10`).
6. The decode: "赞同 (a) + (c)" — an entry that does not decode is silently
   no entry (the only normal cause is a format change; the key is
   overwritten on the spot), and the handler catches `Subscript` and
   `Unpack` only, so any other exception surfaces as the bug it is.
7. The judge's lemmas MAY cite contextual assumptions, by name: "我认为必须
   可引用 contextual assumptions 这是很重要的! … PLPR 整个推理是确定性的, 复现是同
   一个 ctxt 具有相同的 fact names".  No mechanism changes; §1's contract
   clause is corrected (it had said the opposite, under a citation that
   did not carry it).  The drafter's proposal to insert the assumptions
   into the replay goal was withdrawn as unnecessary ("纯粹是胡闹").
8. The replay's goal: `Goal.init` and `Goal.conclude`, the standard pair,
   at the call site ("你自己加的壳由你自己解"); `Thm.trivial` gone.
9. Phase-2 points: (1) a budgeted lemma's rules being conditional rules
   — "现在就定了, 直接接受"; (2) `Frequent` = the ceiling — "阶段 2 一起定";
   (3) is item 7.
10. The tier measurement (§33): "(a)" — stays shelved until after step 5.
11. The `\<check> \<hypothesis> \<consistency>` follow-up: "赞同" — a plan of
    its own after step 5.
12. Step 5: "赞同" to the drafter's proposal — right after this round's
    implementation and review; the corpus of the earlier runs first, then
    `Phi_Examples` as an extra leg; the consecutive-run leg's floor is
    100 % hits and 0 flips; the concurrent leg is two Isa-REPL processes.
13. `Phi_System/Resource_Template.proof-store` stays tracked ("保留").  The
    audit's own "unverified" list is not urgent ("不用着急").

**The proof store (B3)**: ruling O's widening to the whole record ("赞同
保留"); the goal hash of a runtime symbol by its identifier (`0146687`,
"追认"); the "Find proof" trace at the search sites only (`c88ad1d`,
"追认").  **phi-system (B4)**: the theory-qualified keys of derived
obligations (`752be368`, "追认"); `bool`-typed arbitrary-precision
comparisons in generated C (`d4cbde68`, "追认"); the failure text "Fail to
solve the proof obligation automatically" is the author's own from 2023
(`ccbe42f8`), the audit had misdated it — nothing to rule.  **Isa-Mini
(B5)**: the price table is the drafter's to refresh from the official page,
"但必须确认是对的"; the cost line's format stays, the false "(author-finalized
format, 2026-08-10)" in its comment is deleted.  **Performant_Isabelle_ML
(B6)**: the Event_Log default directory `$ISABELLE_HOME_USER/event_log`
("赞同"); the record boundary is the comment line `<!-- record -->` before
every item, the review agent's space-stuffing transform withdrawn ("你这个边
界太黑了, 我记得我当时的意见是用注释来标记每个对象的开始"; "标记文本就用 <!-- record
-->"; "旧日志文件请你迁移" — done by `ai-artifacts/event_log_migrate.py`, 591
files, 303 609 records before and after); Dynamic_Array was the author's
own order (2026-09-08 10:56), the audit had missed the session.
**Semantic_Embedding (B7)**: D19 (an empty wire statement keeps the stored
`expr`) "追认", the plan row now names the drafter.  **Isabelle_RPC (B8)**:
the `pretty_unicode` / `FileIndex` divergence (private-use symbols, a
drift of six columns per symbol, measured live) becomes a plan of its own
after step 5 — one rendering function shared by both ("请记一下, 作为单独一
个计划之后去实施"); the map size and the version bump "追认".  **The jEdit
slice (B9)**: the 78 old-grammar orphans stay ("留着, 别动"); `phi_field_font`,
the generator-written font name table and the primary-selection wrapper
"追认".

**Accountability** ("对这种对我当时的决策的偏离请问责然后报告"): two departures
were found and reported — the Event_Log boundary (a review agent's
mechanism replacing the approved design under a blanket go-ahead) and
D19 (the drafter's decision recorded as the author's); feedback drafts
filed for both, and for the drafter's repeated forgetting of PLPR's
determinism.

**What changed in code** (rev 26): `reasoners.ML` — the option gone, the
record under `ML_debugger`, the loud guard warning's text and condition,
`Goal.init`/`Goal.conclude` in `replay_lemma`; `guess_instantiate.ML` —
the option gone, the record under `ML_debugger`; `guard_cache.ML` — the
narrowed handler; `Test/Guard_Decision_Smoke.thy` — `declare
[[ML_debugger]]`, the three probes whose ending changed, and `warnings_of`
/ `assert_loud` observing the loud warning (0 on a refuter's verdict, 1 on
the judge's); Isa-Mini `agent_server.ML` — the comment; Performant_Isabelle_ML
`event_log.ML`, `tools/event_log.py`, `Test/Event_Log_Test.thy`,
`EVENT_LOG_PLAN.md` §5/§8 — the marker format; Semantic_Embedding's plan —
the D19 row.

**Verification**: PLPR.thy and both test theories clean under Isabelle-MCP
on the current heap; the marker format checked by a TEMPORARY probe
(`Performant_Isabelle_ML/ai-artifacts/Event_Log_Marker_Probe.thy`, three
records byte-for-byte, the comment skipped) because `event_log.ML` is
compiled into the heap — `Test/Event_Log_Test.thy` runs after the next
rebuild; the migration verified on a copy first (record counts equal),
then applied.

## 38. Step 5 run (2026-09-14) — corpus acceptance via Isa-REPL, pending the author's acceptance

Shape as ruled (§37 item 12): one fresh Isa-REPL server per leg on the
`Phi_System_Base` heap, the corpus loaded from source, wall clock by the
harness (`ai-artifacts/step5/run_leg.py`), the `guard_decision` records
read back by `ai-artifacts/step5/analyze.py`; the full report with every
number is `ai-artifacts/step5/STEP5_REPORT_2026-09-14.md`.  The corpus:
`Phi_Test.PhiTest_Arithmetic` and its imports (355 decisions, 261 digests),
then the eight `Phi_Examples` theories as the extra leg.  The legs that
count decisions run under `declare [[ML_debugger]]` (the record's gate,
§37 item 1), a TEMPORARY declare in `PLPR.thy`, reverted.

**Floors — MET.**  Consecutive runs (cache on, twice, fresh process each):
261 of 261 digests in common, 0 flips, 151 of 151 non-proved decisions hits
(100 %); wall 320 s then 213 s; guard time 24.5 s then 21.7 s.  Cache on vs
cache off: 0 flips over the 261 digests; cache off costs 161 s of guard
time and 412–416 s of wall against 21.7 s and 213 s.  Concurrent: two
servers loading the corpus at once, 0 flips between them and against the
sequential run, 100 % hits on both, and the store file both rewrote at
theory end (`compact_store` under the `fcntl` lock, the rewrites
overlapping in time) byte-identical to HEAD afterwards.  (The first
version of this section also claimed "no collision warning"; withdrawn on
review — the collision marks exempt guard entries by design, see one
process only, and the REPL server silences warnings, so the claim was
vacuous.)  Phi_Examples:
1756 decisions over 1646 digests, 703 of 708 non-proved decisions hits,
no guard-side exception.  The 400 ms bound re-measured: proved decisions
p99 76–108 ms, far under it; refuted decisions reach it because P-auto runs
to the bound before the hit is honoured (§5 step 2, accepted §17 item 5).

**Two observations outside the guard cache, both ruled.**
1. `exception Option` aborted both uninstrumented cache-on legs at
   `Phi_Types.thy:2591` / `:2594` (the `len_intvl` lemma of §33).  It is the
   bug closed on 2026-09-08 in `OPTION_EXCEPTION_IN_PROOF_REPLAY.md`
   (`future.ML`'s `assign_result` swallows an asynchronous interrupt, then
   `the` on the unassigned result); its one-line fix was found missing from
   `contrib/Isabelle2025-2/src/Pure/Concurrent/future.ML` (the directory
   is git-ignored; the file's mtime was 2026-01-18, so the 2026-09-08 patch
   had never reached this copy) and is applied on this machine [author
   2026-09-14 "请对本机打补丁"]: `future.ML:430-431`, the `Exn.Exn` arm
   reraises.  Pure changed, so every heap is outdated until rebuilt.  The
   seven other legs (C1, C2, E, B, F1, F2, G) did not hit it.
2. The AoA gate is open under Isa-REPL — by design [author 2026-09-14 "AoA
   应该在 Isa-REPL 下工作的, 这是 expected"]: `Dialogue.frontend_identity ()`
   answers `SOME true` for the REPL server, so the Phi_Examples leg
   escalated three obligations not in their stores to the Codex API and
   was stopped only by the local proxy being down.  The drafter had filed
   this as a finding against a clause of §10 step 5 that was its own
   assumption (corrected there).  A corpus load under Isa-REPL spends
   money on every obligation missing from its store; the
   `PhiTest_Arithmetic` corpus has none missing.

A verification leg on 2026-09-21 (after the review and after §39's
`97be6d75`), with the harness passing `-o ML_debugger=true` and `PLPR.thy`
untouched: the records written (the harness flag observed, not inferred);
377 decisions over 283 digests, 171 of 171 non-proved hits, no error; 0
flips on the 261 digests shared with the earlier cache-on leg, 22 digests
new with §39's restructuring of the call (their entries already in the
stores from that work's runs).  Details in the report.

Not measured (no probe): lemma replay cost and budget cut-offs (no judge
installed, every entry lemma-less: both zero); store I/O and the
forked-proof write, which exist only with the cache on and are therefore
bounded by the 200 s a cache-on load saves; the export hook's cost per
boundary, which is NOT bounded by that difference (the hook is installed
unconditionally and runs on the cache-off leg too).  Only the Phi_Examples
leg wrote guard entries (five: four into `Dynamic_Array`'s store, one into
`Quicksort`'s; eight tracked stores show as modified in the working tree,
named in the report — they were already modified by other work, and the
end-of-theory compaction rewrites a store even without a new entry); the
`PhiTest_Arithmetic` legs wrote none — every
decision took a non-writing path, and that corpus' store is byte-identical
to HEAD after them.  The Phi_Examples stores and exported C files were
already modified in the working tree by other work and are left
uncommitted.  The Quicksort obligation failure of the Phi_Examples leg is
undiagnosed (the report says what is known); the four failures of that leg
are reported, not attributed.

## 39. The Quicksort regression diagnosed (2026-09-15) — P-auto's second simplification; rulings, pending implementation

**Symptom** [author 2026-09-15 "你看一下 Phi_Examples/Quicksort.thy:47 被你
搞坏了"; "AoA 显示现在生成的 proof obligation 是 unprovable 的！而且如果只是 AoA
的问题的话 L49 是不会出错的，但现在 L46 L49 都出错了，一定是 PLPR 推理中的问题"]:
`Phi_Examples/Quicksort.thy` fails at the two recursive calls and the
closing bracket of the else branch (lines 46–49); the obligation the run
now produces is unprovable; and the store's AoA proof of the old one
(`Quicksort.qsort/2/8/10/2:0`, 59 KB, in the store since before the guard
cache) was tombstoned as "outdated" by a replay failure and compacted
away — a consequence, not the cause.

**Diagnosis** (Isabelle-MCP on `Phi_System_Base`, the theory from source;
the G leg's `guard_decision` records of §38; the code history):
1. After the `iterate` loop the memory is three slices (`l'a`, the pivot,
   `l'b`); merging them back into `[i, len]` at the `return` needs
   arithmetic guards on the slice bounds — `d ≤ len`, `d + (len - d) ≤
   len`, `d - Suc 0 ≤ len` among them.  They all come out `Unknown` ("Fail
   to prove or falsify …"), `d ≤ len` included although it is a premise
   verbatim.  With the merge rules unapplied the reasoning takes the branch
   that requires the slices empty, and the final obligation carries
   `list_all (λ_. False) …` conjuncts (the G leg's failure text, §38) —
   unprovable.
2. The guards' premises (about 25) hold five natural-number subtractions
   (`d - Suc 0`, `len - d`, `len - (d - Suc 0)`, `d - (d - Suc 0)`,
   `length l' - (d - Suc 0)`), and `Quicksort.thy:9` declares
   `linarith_split_limit = 20` (the default is 9; only `Quicksort.thy` and
   `Matrix_Oprs.thy:150` raise it): one `asm_full_simp` of them, linarith
   case-splitting every subtraction, costs hundreds of milliseconds to
   seconds — the arithmetic-guard cost §33 item 2 measured on
   `Phi_Types.thy`'s `len_intvl` guards.
3. P-auto (`p_auto_search_tac`) began with its own `asm_full_simp` +
   `quick_cut` — the same simplification the factory's "G.simpcut" pass
   had just completed — and on these guards that second pass alone
   exceeded the 400 ms, so the search never ran.  §33 item 2 had recorded
   exactly this ("P-auto then repeats the same work under its own 400 ms
   and fails"); the 2026-09-11 rulings fixed the pass's bound and left the
   repetition standing.  The G leg agrees: at these lines every `Unknown`
   decision took 410–1004 ms (the timer started after the pass: P-auto
   burnt its bound), every `Refuted` hit 14–55 ms (a search that exhausts
   quickly is not slow).  The author's jEdit showed no "probably loops"
   warning; the drafter first read the warnings it saw as an artefact of
   its own loaded machine (an orphaned 28 GB veriT of an earlier
   sledgehammer call, killed) — wrong: the measurement below shows the
   simplification of these states needs 7–13 s at load 3, so the 5 s
   bound is exceeded on this machine whatever the load, and the author's
   run must have hit it too (why no warning showed there is not known; a
   session on a heap holding the pre-2026-09-11 `reasoners.ML`, whose
   400 ms timeout was silent, would explain it).
4. History: from the 2024-05-15 original (`07db77d2`) until the race
   (`d49023f2`, 2026-08-24) the guard prover was ONE unbounded
   `asm_full_simp` + `quick_cut` pass and then 300 ms of
   `auto_search_tac`, whose opening is `safe_tac` — no second
   simplification [author 2026-09-15 "最早的时候只有 300ms!!"].  The
   2026-09-02 experiment `p_auto_search_tac` replaced that opening by
   `asm_full_simp` + `quick_cut` ("The only change from auto_search_tac is
   the OPENING"), which the race's 2000 ms hid; step 1's 400 ms
   (2026-09-09) exposed it.  400 ms itself is safe — §32: every proved
   guard's P-auto at most 204 ms of thread CPU over 341 decisions [author
   2026-09-15 "400ms 是很安全的啊"] — for the search, not for the search
   preceded by a second simplification.

**Retracted by the drafter along the way**: the reading "the simplifier
loops" (a load artefact, item 3); a TEMPORARY `\<phi>guard_classic_prover_timeout
= 20000` probe declared in `Quicksort.thy` — cancelled and reverted at
once: it multiplies the cost of every undecidable guard and made the
machine unusable [author 2026-09-15 "你这会导致整个系统几乎不可用！你理解我们为
什么要把超时设置成 400ms 吗？？？"]; the proposal to append the tombstoned AoA
record back and re-run as an experiment [author 2026-09-15 "否决！"]; and
the claim that the pass's simpset and P-auto's were "the same when the
delta is empty" [author 2026-09-15 "那就是不一样！你别想浑水摸鱼！！！严厉批
评！"] — they differ by design: P-auto's carries the entry's lemmas, the
pass's did not.  Also corrected: `p_auto_solving` did simplify — through
P-auto's opening, in the same simpset as the pass — so the out-of-run
instances simplified twice as well [author 2026-09-15 "但 p_auto_solving
实际上会做全量 simp 啊！"].

**Rulings (2026-09-15)**
1. P-auto no longer simplifies; the guard-side simplification is done
   once, before it, by `guard_simp_tac` [author "我们现在可以按你推荐的，取消
   P-auto 中的重复 simp"; the name: "赞同 guard_simp_tac"; why not
   "simpcut": "simpcut_tac 为什么要叫 simpcut_tac？这不就是标准的 simp 吗？"].
   Terms from now on: the guard-side simplification (`guard_simp_tac`), a
   step of the call, and P-auto (`p_auto_tac`), the search [the first
   wording here, "P-auto's simplification step", contradicted ruling 2 and
   was corrected at the review's D7].
2. `guard_simp_tac` runs on `enhance_for_guard` of the context that
   carries the entry's delta, `ctxt_g`, so it lives in the solving
   function, not in the factory; after the judge replaces the delta it
   runs again, on `ctxt_g'` [author "显然，simpcut 得用
   enhance_for_guard(guard_ctxt + delta) 但这样的话，注意 judge 是会修改 delta
   的，于是在修改后我们必须重新跑 simpcut 对吗？"].  Its output is shared by
   P-auto, R-conv, R-nitpick and the judge — it is a step of the call, not
   a part of P-auto [author "你考虑过别的 refuter 吗？R-conv, R-nitpick 吗？？"].
3. The factory stays a generation over `solve` and assumes no delta, no
   entry [author "现在的 gen_guard_condition_solver is a generation. The
   parameter `solve` can be anything. So `gen_guard_condition_solver`
   doesn't assume the presence of the delta, the entry records"]; it
   hands the solving function the unsimplified state.
4. The `is_F` shortcut is deleted [author "建议直接删除 is_F 分支"]; §1
   `gen_guard_condition_solver` says why nothing changes.
5. `p_auto_body` is renamed `p_auto_tac` [author "p_auto_body 这个名字很难
   听"; "批准 p_auto_tac"].
6. `solve_obligation_now` (`PLPR.thy:1983`) gets NO `guard_simp_tac`
   before its `fastforce` [author "你都用 fastforce 了为什么还要用
   guard_simp_tac？"]: `fast_force_tac` is `Classical.fast_tac o addss`,
   so its `asm_full_simp_tac` runs inside the search, on the whole goal,
   in the same simpset (the guard-side ctxt plus `Guard_Simp_SS`),
   so the pass the factory ran there was one more duplicate.  The drafter
   had recommended keeping it as "no behaviour change" — wrong in spirit:
   it would have kept a duplication; the one thing that ends is the entry
   lemmas' incidental presence in that instance's simplification, and the
   obligation instance was never a consumer of the lemma list.

**Measured after rulings 1–6 were implemented (2026-09-15, Isabelle-MCP on
`Phi_System_Base`, load ≈ 3; the smoke test clean, `Quicksort.thy` still
failing):** the three states on which `guard_simp_tac` timed out at line
47 were captured with a TEMPORARY probe (reverted) and simplified again
under a 120 s cap, one `asm_full_simp` in the enhanced context each:

| guard (26 premises each) | `linarith_split_limit` 20 (the theory's) | 9 (the default) | 0 |
|---|---|---|---|
| `d + (len - d) ≤ len` | 13.1 s, proved | 6.7 s, proved | 1.8 s, proved |
| `d - Suc 0 ≤ len` | 6.8 s, proved | 2.1 s, NOT proved | 0.8 s, NOT proved |
| `d ≤ len` | 12.0 s, proved | 6.3 s, proved | 1.7 s, proved |

(Elapsed times; the `Timing` CPU figures ran up to 2× elapsed, other PIDE
work included.)  So: the simplification of these states terminates and
PROVES the guards outright — the 5 s bound was simply below its cost;
pinning the split limit to the default is no remedy (6.5 s, and the
second guard then needs the search); `asm_simp` variants that do not
simplify the premises ran in milliseconds but are ruled out — "必须用
asm_full_simp，否则是错的！" [author 2026-09-15].  Until step 1 (2026-09-09)
this simplification was unbounded, so the old pipeline paid the 7–13 s per
guard silently.

7. **`guard_simp_tac`'s bound is 60 s of thread CPU** (from 5 s), still
   fixed in the code, no option [author 2026-09-15 "赞同"]: the bound exists
   to catch a looping simplifier, which any finite value catches; a bound
   below a terminating simplification's cost turns provable guards into
   `Unknown`, which is this regression; the cost of the larger value falls
   only on a guard whose simplification really loops, a bug in its own
   right.  The alternative of keeping 5 s and letting a theory raise it
   (an option, as `Quicksort.thy` raises `linarith_split_limit`) was
   listed and not taken (§1 `guard_simp_tac`, §10).
8. **Step 6 re-simplifies from the state the call was given**, not from
   step 1½'s result [author 2026-09-15 "MD1 step 6 从进入 prove_or_refute 时的
   原始状态重新化简"]: the review's one MUST_DISCUSS item — a rewrite made at
   step 1½ by a lemma of the old delta would otherwise survive the judge's
   deletion of that lemma and let P-auto write a `Proved` entry that a
   later call, simplifying the raw state under the new delta alone, need
   not reproduce (§5 step 6).  The judge is still handed step 1½'s state.
9. **`p_auto_attempt`** — the review's P1 [author 2026-09-15 "P1 赞同"]:
   one exported composition, `guard_simp_tac` then P-auto once under
   `\<phi>guard_classic_prover_timeout`, run by the out-of-run instance
   `p_auto_solving` and by the method `\<phi>guard_P_auto`, so the two
   cannot drift apart (§1 P-auto, §3).  The name is the drafter's.
10. **A refutation by the simplifier is a verdict** — the review's P2
   [author 2026-09-15 "P2 可以写 Refuted、出记录、entry 原是 Proved 时响亮报警"]:
   when `guard_simp_tac` at step 1½ rewrites the guard's conclusion to
   `False` (`quick_cut` leaves no state), the call writes `{delta,
   Refuted}`, emits the decision record with refuter `guard_simp_tac`, and
   prints the loud guard warning if the entry said `Proved`, naming the
   simplifier in place of the judge (§1 the loud guard warning; §5 step
   1½).  Until then that ending returned before every write, warning and
   record.  The refuter name in the record and the warning's wording are
   the drafter's.

**The review (2026-09-15, `wf_cdb1c300-357`: 8 interrogators, 57
findings; one fresh defender per finding [author "每个质疑只配一个 rebuttal
agent 就够了"], 35 survived; the judge): MET_ON_CONDITION** — rulings 1–7
implemented exactly, no reachable input with a wrong verdict or a crash,
the verification credible; one MUST_DISCUSS (ruling 8 above), twelve
DRAFTER_MAY_DECIDE items (all text: §7's five pre-2026-09-15 sentences,
§1's "the goal state" entry, three `reasoners.ML` comments and the
method's description string that over-generalised "every solving
function", the status line's quantifier, four dead anchors, ruling 1's
terminology sentence, the `is_F` justification's visible differences,
step 1½'s "nothing written", a probe for the judge path's third `error`
and the smoke test's header, `ai-artifacts/Guard_False_Probe.thy`'s
`p_auto_body`, ruling 6's description of `fast_force_tac`) — all applied
in this revision; 25 findings rejected with rebuttals (the report:
`ai-artifacts/QUICKSORT_REGRESSION_FIX_REVIEW_2026-09-15.md`).  Its two
proposals became rulings 9 and 10 above.

**The re-review (2026-09-15, `wf_3ac0ec80-955`: 4 interrogators, 25
findings, one defender each, 17 survived; the judge): MET_ON_CONDITION,
no MUST_DISCUSS** — rulings 8–10 implemented as ruled, D1–D12 applied;
nine DRAFTER_MAY_DECIDE conditions, all text or comments, no behaviour
change, all applied: §1's factory entry names `p_auto_attempt` and
`try_prove_or_give_up`'s one remaining caller; the `guard_simp_tac` entry
and §33's note count the two solving functions that call it; §1's
description of `fast_force_tac`; §1's P-auto entry and §5 step 4 carry
ruling 10; the `guard` entry's registration anchors and §5 step 1's
anchors; §39's verification block records its three runs; the
`guard_decision` signature comment lists `guard_simp_tac` among the
refuter values; the smoke test's header names its one exception and the
P2 probe's comment names the refuter; 8 findings rejected (the report:
`ai-artifacts/QUICKSORT_REGRESSION_FIX_REREVIEW_2026-09-15.md`).  **The
final round (`wf_b7d44a31-12e`: 2 interrogators, 14 findings, 10
survived; the judge): MET_ON_CONDITION** — seven text conditions, all
applied: this bookkeeping paragraph and the status line; the review
context document's verification labels and its summary's quantifier; §1's
"a `prove_or_refute` call", verdict and refuter entries qualified for
ruling 10; §5's remaining dead anchors; §3's caller list and the
provenance paragraph; three leftovers in §10's step list (the report:
`ai-artifacts/QUICKSORT_REGRESSION_FIX_FINAL_ROUND_2026-09-15.md`).

**The code plan** (`reasoners.ML` anchors of 2026-09-15):
- `:999` `p_auto_search_tac` and `:1070` `p_auto_body` → one function
  `p_auto_tac ctxt`: `enhance_for_guard` of the ctxt (with
  `Context_Position.set_visible false`), `main_tac i = CHANGED
  (nodup_depth_tac (addss ctxt) 10 i)`, `solved_states (norm_tac
  (REPEAT_DETERM (FIRSTGOAL main_tac) #> Seq.take 1))`; the 2026-09-02
  EXPERIMENT comment goes with the opening it describes.
- `:1565` `simpcut_tac` → top level as `guard_simp_tac`, next to
  `enhance_for_guard`, body unchanged.
- The factory `:1557`: `is_F`, `is_false`, `is_guard_mode` and the local
  `simpcut_tac` deleted; `solving d th = solve can_inst guard_ctxt d
  (ctxt0, th)`; the header comment shortened accordingly.
- `prove_or_refute :1401`: step 1½ after step 1 — `case Seq.pull
  (guard_simp_tac ctxt_g th) of NONE => Seq.empty | SOME (th, _) => …`,
  `goals` taken there; step 2 through `p_auto_tac`; step 6 runs
  `guard_simp_tac ctxt_g'` first, on the state the call was given (ruling
  8), `NONE` → the "judge is broken" `error`.
- `p_auto_solving :1615`: `p_auto_attempt ctxt th |> Seq.map (pair
  ctxt0)`, with `p_auto_attempt ctxt = guard_simp_tac ctxt THEN
  cpu_bounded_tac (guard_classic_prover_bound ctxt) (p_auto_tac ctxt)`
  defined after `p_auto_tac` (ruling 9).
- The signature `:113-114`: `guard_simp_tac` and `p_auto_tac` exported,
  `p_auto_body` gone.
- `PLPR.thy:1972` `\<phi>guard_P_auto`: `SIMPLE_METHOD (p_auto_attempt
  ctxt)` (ruling 9).
- `prove_or_refute`, ruling 10: step 1½'s `NONE` is `refuted_by
  simp_refuter` (the refuter name `"guard_simp_tac"`), `goals` are then
  the state's as given; steps 2–6 sit in a local `decide` on the
  simplified state; the loud guard warning takes the overturning party
  (`"the LLM judge"` / `"the simplifier"`); `Test/Guard_Decision_Smoke.thy`
  gains the probe "the simplifier refuting a Proved entry" and asserts the
  two loud lines apart.
- `PLPR.thy:1983` `solve_obligation_now`: unchanged in itself; it simply
  no longer receives the factory's pass (item 6 above).
- `Test/Guard_Decision_Smoke.thy` and every other reference to the old
  names follow; the plan's §1, §3, §5, §10 and this section carry the
  design (done in this revision).
- Stated consequences: `elapsed_ms` now includes the simplification; the
  `quick_cut` refutation at step 1½ is a verdict since ruling 10 (`Refuted`
  written, the record, the loud warning over a `Proved` entry) — before
  it, no verdict and no entry write of its own; a `\<condition> False`
  guard closed by simp now yields the trace line and, under `ML_debugger`,
  a decision record.

**Verification (2026-09-15, three runs)**: `Phi_System_Base` rebuilt on
the author's approval ("你可以自己 build 批准": its parent
`Semantic_Embedding` had been rebuilt by another session).  (i) Under
rulings 1–7: `PLPR.thy` clean under Isabelle-MCP, with only the three
pre-existing ML warnings; `Test/Guard_Decision_Smoke.thy` clean, every
probe as before; `Phi_Examples/Quicksort.thy` CLEAN, with the tombstoned
AoA record appended back from HEAD into `Quicksort.proof-store` ("你现在就
可以做") and `AoA_driver = "test"` declared TEMPORARILY (reverted): at the
`return` only the three genuinely unprovable guards are undecided, no
"probably loops" warning, the slice-merge obligation is back to its
provable shape, and the AoA record replays and stays live (222 live
records, no tombstone).  With the 5 s bound the same run had still failed
exactly as before the fix, which is what the measurement above settled.
(ii) After the review's conditions (ruling 8, D1–D12): the smoke test
clean with the probe of the judge's third error added.  (iii) After
rulings 9 and 10: the smoke test clean with the probe "the simplifier
refuting a Proved entry" added (its record: `verdict=refuted, hit=proved,
refuter=guard_simp_tac`, one loud line naming the simplifier);
`Quicksort.thy` re-run under this final code: CLEAN, the `return`'s
three undecided guards and the slice-merge obligation as in run (i), the
AoA record replaying and live; ruling 10 wrote seven `Refuted` entries
into `Quicksort.proof-store` (222 → 229 live records, no tombstone) —
guards the simplifier refutes outright, which until then left no trace.
