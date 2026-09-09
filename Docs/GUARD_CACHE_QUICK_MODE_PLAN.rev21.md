# PLPR Guard Cache — prove_or_refute rework

Status: rev 21 (2026-09-09).  The eighteenth review (rev 20: NOT_READY,
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
`.rev15.md`, `.rev16.md`, `.rev17.md`, `.rev18.md`, `.rev19.md` and
`.rev20.md` (archived beside this file); consult them for history, never
for the design.  §11–§24 record earlier rulings; §17 says which of
§11–§16 are superseded, §18 which of §17 (the `trace_ops` hook, the
`iNet` counter), §19 which of §11–§18 (the unbounded "G.simpcut" pass),
§20 which of §19 (nothing — it adds the preparatory phase), §21–§24 which
of §20 (nothing — drafter fixes only).  Every behavioral decision carries its provenance: [author
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
for `PLPR.thy`, `reasoner.ML` and the `Phi_System` callers, 2026-09-08
for `sledgehammer_solver.ML`, `raw_simplifier.ML`, `simpset.ML`,
`accounted_timeout.ML`, and 2026-09-08 evening for `cache_file.ML` — that
file changed under the plan during the day (commit `7615fe5` and
uncommitted edits: `proof_cache` became `times * string`), so every one of
its anchors was re-taken by symbol, and §10 step 0 says to do so again by
symbol, never by offset.  All are re-verified at implementation start
(§10.0).  No code has been written.

Submitted for a nineteenth review, scoped to §1, §3, §5, §7 and §10 —
the canonical form's type generalisation (now over-generalising) and the
propagation of §5 step 6's replacement are the changed places.

---

## 1. Glossary

Each entry gives the term, its meaning, and where the term comes from: the
author's own words, an existing name in the code, or a plain descriptive
phrase.  No other name is used for any of these concepts anywhere in this
document.

- **guard**: a premise of the `\<condition>` family (`Premise mode P`, mode
  `MODE_GUARD` or `NO_INST`; `is_guard_mode`, `reasoners.ML:1582-1584`),
  discharged inside a run by the reasoners registered at `PLPR.thy:1984`,
  `:1987`.  [code]
- **a `prove_or_refute` call**: one invocation of `prove_or_refute` run
  through its whole protocol (§5).  Its ML type becomes `bool ->
  Proof.context -> Hasher.digest -> context_state -> context_state Seq.seq`
  (`can_inst`, the guard-side ctxt, the guard digest computed by the
  factory, then the run's state: the run's ctxt `ctxt0` and the goal state)
  [author 2026-09-04 04:19 "我们要把 prove_or_refute 的类型改成 context_state
  -> context_state, 我们要改 context, 且要一路改下去一直到 gen_reason' 的返回"].
  The ctxt it returns is `ctxt0` with this guard's lemmas in the lemma list,
  and nothing else changed.  Its verdict is decided on the spot, by P-auto,
  on every call [author 2026-09-08 05:53 "一切裁决都是取决于 P-auto 的"].
  [descriptive]
- **the goal state**: the thm `prove_or_refute` receives — the PLPR sequent
  after `guard_condition_solver`'s `Goal.protect 1` (`head_only`,
  `reasoners.ML:385-388`): the guard's subgoals visible, the rest of the
  sequent wrapped in `Pure.prop` (`#(rest ⟹ C)`) as the conclusion; case
  split, the aux-fact insertion and the "G.simpcut" pass have already acted
  on it.  A **solved** goal state has no premises and is NOT
  `Goal.conclude`d — `head_only` concludes it afterwards [author 2026-09-04
  03:14].  [descriptive]
- **"G.simpcut"**: the last preprocessing pass before the solving function
  — `ALLGOALS (Simplifier.asm_full_simp_tac ctxt THEN_ALL_NEW quick_cut)`
  (`reasoners.ML:1605`; `quick_cut` `:941-944` fails a subgoal whose
  conclusion simplified to `False`), in the guard-side ctxt, with the
  lemmas enabled by its own `enhance_with_lemmas` call; the name is this
  plan's, inherited from the label of the `option_hunt` probe that used to
  wrap the pass and that commit `8c26c3b4` removed — the code no longer
  carries the string.  From now on the pass runs under a wall-clock bound
  of `\<phi>guard_classic_prover_timeout`, in all three factory instances
  (§3): the pass's sequence is pulled inside `Timeout.apply` of that
  bound, and on its `TIMEOUT` the pass yields the state it was given,
  unchanged, so the solving function runs on the unsimplified guard; a
  failure of the pass — `quick_cut` finding `False` — stays `Seq.empty`,
  as today [author 2026-09-08 12:51 "赞同" (the thirteenth review's first
  relaxation proposal); the timeout shape: drafter].  Not `timed_tac`
  (`:931`), whose timeout is an empty sequence and would read as that
  refutation by simplification.  Today the pass is unbounded (`:1603-1605`
  install no clock), which was the hole the lemma budget could not cover
  (§7).  [code]
- **`guard_condition_solver`**: from now on a FACTORY — the existing
  preprocessing template (`oblg_template`, the `is_F` shortcut, case split,
  `apply_tac`'s fact insertion, the "G.simpcut" pass) parameterised by the
  solving function it ends with, whose type is `prove_or_refute`'s
  [type: drafter].  Its pipeline (`reasoners.ML:1625-1635`), in order:
  `quick_cut`; under `head_only`: the configured pre-tactic `pre`; the
  case split of the leading subgoal (`case_split_by_annotations_leading_subgoal`,
  `:1628`); **the guard digest** (below), taken on the whole state at this
  point — the split subgoals, nothing inserted yet [author 2026-09-08
  11:52 "赞同. 批准"]; `Method.insert_tac ctxt aux` on every subgoal
  (`:1629`; `aux` is the hook fold's aux component, seeded with
  `aux_thms ctxt` by `apply_tac`, `:226`, and extended by the registered
  `Tactic_Configures` hooks — today `Phi_Envir.ML:336-338`, which prepends
  `IDE_CP_Core.\<phi>implication`); then
  `auto_tac`: "G.simpcut" and the solving function (`:1603-1608`).  The
  `HEADGOAL (case_split THEN_ALL_NEW insert)` of `:1627-1629` therefore
  becomes `HEADGOAL case_split THEN <the digest step> THEN ALLGOALS insert`,
  the same thing with one whole-state step between; the digest step is an
  optional parameter that only the `guard_condition_judge` instance passes
  [drafter].  The factory's contract, total [drafter, tenth review]:
  `oblg_template` (`reasoners.ML:336-380`) is SHARED — four live callers,
  `defer_obligation` `:819`, `hammer_obligation_solver` `:850`,
  `guard_condition_solver` `:1591`, `safe_obligation_solver` `:1650` — and
  becomes polymorphic in the solving function's result type `'a` through
  three extra parameters, `inj : thm -> 'a` (how a thm that never reached
  the solving function becomes a result), `on_thm : (thm -> thm) -> 'a ->
  'a` (how a thm-to-thm post-pass reaches the result) and `prj : 'a -> thm`
  (how a filter reads the thm out of a result); the three thm-returning
  callers pass `I`, `I` and `I`, the guard path passes `pair ctxt0`,
  `apsnd` and `snd`.  Every exit of the template that bypasses the solving
  function goes through `inj` — the `TrueI` exit `:344-345`, the two
  `fast_inst` exits `:346-347` and `:369-370`, `guard_condition_solver`'s
  own `is_F` arm `:1606-1607`, and `head_only`'s zero-premise arm `:386`
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
  the hook fold with an identity fallback to obtain the configured `(aux,
  pre, ctxt')` and calls the body on them OUTSIDE the hook; the hook's
  `state` type and its one registration outside PLPR
  (`Phi_System/library/system/Phi_Envir.ML:336-338`, which only adds aux
  theorems) are untouched.  The one behaviour that changes: a hook
  raising `Hooks.Success` with a tactic of its own used to REPLACE the
  body; now its state is used like the fold's result and the body runs.
  No registration does that today [drafter; §10].  Invariant: the state
  leaving a guard reasoner is `ctxt0` plus this guard's lemmas, and only
  the solving function may replace the ctxt.
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
  `can_inst`, take no digest, return the ctxt they were given, keep their
  thm-returning entry points, and never touch the store — the cache is
  `prove_or_refute`'s alone [author 2026-09-03 09:44; 11:11; 2026-09-08
  07:34 "不要. 我们现在只是给 prove_or_refute 做, 不是给 guard_condition_solver
  做"].
- **`try_prove_or_give_up`**: `Time.time option -> (Proof.context -> tactic)
  -> Proof.context -> thm -> thm Seq.seq` — run the tactic once, under the
  bound if given, keep only a solved state; otherwise `Seq.empty`.  Out of
  a run: `SOME \<phi>guard_classic_prover_timeout` over P-auto [author
  2026-09-03 09:44]; for obligations: `fastforce` in a
  `Guard_Simp_SS`-enhanced ctxt, no bound by default [author 2026-09-03
  11:15; 12:53].
- **lemma**, **tier**, **entry**, **verdict**: what the store holds for one
  guard —
  ```
  datatype tier = Only_Once | Rarely | Normal | Frequent   (* 3 / 30 / 300 / 1000 applications *)
  type lemma = term * Phi_Proof_Store.proof_cache * tier   (* statement, (replay times, method text), budget *)
  datatype verdict = Proved | Refuted | Unknown
  type entry = {lemmas : lemma list, verdict : verdict}
  ```
  `Phi_Proof_Store.proof_cache = Phi_Proof_Store.times * string` with
  `times = {thread_cpu : Time.time, wall : Time.time}` (`cache_file.ML:168`,
  `:176` in the signature; `:274`, `:285` in the body): two independent
  standard-machine measurements of the replay, thread CPU and wall, and
  the method text.  `Proved` = P-auto proved the guard
  with the lemmas; `Refuted` = a refuter found a countermodel, or the judge
  answered `Unprovable` — a reliable negative, silent on a hit; `Unknown` =
  nobody could decide — a hit warns again [author 2026-09-08 06:10 "3. 好
  的, 那么赞同 Proved of lemmas | Refuted | Unknown"; "4. 对"].  The tier is
  the judge's estimate of how often the lemma will be applied in one
  P-auto call; the numbers are constants of §10 [author 08:19 "我打算给
  judge 几个选项: Only_Once, 很少 (30 次以内), 一般 (300 以内), 频繁 (1000)";
  08:20 "Only_Once 给 3"].  A guard with NO entry that P-auto proves gets
  none written [author 06:27 "1. 不用写"]; a guard whose entry is
  `Refuted` or `Unknown` and that P-auto then proves gets `{lemmas,
  Proved}` (§5 step 3), so a `Proved` entry with an empty lemma list is
  reachable (§7).  `Refuted` is the constructor's name again; `Unprovable`
  names only the judge's answer [supersedes 2026-09-04 03:23].  `verdict`,
  `tier`, `lemma`, `entry` are declared in `guard_cache.ML` (§4);
  `judgement` in `reasoners.ML` beside the judge.
- **guard digest**: the `Hasher` digest (`Word64.word`) of the guard's own
  subgoals — `Thm.cprems_of` of the state the factory holds right after
  the case split and BEFORE the aux facts are inserted (`reasoners.ML`
  between `:1628` and `:1629`), each subgoal with its parameters and its
  own premises; not the ctxt's assumptions, not the aux facts, not the
  theory name [author 2026-09-03 07:48; 2026-09-08 06:10 "2. 不掺"; 07:05
  "digest 取在这道化简之前"; 11:52 "赞同. 批准" — before the insertion].
  Under `head_only`'s protection every visible premise at that point IS a
  guard subgoal, so the digest covers exactly the guard.  Computed by a new
  `Hasher.terms : term list -> digest` added to `HASHER` and
  `contrib/auto_sledgehammer/library/Hasher.ML` (the `hash_term`
  accumulator chained from the FNV basis over the list; `Hasher : HASHER`,
  `Hasher.ML:81`, hides the accumulator, so it cannot live in
  `guard_cache.ML`).  The key moves in three cases and no other: when the
  guard's text changes; when `oblg_template`'s normalisation of it does
  (`:341-342`, the ctxt's simpset on the tag); and, for a guard that still
  carries schematic variables when it reaches the factory, when those
  variables' names or INDICES do.  On the `\<condition> ?P` reasoner
  (`PLPR.thy:1984`, `can_inst = true`) the factory runs `oblg_template` at
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
  the `NO_INST` reasoner (`:1987`, `fix_level = 2`) does the import run
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
  recorded in §7.  Two guards with the same subgoals share one entry, in
  one run or across runs, builds and contexts: the entry is advice, not a
  decision, so sharing is right [author 06:10 "1. 同意"]; its cost is
  recorded in §7.
- **the store**: one table per theory, guard digest → entry, kept in
  `<thy>.guard-cache` through the proof store's functor instance
  `Phi_Guard_Store` (§8); read at the start of a `prove_or_refute` call,
  written at the points §5 names, never validated.  Key: `"PLPRGUARD" ^
  Hasher.compact digest` [author 2026-09-03 02:18; `compact` kept over
  `hex`: 2026-09-07 13:09 "我坚持用 compact"; `Hasher.compact`
  (`Hasher.ML:74`, `:113`) is the 8-byte big-endian rendering, not text,
  never printed].  Concurrent runs may write one entry; the store is
  last-write-wins, and two runs deciding the same guard write the same
  thing in the common case.  `\<phi>guard_cache` off = no entry is read
  and no entry is written; every call decides as if it had none [author
  2026-09-02 10:41; 2026-09-03 12:52].  The store's own `Theory.at_end`
  still loads and compacts an existing `<thy>.guard-cache`, since the
  switch gates nothing inside the store (§8).

The five protocol stages that follow — P-auto, R-conv, R-nitpick, the
judge, the two warnings — describe what one call does AFTER it has read
its entry and enabled the entry's lemmas (§5).

- **P-auto**: `p_auto_body ctxt = solved_states (p_auto_search_tac
  (enhance_with_lemmas (Guard_Simp_SS.enhance ctxt)))`, and P-auto =
  `timed_tac \<phi>guard_classic_prover_timeout o p_auto_body` — the one
  proof attempt EVERY call makes, hit or no hit, with the entry's lemmas
  enabled; its outcome IS the call's verdict [author 2026-09-02 07:11; 400
  ms provisional 08:49; on every call: 2026-09-08 05:36 "即便是对于 refuted
  也要跑 400ms 的 P-auto 以检查是否 refutation 依旧有效"; the steady-state
  cost of one P-auto budget per unprovable guard per run accepted without
  measurement: 06:10 "值的. 不需要测量. 相信我是值的"].  Exposed as the proof
  method **`\<phi>guard_P_auto`** [author 2026-09-03 11:11]; the body is
  named separately [drafter, eighth review].
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
  by either is what makes an entry `Refuted`.
- **the judge**: ONE optional function in a process-global ref,
  `judge : (judge_arg -> judgement) option Unsynchronized.ref`, default
  `NONE`, installed by ML code (phase 2: the LLM judge) [author 2026-09-04
  03:04].
  ```
  type judge_arg = {ctxt : Proof.context, outer_ctxt : Proof.context,
                    can_inst : bool, thm : thm}      (* thm = the goal state *)
  datatype judgement = Provable of lemma list | Unprovable
  ```
  [author 2026-09-04 03:11–03:14 (`thm` in); `Provable` reduced to lemmas:
  2026-09-08 06:14 "赞同" (no `proof`, no returned state — P-auto proves the
  guard with the lemmas, on the spot, so the recording run and every
  later run behave alike)].  `judge_arg.ctxt` is the guard-side ctxt with
  the entry's lemmas enabled (§5 step 1's `ctxt_g`), `outer_ctxt` is
  `ctxt0`.  The judge receives no list of the entry's lemmas as an
  argument — `judge_arg` has no lemmas field — and must ignore the ones
  it can read out of `judge_arg.ctxt`'s lemma list; its list REPLACES
  them: a bad lemma disappears by the judge not proposing it again
  [author 08:34 "LLM judge 那里, 是无视 the prove_or_refute point 上已有的的
  lemmas. 得到的 lemmas 是直接替换, 而不是继承已有的 lemmas, 以允许把坏的 lemmas
  移除掉"].  Its obligations, a contract with no run-time check beyond what
  §5 does anyway: each lemma is a closed statement of type `prop`
  (`Trueprop`-wrapped for a HOL proposition), certifiable by `Thm.cterm_of
  ctxt0` and provable by its own method text in ANY `ctxt0` that can
  reach this guard's digest — the digest excludes the ctxt by ruling
  [author 06:10 "2. 不掺"] and the entry is shared across contexts, so the
  method text may cite theory-level facts only, never a fact local to the
  recording call's context, and runs without `oblg_template`'s fixes, the
  inserted aux facts and the guard-side assumptions; the lemmas together
  must make P-auto prove the guard; its
  times are RAW measured times (`Phi_Proof_Store.times`, thread CPU and
  wall), which `prove_or_refute` normalises with
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
  re-entrant.  It may re-enter PLPR — nothing counts calls any more
  [supersedes 2026-09-07 13:21] — but a re-entered run inside the judge
  enables its own lemmas on top of `judge_arg.ctxt`'s (§1 the lemma
  budget: nesting is not handled) [author 2026-09-08 11:44 "你不用担心嵌套的
  问题. 你可以 leave a comment"].  An exception escaping the judge or a
  refuter propagates through `prove_or_refute` like any other exception of
  the run [author 2026-09-03 12:31 "hook 的崩溃应该视作 PLPR 推理链的崩溃"].
- **`Guard_Simp_SS`**, attribute **`\<phi>guard_simp`**: the simpset of
  USER-declared rules that strengthen guard proving — an instance of the
  repository's `Simpset` functor (`library/tools/simpset.ML`) [author
  2026-09-03 11:15].  Applied by an `enhance` inside each consumer and
  nowhere else [author 2026-09-03 13:26–13:27]: the "G.simpcut" pass,
  `p_auto_body` (so `\<phi>guard_P_auto`), R-conv, the obligation
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
  step 1's append (and step 6's replacement) inside a call, and by the
  guard-cache export hook, which replaces the whole outer list at every
  run and block boundary; read by `enhance_with_lemmas` and by the hook
  itself.  It travels with the ctxt and
  is what the guard-cache export hook carries.  Its consumers are
  "G.simpcut", `p_auto_body` and R-conv — each through
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
  is `SSymb`, so a hook installed in PLPR is lost where phi-system proves
  guards, and installing it per call through a derived theory makes
  sibling theories whose certificates cannot be joined (`:663-669`); making
  every lemma itself a simproc works but is tried only after every rewrite
  rule (`:1130-1135`), loses ordered rewriting and the `mk_eq_True`
  fallback (`:975`, `:971-973`), is invisible to `Simplifier_Trace`, costs
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
  list grows by §5 step 1's append, shrinks where §5 step 6 replaces the
  whole list with the judge's (whichever entry put a statement there),
  and loses at a run or block boundary the theorems `export_aux_lemma`
  refuses; it never repeats a statement: §5 step 1's append stores every
  theorem in **the canonical form** — `Raw_Simplifier.norm_hhf_protect
  ctxt0`, then `Thm.generalize` of every type variable of the proposition
  that occurs in none of the theorem's hyps (`thm.ML:1807-1824`, index
  `Thm.maxidx_of th + 1`), then `Drule.zero_var_indexes`: hhf-normal,
  outer parameters generalised to schematic variables, every type
  variable not pinned by a hyp generalised to a schematic type variable,
  indices renumbered [drafter, §10] — and skips one whose canonical
  proposition is already in the list
  (`Thm.eq_thm_prop`; the entry already there keeps its budget), so a
  guard met twice contributes its lemmas once, `enhance_with_lemmas` gives
  each statement exactly one budget variable, and a lemma's allowance per
  consumer run is the tier of the entry that first put the statement into
  the list — a statement two entries propose at different tiers runs at
  the first one's budget.  The canonical form is what makes that check
  survive the boundary: `Proof_Context.export` is `map (Assumption.export_
  …) #> Variable.export inner outer` (`proof_context.ML:921-923`), and it
  transforms EVERY theorem it carries, with no precondition, in two ways
  — (i) `Assumption.export_` hhf-normalises and `Variable.gen_all`s on
  both sides (`assumption.ML:153-156` `norm_hhf_protect inner #>
  export_thm #> norm_hhf_protect outer`; `raw_simplifier.ML:1556-1561`,
  whose `gen_all` runs even when the rewriting is skipped;
  `variable.ML:510-514`, the index taken from the ctxt's `maxidx`), so a
  lemma stated with an outer `⋀` would otherwise come back as `f ?x.i ≡ g
  ?x.i`, `aconv`-distinct from its next replay `⋀x. f x ≡ g x`; and (ii)
  `Variable.export` generalises every type variable the outer ctxt has
  not declared and no still-fixed variable pins (`variable.ML:515-529`
  `gen_fixesT`; `:565-572`, the index again from the `maxidx`), so a
  lemma carrying such a type variable `'a` would come back as `L[?'a.i]`,
  distinct from its next replay `L['a]` — and, the hook overwriting with
  no equality check, the list would gain a further entry, a further
  `\<r>BUDGET` variable and a further copy of the same rewrite rule at
  EVERY boundary, without bound.  The canonical form is a fixed point of
  both: `norm_hhf_protect` on a hhf-normal theorem with no outer
  parameter is the identity (`is_norm_hhf` skips the rewriting,
  `gen_all` finds nothing); and the type generalisation OVER-generalises
  on purpose — it does not ask which ctxt declares a type variable,
  because declaration grows inward (`variable.ML:216-224`, every declarer
  only adds names; `is_declared` `:185`) and the boundary's
  `Variable.export` generalises what the OUTER ctxt does not declare
  (`:516-518` `declared_outer = is_declared outer`), a set no test
  against `ctxt0` can reproduce — so after the canonical form the
  proposition's only type variables are those occurring in a hyp, and a
  schematic type variable is untouched by any later `Thm.generalize`.  A
  hyp of a replayed lemma is an assumption of an enclosing frame, whose
  ctxt declares its type variables, so the boundary never generalises
  them either (it could not: `thm.ML:1823-1824` raises on a type variable
  free in a hyp) — the exported copy IS the next call's replay.  For
  `enhance_with_lemmas` the canonical form yields the rule set an
  Isar-proved lemma of the same statement would give: HOL's `mksimps`
  begins with the same `Variable.gen_all` (`simpdata.ML:118`) but never
  rewrites with `Drule.norm_hhf_eqs`, so for a statement that is not
  already hhf-normal (`A ⟹ (⋀x. B x)`) the canonical form yields the
  rules — one here, where the raw replay yields none — that Isar's own
  export (`assumption.ML:153-156`) would have produced.  A theorem's
  identity for that check, and for §5 step 6's replacement, is its
  canonical proposition NOW: `export_aux_lemma` drops a theorem that
  mentions a variable fixed inside (`context_export.ML:62-66`, a
  term-level `Free` test), but `Proof_Context.export` may still change a
  kept theorem's proposition in one case the canonical form does not
  absorb — a phi block frame turns a theorem whose hyps hold the block's
  `Premise` assumption into `C ⟹ th` (`Phi_Working_Mode.ML:226-232`) —
  and such a carried copy is a different, weaker rule with its own budget
  that can coexist with the plain `L` the next call replays.  The bound:
  the exported `C ⟹ L` is the identity at later boundaries only for the
  frames that export crossed (`block_export` discharges one frame's
  assumptions per export, `Phi_Working_Mode.ML:226-233`;
  `Proof_Context.export` crosses every frame between inner and outer at
  once, `assumption.ML:150-156`), and the plain `L` the next call
  re-appends after the overwrite can itself come back as `C₂ ⟹ L` at the
  next block whose `Premise` its hyps hold — so the list carries one
  weaker copy per such crossing beside the plain replay; in that case
  nothing is lost and nothing is double-counted.
- **the undecided-guard warning**: the message printed over a guard's
  subgoals when neither a proof nor a refutation was found and no judge is
  installed — today's text at `reasoners.ML:1408-1419`, factored into one
  function of the ctxt and the subgoals; printed, as today, through
  `Phi_Reasoner.warn_pretty … 1` (`reasoner.ML:337-340`), i.e. only where
  `\<phi>trace_reasoning >= 1` (the corpus sets it: `IDE_CP_App2.thy:256`).
  Printed when a call ends `Unknown`, on a first decision and on every
  `Unknown` hit alike [author 2026-09-08 05:53 "对于 reliable = false 的,
  我们直接 warning 不再跑 R-conv, R-nitpick"].  [descriptive]
- **the loud guard warning**: the message printed when a guard whose entry
  said `Proved` could not be proved by P-auto with the entry's lemmas AND
  the call finally ends `Refuted` or `Unknown` — whichever path ended it:
  a refuter, the judge's `Unprovable`, or nobody — printed through
  `warning` unconditionally, not trace-gated, carrying the results of
  R-conv, R-nitpick and the judge [author 07:45 "好"; 08:45 "这个报警仅仅是
  最后真的给出了 refuted/unknown 判决时才报, 如果 the judge 最后还是 proved 那么
  不会报错"].  [descriptive]
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
IN A RUN   (\<condition> ?P, \<condition>[NO_INST] ?P reasoners, PLPR.thy:1984/1987)
  gen_reason' (reasoner.ML:906) — UNCHANGED
    … reasoning …  (state = (ctxt, thm); the ctxt flows from call to call)
      guard_condition_judge = guard_condition_solver prove_or_refute
        the factory (reasoners.ML:1625-1635): quick_cut; under head_only: pre;
                     HEADGOAL case_split; digest d of Thm.cprems_of (the split guard,
                     nothing inserted); ALLGOALS (insert aux); then auto_tac:
                     "G.simpcut" (enhances internally: Guard_Simp_SS, then the lemmas)
                     under \<phi>guard_classic_prover_timeout — TIMEOUT = state unchanged; then
        prove_or_refute can_inst ctxt d (ctxt0, thm):
          0  entry := store lookup d                → NONE | SOME {lemmas, verdict}
          1  enable entry's lemmas: replay each in ctxt0 → thm; failed → drop it (store write), warn;
             lemma list of ctxt0 → ctxt1 (returned); of ctxt → ctxt_g (the provers' base);
             a statement already in the list is not appended again
          2  P-auto on ctxt_g   (p_auto_body enhances internally: fresh budgets)
          3  P-auto proved:
               NONE, or verdict = Proved         → return (ctxt1, solved); nothing written
               verdict = Refuted | Unknown       → store write {lemmas, Proved}, silent; return (ctxt1, solved)
          4  P-auto failed, by the entry:
               Refuted                           → Seq.empty, silent
               Unknown                           → judge installed → step 6; else the undecided-guard warning; Seq.empty
               NONE                              → R-conv refutes → write {[], Refuted}, silent
                                                   else R-nitpick refutes → write {[], Refuted}, silent
                                                   else judge installed → step 6
                                                   else the undecided-guard warning; write {[], Unknown}; Seq.empty
               Proved (lemmas did not suffice)   → R-conv refutes → write {lemmas, Refuted}; LOUD warning; Seq.empty
                                                   else R-nitpick refutes → likewise
                                                   else judge installed → step 6
                                                   else write {lemmas, Unknown}; LOUD warning; Seq.empty
          6  the judge, j {ctxt = ctxt_g, outer_ctxt = ctxt0, can_inst, thm}:
               Provable new  → replace: the list becomes exactly `new` (a failure → error);
                                P-auto again on ctxt_g' (fresh time budget, fresh lemma budgets);
                                proved → write {new, Proved}; return (ctxt1', solved)   (no warning)
                                failed → error "the judge is broken"
               Unprovable    → write {lemmas, Refuted}; if the entry said Proved → LOUD warning;
                                Seq.empty
    the run's resulting ctxt leaves gen_reason' with the thm (stateful PLPR);
    at the run boundary the guard-cache export hook carries the lemma list

OUT OF A RUN   (guard_condition_solver' / guard_condition_solver1: four
                command-level callers in Phi_System — local_value.ML:169,
                toplevel0.ML:387, generic_variable_access2.ML:182, :272;
                application.ML:137 is commented out — solving proof
                obligations, `Premise default P` / `Premise MODE_COLLECT P`)
  guard_condition_solver (fn _ => fn ctxt => fn _ => fn (ctxt0, th) =>
      try_prove_or_give_up (SOME \<phi>guard_classic_prover_timeout) p_auto_body ctxt th
      |> Seq.map (pair ctxt0)):
    same preprocessing (no digest step; "G.simpcut" under its bound, as in
    every instance), then P-auto once, no store; not proved → Seq.empty →
    the caller's error continuation.  A deliberate narrowing: today these
    sites also get a 35 ms auto_search_tac gate (reasoners.ML:1405) and a
    2000 ms P-auto budget (:1421, :1504); all four sites raise `error` on
    failure, so §10 step (5) surfaces any regression as a build failure.

OBLIGATIONS SOLVED ON THE SPOT   (defer_premise, PLPR.thy:1975/1976, when
                Phi_Reasoner_solve_obligation_and_no_defer is 1 or 2 — set
                by the user's prove_obligations_in_time (PLPR.thy:1999-2005)
                and internally by rule_generation.ML:443, the only internal
                setter left since SE_Trim_Empty.ML was deleted, commit 11499285)
  guard_condition_solver (fn _ => fn ctxt => fn _ => fn (ctxt0, th) =>
      try_prove_or_give_up NONE fastforce (Guard_Simp_SS.enhance ctxt) th
      |> Seq.map (pair ctxt0)):
    same preprocessing (no digest step; "G.simpcut" under its bound), then
    fastforce, unbounded by default, no store; not proved → Seq.empty →
    backtrack.  No warning.
```

Removed: the `Race.race` call, the three racer wrappers, the in-race
`protocol` var, `\<phi>guard_race_timeout`, the 35 ms gate, and every
asynchronous piece.  Reused: `Hasher`, the proof store (as a functor
instance, §8), `eval_prf_str`, `Simpset` (for `Guard_Simp_SS`),
`PLPR_Context_Export` (the hook), `Simplifier.make_simproc`,
`Raw_Simplifier.mksimps` and `addsimps` (the lemma budget), `Strhashtab` of
`Performant_Isabelle_ML`, the R-conv/R-nitpick bodies (screens verbatim),
`RPC_Pretty`'s raw term codec (functorised, §8).  `Phi_Reasoners.wrap`
stays at every registration except the two guard reasoners, which now
take the state directly (§1 `guard_condition_solver`) [2026-09-02 12:08
"registrations unchanged" superseded for these two by 2026-09-04 04:19].

Every caller of the old `guard_condition_solver` must migrate, and the
factory's changed type makes a missed one a compile error.  Known callers
(2026-09-07): `PLPR.thy:1984`, `:1987` → `guard_condition_judge` on the
state; `PLPR.thy:1975`, `:1976` (`defer_premise`) → the `fastforce`
instance [author 2026-09-03 11:15]; `Test/Guard_Race_Smoke.thy:79` →
migrated at §10 step (2).  `oblg_template`'s three new parameters (§1)
make its other three callers compile errors too: `defer_obligation`
`reasoners.ML:819`, `hammer_obligation_solver` `:850`,
`safe_obligation_solver` `:1650` each pass `I`, `I` and `I`; and
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
`\<phi>trace_reasoning`]: the types of §1 (`tier`, `lemma`, `verdict`,
`entry`), `Guard_Simp_SS` with its attribute, `Guard_Lemmas`,
`enhance_with_lemmas` with its simproc, the guard-cache export hook,
`\<phi>guard_cache`, `Phi_Guard_Store` and the entry codec.  `Guard_Budget`
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
  d, hash = NONE} (Phi_Proof_Store.zero_times, encode entry)`
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
  `:61-64`, `:110-113`) fires the hooks whether or not a lemma was
  enabled, and the hook then overwrites the outer list with the exported
  inner one, of the same length.
- **The lemma budget** lives in the ctxt `enhance_with_lemmas` returns
  and nowhere else: the weakened rules and the simproc with its table in
  that ctxt's simpset, the `\<r>BUDGET` variables among its fixes
  (`Variable.add_fixes`, `variable.ML:480`); no slot of this design and
  no theory data holds any of it.  That ctxt is handed to exactly one
  consumer run and discarded; `ctxt_g` itself, which the judge receives,
  and `ctxt1`, which the call returns, carry the lemma list and no budget.
  The call is made INSIDE each consumer and nowhere else — `p_auto_body`
  (§1 P-auto), the R-conv body (§6) and the "G.simpcut" pass (§1) each
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
ctxt (`reasoners.ML:1630`'s, carrying `Guess_Instantiate`'s looper and
solver), `d` the guard digest and `thm` the goal state.

0. **Lookup.**  If `\<phi>guard_cache` is false, `entry := NONE`; else
   `entry := decode (get_cached_proof thy (key d))`.
1. **Enable the entry's lemmas.**  For each `(stmt, (t, script), tier)` of
   the entry, in order: `Thm.cterm_of ctxt0 stmt` ("fails to certify" =
   `TYPE`, `TERM` or `THM` — the last from `Thm.trivial` on a non-`prop` —
   caught with one explicit `handle`, the interrupt family untouched);
   `Thm.trivial` of the cterm as the goal; `eval_prf_str` of `script` with
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
   a lemma 重放失败, 此时就已经移除并报警"; the gate: drafter].  The
   surviving theorems, each with
   `budget tier`, are appended to the lemma list of `ctxt0`, giving
   `ctxt1` — the ctxt the call returns — and of `ctxt`, giving `ctxt_g`,
   the ctxt every prover of this call starts from; each is stored in the
   canonical form (§1 the export hook: `norm_hhf_protect ctxt0`, then
   `Thm.generalize` of the type variables no hyp pins, then
   `Drule.zero_var_indexes`), and one whose canonical
   proposition is already in the list (`Thm.eq_thm_prop`) is not appended
   again and the entry already there keeps its budget, so the list holds
   at most one entry per statement.  (`ctxt_g`, not `ctxt1`, because the
   guard-side ctxt is where the verdict is earned: `p_auto_search_tac
   ctxt` (`reasoners.ML:1393-1394`) runs under
   `Guess_Instantiate.add_guess_inst_looper` (`:1604`) over
   `add_guess_inst_solver … addsimps Premise_def` (`:1630`), installed
   nowhere else since 2026-08-29 (`guess_instantiate.ML:305-311`)
   [drafter, tenth review].)
2. **P-auto** on `ctxt_g` — `p_auto_body` calls `enhance_with_lemmas`
   itself, so the budgets are fresh for this consumer run (§4) — under
   `\<phi>guard_classic_prover_timeout` (the
   `Int.max (1, …)` clamp of `reasoners.ML:1420-1421` stays: a bound below
   1 ms installs no timer, `Pure/Concurrent/timeout.ML:26, 33-34`);
   `elapsed` is not recorded — nothing stores P-auto's time any more.
3. **P-auto proved** (`solved`): `entry = NONE` or `verdict = Proved` →
   nothing written; `verdict = Refuted | Unknown` → write `{lemmas, Proved}`
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
     budgets) refutes → write `{[], Refuted}`, return `Seq.empty` silently; else
     R-nitpick refutes → likewise; else a judge is installed → step 6; else
     print the undecided-guard warning, write `{[], Unknown}`, return
     `Seq.empty`.
   - `Proved` — the lemmas did not suffice → R-conv; else R-nitpick; else
     a judge is installed → step 6 [author 06:10 "补充一点 … 如果 R-conv,
     R-nitpick 都失败了, 还要跑 LLM judge, 然后响亮报警"; "6. 要的"].  The
     loud guard warning belongs to the call's FINAL verdict: whenever a
     call that started from a `Proved` entry ends `Refuted` (a refuter
     here, or the judge's `Unprovable` in step 6) or `Unknown` (nobody, no
     judge), print it with the refuters' and the judge's results, write
     `{lemmas, Refuted | Unknown}` — the lemmas stay [author 06:16 "lemmas
     始终是不丢的"] — and return `Seq.empty`; when step 6 ends `Proved`, no
     warning [author 08:45].
5. **Writes** are those named above and in step 6, each the whole entry
   under `key d`.
6. **The judge**: `j {ctxt = ctxt_g, outer_ctxt = ctxt0, can_inst, thm}`.
   - `Provable new` → each lemma's times are normalised with
     `Phi_Proof_Store.standard_time` first (§1 the judge); then the
     lemmas present are REPLACED by `new`: the lemma list of `ctxt0` and
     of `ctxt` becomes EXACTLY the enabled `new` — every statement present
     at this point leaves, whichever entry put it there [author 08:34 "无
     视 the prove_or_refute point 上已有的的 lemmas … 直接替换", as §20 read
     it; a guard whose lemmas left is re-installed by its own entry at
     its next call's step 1] — each of `new` enabled as in step 1 (the
     replay floor and `replay_limits` on the normalised times, the
     canonical form) at the judge's own tier, so no statement of `new`
     can run at another entry's budget, but with a failure being an
     `error` naming the judge (§1); then P-auto again, on the rebuilt `ctxt_g'`, with a fresh
     time budget and — `p_auto_body` enhancing again — fresh lemma
     budgets.  Proved → write `{new, Proved}` with the normalised times as
     they are, return `Seq.single (ctxt1', solved)` — and no loud warning,
     whatever the entry said [author 08:45].  Failed → `error` "the judge
     is broken" [author 08:45].
   - `Unprovable` → write `{lemmas, Refuted}` (the lemmas stay); if the
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
| R-conv | today's `r_conv_racer` body: negate each subgoal, search with `auto_search_tac` in a `Guard_Simp_SS`- and lemma-enhanced ctxt (its own `enhance_with_lemmas`, fresh budgets), with both of its `can_inst` branches as today — the `can_inst = false` one exporting through `outer_ctxt` (`reasoners.ML:1106-1115`, `:1132-1163`) | `Timeout.apply \<phi>guard_classic_prover_timeout`; `TIMEOUT` → not refuted [author 2026-09-04 03:23] |
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
  guard is P-auto's own time, up to `\<phi>guard_classic_prover_timeout`,
  on every run; the store saves the refuters and the warning, not P-auto
  [author 2026-09-08 06:10 "值的"].
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
  silent promotion), and the loud guard warning fires on `Proved` entries
  by their verdict, not by their lemmas.  So a guard that was once
  undecided or refuted and then proved, and later fails P-auto again, runs
  the whole refuter chain, consults the judge and prints the loud warning.
  Two contexts sharing a digest with different provability flip such an
  entry back and forth — `Proved` under one, `Refuted`/`Unknown` under the
  other — and the loud warning fires on every flip; the digest excludes
  the aux facts and the ctxt's assumptions precisely so that entries are
  shared [author 06:10 "2. 不掺"; 11:52], and this is the price.
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
- **A carried lemma may come back weaker.**  A lemma that crosses a phi
  block boundary with the block's `Premise` assumption among its hyps
  returns as `C ⟹ L` (§1 the export hook) and stays in the list beside
  the plain `L` the next call replays: two rules, two budgets, the
  conditional one discharging `C` before it rewrites; one such copy per
  block crossing whose `Premise` the replay's hyps hold (§1 the export
  hook).  (The export's other transformation, type generalisation, is
  absorbed by the canonical form's over-generalisation and makes no
  copy.)
- **Lemmas replayed on every call.**  Each call of a guard with lemmas
  pays their replay (`eval_prf_str`, one per lemma) before P-auto; the
  export hook carries the theorems to later calls along the branch the
  search keeps (a call ending `Seq.empty` takes its `ctxt1` with it), and
  the same call site pays again in every run.
- **A lemma that reaches its budget is cut off, not removed**, so a bad
  lemma costs its budget of rewrites in every consumer run of every guard
  call downstream of the one that enabled it — the rest of the run, the
  following statements of the block, and the two degenerate factory
  instances through their shared "G.simpcut" pass — until any judge
  answers `Provable` at any guard, which replaces the whole list (§5 step
  6), or its own entry is replaced.  A
  growth rule (`g x = g (g
  x)`) that is cut off after `budget` applications leaves the term it
  grew; P-auto then works on that term and usually fails or runs to its
  timeout — this call ends as a P-auto failure.  A reflexive or
  oscillating pair leaves the term unchanged.  The budget sees applied
  rewrite rules only: a lemma that loops through a simproc, a congruence
  rule, or the classical reasoner is stopped by a wall clock — in
  `p_auto_body` and R-conv by `\<phi>guard_classic_prover_timeout` as
  today, and in "G.simpcut" by the same bound from now on [author
  2026-09-08 12:51], where today nothing bounds it.  A conditional lemma
  is charged after its own premises are proved (the budget premise is
  last, §1) — a failed own premise costs nothing; only a `check_conv`
  rejection after all premises are proved costs a unit without rewriting.
  Phase 1 has no producer of lemmas (§9): the exposure begins with §10
  step 2's injected entries and the phase-2 judge.
- **The budget's unit is one consumer run** (one P-auto, one "G.simpcut",
  one R-conv), while the 2026-09-08 measurement counted per top-level
  simplifier invocation; §10 step 3 confirms the tiers on that unit.
- **The digest is taken after the case split and before the aux-fact
  insertion**, so a guard "G.simpcut" solves outright reaches
  `prove_or_refute` as a zero-premise state, P-auto succeeds trivially,
  and nothing is written unless the shared entry already says `Refuted`
  or `Unknown`, which §5 step 3 then promotes to `Proved`.
- **Last-write-wins.**  Two runs deciding one guard at once may write
  different entries (one proved with lemmas, one refuted); the later write
  stands and the next call re-decides.
- **The obligation instance's `fastforce`** is unbounded by default
  [author 2026-09-03 12:53]; the template's "G.simpcut" pass, unbounded on
  every path today, is bounded on every path from now on (§1) — a
  behaviour change on every guard, inside PLPR, not only on the cache
  path [author 2026-09-08 12:51].
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

- **Store functor** [within §11.10's delegation; shape: seventh review U6].
  `cache_file.ML`'s store body becomes a functor over `{ext, migrates,
  marks_writes, describe, switch}`; `Phi_Proof_Store` is instantiated in
  `cache_file.ML` with `{ext = "proof-store", migrates = true, marks_writes
  = true, describe = ("Proof cache", "cached proofs"), switch = <the
  existing enable_proof_store binding>}` — unchanged name, signature and
  callers — and **`Phi_Guard_Store`** is instantiated in `guard_cache.ML`
  with `{ext = "guard-cache", migrates = false, marks_writes = false,
  describe = ("Guard cache", "cached guard advice"), switch =
  \<phi>guard_cache}` (`RPC_Pretty` is not visible from Auto_Sledgehammer,
  `Auto_Sledgehammer.thy:2`; it reaches PLPR via `PLPR_error_msg.thy:7` →
  `Minilang_AoA.thy:2`).  Every module-level piece of state
  (`append_locks`, `warned_dirs`, `openning_stores`, the `Theory.at_end`)
  is per instance; the guard instance is ascribed a narrower signature
  without the by-hash surface; the honest cost is one unused by-hash index
  compiled per instance.  `switch` is a functor argument only because
  `Attrib.setup_config_bool` (`cache_file.ML:270`) cannot declare one
  binding twice; it gates NOTHING inside the store (the only `Config.get`
  of a switch, `:952`, is in the by-hash surface) — the guard switch is
  enforced by `prove_or_refute` at its read and its writes (§4) [eighth
  review].  Per-kind behavior: `migrates = false` → no legacy
  `.proof-cache` fallback, an absent file is an empty table; `marks_writes
  = false` → no `written`/`proof_mark` collision alarm (an entry is
  legitimately rewritten); `describe` feeds `warn_not_writable` (`:510`,
  "Guard cache for theory … is not writable (…); cached guard advice will
  be read but not recorded." [author 2026-09-03 11:22, wording adjusted to
  the redesign]) and `report_cache_is_outdated` (`:829`).  In the shared
  `at_end` (`:892-905`) only the `compact_store` (`:642-652`) call is
  gated by `if File.is_file (store_path thy)` — before `compact_store`'s
  own `with_file_lock`, whose `Posix.FileSys.createf` (`:448`) creates the
  lock file before `compact_store`'s inner `File.is_file` test (`:649`)
  can run; the branch that waits for registered async tasks before
  compacting stays — otherwise every theory in the build gets a
  `<thy>.guard-cache.lock` plus a writability probe at its end; measured
  2026-09-03 as 85 `*.proof-store.lock` files against 38 `*.proof-store`
  files in `contrib/phi-system` [drafter, seventh review U14 / eighth and
  ninth reviews].  This gate is the second behaviour-changing change to
  code outside PLPR (§9).  The dead `bool` in `openning_stores`'s value
  triple (`:687-688`; constructed at `:706`, `:713`, `:730`, `:763`,
  `:821`, `:842`; destructured at `:685`, `:717`, `:728`, `:807`, `:842`,
  `:852` — every one of which discards it or threads it back unchanged,
  so it is never consumed) is dropped in the same pass.
- **Two entry points of `Phi_Guard_Store`**, no new ones [author
  2026-09-03 13:19]: read = `get_cached_proof thy key : proof_cache
  option` (`:767`), the entry being its string half; write =
  `update_cached_proof thy {id = key, hash = NONE}
  (Phi_Proof_Store.zero_times, value)` (`:797`; the times half unused).
  `invalidate_proof_cache` (`:834`) is not used: nothing is deleted.  The
  store's locking (`store_append_lock` `:495`, `with_file_lock` `:445`,
  lock order v → fcntl → `openning_stores`, `:506`, `:585`, `:749-750`)
  is inherited unchanged.
- Entries live in `<thy>.guard-cache`, GITIGNORED [author 2026-09-02
  13:01]: `*.guard-cache`, `*.guard-cache.lock`, `*.guard-cache.tmp*`
  (`write_state_new`, `:419`) in `contrib/phi-system/.gitignore` [author
  2026-09-03 14:57].
- **Entry value**: `{lemmas : (term * proof_cache * tier) list, verdict}`
  packed with the mlmsgpack packers through a `BytesIO` outstream and
  taken as a string (`encode_record`'s shape, `cache_file.ML:104-111`)
  [author 2026-09-03 05:42; the shape 2026-09-08 06:16, 08:20, 08:37].  A
  `proof_cache`'s `times` as `packPair (packInt, packInt)` of
  `Phi_Proof_Store.ms_of_times t` and back through `times_of_ms` (`:172-173`,
  `:279-281`) — the store's own one-slot convention, `(cpu_ms, wall_ms)`
  (`:326`, `:332`), and the order only those two functions spell out
  (`:167`); `tier` and `verdict` each as an int tag like `PUT`/`TOMB` [author
  2026-09-03 13:19]; a lemma's `term` through `RPC_Pretty.pack_raw_term`
  / `unpack_raw_term` (`Isabelle_RPC/Tools/pretty.ML:323-366`, the
  constructor-tagged structural codec) — which, after the preparatory
  phase (§10 step P), carries a runtime symbol as its identifier (tag 9,
  `Phi_Tool_Symbol.dest_symbol` on the way out, `mk_symbol` on the way
  in), honouring `SSymb.thy:19-21`'s invariant that a symbol's per-process
  numeral is never persisted, exactly as `Hasher.hash_term` does
  (`Hasher.ML:184-186`); the functor takes NO symbol parameter, since
  `Phi_Tool_Symbol` is then visible where the codec lives [author
  2026-09-08 15:12 "很好" to the drafter's withdrawal of that parameter] —
  made available on `BytesIO` by turning that codec into a functor over
  the `MessagePack` result signature (`mlmsgpack.sml:1`): that signature
  is named `MESSAGE_PACK` by
  extracting `mlmsgpack.sml:8-106` with `type instream` / `type outstream`
  of its own in place of the `S.`-qualified occurrences (`:11`, `:60`,
  `:62`, `:64`); the functor body gains, immediately after `end = struct`
  (`:106`), the two realizations `type instream = S.instream` and `type
  outstream = S.outstream`; and the functor's ascription at `:8` becomes
  `:> MESSAGE_PACK where type instream = S.instream and type outstream =
  S.outstream`, so `Pack.packer` / `Unpack.unpacker` stay transparent for
  the existing instantiations at `:1002-1004`, which are untouched; then
  instantiating the term-codec functor twice — the `MessagePackBinIO`
  instance keeps `RPC_Pretty`'s names, the `MessagePackBytesIO` instance
  is `RPC_Pretty_Bytes` [name: drafter] — all of it in the preparatory
  phase (§10 step P), because `mlmsgpack.sml` is loaded by
  `Performant_Isabelle_ML.thy:37`, the same root heap `ssymb.ML` moves
  into, and one rebuild of that heap is enough.  The functor stays in
  `Isabelle_RPC` for now and moves to `Performant_Isabelle_ML` after this
  plan [author 2026-09-03 13:19; 13:27; 14:19].  Kept over Pure's
  `Term_XML.Encode.term_raw` + YXML [author 2026-09-07 13:15 "否决. 那个性
  能很慢的"]; measured 2026-09-07 on `Phi_System_Base` (5000 theorem
  propositions; the 500 largest): msgpack encodes 1.6–2.3× faster and in
  half the bytes; its decode through today's `BinIO.StreamIO` lazy
  instream measured slower, which the `BytesIO` instance removes
  (`ai-artifacts/Term_Codec_Bench.thy`).  NO format version [author
  2026-09-03 03:02]: the decode is wrapped `\<^try>\<open>SOME (decode v)
  catch _ => NONE\<close>` — catch-ALL, because a truncated payload raises
  `Subscript` out of `BytesIO.inputN` (`mlmsgpack.sml:918-924`); `\<^try>`
  re-raises interrupts.  Any exception means "there is no entry".
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
the whole lemma path (lemmas in the entry, enabling, the budget, the
export, replacement by a judge) exercised by §10 step (2)'s injected
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
`Phi_Tool_Symbol`'s ML moves from the HOL half of `Performant_Isabelle_ML`
to its Pure half, `RPC_Pretty`'s raw-term codec becomes the functor of
§8 with the symbol clause, and Isa-Mini's copy of the codec becomes an
instance of it.  None of this changes any behaviour PLPR sees, and the
symbol clause alters no live protocol: `pack_raw_term`'s callers outside
`pretty.ML` are `Isa-REPL/library/REPL_serializer.ML:41-42`, a re-export
whose one consumer is `tasks/extraction/theorem-relevance/extraction.ML:244-245`
(a wire whose Python end stores the payload and hands it back to ML
unread), and `evaluation/MLML_Verify/verify_proof_app.ML:33`, `:36`
(likewise carried back unread); Isabelle_RPC's Python side decodes no raw
term; and on both wires a term holding a runtime symbol — which by
`SSymb.thy:19-21` must not cross a process as a numeral anyway — now
packs as its identifier or, if its numeral is unregistered in this
process, raises from `revert_symbol1` (`ssymb.ML:60-63`) instead of
silently shipping the numeral.  Phase 2 is the LLM judge: a function of `judge_arg -> judgement`
installed into the ref, answering `Provable` with lemmas and their tiers,
or `Unprovable` [author 2026-09-02 07:39; 2026-09-04 03:04; 2026-09-08
06:14, 08:19, 08:34], under the contract of §1; installing it needs no
file to be deleted — `Unknown` entries consult it, `Proved` entries that
stop proving reach it, `Refuted` entries never do.

## 10. Configuration, drafter decisions, implementation order

| option / constant | default |
|---|---|
| `\<phi>guard_classic_prover_timeout` | 400 ms, provisional — P-auto's and R-conv's budget [author 2026-09-04 03:23 "直接重命名为 \<phi>guard_classic_prover_timeout"], the "G.simpcut" pass's bound [author 2026-09-08 12:51], and the replay floor of §5 step 1 [author 2026-09-07 13:16] |
| `\<phi>guard_refute_timeout` | 2000 ms (Nitpick's parameter; R-nitpick's outer net is `\<phi>guard_refute_timeout + 5000 ms × length goals`, and each subgoal inside it is bounded by `\<phi>guard_refute_timeout + 5000 ms`) |
| `\<phi>guard_cache` | true |
| `\<phi>log_guard_race` → `\<phi>log_guard_decision` | false (renamed) |
| `\<phi>guard_lemma_apply_limit` | 1000 — the budget of `Frequent`, the ceiling of every tier [author 2026-09-08 07:44 "我们只给一个 1000 的上限"] |
| the tier budgets (ML constants) | `Only_Once` 3, `Rarely` 30, `Normal` 300, `Frequent` = the option [author 08:19, 08:20] |

Names approved [author 2026-09-03 04:58, 11:11, 11:15; 2026-09-04 03:23;
2026-09-08 07:45 "赞同" (the naming table), 07:48 (`Guard_Lemmas` in place
of a simpset), 10:53, 11:32 (`Guard_Budget`, `\<r>BUDGET`)]; ML identifiers not
named by the author are the drafter's under the 11:24 delegation (among
them the judge ref's name and module, `guard_cache.ML`,
`enhance_with_lemmas`).

Nothing is pending the author.

**Drafter decisions that change behavior**, each vetoable: the file
`guard_cache.ML` and what it holds (§4); the shape of the ctxt threading
through the factory — `oblg_template` polymorphic through `inj`, `on_thm`
and `prj`, bypass exits (the zero-premise arm of `head_only` among them)
paired with `ctxt0`, `head_only`'s `Goal.conclude` on the thm half,
`SOLVED'` through `prj`, and `apply_tac` running the body outside
`Tactic_Configures`'s hook fold, so a hook's `Success` no longer replaces
the body (§1); the digest step as an optional factory parameter, passed
by `guard_condition_judge` only (§1); the "G.simpcut" timeout yielding
the state unchanged (§1); the provers run from `ctxt_g`, the guard-side
ctxt plus the lemmas (§5 step 1); the lemma replay in `ctxt0` with
nothing enhanced (§5 step 1); the canonical form of the lemma list —
`norm_hhf_protect ctxt0`, `Thm.generalize` of the type variables no hyp
pins, `Drule.zero_var_indexes` — and the append skipping a statement already
present (§1, §5 step 1); the dropped-lemma warning's gate
(`warning`, unconditional — §5 step 1); `enhance_with_lemmas` extracting
rules with `mksimps` first, rotating the budget premise last, and adding
by `addsimps`, with fresh budgets per consumer run (§1); the one simproc
per `enhance_with_lemmas` and its `Strhashtab` (§1); the export hook's
priority and its overwrite (§1); the exact exceptions of "fails to
certify" and "fails to replay" (§5 step 1); U3 (the factory parameter's
type — §1); the sequential order of R-nitpick's subgoals inside its net
(§6); `zero_times` / `hash = NONE` in the entry write (§8); the catch-all
decode (§8); the `SSymb.thy` certification assertion over
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
digest, n_goals and the number of lemmas enabled — not how many reached
their budget: that count lives in the simprocs' closures and no channel
§4 permits carries it out), behind `\<phi>log_guard_decision`, written by
`prove_or_refute` [drafter].  `Hasher.hex` appears in exactly that line of
the permanent code.

Order:

P. **The preparatory phase** — done and accepted before step 0, and
   reviewed with this plan [author 2026-09-08 15:06 "我建议把这个设置为一个
   准备阶段先去做"; 15:12 "先把它写进 rev 17, 随第十五轮评审一起过一遍"]:
   (a) `Performant_Isabelle_ML/library/ssymb.ML` is loaded by
   `Performant_Isabelle_ML.thy` (the Pure session) instead of
   `HOL/SSymb.thy:98`; its nine antiquotation occurrences — the eight
   `\<^const_name>`s (`SSymb.A` … `SSymb.F` at `:26-27`, `SSymb.Z` built
   at `:28` and matched at `:36`) become the literal strings they resolve
   to (`"SSymb.Z"`, …), and `\<^typ>\<open>symbol\<close>` (`:25`) becomes `Type
   ("SSymb.symbol", [])`, the shape `ssymb_syntax.ML:12` already uses —
   since the file builds and inspects terms structurally and consults no
   theory; the process-global table (`:43-46`) is unchanged.  `decode`'s
   first clause (`:36`) stops repeating the name in a pattern (a
   val-bound name in an ML pattern would bind, not match) and tests `t
   aconv zero` instead, so every constant name occurs exactly once, in a
   constant the file builds.  `ssymb_syntax.ML` (`\<^term>\<open>0::nat\<close>`
   and HOL's numerals) stays in `SSymb.thy`.  The logical definitions
   (`typedef symbol`, `Z`, `A` … `F`, the three simp groups,
   `symbol_digit_eval`) stay in `SSymb.thy`, which gains, after them and
   before its `hide_const`, one ML assertion that certifies with
   `Thm.cterm_of` every constant `ssymb.ML` builds — `ssymb.ML` exports
   them as a list, `Phi_Tool_Symbol.constants` [name: drafter]: `zero`
   and the six digit constants over `symbolT --> symbolT` — so a renamed
   or retyped constant fails where it is defined, which with the names
   occurring only in those constants is the check the antiquotations used
   to give at ML compile time; state-free, unlike a probe through
   `mk_symbol`, which on a fresh table builds only `Z`.
   (b) The codec: the `MESSAGE_PACK` extraction from `mlmsgpack.sml` and
   the term-codec functor over it, both exactly as §8 specifies, with the
   runtime-symbol clause in the functor body: `dest_symbol` answers `SOME
   id` → tag 9 with `id`; tag 9 → `mk_symbol` — the clause
   `Isa-Mini/Agent/agent_packer.ML:62-93` already carries; the two
   instances `RPC_Pretty` (`MessagePackBinIO`, keeping today's names and
   the signature `pretty.ML:7-8`) and `RPC_Pretty_Bytes`
   (`MessagePackBytesIO`).  Isa-Mini's copy lives inside `functor
   MiniLang_Agent_Pack(S)` (`agent_packer.ML:23-31`, `structure MP =
   MessagePack(S)` at `:31`), instantiated at both `BinIO.StreamIO` and
   `BytesIO` (`:365-366`), so no monomorphic codec can replace it: the
   copy (`:42-93`) is deleted and the functor body applies the term-codec
   functor to its own `MP`, which matches `MESSAGE_PACK` by §8's `where
   type` ascription.  The third transcription,
   `Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML:30-73`,
   sits inside the block comment opened at `:29` and closed at `:74`: it
   compiles nothing and persists nothing, and `RPC_Pretty` is already in
   scope there (`Semantic_Embedding.thy:2` imports
   `Isabelle_RPC.Remote_Procedure_Calling`), so nothing is done to it.
   (c) Acceptance: `Isabelle_RPC_Test`; a round trip of a term through
   each instance; Isa-Mini's packer round trip as a no-regression check;
   and one new round trip of a term holding a symbol whose decoded
   `dest_symbol` is the original identifier.  Cost: `ssymb.ML` and
   `mlmsgpack.sml` are in the root `Performant_Isabelle_ML` heap, so every
   heap above it (Auto_Sledgehammer, Minilang, `Phi_System_Base`, …) is
   rebuilt once — on the author's explicit approval, as always.
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
   the codec wait for step 4); the factory: `guard_condition_solver`
   parameterised, the digest step between the case split and the
   insertion, the "G.simpcut" bound, `oblg_template` with `inj`, `on_thm`
   and `prj` and its three other callers, `apply_tac` reshaped around the
   `Tactic_Configures` fold with its two other callers;
   `try_prove_or_give_up`; `p_auto_body` and `\<phi>guard_P_auto`'s
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
   `PLPR.thy:1965` (`\<phi>log_guess_inst = true` on that line is another
   subsystem and stays), so `\<phi>log_guard_decision` keeps its default
   `false`; step 5's harness enables it itself.
3. The export hook end to end: a lemma enabled at one call reaching the
   next call and the next statement (the V2 smoke test of the stateful
   PLPR plan as the model); the budget measured on the corpus with
   test-injected lemmas at each tier to confirm the tier numbers on the
   budget's own unit (one consumer run), not only on the 2026-09-08
   per-invocation sample.
4. Persistence: the store functor and `Phi_Guard_Store`, the gitignore
   entries, the entry codec (over `RPC_Pretty_Bytes` from step P), the
   read at step 0 and the writes of §5 replacing the table of step 2.
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
   approved rebuilds of steps 1 and 4, and with AoA escalation disabled in
   the harness (the 2026-09-08 probe cost real money by copying a theory
   under a new name and defeating its proof store).

After this plan: move the raw-term codec functor to
`Performant_Isabelle_ML` [author 2026-09-03 14:19].

§11–§19 below are the rulings of the earlier designs.  §17 supersedes the
run-level rulings of §11–§16; §18 supersedes §17's `trace_ops`-hook counter
and its `iNet`; §19 supersedes the unbounded "G.simpcut" pass [author
2026-09-03 12:53, §7]; §20 adds the preparatory phase and supersedes
nothing; §21–§24 are drafter fixes only; the rest stand.

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
   意"]; **no ctxt assumptions in the digest** [06:10 "2. 不掺"]; **the
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
    08:45].
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
