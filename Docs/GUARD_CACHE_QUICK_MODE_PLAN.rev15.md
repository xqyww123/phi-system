# PLPR Guard Cache — prove_or_refute rework

Status: rev 15 (2026-09-08).  The twelfth review (rev 14: NOT_READY, two
blockers — the rewrite-counting hook could not survive theory merges, and
a lemma simpset built on Pure's `empty_ss` would drop every lemma — six
majors, nine one-sentence fixes) is folded in together with the author's
rulings of 2026-09-08 09:34–11:52 (§18): the lemma budget is now enforced
entirely inside the simpset — every lemma becomes a conditional rewrite
rule `Guard_Budget \<r>BUDGET<i> ⟹ P`, and one context-local simproc
discharges the premise while counting — so nothing global is touched and
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
`.rev9.md`, `.rev10.md`, `.rev11.md`, `.rev12.md`, `.rev13.md` and
`.rev14.md` (archived beside this file); consult them for history, never
for the design.  §11–§17 record earlier rulings; §17 says which of §11–§16
are superseded, §18 which of §17 (the `trace_ops` hook, the `iNet`
counter).  Every behavioral decision carries its provenance: [author
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
2026-09-04 for `reasoners.ML`, `mlmsgpack.sml` and `pretty.ML`, 2026-09-07
for `PLPR.thy`, `reasoner.ML` and the `Phi_System` callers, and 2026-09-08
for `cache_file.ML`, `sledgehammer_solver.ML`, `raw_simplifier.ML`,
`simpset.ML`, `accounted_timeout.ML`; all are re-verified at
implementation start (§10.0).  No code has been written.

Submitted for a thirteenth review, scoped to §1, §3, §4, §5, §6 and §8.

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
  (`reasoners.ML:1802-1803`; `quick_cut` `:941-944` fails a subgoal whose
  conclusion simplified to `False`), in the guard-side ctxt; the string is
  the label of the temporary `option_hunt` probe (`:1121`, "delete with
  the hunt") wrapping it.  [code]
- **`guard_condition_solver`**: from now on a FACTORY — the existing
  preprocessing template (`oblg_template`, the `is_F` shortcut, case split,
  `apply_tac`'s fact insertion, the "G.simpcut" pass) parameterised by the
  solving function it ends with, whose type is `prove_or_refute`'s
  [type: drafter].  Its pipeline (`reasoners.ML:1824-1834`), in order:
  `quick_cut`; under `head_only`: the configured pre-tactic `pre`; the
  case split of the leading subgoal (`case_split_by_annotations_leading_subgoal`,
  `:1827`); **the guard digest** (below), taken on the whole state at this
  point — the split subgoals, nothing inserted yet [author 2026-09-08
  11:52 "赞同. 批准"]; `Method.insert_tac ctxt aux` on every subgoal
  (`:1828`, `aux = aux_thms ctxt` from `apply_tac`, `:222-228`); then
  `auto_tac`: "G.simpcut" and the solving function (`:1802-1807`).  The
  `HEADGOAL (case_split THEN_ALL_NEW insert)` of `:1826-1828` therefore
  becomes `HEADGOAL case_split THEN <the digest step> THEN ALLGOALS insert`,
  the same thing with one whole-state step between; the digest step is an
  optional parameter that only the `guard_condition_judge` instance passes
  [drafter].  The factory's contract, total [drafter, tenth review]:
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
  Invariant: the state leaving a guard reasoner is `ctxt0` plus this
  guard's lemmas, and only the solving function may replace the ctxt.
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
  type lemma = term * Phi_Proof_Store.proof_cache * tier   (* statement, (replay time, method text), budget *)
  datatype verdict = Proved | Refuted | Unknown
  type entry = {lemmas : lemma list, verdict : verdict}
  ```
  `Phi_Proof_Store.proof_cache = Time.time * string` (`cache_file.ML:149`:
  standard-machine time, method text).  `Proved` = P-auto proved the guard
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
  between `:1827` and `:1828`), each subgoal with its parameters and its
  own premises; not the ctxt's assumptions, not the aux facts, not the
  theory name [author 2026-09-03 07:48; 2026-09-08 06:10 "2. 不掺"; 07:05
  "digest 取在这道化简之前"; 11:52 "赞同. 批准" — before the insertion].
  Under `head_only`'s protection every visible premise at that point IS a
  guard subgoal, so the digest covers exactly the guard.  Computed by a new
  `Hasher.terms : term list -> digest` added to `HASHER` and
  `contrib/auto_sledgehammer/library/Hasher.ML` (the `hash_term`
  accumulator chained from the FNV basis over the list; `Hasher : HASHER`,
  `Hasher.ML:81`, hides the accumulator, so it cannot live in
  `guard_cache.ML`).  The key therefore moves only when the guard's text
  changes or `oblg_template`'s normalisation of it does (`:341-342`, the
  ctxt's simpset on the tag) — not when a lemma is enabled, not when an
  upstream statement adds a useful fact.  Two guards with the same subgoals
  share one entry, in one run or across runs, builds and contexts: the
  entry is advice, not a decision, so sharing is right [author 06:10 "1. 同
  意"]; its cost is recorded in §7.
- **the store**: one table per theory, guard digest → entry, kept in
  `<thy>.guard-cache` through the proof store's functor instance
  `Phi_Guard_Store` (§8); read at the start of a `prove_or_refute` call,
  written at the points §5 names, never validated.  Key: `"PLPRGUARD" ^
  Hasher.compact digest` [author 2026-09-03 02:18; `compact` kept over
  `hex`: 2026-09-07 13:09 "我坚持用 compact"; `Hasher.compact`
  (`Hasher.ML:71-74`, `:111-118`) is the 8-byte big-endian rendering, not
  text, never printed].  Concurrent runs may write one entry; the store is
  last-write-wins, and two runs deciding the same guard write the same
  thing in the common case.  `\<phi>guard_cache` off = nothing read,
  nothing written [author 2026-09-02 10:41; 2026-09-03 12:52].

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
  (`reasoners.ML:1329-1360`, negate and search) under
  `\<phi>guard_classic_prover_timeout` in a `Guard_Simp_SS`-enhanced,
  lemma-enhanced ctxt [author 2026-09-04 03:23 "复用"]; R-nitpick = today's
  Nitpick screen and calls (`reasoners.ML:1656-1675`) under one
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
  `ctxt0`.  The judge is NOT told the entry's existing lemmas, and its list
  REPLACES them: a bad lemma disappears by the judge not proposing it again
  [author 08:34 "LLM judge 那里, 是无视 the prove_or_refute point 上已有的的
  lemmas. 得到的 lemmas 是直接替换, 而不是继承已有的 lemmas, 以允许把坏的 lemmas
  移除掉"].  Its obligations, a contract with no run-time check beyond what
  §5 does anyway: each lemma is a closed statement of type `prop`
  (`Trueprop`-wrapped for a HOL proposition), certifiable by `Thm.cterm_of
  ctxt0` and provable by its own method text in `ctxt0` — without
  `oblg_template`'s fixes, the inserted aux facts and the guard-side
  assumptions; the lemmas together must make P-auto prove the guard; its
  times are RAW elapsed times, which `prove_or_refute` normalises with
  `Phi_Proof_Store.standard_time` (`cache_file.ML:867`) once, at the write
  (§5 step 6).  A lemma that fails to certify or replay, or a `Provable`
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
  07:48 "只要 a Proof Data storing a list of thms 就够了"].  Written at one
  place, §5 step 1 (and step 6's replacement); read by
  `enhance_with_lemmas` and the export hook.  It travels with the ctxt and
  is what the guard-cache export hook carries.  Its consumers are
  "G.simpcut", `p_auto_body` and R-conv — each through
  `enhance_with_lemmas`, and nothing else.
- **`enhance_with_lemmas`**, **the lemma budget**: `enhance_with_lemmas :
  Proof.context -> Proof.context`, the ONE function through which a
  consumer gets the lemmas into its simplifier, and the whole mechanism
  that keeps a bad lemma from making the simplifier loop [author 07:08 "超
  过 1K 就不准再用这个 simplification rule 了"; 08:34 "就别移除了. 改为超过后就禁
  止使用此 rule"; the shape 2026-09-08 10:53–11:46].  Given a ctxt whose
  lemma list holds `(P_i, budget_i)`, `i = 0..k-1`, it: (1) declares `k`
  fresh fixed variables `\<r>BUDGET<i> :: ind` with `Variable.add_fixes`
  (the returned internal names, `\<r>BUDGET<i>__` in a proof-body ctxt, are
  the keys of everything below; `\<r>` is PLPR's own symbol, so no user
  variable collides; the pattern follows `Subgoal_Env.allocate_subgoal`'s
  `\<r>GOAL<n>`, `Subgoal_Env.ML:54`) [author 11:32 "赞同 \<r>BUDGET"];
  (2) weakens each lemma to a conditional rule `Guard_Budget \<r>BUDGET<i>
  ⟹ P_i` by `Thm.implies_intr` of the certified premise; (3) builds a
  `Strhashtab` (`Performant_Isabelle_ML`) from the internal name to the
  remaining budget, `budget_i` [author 11:46 "要不直接用 Strhashtab 吧"; the
  decimal `<i>` is not parsed, the name is only a key: 11:40 "赞同十进制"];
  (4) adds ONE simproc on the pattern `Guard_Budget ?v`
  (`Simplifier.make_simproc` + `Raw_Simplifier.add_proc`, context-local,
  no theory-level declaration) whose closure holds that table: on
  `Guard_Budget (Free (n, _))` it looks `n` up — found with a positive
  remainder → decrement and return `Guard_Budget n ≡ True` (from
  `Guard_Budget_def`); found at zero, or not found → `NONE`; (5) builds a
  simpset holding exactly the `k` weakened rules on `Raw_Simplifier.clear_simpset
  ctxt` — an empty rule net that KEEPS the ctxt's `mk_rews`
  (`raw_simplifier.ML:415-417`), so the rules are extracted by the same
  `mksimps` the consumer's simpset uses (Pure's bare `empty_ss` keeps only
  Pure equations, `:346-352`, and would drop every `Trueprop` lemma) — and
  `merge_ss`es it into the ctxt's simpset (never `addsimps` on the ambient
  simpset, which warns "Ignoring duplicate rewrite rule" for a lemma that
  duplicates an existing rule; `merge_ss` deduplicates silently)
  [drafter].  **`Guard_Budget :: ind ⇒ bool`** is `definition Guard_Budget
  x ≡ True` in `PLPR.thy`, declared to no simpset, and `hide_const (open)
  Guard_Budget` at the end of `PLPR.thy` [author 10:53 "那个前件得是
  Guard_Budget :: ind => bool … 最后要在 PLPR.thy 的末尾 hide_const (open)
  Guard_Budget"]: `ind` has no simp rules, numerals or arithmetic
  procedures, so the premise reaches the simproc unchanged.  What this
  buys, against the code: the simplifier proves a conditional rule's
  premise with its own prover before applying the rule
  (`raw_simplifier.ML:1070-1086`) — the prover simplifies `Guard_Budget
  \<r>BUDGET<i>__`, no rule matches, the simproc answers — so one unit of
  budget is spent exactly when the rewrite is applied; a lemma at zero
  simply stops matching for the rest of that consumer's run, nothing is
  removed and nothing is written, and the lemma is enabled again, with a
  fresh budget, by the next `enhance_with_lemmas`; every property of a
  rewrite rule is kept (`mksimps` splitting, orientation, ordered rewriting
  of permutative rules, the "Applying instance of rewrite rule" trace,
  `Simplifier_Trace`'s `trace_rrule`); nothing global exists — no
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
  enabled at one call reaches every later call of the run, the run's
  returned ctxt, and the following phi statements of the block — unless a
  block frame refuses it.  The list only ever grows along a chain, so a
  guard met twice contributes its lemmas twice; `enhance_with_lemmas`
  treats equal theorems as one rule (`merge_ss`) and gives each list entry
  its own budget variable.
- **the undecided-guard warning**: the message printed over a guard's
  subgoals when neither a proof nor a refutation was found and no judge is
  installed — today's text at `reasoners.ML:1605-1616`, factored into one
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
and rejected), `Simplifier_Trace` "displaced" (it is not).

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
        the factory (reasoners.ML:1824-1834): quick_cut; under head_only: pre;
                     HEADGOAL case_split; digest d of Thm.cprems_of (the split guard,
                     nothing inserted); ALLGOALS (insert aux); then auto_tac:
                     "G.simpcut" in enhance_with_lemmas (Guard_Simp_SS.enhance ctxt), then
        prove_or_refute can_inst ctxt d (ctxt0, thm):
          0  entry := store lookup d                → NONE | SOME {lemmas, verdict}
          1  enable entry's lemmas: replay each in ctxt0 → thm; failed → drop it (store write), warn;
             lemma list of ctxt0 → ctxt1 (returned); of ctxt → ctxt_g (the provers' base)
          2  P-auto on enhance_with_lemmas ctxt_g   (fresh budgets)
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
               Provable new  → replace: enable `new` in place of the entry's lemmas (a failure → error);
                                P-auto again on enhance_with_lemmas ctxt_g' (fresh budget);
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
    same preprocessing (no digest step), then P-auto once, no store; not
    proved → Seq.empty → the caller's error continuation.  A deliberate
    narrowing: today these sites also get a 35 ms auto_search_tac gate
    (reasoners.ML:1602) and a 2000 ms P-auto budget (:1618, :1701); all
    four sites raise `error` on failure, so §10 step (5) surfaces any
    regression as a build failure.

OBLIGATIONS SOLVED ON THE SPOT   (defer_premise, PLPR.thy:1975/1976, when
                Phi_Reasoner_solve_obligation_and_no_defer is 1 or 2 — set
                by the user's prove_obligations_in_time and internally by
                SE_Trim_Empty.ML:54, :114, rule_generation.ML:443)
  guard_condition_solver (fn _ => fn ctxt => fn _ => fn (ctxt0, th) =>
      try_prove_or_give_up NONE fastforce (Guard_Simp_SS.enhance ctxt) th
      |> Seq.map (pair ctxt0)):
    same preprocessing (no digest step), then fastforce, unbounded by
    default, no store; not proved → Seq.empty → backtrack.  No warning.
```

Removed: the `Race.race` call, the three racer wrappers, the in-race
`protocol` var, `\<phi>guard_race_timeout`, the 35 ms gate, and every
asynchronous piece.  Reused: `Hasher`, the proof store (as a functor
instance, §8), `eval_prf_str`, `Simpset` (for `Guard_Simp_SS`),
`PLPR_Context_Export` (the hook), `Simplifier.make_simproc` and
`Raw_Simplifier.clear_simpset` (the lemma budget), `Strhashtab` of
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
migrated at §10 step (2).  `oblg_template`'s two new parameters (§1) make
its other three callers compile errors too: `defer_obligation`
`reasoners.ML:819`, `hammer_obligation_solver` `:850`,
`safe_obligation_solver` `:1850` each pass `I` and `I`.

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
  d, hash = NONE} (Time.zeroTime, encode entry)` — the whole entry, last
  write wins; gated by the same reading of the switch.  There is no
  deletion and no tombstone: an entry is only ever overwritten [descriptive].
- **Concurrency**: parallel runs (forked proofs, Isa-REPL sessions on one
  theory) read and write the same file; the store's locking
  (`store_append_lock` `cache_file.ML:453`, `with_file_lock` `:403`, lock
  order v → fcntl → `openning_stores`, `:543`, `:705-707`) is inherited
  unchanged; two writers of one entry in the same instant produce the same
  content in the common case, and a lost update costs one re-decision.
  Nothing in a call holds mutable state beyond the budget tables of its
  own `enhance_with_lemmas` calls.
- **The lemma list** is `Proof_Data`; it is per ctxt and needs no locking.
  Its only writer is §5 step 1 (and step 6's replacement); its readers are
  `enhance_with_lemmas` and the export hook.  Putting a lemma into it
  makes the ctxt physically new, so `export_context`'s `pointer_eq`
  short-circuit (`context_export.ML:54`) no longer fires for that run and
  the export hooks run at its boundary; a run in which no call enabled a
  lemma returns its ctxt unchanged and the short-circuit stands.
- **The lemma budget** lives in the simpset of the ctxt
  `enhance_with_lemmas` returns — the weakened rules, the simproc with its
  table, the fixed `\<r>BUDGET` variables — and nowhere else: not in
  `Proof_Data`, not in theory data.  That ctxt is handed to exactly one
  consumer run and discarded; `ctxt_g` itself, which the judge receives,
  and `ctxt1`, which the call returns, carry the lemma list and no budget
  (a consumer that wants the lemmas calls `enhance_with_lemmas` on
  `ctxt_g` and gets fresh budgets).  Nothing global is installed and no
  theory is derived.
- **Nesting** is nothing special for the store: a nested `gen_reason'`
  inside a call (through the judge, or a reasoner that re-enters PLPR)
  makes its own `prove_or_refute` calls against the same store, and its
  lemma list is the ctxt's.  For the budget, nesting is not designed for
  (§1).

## 5. One `prove_or_refute` call

`prove_or_refute can_inst ctxt d (ctxt0, thm)`, with `ctxt` the guard-side
ctxt (`reasoners.ML:1829`'s, carrying `Guess_Instantiate`'s looper and
solver), `d` the guard digest and `thm` the goal state.

0. **Lookup.**  If `\<phi>guard_cache` is false, `entry := NONE`; else
   `entry := decode (get_cached_proof thy (key d))`.
1. **Enable the entry's lemmas.**  For each `(stmt, (t, script), tier)` of
   the entry, in order: `Thm.cterm_of ctxt0 stmt` ("fails to certify" =
   `TYPE`, `TERM` or `THM` — the last from `Thm.trivial` on a non-`prop` —
   caught with one explicit `handle`, the interrupt family untouched);
   `Thm.trivial` of the cterm as the goal; `eval_prf_str` of `script` with
   `n = 1` under `Phi_Proof_Store.replay_limits t` (`cache_file.ML:200`,
   `:887-890`: a thread-CPU budget of `1.5 t + 1 s` that `Thread_CPU.apply`
   re-scales, and a wall cap `2 t + 3 s`; overrunning either, or
   `Auto_Fail`, is "fails to replay"), in `ctxt0` exactly as `gen_reason'`
   holds it — with neither `Guard_Simp_SS` nor any lemma of this or an
   earlier entry enabled, so a lemma's replay never depends on the list's
   order [author 2026-09-03 13:27] — `eval_prf_str`'s `Goal.conclude` hands
   back the plain theorem.  A lemma that fails to certify or replay is
   DROPPED from the entry (store write) with a warning naming it — the
   theory changed under it [author 2026-09-08 06:16 "除非 a lemma 重放失败,
   此时就已经移除并报警"].  The surviving theorems, each with `budget
   tier`, are appended to the lemma list of `ctxt0`, giving `ctxt1` — the
   ctxt the call returns — and of `ctxt`, giving `ctxt_g`, the ctxt every
   prover of this call starts from.  (`ctxt_g`, not `ctxt1`, because the
   guard-side ctxt is where the verdict is earned: `p_auto_search_tac
   ctxt` (`reasoners.ML:1590-1591`) runs under
   `Guess_Instantiate.add_guess_inst_looper` (`:1801`) over
   `add_guess_inst_solver … addsimps Premise_def` (`:1829`), installed
   nowhere else since 2026-08-29 (`guess_instantiate.ML:305-311`)
   [drafter, tenth review].)
2. **P-auto** on `enhance_with_lemmas ctxt_g` — the budgets are fresh for
   this consumer run — under `\<phi>guard_classic_prover_timeout` (the
   `Int.max (1, …)` clamp of `reasoners.ML:1617-1618` stays: a bound below
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
   - `NONE` → R-conv (on `enhance_with_lemmas ctxt_g`, fresh budgets)
     refutes → write `{[], Refuted}`, return `Seq.empty` silently; else
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
   - `Provable new` → the entry's lemmas are REPLACED by `new`: the lemma
     list of `ctxt0` and of `ctxt` lose EVERY occurrence of this entry's
     lemma statements and gain `new`, each enabled as in step 1 but with a
     failure being an `error` naming the judge (§1); then P-auto again, on
     `enhance_with_lemmas` of the rebuilt `ctxt_g'`, with a fresh time
     budget and fresh lemma budgets.  Proved → normalise every lemma's
     time with `standard_time`, write `{new, Proved}`, return `Seq.single
     (ctxt1', solved)` — and no loud warning, whatever the entry said
     [author 08:45].  Failed → `error` "the judge is broken" [author 08:45].
   - `Unprovable` → write `{lemmas, Refuted}` (the lemmas stay); if the
     entry said `Proved`, print the loud guard warning (step 4); return
     `Seq.empty` — the judge decided [author 2026-09-04 03:04; 06:10 "4.
     对"].

Any non-interrupt exception escaping P-auto, a refuter, lemma enabling or
the judge propagates out of `prove_or_refute` unchanged and becomes the
run's own exception [author 2026-09-03 12:31; 2026-09-04 03:04]; the two
`error`s of step 6 are such exceptions.  An interrupt passes untouched on
every path: `Timeout.apply` in scope is `Performant_Isabelle_ML`'s shadow
(`accounted_timeout.ML:113-133`, `:138-144`), which releases a non-proper
exception unchanged except that a flagless cancellation arriving after a
bound has expired is reported as its `TIMEOUT` (`:37-39`) — then P-auto
merely "failed" and the call continues; and `eval_prf_str0`'s catch-all
re-raises an exception in which `Interrupt_Family.contains_interrupt`
finds an interrupt (the one-clause change of §9).  Two calls in one run
that meet the same guard share one entry (§1 guard digest) and each
decides it by P-auto [supersedes 2026-09-03 07:54].

## 6. The refuters and the judge

There is no registry and no priority.  Three plain functions, each
bounding itself, in a fixed order — R-conv, R-nitpick, the judge — all on
the run's thread:

| step | what | its own bound |
|---|---|---|
| R-conv | today's `r_conv_racer` body: negate each subgoal, search with `auto_search_tac` in a `Guard_Simp_SS`- and lemma-enhanced ctxt (its own `enhance_with_lemmas`, fresh budgets), with both of its `can_inst` branches as today — the `can_inst = false` one exporting through `outer_ctxt` (`reasoners.ML:1303-1312`, `:1329-1360`) | `Timeout.apply \<phi>guard_classic_prover_timeout`; `TIMEOUT` → not refuted [author 2026-09-04 03:23] |
| R-nitpick | today's screen and Nitpick calls (`reasoners.ML:1656-1675`), subgoals one after another, each Nitpick call with its 2000 ms parameter as today; a `genuine` or `quasi_genuine` answer refutes (`guard_refute.ML:280-281`); R-nitpick's own preprocessing simpset `Nitpick_Refute_SS`; no lemmas | one outer `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms × length goals`, and inside it one `Timeout.apply` of `\<phi>guard_refute_timeout + 5000 ms` per subgoal — a subgoal's `TIMEOUT` moves to the next, the outer `TIMEOUT` ends R-nitpick; either way → not refuted [author 2026-09-03 13:05; inner bound 2026-09-07 13:00; sequential: drafter] |
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
  start — R-nitpick's `quasi_genuine`, which `reasoners.ML:1494-1503`
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
- **Lemmas replayed on every call.**  Each call of a guard with lemmas
  pays their replay (`eval_prf_str`, one per lemma) before P-auto; the
  export hook carries the theorems to later calls of the run, but the same
  call site pays again in every run.
- **A lemma that reaches its budget is cut off, not removed**, so a bad
  lemma costs its budget of rewrites in every consumer run of every call
  of that guard until the judge replaces it.  A growth rule (`g x = g (g
  x)`) that is cut off after `budget` applications leaves the term it
  grew; P-auto then works on that term and usually fails or runs to its
  timeout — this call ends as a P-auto failure.  A reflexive or
  oscillating pair leaves the term unchanged.  The budget sees applied
  rewrite rules only: a lemma that loops through a simproc, a congruence
  rule, or the classical reasoner is stopped by the wall-clock timeout, as
  today.  A conditional lemma is charged only when its own premises are
  proved too — a failed attempt costs nothing.
- **The budget's unit is one consumer run** (one P-auto, one "G.simpcut",
  one R-conv), while the 2026-09-08 measurement counted per top-level
  simplifier invocation; §10 step 3 confirms the tiers on that unit.
- **The digest is taken after the case split and before the aux-fact
  insertion**, so a guard "G.simpcut" solves outright reaches
  `prove_or_refute` as a zero-premise state, P-auto succeeds trivially and
  no entry is written.
- **Last-write-wins.**  Two runs deciding one guard at once may write
  different entries (one proved with lemmas, one refuted); the later write
  stands and the next call re-decides.
- **The obligation instance's `fastforce`** is unbounded by default, as is
  the template's own "G.simpcut" pass on that path today [author
  2026-09-03 12:53].
- Deleting `Race.race` deletes its crash absorption: today an exception in
  P-auto or a refuter is that racer's `Crashed` exit; now it is the run's
  exception (two known instances: the undiagnosed `Option` exception;
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
  `Attrib.setup_config_bool` (`cache_file.ML:241`) cannot declare one
  binding twice; it gates NOTHING inside the store (the only `Config.get`
  of a switch, `:903`, is in the by-hash surface) — the guard switch is
  enforced by `prove_or_refute` at its read and its writes (§4) [eighth
  review].  Per-kind behavior: `migrates = false` → no legacy
  `.proof-cache` fallback, an absent file is an empty table; `marks_writes
  = false` → no `written`/`proof_mark` collision alarm (an entry is
  legitimately rewritten); `describe` feeds `warn_not_writable` (`:468`,
  "Guard cache for theory … is not writable (…); cached guard advice will
  be read but not recorded." [author 2026-09-03 11:22, wording adjusted to
  the redesign]) and `report_cache_is_outdated` (`:786`).  In the shared
  `at_end` (`:849-861`) only the `compact_store` (`:600`) call is gated by
  `if File.is_file (store_path thy)`; the branch that waits for registered
  async tasks before compacting stays — otherwise every theory in the
  build gets a `<thy>.guard-cache.lock` created by `with_file_lock`'s
  `Posix.FileSys.createf` (`:406-408`) plus a writability probe at its
  end; measured today as 85 `*.proof-store.lock` files against 38
  `*.proof-store` files in `contrib/phi-system` [drafter, seventh review
  U14 / eighth and ninth reviews].  This gate is the second
  behaviour-changing change to code outside PLPR (§9).  The dead `bool` in
  `openning_stores`'s value triple (`:644-645`; six writers, no readers) is
  dropped in the same pass.
- **Two entry points of `Phi_Guard_Store`**, no new ones [author
  2026-09-03 13:19]: read = `get_cached_proof thy key : proof_cache
  option` (`:724`), the entry being its string half; write =
  `update_cached_proof thy {id = key, hash = NONE} (Time.zeroTime, value)`
  (`:754`; the time half unused).  `invalidate_proof_cache` (`:791`) is not
  used: nothing is deleted.  The store's locking (`store_append_lock`
  `:453`, `with_file_lock` `:403`, lock order v → fcntl →
  `openning_stores`, `:543`, `:705-707`) is inherited unchanged.
- Entries live in `<thy>.guard-cache`, GITIGNORED [author 2026-09-02
  13:01]: `*.guard-cache`, `*.guard-cache.lock`, `*.guard-cache.tmp*`
  (`write_state_new`, `:377`) in `contrib/phi-system/.gitignore` [author
  2026-09-03 14:57].
- **Entry value**: `{lemmas : (term * proof_cache * tier) list, verdict}`
  packed with the mlmsgpack packers through a `BytesIO` outstream and
  taken as a string (`encode_record`'s shape, `cache_file.ML:94-99`)
  [author 2026-09-03 05:42; the shape 2026-09-08 06:16, 08:20, 08:37].  A
  `proof_cache`'s `Time.time` as `packInt (Time.toMilliseconds t)` /
  `Time.fromMilliseconds`, the store's own convention (`:291`, `:285`);
  `tier` and `verdict` each as an int tag like `PUT`/`TOMB` [author
  2026-09-03 13:19]; a lemma's `term` through `RPC_Pretty.pack_raw_term`
  / `unpack_raw_term` (`Isabelle_RPC/Tools/pretty.ML:323-366`, the
  constructor-tagged structural codec) made available on `BytesIO` by
  turning that codec into a functor over the `MessagePack` result
  signature (`mlmsgpack.sml:1`): that signature is named `MESSAGE_PACK` by
  extracting `mlmsgpack.sml:8-106` with `type instream` / `type outstream`
  of its own in place of the `S.`-qualified occurrences (`:11`, `:60`,
  `:62`, `:64`); the functor body gains, immediately after `end = struct`
  (`:106`), the two realizations `type instream = S.instream` and `type
  outstream = S.outstream`; and the functor's ascription at `:8` becomes
  `:> MESSAGE_PACK where type instream = S.instream and type outstream =
  S.outstream`, so `Pack.packer` / `Unpack.unpacker` stay transparent for
  the existing instantiations at `:1002-1004`, which are untouched; then
  instantiating the term-codec functor twice; the `MessagePackBinIO`
  instance keeps `RPC_Pretty`'s names.  The functor stays in `Isabelle_RPC`
  for now and moves to `Performant_Isabelle_ML` after this plan [author
  2026-09-03 13:19; 13:27; 14:19].  Kept over Pure's
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
  2026-09-02 10:41]; off = the store is neither read nor written, every
  call decides as if it had no entry [author 2026-09-03 12:52].

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
(`sledgehammer_solver.ML:632-634`), `| err => if
Interrupt_Family.contains_interrupt err then Exn.reraise err else <today's
body>`, so that a `Par_Exn` wrapping an interrupt is no longer relabelled
`Auto_Fail (Unknown …)`; every `eval_prf_str` caller (the proof store's
replay, AoA) thereby propagates such an interrupt instead of starting a
fresh search on it [author 2026-09-08 02:37 "我认为这挺好的, 为什么不采纳
呢?"]; (b) the `at_end` gate on `compact_store` (§8, drafter, vetoable in
§10), which also affects the existing proof-store instance.  The purely
additive changes outside PLPR are `Hasher.terms` (§1) and, at §10 step
(4), the store functor, the `MESSAGE_PACK` extraction and the term-codec
functor.  Phase 2 is the LLM judge: a function of `judge_arg -> judgement`
installed into the ref, answering `Provable` with lemmas and their tiers,
or `Unprovable` [author 2026-09-02 07:39; 2026-09-04 03:04; 2026-09-08
06:14, 08:19, 08:34], under the contract of §1; installing it needs no
file to be deleted — `Unknown` entries consult it, `Proved` entries that
stop proving reach it, `Refuted` entries never do.

## 10. Configuration, drafter decisions, implementation order

| option / constant | default |
|---|---|
| `\<phi>guard_classic_prover_timeout` | 400 ms, provisional — P-auto's and R-conv's budget [author 2026-09-04 03:23 "直接重命名为 \<phi>guard_classic_prover_timeout"] |
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
through the factory — `oblg_template` polymorphic through `inj` and
`on_thm`, bypass exits paired with `ctxt0`, `head_only` and `SOLVED'` on
the thm half (§1); the digest step as an optional factory parameter,
passed by `guard_condition_judge` only (§1); the provers run from
`ctxt_g`, the guard-side ctxt plus the lemmas (§5 step 1); the lemma
replay in `ctxt0` with nothing enhanced (§5 step 1); `enhance_with_lemmas`
building on `Raw_Simplifier.clear_simpset ctxt` and `merge_ss`, with fresh
budgets per consumer run (§1); the one simproc per `enhance_with_lemmas`
and its `Strhashtab` (§1); the export hook's priority and its overwrite
(§1); the exact exceptions of "fails to certify" and "fails to replay" (§5
step 1); U3 (the factory parameter's type — §1); the sequential order of
R-nitpick's subgoals inside its net (§6); `Time.zeroTime` / `hash = NONE`
in the entry write (§8); the catch-all decode (§8); the store functor's
argument list and the narrowed guard signature (§8); the `at_end` gate on
`compact_store` only (§8, §9); the `guard_decision` record's fields, and
that it is a permanent record rather than temporary measurement code
(below).

Instrumentation is temporary measurement code [author 2026-09-03 04:01].
One record is permanent: `guard_decision` (the verdict, the path taken —
hit kind, which refuter, judge asked — elapsed, `Hasher.hex` of the guard
digest, n_goals, the number of lemmas enabled and the number that reached
their budget), behind `\<phi>log_guard_decision`, written by
`prove_or_refute` [drafter].  `Hasher.hex` appears in exactly that line of
the permanent code.

Order:

0. Re-verify every line anchor individually — §1's and §3's included, the
   `Phi_System` caller list among them; the tracing gate.
1. `Hasher.terms : term list -> digest` in `HASHER` and
   `contrib/auto_sledgehammer/library/Hasher.ML`; the one clause in
   `eval_prf_str0` (§9); `Guard_Budget` in `PLPR.thy` and its `hide_const`;
   `library/guard_cache.ML` (the types, `Guard_Simp_SS` with its attribute,
   `Guard_Lemmas`, `enhance_with_lemmas` with the simproc and the budget
   table, the export hook, `\<phi>guard_cache` — the store instance and
   the codec wait for step 4); the factory: `guard_condition_solver`
   parameterised, the digest step between the case split and the
   insertion, `oblg_template` with `inj` and `on_thm` and its three other
   callers; `try_prove_or_give_up`; `p_auto_body` and `\<phi>guard_P_auto`'s
   `method_setup`; the `Guard_Simp_SS` and `enhance_with_lemmas` sites; the
   `Nitpick_Refute_SS` rename; `guard_condition_solver'`/`1` on P-auto; the
   `fastforce` instance for `defer_premise`; the two warnings as functions;
   the obsolete comment at `reasoners.ML:1415-1421` rewritten.
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
4. Persistence: the store functor and `Phi_Guard_Store`, the raw-term codec
   functor and its `BytesIO` instance, the gitignore entries, the entry
   codec, the read at step 0 and the writes of §5 replacing the table of
   step 2.  (The gate of rev 11–13 — proceed only if record keys repeat
   across runs — is deleted: the key is the guard's own digest and repeats
   by construction [author 2026-09-08 07:38 "赞同删掉"].)
5. Corpus acceptance: a cache-on and a cache-off leg, a concurrent Isa-REPL
   leg, a consecutive-run leg with a hit-rate floor; measure wall time,
   verdict flips per guard cache-on vs cache-off, first-decision latency,
   the path distribution (hit kinds, refuters, judge), lemma replay cost,
   budget cut-offs, hard failures attributable to guard-side exceptions,
   digest cost, store I/O, the forked-proof write, the guard-cache export
   hook's cost per run boundary; re-measure 400 ms.  Testing via Isa-REPL
   against `Phi_System_Base` sources — never `isabelle build`, and with
   AoA escalation disabled in the harness (the 2026-09-08 probe cost real
   money by copying a theory under a new name and defeating its proof
   store).

After this plan: move the raw-term codec functor to
`Performant_Isabelle_ML` [author 2026-09-03 14:19].

§11–§17 below are the rulings of the earlier designs.  §17 supersedes the
run-level rulings of §11–§16; §18 supersedes §17's `trace_ops`-hook counter
and its `iNet`; the rest stand.

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
