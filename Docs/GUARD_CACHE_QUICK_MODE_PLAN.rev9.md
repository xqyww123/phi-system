# PLPR Guard Cache — prove_or_refute rework

Status: rev 9 (2026-09-03).  Rev 8 went through a sixth adversarial review
(5 interrogators, 5 fresh defenders, 1 judge; all Opus 5) which ruled
NOT_READY with 23 upheld findings and 3 relaxation proposals.  Every item
was then put to the author on 2026-09-03; §12 records the rulings.  The
author's rulings changed the design in five places — the table went back
to the author's original index design, the env lost all its concurrency
machinery, the out-of-run entry points got their own solver, the
per-record tombstone reuses the proof store's existing function, and the
verdict/chain types were settled (P-auto as a named method, run lemmas
with proofs, no `evidence`) — and those changes dissolved seven of the
judge's findings outright.  This
document states the FINAL design only.  History (the five earlier reviews,
every rejected mechanism, the adjudication ledger) lives in
`GUARD_CACHE_QUICK_MODE_PLAN.rev7-full.md`; consult it for history, never
for the design.  Every behavioral decision carries its provenance in
brackets: [author YYYY-MM-DD HH:MM] is the author's own ruling (transcript
timestamp), [drafter] is a drafting decision the author may veto.

Predecessor: `GUARD_NITPICK_FALSIFY_PLAN.md` (the guard race this plan
dismantles).  Line anchors into `reasoners.ML` are as of 2026-09-02 and are
re-verified at implementation start (§10.0); §5's former anchor
`reasoners.ML:1116-1117` is already stale.  No code has been written.

Submitted for a seventh review, scoped by the sixth judge's own
recommendation to §4–§6 (the concurrency rewrite) plus the sections the
author's rulings rewrote (§1, §5, §7, §8).

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
  `bool -> Proof.context -> Proof.context -> thm -> thm Seq.seq`.  Always
  named by the function.  [descriptive]
- **`guard_condition_solver`**: from now on a FACTORY — the existing
  preprocessing template (`oblg_template`, the `is_F` shortcut, case split,
  `apply_tac`'s insertion of the template's own facts, simp) parameterised
  by the solving tactic it
  ends with.  Three instances exist (§3): **`guard_condition_judge`** =
  the factory applied to `prove_or_refute`, used by the in-run
  `\<condition>` reasoners; the existing **`guard_condition_solver'`** /
  **`guard_condition_solver1`** = the factory applied to
  `try_prove_or_give_up` over P-auto, used by the out-of-run callers; and
  the factory applied to `try_prove_or_give_up` over `fastforce` for
  `defer_premise`'s solve-now case.  [author 2026-09-03 09:44 "我们现在做的
  这些应该被命名为 guard_condition_judge … 把原有的 guard_condition_solver
  改成一个 factory 允许去选用不同的 prove_or_refute"; third instance 11:11
  "建议用 guard_condition_solver over a the fastforce tactic"; the factory
  keeps the old name]
- **`try_prove_or_give_up`**: `Time.time option -> (Proof.context -> tactic)
  -> Proof.context -> thm -> thm Seq.seq` — run the tactic once, under the
  bound if one is given, keep only a solved state; otherwise `Seq.empty`.
  No table, no judge, no chain.  Out of a run: `SOME \<phi>guard_prove_timeout`
  over P-auto [author 2026-09-03 09:44 "直接使用 P-auto 跑那个 400ms … 跑不
  出来就直接 Seq.empty"]; for obligations: `fastforce` in a ctxt enhanced by
  `Guard_Simp_SS`, bound optional, none by default [author 2026-09-03 11:15
  "赞同, 但限时是可选的, 也可以不限时"].
- **verdict**: the value stored for one guard —
  `Proved of proof | Refuted of {refuter : string}` with
  `type proof = Phi_Proof_Store.proof_cache` (= `Time.time * string`,
  `cache_file.ML:149`: standard-machine time, method text) [author
  2026-09-02 12:03 "provable 就记录证明和时间, refuted 就记录 refuted";
  `Proved of Phi_Proof_Store.proof_cache`: 2026-09-03 11:00].  The method
  text is what `eval_prf_str` replays; a guard proved by P-auto stores
  P-auto's own method name (below) and is short-circuited on replay.
  `Refuted {refuter}` names the hook that answered: `"R-conv"`,
  `"R-nitpick"`, or `"default"` [names author 2026-09-03 04:58].
  [author's word]
- **refutable**: the RUN-TIME answer of a `prove_or_refute` call, "treat
  this guard as not holding" — it returns `Seq.empty` and the engine
  backtracks.  Not a stored value; the table entry it earns is written when
  its judge settles.  The chain's answer `Refutable name` (§6) is the same
  answer with the hook's signature attached; the stored `Refuted {refuter}`
  is its record.  No evidence travels with it [author 2026-09-03 10:59
  "建议直接删掉 evidence"; R-nitpick's countermodel text stays in its
  Event_Log line as today].  [author 2026-09-02 08:54 "warn the
  user 然后返回 refutable"; the drafting's name "Guard_Fails" retired
  2026-09-03 07:35 "这根本不是 failure 是被判定为 unprovable"]
- **P-auto**: `timed_tac \<phi>guard_prove_timeout (solved_states
  p_auto_search_tac)` — the one proof attempt a `prove_or_refute` call
  makes, alone, with no gate before it [author 2026-09-02 07:11 "只进行
  300ms 超时的 P-auto (甚至连最初 30ms 的 auto_search_tac 都不进行)";
  budget configurable and 400 ms provisional: author 08:49; no gate
  reconfirmed 2026-09-03 05:20].  [author's word]
- **P-auto IS exposed as a named proof method** `\<phi>guard_P_auto` (one
  `method_setup` in `PLPR.thy`) [name: author 2026-09-03 11:11 "批准"], and
  its name is the method text a P-auto-proved guard stores [author
  2026-09-03 10:59 "我们可以直接走 string 类型然后用它的名字吗? 当然在
  evaluation 时候可以用此名字来短路" — supersedes 05:19, under its own
  rule "如果暴露了的话 … 应该用这个 tactic string 来表示"].  The method
  runs in a ctxt enhanced by `Guard_Simp_SS` (§9), so a replayed P-auto and
  a replayed script see the same simpset.
- **`Guard_Simp_SS`**, attribute **`\<phi>guard_simp`**: the simpset that
  strengthens P-auto (and the obligation instance's `fastforce`) — an
  instance of the repository's `Simpset` functor (`library/tools/simpset.ML`),
  like `Nitpick_Refute_SS`; theory-level declarations via the attribute, the
  run lemmas added per ctxt with `add_simps'`, consumed with `enhance`
  [author 2026-09-03 11:15 "赞同 Guard_Simp_SS, \<phi>guard_simp 命名"].
  Distinct from **`Nitpick_Refute_SS`** (today's `Guard_Refute_SS`,
  attribute `\<phi>guard_refute_simp`, renamed [author 2026-09-03 11:15 "把
  Guard_Refute_SS 重命名为 Nitpick_Refute_SS"]), which is R-nitpick's
  preprocessing simpset and unfolds definitions for model search.
- **There are no modes** [author 2026-09-02 07:39; 2026-09-03 05:48 "其实
  我们是不需要分 mode 了的"].  The one behavior: a guard P-auto cannot
  prove is answered refutable immediately and evidence is gathered
  asynchronously by a judge.  The no-cache re-run of R2/R3 is the same
  behavior with an empty table, not a mode.
- **the chain**: the refutation hooks, a priority-ordered `Handlers`
  registry (`Hook.ML:116`; smaller priority runs first) [author 2026-09-02
  08:54 "这个链…在框架上就直接使用带有优先级的 Hooks 机制实现"].  Its
  lowest-priority member is the **default refuter**, an ordinary hook that
  warns the user and answers `Refutable "default"` [author 2026-09-02
  08:54; reaffirmed 2026-09-03 04:42 "the default warner 真的就是一个普通人"].
- **judge**: one `Future` task per `prove_or_refute` call that answered
  refutable; its body runs the chain for that guard [author 2026-09-02
  09:13 / 09:29 "赞同 async judges 用 Future"].  Judges never write the
  table; the topmost `gen_reason'` invocation copies their answers in at
  the end of the run.
- **env**: the record (§4) holding one run's table, judges and
  bookkeeping.  It sits in a `Proof_Data` slot of type
  `env option Unsynchronized.ref option`: the outer `option` says whether
  this ctxt was ever given a cell, the cell's content says whether the run
  is still open (`SOME env`) or has ended (`NONE`) [author 2026-09-03 08:08
  / 08:11 "type T = env option Unsynchronized.ref option … 所谓关闭就是直接
  设置成 NONE"].  [author's word "环境"]
- **the run**: everything between one `gen_reason'` invocation installing
  an env and that same invocation finishing.  The invocation that installs
  the env is **the topmost `gen_reason'` invocation** — the one whose slot
  check found no open env [author 2026-09-02 15:45 "始终只保留最顶层的那
  一个"].  Nested `gen_reason'` invocations inside the run inherit the env.
  What the topmost invocation does when the run ends (§4) is called **the
  end-of-run steps**.  The run's thread is the only writer of the env's
  mutable fields.  [author's words "跑", "最顶层"]
- **run failure**: the topmost `gen_reason'` invocation returning `NONE`,
  OR ending with a non-interrupt exception (`Interrupt_Family.contains_interrupt`
  false; the test at `reasoners.ML:1625`) [author 2026-09-03 07:35 "把 R2
  的触发条件从'返回 NONE'扩成'返回 NONE 或以非中断异常结束' 赞同"].  A
  nested `\<r>BEGIN` reasoning whose nested run returns `NONE` raises an
  ERROR (`nested.ML:33`), and `gen_reason`'s step limit raises too
  (`reasoner.ML:794-799`); both reach the topmost invocation on the
  exception path.  Verdicts are answers, never successes or failures; a
  refutable answer does not make a run fail.
- **call index**: the position of a `prove_or_refute` call within its run,
  0, 1, 2, … in call order, taken from the env's counter [author
  2026-09-02 07:11 "key 是 guard_counter … 然后 guard_counter += 1";
  restored 2026-09-03 07:59 "好, 请回到我的 index 设计"].
- **guard digest**: the `Hasher` digest (`Word64.word`, `Hasher.ML:55`) of
  the guard's own subgoals — the visible subgoals of the thm
  `prove_or_refute` receives (`Thm.cprems_of th`, each subgoal's parameters
  and premises included), nothing else: not the proof context's assumptions,
  not the theory name [author 2026-09-03 07:48 "对我说的就是 guard 子目标
  自身的 premises. proof context 的假设不考虑 … 因为已经被 gen_reason' 考虑
  过了"].  A new `Hasher.terms : term list -> digest` (fold of the existing
  `hash_term`) computes it.  In memory it stays a `Word64` everywhere
  [author 2026-09-03 07:58 "建议始终用 Word64"].
- **table**, **slot**: the run's `(digest * verdict) Inttab.table` keyed by
  call index [author 2026-09-02 07:11 "Inttab … key 是 guard_counter";
  2026-09-03 02:18 "value 是 … 那个 Inttab, 从 index 到 hash, verdict 的映射"].
  Slot `i` holds what the `i`-th call of the previous run determined; the
  stored digest says which guard that was.  A **hit** is slot `i` present
  with the stored digest equal to this call's guard digest; anything else
  is a **miss**; a **replay** is re-running what a `Proved` slot recorded.
- **record**, **record key**: the one proof-store item holding a whole
  run's table (the author's "proof store 只有一个 entry").  Key:
  `"PLPRGUARD" ^ Hasher.compact (Hasher.hash_in_context ctxt (Thm.prop_of initial))`
  of the run's first pulled initial state — the whole initial sequent
  (all subgoals and conclusion), salted with the ctxt's assumptions and the
  theory short name by `hash_in_context'` (`Hasher.ML:213-222`) [author
  2026-09-03 02:18 "key 是 the whole sequent hash"; `Hasher.compact` and
  the prefix: 08:33, 08:44 "反对删除前缀! 采用 PLPRGUARD"].  `Hasher.compact`
  is the 8-byte raw rendering (`Hasher.ML:76`); it never appears in a log
  line.  Stability caveat: `hash_in_context` on `Thm.prop_of` is the
  formula `cache_file.ML:856-859` calls not invariant under fork/promise
  discharge; a moved record key costs a total miss for that run plus one
  extra record, never a wrong verdict.
- **final digest**: `Hasher.hash_in_context ctxt' (Thm.prop_of th')` of
  the run's resulting state [author 2026-09-02 07:11 "检查得到的 sequent
  的表达式, 若与缓存中记录的相同,则放行"].  Same stability caveat; a moved
  final digest costs one R3 no-cache re-run.  A run with no resulting state
  has no final digest and records nothing [author 2026-09-02 11:39].
- **tombstone**: the proof store's own per-key deletion (`TOMB`,
  `encode_tombstone`, `cache_file.ML:66`, `:93`), written by the existing
  `invalidate_proof_cache` (`:731-741`) with `warn = false` and the guard
  store kind [author 2026-09-03 08:45 asked "具体是如何打? 调用什么函数?";
  reuse: drafter].
- **no-cache re-run**: re-entering the reasoning body on the ORIGINAL
  `states` argument of the topmost invocation with an empty table (R2's
  `NONE` case, R3).  [author's word "重跑"]
- **run lemmas**: `(term * string) list` — (statement, method text) pairs
  that strengthen P-auto's simplifier for one run.  They live in the run's
  record and env; at installation each statement is proved by replaying
  its method text (`eval_prf_str` on the statement's initial goal) and the
  resulting thms are added to `Guard_Simp_SS` in the run's ctxt
  (`Guard_Simp_SS.add_simps'`), which P-auto's ctxt consumes.  Phase 1 has no producer (the list is always
  empty); phase 2's LLM judge produces them [author 2026-09-02 07:39 "提供
  一些 auxiliary lemmas 加入进一个专用于 prove_or_refute 的 … 额外化简集";
  2026-09-03 10:53 "the lemmas 是需要带证明的, 所以是 (statement, proof
  script) pairs … proof store 中(也可能是 env 中)要多一个字段记录 the
  lemmas, 然后在 gen_reason' 的启动阶段 evaluate the proof script 得到这些
  lemmas 并 add them into a specific simpset that will augment the P-auto
  ctxt"].
- **R1–R4**: the four rules of §7.

Retired names — never used below; to be read as follows wherever an older
document or transcript uses them: "owner" = the topmost `gen_reason'`
invocation; "scope" = the run; "determination" = a `prove_or_refute` call;
"the proving stage" = P-auto; "store key" / `cache_key` = record key /
`record_key`; "exit protocol" = the end-of-run steps; "defensive rule" /
"no-env case" = the out-of-run entry points (§3); "blob" = the record
value (§8); "async judge" = judge; "Guard_Fails" = refutable; "quick mode"
= (no modes); "aux" = the fields of `Provable` (§6); "evidence" =
(deleted); "`NONE` = P-auto" = `\<phi>guard_P_auto`; "Actually_Provable" =
`Provable`; "Chain_Ran" = `Chain_Answered`; "the auxiliary-lemma slot" =
`Guard_Simp_SS`; "Guard_Refute_SS" = `Nitpick_Refute_SS`.

## 2. Motivation

~88 % of the corpus's `prove_or_refute` calls end with the guard not
holding (median refuted 607 ms, undecided 2367 ms), and that answer is
behaviourally identical to assuming the guard false; refutation evidence
cannot be validated item by item.  So: answer refutable immediately,
gather evidence off the critical path (judges), record every verdict, and
validate end to end per run (§7).  Soundness is untouched: verdicts only
select which rules PLPR tries; a wrong refutable answer yields a different
but valid derivation, never a wrong theorem.

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
          i := next call index
          slot i, stored digest = this guard's digest?
            hit Proved (t, P-auto's name) → run P-auto directly (short-circuit)
                                      under the replay bound;
                                      not landed → delete slot i, refutable arm
            hit Proved (t, script)  → eval_prf_str replay under the replay bound;
                                      not landed → delete slot i, miss arm
            hit Refuted {refuter}   → refutable; silent unless refuter="default"
            miss                    → P-auto: proves → slot i := Proved (elapsed, P-auto's name)
                                               else   → spawn judge i, answer refutable
    end-of-run steps (topmost invocation only):
      close (cell := NONE) → run failed? [R2] → final digest = recorded? [R3]
        → (R2/R3: cancel the judges, tombstone, no-cache re-run)
        → otherwise join ALL judges → cancelled from outside? → copy judges'
          Refuted into their slots → persist if the table is non-empty

OUT OF A RUN   (guard_condition_solver' / guard_condition_solver1: four
                command-level callers in Phi_System, §12.9)
  guard_condition_solver (try_prove_or_give_up (SOME \<phi>guard_prove_timeout) P-auto):
    same preprocessing, then P-auto once; not proved → Seq.empty → the
    caller's error continuation, as today.  No table, no judge, no chain.

OBLIGATIONS SOLVED ON THE SPOT   (defer_premise, PLPR.thy:1974/1975, when
                Phi_Reasoner_solve_obligation_and_no_defer is 1 or 2)
  guard_condition_solver (try_prove_or_give_up NONE fastforce):
    same preprocessing, then fastforce in a Guard_Simp_SS-enhanced ctxt,
    unbounded by default; not proved → Seq.empty → backtrack.  No table,
    no judge, no chain, no warning.

judge (Future, one per refutable answer): the chain, ascending priority
    100      R-conv     (\<phi>guard_rconv_timeout, 300 ms)
    200      R-nitpick  (\<phi>guard_refute_timeout 2000 ms; hang net +5 s)
    1000     (reserved: LLM judge, phase 2)
    1000000  default    (warn; Refutable "default")
```

Removed: the `Race.race` call, the three racer wrappers, the in-race
`protocol` var, `\<phi>guard_race_timeout`, the 35 ms gate.  Reused:
`Hasher`, `Phi_Proof_Store` (its three entry points, §8), `eval_prf_str`,
`Phi_Reasoners.wrap` (registrations unchanged [author 2026-09-02]), the
`Handlers` functor, the R-conv/R-nitpick bodies (screens verbatim),
`checked_io`, `invalidate_proof_cache`.

Every caller of the old `guard_condition_solver` must migrate, and the
factory's changed type makes a missed one a compile error.  Known callers
(2026-09-03): `PLPR.thy:1983`, `:1986` → `guard_condition_judge`;
`PLPR.thy:1974`, `:1975` (`defer_premise`, the `\<premise>`/`\<obligation>`
reasoner under `Phi_Reasoner_solve_obligation_and_no_defer` = 1 or 2, set
by the user's `prove_obligations_in_time` and internally by
`SE_Trim_Empty.ML:54`, `:114`, `rule_generation.ML:443`) → the
`fastforce` instance [author 2026-09-03 11:15 "(b) 赞同"];
`Test/Guard_Race_Smoke.thy:79` → migrated at §10 step (2).

## 4. The env

```
type env =
  {record_key     : string,
   previous_final : digest option,            (* NONE: no record *)
   lemmas         : (term * string) list Unsynchronized.ref,   (* run lemmas, §1 *)
   counter        : int Unsynchronized.ref,
   entries        : (digest * verdict) Inttab.table Unsynchronized.ref,
   judges         : (int * digest * judge_outcome future) list Unsynchronized.ref,
   judge_group    : Future.group}
```

(`judges` keeps, per judge, the call index and the guard digest its slot
will carry, so the merge can fill the slot without recomputing anything.)

[author 2026-09-03 08:11 "你这里不要过度设计"; fields ruled 08:33–09:51:
`run_id`, `consumed`, `closed`, `probe_group` deleted; plain refs, no
`Synchronized`, no `Lazy`; `lemmas` added 10:53.]  The run's thread is the
only writer of the four refs; judges never touch them.

- **Installation**: `gen_reason'` reads the slot of the FIRST PULLED
  initial state's ctxt (that is where reasoners get their context,
  `reasoner.ML:813`; `gen_reason'`'s own ctxt parameter never reaches the
  states).  No cell, or a cell holding `NONE` → create the env, put it in a
  fresh cell, install the cell by a lazy `Seq.map (apfst install)` over the
  initial states; a cell holding `SOME env` → inherit.  ONLY `gen_reason'`
  installs [author 2026-09-02 15:45; 14:54 "我们根本不区分"].  At
  installation: `record_key` from the first pulled state; the record is
  read (§8) — `previous_final := SOME final`, `entries := its table`,
  `lemmas := its lemmas` — or, with no record or an undecodable one,
  `previous_final := NONE`, `entries := Inttab.empty`, `lemmas := []`;
  eagerly, no laziness [author 2026-09-03 05:38 "否决。别增加复杂度"].
  Each run lemma is then proved by replaying its method text on the
  statement's initial goal (`eval_prf_str`, `tolerant_time` of nothing
  recorded → `\<phi>guard_prove_timeout` [drafter: bound]); a lemma whose
  replay does not land is dropped for this run (P-auto merely lacks it);
  the thms go into `Guard_Simp_SS` of the ctxt P-auto will see
  (`Guard_Simp_SS.add_simps'`, §9) [author 2026-09-03 10:53].  `counter := 0`; `judge_group :=
  Future.new_group (SOME (Task_Queue.group_of_task task))` for the current
  worker task, or `Future.new_group NONE` off a worker thread
  (race.ML:204-210's shape, one level only [author 2026-09-03 09:50 asked
  why a parent; none is needed, §12.13]).
- **Nesting**: a nested `gen_reason'` (`\<r>Call`, `\<r>BEGIN`,
  `ToR_Entry_Point` via `internal_reason`) inherits: one table, one
  counter, one judge list.  It performs no end-of-run steps.  Its `NONE`
  is ordinary backtracking for `\<r>Call` and `ToR_Entry_Point`
  (`nested.ML:42-45`); `\<r>BEGIN` converts it to an ERROR (`nested.ML:33`)
  that reaches the topmost invocation as an exception (§1 run failure).
  [author 2026-09-02 15:45, 16:02]
- **End-of-run steps** (topmost invocation only), in order:
  1. `cell := NONE` — the run is closed for every ctxt derived from it
     [author 2026-09-03 08:08].
  2. Did the run fail?  `NONE` → R2 with re-run; non-interrupt exception →
     R2 without re-run; interrupt → the exception path.  All three go to
     step 5 with `discard = true`.
  3. Otherwise compute the final digest; `previous_final = SOME f` and
     `f <> final` → R3: `discard = true`.  (Compared BEFORE the join: the
     digest depends only on the resulting state, never on a judge.)
  4. Otherwise `discard = false`.
  5. If `discard`: `Future.cancel_group judge_group`, then
     `Future.join_results` under `Thread_Attributes.uninterruptible` (the
     cancelled judges exit promptly; their answers are not read) [author
     2026-09-03 09:48 "赞同, 可以直接取消"].  If not: `Future.join_results`
     on every judge, IN FULL, no bound of any kind [author 2026-09-03 01:56
     "必须老老实实等待所有 async judge work 结束"].
  6. `Task_Queue.is_canceled judge_group` after a non-discard join →
     something outside this run cancelled it (a user interrupt, an
     enclosing timeout: `is_canceled` walks the parent chain,
     `task_queue.ML:82-84`) and the judge that absorbed the interrupt has
     already re-raised it into the group (§6) — take the exception path.
  7. Not discarded and not cancelled: copy every judge's `Refuted` into its
     slot (§6 merge); if the table is non-empty, persist the record (§8)
     [author 2026-09-03 08:04 "A 赞同"].
  8. Then: R2 with re-run and R3 → tombstone the record, re-enter the
     reasoning body on the ORIGINAL `states` argument (never the mapped
     sequence, whose `install` closure captured the now-closed cell) with a
     fresh env whose `previous_final = NONE`, `entries = Inttab.empty` and
     `lemmas = []` (the tombstone's in-memory half has already removed the record, so
     even a re-read would find nothing), adopt its result.  R2 without
     re-run → tombstone, re-raise.  Exception path → re-raise (`Isabelle_Thread.raise_interrupt
     ()` in the cancelled-from-outside case), nothing written or deleted.

## 5. One `prove_or_refute` call

Inside a run only (the out-of-run entry points never reach here).

1. `i := !counter; counter := i + 1`.  `d := Hasher.terms (map Thm.term_of
   (Thm.cprems_of th))`, the guard digest, computed on the thm as received.
2. Look up slot `i`: a hit is `SOME (d', v)` with `d' = d`; otherwise miss.
3. **Hit `Proved (t, script)` with `script` = P-auto's method name**
   (short-circuit, no `Method.parser`): run P-auto once, bounded by
   `Time.max (tolerant_time t) \<phi>guard_prove_timeout` where
   `tolerant_time t = 1.5t + 1 s` (`cache_file.ML:832-834`) [floor: author
   2026-09-02; the summand and reusing `tolerant_time`: author 2026-09-03
   02:10 "直接定死为 1s"].  Landed → return the solved states (`t` not
   refreshed [drafter]).  Not landed → delete slot `i` and take the
   refutable arm of step 6 directly, judge spawn included (this replay was
   itself the one search) [author 2026-09-02 10:29 "统一成全部走重放";
   CLOSED 2026-09-03 05:21 — not to be re-asked].
4. **Hit `Proved (t, script)` with any other `script`**: replay via
   `eval_prf_str` under `tolerant_time t`, `n = Thm.nprems_of th`, keywords
   `Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)`; the returned
   ctxt' is discarded.  Not landed → delete slot `i` and fall to the miss
   arm [author 2026-09-02 10:29].  Phase 1 has no producer of such
   scripts.
5. **Hit `Refuted {refuter}`**: answer refutable.  Silent when the refuter
   is R-conv or R-nitpick (today's silent refutation, `reasoners.ML:1526`); when
   `refuter = "default"`, print the default's warning again (today's
   per-run warning).  Never re-judged [author 2026-09-02 10:40 "C 一定不能
   判, 一定要如实遵守缓存"].
6. **Miss**: run P-auto.  Proves → `entries := Inttab.update (i, (d, Proved
   (elapsed of the whole timed_tac call through standard_time, P-auto's
   method name)))` [drafter: whole-call elapsed].  Does not prove → fork judge `i` with
   `judge_arg` (§6), `judges := (i, d, future) :: !judges`, answer refutable.
   The topmost invocation writes the judge's `Refuted {refuter}` into slot
   `i` at the end of the run.

Two calls in one run that meet the same guard occupy two slots and get two
judges: the slot, not the guard, is the identity, so two contexts may
legitimately give two answers [author 2026-09-03 07:54 "这些都是最初为什么
我要用 index 来做索引而不直接用 digest 做索引的原因"].

## 6. Hooks and judges

**Registration.**  The single route is

```
add_refuter : priority -> {name : string, bound : Proof.context -> Time.time}
            -> (judge_arg -> chain_verdict option) -> Context.generic -> Context.generic
judge_arg     = {ctxt, outer_ctxt : Proof.context, can_inst : bool, goals : cterm list}
chain_verdict = Provable of {lemmas : (term * string) list, proof : proof}
              | Refutable of string
```

[author 2026-09-03 10:59 (fields inlined, `evidence` deleted), 11:01
"Actually_Provable of {lemmas : (term * string) list, proof: proof} 可以直接
让 judge 来给时间"; the constructor's name shortened to `Provable` under
the 11:24 naming delegation.]  `Provable` is a VERIFIED answer: the hook
has replayed `proof`'s method text on the guard (with `lemmas` in the
simpset) on the judge's thread and measured its time, so the merge can
store it as it is.  `lemmas` are run lemmas (§1) the hook proposes;
phase 1 has no hook that answers `Provable`.  The two datatypes differ
only there: `Refutable name` and `Refuted {refuter = name}` carry the same
string; `Provable` carries the lemmas the slot does not.

Each hook derives and screens what it needs from `ctxt` inside its own
body (R-nitpick's assumption screen, `reasoners.ML:1645-1665`, moves with
the body; R-conv never used it).  The wrapper is protective only [author
2026-09-02]: `Exn.capture_body` around `Timeout.apply bound` around the
body; an interrupt re-raises; `Timeout.TIMEOUT` and any other exception
(logged via `Exception_Log`) make the hook answer `NONE` so the chain
proceeds.  Per-hook timings are temporary instrumentation inside hook
bodies, never a design surface.

| priority | hook | bound |
|---|---|---|
| 100 | R-conv | `\<phi>guard_rconv_timeout`, 300 ms [author 2026-09-02 10:37] |
| 200 | R-nitpick | `\<phi>guard_refute_timeout` 2000 ms, hang net +5 s = 7000 ms [author 2026-09-02 08:57]. The hook tries its subgoals inside its own body under the hook's ONE `Timeout.apply bound` — concurrently when there is more than one (`reasoners.ML:1645-1663` assembles one attempt per subgoal today; the parallel mechanism inside the body is the drafter's, `Par_List` or plain `Future.forks`, since `Race.race` is gone). The bound is the author's per-call hang net; it is never serialised over and never multiplied by the subgoal count. |
| 1000 | (reserved: LLM judge, phase 2) | own bound |
| 1000000 | **default refuter** | trivial — prints today's warning (`reasoners.ML:1486-1489`), answers `Refutable "default"` [author 2026-09-02 08:54] |

Priorities [author 2026-09-02 08:58].  `Handlers.invoke` returning `NONE`
is a registry defect (the default missing), never a normal outcome.

**The chain as one function.**  `run_chain : judge_arg -> chain_verdict
option` is the `Handlers.invoke` over the registry.  It is what a judge's
body calls.

**Judge body**, written out (not by reference — the sixth review found
that citing race.ML by line number lost its load-bearing `run`):

```
datatype judge_outcome = Chain_Answered of chain_verdict option | Judge_Aborted of exn

fun judge_body arg () =
  Thread_Attributes.uninterruptible_body (fn run =>
    (*`run` restores the task's normal attributes for the chain call ONLY:
      without it every Timeout.apply inside the chain is inert, because
      Timeout.apply' captures the attributes at its call site
      (timeout.ML:33-47) and a deferred interrupt is queued, not delivered.
      Classifying the outcome runs under deferred interrupts.*)
    case Exn.capture_body (fn () => run (run_chain arg) ()) of
      Exn.Res v => Chain_Answered v
    | Exn.Exn exn =>
        if Interrupt_Family.contains_interrupt exn
        then Exn.reraise exn      (*see below*)
        else Judge_Aborted exn)   (*a non-interrupt exception must not
                                    escape: it would cancel judge_group and
                                    every sibling (future.ML:422-437)*)
```

Forked as `Future.forks {name = "PLPR.guard_judge", group = SOME
judge_group, deps = [], pri = p, interrupts = true}` where `p` is the
forking task's own priority (`Task_Queue.pri_of_task` of `Future.worker_task
()`, 0 off a worker) — judges at the run's priority, so the end-of-run join
does not drain a fleet of lowest-priority tasks serially on the run's own
thread (`task_queue.ML:167-168`; race.ML:204-209 does the same).  Both
`interrupts = true` at fork AND `run` around the chain call are required
for the hooks' bounds to work; either alone leaves every bound inert.

**Why an interrupt re-raises.**  An interrupt reaching the top of a judge
body is never a hook's own timeout (those are converted to `TIMEOUT`
inside `Timeout.apply` and absorbed by the wrapper); it is a cancellation:
either `judge_group` was cancelled by the end-of-run steps (discard or
exception path — the outcome is not read), or the run was cancelled from
outside.  In the outside case the interrupt may have been absorbed by the
judge because `Future.join_results` executes ready judge jobs on the joining
thread itself (`future.ML:523-536`), so it never reaches the run's thread as
an exception.  Re-raising out of the job cancels `judge_group`
(`assign_result`, `future.ML:422-437`), which is exactly the signal step 6
of §4 reads after the join.  No thread identity and no flag are needed.

**Merge** (topmost invocation, after a complete join;
`Future.join_results`, four rows): `Exn.Res (Chain_Answered (SOME (Refutable
hook)))` → `entries := Inttab.update (i, (d, Refuted {refuter = hook}))`;
`Exn.Res (Chain_Answered (SOME (Provable {lemmas, proof})))` →
`entries := Inttab.update (i, (d, Proved proof))` and `lemmas := !lemmas
@ lemmas` (so the record carries them; the re-run that lets the engine use
the new `Proved` is phase 2's loop); `Exn.Res (Chain_Answered NONE)`, `Exn.Res
(Judge_Aborted _)`, `Exn.Exn _` → write nothing (slot `i` stays deleted).
`i` and `d` come from the judge's entry in `judges`.

**Warning** is the default refuter's own body, printed at the end of the
chain on the judge's thread [author 2026-09-03 04:14 "这个报警本身就是优先级
最低的最后执行的 default"]; `future_job` restores the forking thread's
Position data (`future.ML:441-452`), so it lands on the right command.

## 7. Rules

Stated of one run (§1).

- **R1 recording** [author 2026-09-02 12:03]: every completed
  `prove_or_refute` call ends with its slot filled — `Proved` by the call
  itself when P-auto proves, otherwise by the topmost invocation at the
  merge from the judge's answer (`Refuted`, or phase 2's `Proved`).  At the end of
  a run whose table is non-empty, the topmost invocation writes the run's
  WHOLE table as the record (never a delta — the store is last-write-wins)
  [author 2026-09-02 07:11 "在每次跑完后会把缓存重新写入磁盘"; empty
  table exempt: 2026-09-03 08:04].  A failed run records nothing [author
  2026-09-02 11:40]; an interrupted run writes and deletes nothing; a run
  that fired R2/R3 leaves the recording to its no-cache re-run.
- **R2 run failure against a record** [author 2026-09-02 11:48, 11:54;
  widened 2026-09-03 07:35]: a run with a record (`previous_final =
  SOME _`) fails → the record is stale: tombstone.  Failure by `NONE` →
  one no-cache re-run; its result is reported and it records under R1.
  Failure by a non-interrupt exception → no re-run, the exception is
  re-raised.  The deletion stands regardless.
- **R3 validation** [author 2026-09-02 07:11]: a run with a record
  compares its final digest with `previous_final`; mismatch → tombstone,
  one no-cache re-run, recorded under R1.
- **R4 faithful hits** [author 2026-09-02 10:40]: a hit is never re-judged.

On R2's re-run case and R3, the judges of the discarded run are cancelled,
not awaited (§4 step 5): their answers would be thrown away, and the
re-run judges the same guards afresh.  A failed run WITHOUT a record gets
no re-run, so its judges ARE awaited — the default refuter's warning is
then the diagnostic that explains the failure.

Recorded honestly, with no rule answering it:

- Staleness that leaves the final outcome unchanged (a `Refuted` whose
  countermodel rests on a changed definition; a `"default"` slot for a guard
  a new simp lemma would now prove — it warns on every hit; an R-nitpick
  model the pipeline cannot certify genuine) is reproduced faithfully
  forever.
- A cold run under load (a first build, or an R2/R3 re-run) can turn a
  guard that once proved inside the P-auto budget into a permanent
  `Refuted {"default"}`: the slot reproduces the cold run's own answer, so
  R3 structurally cannot fire on it.
- A run that gains or loses one `prove_or_refute` call early shifts every
  later call index; those calls miss (digest mismatch) for that run and the
  table is rewritten at its end.  One run's cost, not a permanent one.
- Two runs in one theory whose first pulled initial states agree in
  sequent and assumptions share a record key and clobber each other's
  record under last-write-wins.  §10's gate between steps (4) and (5)
  measures whether record keys repeat across corpus runs at all.
- There is NO user-facing invalidation feature [author 2026-09-03 04:55
  "否决。我从未批准过这东西"]; the file is regenerable and deleting it is
  the reset.

## 8. Persistence

- **Store kind.**  `cache_file.ML` gains `datatype store_kind = Proof_Store
  | Guard_Cache` (two nullary constructors — an equality type) and ONE total
  function carrying every per-kind constant:
  `kind_info Proof_Store = {ext = "proof-store", migrates = true,
  marks_writes = true, describe = ("Proof cache", "cached proofs")}`,
  `kind_info Guard_Cache = {ext = "guard-cache", migrates = false,
  marks_writes = false, describe = ("Guard cache", "cached guard verdicts")}`;
  `warn_not_writable` prints `"<Proof cache|Guard cache> for theory <name>
  is not writable (<path>); <cached proofs|cached guard verdicts> will be
  read but not recorded."` — the proof-store wording is today's
  (`:456-458`), the guard wording [author 2026-09-03 11:22 "批准"].
  `store_path` reads `#ext` (and `lock_path`, `store_file_key`,
  `probe_writable` follow unchanged); `migrate_legacy` and `load_store_raw`'s
  legacy `.proof-cache` fallback (`:594-597`) read `#migrates` — the guard
  kind's absent file is an empty table, never a fallback read;
  `update_cached_proof`'s collision detection (`written`, `proof_mark`,
  `:694-720`) reads `#marks_writes` — a guard record is legitimately
  rewritten every run and must not trip the "two DIFFERENT proofs under one
  key" alarm; `warn_not_writable` reads `#describe`, and `warned_dirs` is
  keyed by (directory, kind) (`:408-419`).  `openning_stores` becomes an
  instance of the `Table` functor over `(string * store_kind)` — a typed
  pair, never a concatenated string — across its whole entry-point surface
  (`force_reload`, `get_entry_i`, `get_store_i`, `get_store`,
  `register_async_task`, `close_store`, `invalidate_store`,
  `update_cached_proof`, `invalidate_proof_cache`, `try_write`/
  `store_is_writable`/`warn_not_writable`, `ensure_new_format`); a second
  `Theory.at_end` compacts the guard file.  [ruling 10 in §11: "not a
  behavior"; shape: sixth review U12]
- **Three existing entry points, no new ones** [author 2026-09-03 08:45
  asked which function; reuse: drafter]: read = `get_cached_proof thy
  Guard_Cache record_key : proof_cache option`, the record value being its
  string half; write = `update_cached_proof thy Guard_Cache {id =
  record_key, hash = NONE} (Time.zeroTime, value)` (signature `:184`; the
  time half is unused for this kind); tombstone = `invalidate_proof_cache
  false Guard_Cache record_key thy` (`:731-741`: in-memory
  `store_invalidate_proof`, then `append_record` of `encode_tombstone`).
  The proof store's locking (`store_append_lock`, `with_file_lock`, lock
  order v → fcntl → `openning_stores`, `:486`) is inherited unchanged.
- Guard records live in `<thy>.guard-cache`, GITIGNORED [author 2026-09-02
  13:01]: three patterns — `*.guard-cache`, `*.guard-cache.lock`,
  `*.guard-cache.tmp*` (compaction's temp file, `write_state_new`,
  `:319-328`) — in `contrib/phi-system/.gitignore` beside the existing
  `*.proof-store.lock` (the root `.gitignore` ignores `/contrib` wholesale
  and does not govern this tree).
- **Record value**: `{final : digest, lemmas : (term * string) list,
  entries : (int * digest * verdict) list}` [`lemmas`: author 2026-09-03
  10:53 "proof store 中 … 要多一个字段记录 the lemmas"] packed with the
  mlmsgpack packers `Proof_Store_Format` already uses
  through a `BytesIO` outstream and taken as a string (`BytesIO.mkOutstream`
  → pack → `BytesIO.toString`, exactly `encode_record`'s shape,
  `cache_file.ML:76-82`) [author 2026-09-03 05:42 "建议 ③MessagePack 然后走
  ByteIO packer 然后获取 string"].  Digests go through `packWord64` /
  `unpackWord64` (`mlmsgpack.sml:47`, `:94`, `:300-304`, `:804-816`), never
  `packInt`; `verdict` is tagged by an int like `PUT`/`TOMB`; a lemma's
  `term` is stored as the YXML string of `Term_XML.Encode.term` and read
  back with `Term_XML.Decode.term` (Pure's own term codec) [drafter].  NO
  format
  version [author 2026-09-03 03:02 "格式不对就直接抛弃"]: the decode is
  wrapped `\<^try>\<open>SOME (decode v) catch _ => NONE\<close>` — catch-ALL,
  because a truncated payload raises `Subscript` out of `BytesIO.inputN`
  (`mlmsgpack.sml:917-923`), not `Unpack`; `\<^try>` re-raises interrupts.
  Any exception means "there is no record".
- Written at most once per run, at the end of the run, after the merge,
  only when the table is non-empty.
- `\<phi>guard_cache` (default true; off = neither consult nor persist)
  is the one debugging switch [author 2026-09-02 10:41; off-semantics:
  drafter].  There is no judge switch [author 2026-09-03 05:47].

## 9. Phase 2 (deferred) and phase-1 enablers

Phase 1 lands: the control-flow classifier in Performant_Isabelle_ML (an
extensible predicate PLPR extends with `Success`, `Global_Cut`,
`Explorative_Backtrack`; `Phi_Sledgehammer_Solver.normalise` and
`eval_prf_str0` re-raise before classifying; `reason_record` redefined on
it); the `eval_prf_str` tracing line behind a verbosity gate [author
2026-09-02 10:29]; `Guard_Simp_SS` (§1) — a `Simpset`-functor instance
with attribute `\<phi>guard_simp`, filled per run at installation from the
run lemmas (§4; empty in phase 1 unless a theory declares something,
because nothing produces run lemmas yet) — consumed with
`Guard_Simp_SS.enhance` at the existing guard-context construction site
(`reasoners.ML:1819`), by `\<phi>guard_P_auto` and by the obligation
instance's `fastforce`; an empty simpset is the identity [author
2026-09-02 10:37 "(A) 赞同" — "先只落 is_control_flow 谓词和空引理化简集
槽"; the functor instance: 2026-09-03 11:15].  `Guard_Refute_SS` is
renamed `Nitpick_Refute_SS` in the same step [author 2026-09-03 11:15].
The types are settled now (§6); the LLM judge and the re-run loop that
consumes a merged `Provable` are phase 2 [author 2026-09-02 07:39 "LLM
judge 只是令我们重新跑, 不停重新跑直到 the judge 通过"].

## 10. Configuration, instrumentation, implementation order

| option | default |
|---|---|
| `\<phi>guard_prove_timeout` | 400 ms, provisional |
| `\<phi>guard_rconv_timeout` | 300 ms |
| `\<phi>guard_refute_timeout` | 2000 ms (kept; hang net +5 s derived) |
| `\<phi>guard_cache` | true |
| `\<phi>log_guard_race` → `\<phi>log_guard_decision` | false (renamed) |

Names approved [author 2026-09-03 04:58], as are the refuter names and the
module names `PLPR_Guard_Cache` / `PLPR_Refuters`.

Nothing is pending the author (2026-09-03 11:25).  Names: the factory
keeps `guard_condition_solver` [author 09:44]; `guard_condition_judge`,
`try_prove_or_give_up` [09:44], `\<phi>guard_P_auto` [11:11],
`Guard_Simp_SS` / `\<phi>guard_simp`, `Nitpick_Refute_SS` [11:15] are the
author's; the remaining ML identifiers (`run_chain`, `judge_body`,
`judge_outcome` with `Chain_Answered` / `Judge_Aborted`, `judge_arg`,
`add_refuter`, `Provable` / `Refutable`, `judge_group`, `previous_final`,
`record_key`, `kind_info`, `store_kind` with `Proof_Store` /
`Guard_Cache`, `Hasher.terms`, the Future name `"PLPR.guard_judge"`) are
the drafter's under the author's delegation [11:24 "这个不需要我批, 你可以
自行决定"].  Step (5)'s gate below is kept [11:25 "赞同留着"].

Instrumentation is temporary measurement code [author 2026-09-03 04:01]:
one permanent record, guard_decision (the successor of today's guard_race
record: verdict token, replay field, elapsed, `Hasher.hex` of the digest,
call index, n_goals, miss-side payload), behind `\<phi>log_guard_decision`;
everything the acceptance runs need beyond that is written for those runs
and must not change system behavior.  `Hasher.hex` appears in exactly one
place in this design: that log line.

Order — the split between (4) and (5) is about what each half can be
TESTED against, not commit granularity:

0. Re-verify line anchors; land the classifier, the two normaliser
   clauses, `reason_record`, the tracing gate, `Hasher.terms`.
1. `PLPR_Refuters`: the registry, `add_refuter`, `chain_verdict`,
   `run_chain`, the R-conv/R-nitpick bodies, the default refuter; rename
   `Guard_Refute_SS` → `Nitpick_Refute_SS` (four references).
2. The factory: `guard_condition_solver` parameterised; `try_prove_or_give_up`;
   `guard_condition_solver'`/`1` on it; P-auto's `method_setup`;
   `prove_or_refute` over the chain with no table and no judges (interim;
   same session as 3); `guard_condition_judge`; migrate every caller (§3);
   migrate `Test/Guard_Race_Smoke.thy`.
3. The env, the judges, join/merge, the end-of-run steps without R2/R3,
   guard_decision.
4. In-memory table: the call index, lookups, the two replay arms, slot
   deletion, R4, R1's in-memory half.
5. Persistence, gated: proceeds only if step (3)'s temporary instrumentation
   shows record keys repeating across two consecutive corpus runs (the
   same measurement leg (7) later tests).  Then: the store kind and
   `kind_info`, the re-keyed `openning_stores`, the second `at_end`, the
   three kind-threaded entry points, the `\<phi>guard_cache` switch, the
   gitignore entries, R1's write half, R2, R3, `previous_final`.
6. `Guard_Simp_SS` and its attribute, its consumption by
   `\<phi>guard_P_auto`, the guard-context construction site and the
   obligation instance, `lemmas` in the record and the env, and the
   run-lemma replay at installation.
7. Corpus acceptance: a cache-on and a cache-off leg, a concurrent
   Isa-REPL leg, a consecutive-run leg with a hit-rate floor; measure wall
   time, verdict flips as a per-call-index cache-on vs cache-off
   comparison, the latency of the first `prove_or_refute` call at the
   direct call sites, evidence rate, wall time of the join in the
   end-of-run steps, R2/R3 fire count, digest cost, store I/O; re-measure
   400 ms.  Testing via Isa-REPL against `Phi_System_Base` sources — never
   `isabelle build`.

## 11. Archaeology rulings (2026-09-03; all CLOSED)

An Opus agent compared every author utterance (156, interjections
included) against rev 7 and found the drafting had kept or introduced the
following without approval.  Each was put to the author; the rulings, with
the author's words, are recorded here.

1. ~~The 35 ms gate~~ — CLOSED 05:20: no gate; one P-auto under
   `\<phi>guard_prove_timeout` (400 ms provisional).
2. ~~Judge spawn after a non-landing `Proved (NONE, t)` replay~~ — CLOSED:
   already ruled 2026-09-02 10:29/10:31; wrongly re-asked three times.
3. ~~`guard_condition_solver` installing its own env~~ — CLOSED on the
   author's words: "我们还是在 gen_reason' 中做" (15:45) and "我们根本不区分"
   (14:54).  Superseded in shape by §12.9: the out-of-run callers use a
   different factory instance and never reach `prove_or_refute`.
4. ~~The `Lazy` store read and record key~~ — CLOSED 05:38 "否决。别增加
   复杂度": eager at installation; no `Lazy` anywhere.
5. ~~Conditional persistence~~ — CLOSED on the author's words: 07:11
   "在每次跑完后会把缓存重新写入磁盘"; the only-if-changed narrowing is
   dropped.  Refined by §12.8: an EMPTY table is not written.
6. ~~`final = NONE` matched option-wise~~ — CLOSED on the author's words:
   11:39 "run 层终局结果是 NONE 的话是不记缓存的因为整个 PLPR 失败了".  A
   `NONE` run result is R2's case and records nothing; `final` in a
   record is therefore always a digest, and R3 compares digests.
7. ~~The record value's shape~~ — CLOSED 05:42: MessagePack through a
   `BytesIO` packer, taken as a string, as the `PUT` value.
8. ~~The `\<phi>guard_judge` switch~~ — CLOSED 05:47: dropped.
9. ~~The 1.5× multiplier~~ — CLOSED: the author's 1 s ruling was given
   AGAINST the plan's `1.5t + delta` formula and reuses `tolerant_time`
   (`1.5t + 1000ms`) verbatim; the factor is the reused function's.
10. ~~Store-kind refactor extent~~ — CLOSED as implementation of the
    approved separate gitignored file ("好", 13:01).  Not a behavior.
11. ~~Phase-1 enablers~~ — CLOSED: the tracing gate is the author's
    (10:29); the re-raise clauses ARE the classifier "(A) 赞同" landed; the
    empty simpset slot is in the same "(A)" item verbatim.
12. ~~Implementation-order details~~ — CLOSED: work plan, not behavior;
    delegated ("其余的你可以让 agent team 去审核").

## 12. Sixth-review rulings (2026-09-03, 07:35–11:25)

The judge's 23 upheld findings and 3 relaxation proposals were put to the
author.  Rulings, in the order given:

1. **R2's trigger** (judge U3b): widened to `NONE` OR a non-interrupt
   exception; on the exception path cancel the judges, uninterruptible
   re-join, tombstone the record, re-raise, NO re-run [07:35 "赞同" ×4].
2. **`Guard_Fails` retired** for "refutable" [07:35 "这根本不是 failure 是
   被判定为 unprovable"; the name "refutable" is the author's 08:54 word].
   `prove_or_refute`'s type is unchanged; `Refutable` is the chain's
   constructor (07:38).
3. **Back to the index design** [07:54 "这些都是最初为什么我要用 index 来做
   索引而不直接用 digest 做索引的原因"; 07:59 "好, 请回到我的 index 设计"].
   The drafting's digest-keyed table (approved 2026-09-02 10:25 on a wrong
   argument by the drafter) is withdrawn.  DISSOLVED by this ruling: judge
   U5 (dedup per digest), U8 (`Symtab.default` merge), U9 (R3 thrash on
   the shared-entry class), and the "identical subgoals share an entry"
   staleness class.  An earlier 07:44 "赞同" to a digest-keyed judge table
   is superseded.
4. **Guard digest content**: the guard's own subgoals only — not
   `Assumption.all_assms_of ctxt`, not the theory name [07:48].
5. **Digests are `Word64`** in memory, `packWord64` on disk [07:51, 07:58;
   judge U14].
6. **The env**: `Proof_Data` slot of type `env option Unsynchronized.ref
   option`; closing is `cell := NONE`; no `Synchronized` anywhere ("关闭就
   只是赋值! 赋值是瞬间的", 08:11); `run_id`, `consumed`, `closed` deleted
   (08:11–08:33); `probe_group` deleted (09:50–09:51: nobody but the
   topmost invocation cancels `judge_group`, so `is_canceled judge_group`
   alone tells outside cancellation apart).  DISSOLVED: judge U2's
   `owner_thread` + absorption flag (an interrupt re-raises instead, §6),
   U4's three-state slot check (a cell holding `NONE` IS "no open env"),
   U13 (no atomicity rule: one writer).  The AoA-fork scenario the sixth
   review used to motivate a closed-env branch was ruled "钻牛角尖 … 现有
   代码里绝对没有这种行为" (08:10); no such branch exists.
7. **Record key**: `"PLPRGUARD" ^ Hasher.compact (…)` [08:33 "建议直接使用
   Hasher.compact"; 08:44 "反对删除前缀! 采用 PLPRGUARD"].  The 08:15
   question about the proof-ID mechanism is answered by this: the key is a
   `Hasher` digest, not a `Phi_ID`.
8. **Relaxation A accepted**: an empty table is not persisted [08:04].
9. **Relaxation B superseded by the author's factory** [09:44]: the
   out-of-run callers (`local_value.ML:168`, `toplevel0.ML:364`,
   `generic_variable_access2.ML:181`, `:264`; `application.ML:133` is
   commented out) solve proof obligations (`Premise default P`,
   `Premise MODE_COLLECT P`), all through `guard_condition_solver'`/`1`;
   they get `try_prove_or_give_up`.  In-run reasoners get
   `guard_condition_judge`.  `defer_premise` (`PLPR.thy:1974-1975`), the
   one other in-run user of the old function, gets the third instance
   (§12.18).
10. **Relaxation C accepted**: on R2 (re-run case) and R3 the judges are
    cancelled, not awaited; R3's comparison moves before the join [09:48
    "好的, 赞同, 可以直接取消"].  Not the rejected join deadline: nothing
    cut is ever persisted.
11. **`aux`** deferred until the plan is approved [07:40].
12. **Tombstone function**: the existing `invalidate_proof_cache` with the
    kind and `warn = false` [08:45 asked; drafter's answer, §8].  The rev-8
    "trio" of new functions is withdrawn; `kind_info`'s `marks_writes`
    replaces it.
13. **`work_group` → `judge_group`**, one level, child of the current
    task's group [09:49–09:51].
14. **`aux` inlined; run lemmas carry proofs** [10:50 "judging a provable
    goal 需要返回以下信息: 1. 哪些 lemmas might be helpful to strengthen the
    simplifier in the P-auto 2. 对 the goal 的证明 tactic script"; 10:53
    "(statement, proof script) pairs … proof store 中(也可能是 env 中)要多
    一个字段"; 10:59 "不需要专门定义一个类型叫 aux, 可以直接内联进
    Actually_Provable 构造子"].  The record and the env gain `lemmas`; they
    are proved at installation and go into `Guard_Simp_SS` (item 19).
15. **`evidence` deleted** [10:59 "建议直接删掉 evidence"]: `Refutable of
    string`.
16. **P-auto exposed as a named proof method; verdict stores its name**
    [10:59 "可以直接走 string 类型然后用它的名字吗? 当然在 evaluation 时候
    可以用此名字来短路"].  `Proved of proof`, `type proof =
    Phi_Proof_Store.proof_cache` [11:00].  Supersedes 05:19 under that
    ruling's own second clause.  Method name `\<phi>guard_P_auto` [11:11
    "批准"].
17. **`Actually_Provable of {lemmas : (term * string) list, proof : proof}`**,
    the judge measuring the time [11:01 "可以直接让 judge 来给时间"]; the
    two datatypes then differ only by the lemmas.  The constructor is
    written `Provable` below (naming delegated, item 22).
18. **`defer_premise`'s solve-now case**: `guard_condition_solver` over
    `fastforce` in a `Guard_Simp_SS`-enhanced ctxt, bound optional and
    absent by default [11:11 "建议用 guard_condition_solver over a the
    fastforce tactic … 这个 fastforce will be augmented by that specific
    simpset"; 11:15 "赞同, 但限时是可选的, 也可以不限时"].
    `try_prove_or_give_up` therefore takes the tactic and an optional bound.
19. **`Guard_Simp_SS` / `\<phi>guard_simp`** as the run-lemma simpset, an
    instance of the repository's `Simpset` functor [11:15 "赞同
    Guard_Simp_SS, \<phi>guard_simp 命名"]; replaces rev 9's "auxiliary-
    lemma slot" (a bespoke `thm list` would have reinvented the functor).
20. **`Guard_Refute_SS` → `Nitpick_Refute_SS`** [11:15], after the author
    asked what it is for (11:13): R-nitpick's preprocessing simpset.
21. **Not-writable warning wording for the guard kind** [11:22 "批准"]:
    "Guard cache for theory … is not writable (…); cached guard verdicts
    will be read but not recorded."
22. **Remaining ML identifiers delegated to the drafter** [11:24 "这个不需
    要我批, 你可以自行决定"]; the drafter chose `Provable` (for
    `Actually_Provable`) and `Chain_Answered` (for `Chain_Ran`), the rest
    as listed in §10.
23. **Step (5)'s gate kept** [11:25 "赞同留着"].

Drafter fixes from the sixth review applied without a ruling (work plan
and wording, per §11.12): U1 (judge body with `run`, written out), U3a
(nesting wording), U6 (judge priority), U7 (R-nitpick subgoals concurrent),
U10 (record-key collision recorded; step-5 gate), U11 (`migrates`), U12
(`kind_info`, typed table key), U15 (tombstone halves — now by reuse),
U16 (`warned_dirs` key; wording approved, item 21), U17 (catch-all decode), U18
(gitignore), U19 (`judge_arg` without `assms`), U20 (order re-split), U21
(digest caveats), U22 (cold-run ratchet disclosed; per-index flip metric),
U23 (slot representation).  Discarded by the judge and not applied: the
`written`-table collision detector, the `Symtab.default` merge (moot), the
merged-table re-run, the equalised replay bound, the widened `bound`.

Terminology pass (07:30): §1 is the authoritative glossary; the retired
names are listed at its end.
