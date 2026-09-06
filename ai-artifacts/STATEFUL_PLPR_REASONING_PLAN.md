# Stateful PLPR reasoning — carrying the context across run boundaries

Status: rev 11 (2026-09-05), review converged.  No code has been written.
The seventh review's frame finding is decided (§9.14, §10.38:
`export_aux_lemma`); the eighth review (Workflow `wf_7f684be1-055`) ruled
READY_WITH_EDITS with one wording correction in §11.2, folded in.  The fifth review
(Workflow `wf_5c0349fd-da9`, NOT_READY, 12 upheld, all on the rev 7
material) is folded in; its one author decision was the status quo
(§9.12).  The sixth review (Workflow `wf_6bb7767f-95e`, NOT_READY, 4
upheld, 11 rejected as hair-splitting) is folded in; its author decision
is §9.13.  The seventh review (Workflow `wf_f3f7c6f5-bd8`, NOT_READY, 2
upheld, 1 rejected) found one frame outside phi's control (Isar `obtain`
inside a block) — open as §9.14 — and one wording fix, folded in.  The fourth review
(Workflow `wf_379c9e90-317`) ruled READY_WITH_EDITS — twelve mechanical
corrections, no design change, no author decision — and they are folded
in.  After it the author ruled on one behavioural point the fourth review
had only filed as a note (the two Pure-installed assumption frames a
transplanted theorem crosses when leaving a block): §10.37, with the
uniform block-boundary export function in §6.4; the installation
mechanism for the frame at `toplevel0.ML:234` was verified by an agent
(§9.12).  The first
adversarial review of the call-site classification (Workflow
`wf_880bcf1d-a03`, NOT_READY, 31 upheld) is folded into §5; the second
review of the whole plan (Workflow `wf_ffa4d227-452`, NOT_READY, 39 upheld,
7 rejected, 6 author decisions A1–A6) is folded in everywhere, and the
author's rulings on A1–A6 are §10.29–§10.34; the third review (Workflow
`wf_711de0d3-5db`, NOT_READY, 19 upheld, 10 rejected, 2 author decisions
AD1–AD2) is folded in, its rulings are §10.35–§10.36 and §9.11; the
opinions the author or the judges rejected are listed in §9.10 and must
not be raised again.  Every
behavioural decision carries its provenance: [author YYYY-MM-DDTHH:MM
"quote"] is the author's own ruling (transcript timestamp, UTC); [drafter]
is a drafting decision the author may veto; §9 lists every [drafter]
decision.  Line anchors are as of 2026-09-04/05 and every anchor of §2, §5,
§6, §10 and §12 is re-verified at implementation start (§8 step 0).

Scope: this plan designs a GENERAL mechanism — data learned inside a run
reaches later reasoning and later phi statements — and the engine changes
that carry it.  Applications of the mechanism (which data, registered by
whom) are out of scope; each application will be its own plan.  [author
2026-09-04T04:36 "我们也许不得不需要扩展整个 PLPR 引擎以 context_state ->
context_state"] [author 2026-09-04T06:01 "我们现在在设计一个通用的机制、系
统 … 我们现在不考虑 guard SS 而只考虑这个通用机制"]

Paths are relative to `contrib/phi-system/`.  `PLPR/` abbreviates
`Phi_Logic_Programming_Reasoner/library/`, `SYS/` abbreviates
`Phi_System/library/`, `SEM/` abbreviates `Phi_Semantics/library/`.
Isabelle sources: `contrib/Isabelle2025-2/src/Pure/`.

---

## 1. Glossary

- **run**: one invocation of the engine `gen_reason'` (`PLPR/reasoner.ML:910`).
  Inside a run the state is `context_state = Proof.context * thm` and every
  reasoner is `context_state -> context_state Seq.seq`.  [code]
- **run boundary**: the place where a run's result `(ctxt', thm')` is handed
  back to the code that started the run.  Today the boundary keeps `thm'`
  (after `Proof_Context.export ctxt' ctxt`) and discards `ctxt'`
  (`PLPR/reasoner.ML:946-967`).  [plain phrase]
- **inner context / outer context**: the `ctxt'` a run ends with, and the
  `ctxt` the run was started with.  [plain phrase, same as Isabelle's
  `Proof_Context.export inner outer`]
- **the chain**: the continuous sequence of reasoning in the certified
  programming environment, where each phi statement inherits the context of
  the previous one.  [author 2026-09-04T05:28, §5.1]
- **export hook**: a registered function `inner -> outer -> outer'` that
  transplants one kind of data from the inner context into the outer
  context.  [author 2026-09-04T05:21 "可注册的导出钩子表"]
- **the run-boundary export function**: the single function every run
  boundary calls; it exports the theorem and runs the export hooks.  [author
  2026-09-04T05:21 "专门做成一个 PLPR export 函数"]
- **boundary function / caller**: the two kinds of line in the call-site
  classification, §5.1.  [plain phrase; replaced the earlier four
  categories A/B/C/D after the first review]

---

## 2. What the run boundary does today (verified facts)

### 2.1 The four boundary export sites

The engine `gen_reason'` (defined at `PLPR/reasoner.ML:910`) is called at
exactly three places, all in `reasoner.ML`: `:931` (`internal_reason`),
`:962` (`internal_reason_s`), `:972` (`reason_tac`); every other entry to
the engine goes through `internal_reason` (`:1262`, the path for rules
carrying an ML guard, which no live rule reaches, and the §5.5 sites).
Theorems are exported at a run boundary at four sites today:

- `PLPR/reasoner.ML:952` in `reason` (`:947-953`; `reason1` `:955-958` calls it);
- `PLPR/reasoner.ML:968` in `reason_sXXX` (`:965-969`) — dead: no caller
  anywhere (the only historical one is inside the comment
  `SYS/system/application.ML:109-137`); deleted by the migration, not ported;
- `PLPR/optimum_solution.ML:137` in `best_among` (`:127-138`): one candidate
  goes through `reason`, several run its own search and export the winner;
- `PLPR/exhaustive.ML:66` in the success handler of `reason_exhaustively`
  (`:64-67`; the run itself is at `:68`).

Kept without export today: the Isar method `\<phi>reason` (`Method.setup`,
`reasoner.ML:1435-1443`, via `reason_tac` `:971-976`, `Seq.Result (ctxt', thm')`
— the inner context goes straight into the Isar proof state; after the
migration it exports like every other boundary, §10.16), and every
`internal_reason` caller (§5.5).  The method has no live caller: its twelve
uncommented uses are all in `Phi_System/PhiSem_Formalization_Tools'.thy`,
which is never loaded (§5.1 item 5), and the two hits in `Phi_Semantics`
are inside comments.

After the migration the sites that call `export_state` are `reasoner.ML:952`
(`reason`), `:971-976` (`reason_tac`, newly exporting), `optimum_solution.ML:137`
(`best_among`) and `exhaustive.ML:66` (success handler, context discarded,
§9.4); `reason_sXXX` / `:968` is deleted.  §12.2 is the authoritative table.

### 2.2 What `Proof_Context.export inner outer` does

`Isar/proof_context.ML:922-926`: `Assumption.export inner outer` then
`Variable.export inner outer`.

- `assumption.ML:153-156`: `norm_hhf_protect inner`, then the export
  function of every assumption present in inner but not in outer, then
  `norm_hhf_protect outer`.  The two HHF normalisations run unconditionally;
  `gen_norm_hhf` (`raw_simplifier.ML`) skips the rewrite when the theorem is
  already in HHF form but always does `Thm.adjust_maxidx_thm ~1` and
  `Variable.gen_all` (outermost `⋀` parameters become schematic variables).
- `variable.ML:516-572`: generalises the Frees fixed in inner but not in
  outer and the TFrees declared only in inner; with no new fixes
  `Thm.generalize` on empty sets is the identity (`thm.ML:1807-1808`).

### 2.3 Which reasoners change the context inside a run

All 126 `\<phi>reasoner_ML` registrations and the `\<phi>reason` rule path
(`reasoner.ML:850`, `:866`, ctxt passed through unchanged) were inspected;
no ML-side registration exists besides `\<phi>reasoner_ML`.

Logical changes (fixes / assumptions), one family only:
- `PLPR/Subgoal_Env.ML:50-79` `allocate_subgoal`: `Variable.add_fixes`
  of a fresh `\<r>GOALn`, an empty `Assumption.add_assms` whose export
  function errors if the tag still occurs in the exported theorem, and a
  Proof_Data update.  Users: SUBGOAL (`PLPR.thy:2597`), Try (`:2820`),
  Orelse_shortcut (`:2716`).  SOLVE_SUBGOAL (`:2599`) changes Proof_Data
  and a Synchronized variable only.
- PLPR's own Obtain / DO_OBTAIN (`PLPR.thy:3119-3193` is one comment block,
  so the assumption frame at `:3186` is dead too — a different mechanism
  from phi's live existential elimination `NuObtain`,
  `Phi_System/library/system/obtain.ML`, whose frame is a block-level one,
  §6.4), Exhaustive Divergence
  (`:2606-2626`) and `End_Optimal_Synthesis` (`Phi_System/IDE_CP_Core.thy:569`,
  inside the comment block `:557-581`; it calls a `PLPR_Optimum_Solution.finish`
  that the signature `optimum_solution.ML:1-11` does not export, so it could
  not compile if live) are inside comment blocks; not live.

Data changes (Proof_Data / Config / reasoner table), lost at the boundary
today:
- `PLPR.thy:1281-1296` Push_Envir_Var / Pop_Envir_Var (`PLPR_Env.push/pop`);
  effects such as `prove_obligations_in_time` (`PLPR.thy:1996-2004`) change
  Config values through it.
- `PLPR/nested.ML` Scope counter; `PLPR/optimum_solution.ML` Stack / Cost.
- `PLPR/memoization.ML:39-47` Memoize: `Phi_Reasoner.add` puts a local rule
  into the context's reasoner table.  Note `gen_reason'` snapshots the
  reasoner table at entry (`reasoner.ML:915`) and the loop uses the snapshot
  (`:855`), so a rule added mid-run is visible only to runs started later.
- `Phi_BI/Phi_BI.thy:5594` ToR_Entry_Point keeps the ctxt' of a nested
  `internal_reason`.

NOT lost today, and unaffected by the migration: data held in ref-backed
Proof_Data.  `report_unprocessed_element_index`
(`Phi_System/IDE_CP_Core.thy:2026-2040`) writes `Unprc_EleIdx`, a
`Single_Thread_Proof_Data_Opt` (`Phi_Help.ML:235-258`,
`generic_element_access.ML:56`) whose slot holds an `Unsynchronized.ref`;
`put` writes through the reference, so the value is visible in the outer
context that installed it (`Phi_Semantics/library/generic_element_access.ML:117-123,
:172-178`).  The failure-reason collector (`failure_reason.ML:26-37`,
`Synchronized.var`) has the same shape.  Expected behaviour; not touched
(§10.24).

Every other in-reasoner `Variable.import`, `variant_fixes`, `put_simpset`
(`PLPR/simplifier.ML:53, :89`, `Phi_BI/library/tools/helper_reasoners.ML`,
`PLPR/reasoners.ML:1355`, `PLPR.thy:1061`) is local and the original ctxt is
re-paired on return.

Consequence: the only logical necessity of today's export is the
Subgoal_Env tag guard; everything else the export does is HHF
normalisation and the (unintended) loss of data changes.

---

## 3. Design decisions already taken

- D1. One run-boundary export function, used at every post-migration
  boundary site (the list at the end of §2.1; §12.2).  [author
  2026-09-04T05:21 "赞同，建议专门做成一个 PLPR export 函数"]
- D2. Data leaves a run only through registered export hooks; the boundary
  returns the OUTER context plus what the hooks transplant, never the inner
  context as-is.  [author 2026-09-04T05:21 "赞同 2 可注册的导出钩子表"]
- D3. A hook that transplants theorems exports each of them itself, one
  by one — since §10.38 through `PLPR_Context_Export.export_aux_lemma
  inner outer`, which wraps `Proof_Context.export inner outer`.  [author
  2026-09-04T05:21 "赞同。建议这个由钩子自己去写"; 2026-09-05T10:46]
- D4. The public entry points return a context: the top-level type becomes
  `context_state -> context_state option` (or the corresponding shape).
  [author 2026-09-04T05:24 "这依旧需要把整个引擎的顶层函数类型改成
  `context_state -> context_state`"]
- D5. Classification principle, §5.1.  [author 2026-09-04T05:28]
- D6. `extract_implied_fact` does not inherit (a discarding caller).  [author
  2026-09-04T05:34 "extract_implied_fact 的语义是很明确的，是去提取出 the
  implied facts 因此我认为应当不继承"]
- D7. This plan lives in `ai-artifacts/`.  [author 2026-09-04T05:44 "可以把计
  划文档等写到 @ai-artifacts/ 里"] [drafter: the repository root has no
  `ai-artifacts/`; `contrib/phi-system/ai-artifacts/` is the one meant]
- D8. Data transplanted into the chain context lives for the rest of the
  programming block; the mechanism has no removal point.  [author
  2026-09-04T06:02 "没错，这就是我期望的！"]

---

## 4. The design

### 4.1 The structure `PLPR_Context_Export`

A new file `Phi_Logic_Programming_Reasoner/library/context_export.ML`, loaded
by a new `ML_file` line placed immediately before `library/reasoner.ML`
(`PLPR.thy:542`); it depends only on `Proof.context`, `thm` and
`Generic_Data`.  [author 2026-09-04T07:16 "我建议专门新建一个 ML structure 与文
件"] [author 2026-09-04T07:17 "赞同 PLPR_Context_Export.export_context"]

```
signature PLPR_CONTEXT_EXPORT = sig

  (* the hook table: the existing Hooks functor (library/tools/Hook.ML,
     loaded at PLPR.thy:441), no wrapper around it.
     A hook is  inner -> outer -> outer';  registered with
       PLPR_Context_Export.Hooks.add priority hook
     (smaller priority runs first; one hook per priority per theory). *)
  structure Hooks : HOOKS
    where type arg = Proof.context (*inner*) and type state = Proof.context (*outer*)

  (* transplant hook-owned data from inner into outer.
     Precondition: inner extends outer (as for Proof_Context.export). *)
  val export_context : Proof.context (*inner*) -> Proof.context (*outer*) -> Proof.context

  (* the run boundary: Proof_Context.export for the theorem, export_context for the context *)
  val export_state   : Proof.context (*inner*) -> Proof.context (*outer*) -> thm -> Proof.context * thm

  (* raised by the block-boundary export function (§6.4) for a theorem that is not
     the state sequent but depends on a frame assumption that is not of the form
     Premise _ C: the theorem cannot leave the block.  (A Premise _ C dependence is
     exported as C ==> th instead, §10.37.)  export_aux_lemma catches it. *)
  exception UNEXPORTABLE of thm

  (* the only way a hook exports a theorem (H1).  NONE: the theorem does not leave
     the run/block — it mentions a variable fixed in inner but not in outer, or an
     assumption frame raised UNEXPORTABLE.  SOME: Proof_Context.export inner outer. *)
  val export_aux_lemma : Proof.context (*inner*) -> Proof.context (*outer*) -> thm -> thm option

end
```

`export_aux_lemma` (§10.38):
```
fun export_aux_lemma inner outer th =
  if Term.exists_subterm (fn Free (x, _) => Variable.is_newly_fixed inner outer x | _ => false)
                         (Thm.prop_of th)
  then NONE
  else SOME (singleton (Proof_Context.export inner outer) th) handle UNEXPORTABLE _ => NONE
```
`Variable.is_newly_fixed` (`variable.ML:363`) is Pure's own "fixed in inner,
not in outer".  Only the statement (`Thm.prop_of`) is inspected: a theorem
whose statement is free of local variables but whose proof used a block
fact is exactly what the frames are for (§6.4).  [author 2026-09-05T10:46
"可以，但不能叫 export_thm，最多叫 export_helper_thm/export_aux_lemma 之类"]

`UNEXPORTABLE` lives here because `context_export.ML` (`PLPR.thy:542`) is
loaded before every callback frame that raises it (`Phi_System`, loaded
after `PLPR`) and before every hook that catches it.  [author
2026-09-04T14:34 "(1) 赞同"]

[author 2026-09-04T07:30 "建议直接重用 the Hooks functor 别搞任何 wrappers! 可
以带有 priority"]

Behaviour:
- `export_context inner outer =
   if pointer_eq (inner, outer) then outer
   else Hooks.invoke (Context.Proof outer) inner outer`:
  the hook table is read from `outer`, the receiving side [author
  2026-09-04T07:30 "赞同"]; a hook registered only inside a run is not run.
  `Hooks.invoke` folds the table in priority order (`Hook.ML:100-107`).
  The `pointer_eq` short cut covers the two short circuits of
  `internal_reason` (`reasoner.ML:928`, `:930`), which return the incoming
  context itself.  [author 2026-09-04T10:56 "支持使用 pointer_eq 的 short
  cut"]  No other check: folding an empty table is already the cheapest path.
- `export_state inner outer thm =
   (export_context inner outer, singleton (Proof_Context.export inner outer) thm)`
  — the theorem part is exactly what the boundary sites do today, so the
  Subgoal_Env tag guard and the HHF normalisation (§2.2) are unchanged
  (§10.5).  `Proof_Context.export` (not `export_goal`) at every boundary,
  including the Isar method `\<phi>reason` whose theorem is a goal state:
  the two differ only in how assumptions made by `assume` are discharged
  (`assumption.ML:48-49`, `#A ⟹ B` versus `A ⟹ B`), and the only assumption
  frame a run adds (`Subgoal_Env.ML:62-65`) has no assumptions and ignores
  the flag.  [author 2026-09-04T10:56 "我认为使用 Proof_Context.export 是没
  错的"]
- The four post-migration boundary sites (`reasoner.ML:952`, `:971-976`,
  `optimum_solution.ML:137`, `exhaustive.ML:66`; end of §2.1) call
  `export_state`.  Code that must send a context back onto an earlier base
  without a theorem calls `export_context` directly (§6.5).  [author 2026-09-04T07:14 "the PLPR
  export 钩子需要在 reasoner.ML 的 signature 中暴露一个接口允许把任意 ctxt' 导出
  到 ctxt"]

Because the base is `outer`, the fixes and the assumption of Subgoal_Env,
the Scope / Stack / Cost counters, the `PLPR_Env` stack, the memoised local
rules, the trace-level Config tweaks (`Config.map Phi_Reasoner.trace`) and
`Context_Position.set_visible false` (`PLPR.thy:2145`) all stay inside the
run.  No rewrite of Subgoal_Env is needed (§10.29).

Storage of the hook table: whatever the `Hooks` functor does
(`Generic_Data` keyed by priority and theory name, `Hook.ML:64-78`).

### 4.2 The hook contract

Hook contract (each registered hook must document that it satisfies it):
- H1. Theorems transplanted go through `PLPR_Context_Export.export_aux_lemma
  inner outer`, one theorem at a time, `NONE` meaning "drop it"; a hook
  never calls `Proof_Context.export` itself (§10.38).  `export_aux_lemma`
  drops a theorem that mentions a variable fixed inside the run or block
  (it could not mean anything outside, and an un-owned Pure frame such as
  Isar `obtain`'s would abort on it, §9.14), and otherwise runs
  `Proof_Context.export inner outer` (D3), dropping the theorem when the
  block-boundary export function raises `UNEXPORTABLE` — a theorem that is
  not the state sequent and depends on a block assumption that is not of
  the form `Premise _ C` (§6.4, §10.29, §10.37; a `Premise _ C` dependence
  comes out as `C ⟹ th`).  Exporting a whole list at once would lose the
  whole list on the first unexportable theorem.  [author
  2026-09-04T14:30 "在识别到非 sequent 又依赖了那些假设的的话，是必须 raise some
  specific exception 令 the export 放弃，抛弃这些 thms 的"]
- H2. Re-exportable: for any three contexts with `inner` extending
  `outer` extending `base`, `hook (hook inner outer) base` equals
  `hook inner base`.  Consequences: exporting twice onto the same base is
  the same as exporting once (idempotence, `outer = base`), so a hook that
  ACCUMULATES — appends inner's content to outer's slot on every export,
  e.g. `outer_list @ inner_list` — does not satisfy the contract; a hook
  that overwrites its slot, or merges as a set union, does.  H2 is what
  makes §6.5 (re-export onto an earlier base) and §4.3 (data climbing
  through nested boundaries) sound.  [author 2026-09-05T06:16 "AD2 (a)";
  §10.36]
- H3. Order-independent with respect to the other hooks: a hook reads only
  its own data from `inner` and writes only its own data into `outer`.
- Consequence for callers of `export_context`: a base whose export result
  is KEPT is exported onto once.  `export_context` is not commutative for a
  hook that overwrites its slot, so two inner contexts that are siblings
  (both extending the same base, neither extending the other) must not be
  exported onto that base one after the other with the results chained —
  the second would overwrite what the first brought.  To combine data from
  two runs, export the first, continue reasoning ON the result, then export
  the second onto it (§10.30).  Exporting the SAME inner twice onto one base
  is merely redundant, by H2; and `exhaustive.ML:66` exports every branch
  onto one fixed base but discards every result (§9.4, §12.2), which is
  harmless for the same reason.
- (There is no rule about cost.  How much work a hook does, and whether it
  compares before writing or simply overwrites, is entirely the hook's own
  business; a hook that overwrites is often the fastest.  [author
  2026-09-04T07:33 "这个可以全权交给钩子自己去实现 … 直接覆写是最快的，反而检查
  相等是非常慢的"])

### 4.3 The entry points

[author 2026-09-04T06:12 "赞同": the state-returning functions take the
existing names.]

```
val reason      : handlers option -> int option -> context_state -> context_state option      (* was: Proof.context -> thm -> thm option *)
val reason1     : (unit -> string) -> handlers option -> int option -> context_state -> context_state
val reason_tac  : handlers option -> int option -> Proof.context -> context_tactic             (* type unchanged; body exports, §10.16 *)
val internal_reason : handlers option -> int option -> context_state -> context_state option (* unchanged *)
```

`reason_tac`'s export base is `fst stat` (the goal node's context), not
its `ctxt` parameter (the static method context of `Method.evaluate`,
`method.ML:537-539`): `apply_method` writes the result onto the goal node
(`proof.ML:418-422`) and `after_qed'` exports from it (`:1101-1105`).

No thm-only wrapper is provided: a caller that does not need the context
writes `|> Option.map snd` (after `reason`) or `|> snd` (after `reason1`)
itself, so the discard is visible at the call site.  [author
2026-09-04T07:29 "不要提供这样的包装，而是让调用方自己去 snd/fst"]

`reason` = `internal_reason` then `PLPR_Context_Export.export_state ctxt' ctxt`.
Every discarding caller (§5.4) is edited once to add the `snd`; the hooks
run there too (§10.7).
`reason_sXXX` / `internal_reason_s` are deleted (dead, §2.1).

`best_among` (`optimum_solution.ML:127-138`) returns `context_state option`
and uses `export_state` for the winning branch.  The exhaustive success
handler (`exhaustive.ML:64-67`) keeps exporting each branch theorem through
`export_state` and discards the per-branch context (§9.4).

A boundary reached from inside another run and whose context is kept
(`simplifier.ML:75`) has the enclosing run's mid-run context as its
`outer`, so transplanted data climbs one level per boundary; the enclosing
run's own boundary transplants it again onto the enclosing run's start
context.  Since inner extends the mid-run context, which extends the start
context, H2 in its three-context form says the result is the same as one
direct export.  (The other nested boundary, `memoization.ML:22`, discards
its context by §10.18; nothing climbs from it.)

---

## 5. Call-site classification

### 5.1 Principle

[author 2026-09-04T05:28] "我认为基本上秉承的原则是，连续的一长串推理必须继承
the context 比如 the certified programming 环境中，下一个语句的 context 需要继
承上一个语句的；相反如果各个推理是各自的最后不 join 的任务，比如
phi_type_algebra 推导器，每次自己就是一个独立的任务去推理一个独立的事项，那么此
时我认为，作为推理的终结是不需要继承 the context"

The test applied to a call site, in the principle's own terms: after this
run, will the chain read the returned context again?  Yes → the caller
inherits.  No → the caller discards explicitly with `snd` (§4.3).
Recorded exception: `extract_implied_fact` discards (D6) even though its
callers install the extracted facts into the live context through
`Phi_Sys.add_lemmata`, an explicit, already-exported route.

Two kinds of line are distinguished (after the first adversarial review,
which found the previous four categories mixing them):

- **boundary function**: code that starts a run (or calls another boundary
  function) and hands the result to its own caller.  A boundary function
  gets no inherit/discard label; its signature simply changes to return
  `context_state` (§5.2).  Its callers carry the label.
- **caller**: a place that calls a boundary function on a `(ctxt, thm)`
  and decides what to do with the returned context (§5.3, §5.4).

Sites that use `internal_reason` inside a reasoner are not classified at
all: the inner run's context flows into the enclosing run's state by
construction and nothing changes for them (§5.5) [author 2026-09-04T07:17
"既然所有的例子都是自然继承那么我建议你可以直接不考虑这些"].

Inventory method (corrected after the review):
1. `grep -rn "gen_reason'"` over `reasoner.ML` returns the definition line
   (`:910`) plus the three call sites (§2.1).
2. `grep -rn 'Phi_Reasoner\.\(reason\|reason1\|reason_sXXX\|internal_reason\|reason_tac\)\b'`
   over `*.ML`, `*.thy` for external callers, plus a per-line comment check
   inside `reasoner.ML` (its own calls are unqualified: `:1262`, `:1432`,
   `:1441`).  Excluded: `Docs/`, `ai-artifacts/`, `*.unicode.thy`;
   `Phi_Logic_Programming_Reasoner/Test/` (unbuilt: the PLPR ROOT builds
   only the theory `PLPR`, and `Test/Guard_Race_Smoke.thy` is imported by
   nothing); the single theory
   `Phi_Test/Instructions_to_make_a_conventional_VCG.thy` (in no ROOT and
   imported by nothing).  `Phi_Test/` itself is a built session
   (`ROOTS`, `Phi_Test/ROOT`: `PhiTest_All`, `PhiTest_Arithmetic`) and is
   NOT excluded.
   Result: 56 hits, 2 of them the `Exception_Log.capture` site strings at
   `PLPR/reasoner.ML:948, :956`, 13 in comments or prose (`PLPR.thy:841`,
   `SYS/system/processor.ML:240`, `deriver_framework.ML:1042`,
   `semantic_type.ML:53`, `semimodule_scalar.ML:21, :62`,
   `guess_property.ML:41`, `guess_semimodule.ML:100, :288, :325, :370`,
   `PLPR/reasoners.ML:323`, `PLPR/tools/extracting_pure_facts.ML:160`),
   41 live.
3. The adapters `Phi_Reasoners.wrap` (28 occurrences, 27 uncommented —
   `IDE_CP_Core.thy:771` is inside the comment block `:755-772` — of which
   25 sit inside 24 registrations (`IDE_CP_Reasoning1.thy:172-178` is one
   registration holding two, `:174` and `:176`) and 2, `IDE_CP_Core.thy:324,
   :338`, are direct applications inside a reasoner body; none is a run
   site), `wrap'` (2:
   `modifier.ML:13, :14`) and `wrap''` (12 live occurrences:
   `IDE_CP_Core.thy:2291, :2352, :2383, :2389, :2406, :2634`,
   `opr_stack2.ML:165, :216`, `SEM/generic_element_access.ML:134, :137,
   :173`, `PhiSem_Mem_Pointer.thy:1028`; dead in comments:
   `opr_stack2.ML:333`, `SEM/generic_element_access.ML:143, :217`).
   `IDE_CP_Core.thy:2634` wraps a pure conversion (`obligation_intro_Ex_conv`,
   `reasoners.ML:25`, no engine call), not a run, keeps its `wrap''` and is
   not a site; the other 11 wrap a boundary function.  All three adapters
   re-pair the caller's own context (`helpers1.ML:19-21`).
4. Other exported functions that reach the engine:
   `PLPR_Exhaustive.reason_exhaustively` (`exhaustive.ML:4`, body `:25-82`,
   run at `:68`); the attribute `\<phi>reasoned` (`reasoner.ML:1430-1432`);
   the method `\<phi>reason` (`reasoner.ML:1435-1443`).
5. Dead files, not ported (the deletion list is §6.9): `SYS/tools/elimination_rule.ML`
   (never loaded: `PLPR.thy:1374` is a comment; its call of `reason` is
   API-stale); `SYS/tools/unfold_typeof.ML` (never loaded: its only
   `ML_file`, `Spec_Framework.thy:615`, sits inside the comment block
   `:585-616`; its simproc is in any case registered nowhere, `toplevel0.ML:230`
   and `toplevel.ML:273` are comments); `SYS/phi_type_algebra/SE_Trim_Empty.ML`
   (never loaded, `Phi_Type.thy:7489-7540` is a comment block);
   `deriver_framework.ML:2075` `pure_PLPR_reasoner` (no caller);
   `Phi_System/PhiSem_Formalization_Tools'.thy` and
   `PhiSem_Formalization_Tools2.thy` (each declares `theory
   PhiSem_Formalization_Tools`, which under `Phi_System/ROOT` resolves to
   `PhiSem_Formalization_Tools.thy`, and nothing imports them by file name;
   they hold the only uncommented uses of the method `\<phi>reason`).

### 5.2 Boundary functions and what happens to each

| Boundary function | Where | Disposition | Its callers |
| --- | --- | --- | --- |
| `Phi_Reasoner.reason`, `reason1` | `PLPR/reasoner.ML:947-958` | widened | all sites below |
| `Phi_Reasoner.reason_sXXX` | `:965-969` | deleted | none |
| method `\<phi>reason` via `reason_tac` | `:971-976`, `:1435-1443` | type unchanged, body exports | no live caller (§5.1 item 5); today hands the inner context to the Isar state without export (§10.16) |
| attribute `\<phi>reasoned` | `:1430-1432` | type unchanged, `snd` inside | `IDE_CP_Reasoning2.thy:1380, :1498` (declaration-time rule generation, discard) |
| `PLPR_Optimum_Solution.best_among` → `Phi_Apply.try_apply / apply / apply1` | `optimum_solution.ML:127-138`; `application.ML:21-23, 75-107` | widened | §6.1 |
| `Phi_Sys.synthesis` → `Generic_Variable_Access.get_value` | `sys.ML:225-238`; `generic_variable_access2.ML:48-66` | widened | §6.3 |
| `Phi_CoP_Simp.force_invoke / invoke_when_needed` | `CoP_simp_supp.ML:16-27` | widened | `IDE_CP_Core.thy:2575` |
| `Phi_Working_Mode.generic_cast` → `#cast`, `#cast_exception`, `Phi_Sys.cast`; `vcg_by_cast` | `Phi_Working_Mode.ML:124-138, :195-199, :201-208`; `sys.ML:40` | widened | §6.6: `toplevel0.ML:314` (inherits, §10.17); `generic_variable_access2.ML:261, :263` (threaded inside the closure, dropped once at its end, §5.6, §10.21b); `vcg_by_cast` at `Phi_Working_Mode.ML:331, :433, :510` (reached from `toplevel0.ML:334`); `value_properties.ML:39-40` reuses implication's fields |
| `PLPR_Simplifier.simplifier / simplifier_by_ss / simplifier_by_ss' / simplifier_only` | `simplifier.ML:9-17`, run at `:75` | widened | the 17 registrations of §6.7 and `Calculus_of_Programming.thy:104` |
| `IDECP_Induct_Analysis.case_analysis_phityp / case_analysis_system / case_analysis` | `induct_analysis.ML:3, :51-80`, run (`Phi_Apply.apply1`) at `:52` | widened | `induct_analysis.ML:80` |
| the merged `make_zero_value` | `value_properties.ML:11-36`, run at `:17` | merged into one `Proof.state -> thm * Proof.state` | the `initialize_sequent` field registered at `:36` |
| `PLPR_Exhaustive.reason_exhaustively` | `exhaustive.ML:25-82` | type unchanged (`thm option`, §9.4) | only `deriver_framework.ML:2093` (deriver, discard) |
| (guard / obligation solvers and their adapters, `reasoners.ML:405`, `:922`, `:1840`, `:1872`) | — | not runs, not touched (§6.2) | — |

`reason_exhaustively` keeps returning `thm option` (§9.4).  The cast family
IS upgraded to `context_state -> context_state` (§6.6) [author
2026-09-04T08:48 "working_mode 的 cast 系列值得升级成 context_state ->
context_state"]: the `working_mode` record already holds state-shaped
fields (`vcg_before_assembling`, `introduce_existence*`), the cast fields
were the odd ones out, and at `toplevel0.ML:314` the cast's context is read
again by the rest of the block-closing sequence (§10.17).

### 5.3 Callers that inherit

| Caller | Boundary function called | Why the chain reads the context again |
| --- | --- | --- |
| `Phi_System/IDE_CP_Core.thy:2510` | `reason1` | Post_App 100 puts the result into `ReEntry (arg, (ctxt, sequent))` |
| `Phi_System/IDE_CP_Core.thy:2575` | `invoke_when_needed` | Post_App 320, same |
| `SYS/system/generic_variable_access2.ML:158, :178` | `Phi_Apply.apply`, `reason1` | assignment statement returns `(ctxt, sequent')` (`:268`); the `guard_condition_solver'` call at `:181` is unchanged (§6.2) |
| `SYS/system/generic_variable_access.ML:352, :365` | `reason1` | `extract_values` returns `(vals, (ctxt, sequent'))` (`:379`) to the operator stack (`opr_stack2.ML:243, :248, :266, :322, :343, :352`; `:266` `get_operands` is already state-shaped and needs no edit), `toplevel.ML:303`, `generic_variable_access.ML:466`, `SEM/generic_element_access.ML:295-296`; today the run's context is discarded and the original re-paired |
| `SYS/system/modifier.ML:14` | `reason` | modifier on the state (`toplevel.ML:210`); `:13` (`single_RS'`) is not a run and keeps its `wrap'` |
| `SEM/generic_element_access.ML:281, :282` | `reason1`, `Phi_Apply.apply1` | two chained runs of one statement; result exported onto ctxt' (§6.5) |
| `SEM/cf_routine.ML:76` | `reason` | routine modifier returns `(ctxt', ret)` |
| `SYS/additions/local_value.ML:167` | `Phi_Apply.apply` | fast_assign returns the context after `update_val`; the `guard_condition_solver1` call at `:168` is unchanged (§6.2) |
| `SYS/tools/induct_analysis.ML:52` | `Phi_Apply.apply1` | case analysis on the state; the whole chain `case_analysis_phityp` / `case_analysis_system` / `case_analysis` (`:3, :51-76`) becomes `context_state -> context_state` and `:80` stops re-pairing `ctxt` (§12) |
| `SYS/system/toplevel.ML:303` `clean_values` | `extract_values` | the `;` statement boundary (`Begin_of_Statement`, `:337-340`); inherits for free once `extract_values` carries the context |
| the 11 live `wrap''` sites that wrap a boundary function (§5.1 item 3, excluding `IDE_CP_Core.thy:2634`, which keeps its `wrap''`) | `Phi_Apply.*`, `synthesis`, `get_value` | operator stack / language parsers on the state |
| `SYS/system/toplevel0.ML:196, :209` | `reason`, `Phi_Apply.try_apply` | inside `after_qed` of `gen_begin_block` (`:162`), after the nested block was closed (`:163`); the result is installed on the enclosing state (`:218` via `Phi_Envir.map_state_sequent`, `Phi_Envir.ML:167-171`) — re-entry into the enclosing chain |
| `SYS/system/Phi_Working_Mode.ML:539` | `reason` | block initialisation: the caller `toplevel0.ML:121-123` installs whatever context `infer_working_mode_of_sequent` returns; today `:554` returns the incoming `ctxt`, so `:539-554` must bind the run's context and use it at `:547`, `:550`, `:553`, `:554` (§10.15) |
| `SYS/additions/value_properties.ML:17` | `reason` | block initialisation: `make_zero_value'` (`:26-27`) is `Proof.map_context_result`; the two functions are merged into one that returns the run's context (§10.15) |
| `SYS/system/toplevel0.ML:297`, `:314` | `reason1`, `Phi_Sys.cast` | block closing: the context continues to `move_lemmata` (`:302`), `solve_obligation'` (`:326`), `vcg_before_assembling` (`:334`) and `obligation_proof` (`:340`) (§10.17) |
| `SYS/system/toplevel0.ML:363` | `Phi_Apply.apply1` | the terminal method of `gen_finish_proc` returns the context through `qed` to this block's own `after_qed` (`:162`, attached at `:234-235`), whose resulting state re-enters the enclosing chain at `:212-218` (§10.21a, §10.30) |
| `PLPR/simplifier.ML:75` | `reason` | inner run of `PLPR_Simplifier.simplification`; its context becomes the reasoner's result state (§6.7) |
| `PLPR/reasoner.ML:1441` (method `\<phi>reason`) | `reason_tac` → `export_state` | the Isar proof state continues with the returned context (§10.16) |

The inherit / discard classification is complete (every ruling recorded in
§10); §12 is the downstream trace of every row (§10.23).

### 5.4 Callers that discard explicitly (`snd` at the call site, §4.3)

Approved by the author after an independent re-check of every site
(§10.20) [author 2026-09-04T09:32 "这些我之前都看过一遍，基本没问题"].  One
site in this list needs no edit at all: `deriver_framework.ML:2093` calls
`reason_exhaustively`, which is already `context_state -> thm option` and
stays so (§9.4).

Derivers (8): `deriver_framework.ML:1034, :2071, :2093, :2134`;
`function_congruence.ML:67`; `gen_tyops_commute.ML:154`;
`guess_property.ML:83`; `SEM/reasoning/pointer_of.ML:31` (registered at
`PhiSem_Mem_Pointer.thy:939`).  Structural reason, beyond the principle:
every deriver runs inside `Local_Theory.begin_nested … end_nested`
(`typ_def.ML:656-660`), and `end_nested` rebuilds the context from the
stored outer target (`local_theory.ML:167`, `:452-456`), wiping every
Proof_Data / Config change made inside; `derive_properties` already
injects its setup through `Local_Theory.map_contexts` (`typ_def.ML:650`)
for exactly this reason.  Derivers cannot run inside a programming block
(all deriving commands are `thy_defn`, `Phi_Type.thy:3`).  `:2093` has no
single context to return at all (one per exhaustive branch, §9.4).
`gen_tyops_commute.ML:154` and `pointer_of.ML:31` reason on the live
local theory rather than a scratch context, but `end_nested` wipes them
just the same.
Exactly one of these applies `reason` partially, to a context only, and
passes the resulting `thm -> thm option` on: `deriver_framework.ML:1034-1035`
(bound as `val reason = …` and handed at `:1043` to
`Phi_Help.reason_tracing_tyinst`, whose parameter type `thm -> thm option`,
`Phi_Help.ML:46-47`, is unchanged).  Its discard is eta-expanded:
`val reason = fn th => Option.map snd (Phi_Reasoner.reason NONE NONE
(ctxt_mod, th))`.  `guess_property.ML:82-88` is an ordinary discarding
site (`goal |> Phi_Reasoner.reason …` scrutinised by `case … of SOME ret`);
its edit is the pattern `SOME (_, ret)` at `:88`.  The other discarding
sites likewise drop the context where the option is consumed: `snd` /
`Option.map snd` where the result is piped on, a `SOME (_, th)` pattern
where it is scrutinised (`deriver_framework.ML:2071`, `:2134`,
`gen_tyops_commute.ML:154`, `function_congruence.ML:67-68`,
`pointer_of.ML:31` `Option.mapPartial`).

Rule generation and queries (6):
- `PLPR/rule_generation.ML:497`: the instance rule is installed into the
  generic context by `invoke_action` / `note_thms` (`:571-575`); the
  run context is dropped at the exit of `invoke_generation`; inside the
  function the context is threaded (§6.4).
- `PLPR/tools/extracting_pure_facts.ML:72` (D6).  Six live callers:
  `deriver_framework.ML:1760, :2109`, `rule_generation.ML:355`,
  `PLPR.thy:1405` (off the chain); `generic_variable_access.ML:403`
  (`setup_lemmata`, on the chain; could carry trivially, D6 says no) and
  `Phi_Envir.ML:104` (on the chain; cannot carry: the call sits in a
  `Lazy` stored into the very context it would update, `:127-130`).
- `extracting_pure_facts.ML:113` (`\<phi>inhabitance_rule` attribute,
  `Variable.import`ed context exported at `:118`; inside, the context is
  threaded, §6.4).
- `gen_synthesis_rule.ML:29` (`\<phi>synthesis` attribute; rule installed
  by `add_rule`).
- `SYS/system/generic_element_access.ML:38`: runs inside the syntax phase
  `\<phi>-System.GVA`, registered through `Syntax_Phases.term_check`
  (`generic_variable_access.ML:285`; `syntax_phases.ML:951`), whose
  `simple_check` wrapper (`:939-941`) hands back the context it received;
  Pure's `'a check` type does thread a context between phases (`:902`) but
  `check` drops it regardless (`:969`, `#1 (…)`), so nothing escapes to the
  caller.  Also unreachable today: the
  only `Get_Abstract_Element` rule is the `Nil` case
  (`IDE_CP_Core.thy:1980-1982`) and no live syntax produces a non-`Nil`
  index (`generic_variable_access.ML:227-243`, `IDE_CP_Core.thy:2084-2086`).
- `reasoner.ML:1432` (`\<phi>reasoned`): an attribute may return a context
  in principle (`more_thm.ML:675`), but a theory-level `declare` applies it
  on the global leg too (`generic_target.ML:376-378`), where
  `Context.the_theory` (`more_thm.ML:703`) rejects a Proof context; the
  two live uses sit in anonymous `context … begin/end` blocks whose data
  dies at `end` (`IDE_CP_Reasoning2.thy:1315, :1504`).

Dead code, deleted by the migration [author 2026-09-04T09:32 "赞同删除"]:
the authoritative list is §6.9; the two entries found here are
`SE_Trim_Empty.ML` (never loaded: `Phi_Type.thy:7489-7540` is one comment
block containing its `ML_file`, deriver and template-pass registrations;
the file does not even type-check against `deriver_framework_no_hints`) and
`deriver_framework.ML:2075-2082` `pure_PLPR_reasoner` (no caller; signature
`:241`).

Block end: no discarding site remains — `toplevel0.ML:363` inherits
(§10.21a, §10.27, §10.30); `:364` (guard solver) keeps its signature and is
handed the post-run context `ctxt'2` (§6.2); `:334` already passes the
state to `#vcg_before_assembling` (`Phi_Working_Mode.ML:15`, `:66`) — the
drop is inside the three implementations (`:331`, `:433`, `:510`) and
disappears once §6.6 widens `vcg_by_cast` (`:201-208`).
`SYS/system/generic_element_access.ML:38` discards inside the function
(`val (_, ret) = …`): it returns a cterm, so the discard cannot be an
exit-level `snd`.

Nested boundaries: `exhaustive.ML:68` discards (its only caller is a
deriver; §9.4); `memoization.ML:22` discards (§10.18; the mechanism is dead,
§10.22); `simplifier.ML:75` inherits (§6.7).

### 5.5 Sites not classified: `internal_reason` inside a reasoner

`PLPR/nested.ML:25` (`\<r>BEGIN`), `:43` (`\<r>CALL`);
`PLPR/optimum_solution.ML:114`; `Phi_BI/Phi_BI.thy:5101` (source
normalisation used by `ToR_Entry_Point`, `:5597`).  Verified 2026-09-04: each
returns the inner run's `(ctxt', thm')` as the enclosing run's next state.
`Phi_BI.thy:5116` (target normalisation) does the same but has no caller.
`reasoner.ML:1262` (ML-guarded rules) is a fifth such entry, currently
unreached.  Nothing changes for any of them.

### 5.6 Callers inside an assumption export function: `generic_variable_access2.ML:255-267`

`:261` `Phi_Sys.cast` and `:263` `#cast_exception` ARE runs through the
cast family (§6.6), and `:264` is the guard solver; all three run inside the
export function of an `Assumption.add_assms`, i.e. at export time on a
captured context, so their context cannot leave the closure.  With the cast
family returning the context, the closure reads:
```
val (ctxtA, sequentx1) = if Pattern.matches thy (Thm.term_of ret_spec, Y)
                         then (ctxt, sequentx)
                         else Phi_Sys.cast ret_spec (ctxt, sequentx)
val (ctxtB, sequentx2) = #cast_exception Phi_Working_Mode.programming E_spec (ctxtA, sequentx1)
in Phi_Reasoners.guard_condition_solver1 {can_inst=true} ctxtB sequentx2
```
(`:259-261` is one `if … then sequentx else Phi_Sys.cast …`, so the `then`
branch must supply the pair.)  The context is dropped once, at the
closure's end, because `Assumption.export`'s type carries no context
(`assumption.ML:9`).  Accepted as a known limitation (§10.21b).  The same
closure is one of the assumption-frame callbacks that §6.4 teaches to
recognise the state sequent (§10.29).

---

## 6. Cascades and the modification plan

Design rule for every site below: the returned context is the one the run
was started with plus the hooks' transplant (D2).  A site that changes the
context *before* the run to something it does not want back re-exports onto
its own base (§6.5).

### 6.1 Pipeline 1 — `Phi_Apply` (`SYS/system/application.ML`)

Before: `try_apply : thm list -> Proof.context -> thm -> thm option`,
`apply`, `apply1 : thm list -> Proof.context -> thm -> thm`.

After:
```
val try_apply : thm list -> context_state -> context_state option
val apply     : thm list -> context_state -> context_state
val apply1    : thm list -> context_state -> context_state
```
- `try_apply` (`:75-87`): `best_among (ctxt, candidates)` now yields
  `context_state option`; the statistics side effect (`:82-86`) unchanged.
- `apply` (`:89-92`): pass-through.
- `apply1` (`:94-107`): it installs the failure-reason environment on the
  context first (`Phi_Reasoners.setup_failure_reason_environ [] ctxt`,
  `:95`), today by shadowing `ctxt`.  The environment was never exported and
  is not exported now (§10.10): the run is started on the environment
  context, and on success the result is re-based onto the parameter
  context: `val ctxt_run = setup_failure_reason_environ [] ctxt` (no
  shadowing), `SOME (ctxt'', th) => (PLPR_Context_Export.export_context
  ctxt'' ctxt, th)` (§6.5).  The failure branch (`:98-106`) keeps reading
  the environment context: `:101` (`Thm.pretty_thm`), `:103` and,
  load-bearingly, `:104` `Phi_Reasoners.failure_reasons_of'` all take
  `ctxt_run` — with the parameter `ctxt` there the collected failure reasons
  would be lost (`Failure_Reasoners` is a Proof_Data initialised to `NONE`,
  `failure_reason.ML:26-29`; `:95` is the only caller of
  `setup_failure_reason_environ` on the `apply1` path — the module's own
  `report_failure_reason`, `failure_reason.ML:39-42`, used at
  `typ_def.ML:648`, is unrelated).  Only the success-branch
  `export_context` uses the parameter `ctxt`.
- `apply_proc_naive` (`:46-47`) is already `context_state -> context_state`.

Callers (all mechanical):
- the `wrap''` sites that wrap `Phi_Apply.*` (§5.1 item 3): delete
  `Phi_Reasoners.wrap''`, pass the state.
- `SYS/tools/induct_analysis.ML:52`: `Phi_Apply.apply1 [rule] (ctxt, sequent)`.
- `SYS/additions/local_value.ML:167`: §6.4.
- `SYS/system/generic_variable_access2.ML:158`: §6.4.
- `SYS/system/toplevel0.ML:209`: inherits (§5.3); the `Internal_Match_Fail`
  handler returns the returned state `s'` instead of `(ctxt, s')`.
- `SYS/system/toplevel0.ML:363`: inherits through the terminal method
  (§10.21a, §10.27, §10.28, §10.30).
- `SEM/generic_element_access.ML:282`: §6.5.

### 6.2 The guard / obligation solvers are NOT touched

`guard_condition_solver`, `safe_obligation_solver`,
`hammer_obligation_solver` and their adapters (`reasoners.ML:405`, `:922`,
`:1840`, `:1872`), the registrations `PLPR.thy:1980-1992` and
`defer_premise` (`PLPR.thy:1970-1978`) keep their thm-only shape.  None of
them starts a PLPR run (no engine call in `reasoners.ML:1778-1838`), and
none changes the context today; a function needs the context-returning
shape only when it changes the context.  If an application later makes a
solver change the context, widening its signature belongs to that
application's plan.  [author 2026-09-04T08:28 "赞同把 §6.2 整段移出本计划、留给
应用计划 … 建议本计划别碰 guard solver"]

Consequently no solver signature, adapter or registration is touched.  Where
the enclosing code now threads a context, the solver is simply handed the
post-run context instead of the pre-run one: `local_value.ML:168` (via the
shadowing at `:167`), `generic_variable_access2.ML:181` (once the `:178`
pipeline is split, §12.3) and `:264` (`ctxtB`, §5.6), `toplevel0.ML:326`
(`solve_obligation'`, handed the cast's context, §6.4, §10.17) and `:364`
(`ctxt'2`, §10.30).  The dead `safe_obligation_solver'` /
`safe_obligation_solver1` (`:1872-1879`, no caller) are left alone too.

### 6.3 Pipeline 3 — `synthesis` and `get_value`

Before: `Phi_Sys.synthesis : cterm -> Proof.context -> thm -> thm`
(`SYS/system/sys.ML:225-238`); `Generic_Variable_Access.get_value :
string -> element_index_input -> Proof.context -> thm -> thm`
(`generic_variable_access2.ML:11, :48-66`).

After: `synthesis : cterm -> context_state -> context_state`;
`get_value : string -> element_index_input -> context_state -> context_state`.
- `synthesis` body: `reason1` on the state; signature line `sys.ML:20`
  changes with it.  The `THM ("Application Fail", …)` handler in
  `get_value` (`:65-66`) is unchanged (it only formats an error);
  signature line `generic_variable_access2.ML:11` changes.
- `IDE_CP_Core.thy:2383, :2389`: drop `wrap''`.
- `get_value` users `SEM/generic_element_access.ML:134, :137` and
  `IDE_CP_Core.thy:2406`: drop `wrap''` (`:143` is in a comment).

### 6.4 Local sites (one function each)

Internal threading inside functions that discard at their exit [author
2026-09-04T09:34 "赞同 … 能继承就继承肯定是最好的"]:
- `PLPR/rule_generation.ML:441-522` `invoke_generation`: `ctxt'` is bound
  once at `:442-444` and used both inside the `fold_pad` body (`:466`
  `PLPR_Syntax.guardize … (Context.Proof ctxt')`, `:483` `prop RSN' (ctxt',
  i+1, thm'1)`, `:497-498` the run) and after it (`:521-558` error
  messages, `pass_generated_rule … ctxt'`, and the third tuple component
  `ctxt'` handed to the user pass at `:555`).  The context is threaded
  through the fold accumulator, `(i, thm)` becoming `(i, thm, ctxt')`, and
  the body's parameter shadows the name: `fn positioned_prop'' => fn (i,
  thm, ctxt') => …`, so `:466` and `:483` in round k use the context
  threaded through rounds 1..k−1 without any edit; the whole `thm'3`
  expression (`:493-520`) becomes `val (ctxt'', thm'3) = case
  is_reasoning_goal of SOME err_term => (Config.map Phi_Reasoner.trace (fn
  i => i-1) ctxt', thm'2 |> Thm.permute_prems 0 i) |> Phi_Reasoner.reason
  NONE (SOME delt) |> (fn SOME (ctxt'r, th) =>
  (PLPR_Context_Export.export_context ctxt'r ctxt', th) | NONE => …error
  branch unchanged…) |> apsnd (Thm.permute_prems 0 (~i)) | _ => (ctxt',
  thm'2)` (the `permute_prems` at `:516` now acts on the pair's theorem, the
  `_` branch at `:520` pairs `ctxt'`), and `:521` returns the triple `(if
  is_some is_reasoning_goal then i else i + delt, thm'3, ctxt'')`; the
  fold's tail `:523-524` `|> snd |> Phi_Help.beta_eta_contract` becomes
  `|> (fn (_, th, c) => (Phi_Help.beta_eta_contract th, c))`, rebinding
  `val (rule'1, ctxt') = …`, so every later use of `ctxt'` (`:521-558`,
  including `:555`) takes the final threaded context without edits.  The exit of `invoke_generation` still drops it (§5.4), and
  `invoke_action` (`:571`) keeps the command's own `Context.generic`.
  Trap: `:498` starts each run on `Config.map Phi_Reasoner.trace (fn i => i-1)
  ctxt'`; threaded naively the decrement compounds once per antecedent, so
  each run's result is exported onto the context BEFORE the decrement (the
  §6.5 idiom above).  [author 2026-09-04T11:13 "批准"; 2026-09-05T05:18
  "好的，赞同" — uniformly the threaded context, §10.34]
- `PLPR/tools/extracting_pure_facts.ML:100-125` `generate_extraction_rule`:
  `reason1` at `:113` runs on `Config.put is_generating_extraction_rule true
  ctxt` and yields `(ctxt'r, rule)`; `val ctxt' = export_context ctxt'r ctxt`
  strips the flag (§6.5 idiom); the simplification at `:116-117` and the
  `Variable.export` at `:118` use `ctxt'`; the exit still returns only the
  rule.  [author 2026-09-04T11:13 "批准"]
- `SYS/system/toplevel.ML:208-214` `apply_modifier`: the fold threads the
  state but evaluates each modifier with the pre-fold `ctxt`
  (`Attrib.eval_thms ctxt`, `prep_attr ctxt`) and reads the finishing hook
  table from it; after the migration a rule transplanted by modifier n's
  run would be invisible to modifier n+1.  Change: each fold step takes the
  context from the current state, and `Finishing_Modifier_Hooks.invoke`
  reads from the final state's context.  [author 2026-09-04T11:08 "赞同修复
  (a)"]  Not changed, by the author's ruling: the once-computed `post_app`
  closure at `Phi_Semantics/library/generic_element_access.ML:110` (it only
  fetches the Post_App handler table) and the `Drule.infer_instantiate
  ctxt'1` at `:170` (certification only).  [author 2026-09-04T11:08 "(b) 不是
  问题 … (c) 也不是问题"]
- `SYS/system/toplevel0.ML:162-168` `after_qed` of `gen_begin_block`: the
  state after `end_block` (`:163`) gets
  `Proof.map_context (PLPR_Context_Export.export_context ctxt')`, where
  `ctxt'` is the context the terminal method returned (§10.21); the theorem
  list at `:166-167` keeps `Proof_Context.export ctxt' ctxt''`.  Leaving a
  block is thus a two-leg export: the first leg (`:350`, then §10.30's
  `base`) crosses the block's own frames, the second (`:163`, `:167`)
  crosses the frame of the block's declared premises (`:234`, `:159`);
  the block's own result crosses that frame first inside Pure, at
  `local_goal`'s `after_qed'` (`proof.ML:1102`).  After §10.37 both legs'
  frames carry the block-boundary export function below, so a
  transplanted theorem arrives clean, or with a `\<premise>`-tagged
  premise it used as an untagged premise, or is dropped.  The `TERM x` theorems that `:166` exports alongside `th`
  (`Drule.mk_term`) have no hyps and pass through unchanged.
- The block-boundary export function (§10.29, §10.37).  Essence: every
  assumption frame a programming block installs gets ONE export function,
  which recognises the state sequent and treats it as today, and for any
  other theorem looks at whether the theorem's proof used the frame's
  assumption — not used: pass unchanged; used and the assumption is a
  `\<premise>`/`\<condition>` (`Premise _ C`): export as `C ⟹ theorem`,
  tag removed; used and anything else: raise `UNEXPORTABLE`, the hook drops
  it.  Seven frames get it: the five phi frames with a custom export
  function today (below) and the two Pure-installed frames
  (`generic_variable_access2.ML:244`, `toplevel0.ML:234`; §10.37).  The
  list is complete: a repository grep for `Assumption.add_assms` finds,
  besides these seven, only `deriver_framework.ML:1921`, `:2108` (derivers,
  off the chain), the shape-independent `Subgoal_Env.ML:62`, and comments;
  `Proof.internal_goal` at `toplevel0.ML:234` is the only `strict_asm`
  goal on the block path that installs a non-empty assumption frame
  (`Phi_Sys.obligation_proof`, `sys.ML:259`, is the other `strict_asm`
  goal, but both its callers pass no assumptions, so its frame's export
  is the identity).  That grep covers `contrib/phi-system/` only; a
  programming block is an Isar proof state, and an Isar command written
  at block level installs a frame phi does not own: `obtain` does so
  live (`Phi_Examples/Binary_Trees.thy:268` and nine more lines;
  `Pure/Isar/obtain.ML:224` via `proof.ML:665`, export `obtain_export`
  `obtain.ML:70-71`), and `assume` / `presume` / `define` would.  Those
  frames keep Pure's export; what protects a hook's theorems there is
  `export_aux_lemma` (§4.1, §10.38): a theorem mentioning a block-local
  variable never reaches them, and for the rest `obtain_export` performs
  the correct existential elimination, `define`'s export unfolds the
  definition, and `assume` / `presume` add their assumption
  unconditionally (§11.1).  Nothing else about any frame changes:
  - `SYS/system/sys.ML:130-132` → `export_codeblock` (`:53-74`), one
    assumption (the accepted code block); today its first line
    `Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent0)` raises
    `TERM` on anything else.  `export_codeblock` gains a `working_mode`
    parameter.
  - `SYS/system/Phi_Working_Mode.ML:249` → `finish_proc` (`:215-224`), one
    assumption (the initial sequent of an assignment statement's
    procedure: `initialize_sequent_procedure`, `:231-253`, has exactly one
    caller, `generic_variable_access2.ML:248` inside `default_assignment`);
    today the `COMP \<phi>reassemble_proc_final` fails on a non-sequent.
  - `SYS/system/obtain.ML:95-96` → `obtain_export` (`:47`) →
    `eliminate_nusys` / `eliminate` / `eliminate_term` (`:15-46`), one
    assumption (`meta'_term`, the obtained instance), installed by
    `NuObtain.choose` for existential elimination (`IDE_CP_Core.thy:2453`)
    and by `auto_choose` from Post_App 600 (`:2594-2603`, `\<phi>auto_\<exists>fix`
    defaults to true, `obtain.ML:100`); today `eliminate_term` (`:23`) ends
    in `#introduce_existence_in_assembling mode`, which raises `THM
    "Unrecognizable form of sequent."` (`Phi_Working_Mode.ML:143-144`,
    `:193`) on a non-sequent.  Today it fetches the mode inside
    `eliminate_term` (`:18`); after the change it is fetched in `choose`
    and closed over like the others.  [author 2026-09-05T06:15 "AD1 赞同
    (a)"; §10.35]
  - `SYS/system/generic_variable_access2.ML:196-198` (`concact_sequent`,
    zero assumptions) and `:255-267` (§5.6, zero assumptions).
  - `SYS/system/generic_variable_access2.ML:241-244`: the assignment
    statement's declared hypotheses (`LOCAL_VAR v TY`, one per declared
    variable, `PhiSem_Variable.thy:160-161`; extracted at `:192-194` from
    the rule's `⋀vari. LOCAL_VAR vari TY ⟹ proc …` premise and handed to
    `declare_rule`, `variable.ML:61-68`), today `Assumption.presume_export`
    (unconditional `implies_intr`, `assumption.ML:48-49`, `:57-58`).
  - `SYS/system/toplevel0.ML:234`: the premises of the antecedent the block
    is opened on (`prems`, `:159`: branch conditions such as `\<premise>
    addr = NULL` from `branch_\<phi>app`, `PhiSem_CF_Basic.thy:109-113`;
    scope hypotheses such as `LOCAL_VAR vari TY`; a top-level `proc`'s
    `requires` premises), today installed by `Proof.internal_goal … true`
    with Pure's `assume_export` (`proof.ML:1069-1071`, `:1083`).  Pure
    offers no goal API with a custom export (`local_goal` / `generic_goal`
    are not in `PROOF`'s signature, `proof.ML:8-148`; `strict_asm` only
    chooses `assume_export` vs `presume_export`, both unconditional), so
    phi installs the frame itself, on the goal node right after
    `internal_goal`: `:234-237` passes `raw_assumes = []`, and a NEW
    `Proof.map_context` inserted between `:237` and the existing one at
    `:238` calls `Proof_Context.add_assms (block_export mode
    (Drule.implies_intr_list)) (map2 … bindings prems)`.  It runs before
    `:239`'s `Proof_Context.set_mode Proof_Context.mode_default`, for
    parity with today: `internal_goal` certifies the same props under
    `mode_pattern` (`proof.ML:1230-1232`) and the goal node still carries
    that mode at `:237`, whereas `add_assms` certifies in the ambient mode
    (`gen_assms cert_propp`, `proof_context.ML:1371`, `:966`).  (The props
    are schematic-free either way — `Thm.assume` rejects schematics,
    `thm.ML:1259-1264`, and today's `local_goal` already puts the same
    props through it, `proof.ML:1083` — so the placement changes no
    outcome; it merely keeps the certification identical.)  The argument
    is byte-for-byte what `:236` builds today, and
    `Proof_Context.add_assms` (`proof_context.ML:153-155`, `:1354-1370`)
    certifies the props and patterns, installs one frame for the list
    (as `local_goal` does at `proof.ML:1083`), binds the pattern
    term-bindings and notes the facts under the given bindings with their
    attributes (so `premises G [attrs]` and `Premises_Attribute`,
    `:221-224`, work as today).  The frame must sit on the goal node, not
    below it: `Assumption.local_assumptions_of` drops the common prefix
    (`assumption.ML:117-122`), so a frame added before `internal_goal`
    would be on both sides of `after_qed'`'s export (`proof.ML:1102`) and
    discharge nothing there.  One thing `local_goal` did that `add_assms`
    does not, re-done by hand: the `that` fact.  Pure notes it from the
    RAW assumption theorems, before any attribute (`val prems =
    Assumption.local_prems_of ctxt' ctxt`, `proof.ML:1086`, noted at
    `:1089-1091`; attributes applied only afterwards, `:1092-1093`), so
    phi notes `Proof_Context.note_thms "" ((Binding.name Auto_Bind.thatN,
    []), [(Assumption.local_prems_of ctxt_after ctxt_before, [])])` around
    its `add_assms` call, guarded by `not (null prems) ?` exactly as Pure
    guards it (`proof.ML:1089`; an unguarded note would define an empty
    `that` in a premise-free block and shadow the enclosing one:
    `Facts.add_static` skips only an empty binding, `facts.ML:285-287`) —
    NOT `add_assms`' own result, which has already
    been through the bindings' attributes (`proof_context.ML:1366`,
    `:1132-1141`), and phi's premise attributes do rewrite premises
    (`\<phi>premise_attribute [THEN Premise_D] for \<premise> ?x`,
    `IDE_CP_Core.thy:2229-2230`).  Not reproduced, by design: the
    re-binding of the premise patterns' term bindings after
    `\<medium_right_bracket>` (`generic_goal`'s `result_binds`,
    `proof.ML:1027-1028`) — today it lands on a node that `Proof.end_block`
    at `:163` pops at once, so those bindings never reach the context
    after the block; keeping that is the status quo (§9.12).  Differences
    accepted: `add_assms` also runs `auto_bind_facts` on the premises,
    binding `?this` and `...` (`Auto_Bind.dddot_indexname`) to the last
    premise (`proof_context.ML:1363`, `:942`; `auto_bind.ML:59-63`), as
    plain `assume` does; `result_text` loses its `prems ⟹` prefix, which
    only feeds `Proof_Context.augment` and changes nothing (every free of
    `prems` is fixed at `:152-155`); Pure still pushes an empty frame for
    `raw_assumes = []` (`assumption.ML:133-140`), whose export is the
    identity; `block_export` ignores `Assumption.export`'s `is_goal` flag,
    which at this frame selected `implies_intr_protected` for a
    `{goal = true}` export (`assumption.ML:32`, `:48-49`) — safe because
    the only `Proof_Context.export_goal` user in Pure is `refine_goals`
    (`proof.ML:479`), which exports INTO the goal node so this frame lies
    in the dropped common prefix, and phi calls `export_goal` nowhere.
    The goal's own result stays `prems ⟹ goal'`: `on_sequent` is the same
    `Drule.implies_intr_list` on the same cterm list, and it crosses the
    new frame first inside Pure, at `local_goal`'s `after_qed'`
    (`proof.ML:1102`, `burrow export results` `:1109`), then again
    unexported at `toplevel0.ML:167` — twice today as well.  Verified by an
    agent on 2026-09-05 (§9.12).
  The one function, [drafter name] `Phi_Working_Mode.block_export`, placed
  in `Phi_Working_Mode.ML` (loaded at `IDE_CP_Core.thy:246`, before every
  frame; placed above `finish_proc`, `:215`):
  ```
  (* mode: the block's working mode, fetched before Assumption.add_assms and closed over;
     on_sequent: today's export logic of the frame, applied to the theorem the frame
     is meant for (for the two Pure frames: Drule.implies_intr_list asms) *)
  fun block_export (mode : working_mode) on_sequent : Assumption.export = fn _ => fn asms =>
    (fn th =>
       if #domain mode (PLPR_Syntax.dest_tags (Thm.concl_of th)) then on_sequent asms th
       else fold_rev (fn A => fn th =>
              if not (member (op aconv) (Thm.hyps_of th) (Thm.term_of A)) then th
              else case Thm.term_of A
                of Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ _)
                     => Thm.implies_intr A th |> <rewrite the new first premise with Premise_def>
                 | _ => raise PLPR_Context_Export.UNEXPORTABLE th) asms th,
     I)
  ```
  registered as `Assumption.add_assms (block_export mode on_sequent)
  cprops ctxt` (at `:234` through `Proof_Context.add_assms`, below), the
  same at all seven frames.  Every theorem reaching a frame has already
  been through `Raw_Simplifier.norm_hhf_protect inner` (`Assumption.export_`,
  `assumption.ML:153-156`), which may beta-normalise it and instantiate
  nothing but keeps its head constant, so `#domain mode` on the
  tag-stripped conclusion is unaffected.  At `toplevel0.ML:234` the
  theorem today's logic is meant for is not the state sequent but the
  block's own result, whose conclusion is (an instance of) `goal'`
  (`:160`).  `goal'` is the conclusion of the mode's Programming_Deduction
  (the block is opened on `PROP D` of `reason_programming`,
  `IDE_CP_Core.thy:236-242`, after `Phi_Working_Mode.ML:539`, `:552-553`
  and `toplevel0.ML:147-160`): a `PendingConstruction` for the programming
  mode (`IDE_CP_Core.thy:385-393`), a `CurrentConstruction view_shift_mode`
  for view shift (`:362-370`), a `ToA_Construction` for implication
  (`:349-357`), a `Semantic_Zero_Val` for zero_value (`IDE_CP_App2.thy:467-472`)
  — each accepted by `#domain mode` through its construction clause
  (`is_construction_mode` at `Phi_Working_Mode.ML:339-340`, `:408-409`;
  `dest_ToA_Construction` at `:478`; `dest_Zero` at `value_properties.ML:31`),
  `mode` being the ML value inferred for this block at `:121-123`; so
  there is no false negative there and the block close cannot abort on
  it.  False-positive direction at `:234`, recorded and accepted: any hook
  theorem that `#domain mode` accepts (a construction of the block's mode
  or the mode's target shape, e.g. a transformation rule in implication
  mode) is routed to `on_sequent` and receives all the block's premises,
  used or not — exactly what today's Pure frame does to EVERY theorem, so
  never worse than today.
  (rev 7/8's special recogniser for `:234`, a `Pattern.matches` against
  the raw `goal'`, was withdrawn: the sixth review showed it does not
  survive the normalisation and instantiation above, and a false negative
  there would abort the block close with no message, `proof.ML:1102` and
  `:167` having no handler.)  [author 2026-09-05T09:35 "赞同 (d)"; §9.13]
  For a
  zero-assumption frame `asms = []` and a non-sequent theorem passes
  through.  `Premise` is one
  constant with a mode argument (`PLPR.thy:199-207`: the definition
  `:199-200`, `\<premise>` = `Premise default` `:202-203`, `\<condition>` =
  `Premise MODE_GUARD` `:204-205`, `\<obligation>` `:206-207`), so the tag
  test is on the constant, and the tag is removed with `Premise_def`
  (`Premise mode x ≡ x`, `:200`) so the exported theorem is `C ⟹ th`, a
  conditional rule the reasoner can discharge.
  The premise is added only when the theorem's proof used it; Pure's
  default adds it unconditionally.  [author 2026-09-05T07:12 "好的，赞同
  (b)"; T07:23 "如果是 premise tag 的话那就只是普通的前件，是可以导出的，最多最多
  你只能对用到了非 premise tag 的前件的 theorems 去抛 UNEXPLORABLE"; T07:24
  "导出时把 \<premise> tag 消除，注意不只是 \<premise>，还有 \<condition> 这个";
  T07:25 "都确认"]
  `#domain mode` is the registered mode's own test (record field
  `Phi_Working_Mode.ML:56`), per mode: programming (`:339-340`) accepts
  `CurrentConstruction programming_mode` and `PendingConstruction`
  (`is_construction_mode`, `Phi_Syntax.ML:78-81`) plus a procedure triple
  (`dest_procedure`); view_shift (`:408-409`) accepts `CurrentConstruction
  view_shift_mode` plus a view shift; implication (`:478-479`) accepts
  `ToA_Construction` (its own constant, `Phi_Syntax.ML:103-105`; no
  `CurrentConstruction` clause) plus a transformation; the fourth
  registered mode `zero_value` (`value_properties.ML:31`) accepts
  `dest_Zero`.  The target-shape clauses mean a hook theorem of that shape
  would enter the sequent branch and fail loudly there — accepted.  The
  target-shape clause and the use of `Thm.concl_of` are moreover
  LOAD-BEARING at `generic_variable_access2.ML:196-198`: the frames of one
  assignment statement run newest-first (`add_assms` conses,
  `assumption.ML:133-140`; `thm_export` is `fold_rev`, `:35`), so
  `concact_sequent` runs last and receives `finish_proc`'s output — the
  conclusion of `\<phi>reassemble_proc_final` is a `proc` triple, admitted
  by `#domain programming` only through `can Phi_Syntax.dest_procedure`
  (`Phi_Working_Mode.ML:339-340`) — possibly carrying the premises that the
  `presume_export` frame at `:244` added, which only `Thm.concl_of` strips.
  The guard must not be tightened to `Thm.prop_of` or to premise-free
  theorems.  A `#domain` false negative on the state sequent has a
  different face at each kind of frame.  At `sys.ML:130-132`,
  `Phi_Working_Mode.ML:249` and `obtain.ML:96` the sequent's hyps provably
  contain the frame's own assumption (the sequent is built from it:
  `\<phi>accept_proc OF [sequent, codeblk]`, `sys.ML:132`; the `Thm.assume`d
  `init`, `Phi_Working_Mode.ML:246-250`; `meta'` assumed and installed,
  `obtain.ML:92-98`), so a false negative is an `UNEXPORTABLE` raised at an
  export that has no catcher — `toplevel0.ML:350` and §10.30's
  `Proof_Context.export ctxt'1 base` (inside `\<^try>…catch E => raise`)
  catch nothing — i.e. a message-less failure of the block close.  At the
  two zero-assumption frames it is a silent pass-through (the sequent
  skips the frame's transformation, no error).  At
  `generic_variable_access2.ML:244` it is silent too, and harmful: the
  `LOCAL_VAR` hypotheses never enter the sequent's hyps (they only go to
  `declare_rule`, `:245`, and the sequent is assumed fresh at `:248`), so a
  false negative passes the sequent through WITHOUT the `LOCAL_VAR ⟹`
  prefixes that `concact_sequent` (`:196-198`, which runs one frame later)
  needs to compose against `proc`'s `⋀vari. LOCAL_VAR vari TY ⟹ …`
  premise — a mis-composition, not an exception.  At `toplevel0.ML:234`
  it cannot happen (the block result is the mode's target shape, above).
  Hence the obligation, per frame: `#domain mode` must accept every
  theorem today's frame logic is applied to at that frame; `UNEXPORTABLE`
  reaching any export site other than a hook is a bug, never a supported
  outcome (§12.2).
  `PLPR_Syntax.dest_tags` first strips PLPR
  tags, as the `IDECP_simp` fields do (`:358`, `:440`, `:521`).  The mode is
  fetched before `Assumption.add_assms` and closed over: an export function
  receives no context, and at six of the frames the mode is already set
  in the context — they are installed inside an open programming block
  (`toplevel0.ML:250` `Phi_Working_Mode.set mode` runs before the block
  body), and `Phi_Working_Mode.ML:249` cannot name `val programming`
  (`:336`, defined later in the file) directly; at `:234` the context
  has no mode yet and the ML value bound at `:121-123` is used.  The
  term-side export function stays `I`.
  Not changed: `PLPR/Subgoal_Env.ML:62-65` (its check is shape-independent
  and a hook never carries `\<r>GOALn`, §10.29), `PLPR.thy:3186` and
  `Phi_Working_Mode.ML:400`, `:470` (inside comments, §2.3).
  [author 2026-09-04T14:24, T14:30, T14:34; 2026-09-05T04:52 "赞同用
  domain … 建议先把 working mode 取出来，再绑定到回调中"; T04:53; T04:55 "点头"]

- `Phi_System/IDE_CP_Core.thy:2510-2516` (Post_App 100): `reason1 … (ctxt,
  sequent) |> (fn s' => raise Post_App.ReEntry (arg, s'))` — the `ReEntry`
  must carry the returned state, not `(ctxt, sequent)`.
- `SYS/tools/CoP_simp_supp.ML:5-27`: the first argument is today the pair
  `(ctxt, mode)`; the context moves into the state:
  `force_invoke : working_mode -> context_state -> context_state`,
  `invoke_when_needed : working_mode -> context_state -> context_state
  option`; `RS'` (`:17`) and `is_simp_needed` (`:23`) read the state's
  context.  The only caller `IDE_CP_Core.thy:2575-2577` (Post_App 320)
  raises `ReEntry (arg, s')` with the returned state.
- `SYS/system/generic_variable_access2.ML:145-270` default_assignment:
  `:158` `Phi_Apply.apply [rule] (ctxt, sequent)` gives `(ctxt, proc'2)`;
  `:178` `reason1` gives `(ctxt, proc)`; `:181` `guard_condition_solver'`
  is called on that ctxt as today and returns a theorem; the rest of the
  `let` (`:186-268`) already threads `ctxt` by rebinding, so it continues
  from the returned one.
- `SYS/system/generic_variable_access.ML:316-381` extract_values: the inner
  `gen_rule num thm` (`:334-369`, nine result branches: `:335, :338, :340,
  :353, :355, :358, :365, :367, :369`) becomes
  `gen_rule num (ctxt, thm)`, every branch re-pairs the current context,
  the two `reason1` calls (`:352`, `:365`) use `gen_rule`'s own `ctxt`;
  `:371` binds `val (ctxt', rule) = gen_rule num_limit (ctxt, initial)` and
  the return at `:379` becomes `(vals, (ctxt', sequent'))` — today it
  returns the parameter `ctxt`, and leaving that line alone compiles and
  drops everything (§12).
- `SYS/system/modifier.ML:12-19` by_rule: replace `wrap' (reason …)` at
  `:14` with `reason …` on the state; `:13` keeps `wrap'`.
- `SEM/cf_routine.ML:72-78`: the run at `:76` is `Phi_Reasoner.reason`
  (option); delete the `ctxt'` binding at `:72-74` and apply the
  `Process_of_Argument.put` to the run's returned context; returning the
  old `ctxt'` would compile and drop the run's context.
- `SYS/additions/local_value.ML:167-172` fast_assign: `val (ctxt, sequent) =
  Phi_Apply.apply [rule] (ctxt, sequent)` (shadow `ctxt`);
  `guard_condition_solver1 … ctxt sequent` as today; the exit `fold2 …
  update_val … ctxt |> rpair sequent` (`:172-173`) then runs on the
  returned context and is unchanged.
- `SYS/system/Phi_Working_Mode.ML:533-554` infer_working_mode_of_sequent:
  bind `val (ctxt', sequent') = … reason NONE (SOME 1) (ctxt, …)` at `:539`
  and use `ctxt'` at `:547`, `:550`, `:553`, `:554`.
- `SYS/additions/value_properties.ML:11-36`: merge `make_zero_value` and
  `make_zero_value'` into one `Proof.state -> thm * Proof.state` that runs
  `reason` on `(Proof.context_of stat, rule)` and installs the returned
  context with `Proof.map_context_result` (the shape `:26-27` already has;
  `Proof.map_context` alone cannot produce the `thm * Proof.state` the
  `initialize_sequent` field requires, `Phi_Working_Mode.ML:9`, `:61`);
  `:36` registers the merged function.
- `SYS/tools/induct_analysis.ML:3, :51-80`: `case_analysis_phityp`,
  `case_analysis_system` (no run; pairs the incoming context) and
  `case_analysis` become `context_state -> context_state`; `:80` returns
  `case_analysis data (ctxt, sequent)` directly.
- `SYS/system/toplevel0.ML:170-211` gen_sequent: bind the context returned
  by `reason` at `:196`, return it at `:206`; the `Internal_Match_Fail`
  handler (`:208-211`) returns `try_apply`'s state.
- `SYS/system/toplevel0.ML:284-334` gen_finish_proc: `:284-301` is one
  `if Thm.no_prems sequent_pre1 then sequent_pre1 else let … reason1 … end`,
  so the `then` branch at `:286` becomes `(ctxt, sequent_pre1)`; bind
  `(ctxt0, sequent)` from the whole conditional and feed `ctxt0` to
  `move_lemmata` (`:302`);
  the `case spec` branch (`:303-333`) threads the context through
  `Phi_Sys.cast` (`:314`) into `solve_obligation'` (`:326`) and drops the
  `|> pair ctxt'` at `:333`, which re-pairs the pre-cast context.

### 6.5 Sites that change the context before the run and must not get the change back

Idiom: `PLPR_Context_Export.export_context ctxt_after_run ctxt_own_base`.
Sound by hook contract H2; the precondition (inner extends outer) holds at
all four sites: the two below, plus `rule_generation.ML:498` (the trace
decrement) and `extracting_pure_facts.ML:113` (the
`is_generating_extraction_rule` flag), both described in §6.4 and listed
in §12.2.

- `SYS/system/application.ML:95` apply1 (failure-reason environment), §6.1.
- `SEM/generic_element_access.ML:273-282`.  `:273` registers the argument
  values' specification theorems as local reasoner rules (plus the lemmata
  `setup_lemmata` extracts) into `ctxt''`, only so that the run at `:281` can
  find the arguments; the arguments no longer exist in the sequent after
  `:282`, and carrying the registrations forward would clutter the reasoner
  table and can raise "Clash with existing reasoner!" on the next
  construction that reuses a value at the same slot (`reasoner.ML:486-500`).
  That is what `(*not ctxt''!*)` records (introduced in commit 06e6edf1,
  2024-04-11, message "WIP"; rationale reconstructed from the code).
  After the migration the two runs are chained and exported once onto ctxt':
  ```
  val (ctxt'3, rule')   = ... |> (fn rule => Phi_Reasoner.reason1 ... (SOME 1) (ctxt'', rule))
  val (ctxt'4, sequent') = Phi_Apply.apply1 [rule'] (ctxt'3, sequent)
  in (oprs, (PLPR_Context_Export.export_context ctxt'4 ctxt' (*not ctxt''!*), sequent'))
  ```
  The `:273` registrations are owned by no hook and stay behind; hook-owned
  data from both runs reaches ctxt'.  [author 2026-09-04T07:14
  "generic_element_access.ML:282 这里虽然还是返回 ctxt' 但要把 L281 所返回的
  ctxt''' 导出到 ctxt'"]  The pure facts `setup_lemmata` extracts stay
  dropped as today (§10.14).

### 6.6 Pipeline 4 — the cast family of `working_mode`

[author 2026-09-04T08:48]  Before: record fields `cast`, `cast_exception :
cterm -> Proof.context -> thm -> thm` (record type `Phi_Working_Mode.ML:13-14`
and `:64-65`, `val cast` / `cast_exception` `:45-46`);
`generic_cast rule place desired ctxt sequent` (`:124-138`, run at
`:128`); dispatchers `Phi_Working_Mode.cast` / `cast_exception` (`:195-199`)
and the alias `Phi_Sys.cast` (`sys.ML:40`).

After:
```
cast, cast_exception : cterm (*desired*) -> context_state -> context_state
generic_cast : thm -> string -> cterm -> context_state -> context_state
Phi_Working_Mode.cast, Phi_Sys.cast : cterm -> context_state -> context_state
```
- `generic_cast` (`:124-138`): bind `val (ctxt', sequent') = Phi_Reasoner.reason
  NONE NONE (ctxt, sequent RS rule)`; the shape check at `:131` reads
  `sequent'` and the result at `:137` is `(ctxt', sequent')`; `CastFail`
  unchanged.
- The three mode implementations: programming (`cast` `:257-272`,
  `cast_exception` `:274-284`; its `vcg_before_assembling` is separately
  `:286-332` with the `vcg_by_cast` call at `:331`), view_shift (`:421-433`:
  `cast` from `:421`, `cast_exception` `:431`, `vcg_before_assembling`
  `:432-433`), implication (`:487-511`: `cast` `:487-496`, `cast_exception`
  `:497`, `vcg_before_assembling` `:498-511`); `value_properties.ML:39-40`
  reuses implication's and needs no change beyond the type.
- `vcg_by_cast` (`:201-208`, `cterm -> Proof.context -> thm -> thm`) is a
  fourth member of the family and is widened to `cterm -> context_state ->
  context_state`.  Its three uses inside `vcg_before_assembling` (`:331`,
  `:433`, `:510`) are `(ctxt, vcg_by_cast … ctxt sequent)` — state-shaped
  code that re-pairs the pre-cast context — and become
  `vcg_by_cast … (ctxt, sequent)`; without this the cast's context is
  silently dropped at `toplevel0.ML:334`, between `:314` and `:340`
  (§10.17).  [author 2026-09-04T11:13 "8. 赞同"]
- Signature lines that change with the record: `Phi_Working_Mode.ML:45-46`,
  `sys.ML:11-12`; the structure-side record type is at `:64-65`.
- Callers: `toplevel0.ML:314` inherits (the returned context continues into
  `solve_obligation'`, `vcg_before_assembling`, `obligation_proof`; §10.17);
  `generic_variable_access2.ML:261, :263` are inside the assumption export
  function and thread their context on to `:264`, dropped once at the
  closure's end (§5.6, §10.21b); `IDE_CP_Core.thy:2712` is a comment.

### 6.7 Pipeline 5 — `PLPR_Simplifier` (`PLPR/simplifier.ML`)

[author 2026-09-04T09:47]  Before (`:9-17`; `:19-20` are `conjs_to_aseq` /
`aseq_to_conjs`, not widened): `simplifier`, `simplifier_by_ss`,
`simplifier_by_ss'`, `simplifier_only : … -> Proof.context -> thm -> thm Seq.seq`.
After: `… -> context_state -> context_state Seq.seq`.
- `simplification` (`:51-80`): the inner run at `:75`
  (`Phi_Reasoner.reason NONE (SOME 1) ctxt (End_Simplification'' RS' …)`)
  now yields `(ctxt', th)`, which becomes the result state; the
  `End_Simplification` shortcut (`:72-73`, the `single_RS'` branch) and the
  `fallback` (`:78`) pair the incoming context.  `simp_premis` (`:87-95`;
  `:81-85` is a commented-out block) starts no run; it pairs the incoming
  context.
- The 17 `Phi_Reasoners.wrap` occurrences in 16 registrations
  (`IDE_CP_Reasoning1.thy:172-178` holds two, `:174` and `:176`) drop
  `wrap`: `PLPR.thy:2115, :2120,
  :2208`; `IDE_CP_Reasoning1.thy:174, :176, :350, :455`;
  `IDE_CP_Reasoning3.thy:605`; `Spec_Framework.thy:1610, :1616`;
  `Phi_Type.thy:5931`; `Calculus_of_Programming.thy:339, :342`;
  `Phi_BI.thy:4817, :4822, :4827`; `PhSm_Ag_Base.thy:340`
  (`IDE_CP_Core.thy:771` is inside the comment block `:755-772`, not a
  registration).  `Calculus_of_Programming.thy:98-107`
  (`\<phi>programming_simps`) calls `simplifier` directly and re-pairs
  `ctxt` with `Seq.map (pair ctxt)` (`:105`); it passes the state instead.

### 6.8 Already state-shaped infrastructure (propagation stops here)

Post_App handlers (`context_state -> context_state`; the nine `Post_App.add`
sites `IDE_CP_Core.thy:2465` (50), `:2498` (100), `:2523` (200), `:2527`
(300), `:2569` (320), `:2582` (400), `:2584` (500), `:2594` (600), `:2610`
(999)),
the operator stack (`opr_stack2.ML`), the processor
(`processor.ML:132-165`), `Assignment_Hooks` (`generic_variable_access2.ML:272-273`,
`state = context_state`), `Phi_Modifier` (`modifier.ML:3-5`).

### 6.9 What is NOT changed, and the deletion list

- Discarding callers (§5.4): one edit each, dropping the context where the
  option is consumed — `snd` / `Option.map snd` where the result is piped
  on, a `SOME (_, th)` pattern where it is scrutinised (§4.3, §5.4); the one
  partial application (`deriver_framework.ML:1034`) gets the eta-expanded
  `Option.map snd` of §5.4; `deriver_framework.ML:2093` needs no edit
  (`reason_exhaustively` keeps `thm option`, §9.4).
- `reason_exhaustively` (§9.4).
- `Subgoal_Env` (§4.1, §10.29).
- The guard / obligation solvers, their adapters and registrations (§6.2).
- The `internal_reason` sites (§5.5).
- Dead code, deleted (the single authoritative list; §5.1 item 5 and §5.4
  point here; §8 step 1 schedules all five): `reason_sXXX`,
  `internal_reason_s` (`reasoner.ML:124-133`, `:960-969`);
  `SYS/tools/elimination_rule.ML`; `SYS/phi_type_algebra/SE_Trim_Empty.ML`;
  `deriver_framework.ML:2075-2082` `pure_PLPR_reasoner`.
- Left as is: `SYS/tools/unfold_typeof.ML` — safe precisely because the
  file is never compiled (§5.1 item 5), despite its stale
  `Phi_Reasoner.reason` call at `:22`; the dead `safe_obligation_solver'` /
  `safe_obligation_solver1`.

---

## 7. Verification

The author runs every build (`isabelle build` is never run by the drafter).
No test theory enters any ROOT or session [author 2026-09-05T05:03 "所有的
测试都不需要进 ROOT/Session"]; V2 is loaded interactively on top of the
`Phi_Semantics` heap, like `Test/Guard_Race_Smoke.thy` today (§10.33).
- V1. Step 1 of §8 alone must be behaviour-preserving: after step 1 every
  caller passes `(ctxt, thm)` and no hook is registered, so every session
  listed in `ROOTS` that builds today builds unchanged.
- V2. A smoke theory under `Phi_Logic_Programming_Reasoner/Test/`,
  importing the `Phi_Semantics` theory it needs, registers one hook that
  transplants a marker Proof_Data value set by a test reasoner inside a run,
  and checks these cases (they cover the inheriting families of §12.3, not
  every bullet): an assignment statement (`generic_variable_access2.ML:158,
  :178`); an operator-stack expression that extracts values
  (`generic_variable_access.ML:379`); a `;` statement boundary
  (`toplevel.ML:303`); a block closed with a spec annotation
  (`toplevel0.ML:314` → `:326` → `:334`); a nested block closed by
  `\<medium_right_bracket>` — the marker is present in the enclosing block
  (§10.27, §10.30); a modifier chain of two modifiers (`toplevel.ML:208-214`);
  an aggregate construction (`SEM/generic_element_access.ML:273-282`: the
  marker set by either of its two runs arrives, the `:273` local reasoner
  registrations do not); a failing `Phi_Apply.apply1` whose error message
  still lists the collected failure reasons (`application.ML:104` reads
  `ctxt_run`); a deriver — the marker is absent (a discarding caller).  For
  the Isar method `\<phi>reason` (§10.16) the test is positive: a test
  reasoner fixes a variable and sets the marker; afterwards the marker is
  present in the resulting Isar context and the variable the reasoner fixed
  is generalised away in the exported goal state.  A last case exports a
  theorem through a hook across `\<medium_right_bracket>` in a block that
  used existential elimination: one theorem that depends on the block's
  code-block assumption is dropped (`UNEXPORTABLE`), one that does not
  arrives (§10.29, §10.35).  Two more cases for §10.37, one per Pure frame:
  a block opened on a branch condition (`if (…)`), exercising the block's
  own premise frame (`toplevel0.ML:234`, second leg) — a theorem that used
  the `\<premise>` branch condition arrives as `C ⟹ …` with the tag gone,
  one that used neither arrives unchanged; and a variable declared by an
  assignment statement INSIDE the block, exercising the `LOCAL_VAR` frame
  (`generic_variable_access2.ML:244`, first leg) — a theorem that used
  `LOCAL_VAR v TY` is dropped.  A last case checks the user-visible side
  of the `:234` replacement: inside a block with `premises G` the facts
  `G` and `that` exist, `that` is the raw premise (tag still on) and `G`
  carries its attributes' effect; nothing built covers this today (the
  only uses of a block's `that`, `Phi_Test/PhiTest_1.thy:14` and
  `PhiTest_nonbreakable.thy:12`, are in no ROOT).  Two cases for
  `export_aux_lemma` (§10.38): a hook theorem mentioning a variable fixed
  inside the block is absent after `\<medium_right_bracket>`; in a block
  that used Isar `obtain L … where f: …` (as `Phi_Examples/Binary_Trees.thy:268`),
  a theorem proved from `f` whose statement does not mention `L` arrives
  eliminated, and one mentioning `L` is absent.
- V3. After every step: every session in `ROOTS` that builds today still
  builds (`Phi_Test`, `Phi_Examples`, `PhiStd` under `Phi_StdLib/`, and the
  rest).

---

## 8. Implementation order

0. Re-verify every line anchor of §2, §5, §6, §10 and §12.
1. Boundary (§4): `context_export.ML` (`PLPR_Context_Export`, including
   `UNEXPORTABLE` and `export_aux_lemma`), `reason` / `reason1` returning the context,
   `best_among`, the exhaustive handler, and the five deletions of §6.9
   (`reason_sXXX`, `internal_reason_s`, `elimination_rule.ML`,
   `SE_Trim_Empty.ML`, `pure_PLPR_reasoner`).  In the SAME commit every
   caller of `reason` / `reason1` / `best_among` is mechanically re-shaped
   to pass `(ctxt, thm)` — the old curried shape no longer type-checks —
   discarding callers with their final `snd` (§5.4), inheriting callers
   provisionally with `snd` too, so that the step is behaviour-preserving.
   Build (V1).
2. Pipeline 1 (§6.1) and its callers; §6.5 for apply1 and
   `generic_element_access.ML:282`.  Build.
3. Pipeline 3 (§6.3).  Build.
4. Pipeline 4, the cast family (§6.6).  Build.
5. Pipeline 5, `PLPR_Simplifier` (§6.7).  Build.
6. Local sites (§6.4, replacing the provisional `snd`s of step 1 with real
   threading), the method `\<phi>reason` (§10.16), the terminal method of
   `gen_finish_proc` (§10.21a, §10.30), `block_export` and the seven frames
   (§6.4, §10.29, §10.35, §10.37, §9.12).  Build; V2.
Steps 2–5 widen pipelines whose consumers are scheduled later and therefore
insert further provisional discards of their own: step 2 widens `apply1`
while `induct_analysis.ML:52` / `:80` (widened in step 6 with
`case_analysis*`) and `toplevel0.ML:363` (rewritten in step 6, §10.30)
still expect a theorem; step 4 widens `Phi_Sys.cast` while
`toplevel0.ML:314` sits inside the step-6 `gen_finish_proc` rewrite.
Steps 2–6 together replace every provisional discard; the completeness
check after step 6 is the §12.3 checklist walked bullet by bullet (a grep
cannot see a `SOME (_, th)` pattern), plus `grep -n 'snd (Phi_Reasoner\.\|snd (Phi_Apply\.\|snd (Phi_Sys\.cast\|Option.map snd'`
hitting only §5.4 sites.  Each step is one commit on `main`.  Applications
register their hooks in their own plans, after step 6.

---

## 9. Open items and [drafter] decisions for the author

- 9.1 DECIDED: names `PLPR_Context_Export`, `Hooks` (the functor instance),
  `export_context`, `export_state` [author 2026-09-04T07:17, T07:29 "都批准"],
  `export_aux_lemma` [author 2026-09-05T10:46]
  (the wrapper names `hook`, `add_hook`, `hooks` proposed earlier were
  superseded by the T07:30 no-wrapper ruling, §9.6) and `UNEXPORTABLE`
  [author 2026-09-04T14:34 "(1) 赞同"];
  no thm-only wrapper, callers use `snd` [author T07:29]; `reason`/`reason1`
  return the context (§10.6); the plan lives in
  `contrib/phi-system/ai-artifacts/` [author T07:29 "好"].
- 9.2 CLOSED: no solver is touched (§6.2) [author 2026-09-04T08:28].
- 9.3 Closed (§10.5): the HHF normalisation stays as today.
- 9.4 DECIDED: the exhaustive reasoner discards each branch's context (a
  fold of the hooks over branches would be order-dependent, and its only
  caller is a deriver); `reason_exhaustively` keeps returning `thm option`.
  [author 2026-09-04T08:45 "赞同丢弃"]
- 9.5 DECIDED: hook table read from the outer context [author 2026-09-04T07:30].
- 9.6 DECIDED: the hook table is the existing `Hooks` functor with
  priorities, no wrapper [author 2026-09-04T07:30].
- 9.7 DECIDED: the §6.5 idiom at apply1 (§10.10),
  `generic_element_access.ML:282` (§10.9), `rule_generation.ML:498` and
  `extracting_pure_facts.ML:113` (§6.4, author 2026-09-04T11:13).
- 9.8 First review of §5 folded in (rev 2); rev 3 (all rulings, §12) went
  to the second review; rev 4 folded the second review in (§10.29–§10.34)
  and went to the third; rev 5 folded the third in (§10.35–§10.36) and
  went to the fourth, which ruled READY_WITH_EDITS (twelve mechanical
  corrections, no author decision); rev 6 folds them in.
- 9.9 DECIDED: §10.30 (the final form of `end_tac`, verified by an agent
  on 2026-09-05) approved.  [author 2026-09-05T05:30 "A3 批准"]
- 9.11 REJECTED (third review, U4): the proposal to add a contract line
  forbidding export hooks from raising the `Hooks` functor's `Success` /
  `ReEntry` (`Hook.ML:96-107`).  No such line is added; the functor is
  reused as is (§9.6).  [author 2026-09-05T06:21 "U4 驳回"]
- 9.12 [drafter, verified by an agent 2026-09-05 and by the fifth review;
  the author may veto]: the mechanism for the frame at `toplevel0.ML:234` —
  `Proof.internal_goal` with `raw_assumes = []`, then, still under
  `mode_pattern`, `Proof_Context.add_assms (block_export …)` on the goal
  node, `that` re-noted from `Assumption.local_prems_of` only when `prems`
  is non-empty (§6.4).  The
  premise patterns' term bindings are NOT re-bound after the block: today
  they die with the node `Proof.end_block` pops at `:163`, and the plan
  keeps that status quo (the fifth review's AD-1, option (a); rev 7's
  "reproduce them" would have added behaviour).  Also [drafter]: the name
  `Phi_Working_Mode.block_export`.
- 9.13 DECIDED (sixth review, AD-1): the recogniser at the
  `toplevel0.ML:234` frame is `#domain mode`, as at the other six frames,
  with `mode` the ML value of `:121-123`; `block_export mode on_sequent`
  is uniform at all seven frames.  rev 7/8's `Pattern.matches` against the
  raw `goal'` was withdrawn: it does not survive `norm_hhf_protect` and
  instantiation, and a false negative would abort the block close.  Why
  (d): the block result always satisfies `#domain mode` — it is the
  conclusion of the mode's Programming_Deduction, a construction of that
  mode, accepted by the construction clause (§6.4) — so no false negative
  and no abort; the false-positive class (any hook theorem `#domain mode`
  accepts) gets all the block's premises unconditionally — what today's
  Pure frame does to every theorem — so never worse than today; no
  special case.  The
  other options (normalised `goal'` match; the goal node's goal; a
  fallback) were rejected.  [author 2026-09-05T09:35 "赞同 (d)"]
- 9.14 DECIDED (seventh review): option (d) below, implemented as
  `PLPR_Context_Export.export_aux_lemma` (§4.1, §10.38).  [author
  2026-09-05T10:38 "(d) 当然是好的"; T10:46 "可以，但不能叫 export_thm"]
  The finding: an assumption frame phi does not own.  A
  programming block is an Isar proof state, so Isar commands can appear
  at block level; `obtain` does, live and built:
  `Phi_Examples/Binary_Trees.thy:268` `obtain L node R where tree_def[simp]:
  ‹tree = ⟨L, node, R⟩› by hammer_or_aoa \<semicolon>` (and nine more lines
  in that theory; `Phi_Examples/ROOT`, `ROOTS`).  Pure installs its frame
  on the block's node (`Pure/Isar/obtain.ML:224` → `Proof.assm` →
  `proof.ML:665`) with `Obtain.obtain_export` (`obtain.ML:70-71`): for a
  theorem whose proof used the obtained facts it performs the proper
  existential elimination and yields a clean theorem; for a theorem whose
  statement mentions an obtained parameter (`L`, `node`, `R`) it raises
  `ERROR "Result contains obtained parameters"` (`:48-50`); for a
  conclusion that is not an object-logic judgment it raises `ERROR`
  (`:56-57`).  `block_export` cannot be put on it, and H1's catch is
  `UNEXPORTABLE` only, so a hook theorem mentioning an obtained parameter
  would abort the block close with no catcher.  The §6.4 completeness
  claim is a grep over `contrib/phi-system/` and cannot see frames Pure
  commands install from user text; `assume`, `presume`, `define`, `fix`
  are the same class (no live block-level instance found; `assume` /
  `presume` would add their assumption to every crossing theorem
  unconditionally, `define` unfolds its definition).  Options: (a) record
  the abort as an accepted outcome; (b) widen H1's catch to `ERROR` /
  `THM` (hides genuine errors); (c) keep hook theorems away from the block
  interior (a different leg structure); (d) drafter's recommendation: a
  theorem that mentions a variable fixed inside the block does not leave
  the block — the hook drops it before exporting (the check is
  `Variable.is_fixed` on the frees of the theorem against the inner
  context minus the outer), which the author already anticipated
  [author 2026-09-04T09:32 "我们可能得 remove 一些 thms containing the local
  variables"]; with it the `obtain` frame is never asked to export a
  parameter-mentioning theorem, its elimination of fact-dependent
  theorems is exactly right, and §11.1's "generalised by
  `Variable.export`" case disappears (such theorems are useless outside
  the block anyway).  Residue under (d), recorded as known limitations
  (§11.1): a non-judgment conclusion (a meta-equality `≡`, a `TERM`)
  through an `obtain` frame still errors, and a user-written `assume` /
  `presume` still adds its assumption unconditionally.
- 9.10 Review opinions REJECTED by the author or the judge — do not raise
  them again:
  - a hook-free variant of the exhaustive boundary (judge, review 2);
  - the claimed "inconsistency" between hook priorities and H3 (judge);
  - anchor "corrections" for `proof.ML:418-422`,
    `generic_variable_access.ML:403`, `IDE_CP_Reasoning2.thy:1315, :1504`,
    `Phi_Working_Mode.ML:201-208`, `CoP_simp_supp.ML:5-8` (judge: the plan
    is right);
  - A4: an "ownable slots" / per-site-obligation clause to back H2 at the
    §6.5 sites.  [author 2026-09-05T04:58 "这纯粹是钻牛角尖胡扯，明理的用户都知
    道是什么意思的 … 忽略"]  §6.5 stays "sound by H2".
  - A2: a purity clause for hooks (no writes to ref-backed data).  [author
    2026-09-05T04:59, same words]  A hook is a function `inner -> outer ->
    outer'`; what it does with a `ref` is its own business (§10.24).
  - the option of forbidding theorem-carrying hooks at the block boundary
    (A1 option (a)) and the option of relaxing H1 to a hand-written
    discharge (A1 option (b)); the author chose a third route, §10.29.
  - third review, rejected by the judge (the plan is right): rewriting the
    `extract_values` bullet as literal code; the `gen_finish_proc` case-spec
    `NONE => I` branch; narrowing the callback guard to `Thm.no_prems`
    (§6.4 explains why it must stay `Thm.concl_of`); dropping
    `export_codeblock`'s `working_mode` parameter; a `ctxt'` name collision
    in `simplifier.ML:52-55`; `deriver_framework.ML:241` missing from
    §12.4; the `rule_generation.ML` `ctxt'` use ranges; the solver row of
    §5.2; the "41 live" count; the claim that §10.29's "passes through
    unchanged" is false.
  - the option of ruling that theorem-carrying hooks are unsupported across
    a block that used existential elimination (AD1 option (b)); the author
    chose (a), §10.35.
  - weakening H2 to permit accumulating hooks (AD2 option (b)); the author
    chose (a), §10.36.
  - a contract line forbidding export hooks from raising `Hooks.Success` /
    `Hooks.ReEntry` (third review, U4).  [author 2026-09-05T06:21 "U4 驳回"]
  - sixth review, rejected by the judge as hair-splitting: a `⋀`- or
    `⟹`-shaped `Premise` block premise (no live line produces one);
    sentence placement of the §10.29 carve-out; literal ML for the
    `Premise_def` rewrite and for the `add_assms` call; ambiguity about
    which state `:163`'s `ctxt''` is read from; `declare_term` versus
    `augment` (conceded sound); a "third face" for `Premise`-shaped
    frames; and the rest of the anchor drift.
  - fifth review, rejected by the judge: that a target-shaped hook theorem
    failing loudly in `export_codeblock` is a defect (it is the accepted
    class of §6.4); that the zero-assumption frames' pass-through is
    misdescribed; that the premise-pattern binds are "not reachable";
    that the `TERM x` sentence claims equality with today; that the
    `Premise` ruling should be split per abbreviation; that the `:234-237`
    reshaping belongs in §12.2/§12.3; "procedure triple" as an arity
    claim; that the mode is unavailable at `:234`.
  - fourth review, rejected by the judge: a "live fifth `internal_reason`
    site" at `reasoner.ML:1262` (reached only through `guarded_RS`'s
    `guarded` branch, which needs a leading `\<r>Guard` premise none of the
    five live ML-guarded rules has); literal-code rewrites of the
    `generic_cast`, `apply_modifier` and `rule_generation` seed bullets;
    naming `Phi_Working_Mode.programming` instead of `mode1 ctxt` at
    `:249`; a V2 test of the trace-decrement trap (trace is a printing
    level, nothing observable); the wording "callback frame" in §4.1.

---

## 10. Points that need the author's explicit confirmation

Listed 2026-09-04 at the author's request; each names the trap and the
question, and records the author's ruling once given.  As of rev 4 every
item is decided, closed or rejected.

- 10.1 (removed: application-specific; the mechanism is designed
  independently of any application [author 2026-09-04T06:01].)
- 10.2 DECIDED: transplanted data lives for the rest of the programming
  block; the mechanism offers no removal point.  [author 2026-09-04T06:02
  "没错，这就是我期望的！"]  Recorded as D8.
- 10.3 RESOLVED, no decision needed: every planned caller of
  `export_context` / `export_state` passes an `outer` that `inner` extends
  (the boundary sites; §6.5; §10.27, §10.30).  No violation exists in the
  code.  The precondition is stated in the signature comment because Pure
  checks only the assumption side — `assumption.ML:104-106`, `:108-113`,
  `:117-120` raise `Fail "Outer context disagrees on assumption"` when
  `outer` carries assumptions `inner` does not share as a prefix — and not
  the fixes side (`variable.ML:516-530` silently generalises whatever
  `inner` fixed). [drafter]
- 10.4 DECIDED: the hook contract (§4.2 H1-H3) is a specification that each
  hook implementer must satisfy and check themselves; no runtime check is
  built.  [author 2026-09-04T06:04 "这当然只是规约啊。这当然是具体的实现者自
  己要检查的啊 … 就把规约写清除够了"]
- 10.5 DECIDED: the run-boundary export function keeps calling
  `Proof_Context.export`, so the HHF normalisation stays exactly as today.
  [author 2026-09-04T06:07 "好。我认为这甚至不需要跟我讨论。"]  §9.3 closed.
- 10.6 DECIDED: `Phi_Reasoner.reason` / `reason1` return the context
  [author 2026-09-04T06:12 "赞同"]; no thm-only wrapper exists, every
  discarding caller adds `snd` itself [author 2026-09-04T07:29].
- 10.7 DECIDED: the hooks run at the run boundary in `reasoner.ML`,
  uniformly for every entry point; a thm-only wrapper is nothing but the
  state-returning entry with the context dropped.  There is no hook-free
  path.  [author 2026-09-04T06:07 "这个钩子是在 reasoner.ML 的层级上去统一做
  的"]
- 10.8 DECIDED: Config values and `PLPR_Env` effects set inside a run stay
  run-local; a reasoner that needs its data outside the boundary must
  register an export hook for it.  [author 2026-09-04T06:12 "没错。这是
  expected. 各个 reasoner 需要的话必须手动给钩子才能导出边界外"]
- 10.9 DECIDED: `generic_element_access.ML:282` keeps ctxt' as the base and
  exports the context of the chained runs onto it with
  `PLPR_Context_Export.export_context` (§6.5).  [author 2026-09-04T07:14]
- 10.10 CLOSED, nothing to decide: the failure-reason environment was never
  exported and is not exported now.  `apply1` simply uses the context it
  received as the base of `export_context` (§6.1, §6.5); that is an
  implementation detail, not a design point.  [author 2026-09-04T07:41
  "原本就不导出的信息你也不应该导出啊"]
- 10.11 CLOSED, nothing to decide: `hammer_obligation_solver` starts no run
  and changes no context; there is nothing to migrate.  With §6.2 no solver
  is touched by this plan.  [author 2026-09-04T08:28]
- 10.12 DECIDED: exhaustive branch contexts are dropped, only the theorems
  are merged (§9.4).  [author 2026-09-04T08:45]
- 10.13 CLOSED, nothing to decide: the engine snapshots the reasoner table
  at run entry (`reasoner.ML:915`, `:855`), so a rule transplanted by a hook
  is seen by runs started afterwards, not by the remaining steps of the run
  that produced it.  This is existing behaviour, unrelated to the mechanism,
  and stays.  [author 2026-09-04T07:36 "这个行为很好啊 … 为什么要改"]
- 10.14 CLOSED, nothing to change: the pure facts `setup_lemmata` extracts
  at `generic_element_access.ML:273` are dropped with ctxt'' today and stay
  dropped; existing behaviour, not a bug, not touched by this plan.  [author
  2026-09-04T10:05 "原本的行为你为什么要动呢？这不是个 bug 啊"]
- 10.15 DECIDED: both block-initialisation runs inherit.
  `Phi_Working_Mode.ML:539`: `infer_working_mode_of_sequent` returns the
  run's context in its `(mode, (ctxt, sequent''))` result (`:554`, today the
  incoming context; §6.4 binds the run's), which `toplevel0.ML:121-123`
  already installs.  [author 2026-09-04T09:09
  "infer_working_mode_of_sequent 也是明显可以导出 ctxt 的"]
  `value_properties.ML:17`: `make_zero_value` and `make_zero_value'`
  (`:11-27`) are merged into one function of type
  `Proof.state -> thm * Proof.state` that installs the run's context through
  `Proof.map_context_result`.  [author 2026-09-04T09:15 "是的，而且可以合并
  make_zero_value' 和 make_zero_value"]
- 10.16 DECIDED: the Isar method `\<phi>reason` (`reasoner.ML:1441` via
  `reason_tac` `:971-976`) goes through `export_state ctxt' (fst stat)`
  like every other boundary: the theorem is exported to the goal node's
  context `fst stat` — not the method's static `ctxt` parameter (§4.3,
  §12.2) — and the returned context is that context plus hook data; the
  inner fixes and assumptions no longer leave the run.  No live caller in
  the repository.  [author 2026-09-04T09:38 "赞同"]
- 10.17 DECIDED: `toplevel0.ML:297` and the cast at `:314` inherit; the
  context continues to `move_lemmata` (`:302`), `solve_obligation'` (`:326`),
  `vcg_before_assembling` (`:334`) and `Phi_Sys.obligation_proof` (`:340`),
  inside which the user proves the generated obligation.  [author
  2026-09-04T09:15 "19 这里我觉得也是能继承的"]
- 10.18 DECIDED for `simplifier.ML:75`: widen.  `PLPR_Simplifier.simplifier`
  and its variants become `context_state -> context_state Seq.seq` and the
  inner run at `:75` feeds its context into the result (§6.7).  [author
  2026-09-04T09:47 "赞同加宽签名"]
  `memoization.ML:22` DECIDED: discard (`snd`).  Reason: a memoised result
  is a theorem saved as a local rule (`:28-47`); on a cache hit the saved
  rule is applied (`:31-37`) and nothing the original run did to the context
  is replayed, so carrying the context on the first run but not on hits
  would make the two paths behave differently.  The mechanism is dead in
  practice (§10.22).  [author 2026-09-04T09:18 "我建议
  memoization.ML 这里丢弃 ctxt"]
- 10.19 DECIDED: no contract item about cost; each hook decides for itself
  (overwriting is allowed and often fastest).  [author 2026-09-04T07:33]
- 10.20 DECIDED: every discarding site of §5.4 was re-checked
  independently (each traced to its top-level caller) and approved; the
  reasons are recorded in §5.4.  Rule: never drop a context unless it is
  logically right to drop it.  [author 2026-09-04T08:55 "能不丢弃就不要丢弃，
  除非是逻辑上就是应该丢弃"; 2026-09-04T09:32 "基本没问题"]
- 10.23 DONE: five agents followed the context downstream from every
  inheriting site; the consolidated result is §12.  [author 2026-09-04T09:32
  "全面地列出所有这些需要手动加 PLPR_Context_Export 的地方 … 启动一堆 agents 顺着
  这些继承点放下找"]
- 10.21a DECIDED: `toplevel0.ML:363` inherits.  Verified path: the
  terminal method's context is installed on the goal node by
  `apply_method` / `map_goal` (`proof.ML:418-422`, `:332-346`), read back by
  `generic_qed` (`:1049`), and handed to the goal's `after_qed` by
  `local_goal`'s `after_qed'` (`:1111`); for phi that is
  `toplevel0.ML:162`, whose state continues the enclosing block (`:212-218`,
  both branches install the context: `Phi_Envir.map_state_sequent`,
  `Phi_Envir.ML:167-171`, and `Proof.apply` of a `CONTEXT_METHOD`).
  Change: `basic_method` (`:273`, single use at `:351`) is replaced by a
  raw context-tactic `Method.Basic (fn _ => fn _ => fn (goal_ctxt, goal') =>
  …)` (no `Method.CONTEXT_METHOD`, which would prepend `ALLGOALS
  Goal.conjunction_tac`, `method.ML:109-110`; §10.28) whose final form is
  §10.30: the block's data is exported onto `goal_ctxt` first, `Phi_Apply.apply1`
  runs on that base and its returned context `ctxt'2` is the method's
  result; the guard solver at `:364` takes `ctxt'2`; `:162-168` then
  transplants with `export_context` (§6.4).
  The method's context must agree with the goal's ambient context on
  fixes and assumptions (`proof.ML:1101-1105`), which `export_context`
  guarantees.  [author 2026-09-04T09:39 "很好，批准 17"]
- 10.21b DECIDED: option (3) — the one drop at the closure's end of
  `generic_variable_access2.ML:255-267` is accepted as a known limitation;
  option (2) is recorded below as the future restructuring.  [author
  2026-09-04T09:42 "我认为可以接受这里的丢弃"]  Inside the closure the casts
  at `:261` and `:263` thread their context on to `:264`.  It runs when
  `toplevel0.ML:350` exports the block's sequent (`Proof_Context.export
  ctxt ctxt'1`, `Assumption.export` folding the frames: `assumption.ML:35`
  `thm_export`, frame list from `:117-120`); Pure's `export` type carries
  no context (`assumption.ML:9`) and the frames are inaccessible from
  outside, so no functional channel exists through that mechanism; the
  closure also captures the assignment-time `ctxt` (`:258, :261, :263,
  :264`), not the live one.  Options:
  (1) a `ref` written inside the closure and read at `toplevel0.ML:350`
  (stateful, needs a ref registry, racy against any other export crossing
  the frame, breaks replay) — not recommended;
  (2) move the two zero-assumption callback frames (`:198`, `:255-267`)
  out of `Assumption` into a phi-owned exit-hook stack in Proof_Data that
  threads `thm * Proof.context`, and replace `toplevel0.ML:350` by a
  segment-wise export that runs the phi hooks between the genuine
  assumption segments; the same shape exists at the live frames
  `Phi_Working_Mode.ML:249-250`, `sys.ML:130-132`, `Subgoal_Env.ML:62`
  (`Phi_Working_Mode.ML:400`, `:470` and `PLPR.thy:3186` are inside
  comments);
  (3) accept this one drop as a known limitation and record it.
- 10.24 DECIDED: ref-backed Proof_Data — `Unprc_EleIdx`
  (`Single_Thread_Proof_Data_Opt`, `Phi_Help.ML:235-258`,
  `generic_element_access.ML:56`) and the failure-reason collector
  (`failure_reason.ML:26-37`) — already cross run boundaries through the
  shared reference and keep working unchanged after the migration; they are
  expected behaviour and are NOT touched.  §2.3 is corrected accordingly and
  §10.8 holds only for functional Proof_Data.  [author 2026-09-04T11:03
  "这些都不是 bug 都是 expected behaviors 千万别动"]
- 10.25 DECIDED: the dead Memoize mechanism and the unused
  `Agg_Path_Encoders` (`Phi_Semantics/library/generic_element_access.ML:60-63`)
  are left alone for now.  [author 2026-09-04T11:03 "先别动"]
- 10.26 DECIDED: `Phi_Sys.obligation_proof` (`sys.ML:240-262`) is NOT
  changed.  It hands a proof obligation to the user as an Isar goal; an
  interactive obligation proof is not expected to change the outer context
  and runs no solver on the chain, so its `after_qed'` keeps dropping the
  goal's result context as today.  [author 2026-09-04T11:23 "那这个交互式证
  明并不期望会改 the outer context 啊 … 我目前看不到合理理由"]
- 10.27 DECIDED: the data accumulated inside a nested programming block
  crosses `\<medium_right_bracket>` into the enclosing chain.  `end_tac`
  first computes `base = export_context ctxt goal_ctxt` (§10.30), where
  `ctxt` is the block's live context bound at `toplevel0.ML:343` (before
  `exit_programming_environ` and `Proof.end_block`, which pops the block's
  nodes: `proof.ML:886-893`, `stack.ML:42`) and `goal_ctxt` is the
  terminal method's goal context (node G, opened by `:234`); `:162` then
  installs the method's result on the enclosing state.  Precondition holds
  by the stack structure (`:144` pushes two nodes; `:234` opens G; `:244-246`
  `Proof.proof` opens B1 as a copy of G; `:253` `begin_block` pushes B2 and
  B3; every block context descends from G) and is stated in a comment.  The
  same path serves blocks closed by `)` (`opr_stack2.ML:221-224`).  [author
  2026-09-04T11:21 "很好，点头"]
- 10.28 DECIDED: the terminal method of `gen_finish_proc` is written in the
  raw context-tactic shape `Method.Basic (fn _ => fn _ => fn (goal_ctxt,
  goal') => …)` returning `Seq.single (Seq.Result (ctxt_out, thm_out))`,
  not with `Method.CONTEXT_METHOD` (which prepends `ALLGOALS
  Goal.conjunction_tac`, `method.ML:109-110`); the export base is
  `goal_ctxt` — the first component of the `context_state` that
  `apply_method` passes to the method from `find_goal` and writes back
  (`proof.ML:418-422`) and that `after_qed'` exports from (`:1101-1105`) —
  with the block's data exported onto it first (§10.30), not the static
  method context of `Method.evaluate` (`method.ML:537-544`).  Relation to
  today's code: the `ctxt'` that `basic_method` hands to the body is that
  static context, which for a `qed` IS `goal_ctxt` with only `Method`'s
  facts slot set (`proof.ML:426` `refine text (context_of state)` after
  `end_proof`'s `close_block` has made G the top node, `:951`; `Method.evaluate`
  `:537-541` applies `set_facts`, `:347-349`), and no phi code reads that
  slot (repository grep for `Method.get_facts` / `the_facts`: no hit).  So
  today `apply1` at `:363` already runs on G's context, and the only new
  input is the hook data.  [author 2026-09-04T11:29 "赞同你的建议"; verified
  by an agent 2026-09-05, §10.30]
- 10.22 CHECKED: the Memoize mechanism is dead in practice.  The only
  `MEMOIZE` antecedents in the repository are the four rules
  `Phi_System/Phi_Domainoid.thy:447-481` on `Separation_Disj\<^sub>\<psi>`
  goals, and nothing poses such a goal any more (the last producer was
  deleted in commit deab40b2, 2024-01-23; all live entry points stop at
  `Separation_Disj\<^sub>\<phi>`, `Phi_Domainoid.thy:428-438`).  `memoize_safe`
  / `memoize` have no callers.  A latent defect at `memoization.ML:56`
  (`Memoize_D RS th` with `th` premise-free raises "RSN: no unifiers")
  confirms the tagged path never ran.  The `snd` at `:22` is therefore
  mechanical; whether to delete the mechanism is the author's call.
- 10.29 DECIDED (A1): phi's assumption-frame callbacks recognise the state
  sequent and process only it (§6.4).  Essence: the frames at
  `sys.ML:130-132`, `Phi_Working_Mode.ML:249`, `obtain.ML:96` (§10.35),
  `generic_variable_access2.ML:198` and `:255-267` assume every theorem
  exported through them is the state sequent; a hook exporting another
  theorem across `\<medium_right_bracket>` (§10.27) would hit them
  (`export_codeblock` raises `TERM`, `finish_proc` fails at `COMP`,
  `eliminate_term` raises `THM`).  Ruling: each frame fetches the working mode at
  registration and closes over it; a theorem accepted by `#domain mode` is
  the sequent and takes today's path; any other theorem that depends on the
  frame's assumption (`member (op aconv) (Thm.hyps_of th) (Thm.term_of
  assm)`) raises `PLPR_Context_Export.UNEXPORTABLE` — it cannot leave the
  block and the hook drops it (H1); any other theorem passes through
  unchanged; the term-side export stays `I`.  H1 itself is unchanged.
  Obligation that comes with it (§6.4): `#domain mode` must accept the
  state sequent at every frame, because at a frame whose assumption is in
  the sequent's hyps a false negative raises `UNEXPORTABLE` where nothing
  catches it, and at `generic_variable_access2.ML:244` it silently drops
  the `LOCAL_VAR` prefixes the next frame composes with.
  `Subgoal_Env.ML:62-65` is NOT changed: `\<r>GOALn` occurs only in the
  state sequent, a hook never carries it, and if one ever did, today's
  `error` is the right loud signal.  `PLPR.thy:3186`, `Phi_Working_Mode.ML:400`,
  `:470` are inside comments.  Why not the other options: forbidding
  theorem hooks at the boundary kills the main use; a hand-written
  discharge in every hook asks every hook author to remember the frames.
  Consequence for applications (§11.1): a theorem proved inside a block
  from the block's assumptions (e.g. facts read off the state sequent) is
  dropped at the boundary — except that a dependence on a `Premise _ C`
  assumption is exported as the premise `C` (§10.37); one whose proof does
  not use them arrives clean.
  [author 2026-09-04T14:24 "让 phi 自己注册的假设回调识别出并且只去处理 sequent";
  T14:30 "必须 raise some specific exception 令 the export 放弃，抛弃这些 thms
  … 这些 thms 是不能被 export 出来的"; T14:34 "(1) 赞同 … 赞同 … 赞同";
  2026-09-05T04:52 "赞同用 domain … 建议先把 working mode 取出来，再绑定到回调中";
  T04:53 "Subgoal_Env.ML:62 天生就运行良好，不需要做任何修改"; T04:55 "点头"]
- 10.30 DECIDED (A3): the final form of `end_tac` (`toplevel0.ML:351-368`),
  replacing rev 3's
  `export_context ctxt'2 (export_context ctxt goal_ctxt)`, which composed
  two SIBLING inners onto one base (`ctxt'2` extended the bare `goal_ctxt`,
  not the base carrying the block's data, so an overwriting hook would have
  wiped the block's data):
  ```
  val end_tac = Method.Basic (fn _ => fn _ => fn (goal_ctxt, goal') =>
    let val base = PLPR_Context_Export.export_context ctxt goal_ctxt   (* B3 → G, the one cross-block export *)
     in (\<^try>\<open>let
          val sequent' = singleton (Proof_Context.export ctxt'1 base) sequent'1
          val _ = Phi_Reasoner.info_print base 2 (fn _ => … Syntax.pretty_term base … Thm.pretty_thm base …)
          val (ctxt'2, result) = Phi_Apply.apply1 [sequent'] (base, goal')
          val result = Phi_Reasoners.guard_condition_solver1 {can_inst=true} ctxt'2 result
          val _ = PLPR_Statistics.stop_recording_a_semantic_operation ctxt'2
        in Seq.single (Seq.Result (ctxt'2, result)) end
        catch E => raise (@{print} E)\<close>)
        handle THM _ => Seq.empty
    end)
  ```
  `apply1` already re-bases its result onto its parameter (§6.1), so `ctxt'2`
  is at `base`'s level and is returned directly — a further `export_context
  ctxt'2 base` would run the hooks a second time on already-transplanted
  data (`pointer_eq` does not short-cut it), which H2 makes redundant, not
  wrong (§10.36).  `base` is computed outside the `THM` handler so that a
  hook's `THM` is not swallowed into "Failed to finish proof".  `handle THM
  _ => Seq.empty` reproduces what `PRIMITIVE` (`tactical.ML:314`, via
  `PRIMSEQ` `:311`) did for `basic_method`; it must sit
  outside `\<^try>…catch`, whose `E => raise …` re-raises everything.  The
  seven uses of the deleted `ctxt'` (`:353`, `:354`, `:358`, `:360`,
  `:363`, `:364`, `:365`) go to `base` (first four), `base` as `apply1`'s
  context (`:363`) and `ctxt'2` (`:364`, `:365`).  `Proof_Context.export
  ctxt'1 base` keeps `ctxt'1` (node B1, where `sequent'1` was made at
  `:350`) as the source: B1 is a `Stack.push` copy of G plus the working
  mode and the thesis (`:248-252`), same fixes and assumptions, so the
  export is a no-op in effect, exactly as today's `:353`.  Verified by an
  agent on 2026-09-05 (C1–C6: node stack, extension relations, `ctxt'`
  versus `goal_ctxt`, redundancy of the second export, outflow through
  `qed` to `:162`, exception handling and `Seq.Result`), all confirmed.
  [author 2026-09-04T14:16 "你确定你提议的是对的吗？？"; T14:19 "你 run an
  agent 验证一下吧"; 2026-09-05T05:30 "A3 批准"]
- 10.31 REJECTED (A4), see §9.10.  [author 2026-09-05T04:58]
- 10.32 REJECTED (A2), see §9.10.  [author 2026-09-05T04:59]
- 10.33 DECIDED (A5): no test theory enters any ROOT or session; V2 stays a
  standalone theory under `Phi_Logic_Programming_Reasoner/Test/` importing
  what it needs from `Phi_Semantics`, loaded interactively (§7); V3 names
  the `ROOTS` sessions; §5.1 item 2 no longer excludes `Phi_Test/`.  [author
  2026-09-05T05:03 "所有的测试都不需要进 ROOT/Session"]
- 10.34 DECIDED (A6): inside `rule_generation.ML:441-522` every use of the
  context uses the threaded one — `:466` and `:483` in round k the context
  after rounds 1..k−1 (they only certify and read configuration, hook data
  is harmless there), everything after the fold, including the third tuple
  component at `:555`, the final one — implemented by threading the context
  through the `fold_pad` accumulator and shadowing `ctxt'` (§6.4).  [author
  2026-09-05T05:16 "可以统一使用串接后的上下文吗？自然吗？代码好写吗？"; T05:18
  "好的，赞同"]
- 10.35 DECIDED (AD1): the existential-elimination frame
  `Phi_System/library/system/obtain.ML:95-96` (`NuObtain.choose` /
  `auto_choose`) is the fifth live phi-owned assumption frame and gets the
  same shape as the other four (§6.4, §10.29): mode fetched in `choose` and
  closed over; a theorem accepted by `#domain mode` takes today's
  `eliminate_nusys` path; a non-sequent theorem whose hyps contain
  `meta'_term` raises `UNEXPORTABLE`; any other theorem passes through.
  Rev 4 missed it because §2.3 had lumped it together with PLPR's
  commented-out DO_OBTAIN (`PLPR.thy:3119-3193`), a different mechanism.
  [author 2026-09-05T06:15 "AD1 赞同 (a)"]
- 10.36 DECIDED (AD2): hooks must be idempotent; an accumulating hook (one
  that appends inner's content to outer's slot on every export) is outside
  the contract.  H2 is stated in its three-context form (§4.2), which
  covers §6.5, §4.3 and §10.30 alike; §10.30's second export is therefore
  redundant, not harmful.  [author 2026-09-05T06:16 "AD2 (a)"]
- 10.37 DECIDED: the two Pure-installed assumption frames a theorem crosses
  when leaving a block — the assignment statement's `LOCAL_VAR` hypotheses
  (`generic_variable_access2.ML:244`, `presume_export`) and the block's
  declared premises (`toplevel0.ML:234`, `Proof.internal_goal … true`,
  `assume_export`) — get the same hyps-aware export as phi's five frames,
  refined by the tag of the assumption: a theorem that did not use the
  assumption passes unchanged; one that used a `Premise _ C` assumption
  (`\<premise>`, `\<condition>`, `\<obligation>`) is exported as `C ⟹ th`
  with the tag removed (it is an ordinary antecedent the reasoner can
  discharge later); one that used any other assumption (`LOCAL_VAR vari
  TY`, a `requires` premise such as `Semantic_Type U TY`, a meta-level
  hypothesis) raises `UNEXPORTABLE` and is dropped.  The state sequent and
  the block's own result keep today's behaviour.  All seven frames share
  one export function (§6.4).  Rejected on the way: leaving the Pure frames
  as they are and letting applications filter (they add the premise to
  every theorem, used or not, so a clean theorem is polluted and cannot be
  cleaned afterwards); dropping every theorem that used a `\<premise>`
  assumption (wrong: such a premise is exportable).  [author
  2026-09-05T07:12 "好的，赞同 (b)"; T07:23 "如果是 premise tag 的话那就只是普通的
  前件，是可以导出的，最多最多你只能对用到了非 premise tag 的前件的 theorems 去抛
  UNEXPLORABLE"; T07:24 "导出时把 \<premise> tag 消除，注意不只是 \<premise>，还有
  \<condition> 这个"; T07:25 "都确认"]
- 10.38 DECIDED: a theorem that mentions a variable fixed inside the run
  or block does not leave it, and every hook exports its theorems through
  the one function `PLPR_Context_Export.export_aux_lemma inner outer`
  (§4.1), which applies that rule, runs `Proof_Context.export`, and turns
  `UNEXPORTABLE` into `NONE`; H1 is restated on it.  Why in the mechanism
  and not in the application: one place, no hook author has to remember
  either rule.  Why the rule: such a theorem cannot mean anything outside
  the block, and Isar `obtain`'s frame (§9.14), which phi does not own,
  raises `ERROR` on it; with the rule that frame is only ever asked to
  export theorems it handles correctly.  It supersedes §11.1's earlier
  "generalised by `Variable.export`, the application may remove them"
  for block-local variables.  Consequence at run boundaries: the only
  fixes a run adds are `\<r>GOALn` (§2.3), so a theorem mentioning one is
  now dropped instead of tripping `Subgoal_Env.ML:62`'s `error` — the
  `Subgoal_Env` guard stays for the state sequent.  [author
  2026-09-04T09:32 "我们可能得 remove 一些 thms containing the local variables";
  2026-09-05T10:38 "(d) 当然是好的"; T10:46 "可以，但不能叫 export_thm，最多叫
  export_helper_thm/export_aux_lemma 之类"]

---

## 11. Notes for applications (out of scope here, recorded so they are not lost)

- 11.1 A hook that transplants a simpset (the guard simpset application)
  exports every theorem one at a time through `export_aux_lemma` (H1,
  §10.38): `map_filter (PLPR_Context_Export.export_aux_lemma inner outer)`
  is all it writes.  It gets back, for free: theorems mentioning
  block-local variables removed; theorems depending on a block assumption
  removed (`UNEXPORTABLE`, §10.29); a theorem that used a
  `\<premise>`/`\<condition>` assumption as `C ⟹ theorem` with the tag
  removed (§10.37) — a conditional rule; a theorem that used an Isar
  `obtain`'s facts existentially eliminated by Pure (§9.14).  Whether a
  conditional rule is still useful is the application's decision.  Known
  limitations it inherits (§9.14): a theorem whose conclusion is not an
  object-logic judgment (a meta-equality, a `TERM`) aborts the block close
  if the block used Isar `obtain`; a user-written Isar `assume` / `presume`
  in a block prefixes its assumption to every transplanted theorem.  To be
  worked out in that application's plan.  [author 2026-09-04T09:32 "一些 thm 可能依赖于特定
  的 local variables which have no export ways，这意味着我们可能得 remove 一些
  thms containing the local variables"]
- 11.2 Crossing `\<medium_right_bracket>` (§10.27) runs phi's own
  assumption-frame callbacks on every theorem a hook exports there
  (`sys.ML:53-74` via `:130-132`, `Phi_Working_Mode.ML:215-224` via `:249`,
  `obtain.ML:15-47` via `:96`, `generic_variable_access2.ML:196-198`,
  `:255-267`, the `LOCAL_VAR` frame at `generic_variable_access2.ML:244`,
  plus the `Subgoal_Env.ML:62-65` tag guard), then, on the second leg
  (`toplevel0.ML:163`, `:167`; §6.4), the frame of the block's declared
  premises (`toplevel0.ML:234`) alone.  (A frame an Isar command written
  in the block installed — `obtain`, §9.14 — sits on the block's own node
  and is crossed on the FIRST leg, `toplevel0.ML:350` and §10.30's
  `base`.)  After §10.29, §10.37 and
  §10.38: a theorem mentioning a block-local variable is dropped by
  `export_aux_lemma` before any frame sees it; at the seven phi-owned
  frames a theorem that did not use the frame's assumption passes
  unchanged, one that used a `Premise _ C` assumption becomes `C ⟹
  theorem`, one that used any other assumption raises `UNEXPORTABLE` and
  `export_aux_lemma` drops it; an Isar `obtain` frame eliminates the
  obtained facts it was used with.
- 11.3 `post-app-handlers.ML:51-60` `call_of_state_sequent` installs the
  context returned by a whole statement onto the stored `Proof.state` with
  `Proof.map_context (K …)` (`:57`), with no check.  A hook violating H1
  (transplanting a theorem that mentions run-inner Frees without exporting
  it) would go undetected there; this is why H1 is not optional.

---

## 12. Downstream trace: every hand-written call, every silent-drop site (§10.23)

Consolidated from five agents (operator stack / Phi_Apply; block lifecycle
and the cast family; assignment, values and modifiers; Post_App chain and
processor; PLPR internals), each claim re-verified against the working
tree on 2026-09-04.  §8 step 0 re-verifies the anchors.

### 12.1 Implementation rule that prevents most silent drops

At every widened run site the pre-run context binding stays in scope with a
valid name and type, so the old expression that mentions it still
compiles.  Rule: **where the enclosing code already rebinds `ctxt`, shadow it
(`val (ctxt, th) = …`), never introduce a primed name; where shadowing is
impossible (the pre-run name is the function's parameter or a separately
computed value), edit the return expression in the same commit.**  After
each function, grep the remainder of the function for the pre-run name.
Sites that depend on this: `generic_variable_access2.ML:158, :178` (17
later reads of `ctxt`, returns at `:188`, `:268`), `local_value.ML:167`
(`:172`), `generic_variable_access.ML:371-379`, `cf_routine.ML:72-77`,
`toplevel0.ML:196-211`, `:284-302`, `:351-368` (seven uses of `ctxt'`,
§10.30), `Phi_Working_Mode.ML:539-554`, `rule_generation.ML:441-558`
(`ctxt'` shadowed inside the fold and rebound after it, §6.4).

### 12.2 Hand-written `PLPR_Context_Export` calls (the only places)

| file:line | call | base | why |
| --- | --- | --- | --- |
| `PLPR/reasoner.ML:952` `reason` | `export_state ctxt' ctxt sequent'` | the run's start context | the boundary |
| `PLPR/reasoner.ML:971-976` `reason_tac` | `export_state ctxt' (fst stat) sequent'` | the goal node's context | §10.16; not the `ctxt` parameter |
| `PLPR/optimum_solution.ML:137` `best_among` | `export_state ctxt' ctxt th` | the argument context (not the stack-pushed `:93` one) | the boundary; the Stack frame must not escape |
| `PLPR/exhaustive.ML:66` success handler | `snd (export_state ctxt' ctxt sequent)` | the function's `ctxt` (the handler's parameter `ctxt'` shadows `:61-63`) | §9.4, branch context dropped; hooks run once per branch, result unused |
| `SYS/system/application.ML:94-107` `apply1` | `export_context ctxt'' ctxt` | the parameter `ctxt`, before `setup_failure_reason_environ` | §6.5, §10.10 |
| `SEM/generic_element_access.ML:282` | `export_context ctxt'4 ctxt'` | `ctxt'` (not `ctxt''`) | §6.5, §10.9 |
| `PLPR/rule_generation.ML:498` | `export_context ctxt'r ctxt'` after each antecedent's run (`ctxt'` = the fold body's shadowing parameter) | the threaded context before `Config.map trace (i-1)` | §6.4, §10.34; otherwise the decrement compounds |
| `PLPR/tools/extracting_pure_facts.ML:113` | `export_context ctxt'r ctxt` | the import context, before `Config.put is_generating_extraction_rule` | §6.4 |
| `SYS/system/toplevel0.ML:351-368` `end_tac` | `val base = export_context ctxt goal_ctxt`, once, before `apply1`; the method returns `apply1`'s context directly | `goal_ctxt` (node G); `ctxt` bound at `:343` | §10.27, §10.28, §10.30 |
| `SYS/system/toplevel0.ML:163` `after_qed` | `Proof.end_block stat0 |> Proof.map_context (export_context ctxt')` | the state after `end_block` | §6.4; `end_block` restores the saved node wholesale |

No other site calls `export_context` / `export_state`.  Of the seven
frames carrying the block-boundary export function of §6.4, the five with
assumptions (`sys.ML:130-132`, `Phi_Working_Mode.ML:249`, `obtain.ML:96`,
`generic_variable_access2.ML:244`, `toplevel0.ML:234`) can raise
`PLPR_Context_Export.UNEXPORTABLE` and the two zero-assumption frames
(`generic_variable_access2.ML:198`, `:255-267`) pass a non-sequent theorem
through; `export_aux_lemma` (called only by hooks) is the only catcher
(H1) — `UNEXPORTABLE` reaching `toplevel0.ML:350`, `:167`, Pure's own
`proof.ML:1102` (the first crossing of the `:234` frame), §10.30's export
or any other non-hook export site is a bug (§6.4).  Every other change is a signature widening, a `let`
rebinding, or dropping `wrap`/`wrap'`/`wrap''`.

### 12.3 Sites that would still silently drop the context after a naive edit

Each must be edited by hand; most still typecheck with the old expression
left in place and drop the context silently (the `vcg_by_cast` bullet is
the exception: it becomes a compile error).

- `SYS/system/generic_variable_access.ML:379` `in (vals, (ctxt, sequent'))`
  → `(vals, (ctxt', sequent'))`.  The funnel for the whole operator stack
  (`opr_stack2.ML:243, :248, :266, :322, :343, :352`), `toplevel.ML:303`,
  `generic_variable_access.ML:466`, `SEM/generic_element_access.ML:295-296`.
- `Phi_System/IDE_CP_Core.thy:2515-2516` (Post_App 100) and `:2576`
  (Post_App 320): `ReEntry (arg, (ctxt, sequent))` → `ReEntry (arg, s')`.
- `SYS/system/application.ML:101`, `:103`, `:104` (the failure branch of
  `apply1`): keep reading the environment context `ctxt_run`, not the
  parameter `ctxt` (§6.1) — with the parameter the collected failure
  reasons vanish silently (§10.24).
- `SYS/system/generic_variable_access2.ML:158`, `:177-185`: shadow `ctxt`;
  split the `reason1 |> guard_condition_solver' |> RS conjunct1` pipeline
  so the pair from `reason1` is bound first.
- `SYS/system/generic_variable_access2.ML:259-264` inside the export
  closure: the `if … then sequentx else Phi_Sys.cast …` at `:259-261`
  becomes `val (ctxtA, sequentx1) = if … then (ctxt, sequentx) else
  Phi_Sys.cast ret_spec (ctxt, sequentx)`; `:262-263` `#cast_exception …
  (ctxtA, sequentx1)` gives `(ctxtB, sequentx2)`; the guard solver at
  `:264` takes `ctxtB`, not the captured `ctxt` (§5.6).
- `SYS/additions/local_value.ML:167` (shadow; `:172` depends on it).
- `deriver_framework.ML:1034-1035`: a partial application of `reason` to a
  context; the discard is the eta-expanded `Option.map snd` of §5.4, not a
  bare `snd`.  `guess_property.ML:88`: pattern `SOME (_, ret)`.
- `SEM/cf_routine.ML:77` `(ctxt', ret)` → apply the `put` to the run's
  context.
- `SEM/generic_element_access.ML:281-282`: bind both runs' contexts (today
  `:281`'s result context has no name at all) before the §6.5 export.
- `SYS/tools/induct_analysis.ML:80` `(oprs, (ctxt, case_analysis …))` →
  `(oprs, case_analysis data (ctxt, sequent))` (with the chain widened).
- `SYS/system/toplevel0.ML:206` `(ctxt, sequent'4)` and `:209-211`
  `SOME s' => (ctxt, s')`.
- `SYS/system/toplevel0.ML:284-301` (`reason1`, then `:302` reuses `ctxt`)
  and `:333` `|> pair ctxt'` (re-pairs the pre-cast context over the
  cast's; `solve_obligation'` itself returns only a theorem,
  `Phi_Envir.ML:45-46`).
- `SYS/system/Phi_Working_Mode.ML:331`, `:433`, `:510`
  `(ctxt, vcg_by_cast … ctxt sequent)` → `vcg_by_cast … (ctxt, sequent)`;
  `:545-554` reuse `ctxt` after the run at `:539`.
- `SYS/additions/value_properties.ML:27` `(…, c)` (the merge removes it).
- `SYS/system/toplevel0.ML:273` `basic_method`: `CONTEXT_TACTIC` is
  `Seq.map (Seq.Result o pair ctxt)` (`context_tactic.ML:36-39`) — the
  canonical drop; and `PRIMITIVE` (`tactical.ML:314`, via `PRIMSEQ` `:311`)
  turns a `THM` into `Seq.empty`, which the replacement writes out by hand;
  replaced per §10.28, §10.30.
- `SYS/system/toplevel0.ML:351-368` `end_tac`: deleting `basic_method`
  deletes the binding `ctxt'`; its seven uses `:353`, `:354`, `:358`,
  `:360`, `:363`, `:364`, `:365` are redirected as §10.30 lists.  Both
  today's `ctxt'` and the new `goal_ctxt` are node G's context
  (`proof.ML:418-421`, `:426`, `:951`; `method.ML:537-541`), so the
  redirection is behaviour-preserving apart from the hook data.
- `PLPR/rule_generation.ML:521-558`, in particular `:554-555` (`ctxt'`
  twice, the second the tuple component handed to the user pass): no edit
  — the rebinding `val (rule'1, ctxt') = …` after the fold makes them read
  the final threaded context (§6.4, §10.34); the fold's tail `:523-524`
  `|> snd |> Phi_Help.beta_eta_contract` is what becomes `|> (fn (_, th, c)
  => (Phi_Help.beta_eta_contract th, c))`.
- `Phi_System/Calculus_of_Programming.thy:105` `Seq.map (pair ctxt)` after
  `PLPR_Simplifier.simplifier` → pass the state (§6.7).
- `PLPR/simplifier.ML:72-78`: only the run branch (`:75`) carries the run's
  context; the `single_RS'` shortcut and the fallback pair the incoming
  `ctxt` (correct — no run there).
- `SYS/system/generic_element_access.ML:38`: `val (_, ret) = …` inside the
  function (returns a cterm).
- `PLPR/memoization.ML:22-24` is the `reason` call; the pattern to edit is
  `of SOME ret' =>` at `:25` → `SOME (_, ret')` (§10.18);
  `PLPR/reasoner.ML:1432` `snd (reason1 …)`;
  `PLPR/tools/extracting_pure_facts.ML:71-73` `Option.map (fn (_, th) => …)`
  (D6).

### 12.4 Cascading signature changes (complete list)

- `PLPR/reasoner.ML:117-123` (`reason`, `reason1`); delete `:124-133`
  (`internal_reason_s`, `reason_sXXX`) and `:960-969`.
- `PLPR/optimum_solution.ML:9` (`best_among`).
- `PLPR/simplifier.ML:9-17` (four functions); 17 registrations and
  `Calculus_of_Programming.thy:98-107` (§6.7).
- `SYS/system/application.ML:21-23` (§6.1).
- `SYS/system/sys.ML:11-12` (`cast`, `cast_exception`), `:20` (`synthesis`),
  `:40-41`.
- `SYS/system/generic_variable_access2.ML:11` (`get_value`).
- `SYS/system/Phi_Working_Mode.ML:13-14`, `:45-46`, `:64-65` (record and
  signature), `:124-138` (`generic_cast`), `:195-199` (dispatchers),
  `:201-208` (`vcg_by_cast`), `:257-284`, `:421-433`, `:487-510` (three
  modes; `cast_exception = K (K cannot_cast_exception)` becomes
  `K (cannot_cast_exception o snd)`).
- `SYS/tools/CoP_simp_supp.ML:5-8`, `:16-27` (§6.4; the `(ctxt, mode)` pair
  loses its context).
- `SYS/tools/induct_analysis.ML:3`, `:51-80` (three functions).
- `SYS/additions/value_properties.ML:11-36` (merge).
- `SYS/system/toplevel.ML:208-214` (`apply_modifier` fold, §6.4).
- New `Phi_Working_Mode.block_export` (§6.4).  `SYS/system/sys.ML:53`
  `export_codeblock` gains a `working_mode` parameter (call at `:131`); the
  frame registrations at `:130-132`, `Phi_Working_Mode.ML:249`,
  `obtain.ML:96` (`eliminate_term` no longer fetches the mode itself,
  `:18`), `generic_variable_access2.ML:198`, `:244` (`presume_export`
  replaced), `:255-267`, and `toplevel0.ML:234` (§9.12) switch to
  `block_export` per §6.4 (§10.29, §10.35, §10.37) with no other signature
  change.
- Signature unchanged, body changes (see §6.4 / §12.3): `extract_values`
  (`gen_rule`, the `:379` return), `by_rule` (`modifier.ML:14`),
  `assignment*` / `default_assignment` (the `generic_variable_access2.ML:158`,
  `:178` rebindings), `push_values`, `register_value_spec_thms*` (their
  callers change, not they), `Phi_CP_IDE.Post_App` handlers 100 and 320
  (`ReEntry`).  `gen_default_process'` (`generic_variable_access.ML:464-503`)
  needs no change: `:466` already binds `extract_values`' context and
  `:499-503` returns it.
- Untouched: `setup_lemmata`, `Assignment_Hooks`, `wrap_to_attribute`,
  `apply_wrapped_attribute`, `gen_access`, `rw_access`, `gen_constructor`,
  the Post_App handlers 50, 200, 300, 400, 500, 600, 999,
  `Phi_Envir.map_state_sequent` / `set_state_sequent` /
  `enter_programming_environ'`, `call_of_state_sequent`,
  `Phi_Sys.obligation_proof` (§10.26), `toplevel0.ML:121-123`, `:212-218`,
  `:253-255`, `toplevel.ML:271-284`, `:300-304`, the guard / obligation
  solvers (§6.2), `led_future_proof` (`toplevel0.ML:392-402`; its
  `CONTEXT_TACTIC` re-pair is harmless while solvers are thm-only),
  `Subgoal_Env.ML:62-65` (§10.29).
- Not in any ROOT, no build impact, prose becomes stale:
  `Phi_Test/Instructions_to_make_a_conventional_VCG.thy:33-35, :80-90`.

### 12.5 Recorded, not changed

- Permanent holes on the chain (no context output in the API):
  Post_App 300 (`IDE_CP_Core.thy:2559-2566`, `Simplifier.rewrite` — a run
  started inside a simproc cannot return a context; likewise the
  `IDECP_simp` field of `working_mode`); `Phi_Envir.ML:128-130` (the `Lazy`
  is stored into the context it would update, and captures `ctxt'` at
  creation, so `reason_programming_implication'` later runs in a frozen
  context); the syntax-phase site `generic_element_access.ML:38` (§5.4);
  the assumption export closures (§5.6, §10.21b; the sibling at
  `generic_variable_access2.ML:196-198` has the same shape) — a hole for
  the CONTEXT only; on the theorem side these closures are the callbacks
  §6.4 teaches to recognise the state sequent (§10.29).
- Values computed once and reused across a run: `processor.ML:153-156`
  (`mode`, `one_step` for a whole line), `:215` (`Post_App.invoke` from the
  pre-`Begin_of_Line` context), `opr_stack2.ML:153` and its uses (`:241,
  :277, :302, :342, :351`), `mode` at `opr_stack2.ML:211, :275, :300, :310,
  :339, :348`, `SEM/generic_element_access.ML:110`, `:170` — they fetch
  handler tables, modes or certificates only; not problems [author
  2026-09-04T11:08].
- `auto_level` is written into the live chain context
  (`processor.ML:412-413`, `IDE_CP_Core.thy:2249-2252`) and undone by
  `Config.restore Phi_Reasoner.auto_level` (`processor.ML:225-226`,
  `toplevel.ML:96-98`), which overwrites one slot and therefore keeps hook
  data; do not convert these into `export_context` calls.
- `modifier.ML:26-31` `apply_wrapped_attribute`: an attribute returning
  `NONE` for the context means "no change" by Isabelle's convention, so
  `:30` re-pairing `ctxt` is correct; phi's own modifiers always return
  `SOME (Context.Proof c')`.
- `opr_stack2.ML:221-224` closes an embedded `( … )` block through
  `end_block_auto_proof_cmd → gen_finish_proc → after_qed (toplevel0.ML:162)`;
  covered by §10.27.  The contexts captured before that line (`fst s0` at
  `:210, :211, :241`) are ancestors of the state after it; any future
  `export_context` there must use the post-block state as `inner`.
- Ref-backed Proof_Data (§10.24).
