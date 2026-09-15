# Judge's report — the Quicksort regression fix (2026-09-15)

**Verdict: MET_ON_CONDITION.**

The ML is right. All seven of §39's rulings are implemented exactly, no reachable
input gets a wrong verdict or a crash, and the shape carries no dirty hack. What
fails is criterion (c): the plan and the code do not agree. §1's glossary entry
for the very object this change is about still describes the pre-fix pipeline,
five statements in §7 do the same (two of them now the exact inverse of the
code), three comments the patch itself wrote state a universal the patch breaks,
the `\<phi>guard_P_auto` method's user-visible description is now false about its
own bound, four anchors point at nothing, and §39 ruling 1's terminology sentence
contradicts ruling 2. One new error path has no probe, in a suite whose header
claims it probes them all. Every one of these is a fix the drafter can apply and
re-submit.

One question is genuinely open and only the author can close it (MD1 below): step
6 re-simplifies the state step 1½ produced, so a `Proved` entry written on the
judge path is not guaranteed to reproduce on a later fresh call. It is unreachable
today — `judge` is `NONE` and only the two smoke theories install one — but it
rubs against the reason the author accepted `Provable` carrying lemmas alone.

---

## Method

I re-verified every decisive claim myself against the working tree, HEAD, the
Isabelle 2025-2 sources and plan rev 28, rather than trusting either round. I ran
no Isabelle process, started no session and changed nothing (read-only review).

---

## 1. The acceptance criteria, one by one

### (a) The code implements plan rev 28 §39's rulings 1–7 exactly — **MET**

| Ruling | Author's words (verbatim) | Code | Verdict |
|---|---|---|---|
| 1. P-auto no longer simplifies | "我们现在可以按你推荐的，取消 P-auto 中的重复 simp" | `p_auto_tac` (reasoners.ML:1080-1084) has no opening `asm_full_simp`; the old `p_auto_search_tac` is deleted | ✔ |
| 2. `guard_simp_tac` on `ctxt_g`, again on `ctxt_g'`, output shared | "显然，simpcut 得用 enhance_for_guard(guard_ctxt + delta) 但这样的话，注意 judge 是会修改 delta 的，于是在修改后我们必须重新跑 simpcut 对吗？" (yes); "你考虑过别的 refuter 吗？R-conv, R-nitpick 吗？？" | :1455 on `ctxt_g`; :1487 on `ctxt_g'`; `goals` (:1458) feeds R-conv (:1521), R-nitpick (:1522), the warnings and `n_goals` | ✔ |
| 3. The factory stays generic, pass-free | "现在的 gen_guard_condition_solver is a generation. The parameter `solve` can be anything. So `gen_guard_condition_solver` doesn't assume the presence of the delta, the entry records" | :1580-1598 — `quick_cut`, `pre`, case split, digest, `Method.insert_tac`, then `solve`; no simplification anywhere | ✔ |
| 4. `is_F` deleted | "建议直接删除 is_F 分支" | `is_F`, `is_false`, `is_guard_mode` gone; a repo-wide grep over `*.ML`/`*.thy` finds no survivor | ✔ |
| 5. `p_auto_tac` | "p_auto_body 这个名字很难听"; "批准 p_auto_tac" | :1080, exported at :118 | ✔ |
| 6. No pass before `solve_obligation_now`'s `fastforce` | "你都用 fastforce 了为什么还要用 guard_simp_tac？" | PLPR.thy:1986-1989 — `try_prove_or_give_up NONE (ALLGOALS fast_force_tac)` in `Guard_Simp_SS.enhance ctxt`, no `guard_simp_tac` | ✔ |
| 7. 60 s of thread CPU | "赞同" | `cpu_bounded (Time.fromSeconds 60)` at :1069 | ✔ |

Two consequences of ruling 6 worth stating, because §7 has them wrong (D1): the
obligation instance receives `Guard_Simp_SS.enhance ctxt`, **not**
`enhance_for_guard`, and only `enhance_with_lemmas` (guard_cache.ML:191) installs
the lemma list — so that instance has stopped being a consumer of the lemma
budget altogether. §39 ruling 6 says exactly this ("the one thing that ends is
the entry lemmas' incidental presence in that instance's simplification"); §7
still says the opposite.

### (b) No reachable input gets a wrong verdict or a crash — **MET**

`prove_or_refute`'s restructuring is sound. The `SOME (th, _)` binding at :1457
shadows the unsimplified state, so nothing downstream can reach the stale one by
accident; `goals` is taken after the pass; `p_auto`'s type change (now taking the
state explicitly) is matched at both call sites (:1516 with `th`, :1490 with
`th'`); the `let`/`case`/`let` nesting is well formed and the `end` at :1556
closes the outer binder whose `in` is the visible :1455. On a timeout
`guard_simp_tac` returns `SOME (th, Seq.empty)` with the state unchanged, so a
timeout can never read as a refutation — the documented and correct choice.

`judge` is `Unsynchronized.ref NONE` (:1336). A grep over the repository finds
exactly two installers, both tests: `Test/Guard_Export_Smoke.thy:89` and
`Test/Guard_Decision_Smoke.thy:123`. So step 6 has no production input today.
(Several round-one defenders wrote "no reachable input" for step 6; that is right
about production but wrong about the suites, which do exercise it.)

### (c) The plan and the code agree — **NOT MET**

This is the condition. See D1, D2, D5, D6, D7, D8, D9, D12.

The two inversions are the serious ones, because a reader who trusts them
reconstructs the bug that was just fixed:

- **§1:159-161** — "case split, the aux-fact insertion and the \"G.simpcut\" pass
  have already acted on it", of the state `prove_or_refute` receives. The factory
  hands it over unsimplified.
- **§7:1226-1229** — "The deleting call's own \"G.simpcut\" pass still pays a
  lemma that rewrites the guard term itself: it runs before `prove_or_refute`, on
  the list before the delta (measured 2026-09-13 …)". It runs inside
  `prove_or_refute`, on the list *after* the delta.

Both are misses, not decisions. The rev-28 plan patch's hunk
`@@ -155,51 +161,77 @@` rewrote the entry immediately below §1's stale sentence
and carried its tail as context; hunk `@@ -1163,10 +1236,11 @@` edited the tail
of the very §7 bullet that contains the inverted sentence, updating only the
clock sentence at :1240-1242. The corresponding comment in
`Test/Guard_Decision_Smoke.thy:495-497` **was** correctly reworded, which is what
makes the plan's omission visible.

### (d) The shape is elegant — **MET, with one reservation**

No dirty hack, no duplicated logic. The nested `let`/`case` is what §39's code
plan prescribes character for character, it follows this file's own
chained-tail-`let` idiom (compare `oblg_template` at :378/:384/:410/:420,
untouched by the patch), and its shadowing is precisely the shape that makes the
design's invariant — the step-1½ output is the goal state of the rest of the
call — impossible to violate downstream. Keeping the decision block eager, rather
than deferring it under `Seq.maps`, is also the better shape: it keeps one call =
one decision = one store write, inside the `Timing.start ()` bracket.

The reservation is D3. Moving the pass out of the factory converted a structural
guarantee into a convention that each solving function must honour — and the one
comment that would state that convention states it falsely, at the exported
signature a maintainer reads first. By this project's own standard ("a shape that
makes an invariant impossible to violate beats one that asks people to remember
it"), when we are forced to rely on remembering, the reminder must at least be
true.

### (e) The verification recorded in the context document is credible — **MET**

It is specific and falsifiable: `PLPR.thy` clean with exactly the three named
pre-existing ML warnings (`th`/`ctxt` at :356, `dest_all` at :1005); the smoke
theory clean with every probe unchanged and only three comments reworded;
`Quicksort.thy` clean with the three genuinely unprovable guards still undecided,
no "probably loops" warning, the AoA record live (222 records, no tombstone); and
— decisively — the same run still failing under the 5 s bound, which is what
settles that the bound, not the restructuring, was the remaining cause. The
restore of the tombstoned record carries the author's approval ("你现在就可以做",
plan:3621-3622), and the temporary `AoA_driver = "test"` was reverted. I could
not re-run any of it (read-only, no Isabelle), so I record this as credible on its
face rather than as independently confirmed. One gap worth noting only because
D10 depends on it: "every probe passes unchanged" covers the judge-path probes,
but nothing in the record says the new `:1489` error was exercised — and it
cannot have been, since no probe reaches it.

---

## 2. Must discuss with the author

### MD1 — step 6's starting state, and whether the entry it writes reproduces

Step 6 rebuilds the *context* from scratch but not the *goal state*.
`apply_delta deleted' replayed'` (:1485) folds the judge's delta onto `ctxt`/`ctxt0`
— the lists of the moment before step 1, exactly as its own comment demands
("step 1 and step 6 both start from these, never from each other's result",
:1424-1427) — while :1487 re-simplifies `th`, the state step 1½ produced under the
OLD delta. Simplification is not invertible, so a rewrite made by a lemma the
judge's answer drops stays in the goal.

The consequence that survives scrutiny is narrow and was **not** what round one
filed: `p_auto ctxt_g' th'` can succeed on the strength of such a rewrite, and
:1492 then writes `{delta', Proved}` — an entry a later fresh call, which
simplifies the raw state under `delta'` alone, need not reproduce. That call
fails P-auto, takes the `_ =>` arm at :1521-1528, and pays R-conv, R-nitpick and a
fresh judge consultation, every run.

This asymmetry is new. At HEAD the judge's `p_auto ctxt_g'` closed over the
factory-simplified, delta-free `th`, and `p_auto_search_tac`'s own opening
`asm_full_simp` then ran in `ctxt_g'` — the identical chain a later run performs.
And it rubs against the reason the author accepted `Provable` carrying lemmas
alone [author 2026-09-08 06:14 "赞同"], recorded at plan:507-510: *"no `proof`,
no returned state — P-auto proves the guard with the lemmas, on the spot, so the
recording run and every later run behave alike."*

**What round one got wrong here, and must not be put to the author as if open:**
six findings claimed the judge is shown a state it cannot reproduce and that the
errors at :1489 and :1495 blame an innocent judge. They do not. `consult`
(:1474-1476) passes `thm = th` — the same step-1½ state — together with `delta`
beside `ctxt`, and the judge's contract is stated against the state it is handed
("the lemmas together must make P-auto prove the guard", plan:546). A judge whose
lemmas then fail is broken, and erroring is the author's own ruling [2026-09-08
08:45 "我建议直接 error 说内部错误: the judge 有问题"].

**Why only the author can decide:** the author ruled only *that* the
simplification runs again after the delta changes. "From the state step 1½
produced" (§5 step 6, plan:1104-1107) is the drafter's elaboration inside that
paragraph. Both shapes carry a mismatch — one between what the judge sees and
what P-auto proves, the other between the recording run and later runs — and
choosing which to accept is a phase-2 judge-contract decision. The four options
are set out in the structured `must_discuss` entry.

Whatever is chosen, one thing should change either way: the comment at :1424-1427
names the discipline for the two contexts while the goal state silently chains
from step 1½ into step 6 through the shadowing at :1457. That third inheritance
should be named where the other two are.

---

## 3. Conditions (the drafter fixes, then re-submits)

| # | What | Where |
|---|---|---|
| D1 | §7's five stale statements, two inverted; the cost bullet | plan:1165-1168, :1217-1219, :1226-1229, :1252-1256, :1260-1264 |
| D2 | §1 "the goal state" still says the pass has acted; **plus** the term now has two referents | plan:156-163, vs :222-224, :1048-1050, :503 |
| D3 | Three comments assert "every solving function runs it once"; `:104` disagrees with `:1608` | reasoners.ML:104, :112-114, :1064-1065 (:88-89 for consistency) |
| D4 | The `\<phi>guard_P_auto` description promises 400 ms for a two-step, 60 s-capped method | PLPR.thy:1977 |
| D5 | §1 repeats D3's false universal ("three solving functions … call it") | plan:204-206, :215-217, :4-6 |
| D6 | Dead anchors: `is_guard_mode`, `PLPR.thy:1984/:1987`, `p_auto_search_tac`, two "G.simpcut" cross-references | plan:141-144, :1036-1042, :1150, :1481 |
| D7 | §39 ruling 1's "Terms from now on" contradicts ruling 2 and everything else | plan:3521-3522 |
| D8 | "the one visible difference" — there are two; the trace line is the more visible | plan:229-234, :3611-3614 |
| D9 | §5 step 1½'s "nothing written" — step 1 can rewrite the entry first | plan:1043-1048 |
| D10 | The new `:1489` error has no probe; the suite header still says "both errors" | Guard_Decision_Smoke.thy:6-8 |
| D11 | `Guard_False_Probe.thy:50` still calls the deleted `p_auto_body` | ai-artifacts/Guard_False_Probe.thy:50 |
| D12 | Ruling 6's "clarifies" describes `force_tac`, not `fast_force_tac` | plan:3542-3544 |

Full statements and fixes are in the structured `drafter_may_decide` list. Edit
the plan by hand, not with scripts.

### Three wrong repairs proposed in round one — do not apply them

1. **Do not re-anchor §1 "guard" on `is_syntactic_premise_mode`.** I read it at
   reasoners.ML:500-504: it returns true for `MODE_GUARD`, `NO_INST`,
   `MODE_COLLECT` **and** `default`. Using it would silently widen the plan's
   definition of its most basic term to cover collect-mode and ordinary premises.
   Anchor on the `MODE_GUARD`/`NO_INST` constants (PLPR.thy:187, :189) and the
   registrations (PLPR.thy:2008-2009, :2011-2012), or drop the code citation.
2. **Do not delete §39's "a `\<condition> False` guard closed by simp now yields a
   decision record."** It is true and measured: the factory inserts the aux facts
   before `solve`, so the guard arrives as `useful₁ ⟹ … ⟹ Premise mode False`,
   and §33 item 3 (plan:2924-2937) records `x = None`, `x = Some y` → PROVED in
   1 ms.
3. **Do not add `ALLGOALS quick_cut` to the obligation instance.** `oblg_template`
   (:376-382) guarantees a `Trueprop (Premise mode P)` conclusion at that point;
   `quick_cut` (:970-973) matches only a bare `Trueprop False`. It would be dead
   code.

---

## 4. Proposals for the author

**P1 — one exported `guard_simp_tac`-then-P-auto composition** for
`p_auto_solving` and the `\<phi>guard_P_auto` method (not for `prove_or_refute`,
which cannot use it: ruling 2 shares the pass's output with the refuters and the
judge, and it reads every option from `ctxt0` while running in `ctxt_g`). Relaxes
no ruling. The drift it would prevent is visible in this patch — the two sites
were changed together and the method's description string was the half forgotten
(D4).

**P2 — take §39's parked decision on the `quick_cut` refutation.** §39 already
records it as "a separate decision". The reason to revisit it now is that this
change *widened* the set of inputs reaching that exit: the pass used to run on the
delta-free `guard_ctxt`, so only the ambient simpset could rewrite a guard to
`False`; it now runs on `ctxt_g`, so a cached lemma — or, at step 6, a judge's —
can. Such a guard leaves no verdict, no record and no warning while its entry may
still say `Proved`. Nothing is unsound and phase 1 has no producer of lemmas, which
is exactly why it is cheap to settle before phase 2. If the author prefers silence,
§5 step 1½ should say that the trigger now includes the entry's and the judge's
lemmas, and why.

---

## 5. Rejected, with rebuttals

Twenty-four findings do not survive. One-line rebuttals are in the structured
`rejected` list; the recurring patterns:

- **The judge-path cluster** (ml-correctness/F1, elegance/F5, tests/F1,
  performance/F3, provenance/F6-second-half) — refuted as filed, because the judge
  is handed the same state step 6 re-simplifies and both errors name the right
  party; the one residue is MD1, in a much narrower form than any of them stated.
- **Restatements of a ruling as a defect** — out-of-run/F5's structural half
  (rulings 2 and 3), out-of-run/F7 (§5 step 1½ and §39's own parked decision),
  provenance/F3's provenance half (the method's body follows from rulings 1–2).
- **Pre-existing shapes the patch neither introduced nor worsened** — the three
  spellings of the bounded search (elegance/F6), the double `solved_states`
  (out-of-run/F8), P-auto's `addss` wrapper (out-of-run/F2), §7's already-incomplete
  cost bullet (performance/F2).
- **Layout taste** — ml-correctness/F5 and plan-code/F6, both of which also
  mis-measured the code: the inner `let`/`in`/`end` follows the file's own
  convention and the `end` they call dangling sits beside its own `in`.
- **Findings refuted by reading the text they attack** — tests/F9 (the probe
  comment never mentions P-auto), elegance/F7 (the patch *deleted* the stale
  premise and supplied a valid one), provenance/F8 (§39:3552-3554 records the
  probe it says is unrecorded), tests/F5 (§33 item 3 measured the case it calls
  vacuous).
- **Out of scope** — performance/F5 (§38 is explicitly excluded).

Two rejected findings leave a residue I folded into a condition rather than
dropping: out-of-run/F2's observation that "P-auto searches its result without
simplifying again" is blunter than the code (→ D3), and is-F-deletion/F2's
observation about "clarifies" (→ D12).

---

## 6. Bottom line

The restructuring is correct and the rulings are implemented faithfully; the
Quicksort verification is convincing. What is not ready is the record. Three of
the document's live, authoritative sections still teach the pipeline this change
removed, and three comments the patch wrote teach a rule it breaks — and in a
project where the plan is the contract and comments are load-bearing, that is the
part that costs the next session. Apply D1–D12, put MD1 to the author with the
options laid out, and re-submit.