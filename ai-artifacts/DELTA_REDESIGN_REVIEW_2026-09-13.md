# Judge's report — the delta redesign (§36), two-round adversarial review

## 1. Acceptance

**ACCEPTED_ON_CONDITION.**

The change implements §36's six rulings faithfully. I verified each against the sources:
an entry is `{delta = {added, deleted}, verdict}` (`guard_cache.ML:25-28, 69-72`); the delta is
applied on every call, deletions first, whichever guard added the theorem
(`reasoners.ML:1413-1416, 1434`, `guard_cache.ML:157-158`); the judge receives the pre-delta
guard context *and* this entry's delta (`reasoners.ML:1318-1320, 1447-1448`) and its `Provable`
delta replaces the entry's whole, applied to the same pre-delta bases (`:1458-1459`);
deletions and additions are persistent; identity is `Thm.prop_of`/`aconv` (with one
line exception, below); `canonical_form` is gone. Verification is real, not partial —
§36 records both the cold run **and** the warm run in a new process (355 decisions,
146 `Refuted` + 5 `Unknown` hits, 136 s → 20.6 s), so T7's premise is false.

Conditions:

**C1 (author).** Settle SEM-2 — step 1's append keeps the existing budget
(`guard_cache.ML:170`) while step 6's takes the judge's (`:171`), so an entry written by
step 6 does not reproduce, on replay, the context the call that wrote it returned. The
battery's own re-propose probe (`Test/Guard_Decision_Smoke.thy:481-495`) pins the recording
half of exactly this case and nothing pins the replay half.

**C2 (author).** Settle P3 — a replay that overruns its time budget is treated as a
broken lemma and the lemma is erased from the persisted entry.

**C3 (drafter, then re-review).** SEM-1: convert the delta handed to the judge to this
machine's clock (`Phi_Proof_Store.machine_time`), so that a judge restating a record it was
given is exactly correct instead of double-scaled. One line plus two sentences of contract.

**C4 (drafter).** The one-line identity fix at `guard_cache.ML:163` and the two stale plan
parentheticals.

**C5 (drafter).** The documentation sync: plan §3's whole pipeline block, §1:144-145,
§1:257-258, the header (lines 3-8, 16-36, 122), and `reasoners.ML:1557`.

**C6 (drafter, optional but recommended).** The battery additions listed under
DRAFTER_MAY_DECIDE (E4 first — it is the only one that closes a mutation class that
today passes silently).

Nothing in the change is a dirty hack; comments are for readers and carry no citations
or dates. C3–C5 are mechanical; C1 and C2 are the only design content.

---

## 2. Triage

### MUST_DISCUSS (the author decides)

**SEM-2** — *step 1's `add_lemma` and step 6's `update_lemma` resolve a collision by
opposite rules.* Upheld by all three defenders and by my own reading:
`reasoners.ML:1459` applies the judge's delta with `update_lemma` (new budget wins) and
`:1462` writes that same delta; `:1434` replays it with `add_lemma` (old budget wins). The
step-1 rule is *not* an author ruling — the plan itself says so at line 2629-2631 ("the
drafter's rule, unchanged for step 1 — stated as an assumption") — while §1's judge bullet
records the author's purpose that the recording run and every later run behave alike.
Options in §4.

**P3** — *a transient replay timeout permanently erases a lemma from the persisted
entry.* Upheld 2-1. Confirmed: `reasoners.ML:1388` maps the whole `Auto_Fail` vocabulary,
`Timeout` included, to `Fails_To_Replay`; the wall limb of `Phi_Proof_Store.replay_limits`
(`cache_file.ML:936-939`, 2·wall + 3 s) is wall clock by design and its own header says it
fires on "a loaded machine"; `delta` at `reasoners.ML:1426` is built from the survivors and
is what **all five** write sites persist (`:1432, :1468, :1472, :1481, :1489`), so the loss is
not confined to the drop write the finding cites. The refuting defender is right that the
dominant limb is thread CPU and that §24 already refused "splitting 'fails to replay' by
`Auto_Fail` reason" (plan:2244-2245) — but that was a panel's refusal, not a ruling, and the
author's ruling ("除非 a lemma 重放失败, 此时就已经移除并报警", §5 step 1) is glossed in the
plan itself as *the theory changed under it, or the method text broke §1's contract* —
a broken lemma, not a slow machine. Options in §4.

**P5** — *the two batteries' `.proof-store` files grow and are untracked-not-ignored.*
Factually correct (measured today: `Guard_Decision_Smoke.proof-store` 11621 bytes / 63
records, `Guard_Export_Smoke.proof-store` 777 bytes / 3). This is **already** one of the two
items §35 hands to the author (plan:2980-2982, "which of the new `*.proof-store` files to
track"); the finding adds measurements, not a new question. The drafter must **not** add a
`.gitignore` line on its own judgement — a gitignored side store was rejected by the author
once already (§8 CORRECTION). Options in §4.

### DRAFTER_MAY_DECIDE (clear fix, no design content; apply and re-review)

**SEM-1** — *a judge that echoes a lemma of `judge_arg.delta` gets its times divided by
`timeout_scale` twice.* Upheld 3-0 and confirmed: the inbound delta carries store times
(`guard_cache.ML:116`, `times_of_ms`, no scaling), `reasoners.ML:1450-1451` applies
`standard_time` to **every** returned lemma, `:1462` persists it verbatim; `cache_file.ML:792-795`
states the rule this breaks, and `machine_time` (`:239, :915`) exists, with zero callers in
phi-system, precisely "for the one reader that must hand a stored record back out as a
measurement on this machine's clock". Latent, not live (`judge` is `NONE`; both test judges
build fresh records), and invisible at `timeout_scale = 1.0`, so §36's verification stands.
Fix: bind a converted copy at the hand-off site only —
`{added = map (fn (stmt,(times,script),tier) => (stmt,(Phi_Proof_Store.machine_time times, script), tier)) (#added delta), deleted = #deleted delta}`
— pass it at `reasoners.ML:1448`, leave `:1450-1451` as is. **Do not** convert `delta` itself:
it is also written at `:1432, :1468, :1472, :1481, :1489`. Add the mirrored sentence to the
judge comment (`:1307-1317`) and to plan §1's judge bullet: the times are raw times on this
machine in *both* directions.

**TWO-IDENTITIES-IN-ONE-MODULE** (canonical) / **SEM-5** / **E2** / **P6** — four filings of
one defect: `guard_cache.ML:157-158` deletes by `aconv` on `Thm.prop_of`, `:163` dedups by
`Thm.eq_thm_prop` = `aconv o apply2 Thm.full_prop_of` (proposition + flex-flex pairs),
while `:46` and §36 ruling 6 name one identity for both. Residue of the withdrawn
canonical form (the pre-change line ran on the canonicalised theorem). Behaviourally
reachable only for a replayed theorem carrying tpairs — `eval_prf_str0` ends at
`Goal.conclude` with no `Drule.flexflex_unique`, so not impossible, and the cost if it fires
is one surplus list entry, never soundness. Fix, one line:
`fun same (th', _) = Thm.prop_of th aconv Thm.prop_of th'`. Do **not** factor a shared
predicate (the two sites compare term-vs-thm and thm-vs-thm; a helper is used at one of
them). Plan by hand: line 665 and line 971 to say `aconv` on the proposition; leave line 577
(`Raw_Simplifier`'s own test) alone.

**E3** / **SEC3-PIPELINE-PRE-DELTA** / **SEC1-CALL-RETURNS-PLUS-LEMMAS** / **E6** /
**HEADER-STALE-CANONICAL-FORM** — the documentation residue, upheld unanimously in all
five filings. All verified:
- plan:778 `SOME {lemmas, verdict}`; :779-781 a step 1 with no deletion; :785, :789-796,
  :801, :803 `write {lemmas,…}`/`{[],…}`; :797 a `judge_arg` without `delta`; :798 "this
  entry's lemmas replaced by `new`".
- plan:773-774 still keys the digest to `Thm.cprems_of`, which §1's guard-digest bullet
  explicitly corrects and `reasoners.ML:1610-1611` contradicts (`Hasher.terms` over the whole
  goal state plus `Assumption.all_prems_of`). Also in the same block: :776 bounds
  "G.simpcut" by `\<phi>guard_classic_prover_timeout` (it is a fixed 5 s thread CPU,
  `reasoners.ML:1575`), and :771 writes the factory without its `digest_of` parameter
  (`reasoners.ML:1558, 1613, 1622`).
- plan:144-145 "with this guard's lemmas in the lemma list" and plan:257-258 the factory
  **invariant** "`ctxt0` plus this guard's lemmas" — both false under a deletion, the second
  being the one named invariant a reviewer checks the factory against.
- `reasoners.ML:1557` "derives its ctxt_g by adding the entry's lemmas" — the only sentence
  in the file still written against the pre-delta design (`:1399` was updated).
- plan:3-8 and :122 give two mutually contradictory, five-sections-stale statuses; plan:16-18
  narrates the withdrawn canonical form in the present tense, its obituary sitting 660 lines
  away at :679-681.
Use the wording already in the tree (`reasoners.ML:1399`, "ctxt0 with this guard's delta
applied"); keep "nothing else changed", which is still true and load-bearing. Add §3 to
§36's "What changed" list. Hand edits only. Two defenders propose collapsing §3's steps 0-6
to a pointer at §5, since that duplication is what rotted twice — I endorse it as the
drafter's option, and it is the only version that prevents the next drift.

**E4** — *neither deletion probe can detect over-deletion.* Upheld 3-0; I re-derived the
mutant myself: `delete_lemmas` wiping the whole list whenever `stmts` is non-empty passes
all three deletion probes (`Guard_Decision_Smoke.thy:419-431, 433-437, 466-478`), because in
each the only survivor asserted is the lemma the same delta *adds*. This is the highest-value
test item: over-deletion silently costs an unrelated earlier guard its lemma, which is exactly
what ruling 2 makes possible. Cheapest correct fix (two defenders converge): give the
"deletion naming nothing" probe the `seeded` context **and a statement absent from the
list** (not `chain_nil`, which is the seeded lemma's own proposition), and assert the seeded
lemma is still there at budget 30. One probe pins both halves.

**T1** — *no probe observes a deletion in `ctxt_g`.* Upheld 2-1; correct as a coverage
statement (both deletion probes delete `CHAIN []`, which is irrelevant to their guards — the
add half is witnessed, the delete half is not). Severity is minor, not major: `apply_delta`'s
`into` is one closure applied to both bases (`reasoners.ML:1413-1416`), so no input
distinguishes them. Optional probe: seed the looping lemma at budget 3, guard
`⟨condition⟩ (PP (LOOP fresh))`, entry `{added = [], deleted = [looping stmt]}` at `Unknown`,
no judge; expect `("unknown","unknown","-","-")`. Reuse the `Goal.prove` of the looping
theorem already at `:295-296` rather than copying it.

**T2**, **T3**, **E5** — three further coverage gaps, each closable by changing one field of
an existing probe; all three are optional polish, none is a defect.
- T2 (upheld 1-2): no probe crosses "entry with deletions" with "a judge". Add
  `deleted = [chain_nil]` to the entry of the probe at `:447-462`; the existing assertions
  then also pin that the judge's delta replaced the entry's deletion (the seeded lemma comes
  back at budget 30) and that step 6 starts from the pre-delta contexts.
- T3 (upheld 1-2): every probe reaching the drop write (`:1432`), `refuted_by` (`:1472`),
  `Unprovable` (`:1468`) and the give-up `Unknown` (`:1481`) has `deleted = []`. Add
  `deleted = [chain_nil]` to the entry at `:403` (store becomes "Refuted with 1 lemma(s),
  1 deletion(s)") and, if wanted, to `:409` with a `seeded` context.
- E5 (upheld 2-1): the judge is never handed a delta whose lemmas were *dropped* by step 1,
  and the contract helper's expectation is derived from the injected entry
  (`Guard_Decision_Smoke.thy:95, 100-106`). Best shape (no new option-record field): pass the
  digest to `contract` and read the expectation back with `entry_of` — step 1's drop write
  (`reasoners.ML:1432`) has already landed when `consult` runs, so the store *is* the
  expectation. Do **not** re-implement `replay_lemma`'s success test in the oracle.

**E1** (and **SEM-3**, its duplicate — see REJECTED) — *`apply_delta` takes the deletions
apart from the delta that is written.* No defect exists: both call sites pair correctly, and
the filed fix (pass the delta record) only relocates the hazard to the `replayed`/`replayed'`
argument, which is identically confusable. If the drafter wants the invariant structural,
the only version that delivers it — proposed independently by four defenders — is to let
`apply_delta` **produce** the delta it applies:
`in ({added = map fst replayed, deleted = deleted} : Phi_Guard_Cache.delta, into ctxt0, into ctxt)`,
with `val (delta, ctxt1, ctxt_g) = apply_delta …` at `:1434` (moved above the drop write,
which is its only earlier user) and `val (delta', ctxt1', ctxt_g') = …` at `:1459`. That
deletes the two hand-written `{added = …}` records at `:1426` and `:1458` — net one line
shorter, and information-preserving (`#added delta = map fst replayed` holds at both sites
today). Purely optional.

### REJECTED

**SEM-3** — duplicate of E1, and its specific fix is refuted for the same reason (it closes
one of two identical argument slots).

**SEM-4** — *a deletion cannot protect the "G.simpcut" pass.* Nitpick 3-0, and I agree. The
goal state handed to `prove_or_refute` (and to the judge, `reasoners.ML:1448`) is already
G.simpcut's output, and step 6 validates on that same `th`; so a `Proved` entry was earned on
the rewritten goal and every later call rebuilds the identical pass from the identical
pre-delta list. The proposed hoist would make the goal a function of the entry keyed to it
— the oscillation the finding imagines, self-inflicted — and would let a cached lemma refute
a guard through `quick_cut`'s `Seq.empty` with no store write and no warning. At most one
clause in §7 noting that the deleting call's own G.simpcut still pays the lemma once.

**P1** — *`write_entry` can raise out of the codec.* Nitpick 3-0. Decisive: the same
`Phi_Tool_Symbol.dest_symbol` assertion sits unguarded on the hot path a hundred lines
upstream, in `guard_digest` → `Hasher.hash_term` (`reasoners.ML:1599, 1610-1611`), over the
whole goal state and every assumption, on *every* call; so "the one write that bypasses it"
is false. The raise is a deliberate detector of a stated global invariant (`ssymb.ML:19-24`),
and the decode catch-all exists for *foreign bytes on disk* (§8, no format version), not as
general defensiveness. Swallowing the encode would hide an invariant breach and leave the
offending term live in the context.

**P2** — *`Hasher.compact` puts raw bytes in the collision warning.* The mechanism is real,
the finding is re-litigation: plan:398 and §31 item 4 (plan:1636) record the author's
"我坚持用 compact", and §35 lists "`Hasher.hex` for the key" among items already rejected with
reasons. The fix is also aimed at the wrong layer by its own admission — the payload half
stays raw under any key spelling, and the real repair is either escaping at the print site in
`cache_file.ML` (out of scope, unchanged) or §8's still-OPEN alarm item, under which guard
entries never reach the message at all.

**P4** — *an undecodable record is indistinguishable from no record.* Nitpick 3-0. "No
counter, no warning, no way to tell" is refuted by the `guard_decision` record's `hit` field
(`reasoners.ML:1333-1339, 1517-1523`) — the very instrument §36's "355 decisions, every one a
miss" and the warm run's "146 Refuted and 5 Unknown hits" were read off — and by the smoke
batteries, which round-trip the codec on every probe and would fail by name on a tag renumber.
A miss also rewrites the entry in the current format, so the condition is self-healing.
`lookup_entry` has a `theory`, not a context, so the proposed trace gate is not even reachable
there.

**JUDGE-DELETION-NAMING-UNSPECIFIED** — refuted 3-0, and I checked the two lines it calls
silent: `reasoners.ML:1310` says "the judge may delete any of them by its proposition", and
plan:455-457 says "the theorems the judge may name for deletion, by their propositions".
Its scenario (a) is a category error — the judge drops one of *this* entry's lemmas by not
restating it, since the answer replaces the delta whole — and the proposed run-time check
would break correct judges, since a re-stated deletion may legitimately match nothing at a
site whose boundary history differs (ruling 6's accepted residual).

**DELETION-DOES-NOT-REACH-AN-ENHANCED-SIMPSET** — nitpick 3-0. The sentence it calls
unqualified is qualified in its own first clause: `guard_cache.ML:22` "what the guard does to
**the lemma list of the context it is met in**". A value already built from the list does not
change when the list later changes — true of additions and of budgets equally; this is
`Proof.context` value semantics, not a property of deletion.

**T4** — *no lemma identified by its raw proposition crosses a boundary in a battery.*
Nitpick 3-0. The consequence is stated and accepted twice in the plan (§1 the export hook,
lines 664-681; §7), the growth account is mechanically wrong (the hook `put`s an overwritten
list, `guard_cache.ML:177-182` — a crossing never adds a copy), and the proposed third family
cannot be built in that battery without fabricating a type variable with `Variable.declare_typ`,
i.e. re-testing `Proof_Context.export`. One defender's alternative (rebuild the exported list
through `add_lemma`) I do **not** endorse: it changes which copies exist, against an accepted
design note.

**T5** — *the stored delta is asserted by counts only.* The finding's own mutant is caught.
`show_entry` (`Guard_Decision_Smoke.thy:80-86`) prints the deletion clause only when `deleted`
is non-empty, and every judge probe answering `adds [...]` has `deleted' = []`; writing
`deleted = map #1 new` at `:1458` therefore turns "Proved with 1 lemma(s)" into "Proved with
1 lemma(s), 1 deletion(s)" at `:452`, `:485` and `:502`. Term-level assertions also already
exist, on the read side (`contract`, `:104-106`, aconv element for element through the codec)
and on the returned list (`:428, :457-458, :475, :490`). Pretty-printing terms into thirty-one
expectation literals would make the battery brittle for nothing.

**T6** — *the contract helper hard-codes "the entry replays whole".* Refuted/nitpick 3-0.
Its mutant (hand the judge the stored lemmas) changes the shared `delta` binding at
`reasoners.ML:1426` and so breaks the drop-write assertions at `:396-399` and `:403-406`; the
claim "no probe can be written without first changing the helper" describes an ordinary edit
to a helper in the same file whose precondition is documented. The genuine part is subsumed
by E5's store-read fix.

**T7** — *§36's verification has no hit path.* Refuted 3-0 on the plain text: plan:3055-3058
records the warm run **in a NEW process** — 146 `Refuted` and 5 `Unknown` hits read from the
proof stores, 20.6 s against 136 s cold. The cold line already carries the qualification the
finding asks for ("every one a miss (the old entries do not decode)"). The proposed
non-fresh probe would break the batteries' stated determinism invariant
(`Guard_Decision_Smoke.thy:18-25`) and has no history-independent expectation. The one true
residue — no *non-empty* delta has crossed the file, since the corpus installs no judge — is
covered in-process by every entry probe, and if anyone wants it on disk the hermetic form is
`Phi_Proof_Store.force_reload` (`cache_file.ML:699`) between write and lookup, not a
cross-process probe.

---

## 3. Relaxation proposals I endorse

**R1 (SEM-2) — one collision rule for step 1 and step 6.** Relax §5 step 1's "the entry
already there keeping its budget" (plan:971; §1's export-hook bullet, plan:665), which §31
item 3 (iii) (plan:2629-2631) marks as the drafter's assumption, to: *a proposition already
in the list takes the budget of the delta being applied* — step 6's rule, which the author
did state ("更新 the budget", §1 the judge, 2026-09-09). Benefit: `update_lemma`,
`add_lemma_with` and `apply_delta`'s `add` parameter all disappear; applying a delta to a
lemma list becomes ONE operation, so "the entry, replayed, rebuilds the context the recording
call returned" holds by construction rather than by two lines agreeing; the duplicate-inside-
one-`added` divergence vanishes with it. Cost: a later guard's delta may lower an earlier
guard's lemma budget on replay — which it already does on the recording run, so the change
does not introduce the lowering, it makes the replay agree with the run that was verified.

**R2 (P3) — a time overrun is not a replay failure.** Relax §5 step 1's "overrunning either,
or `Auto_Fail`, is 'fails to replay'" so that *fails to replay* means the lemma is broken
(fails to certify, or its method text cites a fact this `ctxt0` does not have), while a lemma
that overruns its recorded budget is simply not enabled on this call and keeps its place in
the entry, with its own warning. Benefit: it restores, one level up, the principle the author
already imposed inside this file — `reasoners.ML:1037-1038`, "Thread CPU, not wall clock, so
that machine load cannot flip a verdict" — where today the *wall* limb of `replay_limits`
(`cache_file.ML:936-939`, explicitly "the only one that can fire … [on] a loaded machine") can
flip something far more durable than a verdict: the contents of a git-tracked
`.proof-store`. A genuinely broken lemma is still removed and still warns.

I do **not** endorse: `Hasher.hex` for the key (P2, decided), a `.gitignore` glob over
`Test/*.proof-store` (P5 — it would silently swallow `Stateful_Reasoning_Smoke` and
`Guard_Race_Smoke`), rebuilding the export hook's list through `add_lemma` (T4), or any
run-time validation of the judge's `deleted` list (JUDGE-DELETION-NAMING).

---

## 4. MUST_DISCUSS — options and consequences

### SEM-2 — the collision rule

Where: `guard_cache.ML:162-171` (`add_lemma_with fst` / `snd`), used at `reasoners.ML:1434`
(replay) and `:1459` (judge), with `:1462` writing the judge's delta.

- **(a) One rule, the delta wins (R1).** `add_lemma` becomes "a theorem of that proposition
  already present takes the given budget"; `update_lemma` and `add_lemma_with` are deleted,
  `apply_delta` loses its `add` parameter, and the two call sites become the same call. Exact
  in both directions; strictly less code. Battery: the probe at
  `Guard_Decision_Smoke.thy:481-495` keeps its assertion (the recording run is unchanged), and
  one new probe should replay a stored entry into the same seeded context. Cost: a later
  guard's delta may lower an earlier guard's lemma budget on replay.
- **(b) One rule, the list wins.** Symmetric, and wrong for the design: the judge could then
  never change the budget of a lemma already present, which is what §1's judge bullet says a
  re-proposal does.
- **(c) Delete-then-add.** Keep step 1's rule verbatim and make the judge change a budget by
  naming the statement in `deleted` and restating it in `added`. Exact, since `apply_delta`
  already deletes before folding, and it keeps the "no guard silently lowers another's
  budget" protection. Cost: one more sentence of judge contract; the re-added lemma moves to
  the end of the list (simp-rule order shifts, deterministically); the probe at `:481-495`
  must be rewritten.
- **(d) `Int.max`.** Rejected by all three defenders and by me: it is a *third* rule, exact in
  neither direction (the battery's own probe lowers a budget from 30 to 3, and `max` gives 30
  back on replay), and it leaves both functions in place.
- **(e) Do nothing.** The divergence is latent while `judge = NONE`, but the protocol and its
  battery are being frozen now for the phase-2 judge; with a judge installed the guard can
  fail to converge (P-auto fails at the clamped budget → judge → same delta → written again)
  and, with no judge, ends `Unknown` from a `Proved` entry with the loud warning.

My recommendation: (a), with (c) as the acceptable alternative if the author wants to keep
"no guard lowers another's budget".

### P3 — a replay overrun erases the lemma

Where: `reasoners.ML:1371, 1388` (`failure`, the catch-all handler), `:1426` (`delta` from the
survivors), and all five writes `:1432, :1468, :1472, :1481, :1489`.

- **(a) Status quo.** A lemma that overruns is dropped from the entry and warned about. Simple,
  and the dominant limb is thread CPU, which load does not charge. Risk: the wall cap
  (2·wall + 3 s, ≥ 3.8 s after the 400 ms floor) is wall clock, and a dropped load-bearing
  lemma is unrecoverable without a judge — the entry degrades to `Unknown` and the guard is
  thereafter assumed false.
- **(b) R2, one extra constructor.** `Overruns_Its_Budget` beside `Fails_To_Certify` /
  `Fails_To_Replay`; `replay_lemma` matches the `Auto_Fail` payload; the *kept* list (what the
  entry says) is separated from the *replayed* list (what this call may use), so `delta` means
  "the entry as it stands" at all five writes and `apply_delta` still receives only real
  theorems. Note the finding's own fix — suppressing only the `:1432` write — is incomplete
  and must not be taken as filed. Cost: a genuinely diverging lemma is kept for ever, paying
  its bound and one warning per call; the judge is handed a lemma that was not enabled
  (harmless — it replaces the delta whole, and the entry's true content is the honest thing to
  show it, but §5 step 6 needs one sentence).
- **(c) Widen the slack instead.** `replay_limits_with` already takes the slack as a parameter
  (`cache_file.ML:936-939`), so the guard cache could pass a larger one. No new vocabulary, no
  ruling touched, but it only moves the threshold and should not be moved without a
  measurement — none exists.

Note for whichever is chosen: there is no time-overrun probe in either battery (they seed
`unreplayable` and `uncertifiable` only).

### P5 — the batteries' store files

Already §35's open item; the drafter needs the answer, not a new mechanism.

- **(a) Do not `git add` them.** No source change, no `.gitignore`, no ruling touched; one
  decision at commit time. Both files are untracked today.
- **(b) Two literal paths in `contrib/phi-system/.gitignore`** (never a `Test/*.proof-store`
  glob — `Stateful_Reasoning_Smoke` and `Guard_Race_Smoke` open stores in that directory).
  Narrows §8's "nothing is gitignored for them"; justified only for these two theories,
  whose every guard argument is `run_tag + serial ()` so no run can ever hit another run's
  key.
- **(c) Track them.** Consistent with §8 as written; costs ~184 bytes per decided guard on
  each hand-evaluation, for records that are dead by construction.

Measured input for the decision: 11621 bytes / 63 records and 777 bytes / 3 records, against
42 tracked `*.proof-store` files totalling ~49 MB.