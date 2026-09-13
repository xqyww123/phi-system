# Re-review judgment — the collision marks (auto_sledgehammer 5ac4877..a6c2fc7, Isa-Mini d6005f2^..cfe6942, phi-system guard_cache.ML)

## 1. ACCEPTANCE

**ACCEPTED_ON_CONDITION.** The mechanism as shipped is correct; every ruled behaviour is implemented. Three defects remain, all comment- or test-local, and two of them are in text the drafter edited in this round.

### The first report's four conditions — all met

| Condition | Verdict | Evidence |
|---|---|---|
| T1 — test 20c writes with `ML_debugger` off on a theory value | **met** | `Test_Proof_Store_Double_Key.thy:362` `val thy_off = Config.put_global ML_Options.debugger false thy`; used at `:388-389`; `:361` gives `thy_dbg` for the positive direction |
| Hash_Hit comment reworded, no cross-repository pointer | **met** | `Isa-Mini/Test/Test_Proof_Store_Hash_Hit.thy:99-101` — "the collision marks, under ML_debugger, would say so"; no reference to another repo's test |
| hooks-1 wording (what a theory-level hook delivers) | **met**, with one false item — see R2-C3 | `cache_file.ML:674-679` (re-begin, PIDE-cancelled caveat, one stale mark) and the at_begin comment `:917-923` |
| Plan section 8 text | **met**, with the same false item | `GUARD_CACHE_QUICK_MODE_PLAN.md:1211-1213` and `:1217-1247`: retired warning string gone, four lines quoted once (`:1244-1246`), `rewrites = true` in both quoted write calls (`:1212`, `:1225-1227`), begin-hook sentence present |

### The three author rulings — all implemented

- **hooks-1 option A** — the hook is kept (`cache_file.ML:923` `Theory.setup (Theory.at_begin (fn thy => (close_store thy; NONE)))`) and both comments now state what a theory-level hook delivers (`:674-679`, `:917-922`). ✔
- **C1/E3 option B** — code unchanged; the clause is in the `written` comment, `cache_file.ML:678-679`: "A write that leaves the live record byte-identical installs nothing, and marks nothing either." ✔
- **E4 option A** — `cache_file.ML:690-693`: `proof_mark (t, text) = (Hasher.string text, Symbol.beginning proof_head_len (Symbol.explode text), Time.toMilliseconds (#wall t))`. ✔

Also verified: ruling 1 (`rewrites` consumed once, `cache_file.ML:810`; the only `rewrites = true` caller in all three repositories is `guard_cache.ML:137`), ruling 3 (`Hasher.string`, a `Word64`), ruling 4 (`Config.get_global thy ML_Options.debugger` read per write, `:810`), ruling 5 (`collision_message`, `:783-786`, four lines, pinned verbatim by test 20 at `:370-374`).

### Conditions for acceptance

1. **R2-C1** — `Test_Proof_Store_Double_Key.thy:364`: test 20 fails on a second evaluation of its own ML block. One line.
2. **F3 (primary half only)** — `cache_file.ML:789-796`: the last place in the tree that calls the mechanism "guard", in its own doc comment, and ambiguous with the fixed term "the guard cache". Ruling 9 is binding. Fix the whole paragraph, not just the first noun.
3. **R2-C3 (source half only)** — `cache_file.ML:676`: "a batch load" is listed as an occasion on which the marks are dropped; it cannot be one. The plan half is MUST_DISCUSS (§4).

Recommended but **not** conditions, because ruling 8 puts tests in the drafter's hands: F1/T-1, F2/T-2, T-3.

---

## 2. TRIAGE — every id

Two pairs are the same finding filed under two lenses: **F1 ≡ T-1**, **F2 ≡ T-2** (T-2 is the broader form). **R2-C2** and **T-4** are two halves of the same observation about the process-global warning hook.

### MUST_DISCUSS

**R2-C3 (plan half only)** — `GUARD_CACHE_QUICK_MODE_PLAN.md:1234-1236`. The false item sits inside a sentence stamped `[author 2026-09-13; §36]`. The wording descends from the first review's own recommendation text, not from the author's words, but it is an author-attributed line in a decision record. Options in §4.

### DRAFTER_MAY_DECIDE

**R2-C1** (condition) — *verified*. `Test_Proof_Store_Double_Key.thy:364` is the block's only reset, and `invalidate_store` is the one function documented to keep the marks: `cache_file.ML:773-775` rebuilds the entry as `(empty_store, true, written_of tab name)` under "dropping the data does not un-write what this session wrote". The marks die only in `close_store` (`:747-755`), reached from `Theory.at_end` (`:902`) and `Theory.at_begin` (`:923`); re-evaluating one mid-theory ML command begins no theory. Trace of the re-run: `proofs` is empty so `live_and_identical` is false, the `pA` write reaches `:826-828`, finds the stale `digest "pB"`, warns; the `pB` write warns again; `collision_warnings w20` has two elements and the equality at `:370-374` fails with a message that accuses the mechanism. 20b–20e survive (their stale marks equal the next text each writes), so test 20 — precisely the assertion the first review asked for — is the only casualty. Not ruling 2's accepted residual: no cancellation is needed, only a second evaluation.

Fix, and **put `close_store` first**:

```
val _ = S.close_store thy      (*invalidate_store keeps this session's marks by design*)
val _ = S.invalidate_store thy
```

Order matters. With `invalidate_store` last, the entry is installed directly as `(empty_store, true, Symtab.empty)` (`written_of` on an absent entry is `Symtab.empty`, `:695-696`) and no file is read. With `close_store` last the entry is absent, and the next `get_entry_i` calls `load_store_raw` (`:704-708`), which on a missing `.proof-store` falls back to `legacy_cache_path` — and `invalidate_store` removes only `store_path`. Hermetic by luck rather than by construction.

**F3 ≡ primary half** (condition) — *verified*. `cache_file.ML:789` still reads `(*This guard cannot stop a key collision, only make the write that produces one`, and the diff (`COLLISION_MARKS_DIFF_2026-09-13.patch:292-293`) shows this is the very sentence edited this round ("the build" → "the write"). Every sibling now says "the collision marks" (`:216-217`, `:807-809`, test file `:276`, `:292`, `:311`, `:348`, Hash_Hit `:99`). The other occurrences of "guard" in this file (`:423`, `:492-501`, `:612`, `:622`, `:644`, `:704`, `:925-929`) are lock/writability guards, and `:213` says "a guard-cache entry" — the fixed term for a different thing, whose write funnel this is.

**Do not rename the first noun alone**: `:795` reads "Its two questions go to two different tables on purpose". The collision marks ask one question; the two-question gate belongs to `update_cached_proof` (the byte-identical skip against `proofs` at `:822`, plus the mark comparison against `written` at `:825-829`). Rename `:789` and leave `:795` and you make `:795` false. Replace the paragraph:

```
(*The collision marks cannot stop a key collision, only make the write that
  produces one say so on the spot, instead of leaving it to surface days later
  in another theory as an unexplained replay failure.  They sit at the single
  point every writer goes through, so they also see the writers that a Post_App
  probe hook structurally cannot (holds_fact, led_future_proof).

  update_cached_proof asks two questions of two different tables on purpose --
  the reasons are with the declaration of `written` above.  The byte-identical
  skip additionally drops the benign duplicate appends of the rw_access retry
  path.
```

The **secondary half of F3 is REJECTED**: `:660` "under each key" and `:686` "key -> the digest …" are not a terminology slip. `written` is a `Symtab`, and "key -> value" is the idiomatic type annotation; "key" is live vocabulary in this file (`:213`, `:662`, `:670`) and in ruling 9 itself ("the key mint", "a key collision"); the plan's own wording at `:1218` is "what it wrote under each key". Ruling 5's `key:` → `id:` rename governs the user-visible message, not a table's domain comment. Editing `:660`/`:686` would move the source away from the author's ruled wording and make the file *less* consistent.

**R2-C3 (source half)** (condition) — *verified*. `cache_file.ML:675-677`: the parenthetical glosses "begun again in this process", and `and at theory end` is a separate coordinate clause, so "a batch load" cannot be re-read as belonging to the at_end case. In `isabelle build` each theory is begun once (`Thy_Info.eval_thy` builds each node's `init` once; `Theory.begin_theory`, `theory.ML:189-203`, applies the at_begin wrappers per construction), so the hook fires on the first and only begin and `Symtab.delete_safe` removes nothing. Delete the item: `(a re-executed header, a changed import, a reload)`. Do **not** add an explanatory clause saying nothing happens in a batch build — that spends two lines on a non-event.

**F1 ≡ T-1** — *verified, upheld unanimously, and I concur*. `Test_Proof_Store_Double_Key.thy:400-406` writes pA (false) / pB (true) / pA (false) and asserts only `null (collision_warnings w20e)`. Silence follows equally from "the mark is still pA" and from "the rewriting write cleared it". I traced the mutant `cache_file.ML:830` `| NONE => w` → `| NONE => Symtab.delete_safe id w` through the whole corpus: test 20 and 20d never take the NONE branch; 20b and 20c delete an absent key and their assertions are unaffected; 20e goes silent. `rewrites = true` occurs only at `:380`, `:381`, `:404`, and Hash_Hit has none, so nothing else kills it. That mutant is exactly what the first report named as not endorsed (`COLLISION_MARKS_REVIEW_2026-09-13.md:55`).

Fix — **replace** 20e's third write with a third text and assert the message:

```
(*20e: a rewriting write in between neither moves the mark nor clears it: the
      third write, a third text, is still measured against the FIRST one*)
   S.update_cached_proof thy_dbg {id = "K20e", hash = NONE, rewrites = false} (t1, "pC")))
val _ = assert (collision_warnings w20e =
                ["Proof store: two different proofs were written under one proof id in this session.\n\
                 \  id: K20e\n\
                 \  first (100 ms): pA\n\
                 \  now (100 ms): pC"]) "test20e a rewriting write neither moves nor clears the mark"
```

Change the assert label too — the present one ("does not move the mark") is the narrow claim being widened past. `t1 = S.times_of_ms (100, 100)` (`:29`), both heads are far under `proof_head_len = 120`, and the live record holds `pB` at that point so `live_and_identical` is false. One case kills three mutants: left alone → this text; moved → `first … pB`; cleared → no warning.

**Trap, flagged by one defender and confirmed:** do *not* keep the three writes and append a fourth `pC`. The third write is `rewrites = false`, so under the clearing mutant it re-installs pA's mark and the fourth write prints `first (100 ms): pA` exactly as the real code would. The discriminating write must be the one immediately after the rewriting write. Nothing is lost by dropping the silent shape — 20d already pins "the same text at another time is silent".

**F2 ≡ T-2** — *verified*. `cache_file.ML:669-677` makes one invariant load-bearing for the whole design ("deliberately NOT derived from `proofs`… the main collision path runs straight through that loss (L2 hit -> replay fails -> tombstone -> rewrite)"), and three sites implement it by hand: `force_reload:713-715` (`written_of tab name`), `invalidate_store:773-775`, `invalidate_proof_cache:849-852` ("w survives … a mark dropped here is evidence destroyed"). Tests 20–20e never invalidate between a marked write and a differing write — the only `invalidate_store` in the block is at `:364`, before test 20's first write, and `invalidate_proof_cache` appears in the file once, at `:95` (test 6, plain `thy`, no warning assertion). Tests 17b/18/19 do drive the tombstone path but capture no warnings and write through the bare `thy`, where `ML_debugger` is at its default `false` (`Isabelle2025-2/etc/options:187`), so no mark is minted. All three mutants pass green.

T-2's three-case form is better than F2's single case; cover each named site, one id apiece, appended after 20e:

```
(*20f: the tombstone path -- the mark outlives the record, which is why `written`
      is not derived from `proofs`*)
  write pA (thy_dbg) ; S.invalidate_proof_cache false "K20f" thy ; write pB
  assert the four lines verbatim, first (100 ms): pA

(*20g: re-reading the file says nothing about what this session wrote*)
  write pA ; val _ = S.force_reload thy ; write pB ; assert not (null (...))

(*20h: dropping the data does not un-write what this session wrote*)
  write pA ; S.invalidate_store thy ; write pB ; assert not (null (...))
```

Keep `warn = false` on `invalidate_proof_cache` so the unrelated "Proof cache for theory … is outdated!" line never enters the capture. Pin the four lines verbatim in 20f only and use the broad prefix predicate in 20g/20h — that is the shape the first review's C2/T4 settled on. Put 20h last, since `invalidate_store` also removes the file the earlier frame assertions scan. `Config.put_global` does not change `Context.theory_name`, so `thy_dbg` writes and a `thy` invalidation address the same entry — 20b already relies on this.

**T-3** — *verified*. Every text in 20–20e is `"pA"`/`"pB"`/`"pC"`: two symbols, no blanks, against `proof_head_len = 120`, so `Symbol.beginning` (`symbol.ML:210-219`) is the identity on all of them and the E4-A change is entirely unexercised — reverting `proof_mark`'s head to a verbatim one leaves the suite green. The production shape is real: `sledgehammer_solver.ML:1662` builds `"(" ^ String.concatWith ",\n" (rev prfs) ^ ")"` and `record_store` (`:1986-1989`) writes it with `rewrites = false`. Symmetrically, comparing `#2` instead of `#1` at `:827` is invisible when the head is the whole text. The first report blocked this assertion solely on E4 not yet being adopted (`COLLISION_MARKS_REVIEW_2026-09-13.md:34`); that blocker is gone, so this is a queued follow-up, not a new demand.

Prefer one exact equality in test 20's existing style over three structural probes. The cleanest discriminator is two texts sharing their *entire* head, so the printed message shows two identical heads and warns anyway — that is the digest-not-head property, and a head comparison yields `[]`:

```
val long_a = "a,\n" ^ replicate_string 200 "b" ^ "A"
val long_b = "a,\n" ^ replicate_string 200 "b" ^ "B"
val head_f = "a, " ^ replicate_string 117 "b" ^ " ..."
```

`"a,\n"` is three symbols rendering as `"a, "` (the newline becomes one space), 3 + 117 = 120, the text runs to 204 symbols so `" ..."` is appended, and the 120th symbol is a `b` so the blank-suffix trim inside `beginning` does nothing. Write the expected head by hand — calling `Symbol.beginning` in the test would make it tautological against the reversion it exists to catch.

**E7** — *verified, and in scope*: `type written` (`:685`), its slot-legend comment (`:686-687`) and the `#1 old = #1 m` line (`:827`) are all lines this change rewrote; only `collision_message`'s argument patterns are context. The only uses of the element type in all three repositories are `:783`, `:811`, `:827`, `:828`, `:830`; `written_of` (`:695`) destructures the *entry* triple and is untouched. The file's own idiom for such a bundle is a record (`proof_record = {hash, time, proof}`, `:187`; the key record `{id, hash, rewrites}`, `:218` — added in this very change).

Optional, drafter's call. **If taken, the proposed fix as filed will not compile** — SML record selectors are not row-polymorphic, so `#head old` in `collision_message` cannot resolve an unannotated parameter (the author already hit this two lines away: `fun proof_mark (t : times, text)` is annotated precisely so `#wall t` resolves). Name the element type, reusing the word the code already binds at `:810` and ruling 9 already fixes:

```
type mark = {digest: Hasher.digest, head: string, ms: int}
  (*ms is standard-machine wall time, display only*)
type written = mark Symtab.table
...
fun collision_message id (old : mark) (new : mark) = ...
```

Then `#digest old = #digest m` at `:827`, and the slot legend at `:686-687` shrinks to the one fact names cannot carry. The four message lines must come out byte-identical (ruling 5, pinned by test 20). No invariant is at stake — the three slots have three distinct types today, so a transposition is already a compile error; this is legibility, and ruling 3 moves from a comment 140 lines away into the comparison itself.

**E10** — *verified*: `capture_warnings` returns `(r, rev (! got))` (`:353-356`) and all five call sites discard `r` (`:367`, `:379`, `:387`, `:395`, `:402`); every `f` is `unit -> unit` (`update_cached_proof : … -> unit`, `:218`). The `val r =` binding is a fossil of the pre-T2 hand-rolled save/restore — `Unsynchronized.setmp` (`unsynchronized.ML:41-48`) restores on its own. Trivial, optional. **Take only the return-type half**; do not rename to `warnings_while` (churn on a name just settled, and `capture_warnings` describes a function returning captured warnings better than one returning a pair), and leave `collision_warnings ws = filter …` with its named argument.

**T-4 (the swallowing half only)** — true and negligible: `Private_Output.warning_fn` is one process-global ref (`output.ML:71`) and the hook at `:355` keeps what it likes and returns unit, so any other thread's warning inside the window is dropped. The build-log consequence is unreachable (no session loads this theory, verified below), leaving a lost diagnostic line in an interactive PIDE run. Optional hygiene. **If taken, the prefix tee in the proposal is the wrong discriminator** — it hard-codes ruling 5's prefix in a second place in the file, and it does not fix the pollution half it leads with (a foreign *collision* warning matches the prefix too). Either forward everything (`… (got := implode outs :: ! got; orig outs) …`), or filter by thread with `Isabelle_Thread.self`/`is_self` (`isabelle_thread.ML:16`, `:81`) — the warning is emitted synchronously on the writing thread (`cache_file.ML:833`), so thread identity captures exactly the test's own writes and closes both halves.

### REJECTED

**R2-C2** — the stated scenario has no vehicle and the proposed fix would do real damage.
- There is no "auto_sledgehammer Test session": `auto_sledgehammer/ROOT` declares `session Auto_Sledgehammer = Performant_Isabelle_HOL + … theories Auto_Sledgehammer` and nothing else; a grep of every `ROOT`/`ROOTS` under `contrib/` for `Test_Proof_Store_Double_Key` and `auto_sledgehammer/Test` returns nothing. No parallel theory load can inject anything.
- The premise "under `ML_debugger` on — the only configuration in which test 20 tests anything" is backwards. `:361-362` set the option on the *theory values* the test writes with; the session option defaults to `false` (`etc/options:187`). In the configuration the test actually runs in, no other writer in the process computes a mark, so no foreign collision message is constructible. `"Proof store: "` has exactly one emitter in all three repositories (`cache_file.ML:783`).
- The fix would move the message's interior layout (`"\n  id: " ^ id ^ "\n"`) into the predicate that 20b/20c/20d/20e depend on. Reformat the message and test 20 fails loudly (good) while all four `null (collision_warnings …)` assertions start matching nothing and pass **vacuously**. That trades the loud failure the first review's C2 bought for four silent ones.

**E6** — accurate observation, negligible payoff, and the fix does not deliver its stated benefit. `mark` is minted once (`:810`) and scrutinised at `:825-829` and `:830` — consecutive `val` bindings in one `let`, with nothing between them but the end of the first `case`. The tie is `mark` itself, and the natural place to add a participation condition is `:810`, which covers both consumers. Decisively: a *third* site skips both check and mark — the `live_and_identical` early return at `:822-823`, which is there by ruling 6 option B — so `check_and_mark` takes three sites to two, not to one, and the `written` comment's clause stays a promise about code either way. The `SOME m` clause still holds two separable expressions, so the feared edit lands inside it just as easily. Marginal, on code the author has just ruled on. If the drafter nonetheless wants one scrutiny, do it inline (`val (msg, w') = case mark of NONE => (NONE, w) | SOME m => (…, Symtab.update (id, m) w)`), strictly inside the `else` branch — hoisting above the `if` is option A, which the author declined.

**E8** — two of its three parts would undo rulings, and the third is one blank line.
- Leading with the gate contradicts E2's ruling. The table exists in every build: every entry carries a `written` component, created as `Symtab.empty` (`:723`, `:741`), whatever `ML_debugger` says. Only its *contents* are conditional. Opening a type's doc comment with a runtime option also inverts essence-first.
- Deleting `:807-809` is lossy, not redundant. The two lines below it (`:810-811`) only *compute* the mark; that the same `NONE` also means *not compared* and *not stored* is decided at `:825` and `:830`, fifteen and twenty lines further down inside a nested `Synchronized.change_result`. "computed, kept and compared" is the only sentence tying one guard to all three behaviours.
- Trimming `:919-922` walks back hooks-1 option A: the caveat states what the hook does not cover, the `see written` pointer says where the consequence lives; strip either and the cross-reference breaks.
The residue is typographic: `:669-684` is a sixteen-line paragraph. A blank line before "A write that leaves the live record byte-identical…" (`:678`) and before the `ML_debugger` sentence (`:681`) is the whole defensible change, and it is optional.

**E9** — the strongest third is factually wrong and the other two are this document's house style.
- "not only at its end" does not depend on a superseded draft. `at_end` is a live hook named to the reader two bullets earlier, `GUARD_CACHE_QUICK_MODE_PLAN.md:1215-1216`: "The store's locking, migration, compaction and `at_end` are the proof store's, untouched." The contrast is with the current text, and with a real second hook added by this change.
- "SHA1 until 2026-09-13" at `:1219` is welded to the author quotation it introduces — 建议用已有的 hash 机制去算而不是用 SHA1. Delete it and the quote names a term the sentence never introduces. The glossary uses the same shape (`:195`, "until 2026-09-11 `guard_condition_solver`").
- "the drafter's contrary example was wrong" is the rejected-opinion record this document exists to keep (cf. `:2942`, `:2801`, `:2904`, `:2997-3001`); the conclusion is already stated in full before it.
The division ruling 9 asks for is working: the source carries no date, name or review label (`cache_file.ML:658-684`, `:917-923`), and the plan carries the provenance.

---

## 3. RELAXATION PROPOSALS I ENDORSE

**(a) None that change a ruling.** I examined the two tempting ones and reject both explicitly, so they are not re-proposed next round:

- *Make `invalidate_store` (or `force_reload`) drop the marks, so every test block is hermetic for free.* No. The marks mean "what THIS session wrote under this id", which stays true after the data file is thrown away; `close_store` is the one dropper and its comment says why ("it is what makes 'this session' mean 'this theory, start to end'", `:751-754`). Folding a second, weaker meaning into `invalidate_store` buys one line in a test and makes the table's scope depend on which reset a caller happened to use. (For `store_invalidate_proof` it would be outright destructive — `:669-673` explains that the main collision path runs through it.)
- *Split `written` out of the entry triple into its own `Synchronized.var`, so no store mutation can drop a mark.* No. `update_cached_proof` reads `w` and writes both `proofs` and `w` inside one `Synchronized.change_result` (`:816-833`); splitting the tables splits that atomicity across two locks, and two concurrent writers colliding on one id could then both read an empty mark. A debugging aid does not justify a second lock order.

**(b) One extension of ruling 9 that I do endorse**, because it is what let this round's F3 slip through: retire the bare noun **"guard"** for this mechanism, not only the two-word phrase "collision guard". The first report's wording ("the last live occurrence of the retired phrase 'collision guard'") is literally true of the phrase and let `:789` survive a grep, and "guard" already means three other things in this file. Benefit: one grep (`grep -n 'guard' cache_file.ML`) becomes a complete check instead of a partial one, and "the guard cache" — a fixed term for a different thing whose write funnel this is — stops colliding with it.

**(c) One addition, not a relaxation**, worth its two lines: a clause on `proof_mark` (`:690`) saying the head is the text's beginning with blanks rendered as single spaces, *so the message stays four lines on the multi-part texts the solver composes*. Ruling 5's four-line guarantee is visible only at `collision_message` (`:783`), while the thing that enforces it lives at `:690-693`, where a reader sees a call to `Symbol.beginning` and no reason it must be there. Benefit: the invariant sits next to the code that holds it, and T-3 becomes unraiseable about the source even before the test exists.

I do **not** endorse the ruling-8 amendment several defenders proposed ("an invariant a comment declares load-bearing must have one test"). It is the right instinct — `:669-673` forbids three future edits by name and no test detects any of them — but it is a standing policy change, and ruling 8 is the author's. If the drafter simply adds 20f/20g/20h under his own authority, the policy is unnecessary.

---

## 4. MUST_DISCUSS — options and consequences

### R2-C3, plan half: `GUARD_CACHE_QUICK_MODE_PLAN.md:1234-1236`

The sentence reads: "The store also drops a theory's marks whenever the theory is begun again in the process (a re-executed header, a changed import, a reload, **a batch load**), not only at its end [author 2026-09-13; §36]". The fourth item is false for the same reason as in the source: a batch build begins each theory once, so the at_begin hook finds nothing to drop. The phrase originates in the first review's own recommendation text (`COLLISION_MARKS_REVIEW_2026-09-13.md:53`, which said "a *fresh* batch load" — the word that kept it outside the "again" reading), not in the author's words; but the sentence it sits in carries an author stamp, and the repo treats plan-document text as a decision record.

- **Option 1 — delete the four words by hand, leave the rest untouched.** The plan then matches the corrected source comment exactly. Cost: an author-stamped sentence is edited without the author's word. Consequence if wrong: nothing operational; the record loses a phrase the author never wrote.
- **Option 2 — leave the plan, fix only the source.** The plan and the source then say different things about the same hook, and the next reader of §8 still concludes a batch build re-begins theories. Cheapest in approvals, worst in accuracy.
- **Option 3 — ask the author for the one-word deletion before touching it.** One line of approval traffic, and the record keeps its integrity. My recommendation, given the repo's standing rule that anything in a decision record with author attribution is proposed rather than edited.

Note for whichever option is taken: the repo forbids scripted edits to plan documents — `sed`/batch replace is out, this is a by-hand edit.

---

## Anchors touched in this judgment

- `/home/qiyuan/Current/MLML/contrib/auto_sledgehammer/library/cache_file.ML` — `:213-218` (signature comment), `:658-684` (`written`), `:685-687` (type + slot legend), `:689-693` (`proof_head_len`, `proof_mark`), `:713-715`, `:747-755` (`close_store`), `:773-775` (`invalidate_store`), `:783-786` (`collision_message`), `:789-796` (the head comment), `:804-835` (`update_cached_proof`; `:810` the gate, `:822` the skip, `:825-830` the check and the mark), `:849-852` (`invalidate_proof_cache`), `:902` / `:917-923` (the two hooks)
- `/home/qiyuan/Current/MLML/contrib/auto_sledgehammer/Test/Test_Proof_Store_Double_Key.thy` — `:350-356` (`capture_warnings`), `:357` (`collision_warnings`), `:361-364` (`thy_dbg`, `thy_off`, the reset), `:365-374` (test 20), `:376-384` (20b), `:386-391` (20c), `:393-398` (20d), `:400-406` (20e)
- `/home/qiyuan/Current/MLML/contrib/Isa-Mini/Test/Test_Proof_Store_Hash_Hit.thy:97-101`
- `/home/qiyuan/Current/MLML/contrib/phi-system/Phi_Logic_Programming_Reasoner/library/guard_cache.ML:136-138`
- `/home/qiyuan/Current/MLML/contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:1209-1247`
- `/home/qiyuan/Current/MLML/contrib/Isabelle2025-2/src/Pure/General/symbol.ML:210-219`, `src/Pure/Concurrent/unsynchronized.ML:41-48`, `src/Pure/Concurrent/isabelle_thread.ML:16,81`, `src/Pure/General/output.ML:71`, `etc/options:187`