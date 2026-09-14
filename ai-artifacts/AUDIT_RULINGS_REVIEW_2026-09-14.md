# Review of the 2026-09-14 changes (workflow wf_dddde957-1ec: 5 interrogators, 3 fresh defenders per finding, a judge; 69 agents, 21 round-one findings, one defender lost to an API safeguard)

## Verdict

**ACCEPTED_ON_CONDITION.**

The eight rulings are implemented faithfully. I re-checked the load-bearing sites myself: the warning dispatch at `reasoners.ML:1504-1512` is exactly ruling 2 (loud only on `entry_verdict = SOME Proved andalso judge_answer = SOME "Unprovable"`; everything else reports as a call without an entry), the `guard_decision` / `guess_inst` records are gated on `ML_Options.debugger` with their own switches deleted, `decode_entry` catches `Subscript` and `Unpack` only, and the Event_Log marker format (`record_marker` written before every item, `split_items` cutting on it, `comment` breaking up `--`) matches ruling 8 in both readers and in the migration script. No correctness defect survived round two: of twenty-one round-one findings, sixteen were refuted 3–0 by the defenders and I confirm those refutations; three more were duplicates of each other.

Two things remain, both minor, neither a code defect:

1. The format's own specification document contradicts itself on the single point ruling 8 settled.
2. The test apparatus this diff introduced observes two of the three endings ruling 2 changed; the third — the one the ruling moved *away* from the loud warning — is asserted only in prose.

## Must discuss

**M1 — `EVENT_LOG_PLAN.md` still states the withdrawn space-stuffing transform as settled fact (minor).**
Merges the surviving findings `event-log-format-plan-stale-transform` and `elegance-plan-still-describes-withdrawn-transform` (2–1 in favour in both panels).

Verified by reading the file. §5 was correctly rewritten (`…每个条目…前先写一行边界标记 <!-- record -->…读取方按标记切段即可，不需要任何字符变换`) and carries the dated 修订 2026-09-14 note; §8 is correct. Four other places were not touched:

- §2 决策 5 (`记录边界"除首行外没有任何一行以 < 开头"由一次机械变换保证（§5），是定理不是纪律`). This is in the section headed "the settled decisions", and the invariant it states as a *theorem* is now false of real output: `XML.string_of` is flat, so a `Text` node ending in `\n` followed by a sibling element puts `<next>` at line start — which is precisely what record 2 of the permanent `Test/Event_Log_Test.thy` writes.
- §4, the `comment` entry (`内容过 §5 的同一次边界变换`). `comment` (`event_log.ML:175-182`) only breaks up `--`; the marker and the control filter come from `append_string`.
- §5's caption under the example (`续行的行首空格正是 §5 那次变换的产物`), over an example block that still carries no `<!-- record -->` line, i.e. the document's one worked example of the file format is in the old format.
- The status line at §0's head still lists `§5 边界变换改双射` among the implementation corrections.

Why this is for the author and not the drafter: the document is yours, plan documents may not be edited by script, and the document's own convention is to keep the original ruling text and append dated 「实施修正」/「修订」 notes rather than rewrite in place — §2.3 still describes the `\<phi>log_guard_race` / `\<phi>log_guess_inst` Config options that ruling 1 has now deleted, evidently on purpose. So the correction *style* (rewrite §2 決策 5 in place vs. mark it withdrawn and point at §5) is a call only you can make. What is not optional is that §2 決策 5 must stop asserting a false theorem, since the plan is the format's only specification for anyone writing a fourth reader.

## Drafter may decide

**D1 — wire the existing `warnings_of` / `assert_loud` harness to the Unknown ending of a `Proved` entry (minor).**
Merges `tests-1`, `elegance-undecided-ending-unasserted` (both 2–1 in favour) and the weaker `warning-logic-2`.

Ruling 2 changed three endings of a call from a `Proved` entry. Reading the patch hunk, the pre-commit code was `if entry_verdict = SOME Proved then if verdict = Proved then () else loud_guard_warning …`, so: a refuter's verdict went loud → silent (probe wrapped, `assert_loud … 0` at :389), the judge's `Unprovable` stayed loud with new text (probe wrapped, `assert_loud … 1` at :638), and an `Unknown` ending went loud → the ordinary undecided-guard warning (probes at :398 and :431 got only rewritten comments). Those two probes assert on the `guard_decision` record and the store, both of which `reasoners.ML:1513-1521` writes independently of the warning block. The consequence is concrete rather than invented: restoring the condition to `… andalso (judge_answer = SOME "Unprovable" orelse verdict = Unknown)` — a partial revert to the shape the file had one commit ago — leaves the whole smoke theory green while reinstating the shouting the ruling removed.

Two caveats for whoever does it, which is why I leave the shape to the drafter rather than prescribing the round-one patch:
- `warnings_of` installs `Private_Output.warning_fn` and swallows everything it captures. Wrapping the probe at :431 as-is would hide that probe's two unconditional dropped-lemma warnings (ruling 3) from the human reading the output panel. Either count a second prefix (`"Fail to prove or falsify the following guard condition"`, and optionally the dropped-lemma prefix) and re-emit what was captured, or leave :431 alone and wrap only :398.
- The undecided-guard warning goes through `Phi_Reasoner.warn_pretty … 1`, which is live here only because the theory declares `\<phi>trace_reasoning = 3`; an assertion on it silently depends on that declaration, so say so in a comment.

This is a strengthening of apparatus the diff itself introduced, not a demand for new machinery. It is not a blocker: the code is correct today, and the theory is deliberately in no ROOT.

## Rejected findings

- `ml-correctness-judge-answer-display-string`, `warning-logic-1`, `elegance-judge-answer-stringly-typed` (three filings of one claim) — the `judge` field is a report label produced 40 lines above its consumer inside one `let`, its sibling `refuter` is a string by the same design, the two literals are pinned by the signature comment and by seven `expect` tuples in the smoke theory, and the only failure offered is a future rename that those tuples would break loudly.
- `warning-logic-2` — subsumed by D1; filed as "no probe asserts the undecided warning at all", which overstates a gap that is really about the one ending the ruling moved.
- `warning-logic-3` — asks to print the entry's verdict on the level-2 trace line, i.e. to re-announce on a user-visible channel exactly the distinction ruling 2 removed for those endings; also `\<phi>trace_reasoning` defaults to 0, so nothing is lost on a default run.
- `ml-correctness-comment-can-equal-record-marker`, `event-log-format-comment-equals-marker` — `comment cat "record"` does emit the marker bytes, but comments are discarded by both readers by design in every case, no record is ever damaged, `Event_Log.comment` has no caller in the tree, and both proposed fixes (a magic-string special case, or changing the on-disk marker) are worse than the wording imprecision they cure.
- `event-log-format-torn-marker-eats-predecessor` — real reader behaviour, but no torn file exists among ~595 live logs, a killed buffered write does not tear 1–14 bytes into a fresh stream, and the proposed "drop everything after the last newline" merely moves the bad window (it would discard a complete final record whose trailing newline was the part lost).
- `event-log-format-test-lost-marker-coverage`, `tests-3`, `elegance-boundary-probe-comment-inaccurate` — the marker is unrepresentable inside an item because `XML.string_of` escapes `<`, which is exactly what the existing `tricky_text` datum exercises; the proposed datum would serialise to `&lt;!-- record --&gt;` and test nothing new, and the temporary probe was already deleted in `7092f6c` after the permanent test ran on the rebuilt heap.
- `event-log-format-duplicate-attributes-split-the-readers` — the four corrupt chunks come from the retired `accounted_timeout_claim` probe; no live encoder collides with a standard key, the line is untouched by the diff, and the proposed `AList.update` merge would silently falsify `category`/`task` instead of producing a visible bad chunk.
- `tests-2` — the identical `warnings_of` shape was already adjudicated "true and negligible… optional hygiene" for auto_sledgehammer's test; the theory is in no ROOT and the loud warning is emitted inline on the probe's own thread, so nothing the probe does can race it.
- `tests-4` — targets `ai-artifacts/Event_Log_Marker_Probe.thy`, which does not exist: deleted in `7092f6c`, and never part of the reviewed patch.
- `tests-5` — I traced the codec: truncation raises `Subscript` from `Word8VectorSlice.subslice`, every ill-formed or pre-delta payload raises `Unpack` (the old `packPair`'s 0x92 fails `unpackTuple3`'s `expect (fixArray 3)`), so the narrowed handler covers what its inputs can produce; the fix would export the private codec, puncturing the signature's "read and written through these two functions only".
- `elegance-orphan-signature-comment` — the duplication predates the diff, which updated *both* copies in lockstep; the `guard_decision` record schema is an externally observable artifact and the contract block is a defensible home for it.
- `elegance-record-marker-not-exported` — the marker is a cross-language wire constant with deliberate copies in both Python readers; a format test that writes the literal bytes is the correct shape, and exporting `record_marker` would hand every downstream client the boundary string to splice in by hand.

## Notes

- Elegance, weighed as instructed: the shape I looked hardest at is the warning dispatch, and it is good — one site, one `if`/`else if`/`else`, the invariant stated in three lines of comment directly above it, and the old per-ending explanatory string deleted rather than reworded. The `judge`-as-string objection came back three times and I rejected it three times: the record's real convention is that the field driving the store write (`verdict`) is a datatype while the two "how did we get here" fields (`refuter`, `judge`) are report text, and typing one of the pair would break that symmetry rather than restore one.
- One wording residue I am *not* raising as a finding, for the record: `event_log.ML:14-15` ("The marker cannot occur inside an item") and `:173-174` ("so the invariant cannot be violated") argue only about an item's interior. Two degenerate cases sit outside that argument — a comment body that *is* the word `record`, and a write torn part-way through the marker. Both are harmless today (verified: no record is ever lost in either case), and both proposed code fixes were worse than the prose. If you ever revisit the header, the precise statement is "the marker never occurs inside an item, and no complete item equals it."
- Nothing in this review touches the eight rulings themselves; where a finding argued against a ruling (notably the request to surface the entry's verdict on the trace line) I rejected it on that ground alone.
