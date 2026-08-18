# The four word-glyph clipboard plans: order, decisions, conventions, state

`phi_word_clipboard.bsh` in this directory makes phi-System's word glyphs survive the
clipboard. Four plans extend it. This file is the index: it records the order they are
implemented in, the decisions the user has taken, the conventions all four share, what has
been reviewed, and what is still open. Read it before picking up any single plan — each
plan is self-contained about *its* work, but none of them carries the cross-cutting state.

**Plan 1 has landed.** `phi_word_clipboard.bsh`, `test_word_clipboard.bsh`,
`run_word_clipboard_test.sh` and `fonts/WORD_GLYPHS.md` carry it; plans 2, 3 and 4 are
still documents. Line citations into `phi_word_clipboard.bsh` taken before that commit
are stale — the file was rewritten.


## The problem, in three sentences

phi-System declares 135 Isabelle symbols whose code points lie in the Unicode Private Use
Area, U+E000..U+E086; each draws a whole keyword as one wide glyph. A private-use code point
means only what the drawing font says, so handing one to another application yields a blank
box, and `phi_word_clipboard.bsh` therefore **expands** a glyph into the mathematical letters
it draws on the way out, and **folds** those letters back into the glyph on the way in.
Everything below is about routes where that conversion does not happen, or happens wrongly.


## The four plans, in implementation order

| # | Plan | What it does |
|---|------|--------------|
| 1 | `WORD_BOUNDARY_PLAN.md` **(landed)** | Rewrites `phi_word_expand` and `phi_word_fold`: marks word boundaries with `U+2060`, and replaces the interpreted per-character loops with compiled-regex ones. |
| 2 | `PRIMARY_SELECTION_PLAN.md` | Wraps jEdit's `%` register so the X11 primary selection (mouse-select, middle-click) converts too. |
| 3 | `SEARCH_FIELD_PASTE_PLAN.md` | Wraps the transfer handler of jEdit's text input fields so pasting a copied glyph into the Find box matches the buffer. |
| 4 | `DRAG_AND_DROP_PLAN.md` | Installs a transfer handler on every buffer text area so drag and drop converts. |

**Why this order.** Plan 1 is a hard prerequisite: the other three call the two functions it
rewrites, and it creates the top-level `phi_t` all three of them assume. Plans 2, 3 and 4 are
independent of each other — different hook points, different acceptance paths — so their
relative order is a judgement, made on how much of each can be proved without a running
jEdit. Plan 1 has no UI hook at all and is fully covered by the automated test. Plan 2 swaps
one register object at startup. Plan 3 adds a global AWT listener whose handler is a pure
delegate. Plan 4 is the largest, touches every EditPane, and leans hardest on manual checks.

**Finish each step before starting the next**, and do not batch the manual checks: all four
modify the same file and the same test, so a fault found after two steps have landed is much
harder to attribute. Each step ends with its automated test passing, its manual checks run by
the user, its `fonts/WORD_GLYPHS.md` edit applied, and a commit in `contrib/phi-system` plus
a pointer bump in the super-repo.


## Decisions the user has taken

These are settled. A plan that contradicts one of them is wrong, not a proposal.

1. **The boundary marker is `U+2060 WORD JOINER`**, not `U+200B` — it is the non-breaking
   one, so two adjacent words still look adjacent in the receiving application.
2. **A joiner is inserted only between two directly adjacent word glyphs.** Two wider
   variants were measured and rejected. What the narrow rule leaves unrepaired is documented
   as a known limit, not fixed.
3. **Folding strips every `U+2060` unconditionally**, inside `phi_word_fold` itself rather
   than in a helper each consumer must remember to call. `U+2060` is not the code point of
   any Isabelle symbol and appears nowhere in the sources, so removing it costs nothing.
4. **What counts as one run is the mathematical alphanumeric block plus `.` and `_`** — a
   deliberate widening of the shipped rule, which today asks whether a character appears in
   the table. See "A deliberate widening" in plan 1: the narrow behaviour is an artefact of
   the current word list and flips silently when a word is added.
5. **The input-field wrapper covers every `HistoryTextField` / `HistoryTextArea` subclass**,
   including the file browser's fields and Isabelle's Query and Debugger panels.
6. **jEdit's own stale-`dragSource` defect is not repaired.** Plan 4 works around it and
   documents it; reaching into another project's private static is out of scope.
7. **The wrong comment at `phi_word_clipboard.bsh:158-159` is corrected**, by plan 1.
8. **The fold's run pattern requires at least one mathematical letter in a run.** Without it
   `.` and `_` — run-forming because of the `size_t` and `w.r.t.` entries — make every full
   stop in ordinary source a run of its own. Measured: about 4.5 times faster on real source,
   with byte-identical output. Going further and requiring an actual table word in the run is
   measurably worse; plan 1 says why, with the numbers.
9. **Expansion is one `Matcher` pass**, not a joiner `replaceAll` followed by one
   `String.replace` per distinct glyph. Measured: 102 ms against 563 ms over 5 million
   characters, with byte-identical output.


## Conventions every plan follows

- **Prefix every new BeanShell name with `phi_`, method locals included.** Startup scripts
  share one global namespace, and a method assigning a bare name writes through to an
  existing global of that name. This is measured, not folklore: the committed test passes
  today only because two such write-throughs cancel out.
- **Never write an invisible or unrenderable character into a source file or a plan.**
  Construct it — `new String(Character.toChars(0x2060))`. Check afterwards; a literal is
  invisible by definition and `cat -A` is the only way to see it. Both a joiner and four
  private-use characters have already been lost into these documents this way. A scan over
  the private-use area, the `Cf`/`Cc`/`Co`/`Cs` categories and the zero-width characters is
  cheap and should be part of finishing any step.
- **The test suite needs a display.** `phi_word_install` touches
  `org.gjt.sp.jedit.Registers`, whose static initialiser calls `getSystemClipboard()`. This
  is true of the committed suite today. Plan 1 makes `run_word_clipboard_test.sh` use
  `xvfb-run`, and also makes it fail on a load error — the interpreter prints its
  `Evaluation Error` **on stdout**, leaves stderr empty and then **exits 0** (measured), so a
  broken script currently "passes" and no stderr check would notice. The rule that works is
  the absence of the test's own `PASS:` line.
- **Never test against the live X11 display.** Writing the real primary selection would
  clobber whatever the user has selected.
- **BeanShell's own errors escape every guard.** An unbound name or an unresolved method is
  an `EvalError` that neither `catch (Exception)` nor `catch (Throwable)` intercepts inside
  bsh. No runtime guard can catch them; only loading the whole script in the test can.
- **Line citations into `phi_word_clipboard.bsh` go stale after plan 1**, which rewrites both
  functions and the header comment. Refresh them when implementing plans 2, 3 and 4.


## What has been reviewed, and how

Every plan has been through at least one two-turn adversarial review: three reviewers with
different lenses (source accuracy, does-it-run, consequences) find problems independently,
then cross-examine each other and vote findings out. Roughly 230 findings were raised across
the rounds and about 110 survived cross-examination and were applied.

| Round | Target | Raised | Survived |
|-------|--------|--------|----------|
| 1 | drag plan, revision 2 | 26 | 14 |
| 2 | drag plan, revision 3 | 29 | 14 |
| 3 | `WORD_BOUNDARY_PLAN.md` | 33 | 19 |
| 4 | `PRIMARY_SELECTION_PLAN.md` | 29 | 14 |
| 5 | `SEARCH_FIELD_PASTE_PLAN.md` | 28 | 13 |
| 6 | all four, cross-plan | 40 | 20 |
| 7 | all four, audit of round 6's fixes | 47 | 15 |

Two failure modes recurred often enough to be worth naming, because they will recur again:

- **A fix landing in the prose but not in the numbered steps, the code sketch or the test
  bullets.** Round 6 caught three of these. Verify a fix by grepping for the *old* wording,
  not by re-reading the new.
- **A measurement whose corpus is not stated is not a measurement.** Round 7's largest
  finding was of this kind: plan 1's speed figures came from a synthetic text ten times
  denser in glyphs than the real sources, two statements of the same quantity disagreed by a
  factor of four, and a claim that ordinary text costs nothing was false because `.` and `_`
  are run-forming. Every figure was re-taken on one named corpus. Write the corpus down
  beside the number.
- **Reviewing a single plan cannot catch a shared-step omission.** Rounds 3-5 each read one
  plan; two of the three then forgot the same shared call, and only round 6 saw it. Any
  future review of one plan should be paired with a cross-plan pass.


## What landing plan 1 taught, for the three that follow

- **The three compiled patterns live in the table, not in three top-level names.**
  `phi_word_table` builds them and puts them under `glyph_pat`, `run_pat` and `word_pat`,
  so a table and its patterns cannot disagree — whichever table a caller passes, the
  patterns used are that table's own. The plan's wording said "compiled once at top
  level"; this is the same thing done in the one place that makes the pairing an
  invariant rather than a convention.
- **The glyph class is derived from the table's own lowest and highest code point.** A
  private-use character outside that span — a Powerline or Nerd-font glyph in the buffer
  — is not a word and never receives a joiner. The run class is *not* derived: it is the
  fixed convention of decision 4, and the test fails if an entry ever spells with an
  ASCII character it does not cover.
- **"No `PASS:` line" is not enough on its own.** It catches an error anywhere before the
  summary line and nothing after it: **measured**, a stray unbound name appended to the
  test made the suite exit 0. The runner now also fails when the output carries
  `Evaluation Error`, `Script threw exception` or `InterpreterError`. Both checks tested,
  with the fault placed before and after the summary.
- **A test that cannot fail is worth nothing, so make it fail on purpose.** Four
  deliberate mutations were run against the finished code: joiner insertion removed (5
  failures), joiner strip removed (8), the run pattern's mathematical-letter requirement
  removed, and the glyph class widened to the whole private-use area. The third one
  **passed** at first — its output is byte-identical and only its speed differs — so two
  assertions were added that pin the patterns themselves ("punctuation alone is not a
  run", "a private-use character past the table is not a glyph"). Plans 2, 3 and 4 have
  the same hazard wherever a change is invisible in the output.
- **Both text functions were re-measured after landing, on the real corpus**: 5 million
  characters expand in 108 ms and fold in 376 ms, against 20.9 s and 41.2 s for the code
  they replaced. And the round trip over that corpus equals folding the source as it
  stands — copying source out and pasting it back introduces nothing of its own.


## Open items

- **Round 7's audit was launched before decision 4** and reported the widened run class as a
  defect; that part is superseded by the decision and was dismissed. Its remaining findings
  were applied. Its most substantial one became decision 8 above: the widening was fine, but
  the plan's claim that "ordinary text never enters the interpreter at all" was false under
  both the old and the new run class, and the performance figures had been taken on a
  synthetic corpus ten times denser in glyphs than the sources are. Every figure in plan 1 was
  re-measured on the real sources, on one corpus, and the table now says which.
- **Not decided, and not part of any plan**: eight `*.unicode.thy` files carry 239
  pre-migration letter-by-letter spellings — 216 `map`, 21 `poison`, and 2 in
  `Phi_System/IDE_CP_Core.unicode.thy`. Copying such a passage and pasting it back converts
  them to the new single symbols, which are **not letters** and so cannot sit inside an
  identifier. See the end of plan 1.
- **Not fixable from a startup script**: HyperSearch's "copy results"
  (`HyperSearchResults.java:791-794`, `:1049-1052`) writes the system clipboard directly,
  bypassing both the register and the service list. Recorded as a known limit.


## Where the numbers come from

Any claim marked *measured* in these plans was produced by running code: jEdit's own
repackaged BeanShell out of `jedit.jar`, under `xvfb-run` when a clipboard or Swing was
needed, or a Python port of the two text functions that was first validated against that
BeanShell — identical failure set over all 18225 ordered glyph pairs, and an identical
checksum over all 18225 outputs. Claims that were read rather than run say so.
