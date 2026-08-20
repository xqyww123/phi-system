# The four word-glyph clipboard plans: order, decisions, conventions, state

`phi_word_clipboard.bsh` in this directory makes phi-System's word glyphs survive the
clipboard. Four plans extend it, and a fifth (`UI_FONT_PLAN.md`) makes phi-System's glyphs
visible in jEdit's own widgets, which is a rendering problem rather than a clipboard one. This file is the index: it records the order they are
implemented in, the decisions the user has taken, the conventions all four share, what has
been reviewed, and what is still open. Read it before picking up any single plan — each
plan is self-contained about *its* work, but none of them carries the cross-cutting state.

**Plans 1, 2 and 3 have landed**, and so has `UI_FONT_PLAN.md`; plan 4 is still a
document. `phi_word_clipboard.bsh`, `test_word_clipboard.bsh`, `run_word_clipboard_test.sh`,
`fonts/PhiSymbols.ttf` and `fonts/WORD_GLYPHS.md` carry them. Line citations into
`phi_word_clipboard.bsh` taken before plan 1 are stale — that plan rewrote the file — which
is why the plans now cite it by function name instead.


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
| 2 | `PRIMARY_SELECTION_PLAN.md` **(landed)** | Wraps jEdit's `%` register so the X11 primary selection (mouse-select, middle-click) converts too. |
| 3 | `SEARCH_FIELD_PASTE_PLAN.md` **(landed)** | Wraps the transfer handler of jEdit's text input fields so pasting a copied glyph into the Find box matches the buffer. |
| 4 | `DRAG_AND_DROP_PLAN.md` | Installs a transfer handler on every buffer text area so drag and drop converts. |
| — | `UI_FONT_PLAN.md` **(landed)** | Merges a text face into `fonts/PhiSymbols.ttf` so a glyph in a search box can be *seen*. Independent of all four: the blank box is live today with none of them landed. Not in the numbered order, because it fixes rendering rather than conversion. |

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
7. **The wrong comment above `phi_service` in `phi_word_install` is corrected**, by plan 1.
   Done: it now states the measured rule, that an anonymous class body as a call argument
   parses when every method in it returns a primitive type.
8. **The fold's run pattern requires at least one mathematical letter in a run.** Without it
   `.` and `_` — run-forming because of the `size_t` and `w.r.t.` entries — make every full
   stop in ordinary source a run of its own. Measured: about 4.5 times faster on real source,
   with byte-identical output. Going further and requiring an actual table word in the run is
   measurably worse; plan 1 says why, with the numbers.
9. **Expansion is one `Matcher` pass**, not a joiner `replaceAll` followed by one
   `String.replace` per distinct glyph. Measured: 102 ms against 563 ms over 5 million
   characters, with byte-identical output.
10. **The UI font is one file, merged into `fonts/PhiSymbols.ttf`** — not a second generated
    font beside it. See `UI_FONT_PLAN.md`.
11. **Monospaced widgets are not supported.** One font carries one design for ASCII; the sans
    text face is merged, so the Search dialog's Find and Replace boxes become proportional
    while the other thirteen wrapped widgets are untouched. The alternative preserved those
    two and
    changed the thirteen.
12. **The GPL material in the Isabelle text face is shipped and disclosed**, as Isabelle
    itself does: 26 blackboard-bold code points from `txmia`/`pxfonts` are copied by the
    merge, and name ID 0
    and `fonts/phi-font-readme.txt` name them. Excluding them was the alternative, rejected
    because they are common in Isabelle mathematics.
13. **The font's name table is written by the generator**, not by `fonts/PhiSymbols.sfd`, which
    is what `UI_FONT_PLAN.md` had said. FontForge is not installed here, so editing the `.sfd`
    alone could not have produced a correct artefact; and the licence obligations come from what
    the merge copies, which is the generator's doing. Name ID 0 reads `Copyright 2023 Qiyuan
    Xu`, and ID 14 points at `github.com/xqyww123/phi-system/tree/main/fonts`.


14. **The generator reads a committed hand-drawn font and writes the artefact**, rather than
    reading its own output. `fonts/source/PhiSymbols-hand-drawn.ttf` is that input, taken from
    commit `f589d323` with its copyright line normalised to `Copyright 2023 Qiyuan Xu`. It is
    never registered and never installed. This reverses `UI_FONT_PLAN.md`'s own rejection of a
    committed pre-merge file, and deletes the undo apparatus that rejection required.
15. **A retired code point is never handed to another word.** A new word takes the code point
    after the highest ever assigned; the high-water mark is a comment line of `symbols-words`,
    which a deletion cannot take with it. The old rule recycled one once already, in this
    repository. `fonts/WORD_GLYPHS.md` states the new rule.
16. **The GPL text shipped is version 2**, unmodified, as `fonts/GPL-2.0.txt`. No upstream
    states a version — CTAN's pxfonts page, the Isabelle component's README and `txmia`'s own
    `/Notice` all say just "GPL" — and the GPL lets the recipient choose when a work names
    none. Name ID 0 also carries the four upstream copyright lines verbatim, because the font
    travels as a bare `.ttf` where a record pointing at a directory finds nothing.
17. **The concept is called the text face, never the base.** In font merging "base" means the
    font you merge *into*, and Isabelle uses it that way for this very file
    (`component_fonts.scala:4`, "DejaVu base + Isabelle symbols"); here it named the font we
    copy *from*. The rename covers the generator, this file, `UI_FONT_PLAN.md`,
    `WORD_GLYPHS.md` and `phi-font-readme.txt` together.

## Conventions every plan follows

- **Declare every function-local with a type, and prefix every name with `phi_`.** The type
  is what makes a local a local: in BeanShell an *untyped* assignment inside a method walks
  the namespace chain and writes through to an existing binding, while a *typed declaration*
  always creates a local (**measured**, both halves). The prefix alone protects only against
  other people's names — it does not stop two functions of the same script from clobbering
  each other's untyped local of the same name, which is exactly how `phi_word_fold` and
  `phi_word_fold_run` came to share one matcher and die with `IllegalStateException: No
  match found` the moment a global `phi_m` existed. **Measured** with every function-local
  name planted as a hostile global before loading: typed locals leave the round trip intact
  and those globals untouched; untyped ones throw on load.
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
- **Cite `phi_word_clipboard.bsh` by name, never by line number.** The file has been
  rewritten four times since the plans were written — plan 1's rewrite, plan 3's addition,
  the code review's fixes, and the font work — and every `bsh:NNN` citation was wrong by the
  end of it, one of them pointing 194 lines away from what it claimed. All of them have been
  replaced by names: a function, or a named thing inside one (`phi_word_fold_run`, the
  `phi_n == 0` guard in `phi_word_install`, the comment above `phi_service`). A name does not
  have to be refreshed by whoever touches the file next. Citations into files this component
  does not own — jEdit's and the JDK's sources — keep their line numbers, since those move
  only when the distribution is upgraded.


## What has been reviewed, and how

Every plan has been through at least one two-turn adversarial review: reviewers with
different lenses find problems independently, then cross-examine each other and vote findings
out. **Raised** is the number of distinct findings turn one produced, pooled over the
reviewers. **Survived** is how many of those a majority of the cross-examiners voted to keep.

560 findings were raised across the fifteen rounds. 217 survived in the twelve rounds where
that figure can still be recomputed; for three of them it cannot, and the table says so rather
than carrying a number.

Round 8 was the first to review **code** rather than a plan. It raised the fewest findings of
any round and it was the most valuable: it found a suite that hung instead of failing, and two
namespace defects in the shipped script that no reader had seen. Reviewers who run and mutate
the thing find defects that reviewers who read it cannot — and rounds 14 and 15 said the same
again, the second of them catching a repair that would have overwritten a committed file on
its first run.

| Round | Target | Raised | Survived |
|-------|--------|--------|----------|
| 1 | drag plan, revision 2 | 26 | 14 |
| 2 | drag plan, revision 3 | 29 | 14 |
| 3 | `WORD_BOUNDARY_PLAN.md` | 33 | 19 |
| 4 | `PRIMARY_SELECTION_PLAN.md` | 29 | 14 |
| 5 | `SEARCH_FIELD_PASTE_PLAN.md` | 28 | 13 |
| 6 | all four, cross-plan | 40 | 20 |
| 7 | all four, audit of round 6's fixes | 42 | 20 (15 applied) |
| 8 | plan 1's landed **code**, three lenses | 23 | 14 (13 applied) |
| 9 | `UI_FONT_PLAN.md`, first version | 38 | 23 |
| 10 | `UI_FONT_PLAN.md`, rewrite | 57 | not recoverable |
| 11 | `UI_FONT_PLAN.md`, third version | 41 | not recoverable |
| 12 | `UI_FONT_PLAN.md`, fourth version | 29 | not recoverable |
| 13 | `UI_FONT_PLAN.md`, fifth version | 25 | 14 |
| 14 | the font merge's landed **code**, four lenses | 39 | 18 |
| 15 | the repair plan for round 14, four lenses | 81 | 34 |

Four rows need a word, and the reason they do is itself a lesson — see "Numbers written down
are not measurements" below.

* **Rounds 7 and 8** carry two figures because two different quantities were recorded under
  one heading. 20 and 14 survived the vote; 15 and 13 were applied, the difference being
  findings superseded by a decision the user took while the round was running (round 7) and
  one the author judged already covered (round 8).
* **Rounds 10, 11 and 12** cannot be recomputed at all: all three reviewers numbered their
  findings `F1`, `F2`, `F3`…, the ids collide, and the cross-examiners namespaced them
  inconsistently, so any rule silently merges three reviewers' `F1`s into one. The three rows
  used to read 19, 19, 19; nothing in the records produces that, and 19 is traceable to a
  different round's misreported figure. Re-deriving them means matching about 127 findings by
  content, which nobody has done.
* **Round 13** ran with two reviewers rather than three, after a crash was resumed from cache.
  Its "Raised" is therefore two reviewers' output, not three.
* **Rounds 14 and 15** used four lenses rather than three; "a majority of the cross-examiners"
  is four voters there, not three.

Two failure modes recurred often enough to be worth naming, because they will recur again:

- **A fix landing in the prose but not in the numbered steps, the code sketch or the test
  bullets.** Round 6 caught three of these. Verify a fix by grepping for the *old* wording,
  not by re-reading the new.
- **Compare data, not pixels, whenever the property is about data.** Of the eleven blocking
  findings across the font plan's five review rounds, **five were assertions that fail on a
  correct build**, and they came from one source: checking "the glyphs were copied unchanged" by
  rendering them. `stringWidth` and `getStringBounds` answer differently with fractional metrics
  on or off, the differing set moves with the point size, and Java2D's default antialiasing hint
  behaves as *off*. Comparing `glyf` bytes and `hmtx` integers is exact, configuration-free and
  far faster. Rendering checks should be coarse — *does it draw ink* — where nothing can flip.
- **A plan is not a measurement archive.** The same font plan carried about forty measured
  figures, and three consecutive rounds were spent on figures that went stale when a rule
  changed. Keep a number only where a decision hangs on it; put the rest in the commit message.
- **Diminishing returns are real, and they turn negative.** Rounds 11 and 12 of that plan found
  mostly wounds inflicted by round 10's and 11's own fixes. Plan 1's experience points the same
  way: seven review rounds missed two defects that the first day of implementation found.
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


## What landing plan 3 taught

- **A scripted BeanShell class is not the way to subclass a Java class here.** Its
  constructor is not found when a parameter has no declared type, and the anonymous subclass
  bsh generates instead has **only a no-arg constructor**: it does not forward arguments, so
  `new javax.swing.TransferHandler("phi") { ... }` fails exactly like the scripted class did.
  `new javax.swing.TransferHandler() { ... }` works, reaching the superclass's protected
  no-arg constructor. `DRAG_AND_DROP_PLAN.md` subclasses `TextAreaTransferHandler` the same
  way and will meet this; its sketch already binds the object to a name, which is right, but
  it must not grow a constructor.
- **Idempotence is marked on the component, not read off the wrapper's type.** jEdit resets
  the BeanShell class manager when a plugin is unloaded (`PluginJAR.uninit`), after which a
  fresh class object would make an `instanceof` test answer "not ours" and wrap a second
  time — a wrapper around a wrapper, folding twice. A client property on the field cannot
  drift that way.
- **Six mutations were run against the finished field-paste code** — rich flavor ignored,
  folding disabled, the idempotence guard removed, the listener never registered, `canImport`
  not forwarded, the inner handler's `importData` never reached — and the suite catches all
  six.


## What the code review of plan 1 taught

Three reviewers with different lenses read the landed code, ran it, and mutated it. The
findings that survived cross-examination were all of one family — **the tests could not fail
where it mattered** — and the two production defects they found were both of the namespace
kind this file's conventions are about.

- **A test that hangs instead of failing is worse than no test.** The suite's own helper
  `hex()` used untyped locals `b`/`i`/`c`, so it reset the loop counter of the two checks
  that call it. Forcing either to fire printed the same FAIL line for ever: **measured**,
  1,728,919 lines and 135 MB in 30 seconds, and through the runner — which buffered stdout
  into a variable — not one character reached the terminal. The runner now has a timeout, it
  streams to a file, and it truncates a runaway log.
- **Mutate the parts nobody thought to mutate.** The author's own mutation testing covered
  the two text functions and found the suite sound. The reviewers mutated the *installation*
  and the *generated table* instead: swapping copy and paste — the feature exactly inverted —
  still passed, and so did deleting a word from `word-clipboard-text` while `symbols-words`
  still named it. Both now fail. Before trusting a suite, ask which part of the code no
  mutation has ever touched.
- **An invariant that only holds because of an accident of the data is not an invariant.**
  The glyph class is the table's own span, so a code point retired by deleting a word from
  `words.txt` still matched it; expansion marked a boundary beside that non-word because it
  emitted the marker before looking the word up. It now looks up first.
- **Pin what cannot show up in the output.** Dropping `Pattern.quote` from the alternation
  passed every check, and then `w.r.t.` became a pattern whose `.` matches anything.


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


## What landing the font plan taught

- **The four checks only a running editor can answer all passed** (2026-08-20): a word glyph
  selected in the buffer arrives in the Find box drawn as in the buffer; ordinary paths and
  English in the other fields are unchanged; the text area is unchanged at the default
  `view.antiAlias=subpixel HRGB`; and the UI font size behaves as the plan predicted.
- **A check that compares font data instead of pixels found seven distinct defects on its
  first run, and none of them was a false alarm.** The five review rounds spent on rendering
  assertions produced the opposite: five blocking findings that were assertions failing on a
  correct build. The rewrite that replaced them cost about a page of text.
- **A derived field is not part of "copied unchanged".** The first version compared compiled
  glyph bytes, and 52 of the text face's glyphs failed: it stores bounding boxes one unit
  looser than the outline, and fontTools recomputes them on save. Turning the recomputation
  off is not the fix — `recalcBBoxes=False` also switches off `maxp.recalc()`, which is what
  keeps `maxPoints` and `maxContours` correct, and those being too small is the same class of
  failure as the hinting maxima. The comparison dropped the bounding box instead.
- **Every check was shown to fail before it was believed.** Eight deliberate breakages, each
  damaging exactly one thing, each refused by the run: no deep copy, unscaled STIX advances,
  unscaled STIX outlines, the text face winning phi's two code points, the blank glyph not
  supplied from STIX, `prep` left behind, a supplementary code point in a format 4 subtable,
  and an undamaged build that must pass.


## Numbers written down are not measurements

The review table above was audited against the records the rounds actually produced. Five of
its thirteen rows were wrong, and every one of the wrong ones had been written down by hand
from a report rather than recomputed. This is worth keeping because the habit it names is
cheap to repeat and hard to notice.

- **A row was fabricated by copy-paste.** Round 8 appeared twice, because two sessions each
  recorded the same review without seeing the other's row, and the second one's figures --
  `38 | 22` -- turned out to be a verbatim copy of round 9's pair, written in the same edit.
  Neither number had ever been measured.
- **A figure survived a change of the thing it counted.** "Roughly 270 findings ... about 120
  survived" was exactly right for the eight-row table it was written against, and stayed in
  place while five more rows were added.
- **A count in prose outlived its derivation.** `UI_FONT_PLAN.md` claimed "five of the eleven
  blocking findings across five review rounds"; the eleven came from a brief written after
  *four* rounds, and no set of eleven blocking findings exists in the records at all.
- **A measurement was quoted for a different quantity.** "52 of the text face's glyphs" was a
  count of failing checks. The number of glyphs is 46; the other differences are 180
  composites, which differ for an unrelated reason.
- **Two rounds' figures are simply gone**, because their reviewers all numbered findings
  `F1`, `F2`, `F3` and the ids collided. An identifier chosen for convenience inside one
  agent's output destroyed the ability to count across agents.

What follows from all five: **re-derive a figure at the moment you write it down, or write
down that you cannot.** "Not recoverable" in a table is worth more than a plausible number,
and it is the only honest thing to put where nobody can check.


## Where the numbers come from

Any claim marked *measured* in these plans was produced by running code: jEdit's own
repackaged BeanShell out of `jedit.jar`, under `xvfb-run` when a clipboard or Swing was
needed, or a Python port of the two text functions that was first validated against that
BeanShell — identical failure set over all 18225 ordered glyph pairs, and an identical
checksum over all 18225 outputs. Claims that were read rather than run say so.
