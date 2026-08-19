# The four word-glyph clipboard plans: order, decisions, conventions, state

`phi_word_clipboard.bsh` in this directory makes phi-System's word glyphs survive the
clipboard. Four plans extend it, and a fifth (`UI_FONT_PLAN.md`) makes phi-System's glyphs
visible in jEdit's own widgets, which is a rendering problem rather than a clipboard one. This file is the index: it records the order they are
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
7. **The wrong comment at `phi_word_clipboard.bsh:158-159` is corrected**, by plan 1.
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
    base is merged, so the Search dialog's Find and Replace boxes become proportional while the
    other thirteen wrapped widgets are untouched. The alternative preserved those two and
    changed the thirteen.
12. **The GPL material in the Isabelle base is shipped and disclosed**, as Isabelle itself does:
    26 blackboard-bold code points from `txmia`/`pxfonts` are copied by the merge, and name ID 0
    and `fonts/phi-font-readme.txt` name them. Excluding them was the alternative, rejected
    because they are common in Isabelle mathematics.
13. **The font's name table is written by the generator**, not by `fonts/PhiSymbols.sfd`, which
    is what `UI_FONT_PLAN.md` had said. FontForge is not installed here, so editing the `.sfd`
    alone could not have produced a correct artefact; and the licence obligations come from what
    the merge copies, which is the generator's doing. Name ID 0 reads `Copyright 2023 Qiyuan
    Xu`, and ID 14 points at `github.com/xqyww123/phi-system/tree/main/fonts`.


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
- **Line citations into `phi_word_clipboard.bsh` go stale after plan 1**, which rewrites both
  functions and the header comment. Refresh them when implementing plans 2, 3 and 4.


## What has been reviewed, and how

Every plan has been through at least one two-turn adversarial review: three reviewers with
different lenses (source accuracy, does-it-run, consequences) find problems independently,
then cross-examine each other and vote findings out. Roughly 270 findings were raised across
the rounds and about 120 survived cross-examination and were applied. Round 8 was the first
to review **code** rather than a plan, and it was the most productive of the eight: reviewers
who run and mutate the thing find defects that reviewers who read it cannot.

| Round | Target | Raised | Survived |
|-------|--------|--------|----------|
| 1 | drag plan, revision 2 | 26 | 14 |
| 2 | drag plan, revision 3 | 29 | 14 |
| 3 | `WORD_BOUNDARY_PLAN.md` | 33 | 19 |
| 4 | `PRIMARY_SELECTION_PLAN.md` | 29 | 14 |
| 5 | `SEARCH_FIELD_PASTE_PLAN.md` | 28 | 13 |
| 6 | all four, cross-plan | 40 | 20 |
| 7 | all four, audit of round 6's fixes | 47 | 15 |
| 8 | plan 1's *code*, as committed | 38 | 22 |
| 9 | `UI_FONT_PLAN.md`, first version | 38 | 22 |
| 10 | `UI_FONT_PLAN.md`, rewrite | 57 | 19 |
| 11 | `UI_FONT_PLAN.md`, third version | 41 | 19 |
| 12 | `UI_FONT_PLAN.md`, fourth version | 29 | 19 |
| 8 | plan 1's **landed code**, three lenses | 36 | 13 |

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


## Where the numbers come from

Any claim marked *measured* in these plans was produced by running code: jEdit's own
repackaged BeanShell out of `jedit.jar`, under `xvfb-run` when a clipboard or Swing was
needed, or a Python port of the two text functions that was first validated against that
BeanShell — identical failure set over all 18225 ordered glyph pairs, and an identical
checksum over all 18225 outputs. Claims that were read rather than run say so.
