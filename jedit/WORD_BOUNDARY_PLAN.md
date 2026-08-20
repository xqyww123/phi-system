# Making a word glyph survive the clipboard when another glyph is written against it

Read `WORD_CLIPBOARD_PLANS.md` beside this file first: it carries the implementation
order, the decisions the user has settled, the conventions all four plans follow, and what
has already been reviewed.

A work plan, and the **first** of four — `DRAG_AND_DROP_PLAN.md`,
`PRIMARY_SELECTION_PLAN.md` and `SEARCH_FIELD_PASTE_PLAN.md` all reuse the two functions
this one rewrites, so this goes in before any of them. Read `../fonts/WORD_GLYPHS.md`
first; it defines the feature all four extend.

**Convention.** A claim marked *measured* was produced by running code — jEdit's own
repackaged BeanShell out of `jedit.jar`, or a Python port of `phi_word_expand` and
`phi_word_fold` validated against that BeanShell first (identical failure set over all
18225 ordered glyph pairs, and an identical checksum over all 18225 outputs). Everything
else was read.


## The defect

`phi_word_clipboard.bsh` carries a word glyph across the clipboard by **expanding** it —
replacing the single private-use character with the mathematical letters it draws — and
brings it back by **folding** those letters into the glyph again. Expansion is lossy at the
edges: it throws away the fact that a word ended where it did. Folding then has to guess
the boundaries, which it does by scanning a run left to right, taking the longest table
word that matches at each position, and abandoning the whole run when it meets a
mathematical letter no word claims (`phi_word_fold_run`).

Guessing wrongly is possible. Write `\<change>\<do>` with nothing between them: expansion
gives eight letters, `changedo`; the scan finds `changed` at position 0 — a word in its own
right, longer than `change`, so it wins — then a lone `o` that no word claims, which
abandons the run. Both glyphs come back as letters.

In one case the mis-parse consumes everything and produces a clean, wrong answer:
`\<or'>\<else>` expands to `orelse`, `orelse` is itself a word, and the text comes back as
the single symbol `\<orelse>`. **The text has changed meaning, silently.**

### How much of this there is

**Exactly 51 sequences**, 49 of two glyphs and 2 of three. Cross-checked three ways: the
real BeanShell over all 18225 ordered pairs, the validated Python port agreeing on every
one, and a brute force over the 236925 triples whose first glyph is one of the 13 words
that could possibly begin a failure.

Only a word that is a **proper prefix of another table word** can begin a failure, because
the greedy scan always matches at least the word itself, so a divergence needs a strictly
longer word starting at the same place. Thirteen words have that property — `in`, `change`,
`get`, `has`, `no`, `or`, `prem`, `ref`, `ret`, `size`, `subj`, `val`, `var` — and in fact
only **eight** of them begin one of the 51: `change`, `has`, `in`, `no`, `or`, `subj`, `val`
begin the 49 pairs and `prem` begins the two triples. `get`, `ref`, `ret`, `size` and `var`
begin none.

**No minimal failing sequence is longer than three glyphs.** A minimal failure spanning k
glyphs needs the greedy match at position 0 to run past glyph k-1 — if it stopped inside
glyph k-1 the shorter prefix would already fail and the sequence would not be minimal — so
the overshooting tail must cover glyphs 2..k-1 entirely and reach into glyph k. The longest
tail is 5 letters (`var`→`variable` gives `iable`, `in`→`initial` gives `itial`), the
shortest word is 2 letters, and neither `ia` nor `it` is a word, so a tail cannot cover two
whole words. Four is impossible.

**But one failing sequence damages every glyph in the same run.** "Minimal sequence" is not
"blast radius": because `phi_word_fold_run` returns the *entire* run when it abandons, one
bad pair takes all its neighbours down with it. **Measured**: eight `\<by>` glyphs followed
by `\<has>\<has>` — ten adjacent glyphs whose only bad pair is the last two — come back as
22 mathematical letters with no glyph surviving. The fix repairs all ten.

Of the 51 failing sequences, **exactly one** is the **clean-but-wrong** kind
(`\<or'>\<else>` → `\<orelse>`): a different glyph comes back and nothing looks wrong. The
other 50 come back as mathematical letters, which is the **visible** kind. Those two names
are used for these two kinds throughout this plan and nowhere else.

### How much of it is reachable today: none

Every phi-System source file was decoded to real code points — resolving `\<name>` escapes
through Isabelle's `etc/symbols` (412 symbols), this component's `symbols` (50) and
`symbols-words` (135) — and scanned. **Measured**, over the 369 `.thy`/`.ML`/`.sml`/`.sig`
files of `contrib/phi-system` carrying 14719 word glyphs (an earlier pass of this scan
counted 371 files and the same 14719 glyphs; the tree is shared and moves under us, and every
count below reproduced exactly when the scan was repeated):

```
two word glyphs written directly against each other : 0
a word glyph written directly against a math letter : 0
a word glyph written directly against `.` or `_`    : 2   (both harmless: ASCII passes through)
```

So this is a latent defect, not a live one. It is worth fixing anyway for a reason that has
nothing to do with today's sources: **the 51 sequences are a function of the table, and the
table grows.** Adding one word to `words.txt` can create a new prefix relationship with a
word that *is* commonly written against its neighbour. The fix below removes the
directly-adjacent class permanently, so no future addition can reintroduce it.


## The fix: stop guessing, mark the boundary

The information is destroyed during expansion, so it is restored during expansion.

**On the way out**, when two word glyphs are written directly against each other, emit a
`U+2060 WORD JOINER` between their expansions.

**On the way back**, the joiner is not a run-forming character — it is outside the
mathematical alphanumeric block and it is neither `.` nor `_` — so it already ends a run:
each expansion folds in isolation and cannot merge with its neighbour. Folding
then **strips every `U+2060` from its result** as its last step.

### Why "strip every joiner", and why that is not a new function

An earlier draft removed a joiner only when a neighbour had folded into a glyph, so as not
to delete one a user had pasted in from elsewhere. That conditional is both unnecessary and
broken:

* **Unnecessary.** `U+2060` is not the code point of any symbol in Isabelle's `etc/symbols`,
  this component's `symbols`, or `symbols-words`, and it appears nowhere in the 369 source
  files (**measured**). It has no legitimate role in Isabelle source, so removing it costs
  nothing.
* **Broken.** When two adjacent glyphs have the user's own mathematical letters on *both*
  sides, neither expansion folds — the outer letters widen each run past the expansion and
  the abandon rule fires — so neither neighbour is a glyph, the conditional does not fire,
  and **an invisible character is written into the `.thy` buffer** where today's code leaves
  none (**measured**: `𝐳𝐳𝐳\<has>\<has>𝐳𝐳𝐳` comes back with the joiner still in it). That is a
  new failure, not a missing repair.

Stripping unconditionally fixes it: **measured**, the same input comes back as
`𝐳𝐳𝐳𝐡𝐚𝐬𝐡𝐚𝐬𝐳𝐳𝐳` with no joiner, character-for-character what today's code produces.

Because the strip is unconditional it belongs **inside `phi_word_fold` itself**, as its
final step. There is then no separate helper and no list of call sites to keep in step —
every present and future consumer of `phi_word_fold` gets it automatically. This matters:
of the three sibling plans written before this one, two forgot to call the helper that an
earlier draft of this plan proposed.

### Why `U+2060` and not `U+200B`

Both are invisible and zero-width. `U+200B ZERO WIDTH SPACE` also offers a **line-break
opportunity**, so a pasted `\<or'>\<else>` could wrap between `or` and `else` in the
receiving application and no longer look like what was on screen. `U+2060 WORD JOINER` is
the non-breaking one, and the two words were adjacent on screen, so it is the faithful
choice.

### The insertion condition, and why it stops there

**A joiner goes in exactly when the previous character of the source text was also a word
glyph.** Nothing else triggers one: not a glyph against the user's own mathematical letters,
not a glyph against `.` or `_`.

Two wider variants were measured. Inserting also next to any adjacent mathematical letter
would additionally repair 23 of the 26 sequences in which a glyph meets the user's own
mathematical letters; inserting next to any run-forming character would repair 24 of those
and the 9 in which two glyphs are separated by `_`. All three
variants score identically on the directly-adjacent class this plan targets — 135/135 single
glyphs and 18225/18225 adjacent pairs. The narrow rule was chosen and is kept; what it
leaves alone is listed under "What this plan does not cover", where it is left **exactly as
it is today**.


## The other half of the rewrite: both functions become compiled-regex driven

The two functions are today interpreted per-character loops. **Measured** in jEdit's own
BeanShell, an interpreted step costs about **3.5 microseconds**, because every
`codePointAt`, `charCount`, `HashMap.get` and `append` is a reflective dispatch rather than
a compiled call.

**Every figure below was taken on one corpus, and it is the real one**: all 369
`.thy`/`.ML`/`.sml`/`.sig` files of `contrib/phi-system` concatenated and decoded to real
code points — 6,613,699 characters carrying 14719 word glyphs, one glyph per 449
characters. The fold rows read that same text after expansion, which is exactly what comes
back when somebody copies source out to another application and pastes it back. An earlier
draft of this plan quoted figures from a denser synthetic corpus and called one glyph per 46
characters "phi-System's own glyph density"; it is not, it is about ten times denser than the
sources are.

```
                            today        rewritten
expand 1,000,000 chars     4,162 ms          40 ms
expand 5,000,000 chars    20,939 ms         102 ms
fold   1,000,000 chars     8,829 ms         121 ms
fold   5,000,000 chars    41,158 ms         343 ms
```

Those are the prototype's figures, taken while the plan was written. The landed code was
re-measured on the same corpus and is the same shape: **108 ms** and **376 ms** at five
million characters.

At the scale of one real clipboard operation — phi-System's largest source file is
`Phi_System/Phi_Type.thy` at 543,999 characters — the rewritten functions take about 20 ms
in each direction, where the committed ones take about two and five seconds.

**Two deliberate differences from the committed implementation, and no others.** Expanding
inserts a joiner where two glyphs are written directly against each other, which is the point
of this plan. Folding no longer folds a glyph written against a mathematical character no
table word uses, which is the widened run class described two sections below. Everything else
is byte-identical: **measured**, over the expansions of all 18225 ordered glyph pairs, the
rewritten fold and the committed fold return the same string in 18225 cases out of 18225.

**This is a prerequisite, not an optimisation.** `PRIMARY_SELECTION_PLAN.md` runs
`phi_word_expand` on **every mouse drag-selection**, on the AWT thread; at today's speed a
large selection would freeze the editor for seconds. It also removes a problem that exists
today unnoticed: copying a large glyph-bearing region with Ctrl-C already stalls.

### What makes it fast, so nobody simplifies it back

The bottleneck is not scanning, it is **how often control returns to the interpreter**. Each
return costs about 3.5 µs; a compiled call handles the whole string for one. The rewrite
makes the number of returns proportional to the number of glyphs and of letter runs, never to
the number of characters.

**Expanding is one compiled pass.** A single `Matcher` over `[\uE000-\uE086]` walks the
glyphs. Between matches the text is copied wholesale with `StringBuffer.append(text, from,
to)`, and a joiner is emitted exactly when this match starts where the previous one ended —
which *is* the insertion condition stated above, "the previous character of the source text
was also a word glyph", expressed directly rather than encoded in a lookaround. The character
class stops at the table's actual last code point rather than at the end of the private-use
block, so a joiner is never put beside a private-use character that is not a word glyph — a
Powerline or Nerd-font glyph somebody has in the buffer, say.

> An earlier draft expanded in two passes instead: a zero-width `replaceAll` over
> `(?<=[\uE000-\uE086])(?=[\uE000-\uE086])` to insert the joiners, then one compiled
> `String.replace` per **distinct** glyph present. It returns to the interpreter about as
> rarely, but each `String.replace` copies the whole string, so its cost grows with distinct
> glyphs × length: **measured**, 563 ms against 102 ms over the same 5 million characters
> (111 distinct glyphs in them), with byte-identical output. The single pass is both faster
> and shorter, and it needs no separate scan for which glyphs are present.

**Folding keeps its algorithm and changes only how a position is matched.**
1. A compiled pattern extracts the runs:
   `[\x{1D400}-\x{1D7FF}._]*[\x{1D400}-\x{1D7FF}][\x{1D400}-\x{1D7FF}._]*` — the
   mathematical alphanumeric block plus the two ASCII characters the table uses, **with at
   least one character of the block required**. That requirement is not cosmetic. `.` and `_`
   are run-forming because two entries use them (`size_t` and `w.r.t.`), so without it every
   full stop and every underscore in ordinary source starts a run of its own and returns to
   the interpreter. **Measured** over the corpus above: 199,791 runs per 5 million characters
   without the requirement against 19,093 with it, and folding costs 1,563 ms against 343 ms
   — with **byte-identical output over the whole corpus**, because a run holding no
   mathematical letter is all ASCII and the abandon rule carries unmatched ASCII through
   untouched. The committed implementation has the same weakness, since its own run class
   contains `.` and `_` as well; this is a repair, not a regression.

   The obvious next step is not one: **do not put the 135-word alternation into this
   pattern.** Requiring the run to contain an actual table word, rather than merely a
   mathematical letter, does cut the interpreted calls further — 13,580 against 21,026 over
   the same 5 million characters — but the pattern grows from 69 characters to 2,084, the
   engine tries that whole alternation at every scanning position, and folding takes
   **2,793 ms instead of 343 ms** (**measured**, byte-identical output). Saving returns to
   the interpreter is worth it only while the scan stays cheap.
2. Within a run, the 135 keys become **one compiled alternation**, built longest-first.
   Java's alternation is ordered, so the first alternative that matches at a position is the
   longest — exactly the existing greedy rule, and the reason the outputs are identical. The
   interpreted work per run falls from *positions × 135 `startsWith` calls* to one call per
   word actually matched.
3. The abandon rule is unchanged, and it is consulted at **every** unmatched position in the
   run — before the first match, between matches, and after the last. What it does there is
   also unchanged: unmatched **ASCII** is carried through, an unmatched **non-ASCII**
   character abandons the whole run. The tail matters: the headline example `\<has>\<has>`
   expands to `hashas`, the alternation matches `hash` at position 0 and nothing after it, and
   the abandon is triggered by the trailing `as`.
4. The result has every `U+2060` stripped.

Text with no word glyph in it is never free, but it is cheap enough that **no separate "does
this text contain a glyph" pre-check is needed** — the compiled scan is that pre-check.
**Measured** on the same corpus with every glyph replaced by an ASCII letter, 5 million
characters expand in 23 ms and fold in 206 ms.

### A deliberate widening: what counts as one run

Today `phi_word_fold` decides run boundaries by asking whether a character appears **in the
table** — the 51 distinct code points its 135 entries happen to use, a different 51 from the
51 failing sequences above. The rewrite asks instead whether
the character is in the mathematical alphanumeric block (U+1D400..U+1D7FF) or is `.` or `_`.
That is a change of convention, taken on purpose, and it is a change to shipped behaviour
rather than an implementation detail. It is recorded here so nobody later "fixes" it back.

**What it changes.** One kind of neighbour, in two shapes: a word glyph written against a
mathematical character the table does not use — directly, or with only `.` or `_` between
them, those two being run-forming, so the widened run reaches across them.

**Measured** as a round trip, which is the only way to see it: `\<pending>` followed by a
mathematical bold `q` — no entry spells a `q` — expands to eight letters, and folding those
eight letters gives the glyph back today and leaves them as letters after the change. The
same holds with a `.` or a `_` between the two. Folding the glyph-plus-`q` *directly*
distinguishes nothing, under either rule, because the glyph is not a run-forming character
in the first place.

Nothing else moves, and the claim is scoped: all 135 single glyphs and all 18225 ordered
adjacent pairs behave identically under both rules (**measured**), and across the 369
`.thy`/`.ML`/`.sml`/`.sig` sources there are **0** places where a glyph is written against
such a character (**measured**).

**Why the wider rule is the right one.** The abandon rule exists, in `WORD_GLYPHS.md`'s own
words, because "a mathematical letter that no word claims abandons the whole run untouched,
because the run is then somebody else's bold text and none of it may be modified". By that
purpose, `𝐩𝐞𝐧𝐝𝐢𝐧𝐠𝐪` reads as somebody's bold word and folding half of it into a glyph is
precisely the mangling the rule is there to prevent. The narrow behaviour is not a decision
anyone made — it is an artefact of which letters the current word list happens to use, so
**the same input changes behaviour whenever a word is added to `words.txt`**, silently. The
block is a fixed convention that can be stated in one sentence and cannot drift.

An earlier draft also claimed the block is the faster of the two, on the grounds that it is
one range comparison where the table's own code points need eighteen. That argument is
dropped: how much it is worth depends entirely on the text, it was never re-measured after
the run pattern changed, and speed is not why this choice is made. What does matter for
speed is the "at least one mathematical letter" requirement in the section above, and that
one is independent of this decision — it applies to either class.

**What this obliges.** `WORD_GLYPHS.md`'s description of what counts as one run currently
implies the narrow definition; step 6 of the procedure must update it, and must state the
one behavioural change above rather than letting a user discover it.

### What else must change in the existing file, and why

**Hoist the table to a top-level `phi_t`.** All three sibling plans assume it exists; none
of them creates it. The closures in `phi_word_install` name `phi_t` directly; an earlier
draft kept a local `t = phi_t;` because the closure bodies said `t`, and once those bodies
were rewritten the local was only a hazard — it is the one unprefixed name in the file, and
it overwrites a global `t` belonging to any other startup script that has one.

**Declare every local inside a function with a type.** In BeanShell an *untyped* assignment
walks the namespace chain and writes through to an existing binding, creating a local only
when no binding is found; a *typed declaration* always creates a local (**measured**, both
halves). The prefix alone is not enough, and the difference is not academic: `phi_word_fold`
and `phi_word_fold_run` both used an untyped `phi_m`, so the moment any global of that name
existed — the test grew one — the inner call clobbered the outer matcher and folding died
with `IllegalStateException: No match found`. **Measured** with every function-local name
planted as a hostile global before loading: with typed locals the round trip is intact and
the globals are untouched; with untyped ones the script throws on load. Keep the `phi_`
prefix as well, so a reader sees the intent, but the type is what enforces it.

**Keep the null guards.** Both functions start with `if (text == null) return text;` today.
The rewrite must keep them: the service call site can be reached with null, and **measured**,
a rewritten `phi_word_expand` without the guard throws a `NullPointerException` where the
committed one returns null.

**Make `run_word_clipboard_test.sh` use `xvfb-run`.** `phi_word_install` calls
`Registers.getRegister('$')`, and `org.gjt.sp.jedit.Registers`'s static initialiser calls
`getSystemClipboard()` (`Registers.java:609`). **Measured**: with `DISPLAY` unset the
*committed* script and test already die with `HeadlessException` before a single check runs.
The suite has needed a display all along; make that explicit rather than leaving the next
person to discover it.

**The rewrite invalidates line citations elsewhere.** It changes `phi_word_expand` and
`phi_word_fold` wholesale, adds top-level names and compiled patterns, prefixes the locals in
`phi_word_table`, `phi_word_fold` and `phi_word_fold_run`, and rewrites the header comment.
Every `phi_word_clipboard.bsh:NNN` citation in the other three plans was against the file as
it stood before this rewrite, and went stale with it. They have since been replaced by names
— a function, or a named thing inside one — which is the half of that choice that does not
have to be redone every time the file is touched.

**Never write the joiner character itself into the source.** Construct it as
`new String(Character.toChars(0x2060))`. A literal would be invisible — unreadable,
ungreppable, and easy to lose to a stray copy-paste or an editor that normalises whitespace.
This is not hypothetical: the first draft of this plan lost one that way, and it took
`cat -A` to find it.


## Measured

```
                          single glyph   two adjacent glyphs   three adjacent glyphs
today                       135/135         18176/18225
with the joiner             135/135         18225/18225        2460375/2460375

clean-but-wrong results among adjacent glyphs:  today 1   with the joiner 0
joiners inserted across all 369 source files:   0
```

Every row was re-run against the final shape of the rewrite — the single-pass expansion and
the run pattern that requires a mathematical letter — not against a sketch: 135/135,
18225/18225 and 2460375/2460375 are round trips through those two functions as this plan now
describes them.

Both three-glyph failures are fixed: `\<prem>\<is>\<else>` and `\<prem>\<is>\<entry>` come
back unchanged. `\<orelse>` copied alone still folds to `\<orelse>` — the ambiguity is
removed, not resolved against the single word. Somebody else's bold `𝐬𝐭𝐚𝐭𝐞𝐬` and `𝐳𝐳𝐳` are
untouched.


## What this does and does not make true

**It does** make `WORD_GLYPHS.md`'s promise — that "a round trip through another application
loses nothing" — true for word glyphs written against each other, which it is not today.

**It does not** cover a glyph written against anything that is not another glyph. Those
shapes are listed under "What this plan does not cover". None of them is repaired; one of
them moves anyway, because the run class widens — the section "A deliberate widening" states
that change and it is the only shipped behaviour this plan alters outside the adjacent-glyph
class.

**It does not** make expansion-then-folding the identity on arbitrary text, and is not meant
to. Mathematical letters the user wrote themselves that happen to spell a word still fold
into that word's glyph — literal `𝗆𝖺𝗉` becomes `\<map>`. Note the alphabet: the `map` entry
is drawn from mathematical **sans-serif** letters (U+1D5C6 U+1D5BA U+1D5C9), so the bold
`𝐦𝐚𝐩` an earlier draft printed here would not have folded at all. That is the paste direction's
designed behaviour, documented in `WORD_GLYPHS.md`, and out of scope.

**Where behaviour changes for shapes this plan does not target.** The claim "no better and
no worse" holds only for the single-glyph shapes: **measured**, none of the 405
single-glyph-against-bold-`zzz` cases changes. As soon as two glyphs are involved it changes,
almost always for the better — all 36450 cases of bold letters with two glyphs on one side
differ from today, typically recovering one glyph that today is lost. The one shape that does
**not** move is bold letters on *both* sides of the pair: neither expansion folds either way,
so it comes back as letters before and after. Pin that one in the test, so a later reader
knows it is meant to stay where it is — it is also the case that would leave a joiner in the
buffer if the strip were made conditional.

**Consequence for `DRAG_AND_DROP_PLAN.md`.** That plan keeps a two-slot memory so an
intra-jEdit drag restores the exact original text rather than folding. The memory is still
justified — it rests on a glyph written against mathematical letters no word claims. The
widened run class below changes *which* letters those are, and widens the set, so the memory
has more rather than less to do; its "Correction 2" needs no rewrite. The other consequence
is already applied there: its manual checks 1 and 2 used `\<has>\<has>`, which round-trips
on its own once this lands and would therefore pass even with the memory disabled, and they
now use `\<size>_\<then'>`, one of the nine shapes this plan leaves unrepaired.


## Risks

- **An invisible character can reach other applications.** Only where two word glyphs are
  written directly against each other, which happens nowhere in the current sources
  (**measured**: 0 insertions across all 369 files). Where it does happen, a receiving
  application that treats `U+2060` as data would see one extra character.
- **A `U+2060` in text being folded is removed, wherever it came from.** That is the
  deliberate choice above. It cannot corrupt Isabelle source, which has no use for the
  character, but text pasted from an application that uses word joiners for its own purposes
  loses them.
- **It does not travel through `Isabelle_RPC_Host.unicode`.** That path emits `\<name>`
  escapes and never calls these functions, so the semantic database, logs and model prompts
  are unaffected.
- **The copy path serves more than buffers.** `Registers.copy(pretty_text_area, '$')`
  (`contrib/Isabelle2025-2/src/Tools/jEdit/src/pretty_text_area.scala:350`) routes copying
  out of Isabelle's Output, State, Query and Sledgehammer panels through the same register
  and hence the same `phi_word_expand`. What those panels show is pretty-printed prover
  output, where two glyphs can meet without a space more easily than in hand-written source,
  so the 369-file scan understates reachability. Nothing here breaks that path; it is simply
  a second population the fix serves.
- **One shipped behaviour changes on purpose.** A glyph written directly against a
  mathematical character no entry uses no longer folds. Nobody can hit it in the current
  sources (**measured**: 0 such places in 369 files), and the reasoning is under "A
  deliberate widening"; but it is a user-visible change and belongs in `WORD_GLYPHS.md`, not
  only here.
- **The existing round-trip test must keep passing.** Every one of the 135 entries is a lone
  glyph, so no joiner is inserted; if it fails, either the insertion condition or the name
  prefixing is wrong.


## What is NOT verified

Everything above is a property of the two functions and was measured on them directly. What
has not been done is a round trip through a real clipboard in a running jEdit. Two checks by
hand:

**The round trip must leave the JVM, or it tests nothing.** Copying and pasting inside jEdit
never exercises the fold at all: a jEdit copy puts its own rich-text flavor on the clipboard
beside the plain text, the register wrapper hands that flavor back untouched, and
`Registers.paste` prefers it — so the glyphs come back intact **before** any fix, and
`phi_word_fold` never runs. An earlier draft of this plan proposed two in-jEdit checks and
claimed the first one produced `\<orelse>` today; **measured**, it does not. Both checks
below therefore go out to another application and back.

1. **Type `\<or'>\<else>` with nothing between them** (`<or>` then `<else>` from the
   keyboard), select both, copy, **paste into a plain text editor**. Confirm it reads as
   `orelse` with no visible gap and no line break between the two words. Then **select it
   there, copy it from that editor, and paste it back into a `.thy` buffer**. Expect **two
   symbols back**, not the single `\<orelse>`. The same steps before the change produce
   `\<orelse>`, so run it once before and once after if you want to see the difference.
2. **Type `\<orelse>` alone**, copy, take it out to the same editor and back. Expect
   `\<orelse>` — the check that the fix did not buy correctness by making an ordinary symbol
   stop folding.


## Procedure

1. **Rewrite the two functions in `phi_word_clipboard.bsh`.** Top-level `phi_t` and
   `phi_wj`; all three patterns — the glyph class, the run pattern, the longest-first
   alternation — compiled once at top level, never inside a function. `phi_word_expand`
   becomes the single `Matcher` pass over the glyph class, emitting a joiner where a match
   starts exactly where the previous one ended; `phi_word_fold` becomes run extraction plus
   the compiled alternation, ending with the unconditional joiner strip. The run pattern
   requires at least one character of the mathematical block, for the measured reason under
   "What makes it fast" — a pattern of only `[...]+` is 4.5 times slower on real source and
   produces the same bytes, so the difference will not show up in any output comparison.
   Keep both null guards. Prefix
   every bare name, in the new code and in the existing `phi_word_fold`,
   `phi_word_fold_run` and `phi_word_table`, and give every one of them a declared type —
   the prefix documents the intent, the type is what makes a local a local. The closures in
   `phi_word_install` name `phi_t` directly; do not reintroduce a bare `t`.
   Update the file's header comment, which describes the two directions and does not yet
   mention boundaries. Fix the wrong comment above `phi_service` while there — see
   `DRAG_AND_DROP_PLAN.md`, "The delegating wrapper", for the measured rule it gets wrong.
2. **Make `run_word_clipboard_test.sh` run under `xvfb-run`, and make it fail loudly.**
   Say in its header comment why a display is needed. Then fix a second thing: the
   interpreter **exits 0 on a script error**, so a load-time failure today makes the suite
   silently "pass" — which matters because this plan leans on "the whole script still loads"
   as the only way to catch an unbound name or an unresolved method.

   **The rule must be the absence of the test's own `PASS:` line**, not the presence of
   output on stderr. **Measured** twice: a script whose second line calls a method on an
   unbound name prints `Evaluation Error: ... undefined variable or class name` on **stdout**
   with **stderr empty** and returns 0 — `bsh.Interpreter` writes its errors through its own
   output stream, not through `System.err`. The one case that does reach stderr is a
   JVM-level trace, as `env -u DISPLAY ./run_word_clipboard_test.sh` shows with its
   `HeadlessException` (**measured**: exit 0, stack trace on stderr, BeanShell's own message
   on stdout). So: fail when `PASS:` is absent, and fail on stderr output as well — the
   second is a useful extra net, but on its own it catches nothing this step exists for.
3. **Extend `test_word_clipboard.bsh`**:
   - all 135 entries still round-trip alone, with no joiner inserted;
   - all 18225 ordered pairs of adjacent glyphs round-trip, and the two three-glyph cases;
   - `\<orelse>` alone still folds;
   - the both-sides case `𝐳𝐳𝐳\<has>\<has>𝐳𝐳𝐳` comes back with **no** `U+2060` in it;
   - a `U+2060` arriving in text to be folded is removed;
   - the shapes this plan does not fix still behave as they do today — a glyph against bold
     `zzz` on either side still comes back as letters, `\<size>_\<then'>` still comes back as
     letters and an underscore with no glyph, `\<change>` against a user's bold `𝐝` still
     comes back as `\<changed>`. Pin them so a later widening is deliberate;
   - **the one behaviour this plan deliberately changes**: a glyph against a mathematical
     character the table does not use — `\<pending>` followed by a bold `q`, since no entry
     spells a `q` — comes back as letters, where the committed code returns the glyph. Write
     the probe as the **round trip**, expand then fold, not as a fold of the glyph itself:
     folding `\<pending>` + bold `q` directly leaves it alone under either run class, because
     the glyph is not run-forming, so that input distinguishes nothing (**measured**). Pin it
     with a comment naming the widened run class, so the next reader sees a decision rather
     than a regression;
   - `phi_word_expand(t, null)` and `phi_word_fold(t, null)` return null;
   - **a performance floor**: one million characters at the sources' own glyph density
     expand and fold within a budget generous enough not to be flaky but tight enough to
     catch a return to the per-character loop — the rewritten functions do it in about 40 ms
     and 120 ms (**measured**), so a two-second ceiling is ample and would fail loudly
     against the committed implementation, which needs about four and nine seconds;
   - the whole script still loads in the bare interpreter, which is what catches an unbound
     name or an unresolved method — no runtime guard can.
4. **Scan every file touched for unrenderable characters** — the private-use area, the
   `Cf`/`Cc`/`Co`/`Cs` categories, and the zero-width characters — before committing. A
   literal invisible character cannot be seen by reading, and both a word joiner and four
   private-use characters have already been lost into these documents that way.
5. **Ask the user to run the two manual checks.**
6. **Update `../fonts/WORD_GLYPHS.md`, and re-cut the paragraphs the other three plans
   inherit.** Three edits.

   First, its "What the paste direction folds" section needs two things. It describes what
   counts as one run in terms that imply the narrow, table-derived definition; restate it as
   the mathematical alphanumeric block plus `.` and `_`, and say plainly that a glyph written
   directly against a mathematical character no word uses now comes back as letters, where it
   used to come back as a glyph. Then say that an expansion is
   delimited on the clipboard, so a word written against another word comes back intact —
   and, in the same breath, that a word written against somebody else's mathematical letters
   still does not, with the shapes below named. Its promise that "a round trip through
   another application loses nothing" becomes true for adjacent glyphs only; qualify it
   rather than leaving it absolute.

   Second, and this is the part that keeps the four plans from colliding: the paragraph at
   `:101-106` opens "Two places this does not reach." and names exactly two — dragging out of
   jEdit, and Isabelle/VSCode. It names neither the primary selection nor input-field paste,
   so the later plans have nothing to delete and their steps must not be written as
   deletions. **Rewrite that paragraph here, once, into a list that is correct after all four
   plans have landed**: Isabelle/VSCode; HyperSearch's "copy results"; and a place held for
   the one-way asymmetry `SEARCH_FIELD_PASTE_PLAN.md` introduces, that copying *out* of a
   wrapped input field still yields the raw glyph. Mark four lines — drag and drop, the
   primary selection, input-field paste, and that asymmetry — as **covered by a plan not yet
   landed**, with a note to strike the marker as each plan lands. Do not state the asymmetry
   as a fact here: between this plan and plan 3 there is no wrapper to be asymmetric, and
   plan 3's own step fills it in. Plans 2, 3 and 4 then each strike one marker, which is an
   edit that composes; the earlier wording, in which each plan deleted an item that was never
   there, did not.

   Third, the paragraph immediately after it — the one beginning "Outside jEdit,
   `Isabelle_RPC_Host.unicode` keeps a private-use symbol as its `\<name>` escape" — says at
   `:112-113` that a raw private-use character "that came out of a drag can be repaired" by
   that function's reverse direction. Re-aim that clause **here**, once, so it survives all
   four plans: the repair is still available, but the routes that produce such a character
   are HyperSearch's "copy results" and, until the plans in the list above land, a drag and
   the primary selection. Written that way the sentence is true before, between and after the
   four plans, and none of them has to touch it again.


## What this plan does not cover

- **A glyph written against the user's own mathematical letters.** Two shapes. Neither is
  repaired here; one of the two does move, because the run class widens — see "A deliberate
  widening" — in that letters the table happens not to use now abandon the run where they
  used to be ignored, which is the direction of not-mangling-somebody-else's-text. **The
  clean-but-wrong one**: when those letters complete a longer table
  word, the pair folds into a *different* glyph — `\<change>` + a user's bold `𝐝` comes back
  as `\<changed>`, `\<has>` + `𝐡` as `\<hash>`, `\<in'>` + `𝐬𝐭` as `\<inst>`, a user's `𝐨𝐫` +
  `\<else>` as `\<orelse>`. **Measured: 26 such combinations**, 17 with the letters after and
  9 before. **The visible one**: when they do not, the abandon rule takes the glyph down with
  them and the run comes back as letters. Neither occurs in the sources (**measured**: 0
  places where a glyph is written against a mathematical letter), and repairing them needs
  the wider insertion rule that was considered and not taken.
- **A glyph separated from another glyph by `.` or `_`.** Those two characters are
  run-forming, so the re-segmentation reaches across them while the narrow insertion
  condition inserts nothing there. **Measured: 9 sequences still fail**, all of the shape
  `\<size>` + `_` + a word beginning with `t` — `\<size>_\<then'>`, `\<size>_\<threshold>`,
  `\<size>_\<throws>`, `\<size>_\<to>`, `\<size>_\<transforms>`, `\<size>_\<traverse>`,
  `\<size>_\<tree>`, `\<size>_\<tup>`, `\<size>_\<typeof>`. Each comes back as **mathematical
  letters and the underscore, with no glyph at all** — `\<size>_\<then'>` gives eight letters
  and an underscore — because the scan matches `size_t` and is then left with a remainder no
  word claims, which abandons the whole run. So these nine are the **visible** kind, not the
  **clean-but-wrong** kind; an earlier draft of this plan said the opposite. `DRAG_AND_DROP_PLAN.md`
  uses `\<size>_\<then'>` as a manual-check input for exactly this reason. "Removes the whole
  class permanently" is true of the directly-adjacent class only.
- **Old letter-by-letter spellings still fold into the new symbols.** Eight `*.unicode.thy`
  files store symbols decoded rather than escaped, and among them **239** places still carry
  the pre-migration spelling: **216** of `\<m>\<a>\<p>`, **21** of `\<p>\<o>\<i>\<s>\<o>\<n>`,
  and **2** others, both in `Phi_System/IDE_CP_Core.unicode.thy` (`:19` and `:25`), which are
  raw mathematical bold letters rather than the letter-symbol spelling — written
  `\<^bold>b\<^bold>y` and `\<^bold>r\<^bold>e\<^bold>t` in the escaped source
  (**measured**). Copying such a passage and pasting it back converts it to
  `\<map>`, `\<poison>` and so on. That is the paste direction doing its designed job and
  `MIGRATION.md` treats the conversion as the intended direction of travel — but the new
  symbols are **not letters** (see "One thing the generator cannot fix" in
  `WORD_GLYPHS.md`), so the conversion is not meaning-preserving where the old spelling sat
  inside an identifier. Not decided; recorded because the scan for this plan turned it up.


## Constraints on whoever implements this

- **Never run `isabelle build`**, in any session, with any flags.
- Never run `git clean`, `git stash`, `git checkout`, or `git reset --hard`. Shared tree.
- Do not modify anything under `contrib/Isabelle2025-2/`, `ICSE27/` or `ICSE27-x/`.
- Do not test against the live X11 display; use `xvfb-run`.
- `contrib/phi-system` is its own git repository; commit there and bump the super-repo.
