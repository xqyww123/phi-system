# Keyword words as single glyphs

This file covers the generator: how a word becomes a glyph, a symbol and a clipboard
entry, and how to add one.  `MIGRATION.md` beside it covers the other half — how the
sources were rewritten to use these symbols, what deliberately still spells itself out,
and the rule that decides whether a word can be a symbol at all.


phi-System used to write its keywords one Isabelle symbol per letter:

    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>

Each `\<t>` is a standard Isabelle symbol whose code point is a mathematical
sans-serif letter, so the ten symbols together read as `𝗍𝗋𝖺𝗇𝗌𝖿𝗈𝗋𝗆𝗌` on screen.
This replaces the ten symbols with one, `\<transforms>`, whose glyph draws the
whole word.

`fonts/build_word_glyphs.py` generates those glyphs into `PhiSymbols.ttf` and
writes the matching symbol declarations to `../symbols-words`.

## Why one glyph, and not several code points

An Isabelle symbol decodes to **exactly one Unicode code point**.  The `code:`
field of a symbol table is parsed by `Integer.decode` and turned into characters
by `Character.toChars` (`Pure/General/symbol.scala`), so there is no syntax for
more than one, and adding one would break something deeper: the prover reports
positions as *symbol* offsets while the editor counts *characters*, and the two
are reconciled by `Symbol.Matcher`, a purely syntactic scanner with no table of
decoded forms.  A symbol that decoded to seven characters would be counted as
seven symbols by the editor and one by the prover, and every error marker,
hover and completion after it on the line would be off by six.

So the word has to be a single code point carrying a single, very wide glyph.
The code points live in the Private Use Area (U+E000 upwards), which neither
Isabelle nor the hand-drawn part of this font uses.

## Why the glyphs go into PhiSymbols.ttf and not a new font

`Pure/Tools/jEdit/src/syntax_style.scala` permits **at most two** user symbol
fonts and aborts the plugin if a third appears.  Both slots are already taken:
one by the Isabelle distribution itself, one by `PhiSymbols`.  Note also that
jEdit's font substitution is off by default (`view.enableFontSubst=false`), so a
glyph is only reachable through the `font:` field of the symbol table — dropping
that field makes the symbol render as blank.

## Pipeline

    PhiSymbols.sfd  --FontForge-->  PhiSymbols.ttf  --build_word_glyphs.py-->  PhiSymbols.ttf
     (hand-drawn)                                                              (+ word glyphs)

Hand-drawn symbols stay in `PhiSymbols.sfd`; edit them with FontForge and export
the `.ttf` as before.  Word glyphs are generated and never enter the `.sfd`.
The script is idempotent — every glyph it adds is named `word.<word>` and all of
them are dropped at the start of a run — so it is safe to run it repeatedly, and
safe to run it again after re-exporting the `.sfd`.

## Copying a word out of jEdit

The buffer holds the decoded symbol, so a plain copy hands other applications the
private-use code point — U+E048, not `pending`.  `../jedit/phi_word_clipboard.bsh`
fixes that in both directions:

* copying a word out yields the word in **mathematical bold** letters, the same
  letters the glyph was drawn from, so the pasted text looks like what was on
  screen (`𝐩𝐞𝐧𝐝𝐢𝐧𝐠`, `𝐀𝐫𝐫𝐚𝐲`, `𝓣𝓟`) — except for the Medium words, which come
  out in mathematical sans-serif (`𝖺𝗂𝗇𝗍`), there being no bold-free mathematical
  alphabet to match them;
* pasting such letters back in turns them into the glyph again, so a round trip
  through another application loses nothing.

Copying and pasting *within* jEdit is untouched: jEdit prefers its own rich-text
flavor, which is a JVM-local object no other process can see, and the script leaves
it alone.

### What the paste direction folds

It reads a run left to right, longest word first.  When no word matches at a
position it looks at the character: **ASCII that no word claims is carried over**
— a full stop after a word, an underscore or a digit joined to it, `w.r.t.`'s own
periods — while **a mathematical letter that no word claims abandons the whole
run untouched**, because the run is then somebody else's bold text and none of it
may be modified.  So `𝐩𝐞𝐧𝐝𝐢𝐧𝐠.` folds and `𝐬𝐭𝐚𝐭𝐞𝐬` does not.

That ASCII clause was added when the first entries with punctuation, `wrt` and
`size_t`, put `.` and `_` into the table.  Before it, any word written against a
full stop silently stopped folding — the rule was all-or-nothing per run.

### The constraint on a new entry

**Any ASCII character in an entry's drawn text lands in the table and becomes
significant to the paste direction.**  Punctuation and digits are fine.  ASCII
*letters* would not be: the paste step would fold the word wherever it occurs in
an ordinary English sentence.  This is why the Medium words go through
`sans_code_point` even though their glyph is drawn from an ordinary ASCII text
font, and `build_word_glyphs.py` now refuses to write a table containing one.

`phi-System/etc/settings` links the script into `$JEDIT_SETTINGS/startup/`, and puts
it back if it goes missing, so registering the component is all a user has to do.
The letters come from `../jedit/word-clipboard-text`, generated alongside the glyphs.

Two places this does not reach.  Dragging text out of jEdit goes through
`TextAreaTransferHandler`, which builds its own clipboard contents and consults no
service list, so a drag still carries the private-use code point.  And Isabelle/VSCode
carries a symbol table frozen into the VSCodium component when it was built; no
phi-System symbol is in it — not the word glyphs and not the hand-drawn ones either —
so there `\<pending>` simply stays the seven characters you typed.

## Adding or changing a word

1. Edit `words.txt` (one entry per line, `#` starts a comment).
2. Run `python3 build_word_glyphs.py` from this directory.
3. Run `../jedit/run_word_clipboard_test.sh` — it round-trips every entry through
   the real BeanShell interpreter and checks the fold rule described above.  The
   two halves of this feature are generated apart and nothing but this test makes
   them agree.
4. Restart the Isabelle/jEdit session and check the new symbol renders.

An entry is normally just the word, and then the symbol name, the glyph and the
abbreviation are all that word.  They come apart when the word reads with
punctuation, because a symbol name admits only `[A-Za-z][A-Za-z0-9_']*` — no
period, no hyphen.  Then write `name = drawn text = abbreviation`:

    wrt = w.r.t. = w.r.t     \<wrt> draws `w.r.t.` and is typed as <w.r.t>
    size_t                   an underscore needs no split; it is a legal name

Either of the last two fields may be left out.  Punctuation is drawn from the
source font's own ASCII, so a period or an underscore comes out at that font's
regular weight — invisible on a period, slightly light on an underscore against
mathematical bold letters.

Step 2 rewrites `PhiSymbols.ttf`, `../symbols-words` and `../jedit/word-clipboard-text`
together, so the glyph, the symbol declaration and the clipboard text cannot drift
apart.

Code points already assigned in `../symbols-words` are reused, so reordering or
deleting a line never renumbers the words that survive.  Adding a line takes the
next free code point.

Requirements: `fontTools`, `STIXTwoMath-Regular.otf` and `STIXTwoText-Medium.otf`
— the script looks in `~/.local/share/fonts/stix2/` and the usual system font
directories, or takes `--stix PATH` / `--stix-text PATH`.  STIX Two is OFL
licensed (`STIX-OFL.txt` in this directory) and is already the source of several
hand-drawn glyphs in this font.  `--check` verifies the inputs and writes nothing.

## What the generator decides for you

**Which alphabet.**  A word is either a keyword or a semantic type name, and the
two are drawn a weight apart:

| word                              | alphabet                              | example          |
| --------------------------------- | ------------------------------------- | ---------------- |
| keyword, all lower case           | STIX Two Math bold, U+1D41A           | `transforms`     |
| keyword, all upper case           | STIX Two Math bold script, U+1D4D0    | `TP`, `EIHOOK`   |
| keyword, mixed case               | STIX Two Math bold, capital included  | `Array`          |
| semantic type name (`MEDIUM_WORDS`) | STIX Two Text Medium, plain ASCII   | `aint`, `poison` |

Upright bold serif is the convention mathematical writing uses for multi-letter
operator names and program keywords; bold script matches what the old
`\<A>`..`\<Z>` spelling looked like, so the all-upper-case words keep their
appearance.

The semantic type names — `aint areal bool int map poison symbol void` — are notation
for an ordinary ASCII constant (`sem_aint_T` and its siblings), not keywords, so
they are drawn lighter: a line that mentions four of them should not be darker
than the keyword that governs it.  Medium is only available in STIX Two Text; the
mathematical alphanumeric blocks carry regular and bold and nothing in between.
Being an ordinary text font it is addressed as plain ASCII rather than through a
mathematical block.

`pointer` stays bold although `sem_pointer_T` is one of those constants: the
pointer type prints as `\<ptr>`, and the only thing the `\<pointer>` glyph draws
is the operator `\<pointer>-\<of>`, which is a keyword like any other.

That split is also why the clipboard text (below) differs for them: there is no
mathematical alphabet at Medium weight, so a copied type name comes out in the
sans letters it used to be spelled out in.  Plain ASCII would be worse — it would
be indistinguishable from an ordinary identifier.

**How big.**  Outlines are scaled so the word matches the size of the spelling it
replaces: lower case against the x-height of `𝗑` in `IsabelleDejaVuSansMono`,
capitals against the height of `𝒯` (the glyph behind `\<T>`).  Nothing grows or
shrinks on migration.

**The symbol name.**  Normally the word itself.  Seven words collide with symbols
Isabelle already defines — `bool` (𝔹), `in` (∈), `index` (ı), `int` (ℤ), `open`
(the cartouche delimiter ‹), `or` (∨), `then` (⪢) — and those get a trailing
prime: `\<open'>`, `\<in'>`, and so on.  The prime appears only in source text;
the glyph still reads `open`, and the abbreviation is still `<open>`.  The
collision check runs against Isabelle's `etc/symbols` and this component's
hand-maintained `symbols`, so a future name clash is caught automatically.

**The abbreviation.**  Every word gets `abbrev: <word>`, so typing `<transforms>`
in jEdit offers the symbol.  All 133 were checked against every existing
abbreviation in Isabelle and in this component: none collided.

## One thing the generator cannot fix

`Pure/General/symbol.ML` carries a hardcoded list of which symbols count as
*letters*, and `symbol.scala` carries the same list for the editor.  Only
`\<a>`..`\<z>`, `\<A>`..`\<Z>` and the Greek letters are on it.  A new symbol is
therefore **not a letter** and cannot appear inside an identifier: writing
`\<typeof>_plus` no longer names one theorem, it lexes as a symbol followed by
`_plus`.  (`group: letter` in the symbol table has nothing to do with this — that
field only sorts the symbol palette.)

Where the old spelling was embedded in a name — `\<t>\<y>\<p>\<e>\<o>\<f>_plus`,
`has_Zero_\<p>\<o>\<i>\<s>\<o>\<n>` — the name is spelled out in plain ASCII
instead (`typeof_plus`, `has_Zero_poison`).  The alternative would be patching
both lists in the Isabelle distribution, which is not under version control here
and would have to be re-applied by everyone who builds phi-System.

And where the word **was** the name of a constant, a type or a syntax constant, the
thing is given an ordinary ASCII name and the word is attached as notation —
`debt_axiomatization sem_aint_T :: TY ("\<aint>")`, `typedecl int_t ("\<int'>")`.  That
is what `MIGRATION.md` is about; read it before adding a word that names something.
