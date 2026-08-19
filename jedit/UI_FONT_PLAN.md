# Making word glyphs render in jEdit's widgets: one font, merged into PhiSymbols

Read `WORD_CLIPBOARD_PLANS.md` beside this file first: it carries the implementation order, the
decisions the user has settled, the conventions all the plans follow, and what has been
reviewed.

**Where it stands.** Implemented. The fix is applied beside `phi_wrap_field`, which
`SEARCH_FIELD_PASTE_PLAN.md` created and which is committed (`aaec0131`), so that plan was a
prerequisite. One thing was decided differently while implementing, and step 2 below records
it: the name table is written by the generator, not by `PhiSymbols.sfd`.

**How this plan is written.** It records decisions and the reasons for them, not a measurement
archive. Five review rounds were spent largely on figures that went stale when a rule changed,
so a number appears below only where a decision hangs on it. Verify by running things; keep the
evidence in the commit message, not in a document that must stay self-consistent for ever.


## The problem

Put a word glyph into jEdit's Find box — by pasting one, or by selecting a word in the buffer
and pressing Ctrl-F, which `actions.xml:395` feeds from `textArea.getSelectedText()` without
touching the clipboard — and the box shows nothing at all. Not a box: nothing.

The text area can draw it because `symbols-words` gives every word glyph a `font: PhiSymbols`
field and `syntax_style.scala:98` turns that into a per-character syntax style. That machinery
is the text area's alone. A Swing text component has **one font for the whole component**, and
`fonts/PhiSymbols.ttf` covers **0 of the 95 printable ASCII characters** — so no existing font
can serve a widget that must show both ordinary text and a glyph.

Three routes fail, all checked: giving a field `PhiSymbols` as it is (ordinary text becomes
notdef boxes); relying on the JVM's logical families (they draw a notdef box for U+E048, and
`registerFont` does not join a font to a logical family's composite); and installing PhiSymbols
where fontconfig can see it (Java's fallback list is chosen per family at startup, not per
missing code point).

### The widgets are two groups with two different fonts

`Base_Plugin.start()` calls `GUI.use_isabelle_fonts()` (`base_plugin.scala:24`), then four lines
later `Syntax_Style.set_extender(...)`, whose body ends with
`GUI_Thread.later { jEdit.propertiesChanged }` (`syntax_style.scala:63-64`) — and
`propertiesChanged` writes `view.font`, the monospaced editor face, over `TextArea.font`
(`jEdit.java:1058-1062`; the `TextField.font` line beside it is commented out). So, steadily:

```
HistoryTextField  quick-search bar, file browser path and filename, action bar, Isabelle's
                  Query, Sledgehammer and Debugger inputs — about 13 widgets
                  -> TextField.font = Isabelle DejaVu Sans       (proportional)
HistoryTextArea   the Search and Replace dialog's Find and Replace boxes — 2 widgets
                  -> TextArea.font  = Isabelle DejaVu Sans Mono  (monospaced)
```


## The design: merge a text face into PhiSymbols.ttf

Isabelle solves the same problem the same way (`component_fonts.scala`: "DejaVu base + Isabelle
symbols"). This is that operation once more, with phi-System's own font as the destination:

    fonts/PhiSymbols.ttf  +=  Isabelle DejaVu Sans (hinted)  +  STIX mathematical alphanumerics

Four consequences follow from choosing that direction, and they are why the plan is short.

**The family name stays `PhiSymbols`.** `symbols`, `symbols-words` and `etc/settings` need no
edit, and Isabelle's limit of two user symbol fonts — counted over distinct `font:` families,
currently exactly full at `{Isabelle, PhiSymbols}` (`syntax_style.scala:79-81`) — is untouched.

**There is no registration code to write.** `etc/settings` already carries
`isabelle_fonts "$COMPONENT/fonts/PhiSymbols.ttf"`, which appends to `ISABELLE_FONTS`;
`Isabelle_Fonts.init()` registers every entry (`isabelle_fonts.scala:71-72`); and
`jedit_main.scala:26` calls it a hundred lines before `jEdit.main` at `:126`. A startup script
therefore needs no `createFont` and no `registerFont`, and `new Font("PhiSymbols", …)` resolves.

**A broken font fails loudly.** Nothing in `isabelle_fonts.scala` catches, so a missing or
corrupt file throws during Isabelle startup — where `new Font(family, …)` in a script would
silently yield family `Dialog` and paint notdef boxes.

**The text area keeps its sizes.** `GUI.imitate_font` reads `head.unitsPerEm` and hhea's
ascender, descender and lineGap. The merge leaves all four alone (2048 and 1901/-483/0), and
PhiSymbols and both Isabelle faces agree on them, so its ratio is 1.0 before and after. Saving
does change `head`'s bounding box, `indexToLocFormat` and `flags`, and hhea's
`numberOfHMetrics` and side bearings; none of those enters a line height or a rasterisation.


## What the merge copies, and the traps in doing it

**Eight things: `glyf`, `hmtx`, `cmap`, the glyph order, and `fpgm`, `prep`, `cvt` and the
`maxp` maxima.** Isabelle registers the *hinted* faces, whose glyphs carry ttfautohint bytecode
that needs the base's function definitions and stack depth. The four tables must travel
together: with `fpgm` and `prep` but not the raised `maxp` maxima the interpreter gives up and
**every glyph draws nothing**; with all four, the copied Latin renders exactly as it does in the
base. Set all seven instruction-related `maxp` fields, not two — phi's own values are
`maxFunctionDefs` 1, `maxStackElements` 64, `maxStorage` 1, `maxSizeOfInstructions` 46,
`maxTwilightPoints` 0, `maxInstructionDefs` 0, `maxZones` 2, against the base's 141, 434, 318,
526, 196, 0, 2.

*The one cost*: carrying the base's `fpgm` and `prep` slightly changes how phi's own glyphs
rasterise **when antialiasing is off** — they are essentially uninstructed, so what reaches them
is the graphics state `prep` sets. Under jEdit's shipped `view.antiAlias=subpixel HRGB`, and
under greyscale antialiasing, nothing changes. Say so in `phi-font-readme.txt`; it needs no
assertion.

**The base is `ttf-hinted/IsabelleDejaVuSans.ttf`.** `isabelle_fonts-*/etc/settings` takes the
`ttf/` branch only when `isabelle_fonts_hinted=false` appears in the untracked
`$ISABELLE_HOME_USER/etc/preferences`; the default is `ttf-hinted`. Resolve it the way
`find_isabelle_mono` already resolves the mono face — `ISABELLE_HOME` or the sibling
distribution, plus the `contrib/isabelle_fonts-*/ttf-hinted/` glob — in **one helper taking a
file name**, so the x-height reference and the text face can never come from different variants.
Do **not** resolve through `ISABELLE_FONTS`: that variable exists only inside Isabelle's
settings environment, while `WORD_GLYPHS.md` documents the generator as plain
`python3 build_word_glyphs.py`. Assert the resolved base's name ID 5 equals
`Version 2.37; ttfautohint (v1.8.4)`, so a distribution upgrade fails the build instead of
silently ageing the committed font.

**The mathematical alphanumerics come from STIX Two Math**, which `build_word_glyphs.py:64-68`
already locates. The candidate rule is "**the base lacks the code point, or maps it to a glyph
with no outline**" — the base has five blank-outlined entries, one of which, U+1D5D4, is inside
the block. Build the candidate list against the **original** base and PhiSymbols, never against
the destination mid-merge, so which font supplies a code point is a rule rather than an artefact
of statement order. That yields 850 code points (996 assigned in the block, the base lacks 875
and draws one blank, PhiSymbols draws 26 itself).

**Both halves of the em correction matter, and each hides the other's absence.** STIX is drawn
on a 1000-unit em against 2048, with cubic outlines. Scale the outlines —
`TransformPen(Cu2QuPen(TTGlyphPen(None), max_err=1.0), Transform(2.048, 0, 0, 2.048, 0, 0))`,
that pen order — **and** scale the advances by the same factor, rounded to the nearest integer.
Outlines alone leaves the letters overlapping; advances alone draws them at half size while
every width still checks out.

**The cmap rule the existing idiom hides.** `build_word_glyphs.py:312-314` writes a code point
into every Unicode subtable, which is safe only because word glyphs are in the BMP. Writing a
supplementary code point into a format-4 subtable makes `font.save` die with `OverflowError`.
Supplementary code points go only into format 12.

**Two code points belong to phi.** PhiSymbols and the base share exactly `U+061F` and `U+2023`,
both declared `font: PhiSymbols` in `symbols` (`\<rev_quest>`, `\<tribullet>`), so phi's glyph
wins — as it already does in the text area. Assert the overlap is exactly these two, so a future
base growing into phi's territory fails the build.

**The copy must not mutate the source.** Storing a source `Glyph` object in the destination and
then renaming its components rewrites the source's composites — and the base has **180** of
them, in the very object the generator keeps using. Deep-copy each glyph before renaming, and
end the merge by asserting the source's glyph order, composite components, `hmtx` and `cmap` are
unchanged. (Re-opening the source from bytes is *not* an equivalent fix.)


## Keeping the artefact re-derivable

`PhiSymbols.ttf` is committed and is meant to be determined by `PhiSymbols.sfd` plus the
generator's inputs. Two things keep that true, and both belong in `drop_generated`, whose
contract is already "undo everything this generator adds":

* **Two prefixes, one tuple.** Copied glyphs are named `base.` and `stix.` by origin, and
  `drop_generated` drops `("word.", "base.", "stix.")` through a single named tuple. Failing to
  extend it is completely silent: the "skip what the destination already covers" filter then
  finds everything present, copies nothing, and the stale glyphs survive an Isabelle upgrade.
* **Reset what the merge changed besides glyphs**: delete `fpgm` and `prep`, restore `cvt` to
  phi's two entries and the seven `maxp` fields to phi's values, and empty
  `font["post"].extraNames` — fontTools' format-2.0 encoder never removes a name once added, and
  the committed font still carries `word.tr` from a word deleted long ago.

Open the destination with `TTFont(FONT, recalcTimestamp=False)`, or every run differs from the
last in `head.modified` alone. That is enough; a committed pre-merge fixture with an asserted
SHA was considered and dropped as ceremony — the property that matters is "the font contains the
right glyphs", which the checks below establish directly.

**Placement is made robust rather than documented.** `build_word_glyphs.py:284` takes
`order = list(font.getGlyphOrder())` as a snapshot the word-glyph loop appends to; drop that
`list()` copy so exactly one glyph-order object exists in the run, and every position after
`drop_generated` becomes correct. Only "before `drop_generated`" remains an error, and that one
is caught, because the extended drop would eat the merge and the coverage check would fail.


## Applying it to the widgets

**A separate one-line `phi_field_font(phi_field)`, called from the AWT listener in
`phi_install_field_paste` (`phi_word_clipboard.bsh:311-313`) beside `phi_wrap_field` — not
inside it.** `phi_wrap_field` (`:287-299`) returns early when the field is already marked or has
no transfer handler, and neither condition says anything about whether the field can draw a
glyph: a field wrapped by an earlier pass still needs its font. Two jobs, two functions, called
from the one place that discovers the fields. `phi_field_font` keeps the field's style and size
and changes the family to `PhiSymbols`.

**Two shipped behaviours change, and both are visible.** The Find and Replace boxes are
monospaced today and become proportional — the user chose this knowing the mono base would have
changed the other thirteen widgets instead, and that one font carries one design for ASCII. And
a field given a plain `Font` stops following UI font-size changes, since `updateComponentTreeUI`
replaces only `FontUIResource` fonts: the Search dialog is rebuilt on each open
(`Debug.DISABLE_SEARCH_DIALOG_POOL`, `base_plugin.scala:26`) and picks the new size up, while
the quick-search bar and an open file browser keep the old size until restart.


## What this does not cover

* **The text area**, except the antialiasing-off rasterisation change noted above.
* **The history drop-down**: `HistoryTextField` and `HistoryTextArea` show previous entries in a
  `JPopupMenu` of `JMenuItem`s, which take `MenuItem.font`; `phi_field_font` never sees them.
* **Other Swing surfaces** — HyperSearch's result list, tooltips, the file browser's tree. Those
  would need a `UIManager` pass, durable for `TextField.font` but needing re-application on
  `PropertiesChanged` for `TextArea.font` and `TextPane.font`, which jEdit rewrites itself.
* **Bold and italic are synthesised**; only the regular face is merged. No wrapped field is
bold.
* **Complex-script shaping and positioning.** PhiSymbols has a small `GDEF` of its own and no
  `GSUB`, `GPOS` or `MATH`, so the base's layout does not survive: GSUB `{' RQD', aalt, ccmp,
  liga, salt}`, GPOS `{kern, mark, mkmk}`, its 1492-entry `GDEF` and its `MATH` table are all
  lost. Latin is unaffected — precomposed accents and `fi`/`fl` are single glyphs, and Java's
  `drawString` applies no GPOS kerning anyway — while Arabic mark positioning degrades.


## Risks

* **The font travels without its licence files.** `html.scala`'s `init_fonts` copies every
  `ISABELLE_FONTS` entry as a bare `.ttf` into each browser-info directory, and
  `component_vscode_extension.scala:213` into the VS Code extension; neither copies a licence.
  The obligation is unmet today — the shipped font has name IDs 0-6 only, no ID 13, no ID 14,
  and its ID 0 names three upstreams without an OFL notice or a Bitstream attribution. Step 2
  **extends** ID 0 and adds the missing records.
* **The merge brings in GPL material, and the font discloses it.** The Isabelle base is not one
  upstream: its own README says the blackboard-bold glyphs come from `txmia` (package
  `pxfonts`) and "these are subject to GPL", besides Bluesky TeX material scaled 222% and glyphs
  from Symbola. 26 of those blackboard-bold code points — U+2102, U+210D, U+2115, U+2119,
  U+211A, U+211D, U+2124 and 19 in U+1D538..U+1D56B — are in the base's cmap and every one is
  copied. **The user decided to ship the mixture and disclose it as Isabelle does**: name ID 0
  and `phi-font-readme.txt` name the GPL material and its source and point at the Isabelle
  component's README. Excluding those 26 was the alternative, rejected because they are common
  in Isabelle mathematics and would be blank in every wrapped field.
* **The file grows from 96,972 to roughly 480,000 bytes**, and that is what is copied into every
  generated presentation directory.
* **A user who sets `isabelle_fonts_hinted=false`** gets unhinted outlines in the text area and
  the hinted rasterisation in these widgets. One committed font cannot serve both.
* **`build_word_glyphs.py:45` hard-codes `ISABELLE = "Isabelle2025-2"`** as the fallback when
  `ISABELLE_HOME` is unset, so the generator can keep building against a distribution left
  behind by an upgrade. The name ID 5 assertion above is what turns that into a loud failure.
* **`OS/2` fields become false and are left that way**: `usFirstCharIndex` stays 0x061F,
  `ulUnicodeRange1` still advertises private use only, `xAvgCharWidth` stays phi's wide-glyph
  average. None of the consumers this plan names reads them — Java resolves a registered font by
  name ID 1 and rasterises from `glyf` — and "average width" has no honest meaning for a font
  that is mostly symbols. Recorded, not asserted.


## Checking it: compare font data, not pixels

**This is the plan's main methodological decision, and it replaces an earlier design.** An
earlier version asserted pixel identity over the base's 1492 code points and advance equality
through Java's text machinery. Five of the eleven blocking findings across five review rounds
came from exactly that: `stringWidth` and `getStringBounds` give different answers with
fractional metrics on or off, the differing set moves with the point size, Java2D's default
antialiasing hint behaves as *off*, and every one of those configurations produced an assertion
that failed on a correct build.

The property actually wanted is **"the base's glyphs were copied unchanged"**, and that is a
statement about font data. Compare `glyf` outlines and `hmtx` integers: exact, deterministic,
free of every rendering configuration, and orders of magnitude faster. Rendering then needs only
coarse checks — *does the font draw ink at all* — which no configuration can flip.

**Structural checks live in the generator's `--check` mode** (`build_word_glyphs.py:247`), where
fontTools is available. `run_word_clipboard_test.sh` invokes only `jedit.jar`'s BeanShell under
`xvfb-run`; it has no `python3`, so nothing structural can live there.


## Procedure

1. **Extend `fonts/build_word_glyphs.py`.**
   - `find_isabelle_font(name)` replacing `find_isabelle_mono`, resolving through
   `ISABELLE_HOME`
     and the `ttf-hinted` glob, asserting the base's name ID 5.
   - `merge_text_face(font, source, codepoints, prefix)`: deep-copies each glyph, carries
     composites and renames their components, writes `glyf`, `hmtx`, the live glyph order and
     the cmap subtables permitted for each code point, and returns the order.
   - the STIX pass with the pen order and both halves of the em correction, over the candidates
     the base lacks **or draws blank**, computed against the original base and PhiSymbols.
   - `fpgm`, `prep`, `cvt` and the seven `maxp` fields copied from the base.
   - the destination opened with `recalcTimestamp=False`; the `list()` copy at `:284` dropped.
   - `drop_generated` taking `("word.", "base.", "stix.")`, resetting the four hinting tables to
     phi's values and emptying `post`'s `extraNames`.
   - an `--output` **directory** option, defaulting to the committed locations and mirroring the
     component layout, honoured by every artefact the run writes — the font, `symbols-words`,
     `jedit/word-clipboard-text` — so a check build cannot touch a shared working tree.
2. **Write name ID 0 and IDs 13/14 in the generator**, not in `fonts/PhiSymbols.sfd`. This plan
   said the opposite, because the `name` table comes out of the FontForge export. Two things
   changed it. FontForge is not installed here, so editing the `.sfd` alone would leave the
   committed `.ttf` carrying its 2023 name table and no way to fix it. And the obligations come
   from what the *merge* copies — DejaVu and Bitstream Vera, STIX under the OFL, the GPL
   blackboard-bold glyphs — which is the generator's doing, not the hand-drawn font's; the
   `.sfd`'s own notice covers only the hand-drawn glyphs. Whoever re-exports the `.sfd` runs the
   generator afterwards, so the generator's records always reach the artefact. Setting them from
   constants is what keeps the run idempotent, so `drop_generated` has nothing to undo. Neither
   upstream licence requires a rename — DejaVu's terms reserve "Bitstream", "Vera", "Tavmjong
   Bah" and "Arev", STIX's OFL reserves "TM Math" — so `PhiSymbols` needs no licence
   justification; what binds is the OFL's requirement that a derivative carrying STIX
   outlines be distributed under the OFL with its notice. ID 0 reads `Copyright 2023
   Qiyuan Xu`, and ID 14 points at `github.com/xqyww123/phi-system/tree/main/fonts`,
   where the three licence texts are.
3. **Restructure `fonts/phi-font-readme.txt` around three kinds of glyph** — hand-drawn,
   generated word glyphs, and the merged text face, the third being the bulk of the file. Record
   the Isabelle component, `ttf-hinted`, and the base's name ID 5; say the base is itself DejaVu
   Sans plus IsabelleSymbols — Bluesky TeX scaled 222%, Symbola, and the GPL blackboard-bold
   glyphs from `txmia`/`pxfonts` — and point at that component's README rather than paraphrasing
   it. Add the antialiasing-off sentence. Fix the stale count at `:84` ("133 … U+E000..U+E084"
   where the table has 135 running to U+E086).
4. **Add `phi_field_font(phi_field)` to `phi_word_clipboard.bsh`** and call it from the AWT
   listener in `phi_install_field_paste` (`:311-313`) beside `phi_wrap_field`, not inside it.
   Family `PhiSymbols`, style and size from the field's current font. Follow the file's
   BeanShell convention: declare every function-local with a type, and prefix every new bare
   name `phi_`.
5. **Add structural checks to the generator's `--check` mode.** Each must be shown to fail
   against a deliberately broken build made with `--output`; a check nobody has seen fail is not
   a check.
   - every code point in the base's cmap has, in the merged font, a `glyf` outline byte-equal to
     the base's and an equal `hmtx` entry — **except** two named classes, as an equality so that
     anything else differing fails: `{U+061F, U+2023}`, where phi's glyph and advance win, and
     the code points supplied over a blank base glyph, where the merged font must have an
     outline and the base must not;
   - phi's own 196 code points have outlines and advances identical before and after the merge —
     compared within the one run, snapshotting after `drop_generated` and before the merge;
   - every code point in `jedit/word-clipboard-text` is present;
   - the mathematical alphanumeric block is covered by glyphs that have outlines, not merely
     cmap entries;
   - the em correction in both dimensions: each advance equals STIX's scaled and rounded, and
     each bounding-box height is within a few units of the source's scaled — a band, not an
     equality, because cubic-to-quadratic conversion moves extrema — **and** at least 0.9 times
     it, which is the half that catches an outline left at 1000-unit scale;
   - the overlap between PhiSymbols' own code points and the base's is exactly the two;
   - the source fonts are unchanged after the run;
   - the artefact's table set equals a written-down expectation, so a later switch to
     `fontTools.merge` cannot pass;
   - the artefact carries name IDs 13 and 14 and an ID 0 naming every provenance.
6. **Add rendering checks to `test_word_clipboard.bsh`** — coarse, and therefore stable: the
   font resolves by family (`getFamily()`, never `getName()`, which lies about an unregistered
   family); a word glyph drawn in it produces ink; ordinary ASCII drawn in it produces ink;
   and a field the listener has seen reports family `PhiSymbols`. No pixel-identity, no advance
   comparison, no antialiasing configuration.
7. **Scan every file touched for unrenderable characters** before committing.
8. **Ask the user to run the manual checks below.**
9. **Update `../fonts/WORD_GLYPHS.md`**: that jEdit's own input fields draw word glyphs because
   `PhiSymbols.ttf` now carries a text face; that the Find and Replace boxes are proportional as
   a result; that the history drop-down and other Swing surfaces are still not covered; and,
   under "Adding or changing a word", that the generator's `--check` must be run as well as
   `run_word_clipboard_test.sh`.


## Manual checks

Nothing here can be verified outside a running editor. Each names what a wrong outcome looks
like, because a check whose expectation is "no change" cannot be failed by a human.

1. **Select a word glyph in a buffer and press Ctrl-F.** Expect the word itself in the Find box,
   drawn as in the buffer — not blank, not a box — and expect that box's ordinary text to be
   **proportional**, which is this plan's deliberate change. Then paste a glyph into the
   quick-search bar and into Isabelle's Query input, and expect the word in both.
2. **Type an ordinary path into the file browser's filename field and an English phrase into the
   quick-search bar.** Expect ordinary text, correctly spaced, no tofu boxes, no change of face.
3. **Look at a `.thy` buffer** carrying word glyphs and ordinary Isabelle symbols. Expect no
   change at the default `view.antiAlias=subpixel HRGB`.
4. **Change the UI font size in Global Options.** Expect the Search dialog, reopened, at the new
   size, and the quick-search bar at the old size until jEdit restarts. Say which you saw.


## Constraints on whoever implements this

- **Never run `isabelle build`**, in any session, with any flags.
- Never run `git clean`, `git stash`, `git checkout`, or `git reset --hard`. Shared tree, with
  another session committing to it.
- Do not modify anything under `contrib/Isabelle2025-2/`, `ICSE27/` or `ICSE27-x/`. The base
  font is read from there and copied; the distribution's own file is never touched.
- Do not test against the live X11 display; use `xvfb-run`.
- `contrib/phi-system` is its own git repository; commit there and bump the super-repo.
