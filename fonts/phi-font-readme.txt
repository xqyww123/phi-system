PhiSymbols.ttf holds three kinds of glyph.

1. HAND-DRAWN GLYPHS -- source: PhiSymbols.sfd (FontForge)

Glyphs in phi symbol font is copied and modified from the following open fonts,
- Noto Sans Symbol 2
- STIX 2 Math
- DejaVu Sans Mono

Specifically, each glyph in the font comes from,
0x01f799    Noto Sans Symbol 2
0x002023    DejaVu Sans Mono
0x0025C9    Noto Sans Symbol 2
0x0025CF    Noto Sans Symbol 2
0x0025D1    Noto Sans Symbol 2
0x0025D2    Noto Sans Symbol 2
0x00275F    Noto Sans Symbol 2
0x00276c    Noto Sans Symbol 2
0x00276d    Noto Sans Symbol 2
0x002774    Noto Sans Symbol 2
0x002775    Noto Sans Symbol 2
0x002A74    STIX 2 Math
0x0029BC    STIX 2 Math
0x002A38    STIX 2 Math
0x002985    Noto Sans Symbol 2, with modification
0x002986    Noto Sans Symbol 2, with modification
0x00272E    Noto Sans Symbol 2
0x00273C    Noto Sans Symbol 2

The provenance list above records 18 glyphs, but the font carries 61 hand-drawn
code points.  The other 43 were added later without updating this file and their
source is not recorded; they are listed here so the gap is at least visible.
Whoever knows where they came from, please fill it in.

0x00061f    ARABIC QUESTION MARK
0x00207f    SUPERSCRIPT LATIN SMALL LETTER N
0x002080    SUBSCRIPT ZERO
0x002081    SUBSCRIPT ONE
0x002082    SUBSCRIPT TWO
0x002083    SUBSCRIPT THREE
0x002084    SUBSCRIPT FOUR
0x002085    SUBSCRIPT FIVE
0x002086    SUBSCRIPT SIX
0x002087    SUBSCRIPT SEVEN
0x002088    SUBSCRIPT EIGHT
0x002089    SUBSCRIPT NINE
0x002731    HEAVY ASTERISK
0x0027a4    BLACK RIGHTWARDS ARROWHEAD
0x003010    LEFT BLACK LENTICULAR BRACKET
0x003011    RIGHT BLACK LENTICULAR BRACKET
0x00ff1b    FULLWIDTH SEMICOLON
0x01d5a0    MATHEMATICAL SANS-SERIF CAPITAL A
0x01d5a1    MATHEMATICAL SANS-SERIF CAPITAL B
0x01d5a2    MATHEMATICAL SANS-SERIF CAPITAL C
0x01d5a3    MATHEMATICAL SANS-SERIF CAPITAL D
0x01d5a4    MATHEMATICAL SANS-SERIF CAPITAL E
0x01d5a5    MATHEMATICAL SANS-SERIF CAPITAL F
0x01d5a6    MATHEMATICAL SANS-SERIF CAPITAL G
0x01d5a7    MATHEMATICAL SANS-SERIF CAPITAL H
0x01d5a8    MATHEMATICAL SANS-SERIF CAPITAL I
0x01d5a9    MATHEMATICAL SANS-SERIF CAPITAL J
0x01d5aa    MATHEMATICAL SANS-SERIF CAPITAL K
0x01d5ab    MATHEMATICAL SANS-SERIF CAPITAL L
0x01d5ac    MATHEMATICAL SANS-SERIF CAPITAL M
0x01d5ad    MATHEMATICAL SANS-SERIF CAPITAL N
0x01d5ae    MATHEMATICAL SANS-SERIF CAPITAL O
0x01d5af    MATHEMATICAL SANS-SERIF CAPITAL P
0x01d5b0    MATHEMATICAL SANS-SERIF CAPITAL Q
0x01d5b1    MATHEMATICAL SANS-SERIF CAPITAL R
0x01d5b2    MATHEMATICAL SANS-SERIF CAPITAL S
0x01d5b3    MATHEMATICAL SANS-SERIF CAPITAL T
0x01d5b4    MATHEMATICAL SANS-SERIF CAPITAL U
0x01d5b5    MATHEMATICAL SANS-SERIF CAPITAL V
0x01d5b6    MATHEMATICAL SANS-SERIF CAPITAL W
0x01d5b7    MATHEMATICAL SANS-SERIF CAPITAL X
0x01d5b8    MATHEMATICAL SANS-SERIF CAPITAL Y
0x01d5b9    MATHEMATICAL SANS-SERIF CAPITAL Z


2. GENERATED WORD GLYPHS -- source: fonts/build_word_glyphs.py

Each phi-System keyword that used to be spelled one symbol per letter
(\<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>) now has a single symbol whose glyph
draws the whole word (\<transforms>).  135 of them occupy U+E000..U+E086.

Outlines come from STIX Two Math (OFL, see STIX-OFL.txt), from its mathematical
alphanumeric blocks:

  mathematical bold          U+1D400 / U+1D41A   lower-case and mixed-case words
  mathematical bold script   U+1D4D0             all-upper-case words (TP, EIHOOK)

A few words name an ordinary constant rather than a keyword, and are drawn one
weight lighter so that a line full of them does not out-shout the keywords
around them.  The mathematical alphanumeric blocks carry regular and bold and
nothing between them, so those come from STIX Two Text Medium instead, and are
addressed as plain ASCII.

They are composed and scaled by fonts/build_word_glyphs.py and are NOT present
in PhiSymbols.sfd.  Do not edit them by hand -- re-run the script instead.  It
reads fonts/source/PhiSymbols-hand-drawn.ttf and writes this file, so a run has
nothing of its own to undo and running it twice gives the same bytes.  Never
install that source file: it claims the family name PhiSymbols and draws no
printable ASCII.

The word list is fonts/words.txt.  The symbol declarations it generates go to
../symbols-words, which etc/settings adds to ISABELLE_SYMBOLS.

See fonts/WORD_GLYPHS.md for the full rationale: why one word must be one glyph,
why the glyphs cannot live in a separate font, how the symbol names and
abbreviations are chosen, and which seven words carry a trailing prime because
Isabelle already defines a symbol of that name.


3. A MERGED TEXT FACE -- source: the Isabelle fonts component, plus STIX Two Math

This is the bulk of the file.  Sections 1 and 2 draw symbols and words and no
ordinary text at all: between them they cover no printable ASCII.  That is fine
in jEdit's text area, which picks a font per character, but a Swing text
component -- the Find box, the quick-search bar, Isabelle's Query input -- has
one font for the whole component, so a box showing a word glyph beside ordinary
text needs a single family that draws both.  fonts/build_word_glyphs.py makes
PhiSymbols that family by copying a whole text face into it.

  the text face      IsabelleDejaVuSans.ttf, the ttf-hinted variant, from the
                     isabelle_fonts component of Isabelle2025-2 (name ID 5
                     "Version 2.37; ttfautohint (v1.8.4)").  1489 code points,
                     copied outline for outline under the text. glyph prefix.
                     PhiSymbols wins the only two code points both draw,
                     U+061F and U+2023, as it already does in the text area.

  mathematical       850 code points of U+1D400..U+1D7FF that the text face
  alphanumerics      does not draw, from STIX Two Math, under the stix. prefix.
                     STIX is drawn on a 1000-unit em against 2048, so both the
                     outlines and the advances are scaled by 2.048.

The text face is not a single upstream.  Isabelle assembles it from DejaVu Sans
-- itself derived from the Bitstream Vera Fonts, with glyphs imported from the
Arev Fonts -- together with the IsabelleSymbols glyphs, which are Bluesky TeX
fonts scaled 222%, some symbols from Symbola, and blackboard-bold glyphs from
the font txmia of the pxfonts package.  Those last ones are under the GPL, and
26 of them are copied here.  The Isabelle fonts component's own README states
that mixture; it is not paraphrased further, only pointed at.  What the file
itself says is in its name table: name ID 0 names every upstream, ID 13 the
licences, ID 14 this directory, where DejaVu LICENSE, Noto-OFL.txt, STIX-OFL.txt
and GPL-2.0.txt are.  Name ID 0 also carries the four upstream copyright lines
verbatim, because this file travels as a bare .ttf into every generated
presentation directory and into the VS Code extension, where a record pointing
at a directory finds nothing.  No upstream states a GPL version -- CTAN's
pxfonts page, the Isabelle component's README and txmia's own /Notice field all
say just "GPL" -- and the GPL lets the recipient choose when a work names none,
so version 2 is the text included here.

Three things follow that are worth knowing before wondering about them.

The copied glyphs carry ttfautohint bytecode, so the merge also copies the text
face's fpgm, prep and cvt tables and its seven instruction-related maxp maxima.
Those are what the bytecode calls into: with the tables but not the raised
maxima, the interpreter gives up and every glyph in the font draws nothing.
The one cost is that PhiSymbols' own glyphs, which are essentially uninstructed,
now start from the graphics state prep sets, so they rasterise slightly
differently WHEN ANTIALIASING IS OFF.  Under jEdit's shipped
view.antiAlias=subpixel HRGB, and under greyscale antialiasing, nothing changes.

The dates in this font are the hand-drawn font's dates.  head.created is the
FontForge export it came from and head.modified is the last change to that
source, because the merge preserves them rather than stamping the moment the
script ran -- which is what makes two runs produce the same bytes.

Complex-script layout does not survive the merge.  PhiSymbols has a small GDEF
of its own and no GSUB, GPOS or MATH, so the text face's are lost.  Latin is
unaffected -- precomposed accents and fi/fl are single glyphs, and Java's
drawString applies no GPOS kerning anyway -- while Arabic mark positioning
degrades.

See jedit/UI_FONT_PLAN.md for why the merge goes in this direction rather than
into a second font, and jedit/phi_word_clipboard.bsh for the code that hands
the family to a field.
