PhiSymbols.ttf holds two kinds of glyph.

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
draws the whole word (\<transforms>).  133 of them occupy U+E000..U+E084.

Outlines come from STIX Two Math (OFL, see STIX-OFL.txt), from its mathematical
alphanumeric blocks:

  mathematical bold          U+1D400 / U+1D41A   lower-case and mixed-case words
  mathematical bold script   U+1D4D0             all-upper-case words (TP, EIHOOK)

They are composed and scaled by fonts/build_word_glyphs.py and are NOT present
in PhiSymbols.sfd.  Do not edit them by hand -- re-run the script instead; it
drops every glyph it previously added (all named word.<word>) before rebuilding,
so it is safe to run repeatedly and safe to run after re-exporting the .sfd.

The word list is fonts/words.txt.  The symbol declarations it generates go to
../symbols-words, which etc/settings adds to ISABELLE_SYMBOLS.

See fonts/WORD_GLYPHS.md for the full rationale: why one word must be one glyph,
why the glyphs cannot live in a separate font, how the symbol names and
abbreviations are chosen, and which seven words carry a trailing prime because
Isabelle already defines a symbol of that name.
