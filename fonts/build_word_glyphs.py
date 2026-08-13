#!/usr/bin/env python3
"""Render each phi-System keyword as one wide glyph inside PhiSymbols.ttf.

phi-System writes its keywords by spelling them out one symbol per letter, e.g.
``\\<t>\\<r>\\<a>\\<n>\\<s>\\<f>\\<o>\\<r>\\<m>\\<s>``.  This script replaces that with a
single Isabelle symbol per word (``\\<transforms>``) whose glyph draws the whole
word.  Isabelle allows exactly one code point per symbol, so the word has to be
one glyph -- see WORD_GLYPHS.md for why.

Hand-drawn glyphs stay in PhiSymbols.sfd (FontForge).  Word glyphs are generated
here and never enter the .sfd.  The run is idempotent: every glyph this script
previously added carries the ``word.`` name prefix and is dropped first.

Usage:  python3 build_word_glyphs.py [--stix PATH] [--check]
"""

import argparse
import glob
import os
import pathlib
import re
import sys

from fontTools.misc.transform import Transform
from fontTools.pens.boundsPen import BoundsPen
from fontTools.pens.cu2quPen import Cu2QuPen
from fontTools.pens.transformPen import TransformPen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.ttLib import TTFont

HERE = pathlib.Path(__file__).resolve().parent          # contrib/phi-system/fonts
COMPONENT = HERE.parent                                 # contrib/phi-system

FONT = HERE / "PhiSymbols.ttf"
WORDS = HERE / "words.txt"
SYMBOLS_OUT = COMPONENT / "symbols-words"               # generated, listed in etc/settings
SYMBOLS_HAND = COMPONENT / "symbols"                    # hand-maintained
CLIPBOARD_OUT = COMPONENT / "jedit/word-clipboard-text"  # generated, read by phi_word_clipboard.bsh

GLYPH_PREFIX = "word."
FONT_NAME = "PhiSymbols"                                # the `font:` field of every entry
PUA_FIRST = 0xE000                                      # private use area, unused elsewhere
PUA_LAST = 0xE7FF

# Mathematical alphanumeric blocks used as outline sources.
BOLD_CAPITAL_A = 0x1D400        # 𝐀  mathematical bold capital A
BOLD_SMALL_A = 0x1D41A          # 𝐚  mathematical bold small a
BOLD_SCRIPT_CAPITAL_A = 0x1D4D0  # 𝓐  mathematical bold script capital A
SANS_CAPITAL_A = 0x1D5A0        # 𝖠  the code Isabelle gives \<A>
SANS_SMALL_A = 0x1D5BA          # 𝖺  the code Isabelle gives \<a>
SCRIPT_CAPITAL_T = 0x1D4AF      # 𝒯  the code Isabelle gives \<T>; capital size reference

STIX_CANDIDATES = [
    "~/.local/share/fonts/stix2/STIXTwoMath-Regular.otf",
    "/usr/share/fonts/opentype/stix2/STIXTwoMath-Regular.otf",
    "/usr/local/share/fonts/stix2/STIXTwoMath-Regular.otf",
]
STIX_TEXT_CANDIDATES = [
    "~/.local/share/fonts/stix2/STIXTwoText-Medium.otf",
    "/usr/share/fonts/opentype/stix2/STIXTwoText-Medium.otf",
    "/usr/local/share/fonts/stix2/STIXTwoText-Medium.otf",
]

# These words are notation for an ordinary ASCII constant (sem_aint_T and its
# siblings), not keywords, and they are drawn one weight lighter so that a line
# full of them does not out-shout the keywords around it.  The intermediate
# weights exist only in STIX Two Text -- the mathematical alphanumeric blocks
# carry regular and bold and nothing between them -- so these come from
# STIXTwoText-Medium and are addressed as plain ASCII.
#
# `pointer` is not among them: the pointer type prints as \<ptr>, and the only
# thing \<pointer> draws is the operator \<pointer>-\<of>, which is a keyword.
MEDIUM_WORDS = {"aint", "areal", "bool", "int", "map", "poison", "symbol", "void"}


def die(msg):
    sys.exit("build_word_glyphs: " + msg)


def find_font(explicit, candidates, what, option):
    for cand in ([explicit] if explicit else []) + candidates:
        p = pathlib.Path(os.path.expanduser(cand))
        if p.is_file():
            return p
    die("%s not found; pass %s PATH (see WORD_GLYPHS.md)" % (what, option))


def find_isabelle_mono():
    """The font the spelled-out form renders from -- the x-height reference."""
    home = os.environ.get("ISABELLE_HOME") or str(COMPONENT.parent / "Isabelle2025-2")
    hits = glob.glob(home + "/contrib/isabelle_fonts-*/ttf-hinted/IsabelleDejaVuSansMono.ttf")
    if not hits:
        die("IsabelleDejaVuSansMono.ttf not found; set ISABELLE_HOME")
    return pathlib.Path(sorted(hits)[-1])


def read_words():
    out = []
    for line in WORDS.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if not line.isalpha():
            die("not a plain word: %r" % line)
        out.append(line)
    if len(set(out)) != len(out):
        die("duplicate entries in words.txt")
    return out


def taken_symbol_names():
    """Symbol names already claimed by Isabelle or by the hand-maintained table."""
    names = set()
    files = [SYMBOLS_HAND]
    home = os.environ.get("ISABELLE_HOME")
    if home:
        files.append(pathlib.Path(home) / "etc/symbols")
    else:
        files.append(COMPONENT.parent / "Isabelle2025-2/etc/symbols")
    for f in files:
        if not f.is_file():
            continue
        for line in f.read_text(encoding="utf-8").splitlines():
            m = re.match(r"\\<(\^?[A-Za-z][A-Za-z0-9_']*)>", line.strip())
            if m:
                names.add(m.group(1))
    return names


def previous_assignment():
    """word -> code point, so that editing words.txt never renumbers survivors."""
    out = {}
    if SYMBOLS_OUT.is_file():
        for line in SYMBOLS_OUT.read_text(encoding="utf-8").splitlines():
            m = re.match(r"\\<[A-Za-z][A-Za-z0-9_']*>\s+code:\s*(0x[0-9a-fA-F]+).*abbrev:\s*<(\w+)>", line)
            if m:
                out[m.group(2)] = int(m.group(1), 16)
    return out


def source_code_point(ch, all_upper, plain=False):
    if plain:                       # STIX Two Text is an ordinary ASCII font
        return ord(ch)
    if all_upper:
        return BOLD_SCRIPT_CAPITAL_A + ord(ch) - ord("A")
    if ch.isupper():
        return BOLD_CAPITAL_A + ord(ch) - ord("A")
    return BOLD_SMALL_A + ord(ch) - ord("a")


def sans_code_point(ch):
    """The letters the word was spelled out in before it became one glyph."""
    if ch.isupper():
        return SANS_CAPITAL_A + ord(ch) - ord("A")
    return SANS_SMALL_A + ord(ch) - ord("a")


def glyph_height(font, code_point):
    gs, cmap = font.getGlyphSet(), font.getBestCmap()
    if code_point not in cmap:
        die("source font lacks U+%04X" % code_point)
    pen = BoundsPen(gs)
    gs[cmap[code_point]].draw(pen)
    return pen.bounds[3]


def compose(src, word, all_upper, scale, plain=False):
    """Draw `word` left to right into one glyph; return the glyph and its advance."""
    gs, cmap, hmtx = src.getGlyphSet(), src.getBestCmap(), src["hmtx"]
    pen, x = TTGlyphPen(None), 0.0
    for ch in word:
        name = cmap[source_code_point(ch, all_upper, plain)]
        # Cu2QuPen converts STIX's cubic curves to the quadratic ones TrueType needs.
        gs[name].draw(TransformPen(Cu2QuPen(pen, max_err=1.0), Transform(scale, 0, 0, scale, x, 0)))
        x += hmtx[name][0] * scale
    return pen.glyph(), int(round(x))


def drop_generated(font):
    order = [g for g in font.getGlyphOrder() if not g.startswith(GLYPH_PREFIX)]
    for name in set(font.getGlyphOrder()) - set(order):
        font["glyf"].glyphs.pop(name, None)
        font["hmtx"].metrics.pop(name, None)
    for table in font["cmap"].tables:
        for cp in [c for c, n in table.cmap.items() if n.startswith(GLYPH_PREFIX)]:
            del table.cmap[cp]
    font.setGlyphOrder(order)
    font["glyf"].glyphOrder = order


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stix", help="path to STIXTwoMath-Regular.otf")
    ap.add_argument("--stix-text", help="path to STIXTwoText-Medium.otf")
    ap.add_argument("--check", action="store_true", help="verify only, write nothing")
    args = ap.parse_args()

    words = read_words()
    stix = TTFont(str(find_font(args.stix, STIX_CANDIDATES,
                                "STIXTwoMath-Regular.otf", "--stix")))
    stix_text = TTFont(str(find_font(args.stix_text, STIX_TEXT_CANDIDATES,
                                     "STIXTwoText-Medium.otf", "--stix-text")))
    mono = TTFont(str(find_isabelle_mono()))
    font = TTFont(str(FONT))

    if font["head"].unitsPerEm != mono["head"].unitsPerEm:
        die("PhiSymbols and IsabelleDejaVuSansMono disagree on unitsPerEm")

    # Match the spelled-out form's size so nothing grows or shrinks on migration:
    # lower case against the x-height of 𝗑, capitals against the height of 𝒯 (\<T>).
    ref_lower = glyph_height(mono, SANS_SMALL_A + 23)
    ref_upper = glyph_height(mono, SCRIPT_CAPITAL_T)
    scale_lower = ref_lower / glyph_height(stix, BOLD_SMALL_A + 23)
    scale_upper = ref_upper / glyph_height(stix, BOLD_SCRIPT_CAPITAL_A + 19)
    med_lower = ref_lower / glyph_height(stix_text, ord("x"))
    med_upper = ref_upper / glyph_height(stix_text, ord("T"))

    taken = taken_symbol_names()
    assigned = previous_assignment()
    free = (c for c in range(PUA_FIRST, PUA_LAST + 1) if c not in set(assigned.values()))

    drop_generated(font)
    glyf, hmtx = font["glyf"], font["hmtx"]
    order = list(font.getGlyphOrder())
    rows, clip_rows = [], []
    for word in words:
        all_upper = word.isupper()
        plain = word in MEDIUM_WORDS
        src = stix_text if plain else stix
        if plain:
            scale = med_upper if all_upper else med_lower
        else:
            scale = scale_upper if all_upper else scale_lower
        glyph, advance = compose(src, word, all_upper, scale, plain)
        glyph.recalcBounds(glyf)
        gname = GLYPH_PREFIX + word
        code = assigned.get(word) or next(free)
        glyf.glyphs[gname] = glyph
        hmtx.metrics[gname] = (advance, glyph.xMin)
        order.append(gname)
        for table in font["cmap"].tables:
            if table.isUnicode():
                table.cmap[code] = gname
        # A word whose name Isabelle already uses (\<in>, \<open>, ...) gets a prime.
        name = word + "'" if word in taken else word
        rows.append((name, code, word))
        # What the word turns into when it leaves jEdit: the same letters this glyph was
        # drawn from, so the text that lands on the clipboard looks like the glyph.
        # A Medium word has no matching mathematical alphabet, so it falls back to the
        # sans letters it used to be spelled out in -- still not plain ASCII, which
        # would be indistinguishable from an ordinary identifier.
        clip_rows.append((code, "".join(chr(sans_code_point(c)) for c in word) if plain
                          else "".join(chr(source_code_point(c, all_upper)) for c in word)))

    font.setGlyphOrder(order)
    glyf.glyphOrder = order
    font["maxp"].numGlyphs = len(order)

    text = "# Generated by fonts/build_word_glyphs.py -- do not edit.\n" + "".join(
        "\\<%s>%s code: 0x%06X  font: %s  group: letter  abbrev: <%s>\n"
        % (name, " " * max(1, 18 - len(name)), code, FONT_NAME, word)
        for name, code, word in rows)

    clip_text = ("# Generated by fonts/build_word_glyphs.py -- do not edit.\n"
                 "# code point of the word glyph, then the text it becomes on the clipboard.\n"
                 + "".join("0x%06X  %s\n" % row for row in clip_rows))

    if args.check:
        print("%d words, %d code points, would write %d bytes of symbol table"
              % (len(rows), len({c for _, c, _ in rows}), len(text)))
        return
    font.save(str(FONT))
    SYMBOLS_OUT.write_text(text, encoding="utf-8")
    CLIPBOARD_OUT.parent.mkdir(exist_ok=True)
    CLIPBOARD_OUT.write_text(clip_text, encoding="utf-8")
    primed = [n for n, _, _ in rows if n.endswith("'")]
    print("%d word glyphs -> %s" % (len(rows), FONT))
    print("%d symbol entries -> %s" % (len(rows), SYMBOLS_OUT))
    print("%d clipboard entries -> %s" % (len(clip_rows), CLIPBOARD_OUT))
    print("primed to avoid a name clash: %s" % (", ".join(primed) or "none"))


if __name__ == "__main__":
    main()
