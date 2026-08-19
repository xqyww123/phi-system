#!/usr/bin/env python3
"""Render each phi-System keyword as one wide glyph inside PhiSymbols.ttf.

phi-System writes its keywords by spelling them out one symbol per letter, e.g.
``\\<t>\\<r>\\<a>\\<n>\\<s>\\<f>\\<o>\\<r>\\<m>\\<s>``.  This script replaces that with a
single Isabelle symbol per word (``\\<transforms>``) whose glyph draws the whole
word.  Isabelle allows exactly one code point per symbol, so the word has to be
one glyph -- see WORD_GLYPHS.md for why.

Hand-drawn glyphs stay in PhiSymbols.sfd (FontForge).  Word glyphs are generated
here and never enter the .sfd.  The run is idempotent: every glyph this script
previously added carries one of the ``word.``, ``base.``, ``stix.`` name prefixes
and is dropped first.

The other two prefixes are a whole text face, merged in so that a Swing widget
given the family ``PhiSymbols`` draws ordinary text as well as word glyphs -- a
Swing text component has one font for the whole component, and the hand-drawn
font covers no ASCII at all.  See jedit/UI_FONT_PLAN.md.

Usage:  python3 build_word_glyphs.py [--stix PATH] [--output DIR] [--check]
"""

import argparse
import collections
import copy
import glob
import io
import os
import pathlib
import re
import string
import sys

from fontTools.misc.transform import Transform
from fontTools.pens.boundsPen import BoundsPen
from fontTools.pens.cu2quPen import Cu2QuPen
from fontTools.pens.transformPen import TransformPen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.ttLib import TTFont

HERE = pathlib.Path(__file__).resolve().parent          # contrib/phi-system/fonts
COMPONENT = HERE.parent                                 # contrib/phi-system

FONT = HERE / "PhiSymbols.ttf"                          # always read here; written under --output
WORDS = HERE / "words.txt"
SYMBOLS_OUT = COMPONENT / "symbols-words"               # generated, listed in etc/settings
SYMBOLS_HAND = COMPONENT / "symbols"                    # hand-maintained
CLIPBOARD_OUT = COMPONENT / "jedit/word-clipboard-text"  # generated, read by phi_word_clipboard.bsh
GENERATED = (FONT, SYMBOLS_OUT, CLIPBOARD_OUT)          # everything a run writes

# The Isabelle whose symbol table and fonts this component is generated against.
# Named once: falling back to a different distribution would still parse, and answer
# differently -- contrib/Isabelle2024 is right there.
ISABELLE = "Isabelle2025-2"

# The distribution's own text face, merged in whole; and the mono face, which is only
# the x-height reference the word glyphs are sized against.  Isabelle registers the
# *hinted* variant of both unless the untracked $ISABELLE_HOME_USER/etc/preferences
# sets isabelle_fonts_hinted=false, so the hinted variant is what gets merged.
BASE_FACE = "IsabelleDejaVuSans.ttf"
MONO_FACE = "IsabelleDejaVuSansMono.ttf"
# Every face of the component carries this as name ID 5.  Asserted, so that upgrading
# the distribution fails the build instead of silently ageing the committed font.
ISABELLE_FONT_VERSION = "Version 2.37; ttfautohint (v1.8.4)"

# The glyph name prefixes this script owns, by origin.  drop_generated drops all three
# through this one tuple: extending the script without extending it is completely
# silent, because the "skip what the destination already covers" filter would then find
# everything present, copy nothing, and leave the stale glyphs in place.
GENERATED_PREFIXES = ("word.", "base.", "stix.")
GLYPH_PREFIX, BASE_PREFIX, STIX_PREFIX = GENERATED_PREFIXES

FONT_NAME = "PhiSymbols"                                # the `font:` field of every entry
# The `group:` field.  One tab of jEdit's symbol palette per group name, so the words get
# their own instead of doubling the size of Letter.  jEdit titles the tab by splitting on
# `_` and capitalising each all-lower-case part, so this one reads "Phi Keywords".
GROUP = "phi_Keywords"
PUA_FIRST = 0xE000                                      # private use area, unused elsewhere
PUA_LAST = 0xE7FF

# Mathematical alphanumeric blocks used as outline sources.
BOLD_CAPITAL_A = 0x1D400        # 𝐀  mathematical bold capital A
BOLD_SMALL_A = 0x1D41A          # 𝐚  mathematical bold small a
BOLD_SCRIPT_CAPITAL_A = 0x1D4D0  # 𝓐  mathematical bold script capital A
SANS_CAPITAL_A = 0x1D5A0        # 𝖠  the code Isabelle gives \<A>
SANS_SMALL_A = 0x1D5BA          # 𝖺  the code Isabelle gives \<a>
SCRIPT_CAPITAL_T = 0x1D4AF      # 𝒯  the code Isabelle gives \<T>; capital size reference
MATH_ALPHANUMERIC = range(0x1D400, 0x1D800)   # the block all six live in

# The glyphs copied out of the text face carry ttfautohint bytecode, which needs that
# face's function definitions and its stack depth.  All four travel together: with fpgm
# and prep but not the raised maxima the interpreter gives up and every glyph in the
# font draws nothing -- so all seven instruction-related maxp fields, not the two an
# eye would land on.
HINTING_TABLES = ("fpgm", "prep", "cvt ")
MAXP_HINTING_FIELDS = ("maxFunctionDefs", "maxStackElements", "maxStorage",
                       "maxSizeOfInstructions", "maxTwilightPoints",
                       "maxInstructionDefs", "maxZones")
# What the FontForge export of PhiSymbols.sfd carries, restored by drop_generated so
# that a run starts from the hand-drawn font.  A font that has been merged cannot tell
# us these -- it carries the text face's -- so they are written down here, and checked
# against any font that has not been merged.
PHI_CVT = [68, 1297]
PHI_MAXP_HINTING = (1, 64, 1, 46, 0, 0, 2)

# The only code points both PhiSymbols and the text face draw.  PhiSymbols wins them,
# as it already does in the text area -- `symbols` declares \<rev_quest> and \<tribullet>
# `font: PhiSymbols`.  Asserted, so that a text face growing into phi's territory is a
# build failure rather than a silent change of glyph.
PHI_WINS = frozenset([0x061F, 0x2023])

# Cubic-to-quadratic conversion moves the extrema of a scaled outline by a unit or two,
# in a 2048-unit em.  Anything further is not conversion error.
HEIGHT_TOLERANCE = 8

# Where the outlines come from and under what terms.  Written here rather than in
# PhiSymbols.sfd, which the FontForge export would otherwise own: the obligations come
# from what the merge copies, which is this script's doing and not the hand-drawn font's.
# Whoever re-exports the .sfd runs this script afterwards, so these always reach the
# artefact.  Isabelle's own fonts component ships the same mixture and discloses it in
# its README; this says it inside the file, because the file travels alone -- html.scala
# copies every ISABELLE_FONTS entry as a bare .ttf into each browser-info directory, and
# component_vscode_extension.scala into the VS Code extension, neither with a licence.
COPYRIGHT = (
    "Copyright 2023 Qiyuan Xu.\n"
    "Hand-drawn glyphs are copied and modified from Noto Sans Symbols 2, STIX Two Math "
    "and DejaVu Sans Mono.  The mathematical alphanumerics are copied from STIX Two "
    "Math.  The text face is copied from Isabelle DejaVu Sans, which is DejaVu Sans -- "
    "itself derived from the Bitstream Vera Fonts, with glyphs imported from the Arev "
    "Fonts -- together with the IsabelleSymbols glyphs: Bluesky TeX fonts scaled 222%, "
    "some symbols from Symbola, and the blackboard-bold glyphs from the font txmia of "
    "the pxfonts package, which are subject to the GPL.  See the README of the Isabelle "
    "fonts component for that mixture.")
LICENCE = (
    "This font contains glyphs from upstreams under different licences: the Bitstream "
    "Vera Fonts Copyright and the Arev Fonts Copyright (DejaVu Sans), the SIL Open Font "
    "License 1.1 (STIX Two, Noto Sans Symbols 2), and the GNU General Public License "
    "(the blackboard-bold glyphs from txmia, package pxfonts).  The licence texts are "
    "in the fonts directory named below.")
LICENCE_URL = "https://github.com/xqyww123/phi-system/tree/main/fonts"
# Each upstream the copyright notice has to keep naming, so that shortening the notice
# is a build failure rather than a quiet loss of attribution.
PROVENANCE = ("Noto Sans Symbols 2", "STIX Two", "DejaVu Sans", "Bitstream Vera",
              "txmia", "GPL")

# What the merged font's table set must be.  Written down so that swapping this merge
# for fontTools.merge, which would drag in the text face's GSUB, GPOS and MATH tables
# that PhiSymbols has no counterpart for, cannot pass unnoticed.
MERGED_TABLES = frozenset(["FFTM", "GDEF", "OS/2", "cmap", "cvt ", "fpgm", "gasp",
                           "glyf", "head", "hhea", "hmtx", "loca", "maxp", "name",
                           "post", "prep"])

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


def find_isabelle_font(name):
    """One face of the Isabelle fonts component, hinted -- the variant Isabelle registers.

    One helper for both faces on purpose: resolved separately, the x-height reference
    and the merged text face could come from different variants of the distribution.

    Not resolved through ISABELLE_FONTS: that variable exists only inside Isabelle's
    own settings environment, and WORD_GLYPHS.md documents this script as being run as
    plain `python3 build_word_glyphs.py`.
    """
    home = os.environ.get("ISABELLE_HOME") or str(COMPONENT.parent / ISABELLE)
    hits = glob.glob(home + "/contrib/isabelle_fonts-*/ttf-hinted/" + name)
    if not hits:
        die("%s not found under %s; set ISABELLE_HOME" % (name, home))
    path = pathlib.Path(sorted(hits)[-1])
    with TTFont(str(path)) as probe:
        version = probe["name"].getDebugName(5)
    if version != ISABELLE_FONT_VERSION:
        die("%s is %r, not the %r this component is generated against.  A new "
            "distribution has to be reviewed before the committed font follows it: "
            "everything the merge copies would change at once." % (path, version,
                                                                   ISABELLE_FONT_VERSION))
    return path


SYMBOL_NAME = re.compile(r"[A-Za-z][A-Za-z0-9_']*$")   # all Isabelle admits, symbol.scala:318
DRAWABLE = set(string.ascii_letters + string.digits + "._-")


def read_words():
    """One entry per line: `name`, or `name = drawn text`, or `name = text = abbrevs`.

    The three are normally the same word.  They come apart when the word reads with
    punctuation a symbol name cannot carry: `wrt = w.r.t. = w.r.t,wrt` is named
    `\\<wrt>`, draws `w.r.t.`, and answers to both `<w.r.t>` and `<wrt>`.  The third
    field is a comma-separated list because Isabelle reads one abbreviation per
    `abbrev:` field and takes as many as an entry cares to declare.
    """
    out = []
    for line in WORDS.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        fields = [f.strip() for f in line.split("=")]
        if len(fields) > 3:
            die("more than three fields: %r" % line)
        name = fields[0]
        text = fields[1] if len(fields) > 1 and fields[1] else name
        abbrevs = [a.strip() for a in fields[2].split(",")] if len(fields) > 2 else []
        abbrevs = [a for a in abbrevs if a] or [text]
        if not SYMBOL_NAME.match(name):
            die("not a symbol name Isabelle would accept: %r" % name)
        undrawable = [c for c in text if c not in DRAWABLE]
        if undrawable:
            die("no glyph for %r in %r" % (undrawable[0], text))
        for a in abbrevs:
            # It is typed between angle brackets, and the table is whitespace-separated.
            if any(c in a for c in "<> \t"):
                die("not something you could type as <%s>: %r" % (a, line))
        if len(set(abbrevs)) != len(abbrevs):
            die("the same abbreviation twice: %r" % line)
        out.append((name, text, abbrevs))
    names = [n for n, _, _ in out]
    if len(set(names)) != len(names):
        die("duplicate entries in words.txt")
    return out


def already_taken():
    """Symbol names and abbreviations already claimed by Isabelle or the hand table.

    Missing the Isabelle table is fatal, not something to shrug at: priming is what
    keeps `\\<int>` and `\\<open>` off names Isabelle owns, and it would simply not
    happen, quietly, leaving a table that collides with the distribution's own.
    """
    names, abbrevs = set(), set()
    home = pathlib.Path(os.environ.get("ISABELLE_HOME") or COMPONENT.parent / ISABELLE)
    print("symbol names already taken, from %s and %s" % (SYMBOLS_HAND, home / "etc/symbols"))
    for f in [SYMBOLS_HAND, home / "etc/symbols"]:
        if not f.is_file():
            die("no %s; set ISABELLE_HOME if the distribution moved" % f)
        for line in f.read_text(encoding="utf-8").splitlines():
            m = re.match(r"\\<(\^?[A-Za-z][A-Za-z0-9_']*)>", line.strip())
            if m:
                names.add(m.group(1))
            # Kept verbatim: an Isabelle abbreviation need not be bracketed at all
            # (`abbrev: %`, `abbrev: -->`), so there is no inner text to compare.
            abbrevs.update(re.findall(r"abbrev:\s*(\S+)", line))
    return names, abbrevs


def previous_assignment():
    """symbol name -> code point, so that editing words.txt never renumbers survivors.

    Keyed by the symbol name rather than the word, because the two part company
    once a word carries its own abbreviation.
    """
    out = {}
    if SYMBOLS_OUT.is_file():
        for line in SYMBOLS_OUT.read_text(encoding="utf-8").splitlines():
            m = re.match(r"\\<([A-Za-z][A-Za-z0-9_']*)>\s+code:\s*(0x[0-9a-fA-F]+)", line)
            if m:
                out[m.group(1)] = int(m.group(2), 16)
    return out


def source_code_point(ch, all_upper, plain=False):
    # Punctuation has no mathematical alphabet; it comes from the font's own ASCII,
    # which means a period or an underscore is drawn at the font's regular weight.
    if plain or not ch.isalpha():   # STIX Two Text is an ordinary ASCII font
        return ord(ch)
    if all_upper:
        return BOLD_SCRIPT_CAPITAL_A + ord(ch) - ord("A")
    if ch.isupper():
        return BOLD_CAPITAL_A + ord(ch) - ord("A")
    return BOLD_SMALL_A + ord(ch) - ord("a")


def sans_code_point(ch):
    """The letters the word was spelled out in before it became one glyph."""
    if not ch.isalpha():
        return ord(ch)
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


def draw_scaled(pen, glyph_set, name, scale, x=0.0):
    """Draw one source glyph into `pen`, scaled onto this font's em, at offset x.

    Cu2QuPen converts STIX's cubic curves to the quadratic ones TrueType needs.
    """
    glyph_set[name].draw(TransformPen(Cu2QuPen(pen, max_err=1.0),
                                      Transform(scale, 0, 0, scale, x, 0)))


def compose(src, word, all_upper, scale, plain=False):
    """Draw `word` left to right into one glyph; return the glyph and its advance."""
    gs, cmap, hmtx = src.getGlyphSet(), src.getBestCmap(), src["hmtx"]
    pen, x = TTGlyphPen(None), 0.0
    for ch in word:
        name = cmap[source_code_point(ch, all_upper, plain)]
        draw_scaled(pen, gs, name, scale, x)
        x += hmtx[name][0] * scale
    return pen.glyph(), int(round(x))


def map_code_point(font, code, glyph_name):
    """Point `code` at `glyph_name` in every Unicode subtable that can hold it.

    Format 4 is BMP-only: writing a supplementary code point into one makes font.save
    die with OverflowError.
    """
    for table in font["cmap"].tables:
        if table.isUnicode() and (code <= 0xFFFF or table.format == 12):
            table.cmap[code] = glyph_name


def merge_face(font, src, code_points, prefix):
    """Copy `src`'s glyphs for `code_points` into `font`, named `prefix` + source name.

    Deep-copied: storing a source glyph object and then renaming the components of a
    composite would rewrite the source's own composites, and the text face has 180 of
    them, in the very object this run keeps reading.  A component comes along whether
    or not a code point addresses it.
    """
    glyf, hmtx, order = font["glyf"], font["hmtx"], font.getGlyphOrder()
    src_glyf, src_hmtx, src_cmap = src["glyf"], src["hmtx"], src.getBestCmap()
    copied = set()

    def take(name):
        if name in copied:
            return
        copied.add(name)
        glyph = copy.deepcopy(src_glyf[name])
        for component in glyph.components if glyph.isComposite() else []:
            take(component.glyphName)
            component.glyphName = prefix + component.glyphName
        glyf.glyphs[prefix + name] = glyph
        hmtx.metrics[prefix + name] = src_hmtx[name]
        order.append(prefix + name)

    for code in code_points:
        take(src_cmap[code])
        map_code_point(font, code, prefix + src_cmap[code])
    return len(copied)


def merge_scaled_face(font, src, code_points, prefix, scale):
    """The same, from a source drawn on a different em -- STIX's 1000 against 2048.

    Both halves of the correction matter, and each hides the other's absence: scaled
    outlines with unscaled advances leaves the letters overlapping, scaled advances
    with unscaled outlines draws them at half size while every width still checks out.
    """
    glyf, hmtx, order = font["glyf"], font["hmtx"], font.getGlyphOrder()
    gs, src_hmtx, src_cmap = src.getGlyphSet(), src["hmtx"], src.getBestCmap()
    for code in code_points:
        name = src_cmap[code]
        if prefix + name not in glyf.glyphs:
            pen = TTGlyphPen(None)
            draw_scaled(pen, gs, name, scale)
            glyph = pen.glyph()
            glyph.recalcBounds(glyf)
            glyf.glyphs[prefix + name] = glyph
            hmtx.metrics[prefix + name] = (int(round(src_hmtx[name][0] * scale)),
                                           glyph.xMin)
            order.append(prefix + name)
        map_code_point(font, code, prefix + name)


def set_name_records(font):
    """Say inside the file where the outlines came from and under what terms.

    Both platforms the font already carries records for.  Setting them to a constant is
    what makes this idempotent -- there is nothing for drop_generated to undo.
    """
    for name_id, text in ((0, COPYRIGHT), (13, LICENCE), (14, LICENCE_URL)):
        for platform_id, encoding_id, language_id in ((1, 0, 0), (3, 1, 0x409)):
            font["name"].setName(text, name_id, platform_id, encoding_id, language_id)


def maxp_hinting(font):
    return tuple(getattr(font["maxp"], field) for field in MAXP_HINTING_FIELDS)


def set_maxp_hinting(font, values):
    for field, value in zip(MAXP_HINTING_FIELDS, values):
        setattr(font["maxp"], field, value)


def drop_generated(font):
    """Undo everything this script adds, so that a run starts from the hand-drawn font."""
    order = [g for g in font.getGlyphOrder() if not g.startswith(GENERATED_PREFIXES)]
    merged = any(g.startswith(BASE_PREFIX) for g in font.getGlyphOrder())
    for name in set(font.getGlyphOrder()) - set(order):
        font["glyf"].glyphs.pop(name, None)
        font["hmtx"].metrics.pop(name, None)
    for table in font["cmap"].tables:
        for cp in [c for c, n in table.cmap.items() if n.startswith(GENERATED_PREFIXES)]:
            del table.cmap[cp]
    font.setGlyphOrder(order)
    font["glyf"].glyphOrder = order
    # The merge changes more than glyphs, and leaving any of it in place would compound
    # over runs.  A font that has never been merged instead has the values checked, so
    # that re-exporting the .sfd with different hinting is not silently overwritten.
    if merged:
        del font["fpgm"], font["prep"]
        font["cvt "].values = list(PHI_CVT)
        set_maxp_hinting(font, PHI_MAXP_HINTING)
    elif (list(font["cvt "].values), maxp_hinting(font)) != (PHI_CVT, PHI_MAXP_HINTING):
        die("%s carries hinting this script does not know about.  PHI_CVT and "
            "PHI_MAXP_HINTING describe the FontForge export and must be updated "
            "together with it." % FONT)
    # fontTools' format 2.0 `post` encoder appends a glyph name and never removes one,
    # so the committed font still carries word.tr from a word deleted long ago.  Emptied
    # here, and rebuilt from the live glyph order on save.
    font["post"].extraNames = []


def outline_key(glyf, name, prefix=""):
    """What "this is the same glyph" means, comparably across two fonts.

    The points, their flags, and the hinting bytecode -- everything a rasteriser draws
    from.  Two things a glyph also carries are deliberately left out, because they
    differ between two fonts without the drawing differing at all: the stored bounding
    box, which fontTools recomputes from the outline on save and which the text face
    pads by a unit on 52 of its glyphs, and the glyph *ids* a composite compiles its
    components to.  A composite is therefore compared component by component, with the
    copy's name prefix taken back off.
    """
    glyph = glyf[name]
    program = glyph.program.getBytecode() if hasattr(glyph, "program") else b""
    if glyph.isComposite():
        shape = tuple((c.glyphName.removeprefix(prefix),
                       {k: v for k, v in vars(c).items() if k != "glyphName"})
                      for c in glyph.components)
    elif glyph.numberOfContours == 0:
        shape = ()
    else:
        shape = (tuple(glyph.endPtsOfContours), list(glyph.coordinates),
                 list(glyph.flags))
    return shape, program


def glyph_state(font, name):
    """All this script promises not to change about a glyph: its outline and its metrics."""
    return outline_key(font["glyf"], name), font["hmtx"][name]


def unchanged(font, path):
    """Whether a source font still says exactly what its file says.

    The merge deep-copies for a reason: renaming a copied composite's components in
    place would rewrite this font's own, and nothing else in the run would notice.
    """
    with TTFont(str(path)) as fresh:
        if (font.getGlyphOrder() != fresh.getGlyphOrder()
                or font["hmtx"].metrics != fresh["hmtx"].metrics
                or font.getBestCmap() != fresh.getBestCmap()):
            return False
        if "glyf" not in font:
            return True                     # STIX is CFF: no glyf to compare
        return all(outline_key(font["glyf"], n) == outline_key(fresh["glyf"], n)
                   for n in font.getGlyphOrder())


def check_font(font, base, base_path, stix, stix_path, phi_before, stix_codes, clip_rows):
    """Every structural property jedit/UI_FONT_PLAN.md asks the merged font to have.

    Font data, never rendered pixels.  The property wanted is "the text face's glyphs
    were copied unchanged", and that is a statement about glyf outlines and hmtx
    integers: exact, independent of every rendering configuration, and far faster than
    drawing.  What rendering can say -- does this draw ink at all -- is coarse enough to
    be stable, and is checked in jedit/test_word_clipboard.bsh instead.
    """
    problems = []

    def want(ok, message):
        if not ok:
            problems.append(message)

    glyf, cmap, hmtx = font["glyf"], font.getBestCmap(), font["hmtx"]
    base_glyf, base_cmap, base_hmtx = base["glyf"], base.getBestCmap(), base["hmtx"]
    stix_cmap, stix_glyphs = stix.getBestCmap(), stix.getGlyphSet()
    phi_codes = set(phi_before)

    # The text face was copied unchanged, but for two classes of exception -- each an
    # equality, so that anything else differing is a failure rather than a widening.
    supplied = set()
    for code, name in sorted(base_cmap.items()):
        if code in phi_codes:
            continue
        if code not in cmap:
            want(False, "U+%04X of the text face is missing" % code)
            continue
        mine = cmap[code]
        if base_glyf[name].numberOfContours == 0 and glyf[mine].numberOfContours != 0:
            supplied.add(code)
            continue
        want(outline_key(glyf, mine, BASE_PREFIX) == outline_key(base_glyf, name)
             and hmtx[mine] == base_hmtx[name],
             "U+%04X does not draw as the text face draws it" % code)
    want(supplied == set(stix_codes) & set(base_cmap),
         "supplied over a blank text-face glyph: %s, expected %s"
         % (sorted(supplied), sorted(set(stix_codes) & set(base_cmap))))
    want(phi_codes & set(base_cmap) == PHI_WINS,
         "PhiSymbols and the text face overlap on %s, not %s"
         % (sorted(phi_codes & set(base_cmap)), sorted(PHI_WINS)))

    # Nothing PhiSymbols draws itself, word glyphs included, moved in the merge.
    for code, before in phi_before.items():
        want(code in cmap and glyph_state(font, cmap[code]) == before,
             "U+%04X, which PhiSymbols draws itself, changed in the merge" % code)

    # Everything a pasted word glyph can turn into draws: the glyph and its letters.
    for code, clip in clip_rows:
        for ch in chr(code) + clip:
            want(ord(ch) in cmap and glyf[cmap[ord(ch)]].numberOfContours != 0,
                 "U+%04X, which the clipboard text uses, draws nothing" % ord(ch))

    # The mathematical alphanumerics draw, rather than merely appearing in the cmap.
    for code in MATH_ALPHANUMERIC:
        if code in stix_cmap:
            want(code in cmap and glyf[cmap[code]].numberOfContours != 0,
                 "U+%04X of the mathematical alphanumerics draws nothing" % code)

    # The em correction, in both dimensions.
    scale = font["head"].unitsPerEm / stix["head"].unitsPerEm
    for code in stix_codes:
        if code not in cmap:
            continue                        # already reported as missing above
        name, src_name = cmap[code], stix_cmap[code]
        want(hmtx[name][0] == int(round(stix["hmtx"][src_name][0] * scale)),
             "U+%04X is not as wide as STIX's glyph scaled" % code)
        pen = BoundsPen(stix_glyphs)
        stix_glyphs[src_name].draw(pen)
        if pen.bounds is None:
            continue
        wanted = (pen.bounds[3] - pen.bounds[1]) * scale
        height = glyf[name].yMax - glyf[name].yMin
        # The lower bound is the half that catches an outline left on STIX's own
        # 1000-unit em, which is otherwise invisible: every width still checks out and
        # the letters merely come out at half size.
        want(abs(height - wanted) <= HEIGHT_TOLERANCE and height >= 0.9 * wanted,
             "U+%04X is %d units tall, not the %d STIX's glyph scales to"
             % (code, height, wanted))

    for source, path in ((base, base_path), (stix, stix_path)):
        want(unchanged(source, path), "%s was modified by this run" % path)

    tables = set(font.keys()) - {"GlyphOrder"}
    want(tables == MERGED_TABLES, "the merged font carries the tables %s, expected %s"
         % (sorted(tables), sorted(MERGED_TABLES)))

    names = font["name"]
    want(names.getDebugName(13) and names.getDebugName(14),
         "no licence (name ID 13) and licence URL (name ID 14) in the name table")
    notice = names.getDebugName(0) or ""
    for who in PROVENANCE:
        want(who in notice, "the copyright notice does not name %s" % who)

    for message in problems[:20]:
        print("  " + message)
    if len(problems) > 20:
        print("  ... and %d more" % (len(problems) - 20))
    if problems:
        die("%d structural checks failed" % len(problems))
    print("structural checks: all passed")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stix", help="path to STIXTwoMath-Regular.otf")
    ap.add_argument("--stix-text", help="path to STIXTwoText-Medium.otf")
    ap.add_argument("--output", metavar="DIR", help="write the generated files under DIR, "
                    "in the component's own layout, instead of over the committed ones")
    ap.add_argument("--check", action="store_true", help="verify only, write nothing")
    args = ap.parse_args()

    words = read_words()
    stix_path = find_font(args.stix, STIX_CANDIDATES, "STIXTwoMath-Regular.otf", "--stix")
    stix_text_path = find_font(args.stix_text, STIX_TEXT_CANDIDATES,
                               "STIXTwoText-Medium.otf", "--stix-text")
    base_path, mono_path = find_isabelle_font(BASE_FACE), find_isabelle_font(MONO_FACE)
    stix, stix_text = TTFont(str(stix_path)), TTFont(str(stix_text_path))
    base, mono = TTFont(str(base_path)), TTFont(str(mono_path))
    # Without recalcTimestamp=False every run differs from the last in head.modified
    # alone, and the committed font stops being determined by its inputs.
    font = TTFont(str(FONT), recalcTimestamp=False)

    # The merge copies outlines verbatim, so the text face has to agree as well.
    for other, what in ((mono, MONO_FACE), (base, BASE_FACE)):
        if font["head"].unitsPerEm != other["head"].unitsPerEm:
            die("PhiSymbols and %s disagree on unitsPerEm" % what)

    # Match the spelled-out form's size so nothing grows or shrinks on migration:
    # lower case against the x-height of 𝗑, capitals against the height of 𝒯 (\<T>).
    ref_lower = glyph_height(mono, SANS_SMALL_A + 23)
    ref_upper = glyph_height(mono, SCRIPT_CAPITAL_T)
    scale_lower = ref_lower / glyph_height(stix, BOLD_SMALL_A + 23)
    scale_upper = ref_upper / glyph_height(stix, BOLD_SCRIPT_CAPITAL_A + 19)
    med_lower = ref_lower / glyph_height(stix_text, ord("x"))
    med_upper = ref_upper / glyph_height(stix_text, ord("T"))

    taken, taken_abbrevs = already_taken()
    assigned = previous_assignment()
    # Every code point already in use comes from `symbols-words`, and every source that
    # writes one of these symbols depends on it staying put.  If that file is lost, this
    # run would hand out fresh code points from PUA_FIRST in words.txt order and every
    # such source would silently start rendering the wrong word.  A font that already
    # carries word glyphs is proof this is not the first run.
    if not assigned and any(g.startswith(GLYPH_PREFIX) for g in font.getGlyphOrder()):
        die("%s is missing or unreadable, but %s already has word glyphs: regenerating "
            "now would renumber every symbol.  Restore it from git." % (SYMBOLS_OUT, FONT))
    free = (c for c in range(PUA_FIRST, PUA_LAST + 1) if c not in set(assigned.values()))

    drop_generated(font)
    glyf, hmtx = font["glyf"], font["hmtx"]
    # The live glyph order, not a snapshot of it: one object, so that every position
    # after drop_generated is correct by construction rather than by remembering to
    # take the copy late enough.
    order = font.getGlyphOrder()
    rows, clip_rows = [], []
    for word, drawn, abbrevs in words:
        all_upper = drawn.isupper()
        plain = word in MEDIUM_WORDS
        src = stix_text if plain else stix
        if plain:
            scale = med_upper if all_upper else med_lower
        else:
            scale = scale_upper if all_upper else scale_lower
        glyph, advance = compose(src, drawn, all_upper, scale, plain)
        glyph.recalcBounds(glyf)
        gname = GLYPH_PREFIX + word
        # A word whose name Isabelle already uses (\<in>, \<open>, ...) gets a prime.
        name = word + "'" if word in taken else word
        # If that verdict ever flips -- a new Isabelle claims a name this table already
        # uses, or gives one back -- the symbol silently changes name and takes a fresh
        # code point, and every source that wrote the old one breaks with no diagnostic.
        # Refuse instead, and let whoever upgrades decide.
        other = word + "'" if name == word else word
        if name not in assigned and other in assigned:
            die("%r was \\<%s> and is now \\<%s>: Isabelle's symbol table changed under "
                "this component.  Every source writing the old symbol must be rewritten."
                % (word, other, name))
        code = assigned.get(name) or next(free)
        glyf.glyphs[gname] = glyph
        hmtx.metrics[gname] = (advance, glyph.xMin)
        order.append(gname)
        map_code_point(font, code, gname)
        rows.append((name, code, abbrevs))
        # What the word turns into when it leaves jEdit: the same letters this glyph was
        # drawn from, so the text that lands on the clipboard looks like the glyph.
        # A Medium word has no matching mathematical alphabet, so it falls back to the
        # sans letters it used to be spelled out in -- still not plain ASCII, which
        # would be indistinguishable from an ordinary identifier.
        clip = ("".join(chr(sans_code_point(c)) for c in drawn) if plain
                else "".join(chr(source_code_point(c, all_upper)) for c in drawn))
        # Enforced, because getting it wrong is silent and wide: phi_word_clipboard.bsh
        # folds these letters back into the glyph on paste, so an ASCII letter here
        # would turn the word into a glyph wherever it occurs in ordinary English.
        # Nothing above can produce one today -- both mappings send letters into a
        # mathematical block -- and the plausible future change that would ("the Medium
        # glyph is drawn from plain ASCII, so let its clipboard text be too") is wrong
        # for a reason invisible from inside this file.
        if any(c.isascii() and c.isalpha() for c in clip):
            die("%r would put ASCII letters on the clipboard: %r" % (word, clip))
        clip_rows.append((code, clip))

    # ---- the merged text face ---------------------------------------------------
    # Which font supplies a code point is decided here, once, against the original text
    # face and PhiSymbols -- never against the destination mid-merge, where the answer
    # would be an artefact of the order of the statements below.
    phi_cmap = font.getBestCmap()
    phi_before = {c: glyph_state(font, n) for c, n in phi_cmap.items()}
    base_cmap, base_glyf, stix_cmap = base.getBestCmap(), base["glyf"], stix.getBestCmap()
    # The mathematical alphanumerics the text face does not draw: it lacks most of the
    # block outright, and maps one code point in it to a glyph with no outline.
    stix_codes = sorted(c for c in MATH_ALPHANUMERIC
                        if c in stix_cmap and c not in phi_cmap
                        and (c not in base_cmap
                             or base_glyf[base_cmap[c]].numberOfContours == 0))
    # PhiSymbols draws U+061F and U+2023 itself and wins them, as it already does in
    # the text area: `symbols` declares both `font: PhiSymbols`.
    base_codes = sorted(set(base_cmap) - set(phi_cmap) - set(stix_codes))
    copied = merge_face(font, base, base_codes, BASE_PREFIX)
    merge_scaled_face(font, stix, stix_codes, STIX_PREFIX,
                      font["head"].unitsPerEm / stix["head"].unitsPerEm)
    for tag in HINTING_TABLES:
        font[tag] = copy.deepcopy(base[tag])
    set_maxp_hinting(font, maxp_hinting(base))
    set_name_records(font)

    font.setGlyphOrder(order)
    glyf.glyphOrder = order
    font["maxp"].numGlyphs = len(order)

    # An abbreviation is what gets typed, so a collision would silently offer the wrong
    # symbol -- and it stays silent, because Isabelle takes both without complaint.
    mine = collections.Counter(a for _, _, abbrevs in rows for a in abbrevs)
    for a, n in sorted(mine.items()):
        if n > 1:
            die("<%s> is the abbreviation of %d words" % (a, n))
        if "<%s>" % a in taken_abbrevs:
            die("<%s> is already an abbreviation in %s or Isabelle's table" % (a, SYMBOLS_HAND))

    text = "# Generated by fonts/build_word_glyphs.py -- do not edit.\n" + "".join(
        "\\<%s>%s code: 0x%06X  font: %s  group: %s%s\n"
        % (name, " " * max(1, 18 - len(name)), code, FONT_NAME, GROUP,
           "".join("  abbrev: <%s>" % a for a in abbrevs))
        for name, code, abbrevs in rows)

    clip_text = ("# Generated by fonts/build_word_glyphs.py -- do not edit.\n"
                 "# code point of the word glyph, then the text it becomes on the clipboard.\n"
                 + "".join("0x%06X  %s\n" % row for row in clip_rows))

    print("%d words, %d text-face code points in %d glyphs, %d mathematical "
          "alphanumerics from STIX"
          % (len(rows), len(base_codes), copied, len(stix_codes)))
    if args.check:
        # Checked after a round trip through the file format, so that the artefact is
        # what gets checked rather than this script's model of it -- writing a
        # supplementary code point into a format 4 cmap subtable, for one, fails
        # nowhere but in font.save.
        written = io.BytesIO()
        font.save(written)
        written.seek(0)
        check_font(TTFont(written), base, base_path, stix, stix_path, phi_before,
                   stix_codes, clip_rows)
        return

    # Under --output the same three files, in the same layout, somewhere else: a check
    # build must never be able to touch the committed ones.
    root = pathlib.Path(args.output) if args.output else COMPONENT
    font_out, symbols_out, clipboard_out = [root / p.relative_to(COMPONENT)
                                            for p in GENERATED]
    for path in (font_out, symbols_out, clipboard_out):
        path.parent.mkdir(parents=True, exist_ok=True)
    font.save(str(font_out))
    symbols_out.write_text(text, encoding="utf-8")
    clipboard_out.write_text(clip_text, encoding="utf-8")
    primed = [n for n, _, _ in rows if n.endswith("'")]
    print("%d word glyphs and a merged text face -> %s" % (len(rows), font_out))
    print("%d symbol entries -> %s" % (len(rows), symbols_out))
    print("%d clipboard entries -> %s" % (len(clip_rows), clipboard_out))
    print("primed to avoid a name clash: %s" % (", ".join(primed) or "none"))


if __name__ == "__main__":
    main()
