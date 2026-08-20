"""Show that every structural check in ../build_word_glyphs.py --check can fail.

Each case damages the build in exactly one way and expects the run to refuse.
`UI_FONT_PLAN.md` makes this a standard -- "a check nobody has seen fail is not
a check" -- and a harness that only ever lived in a scratch directory could not
hold anyone to it, which is why this is committed.

Run it from anywhere:  python3 fonts/archive/break_checks.py

Not every property is guarded here.  Damage to the hinting transplant -- the
fpgm/prep/cvt tables and the seven maxp maxima -- is caught by the ink checks in
jedit/test_word_clipboard.bsh instead, because its signature is that every glyph
in the font draws nothing, which is exactly what a coarse rendering check sees.
"""
import contextlib, importlib, io, pathlib, sys, types

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
sys.argv = ["build_word_glyphs.py", "--check"]
import build_word_glyphs

CASES = []
def case(what):
    def deco(fn):
        CASES.append((what, fn))
        return fn
    return deco


@case("the source glyphs are not deep-copied")
def _(m):
    m.copy = types.SimpleNamespace(deepcopy=lambda x: x)


@case("STIX advances are left on STIX's own em")
def _(m):
    real = m.copy_glyphs_scaled
    def broken(font, src, codes, prefix, scale):
        n = real(font, src, codes, prefix, scale)
        hmtx, cmap = font["hmtx"], src.getBestCmap()
        for code in codes:
            advance, lsb = hmtx[prefix + cmap[code]]
            hmtx.metrics[prefix + cmap[code]] = (int(round(advance / scale)), lsb)
        return n
    m.copy_glyphs_scaled = broken


@case("STIX outlines are left on STIX's own em")
def _(m):
    real_merge, real_draw = m.copy_glyphs_scaled, m.draw_scaled
    def broken(font, src, codes, prefix, scale):
        m.draw_scaled = lambda pen, gs, name, s, x=0.0: real_draw(pen, gs, name, 1.0, x)
        try:
            return real_merge(font, src, codes, prefix, scale)
        finally:
            m.draw_scaled = real_draw
    m.copy_glyphs_scaled = broken


@case("the text face wins the two code points PhiSymbols draws itself")
def _(m):
    real = m.copy_glyphs
    m.copy_glyphs = lambda font, src, codes, prefix: real(
        font, src, sorted(set(codes) | set(m.PHI_WINS)), prefix)


@case("the blank text-face glyph is not supplied from STIX")
def _(m):
    real = m.copy_glyphs_scaled
    m.copy_glyphs_scaled = lambda font, src, codes, prefix, scale: real(
        font, src, [c for c in codes if c != 0x1D5D4], prefix, scale)


@case("prep is not carried over with the rest of the hinting")
def _(m):
    m.HINTING_TABLES = ("fpgm", "cvt ")


@case("a supplementary code point is written into a format 4 cmap subtable")
def _(m):
    def broken(font, code, glyph_name):
        for table in font["cmap"].tables:
            if table.isUnicode():
                table.cmap[code] = glyph_name
    m.map_code_point = broken


@case("nothing is damaged at all")
def _(m):
    pass


failures = 0
for what, damage in CASES:
    m = importlib.reload(build_word_glyphs)
    damage(m)
    out, refused, why = io.StringIO(), False, ""
    try:
        with contextlib.redirect_stdout(out):
            m.main()
    except SystemExit as exc:
        refused, why = True, str(exc)
    except Exception as exc:
        refused, why = True, "%s: %s" % (type(exc).__name__, exc)
    expected = what != "nothing is damaged at all"
    ok = refused == expected
    failures += not ok
    print("%-4s %-62s %s" % ("ok" if ok else "BAD", what, why or "accepted"))
    if refused:
        for line in out.getvalue().splitlines():
            if line.startswith("  "):
                print("       " + line.strip()[:90])
                break
sys.exit(failures and "%d cases behaved unexpectedly" % failures)
