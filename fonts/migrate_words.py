#!/usr/bin/env python3
"""Rewrite phi-System's spelled-out keywords as single symbols.

    \\<t>\\<r>\\<a>\\<n>\\<s>\\<f>\\<o>\\<r>\\<m>\\<s>   ->  \\<transforms>

Rules, applied to every maximal run of two or more single-letter symbols:

  skip      the nine words that name a constant or type on their own
            (int bool void aint areal symbol poison changed TP) -- a symbol is
            not a letter, so it cannot be a name; those are handled separately
  \\<Array>  \\<bbbA> followed by the run "rray"  (blackboard-bold A + rray)
  \\<Ptr>    \\<bbbP> followed by the run "tr"
  ASCII     the run touches an ASCII identifier character, i.e. it is part of a
            name (\\<t>\\<y>\\<p>\\<e>\\<o>\\<f>_plus -> typeof_plus), or it follows a
            binder, i.e. it is a bound variable (\\<lambda>\\<r>\\<e>\\<t> -> \\<lambda>ret)
  symbol    everything else

Run with --dry-run to see the counts without touching anything.
"""

import argparse
import collections
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path("/home/qiyuan/Current/MLML/contrib/phi-system")
SYMBOLS_WORDS = ROOT / "symbols-words"
LETTERS_FILE = pathlib.Path("/tmp/letters.txt")

SKIP = {
    # Declared as a constant or a type under that bare name -- a symbol is not a
    # letter, so it cannot be one.  Two patterns find them all, and both are needed:
    #   `\\<w>\\<o>\\<r>\\<d> ::`                    typed declarations, including the
    #                                            second and later name of one `consts`
    #   `<defn-command> [\\<open>] \\<w>\\<o>\\<r>\\<d>`  untyped ones, i.e.
    #                                            `abbreviation \\<open>NAME \\<equiv> ...\\<close>`
    # The second pattern was added after Phi_Examples failed with an inner lexical
    # error on `abbreviation \\<open>\\<r>\\<a>\\<t>\\<i>\\<o>\\<n>\\<a>\\<l> \\<equiv> ...`.
    "int", "bool", "void", "aint", "areal", "symbol", "poison", "changed", "TP",
    "map", "pointer", "dynarr", "hash", "mat", "rational",
    # ML builds names from these at run time (package_values "\\<a>\\<r>\\<g>" ...);
    # rendering them as plain ASCII was rejected, so the spelling stays as it is
    "arg", "ret", "vs",
    # spelling collides with mixfix escaping: "'(" is a literal paren, "''" a literal
    # quote, and in IDE_CP_Applications1 the same text is once a name and once an escape
    # `'` after these is a mixfix escape, so they could in principle migrate --
    # but doing so made Phi_Types.thy raise `exception Option` inside phi's own
    # reasoning, so they stay as they are.
    "open",
}
# Names that ML builds at run time, e.g. Procedure_Syntax.package_values "\\<a>\\<r>\\<g>"
# then Free ("\\<a>\\<r>\\<g>" ^ string_of_int i).  The prefix lives in a string literal, so
# nothing local to the text says it is a name; these words go to plain ASCII everywhere so
# the generated names and the sources that mention them keep agreeing.
FORCE_ASCII = set()   # plain-ASCII names were rejected; see SKIP instead

SPECIAL = {("\\<bbbA>", "rray"): "\\<Array>", ("\\<bbbP>", "tr"): "\\<Ptr>"}
BINDERS = {"\\<lambda>", "\\<forall>", "\\<exists>", "\\<And>"}

# A run glued to a letter symbol is part of a longer identifier and must stay one
# token, so it goes to ASCII -- except where the pair is a mixfix delimiter, whose
# declaration and uses change together.  \<phi>\<s>\<u>\<b>\<j> is `infixl` in
# Phi_Types.thy:144; \<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l> is a fact name.
DELIMITER_AFTER_LETTER = {("\\<phi>", "subj")}

RUN = re.compile(r"(?:\\<[a-zA-Z]>){2,}")
LETTER = re.compile(r"\\<([a-zA-Z])>")
# "(2" and friends inside a mixfix template are pretty-printing block markers, not
# identifier characters: ("(2\<c>\<u>\<r>\<r>\<e>\<n>\<t> _ [_] ...").
BLOCK_MARKER = re.compile(r"\(\d+$")
SYM_BEFORE = re.compile(r"(\\<\^?[A-Za-z][A-Za-z0-9_']*>)$")
SYM_AFTER = re.compile(r"^(\\<\^?[A-Za-z][A-Za-z0-9_']*>)")
IDENT_CHAR = re.compile(r"[A-Za-z0-9_']")


def load_symbol_names():
    """word -> symbol name, e.g. 'open' -> \"open'\" when Isabelle owns the name."""
    out = {}
    for line in SYMBOLS_WORDS.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\\<([A-Za-z][A-Za-z0-9_']*)>.*abbrev:\s*<(\w+)>", line)
        if m:
            out[m.group(2)] = m.group(1)
    return out


SCRIPT = re.compile(r"^(\\<\^(?:sub|sup|isub|isup|bsub|bsup)>)")


# A `'` right after these words is a mixfix escape, not part of a name:
#   ("\<a>..\<n>'(_') \<i>\<s>/ _")   -- '( stands for a literal paren
#   ("\<k>\<v>-\<s>..\<a>''")         -- '' stands for a literal quote
# They are the only non-skipped words ever followed by `'` (checked repo-wide).
# `open` also is, but stays skipped: it is a declared syntax-constant name too.
QUOTE_IS_MIXFIX_ESCAPE = {"abstraction", "schema"}


def identifier_span(text, i, j, letters, stop_at_quote=False):
    """Widen [i,j) over everything Isabelle would lex as one name.

    Names carry letter symbols, ASCII letters and digits, a qualifying `G.`
    prefix, and `\\<^sub>` scripts -- all of which must stay in one token.
    """
    while True:
        m = SYM_BEFORE.search(text[:i])
        if m and m.group(1) in letters:
            i = m.start(1); continue
        if i > 0 and IDENT_CHAR.match(text[i - 1]) and text[i - 1] != ">" \
                and not BLOCK_MARKER.search(text[:i]):
            i -= 1; continue
        if i > 1 and text[i - 1] == "." and (IDENT_CHAR.match(text[i - 2]) or text[i - 2] == ">"):
            i -= 1; continue                      # qualified name: G.\<phi>subj
        break
    while True:
        m = SYM_AFTER.match(text[j:])
        if m and m.group(1) in letters:
            j += m.end(); continue
        m = SCRIPT.match(text[j:])
        if m and j + m.end() < len(text) and IDENT_CHAR.match(text[j + m.end()]):
            j += m.end() + 1; continue            # subscript belongs to the name
        if j < len(text) and IDENT_CHAR.match(text[j]):
            if stop_at_quote and text[j] == "'":
                break
            j += 1; continue
        break
    return i, j


def rewrite(text, names, letters, stats):
    """Return (new_text, reconstructed_text); the second must equal `text`."""
    out, back, pos = [], [], 0
    for m in RUN.finditer(text):
        if m.start() < pos:                       # consumed by a preceding special case
            continue
        word = "".join(LETTER.findall(m.group()))
        sym_before = SYM_BEFORE.search(text[:m.start()])
        left = sym_before.group(1) if sym_before else None

        start, replacement = m.start(), None
        if word in SKIP:
            stats["skip " + word] += 1
        elif word in FORCE_ASCII:
            replacement = word
            stats["ascii (run-time name)"] += 1
        elif left is not None and (left, word) in SPECIAL:
            start = m.start() - len(left)         # swallow \<bbbA> / \<bbbP> too
            replacement = SPECIAL[(left, word)]
            stats["special " + replacement] += 1
        elif left in BINDERS:
            replacement = word                    # bound variable -> plain ASCII
            stats["ascii (bound var)"] += 1
        else:
            quoted = word in QUOTE_IS_MIXFIX_ESCAPE
            lo, hi = identifier_span(text, m.start(), m.end(), letters, quoted)
            if (lo, hi) == (m.start(), m.end()):
                replacement = "\\<%s>" % names[word]
                stats["symbol" + (" (mixfix quote)" if quoted else "")] += 1
            elif (lo, hi) == (m.start() - len(left or ""), m.end()) \
                    and (left, word) in DELIMITER_AFTER_LETTER:
                replacement = "\\<%s>" % names[word]   # \<phi>\<subj>, a mixfix delimiter
                stats["symbol (delimiter after letter)"] += 1
            else:
                replacement = word                # inside a longer name -> plain ASCII
                stats["ascii (name)"] += 1

        if replacement is None:
            continue
        out.append(text[pos:start]); out.append(replacement)
        back.append(text[pos:start]); back.append(text[start:m.end()])
        pos = m.end()
    out.append(text[pos:]); back.append(text[pos:])
    return "".join(out), "".join(back)


def check_result(text, names, letters):
    """A generated symbol must never sit inside something Isabelle lexes as a name."""
    word_of = {sym: word for word, sym in names.items()}
    bad = []
    for name in set(names.values()):
        for m in re.finditer(re.escape("\\<%s>" % name), text):
            lo, hi = identifier_span(text, m.start(), m.end(), letters,
                                     word_of[name] in QUOTE_IS_MIXFIX_ESCAPE)
            if (lo, hi) == (m.start(), m.end()):
                continue
            sb = SYM_BEFORE.search(text[:m.start()])
            left = sb.group(1) if sb else None
            if (lo, hi) == (m.start() - len(left or ""), m.end()) \
                    and (left, word_of[name]) in DELIMITER_AFTER_LETTER:
                continue
            bad.append((name, text[max(0, m.start() - 30):m.end() + 20].replace("\n", " ")))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    names = load_symbol_names()
    letters = set(LETTERS_FILE.read_text().split())
    stats = collections.Counter()
    changed, failures = [], []

    # Always start from the committed text, so the run is repeatable and a fixed
    # rule can simply be re-applied instead of unpicking a previous pass.
    listing = subprocess.run(["git", "ls-files", "*.thy", "*.ML"],
                             cwd=ROOT, capture_output=True, text=True, check=True)
    for rel in sorted(listing.stdout.split()):
        path = ROOT / rel
        text = subprocess.run(["git", "show", "HEAD:" + rel],
                              cwd=ROOT, capture_output=True, text=True, check=True).stdout
        if not RUN.search(text):
            continue
        new, back = rewrite(text, names, letters, stats)
        n_hammer = new.count("by auto_sledgehammer")
        if n_hammer:                       # requested: fall back to the AoA agent
            new = new.replace("by auto_sledgehammer", "by hammer_or_aoa")
            stats["by hammer_or_aoa"] += n_hammer
        if back != text:
            failures.append((path, "round-trip mismatch"))
            continue
        bad = check_result(new, names, letters)
        if bad:
            failures.append((path, "glued symbol: %s" % bad[0][1][:60]))
            continue
        if new != path.read_text(encoding="utf-8"):
            changed.append((path, 0))
            if not args.dry_run:
                path.write_text(new, encoding="utf-8")

    for k, n in sorted(stats.items(), key=lambda kv: -kv[1]):
        print("  %-24s %6d" % (k, n))
    print("\n%d files %s, %d occurrences seen"
          % (len(changed), "would change" if args.dry_run else "changed", sum(stats.values())))
    if failures:
        print("\nFAILED on %d files:" % len(failures))
        for p, why in failures[:10]:
            print("   %s: %s" % (p.relative_to(ROOT), why))
        sys.exit(1)
    print("round-trip and glue checks passed on every file")


if __name__ == "__main__":
    main()
