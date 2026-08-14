#!/usr/bin/env python3
"""Rewrite phi-System's spelled-out keywords as single symbols.

    \\<t>\\<r>\\<a>\\<n>\\<s>\\<f>\\<o>\\<r>\\<m>\\<s>   ->  \\<transforms>

Rules, applied to every maximal run of two or more single-letter symbols:

  skip      the words that still name a constant or type on their own (see SKIP)
            -- a symbol is not a letter, so it cannot be a name
  patch     the declarations that DECL_PATCHES rewrites: the eight semantic type
            constants become ASCII names carrying the word as notation
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
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path("/home/qiyuan/Current/MLML/contrib/phi-system")
SYMBOLS_WORDS = ROOT / "symbols-words"

SKIP = {
    # Declared as a constant or a type under that bare name -- a symbol is not a
    # letter, so it cannot be one.  Two patterns find them all, and both are needed:
    #   `\\<w>\\<o>\\<r>\\<d> ::`                    typed declarations, including the
    #                                            second and later name of one `consts`
    #   `<defn-command> [\\<open>] \\<w>\\<o>\\<r>\\<d>`  untyped ones, i.e.
    #                                            `abbreviation \\<open>NAME \\<equiv> ...\\<close>`
    # The second pattern was added after Phi_Examples failed with an inner lexical
    # error on `abbreviation \\<open>\\<r>\\<a>\\<t>\\<i>\\<o>\\<n>\\<a>\\<l> \\<equiv> ...`.
    "TP", "dynarr", "hash", "mat", "rational",
    # ML builds names from these at run time (package_values "\\<a>\\<r>\\<g>" ...);
    # rendering them as plain ASCII was rejected, so the spelling stays as it is
    "arg", "ret", "vs",
}
# Names that ML builds at run time, e.g. Procedure_Syntax.package_values "\\<a>\\<r>\\<g>"
# then Free ("\\<a>\\<r>\\<g>" ^ string_of_int i).  The prefix lives in a string literal, so
# nothing local to the text says it is a name; these words go to plain ASCII everywhere so
# the generated names and the sources that mention them keep agreeing.
FORCE_ASCII = set()   # plain-ASCII names were rejected; see SKIP instead

# What a run spells when it turns out to sit inside a longer name.  Normally the word
# itself; `int` is the exception, because the thing every such name talks about is the
# type, and the type is called `int_t` -- `int` alone would read as the semantic type
# constructor `sem_int_T`, which is a different constant.
EMBEDDED_ASCII = {"int": "int_t"}

# The eight semantic type constants used to be named by the spelling itself, which is
# why they were skipped too: a symbol is not a letter, so it cannot be a name.  They
# are now ordinary ASCII constants (`sem_aint_T` and siblings, following `sem_tup_T`)
# carrying the word as notation, so their spelling is free to migrate like any other
# -- except at the declaration, and at the three sites that name the constant instead
# of using it (`\\<^const_name>`/`\\<^const_syntax>`, which take the internal name).
# Those are patched here, on the text as it comes out of HEAD and before any run is
# rewritten, so the whole migration stays one function of HEAD.
DECL_PATCHES = {
    # `size_\<t>` is the address-space word width expressed as a type -- the pointer-side
    # twin of `int_t`, with the same comment on it.  A symbol is not a letter, so the
    # name goes to ASCII and the word becomes notation.  Only the sites that need the
    # name rather than the notation are patched; every use is left to RENAMES.
    "Phi_Semantics/PhiSem_Mem_Pointer.thy": [
        (r'typedecl size_\<t> \<comment>', r'typedecl size_t ("\<size_t>") \<comment>'),
        (r'instantiation size_\<t> :: len begin', r'instantiation size_t :: len begin'),
        (r'definition [iff]: "len_of_size_\<t> (_::size_\<t> itself) = addrspace_bits"',
         r'definition [iff]: "len_of_size_t (_::size_t itself) = addrspace_bits"')],
    # this whole file is one 200-line comment, `(*theory` to `end*)`, and nothing
    # imports it; the line is patched only so the dead code stays coherent
    "Phi_Semantics/PhiSem_Pointer_Mem.thy": [(
        r'type_synonym size_\<t> = \<open>addr_cap word\<close>',
        r'type_synonym size_t = \<open>addr_cap word\<close> ("\<size_t>")')],
    # the term-level twin of the type, exactly as `sem_int_t'` is for `int_t`: the
    # machine integer at the address-space width.  Its name is what makes this a
    # declaration rather than a use, so the notation has to be spelled out.
    "Phi_Semantics/PhiSem_Mem_C_MI.thy": [(
        r'''abbreviation \<open>size_\<t> \<equiv> \<int'>(size_\<t>)\<close>''',
        '''abbreviation sem_size_t ("\\<size_t>")\n'''
        r'''  where \<open>sem_size_t \<equiv> \<int'>(size_t)\<close>''')],
}

# Entries are dropped once the round that needed them is committed: this script rewrites
# the working tree from HEAD, so a patch whose text is already in HEAD no longer applies
# and would only fail.  What earlier rounds did is recorded in their commits and in
# PHI_WORD_SYMBOL_MIGRATION.md.

# Plain ASCII renames.  They have nothing to do with the spelling migration; they live
# here because this script always rewrites the working tree from HEAD, so a rename done
# in a separate pass would be undone by the next run.
#
# `semty_ntup` is the one TY constructor not shaped like `sem_tup_T`.  Only the bare
# name moves: `semty_` is this codebase's prefix for the lemmas and auxiliaries around a
# TY, and `semty_tup_eq_poison`, `semty_tup_empty` and `_semty_tup` already sit beside
# `sem_tup_T` in exactly that way, so their `ntup` counterparts are left alone.
RENAMES = {
    # the one primitive TY constructor not shaped like `sem_tup_T`; `mk_` in this
    # codebase means a derived convenience (`mk_int_T = sem_int_T o len_of`), while
    # `sem_mk_array` right beside it makes a value, not a type
    "mk_array_T": "sem_array_T",
    # a mixfix delimiter, nothing is named by it.  The symbol cannot be `\<w.r.t.>`:
    # a symbol name admits only [A-Za-z][A-Za-z0-9_']*, so the periods live in the
    # glyph and in the abbreviation `<w.r.t>`, not in the name.
    "\\<w>.\\<r>.\\<t>": "\\<wrt>",
    # every use of the type; its declaration sites are in DECL_PATCHES above, and a
    # name that embeds it (`len_of_size_\<t>`) is excluded by the identifier boundary
    "size_\\<t>": "\\<size_t>",
}
RENAME = re.compile(r"(?<![A-Za-z0-9_'])(%s)(?![A-Za-z0-9_'])"
                    % "|".join(re.escape(k) for k in sorted(RENAMES, key=len, reverse=True)))

# A name antiquotation takes the constant's internal name, so a generated symbol must
# never end up inside one; anything DECL_PATCHES misses is caught here rather than at
# build time.
NAME_ANTIQUOTATION = re.compile(
    r"\\<\^(?:const_name|const_syntax|type_name|type_syntax|const_abbrev)>"
    r"\\<open>(.*?)\\<close>")

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
        m = re.match(r"\\<([A-Za-z][A-Za-z0-9_']*)>.*abbrev:\s*<([^>]+)>", line)
        if m:
            out[m.group(2)] = m.group(1)
    return out


def load_letters():
    """The symbols Isabelle admits inside an identifier, read from its own source.

    `symbol.ML` lists `\\<lambda>` among them with a `sic!` beside it; here it must
    not be one, or a bound variable written right after a binder would be widened
    into the binder's own token.
    """
    home = pathlib.Path(os.environ.get("ISABELLE_HOME") or ROOT.parent / "Isabelle2025-2")
    src = (home / "src/Pure/General/symbol.ML").read_text(encoding="utf-8")
    i = src.index("val letter_symbols =")
    out = set(re.findall(r'"(\\<[^">]*>)"', src[i:src.index("];", i)]))
    if len(out) < 100:
        sys.exit("migrate_words: could not read the letter symbols from symbol.ML")
    return out - {"\\<lambda>"}


SCRIPT = re.compile(r"^(\\<\^(?:sub|sup|isub|isup|bsub|bsup)>)")


# A `'` right after these words is a mixfix escape, not part of a name:
#   ("\<a>..\<n>'(_') \<i>\<s>/ _")   -- '( stands for a literal paren
#   ("\<k>\<v>-\<s>..\<a>''")         -- '' stands for a literal quote
# They are the only non-skipped words ever followed by `'` (checked repo-wide).
# `open` is here for the glue check rather than for the rewriting: DECL_PATCHES writes
# its every site, but one of them is ("\<open'>'(_')") and the check has to read the
# trailing `'` as the escape it is instead of as one more letter of a name.
QUOTE_IS_MIXFIX_ESCAPE = {"abstraction", "schema", "open", "int"}


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
            else:                                 # inside a longer name -> plain ASCII
                replacement = EMBEDDED_ASCII.get(word, word)
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
    # A backslash before a quote is never valid here -- not an Isabelle symbol, not an
    # ML escape -- and HEAD contains none.  It is what a `'` written as \' inside a
    # DECL_PATCHES raw string leaves behind, which nothing else would catch: the patch
    # text bypasses the rewriting, so `\<bool\'>` is not a generated symbol to look for.
    for m in re.finditer(r"\\'", text):
        bad.append(("stray backslash", text[max(0, m.start() - 40):m.end() + 10]))

    generated = {"\\<%s>" % n for n in set(names.values())}
    for m in NAME_ANTIQUOTATION.finditer(text):
        if any(sym in m.group(1) for sym in generated):
            bad.append(("name antiquotation", m.group(0)))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    names = load_symbol_names()
    letters = load_letters()
    stats = collections.Counter()
    changed, failures, conflicts = [], [], []

    # Always start from the committed text, so the run is repeatable and a fixed
    # rule can simply be re-applied instead of unpicking a previous pass.
    listing = subprocess.run(["git", "ls-files", "*.thy", "*.ML"],
                             cwd=ROOT, capture_output=True, text=True, check=True)
    for rel in sorted(listing.stdout.split()):
        path = ROOT / rel
        text = subprocess.run(["git", "show", "HEAD:" + rel],
                              cwd=ROOT, capture_output=True, text=True, check=True).stdout
        head = text
        for old, new in DECL_PATCHES.get(rel, ()):
            if old not in text:
                failures.append((path, "declaration patch does not apply"))
                text = None
                break
            text = text.replace(old, new)
        if text is None:
            continue
        text = RENAME.sub(lambda m: RENAMES[m.group(1)], text)
        # a patch or a rename is a change too, even with no run left to rewrite
        if text == head and not RUN.search(text):
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
        # This is a shared working tree, and the loop above visits every .thy and .ML
        # in the repository.  Writing whenever the file on disk differs from `new`
        # would revert anyone else's uncommitted edit to a file this migration has
        # nothing to say about, silently.  So write only where the migration itself
        # has something to contribute, and report the rest as a conflict.
        on_disk = path.read_text(encoding="utf-8")
        if new == on_disk:
            continue
        if new == head:
            conflicts.append(path)
            continue
        changed.append((path, 0))
        if not args.dry_run:
            path.write_text(new, encoding="utf-8")

    for k, n in sorted(stats.items(), key=lambda kv: -kv[1]):
        print("  %-24s %6d" % (k, n))
    print("\n%d files %s, %d occurrences seen"
          % (len(changed), "would change" if args.dry_run else "changed", sum(stats.values())))
    if conflicts:
        print("\nleft alone -- edited by someone else, and this migration does not touch them:")
        for p in conflicts:
            print("   %s" % p.relative_to(ROOT))
    if failures:
        print("\nFAILED on %d files:" % len(failures))
        for p, why in failures[:10]:
            print("   %s: %s" % (p.relative_to(ROOT), why))
        sys.exit(1)
    print("round-trip and glue checks passed on every file")


if __name__ == "__main__":
    main()
