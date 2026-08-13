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
    "Phi_Semantics/PhiSem_Int_ArbiPrec.thy": [(
        r'debt_axiomatization \<a>\<i>\<n>\<t> :: TY',
        r'debt_axiomatization sem_aint_T    :: TY ("\<aint>")')],
    "Phi_Semantics/PhiSem_Real_Abst.thy": [(
        r'debt_axiomatization \<a>\<r>\<e>\<a>\<l> :: TY',
        r'debt_axiomatization sem_areal_T   :: TY ("\<areal>")')],
    "Phi_Semantics/PhiSem_Generic_Boolean.thy": [(
        r'debt_axiomatization \<b>\<o>\<o>\<l>          :: TY',
        r'''debt_axiomatization sem_bool_T    :: TY ("\<bool'>")''')],
    "Phi_Semantics/PhiSem_Symbol.thy": [(
        r'debt_axiomatization \<s>\<y>\<m>\<b>\<o>\<l> :: TY',
        r'debt_axiomatization sem_symbol_T    :: TY ("\<symbol>")')],
    "Phi_Semantics/PhiSem_Void.thy": [(
        'debt_axiomatization \\<v>\\<o>\\<i>\\<d> :: TY\n'
        '               and \\<v>\\<o>\\<i>\\<d>V :: VAL',
        'debt_axiomatization sem_void_T :: TY ("\\<void>")\n'
        '               and voidV      :: VAL')],
    "Phi_Semantics_Framework/Phi_Semantics_Framework.thy": [(
        r'debt_axiomatization \<p>\<o>\<i>\<s>\<o>\<n> :: TY',
        r'debt_axiomatization sem_poison_T :: TY ("\<poison>")')],
    "Phi_Semantics/PhiSem_Mem_Pointer.thy": [
        # the notation stays \<ptr>, which the rest of the sources already write
        (r'debt_axiomatization \<p>\<o>\<i>\<n>\<t>\<e>\<r> :: TY ("\<ptr>")'
         '\n'
         r'  where \<p>\<o>\<i>\<n>\<t>\<e>\<r>_isnot_\<p>\<o>\<i>\<s>\<o>\<n>[simp]:'
         r' \<open>\<p>\<o>\<i>\<n>\<t>\<e>\<r> \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>',
         r'debt_axiomatization sem_pointer_T :: TY ("\<ptr>")'
         '\n'
         r'  where pointer_isnot_poison[simp]: \<open>\<ptr> \<noteq> \<poison>\<close>'),
        (r'  \<open> Is_Type_Literal \<p>\<o>\<i>\<n>\<t>\<e>\<r> \<close>',
         r'  \<open> Is_Type_Literal \<ptr> \<close>')],
    "Phi_Semantics/PhSm_V_FMap.thy": [(
        r'debt_axiomatization \<m>\<a>\<p> :: \<open>TY \<Rightarrow> TY \<Rightarrow> TY\<close>'
        r' ("\<m>\<a>\<p> [_,_]")'
        '\n'
        r'                and \<m>\<a>\<p>_rep  :: \<open>(sVAL \<Rightarrow> VAL) \<Rightarrow> VAL\<close>',
        r'debt_axiomatization sem_map_T :: \<open>TY \<Rightarrow> TY \<Rightarrow> TY\<close>'
        r' ("\<map> [_,_]")'
        '\n'
        r'                and map_rep   :: \<open>(sVAL \<Rightarrow> VAL) \<Rightarrow> VAL\<close>')],
    "Phi_Semantics/PhiSem_CF_Routine.thy": [(
        r'\<^const_syntax>\<open>\<v>\<o>\<i>\<d>\<close>',
        r'\<^const_syntax>\<open>sem_void_T\<close>')],
    "Phi_Semantics/library/Ag_Tuple.ML": [(
        r'\<^const_name>\<open>\<p>\<o>\<i>\<s>\<o>\<n>\<close>',
        r'\<^const_name>\<open>sem_poison_T\<close>')],
    "Phi_Semantics/library/Ag_Named_Tuple.ML": [(
        r'\<^const_name>\<open>\<p>\<o>\<i>\<s>\<o>\<n>\<close>',
        r'\<^const_name>\<open>sem_poison_T\<close>')],
    # a syntax constant, eliminated again by the parse_ast_translation just below it;
    # the notation must be primed because \<open> is Isabelle's cartouche delimiter
    "Phi_System/IDE_CP_Applications1.thy": [
        (r'''syntax \<o>\<p>\<e>\<n>  :: \<open>logic\<close> ("\<o>\<p>\<e>\<n>")
       \<o>\<p>\<e>\<n>' :: \<open>nat \<Rightarrow> logic\<close> ("\<o>\<p>\<e>\<n>'(_')")''',
         r'''syntax synt_open  :: \<open>logic\<close> ("\<open'>")
       synt_open' :: \<open>nat \<Rightarrow> logic\<close> ("\<open'>'(_')")'''),
        (r'\<^syntax_const>\<open>\<o>\<p>\<e>\<n>\<close>',
         r'\<^syntax_const>\<open>synt_open\<close>'),
        (r"\<^syntax_const>\<open>\<o>\<p>\<e>\<n>'\<close>",
         r"\<^syntax_const>\<open>synt_open'\<close>")],
    # three things share this spelling: the HOL type that indexes the machine-word
    # length, its bit width, and the term abbreviation for the semantic type at that
    # width.  `sem_int_T` is already taken by the TY constructor, so they are named
    # after the type instead.  Lemmas that speak of integers in general, not of that
    # type -- int_neq_poison, ptr_neq_int' -- keep the bare word and need no patch.
    "Phi_Semantics/PhiSem_Machine_Integer.thy": [
        (r'''       "_int_semty_" :: \<open>type \<Rightarrow> TY\<close> ("\<i>\<n>\<t>'(_')")''',
         r'''       "_int_semty_" :: \<open>type \<Rightarrow> TY\<close> ("\<int'>'(_')")'''),
        (r'''typedecl \<i>\<n>\<t> \<comment>''', r'''typedecl int_t ("\<int'>") \<comment>'''),
        (r'''consts \<i>\<n>\<t>_bits :: "nat"''', r'''consts int_t_bits :: "nat"'''),
        (r'''specification (\<i>\<n>\<t>_bits) \<i>\<n>\<t>_bits_L0: "0 < \<i>\<n>\<t>_bits" by blast''',
         r'''specification (int_t_bits) int_t_bits_L0: "0 < int_t_bits" by blast'''),
        (r'''instantiation \<i>\<n>\<t> :: len begin''', r'''instantiation int_t :: len begin'''),
        (r'''definition "len_of_\<i>\<n>\<t> (_::\<i>\<n>\<t> itself) = \<i>\<n>\<t>_bits"''',
         r'''definition "len_of_int_t (_::int_t itself) = int_t_bits"'''),
        (r'''instance by (standard, simp add: \<i>\<n>\<t>_bits_L0 len_of_\<i>\<n>\<t>_def)''',
         r'''instance by (standard, simp add: int_t_bits_L0 len_of_int_t_def)'''),
        (r'''abbreviation \<open>\<i>\<n>\<t> \<equiv> \<i>\<n>\<t>(\<i>\<n>\<t>)\<close>''',
         '''abbreviation sem_int_t' ("\\<int'>")\n'''
         r'''  where \<open>sem_int_t' \<equiv> \<int'>(int_t)\<close>''')],
    # a logical constant, not syntax: it appears in terms such as
    # `\<simplify>[\<changed> default] X : Y`, so it joins its MODE_ siblings
    "Phi_Logic_Programming_Reasoner/PLPR.thy": [(
        r'       \<c>\<h>\<a>\<n>\<g>\<e>\<d> :: \<open>mode \<Rightarrow> mode\<close>',
        r'       MODE_CHANGED :: \<open>mode \<Rightarrow> mode\<close> ("\<changed>")')],
}

# Plain ASCII renames.  They have nothing to do with the spelling migration; they live
# here because this script always rewrites the working tree from HEAD, so a rename done
# in a separate pass would be undone by the next run.
#
# `semty_ntup` is the one TY constructor not shaped like `sem_tup_T`.  Only the bare
# name moves: `semty_` is this codebase's prefix for the lemmas and auxiliaries around a
# TY, and `semty_tup_eq_poison`, `semty_tup_empty` and `_semty_tup` already sit beside
# `sem_tup_T` in exactly that way, so their `ntup` counterparts are left alone.
RENAMES = {"semty_ntup": "sem_ntup_T"}
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
        m = re.match(r"\\<([A-Za-z][A-Za-z0-9_']*)>.*abbrev:\s*<(\w+)>", line)
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
    changed, failures = [], []

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
