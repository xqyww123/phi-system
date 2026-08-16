# The source migration: spelled words → single symbols

phi-System used to write its keywords one Isabelle symbol per letter,
`\<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>`.  `migrate_words.py` rewrote the sources to
use one symbol per word, `\<transforms>`, whose glyph draws the whole word.
`WORD_GLYPHS.md` beside this file covers the other half — how the glyphs, the symbol
table and the clipboard are generated, and how to add a word.

**This migration is finished.**  `DECL_PATCHES` and `RENAMES` in the script are empty,
and running it now is a no-op that re-checks the tree against the rules.  What remains
spelled out remains so on purpose; see below.

## The one fact that governs everything

**An Isabelle symbol is not a letter, so it cannot be part of a name.**  Identifiers
admit only ASCII letters, `\<a>`..`\<z>`, `\<A>`..`\<Z>` and the enumerated Greek names.
Confirmed three ways: the documented grammar (`src/Doc/Isar_Ref/Outer_Syntax.thy:112`);
a hardcoded immutable set in `symbol.ML` and `symbol.scala`, which never read
`ISABELLE_SYMBOLS`; and no component in the distribution or the AFP ships a symbols
file that would extend it.  `group:` in a symbols table is cosmetic — it drives
the jEdit palette only.

Everything below follows from that.  A word that merely *appears* in terms can become a
symbol freely.  A word that **names** something — a constant, a type, a syntax constant —
cannot, so the thing is given an ordinary ASCII name and the word is attached to it as
**notation**:

```isabelle
debt_axiomatization sem_aint_T :: TY ("\<aint>")
typedecl int_t ("\<int'>")
```

A symbol name itself admits only `[A-Za-z][A-Za-z0-9_']*` (`symbol.scala:318`) — no
period, no hyphen.  That is why `w.r.t.` is named `\<wrt>` and draws its periods from
the glyph, and why `\<int>`, `\<open>` and five others carry a prime: Isabelle owns the
unprimed name.

## What the script does

For every maximal run of two or more single-letter symbols:

1. word in `SKIP` → leave alone;
2. `\<bbbA>` + `rray` → `\<Array>`, `\<bbbP>` + `tr` → `\<Ptr>` (those are not words but
   the tails of two hand-drawn symbols);
3. after a binder → plain ASCII, it is a bound variable;
4. otherwise widen to the whole **identifier span** — ASCII letters, digits, `_`, `'`,
   letter symbols, a qualifying `G.` prefix, `\<^sub>` scripts.  Span equals the run →
   the symbol.  Span larger → the run is inside a name, so plain ASCII.

It always reads the committed text (`git show HEAD:<file>`) and rewrites the working
tree, so it is a function of HEAD and a fixed rule can simply be re-applied.  Two
self-checks run on every file: expanding every replacement must reproduce the original
byte for byte, and no generated symbol may end up inside something Isabelle lexes as a
name.  Three more guards were each added after a real mistake: a generated symbol inside
a `\<^const_name>`-style antiquotation, a stray `\'` left by Python raw-string escaping,
and a patch whose new text still contains its old text and would re-apply forever.

## What remains spelled out, and why

675 runs across eight words, all deliberate.

| word | occurrences | why |
| --- | --- | --- |
| `TP` | 581 | `consts \<T>\<P> :: action` in `Phi_BI/Phi_BI.thy:824`, with a primed twin and two `\<^const_name>` references.  Left as it is by decision. |
| `arg` `ret` `vs` | 70 | ML builds these names at run time — `Free ("\<a>\<r>\<g>" ^ string_of_int i)` — and 51 `.thy` sites refer to the results literally, so the prefix must stay lexable.  Rendering them plain ASCII was rejected. |
| `mat` `dynarr` `rational` `hash` | 24 | `abbreviation` struct shorthands in `Phi_Examples`.  Left as they are by decision. |

## The renames this migration performed

Eleven words named something and were given an ASCII name plus notation.  Eight are
semantic type constants following the `sem_tup_T` convention that
`PhiSem_Aggregate_Tuple.thy:8` already used:

| was | now | notation |
| --- | --- | --- |
| `\<a>\<i>\<n>\<t>` | `sem_aint_T` | `\<aint>` |
| `\<a>\<r>\<e>\<a>\<l>` | `sem_areal_T` | `\<areal>` |
| `\<b>\<o>\<o>\<l>` | `sem_bool_T` | `\<bool'>` |
| `\<v>\<o>\<i>\<d>` | `sem_void_T` | `\<void>` |
| `\<s>\<y>\<m>\<b>\<o>\<l>` | `sem_symbol_T` | `\<symbol>` |
| `\<p>\<o>\<i>\<s>\<o>\<n>` | `sem_poison_T` | `\<poison>` |
| `\<p>\<o>\<i>\<n>\<t>\<e>\<r>` | `sem_pointer_T` | `\<ptr>`, unchanged |
| `\<m>\<a>\<p>` | `sem_map_T` | `\<map> [_,_]` |

Three needed their own shape:

* **`int`** carried three unrelated things under one spelling, none of them a `:: TY`
  constant, and `sem_int_T` was already the real TY constructor.  They are named after
  the type instead: `typedecl int_t ("\<int'>")`, `int_t_bits`, and the term abbreviation
  `sem_int_t' ("\<int'>")`.  A name that *embeds* it spells it `int_t`, via
  `EMBEDDED_ASCII` — plain `int` would read as `sem_int_T`, a different constant.
* **`open`** is a syntax constant: `synt_open` / `synt_open'`, notation `\<open'>`,
  primed because `\<open>` is Isabelle's cartouche delimiter.  The
  `parse_ast_translation` below it names both through `\<^syntax_const>`.
* **`changed`** is a logical constant appearing in terms, so it joined its `MODE_`
  siblings: `MODE_CHANGED :: \<open>mode \<Rightarrow> mode\<close> ("\<changed>")`.

Four more renames were pure tidying, unrelated to spelling:

| was | now | why |
| --- | --- | --- |
| `semty_ntup` | `sem_ntup_T` | the one TY constructor not shaped like `sem_tup_T`.  Only the bare name moved: `semty_` is this codebase's prefix for the lemmas and auxiliaries around a TY, exactly as `semty_tup_eq_poison` and `_semty_tup` sit beside `sem_tup_T`. |
| `mk_array_T` | `sem_array_T` | same; `mk_` is reserved for derived conveniences such as `mk_int_T = sem_int_T o len_of`, and `sem_mk_array` right beside it makes a *value*. |
| `size_\<t>` | `size_t` + `\<size_t>` | the address-space word width as a type, the pointer-side twin of `int_t`.  Seven declaration sites across three theories; `sem_size_t` is its term-level twin. |
| `\<w>.\<r>.\<t>` | `\<wrt>` | a mixfix delimiter in `Phi_BI/Phi_Fiction.thy:185`; nothing is named by it. |

## Decisions taken — do not re-open

* Names embedded in identifiers become **plain ASCII** (309 occurrences, 87 distinct
  names): `\<t>\<y>\<p>\<e>\<o>\<f>_plus` → `typeof_plus`.  Approved for theorem names,
  **rejected** for `arg1`.
* `\<phi>\<s>\<u>\<b>\<j>` → `\<phi>\<subj>` where it is the infix notation; inside a
  name it goes ASCII.
* Rendering the run-time-generated `arg`/`ret`/`vs` prefixes as plain ASCII was
  **rejected**.
* The unused alternative, kept on the table: the AFP declares fact names containing
  non-letter symbols by **quoting** them (`lemma "\<^bold>V_def":`, ~959 such names in
  AOT).  The 309 ASCII renames could instead have been `lemma "\<typeof>_plus":`.  It
  works for fact names only — not for constants, which would be unwritable in terms
  without notation, and not for Isar-fixed variables, which is a hard error.

## Verification

Verified through isabelle-mcp rather than a batch build.  `Phi_Semantics_Framework`, the
whole `PhiSem_C` chain, `PhSm_V_FMap` and `PhiTest_All` all evaluate with zero errors,
and every remaining warning matches one that was there before.

Two things this leaves open:

* **Seven tracked theories are in no session's import closure**, so no build covers them
  and nothing verifies a change to them: `Phi_Examples/Bucket_Hash.thy`, `Dyn_Arr2.thy`,
  `Dynamic_Array_arbi_len.thy`, `Phi_Semantics/PhSm_V_FMap.thy`, `PhSm_MoV_FM.thy`,
  `PhiSem_Mem_C_AI.thy`, `PhiSem_Symbol_Type.thy`.  `PhSm_V_FMap` was evaluated by hand
  here, which was likely its first full check.
* **Renaming invalidates cached proofs.**  A stored proof's text cites lemma names, so a
  rename makes the replay fail and the obligation is re-proved — sledgehammer if it can,
  the AoA agent otherwise.  `PhiSem_Mem_C_MI` went that way and printed *Proof cache for
  theory ... is outdated!*.  It costs build time, not correctness.

Unrelated but worth knowing when a build feels slow: `by hammer_or_aoa` and
`by auto_sledgehammer` are hardcoded `async_mode = Sync`, because an Isar method must
report success or failure at its own call site and a fork cannot.  A theory full of them
runs them strictly one at a time.

## Doing another round

1. Fill in `DECL_PATCHES` (declaration sites, which need the *name*) and `RENAMES`
   (everything else, matched on identifier boundaries).  Adjust `SKIP` if a word stops
   naming something.
2. `python3 migrate_words.py --dry-run`, then without it.
3. Verify — isabelle-mcp on a theory that imports the changed ones is enough, and far
   faster than a batch build.
4. Commit the sources, then **empty the tables again**.  They are live rewrite rules
   compiled into a repo-wide regex, not a record: a retired entry would go on forbidding
   its old name everywhere, and two entries from different rounds could chain.  An entry
   that no longer applies fails the run loudly, which is the reminder.
5. Record what the round did here and in the commit message.

Before enumerating declaration sites, grep for **every** declaration form —
`abbreviation`, `typedecl`, `type_synonym`, `definition`, `consts`, `instantiation`,
`axiomatization`, `syntax`, `notation`.  A survey that omitted `abbreviation` missed one
site and produced an inner syntax error that only the build caught.
