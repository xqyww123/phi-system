# Handoff: the C emitter after the instance-naming plan (2026-09-08)

Written before a context compaction. The next step, agreed with the user, is a discussion
(not implementation) of replacing the duplicate copy of an exported function by a forwarding
call. Section 2 gives that discussion its complete context; read it before saying anything.

## 1. State

Commits on phi-system `master`:

- `8fe9c371` C emitter: name instances by their parameters and define each function once.
- `d4cbde68` C emitter: `_v` locals, bool-typed arbitrary-precision comparisons, quicksort
  export.

Plan and verification record: `ai-artifacts/CODEGEN_INSTANCE_NAMING_PLAN.md` (rev 5 plus
post-implementation edits; Section 10 holds the results). Scratch theories and review inputs:
`ai-artifacts/tmp2026-09-08/` (README inside; deletable after 2026-09-15).

Not committed on purpose (the user: "不提交 .C .o"): the regenerated `.C` and `.o` files,
including the working-tree changes to the only two generated files the repository tracks,
`Phi_Examples/Binary_Search.C` and `Phi_Examples/Bucket_Hash.C` (tracked since `ac45356c`;
their committed copies still show the pre-plan `v0` locals). The one generated file this work
did commit is `ai-artifacts/tmp2026-09-08/Scratch_Export.C` (in `d4cbde68`). Not mine, left
untouched: `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md`, `Phi_System/*.proof-store`,
`Phi_Semantics/PhiSem_Aggregate_Array.proof-store`.

Generated files as of 2026-09-08 (before the forwarding function; the later figures are in the
head note of `CODEGEN_INSTANCE_NAMING_PLAN.md`), all regenerated from one session after the
`_v` rename, all checked with `gcc -x c -Wall -Wextra -fsyntax-only`: Matrix_Oprs 8 functions,
Binary_Trees 7, Bucket_Hash 11, Dynamic_Array 9, Linked_List 10, Rational_Arith 8, Quicksort 1
(`quicksort`), Binary_Search 1, PhiTest_Arithmetic 3. Three warnings come from the sources (a
value computed and never used in `strassen_mul`, `pop_dynarr`, `length_of`).

Trust base (`Phi_System/library/codegen/**`, `Phi_Semantics/codegen/**`,
`Phi_StdLib/codegen/**`), by `cloc --force-lang=OCaml,ML --force-lang=OCaml,sig`: 365 code
lines at `8fe9c371`, 366 after the `_v` rename (`d4cbde68`); the figure after the forwarding
function is in the head note of `CODEGEN_INSTANCE_NAMING_PLAN.md`.

## 2. The topic to discuss: a forwarding function instead of a second copy

Concluded on 2026-09-08: the first seed of Section 2.3 was chosen and implemented. The hook
takes a `string option`; on a hit at an export top `new_fun` calls it a second time with the
existing name `m` and it prints a function whose body is a direct `return m(_v0, ...)`. The
frame's instance name is registered to `m`. The record of the change and its verification is
the note at the head of `CODEGEN_INSTANCE_NAMING_PLAN.md`. The rest of this section is the
context the discussion started from.

### 2.1 What the emitter does today

Every C function is named and defined at one point: `new_fun` in
`Phi_System/library/codegen/base.ML`. The routine hook
`op_rec_routine_` (`Phi_Semantics/codegen/C/routine.ML`) calls
`new_fun (fn N => ...)`, where the function it passes prints, under the name `N` it is given,
the header, the body and the closing brace, and returns the printer of a call to `N`.

`new_fun` chooses the name: the export name if this is the first routine hook reached by an
export (`pf = SOME e`), else the instance name carried in the frame (`Named m`, put there by
`Phi_CG.frame` around each generic instance), else a serial `f__N`. Then:

1. If a function is already defined under that name, it is not printed again; only the call
   is printed (the `SOME (FUN G)` case).
2. Otherwise the body is printed into a fresh buffer, and its content key is computed
   (`content_key`: the text with the function's own name blanked to `<self>`).
3. If the key is already in the table (`KEY m`: a function `m` with the same text exists)
   and this is *not* an export top (`pf = NONE`), the printed text is discarded and `name`
   is registered as another name of `m`. Nothing is emitted twice.
4. If the key is already in the table and this *is* an export top (`pf = SOME e`), the
   printed text is kept: a second full copy of the function is emitted under the export name,
   and the alias (the instance name, if the frame had one) is moved to the new copy.

Case 4 is the one to discuss. It exists because an export must be a function under its own
name (a linkable symbol), and the kernel has no way to define one except by printing the
hook's text. The comment in `new_fun` records it; the plan (Section 5.4) records the
decision "second full copy, no warning, discuss a forwarding call after the plan".

### 2.2 When case 4 happens

Only when the same instance is already defined under another name before its export is
reached. Two ways:

- The same instance is exported under two names (`\<phi>export a` and `\<phi>export b` of
  one procedure at the same instance parameters). Negative test A in `tmp2026-09-08`
  exercises it: two functions are produced.
- The instance was defined internally first: some caller instantiated it earlier and it was
  printed under its instance name `f__...`, and later its own export is reached. The
  non-kernel `definition_order` (`Phi_System/library/codegen_nonkernel/emit.ML`) prints
  exports in definition order, callee first, so this does not happen in the corpus; the plan
  records one gap (Section 6): a procedure constant that occurs only in an *instance argument*
  of another export (`\<phi>export for P = bar`) is not ordered by it.

The user asked whether mutual recursion is the only cause; the answer recorded in the plan
is that two separately defined procedure constants cannot be mutually recursive (an Isabelle
definition can only mention earlier constants; self-recursion is inside one definition,
handled by `op_rec_routine`), so the two ways above are the only ones.

### 2.3 The proposal and what it needs

The user's suggestion: when case 4 occurs, do not print the body again; emit under the export
name a function that only forwards to the existing one, e.g.

```c
T e(T0 _v0, T1 _v1) { return m(_v0, _v1); }
```

What the kernel has at that moment: the export name `e`, the existing name `m`, the printed
text of the body (already in the buffer, not yet kept), and the call printer `G`. What it
does not have: the header (return type, parameter types) in structured form; those were
printed by the routine hook, which is outside the kernel's knowledge. So the question is
where the forwarding function is printed. Seeds for the discussion (none decided):

- Let the hook do it: `new_fun` passes the hook not only the name `N` but also the name of
  an existing function to forward to (or the kernel calls the hook twice, once to print the
  real body and, on a hit, once in a "forward to `m`" mode). The routine hook knows the
  types `Ta`, `Tb` and can print the forwarding body. Changes the hook interface
  (`(string -> ctxt -> (V -> M) * ctxt)` today) and touches the trust base.
- Derive the header from the printed text: fragile (the kernel would parse C), reject.
- Keep the copy: it is correct, rare in practice, and costs nothing in the trust base. The
  cost is a duplicated body in the rare case.

The user's rule for this area: the trust base must stay minimal, and elegance counts as much
as correctness (a shape that makes an invariant impossible to violate beats one that asks
people to remember it).

## 3. Other open items, in the user's words where they gave them

- Section 10 item 5 of the plan (`FIX_ARITY_VALs_K` scratch test) is not exercised.
- Whether the generated `.C` files replace the hand-written `.c` files in the example
  directories, and how they are named, is undecided.
- The cartouche spellings `div`/`mod` on nat now synthesise the truncating `op_asdiv`/
  `op_asmod` (the old floor rules `op_udiv_anat_φapp`/`op_mod_anat_φapp` lost their
  `φsynthesis`); on int, `div`/`mod` still synthesise the floor rules, which have no C hook.

## 4. Working conventions in force

- Every file change through the Edit tool (Write only for new files); never scripted edits to
  plan documents.
- Isabelle-MCP session `Phi_System_Base`, already launched; one evaluation at a time; poll
  `isabelle_evaluation_status` every 60 s. A C file is written at the theory's `end`
  command, so evaluate to the `end` line (Matrix_Oprs 343, Binary_Trees 664, Bucket_Hash
  315, Dynamic_Array 237, Linked_List 206, Rational_Arith 126, Quicksort 161, Binary_Search
  73, PhiTest_Arithmetic 144). Editing a trust-base `.ML` re-runs the chain from
  `Phi_System` (about 10 minutes). `Phi_Types.thy` lines 2608-2617 fail nondeterministically
  when another session's PLPR work is loaded; a rerun clears it.
- Never `isabelle build`; commit on the current branch only when asked; never commit `.C`
  or `.o`.
