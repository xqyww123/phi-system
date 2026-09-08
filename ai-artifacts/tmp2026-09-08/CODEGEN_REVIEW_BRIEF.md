# Review brief: the C code emitter port and its follow-up rework

Repository: `/home/qiyuan/Current/MLML/contrib/phi-system` (Isabelle/HOL, phi-system).
Everything under review is in the working tree. The diff of the follow-up rework relative
to the safe-point commit `1625e261` is in `ai-artifacts/codegen_review.diff` (970 lines).
The original port of the emitter is commit `f226afae` (52 files) and the kernel-side
preparation is `63fda45e` and `d2d4fde0`; use `git show` on them for context.

## Ground rules for reviewers

- Read-only. Do not modify any file. Do not run `isabelle build`. Do not call any
  `isabelle-mcp` tool (a prover session is in use by someone else).
- Ground every claim in code you actually read. Quote file:line.
- Grade your own findings honestly: a finding that would not change what a careful
  maintainer does is a nitpick and must be labelled as such.

## What the emitter is (essence)

The emitter is a **verbatim transliterator of definition theorems**. Every `proc` command
ends with `Phi_Procedure.define`, which turns the proven program body into a definition
theorem `X_def : X ≡ λ params. body` (via `closure`) plus a specification theorem
`X_\<phi>app`. The emitter (`Phi_System/library/codegen/emit.ML`, function `gen_tm`) walks the
right-hand side of `X_def` symbol by symbol and prints ML text: constant `Thy.c` becomes
`C'G_Thy.c_`, a type becomes `T_T`, lambdas become `fn`. The text is compiled with
`ML_Context.expression` into the theory's ML environment as `structure C'G_<Theory>`. The
identifiers `c_` are **hand-written printing hooks**, one per semantic instruction, kept in
`Phi_Semantics/codegen/C/*.ML` (loaded by `ML_file` at the end of the theory that defines
the instruction). Running the compiled ML executes the hooks in a small printing monad
(`Phi_CG`, `Phi_System/library/codegen/base.ML`; C specifics in `codegen/C/base.ML`) and
writes `<Theory>.C`. Descendant theories inherit the ML structures, so a callee defined
in an ancestor is printed by calling its already-compiled `C'G_Ancestor.f_`.

Trust base = `library/codegen/**` + `Phi_Semantics/codegen/**` (about 300 lines of ML)
+ the registries in `Phi_System/library/system/procedure.ML` (`Procedures` table,
`Interfaces` table, attribute `\<phi>export`). `codegen_nonkernel/**` (the
`\<phi>export_code` config, the `Theory.at_end` trigger, signature files) is not trust base.

## Constraints fixed by the project owner (do not re-litigate; you may propose a relaxation)

1. The demo's design (branch `origin/demo`, commit 78b929f3) is the reference; the port
   must preserve it and its output. Emitted `Linked_List.C` and `Quicksort.C` are byte-identical
   to the demo's emitted files except for the generated serial numbers and the fixed
   `} {` -> `} else {` bug. The duplication of a recursive callee into a private copy
   (`reverse` calling `f6`, a copy of `reverse_aux`) is the demo's own behaviour.
2. The trust base must stay as small as possible.
3. A procedure definition must be parameterized by **semantic types** (`TY`), never by a
   φ-type. A φ-type parameter `T` may occur in the body only as `\<typeof> T` (`SType_Of T`),
   and each such occurrence becomes a `TY` parameter of the definition.
4. Local variables are typed by default (`\<phi>variable_is_typed` defaults to true).
5. Export tags: monomorphic procedures carry `[\<phi>export]` on the `proc` header;
   polymorphic ones get trailing `declare X_def [\<phi>export for <TY instances>]` lines.
6. The theory-end message is `writeln "<lang> program written to <path>"`, no tracing
   of the generated ML.
7. Every emitted theory transliterates all procedures registered in that theory; a
   missing hook must fail loudly at the theory's `end` (unbound ML identifier).

## The changes since the safe point (all mine), with rationale

A. `Phi_System/library/system/procedure.ML`
   - `closure`: after packaging the value argument, collect every `SType_Of (Var T)` with `T`
     a φ-type schematic variable (`Phi_Syntax.dest_phi_type_ty'`), replace each by a fresh
     `TY` variable (named `TY` when the φ-type is called `T`, else `TY_<name>`), reject any
     other occurrence of a φ-type variable with a `TERM` error, and hand the instantiation
     terms (`SType_Of T` for the new variables, the variable itself otherwise) back.
   - `closure`: drop a `TYPE('a)` parameter when `'a` no longer occurs in the generalized
     body (typically the abstract type of the generalized `T`). Demo's definitions had no such
     parameter.
   - `norm_def` now takes the instantiation terms from `closure` (outermost binder first)
     instead of re-creating schematic variables by name.
   - Attribute `\<phi>export`: the instance term is built with `Syntax.check_term` on
     `Const(name, dummyT)` applied to the arguments, so type variables of the constant get
     instantiated by inference (raw `$` failed on `?'a itself`).
B. `simp_monads` stage gets the `\<typeof>` expansion rules so that a compound
   `\<typeof> ⦃k: \<nat>(\<size_t>), v: T⦄` is pushed down to `\<struct>{k: \<int'>(size_t), v: \<typeof> T}`
   before `closure` runs:
   - `Phi_System/library/phi_type_algebra/semantic_type.ML`: the (only live) deriver of
     `SType_Of T = TY` equations also adds each derived rule to `Proc_Monad_SS`
     (`procedure_simps`). (`SType_Of.ML` is dead code: its `ML_file` and registration sit
     inside a comment block in `IDE_CP_App2.thy` lines 65-96.)
   - `typeof_ntup_1` (Named_Tuple) and `semty_Array` (Array) get the `procedure_simps`
     attribute; simprocs `typeof_ntup` and `typeof_tup` are registered into `Proc_Monad_SS`
     via `setup`.
   - The `typeof_ntup` simproc now discharges the side conditions of `Named_Tuple_Types_N`
     (`s |∉| fmdom Tys`, field-name distinctness) itself, using the theory's complete simpset
     (`Proof_Context.init_global (Proof_Context.theory_of ctxt)`), so it also works inside
     the restricted `procedure_simps` simpset. Previously it returned a conditional rewrite
     that only the global simpset could discharge.
C. `Phi_Semantics/library/variable.ML`: `\<phi>variable_is_typed` default `K true`; the per-file
   `declare [[\<phi>variable_is_typed]]` lines were removed (PhiSem_C, PhiTest_Arithmetic, examples).
   Reason: `proc (nodef)` combinators are inlined verbatim, so a library theory with the flag
   off (PhiStd_Loop) silently injected an untyped `op_var_scope None` into `qsort`.
D. Hooks added: `C'G_Product_Type.Unity_` (misc.ML), `C'G_PhSm_Ag_Base.AgIdx_VN_`
   (agg_base.ML; `AgIdx_VN v` is an array index given by a runtime value),
   `C'G_PhiSem_Mem_C_Ag_Ar.op_get_element_pointer_arr_` (new `pointer_arr.ML`),
   `C'G_PhiSem_Mem_C_MI.calloc_` (new `mem_MI.ML`), `C'G_PhiStd_Slice.memcpy_`
   (new `Phi_StdLib/codegen/C/slice.ML`), width code `~2` for the address-space integer
   type (`size_t_T`, `addrspace_bits_` in pointer.ML; `iT ~2 = intptr_t`, `uT ~2 = uintptr_t`
   in int.ML; the demo used `~1` = `int`/`uint`), and `#include <string.h>` in the prelude.
E. `emit.ML`: `tracing src` removed; `codegen_nonkernel/emit.ML`: `writeln` of the output path.
F. Examples: export tags placed per constraint 5; `for` instances are TY terms (`\<int'>`,
   `\<size_t>`); `len_dynarr`/`del_dynarr` are plain exports (their bodies never mention
   `\<typeof> T`); `var ret :: \<typeof> T` in Bucket_Hash (bare `var ret` is rejected under
   typed variables); `is [routine]` added where missing.
G. `PhiSem_Mem_C_AI.thy`: `calloc_aN`/`calloc_aN2` had a stale `have t1 … the_\<phi>(8)` proof
   (premise index shifted); replaced by the same fix its sibling `calloc` in Mem_C_MI received
   on 2026-08-14 (`…; auto_sledgehammer`).

## Status of verification

- Clean and emitted, compiled with `gcc -x c -Wall -Wextra` (note: gcc treats the `.C` suffix
  as C++ unless `-x c`): PhiTest_Arithmetic.C, Rational_Arith.C, Linked_List.C, Quicksort.C,
  Binary_Search.C, Dynamic_Array.C (the last two after switching to intptr_t; re-check
  pending).
- Bucket_Hash is being re-evaluated now; Binary_Trees and Matrix_Oprs not yet run.
- `ai-artifacts/Scratch_Export.thy` is a throwaway probe theory, to be deleted.

## Known open points (you may take positions on them)

- `Phi_Semantics/PhiCG_C.thy` + `codegen/C.ML` are an empty placeholder inherited from the demo.
- `uint` (printed for unsigned casts, demo's choice) is not a standard C type; it exists on
  glibc via `<sys/types.h>`.
- The width-code scheme in int.ML (`~1` = int, `~2` = address width) is an ad-hoc integer encoding.
- Each application of a polymorphic hook re-creates the callee (`f14`, `f18` copies of `Max`
  in Dynamic_Array.C); inherited from the demo's `fun_name ()` design.
- Unused-binder ML warnings (`b8` …) are emitted for every `bind_` continuation.
- `C'G_PhiSem_Mem_C_MI` has only `calloc_`; `op_shift_pointer`, `abst_shift_pointer` have no hook yet.
- Type of `Named_Tuple` fields is printed in `fmupd` insertion order (`{int data; void* nxt;}`).
