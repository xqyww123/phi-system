# Review brief: forwarding call instead of a second copy (C emitter)

Repository: `/home/qiyuan/Current/MLML/contrib/phi-system` (branch master). The change under
review is uncommitted; its diff is `ai-artifacts/tmp2026-09-08/forwarding_review.diff`.
It has NOT been run in Isabelle yet.

## What the emitter is

The C emitter turns φ-system procedure definitions into C text. Its trust base is
`Phi_System/library/codegen/**`, `Phi_Semantics/codegen/**`, `Phi_StdLib/codegen/**`
(about 362 code lines by cloc); everything else is outside the trust base. The owner's rules:
the trust base must stay minimal; elegance counts as much as correctness (a shape that makes
an invariant impossible to violate beats one that asks people to remember it); no dirty
hacks; consistent terminology, no coined words.

Printing is a state monad `M = ctxt -> V * ctxt`, with
`ctxt = (buffer stack, pf, ftab, ss, vc, frame)`:
- buffer stack: the text being printed, innermost buffer first, each buffer a reversed list
  of string pieces;
- `pf : string option`: the export name, seen only by the first routine hook of an export;
- `ftab : exn Symtab.table`: functions (`"F"^name ↦ FUN call_printer`), typedefs
  (`"T"^key ↦ TY name`) and content keys (`"K"^text ↦ KEY function_name`);
- `ss`: the finished top-level texts (functions, typedefs), most recent first;
- `vc`: the local variable counter (locals are `_v0`, `_v1`, ...);
- `frame`: `Named instance_name | Anonymous`, the instance name the next routine hook takes.

Every C function is named and defined in ONE place: `new_fun` in
`Phi_System/library/codegen/base.ML`. The routine hook `op_rec_routine_` in
`Phi_Semantics/codegen/C/routine.ML` hands `new_fun` a printer `F` which, given a name,
prints the whole function (header, body, closing brace) and returns the printer of a call to
that name. Only the hook knows the header (parameter types `Ta`, return types `Tb`); the
kernel sees only printed text.

## What `new_fun` did before this change

The name is the export name if `pf = SOME e`, else the instance name in the frame, else a
serial `f__N`. Then:
1. A function already defined under that name is only called.
2. Otherwise the body is printed into a fresh buffer and its content key computed
   (`content_key`: the text with the function's own name blanked to `<self>`).
3. Key already present under function `m`, and NOT an export top (`pf = NONE`): the text is
   discarded, `name` registered as another name of `m`.
4. Key already present and an export top (`pf = SOME e`): a second full copy of the function
   was printed under `e` and the alias (the frame's instance name) moved to the new copy.

Case 4 occurs only when one instance is exported under two names, or when an instance was
defined internally (under `f__...`) before its own export is reached. None of the nine
example theories triggers it; `ai-artifacts/tmp2026-09-08/Scratch_Naming_A.thy` does
(`prepend_llist` at `\<int'>` exported as `prepend_a` and `prepend_b`).

## The change

Case 4 now prints, under the export name, a function whose body only forwards to `m`:

```c
T e(T0 _v0, T1 _v1) { return m(_v0, _v1); }
```

(no `return` when the return type is `void`). Decided by the owner: the forwarding body is
a direct `return m(...)`, not a temporary; the hook interface gains a `string option`
argument (`NONE`: print the real body; `SOME m`: print the forwarding body), so `new_fun`
calls the hook a second time on a hit at an export top.

Files changed:
- `Phi_System/library/codegen_nonkernel/base.sig`: `new_fun`'s type.
- `Phi_System/library/codegen/base.ML`: `new_fun`, new branch `(SOME _, SOME (KEY m))` and
  its comment.
- `Phi_Semantics/codegen/C/routine.ML`: `op_rec_routine_` takes `fwd`, factors the parameter
  names into `params`, chooses the body by `fwd`.

Author's claims to be checked:
1. The forwarding branch restarts from `ftab`/`ss` (discarding what the first print
   registered), like the non-top hit branch. Safe because a hit means the body text equals
   `m`'s text; typedef names are serials, so a body that created a new typedef could not
   match; hence the header's types are already memoised and the second hook call creates no
   typedef.
2. The forwarding branch registers neither the alias nor the content key. In both real
   causes of case 4 the instance name is already registered when `m` was printed. Corner
   case: two DIFFERENT instances whose C texts coincide (two φ-types mapping to the same C
   type); the later one's export hits the earlier one's key, its instance name stays
   unregistered, a later internal use prints and discards once more. Correct, one extra
   print; the author chose not to spend a line on it.
3. The forwarding function is a fresh top-level function: variable counter 0, frame
   `Anonymous`, same as the first call.
4. `params` is shared by the header and the forwarding call, so the names cannot diverge.
5. `content_key`'s convention (`base.ML` lines 38-40: no hook may put a piece taken from the
   program before a piece beginning with "(") is respected; the forwarding text is never
   keyed anyway.

Plan document: `ai-artifacts/CODEGEN_INSTANCE_NAMING_PLAN.md` (Section 5.2 `new_fun`,
5.3 why discarding is safe, 5.4 export top, 6 definition order, 10.4 negative tests).
Section 5.4 and 10.4 still describe the old behaviour; updating them is part of the work.
Handoff with more context: `ai-artifacts/CODEGEN_FORWARDING_HANDOFF_2026-09-08.md`.

Other relevant code: `Phi_System/library/codegen/C/base.ML` (`defty'` typedef memoisation,
`var`, `pV`, `call`), `Phi_System/library/codegen_nonkernel/emit.ML` (the emitter, outside
the trust base), `Phi_Semantics/codegen/C/*.ML` (the hooks).
