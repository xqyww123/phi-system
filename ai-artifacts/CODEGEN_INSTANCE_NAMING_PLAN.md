# Plan: one C function per procedure instance

> **Sealed on 2026-09-09.** Everything below this note is the plan as reviewed and approved
> (revision 5) together with its verification record, kept as the record of what was
> approved; it is not maintained. Where the text below and the code disagree, the code is
> authoritative: `Phi_System/library/codegen/base.ML`, `Phi_Semantics/codegen/C/routine.ML`,
> `Phi_System/library/codegen_nonkernel/emit.ML`. The plan was implemented in three commits
> on `master`; the departures from the text below are:
>
> - `8fe9c371`: the plan as written (instance names, `new_fun`, content keys, the checks in
>   `interf`, definition order), plus the truncating `op_asdiv`/`op_asmod` hooks and the
>   `PhiTest_Arithmetic` changes of Section 10.
> - `d4cbde68`: local variables are spelled `_v0`, `_v1`, ... and `interf` refuses export
>   names of that shape (that commit rewrote Sections 4.1, 5.5 and 10 to match, so they are
>   current); comparisons of arbitrary-precision integers are `bool`; `Quicksort.thy` exports
>   `quicksort` (Section 10 still records the `qsort` collision as unresolved).
> - The commit that adds this note: the follow-up of Section 5.4
>   is done. At an export top whose body already exists under a name m, `new_fun` no longer
>   prints a second copy: it calls the routine hook a second time with m, and the hook prints
>   under the export name a function whose body only forwards to m (`return m(_v0, ...)`;
>   no `return` when the return type is `void`); the frame's instance name is registered to
>   m. The hook interface gained a `string option` argument (`base.sig`). Sections 5.2,
>   5.3 (the `pf` bullet), 5.4, 6, 8, 9 and 10 describe the behaviour before this change.
>   The permanent test is `Phi_Test/PhiTest_Arithmetic.thy`, where `GCD` is exported also
>   as `gcd`; the generated `PhiTest_Arithmetic.C` is committed beside it as the expected
>   output (the owner's exception to "never commit `.C`"), and contains
>
>   ```c
>   int gcd(int _v0, int _v1) {
>   return GCD(_v0, _v1);
>   }
>   ```
>
>   Verification (2026-09-09, one prover session after the change): the eight example files
>   regenerated with the same function counts (Binary_Search 1, Binary_Trees 7, Bucket_Hash
>   11, Dynamic_Array 9, Linked_List 10, Matrix_Oprs 8, Quicksort 1, Rational_Arith 8) and
>   identical text up to the typedef serial numbers; `PhiTest_Arithmetic.C` has 4 functions;
>   every file passes `gcc -x c -Wall -Wextra -fsyntax-only` with the same three
>   source-level unused-value warnings as before. The trust base is 375 code lines by
>   cloc (366 before).

Status: revision 5, after the review of revision 4 (judge: ready after the listed fixes,
no further review round) and the decisions taken with the project owner. Nothing
implemented. Baseline commit: `ac45356c`.

Follow-up recorded for after this plan: discuss printing a forwarding call instead of a
second copy when an export top finds its instance already defined (Section 5.4).

## Glossary (authoritative for this document)

- **emitter**: `Phi_System/library/codegen/emit.ML`; transliterates definition theorems to ML text.
- **printing monad**: `M = ctxt -> V * ctxt` (`library/codegen/base.ML`); running an `M` prints C text into `ctxt`.
- **routine hook**: `C'G_PhiSem_CF_Routine.op_rec_routine_` (`Phi_Semantics/codegen/C/routine.ML:5`); the only place a C function is printed, and the only caller of `new_fun`.
- **instance parameters**: the parameters of a procedure definition fixed when the procedure is instantiated: `TYPE` parameters, `TY` parameters, values fixed by a `context` (e.g. `N` of `add_mat`). They are the λ-binders of the definition other than the run-time argument.
- **run-time argument**: the single `\<phi>arg` binder that `closure` packages the run-time values into (`procedure.ML:105`); dropped when it is `unit \<phi>arg` and the body is closed (`procedure.ML:94-96`). A routine definition has no such binder: its body is the routine hook applied to the body printer and is itself of type `proc'`.
- **binder record**: what `closure` knows about a definition's binders and `gen_define` now records per constant beside the parameter names: whether the run-time argument binder survived (Section 4.6). That one bit is all the emitter needs; every other leading binder is an instance parameter.
- **instance**: a procedure constant applied to instance parameters, e.g. `add_mat 4 4`.
- **instance name**: the C function name derived from an instance, e.g. `f__12Matrix__Oprs8add__mat1A41A4` (Section 4.2).
- **content key**: the text of a printed C function with its own name replaced by a placeholder (Section 5.2).
- **frame**: a new component of `ctxt` holding the instance name the next routine hook should take, `Named of string | Anonymous` (Section 4.5).
- **export top**: the moment `Phi_CG.interf` applies an exported instance; recognised by `pf = SOME name` in `ctxt`.
- **generated name**: any identifier the emitter invents: instance names, anonymous function names, typedef names, local variable names (Section 4.1).

## 1. The defect

The emitted ML of a definition puts every λ of the definition, the instance parameters and
the run-time argument alike, outside the routine hook: `gen_tm'` prints an `Abs` as
`(fn b => ...)` (`emit.ML:43-44`) and the hook application `op_rec_routine_ ...` sits inside.
So every application of the procedure, at every call site, evaluates
`fun_name () (new_fun (fn N => ...))` (`routine.ML:5`) anew. `fun_name ()` (`base.ML:20-24`)
allocates a fresh `id : string option ref`, the first application names the function by
`serial "f"` when `pf` is empty, and `new_fun` (`base.ML:28-31`) memoises by that name.
Fresh `id`, fresh name, fresh copy of the body, per call site, whether or not the procedure
has instance parameters.

Evidence: function counts of the checked-in files, and the number of body classes under the
canonicalisation of Section 10.2 (own name replaced by a placeholder, called generated names
expanded to their class's body to a fixpoint, typedef names expanded to their definitions):
`Matrix_Oprs.C` 81 functions, 8 classes; `Binary_Trees.C` 78, 7; `Dynamic_Array.C` 14, 9;
`Linked_List.C` 12, 10; `Bucket_Hash.C` 21, 11; `Rational_Arith.C` 10, 8;
`PhiTest_Arithmetic.C` 3, 3; `Quicksort.C` 1, 1; `Binary_Search.C` 1, 1. The class count
equals the theory's export count in every case. In `Matrix_Oprs.C` the 34 calls of
`copy_mat`, `add_mat`, `sub_mat` in `strassen` (`Matrix_Oprs.thy:211-270`) each produce a
copy, and `strassen_mul` reprints the whole of `strassen` together with all 34 inner copies,
so the blow-up multiplies along the call depth. `del_mat`, which has no instance
parameters, is printed three times.

Only a definition with no λ at all, a `proc`-typed one with no instance parameters and a
trimmed `unit` argument (`init` of Linked_List), is emitted as a bare `val`, evaluated once,
and never duplicated. Those carry the second, latent defect: their single `id` is set by
whichever application comes first; if a caller's export is processed before the callee's
export, the callee's `id` is `SOME "fN"` at its own export top, `fun_name` takes the first
branch (`SOME id'`), and no function with the export name is printed at all. It has not
fired only because `init` is not called internally.

## 2. Requirements

1. Two instances share a C function only if their printed bodies are identical. No scheme may
   merge distinct instances (that would be wrong code); failing to merge equal ones is only a
   loss of sharing.
2. An exported instance is always printed under its export name.
3. Names of shared instances are stable and readable when the instance parameters have a
   text.
4. Instances whose parameters have no text (procedure-valued parameters such as `CMP` of
   Binary_Trees) are still shared when their bodies are identical.
5. The emitter stays a name-by-name transliterator; the type-directed decisions it makes are
   exactly: naming a parameter's `_K` hook from the head type constructor of its type
   (Section 4.3), the two sort tests for `TYPE` parameters (Section 4.3), and distinguishing
   a bare type variable (no head constructor) from a type.
6. Trust-base change list (Section 9): `library/codegen/base.ML`, `library/codegen/C/base.ML`,
   the `_K` hooks in `library/codegen/C/misc.ML` and `library/codegen/C/Phi_Semantics_Framework.ML`,
   the two signatures, `emit.ML` (`binder`, `gen_proc`, `gen_extractor`, `codegen`), and one
   token of `routine.ML`. Outside the trust base: one recorded field in `procedure.ML`
   (Section 4.6) and the export order in `codegen_nonkernel/emit.ML`. Untouched:
   `IDE_CP_Core.thy`, `tr_str`, every other hook.

## 3. Overview

Two mechanisms, both consumed at the single point where a function is named and defined
(`new_fun`):

- **Instance names** (Section 4): the emitter wraps each definition so that, at run time,
  the instance name is computed from the instance parameters and placed in the frame;
  `new_fun` takes it and finds an already defined function by that name.
- **Content keys** (Section 5): whenever `new_fun` prints a function, whatever its name came
  from, it computes the content key; if a function with the same key exists, the freshly
  printed one is discarded and the existing one is called. Requirement 1 rests on the
  injectivity obligation of Section 4.3 only on the name-hit path, where no body is printed
  and so no key can be compared.

Plus, outside the trust base, exports are emitted in definition order (Section 6).

## 4. Instance names

### 4.1 Generated names and export names

| kind | today | plan | scope |
| --- | --- | --- | --- |
| instance name | (none) | `f__` + mangled instance | file |
| anonymous function | `f42` | `f__42` | file |
| typedef | `T15` | `T__15` | file |
| local variable | `v0` | `_v0` | block |

Every generated file-scope name begins with a letter followed by `__`; block-scope names are
`_v` followed by digits (an underscore followed by a lower-case letter is reserved only at
file scope, so a local may carry it) and are spelled in two places, `assign_var`
(`base.ML:27`) and the routine header (`routine.ML:8`). `interf` refuses an export name
matching `^.__` or `^_v[0-9]+$` (Section 5.5). With that check a generated name and an export
name can never coincide in the emitted C, and `new_fun`'s lookup by name cannot hand back a
user function in place of a generated one.

Decision recorded: generated file-scope names do not begin with `_` (C11 7.1.3 reserves such
names for the implementation at file scope); `f__`/`T__` are legal C identifiers (C reserves
only names *beginning* with `__`; C++ reserves any name containing `__`, which is why the
files are compiled with `gcc -x c`).

### 4.2 Mangled instance

`f__` + for each dot-separated segment of the constant's full name: the length of its
spelling + the spelling + for each instance parameter: the length of its spelling + `A` + the
spelling. Spelling is by `spell` (Section 4.2.1). Example: `Matrix_Oprs.add_mat` at
`N⇩x = 4, N⇩y = 4` is `f__12Matrix__Oprs8add__mat1A41A4` (`Matrix__Oprs` has 12 characters,
`add__mat` 8).

The name parses uniquely: a length is the maximal digit run, a segment follows immediately
(a spelled segment begins with a letter), a parameter text follows the letter `A` (its
spelling may begin with a digit, which is what the `A` is for). Two instances of one constant
differ in some parameter text, and two constants differ in some segment, so requirement 1
holds by the injectivity of `spell`.

Readability caveat: `key_strs` yields the C spelling of a type, which for an array or
aggregate is a typedef name (`T__15`); such instance names are deterministic but not
readable.

#### 4.2.1 `spell`

`spell`, in `Phi_CG` beside `mangle`, is the injective spelling of a name segment or a
parameter text as a C identifier fragment. It is distinct from `tr_str` (`emit.ML:5-6`):
`tr_str` spells the ML identifiers of hand-written hooks (`emit.ML:10, 20, 23`) and the C
field names of named tuples at their access site (`C/base.ML:31`, paired with the raw
declaration at `agg_ntup.ML:3`), both of which pin its identity behaviour on ASCII
identifiers; `tr_str` is not touched.

```
fun spell_char #"_" = "__"
  | spell_char c = if Char.isAlphaNum c then str c
                   else let val n = Char.ord c
                         in String.implode [Char.chr (Char.ord #"a" + n div 16), Char.chr (Char.ord #"a" + n mod 16), #"_"] end
val spell = String.translate spell_char
```

An underscore doubles; any other character outside letters and digits (the dot included:
`mangle` splits on it first) becomes two letters `a`..`p` (its byte in hexadecimal) followed
by one underscore. A spelled text never begins with `_`. Unique decodability: in a maximal
run of `k` underscores, an even `k` is `k/2` literal underscores and an odd `k` is the
terminator of the two-letter escape immediately before it followed by `(k-1)/2` literal
underscores. Examples: `add_mat` → `add__mat`, `foo'` → `fooch_`, `\<phi>V_pair` →
`fm_dm_phido_V__pair`, `void*` → `voidck_`, `~2` → `ho_2`. (`Char.isAlphaNum` in Poly/ML is
the ASCII test; Isabelle names and C type spellings are ASCII.)

### 4.3 Parameter text printers (`_K` hooks)

For a parameter whose type has head constructor `t`, the emitter writes the `_K` hook of `t`
applied to the parameter's ML variable, named by the same rule `gen_typ` uses for `_T`
(`emit.ML:22-25`): a qualified constructor becomes a structure member, an unqualified one a
top-level value. Decision recorded: the hook is named from the head constructor alone, its
type arguments ignored; a parameter whose type is a bare type variable (no constructor) gets
the constant `Phi_CG.pair NONE` instead. A missing `_K` hook fails at ML compilation of the
generated structure, like any missing hook; the three the corpus needs are `nat_K`, `TY_K`
and `C'G_fun_K` (`CMP`/`Eq` of Binary_Trees have head constructor `fun`). The library's own
`if` (`PhiSem_CF_Basic.thy:125`, emitted at `:330`) has a `TY list` parameter, and the
common HOL constructors `list`, `option` and `prod` get hooks answering `NONE` ("no text
yet"), so an instance over them is anonymous rather than a build failure.

```
(* library/codegen/base.ML, structure Phi_CG *)
type keyp = ctxt -> string option * ctxt          (* NONE: this value has no text *)
val key_int  : int  -> keyp = pair o SOME o string_of_int
val key_bool : bool -> keyp = pair o SOME o Bool.toString
fun key_strs (P : ctxt -> string list * ctxt) : keyp = P #-> (pair o SOME o String.concat)

(* library/codegen/C/misc.ML *)
structure C'G_Nat = struct ... val nat_K  = Phi_CG.key_int  end
structure C'G_HOL = struct ... val bool_K = Phi_CG.key_bool end
structure C'G_Type_Length = struct structure len0_class = ... val len_K = Phi_CG.key_int end   (* the existing structure, misc.ML:30; a width code, int.ML:9-11 *)
val C'G_fun_K = fn _ => pair NONE                 (* a function value has no text (Section 8) *)

(* library/codegen/C/Phi_Semantics_Framework.ML, structure C'G_Phi_Semantics_Framework *)
val TY_K = Phi_CG.key_strs                        (* TY is declared in Phi_Semantics_Framework.thy:29 *)
val FIX_ARITY_VALs_K : ty -> keyp = ...           (* Section 4.3.1 *)
```

`key_strs` is language-neutral (it needs only the shape `ctxt -> string list * ctxt`), so it
lives in `Phi_CG` and `TY_K` can refer to it although `C/Phi_Semantics_Framework.ML` is loaded
before `C/base.ML` (`IDE_CP_Core.thy:2198, 2203`). `len_K` goes into the `C'G_Type_Length`
that already exists in `misc.ML:30`; a second `structure C'G_Type_Length` in a later file
would shadow the whole structure and lose `len0_class.len_of_`.

**`TYPE` parameters.** The ML value of a `TYPE` binder depends on the instantiating type: a
`len`-sorted type variable is instantiated by width codes (`int_t_T = ~1`, `size_t_T = ~2`,
`bit0_T (...)`: `int`), a `FIX_ARITY_VALs`-sorted one by value-shape printers (`VAL_T`,
`unit_T`, `prod_T`: `ty`). Decision recorded: exactly these two sorts are supported, tested
by subsumption in this order, with `thy = Context.theory_of ctxt` for the context `gen_proc`
receives (`Thm.theory_of_thm` is not usable: `PhiSem_CF_Basic.thy:330` runs the emitter from
a `setup` while its theory is still under construction, and the theorem's certificate has no
content yet):

```
Sign.subsort thy (S, ["Type_Length.len"])                       -> C'G_Type_Length.len_K
then Sign.subsort thy (S, ["Phi_Semantics_Framework.FIX_ARITY_VALs"]) -> C'G_Phi_Semantics_Framework.FIX_ARITY_VALs_K
otherwise                                                       -> Phi_CG.pair NONE
```

`Sign.subsort` on a class the theory does not declare returns `false` (`sorts.ML:149-156`
via `Graph.is_edge`, `graph.ML:217-220`, which answers `false` for an absent node), which is
the wanted answer, so no existence guard is needed. The two class names are the special case
itself and are written in `gen_proc` (`FIX_ARITY_VALs` as the checked antiquotation
`@{class FIX_ARITY_VALs}`, `len` as a string since `Type_Length` is not an ancestor of
`IDE_CP_Core`); the hook names follow from them by `gen_typ`'s rule.

**Injectivity obligation (trust-base rule).** A `_K` hook must be injective on everything its
parameter's ML value can make the printed body depend on, and a type printer must have no
output effect beyond the text it returns (which `defty'`'s memoisation by text already
presupposes). Two disciplines: a *type* printer (`key_strs`) runs in the live context on
purpose, so that `defty'`'s memoisation makes a typedef name, hence the instance name, stable
across call sites, at the price of a possibly unreferenced file-scope typedef that
`gcc -Wall -Wextra` does not report; a *value-shape* printer (Section 4.3.1) allocates
variables (`VAL_T = assign_var #> apfst V`, `C/Phi_Semantics_Framework.ML:6`), so it runs in a
scratch context that is discarded.

#### 4.3.1 `FIX_ARITY_VALs_K`

A value-shape printer affects a printed function only through the `V` it produces (one
variable per `VAL`, none for `unit`, a pair for a product). The key is that shape: run the
printer in a scratch context (`([[]], NONE, ftab, ss, 0, Anonymous)`), check that its buffer
came back empty, discard the context, and serialise the `V` (`V _` → `V`, `V0` → `0`,
`V2 (a,b)` → `(a,b)`). No exported theory in the corpus has a `TYPE` parameter; Section 10
adds a scratch test for it.

### 4.4 Assembling the name

```
(* library/codegen/base.ML *)
fun mangle name (keys : keyp list) : ctxt -> string option * ctxt = fn c =>
  let val (texts, c') = fold_map I keys c
      fun seg s = string_of_int (size s) ^ s
   in if exists is_none texts then (NONE, c')
      else (SOME ("f__" ^ String.concat (map (seg o spell) (space_explode "." name))
                        ^ String.concat (map (fn t => let val s = spell (the t) in string_of_int (size s) ^ "A" ^ s end) texts)), c')
  end
```

### 4.5 The frame

`ctxt` gets a sixth component `frame`, `datatype frame = Named of string | Anonymous`,
declared in `base.sig` beside `type ctxt`. Every pattern on the tuple in `base.ML` and in
`defty'` (`C/base.ML:6-8`) gains the component; `codegen'` (the one in `base.ML`) starts with
`Anonymous`; `interf` requires and re-establishes `Anonymous`, exactly as it already requires
and re-establishes an empty buffer stack and a zero variable counter (`base.ML:33-34`).

```
fun frame (nameP : ctxt -> string option * ctxt) (F : M) : M = fn c =>
  let val (name, c1) = nameP c
      val saved = get_frame c1
      val (v, c2) = F (set_frame (case name of SOME n => Named n | NONE => Anonymous) c1)
   in (v, set_frame saved c2) end
fun frame' nameP (F : V -> M) = fn v => frame nameP (F v)
```

A single slot saved and restored by the one combinator that sets it: an unbalanced state is
impossible. `new_fun` always leaves the frame `Anonymous` before printing, so a frame names
at most one function. The invariant the design rests on: **the C function printed by the
first routine hook reached inside a wrapped body is determined by the definition and its
instance-parameter texts alone**; the run-time argument reaches only `call` (`routine.ML:3`),
never the printed body, and the body's variable names start from `vc = 0`. For a routine
definition that routine is its own (the hook is the head of the body). For an inline
definition (a definition that is not a routine) the frame is consumed by the first routine
reached in its body that was not itself wrapped, if any (a procedure defined with an empty
binding is not a constant, `procedure.ML:197`, and is inlined); under the invariant this is
still the same function for equal instance texts, so sharing by that name is sound, though
the name then belongs to the inline definition rather than to the routine.

### 4.6 The wrapper written by the emitter

`gen_proc` translates `c x₁ … xₙ ≡ λy₁ … yₘ. body`, where the `xᵢ` are the context
parameters (`Var`s or `Free`s on the left of the exported definition; `gen_proc` sees the
theorem after `Morphism.thm` has exported it, `procedure.ML:214-219`) and the `yⱼ` are the
leading binders of the body, `TYPE` parameters first, then `TY` and value parameters, then
the run-time argument if it survived (`procedure.ML:105, 155-158`).

Decision recorded: `gen_proc` does not infer this split from types; it reads the binder
record. `closure` returns `(length ty_params, …, instance)` with `instance = [_]` when the
run-time argument binder survived and `[]` when `trim` dropped it (`procedure.ML:94-96, 105,
158`); `gen_define` already stores the parameter names per constant in the same declaration
(`add_param_names`, `procedure.ML:216-220`), where `TYPE` parameters and the run-time
argument are both stored as `""` and cannot be told apart. The registry gains, per constant,
whether the run-time argument survived (`Phi_Procedure.has_runtime_arg`), which `gen_proc`
reads through the `Context.generic` that `codegen`/`gen_extractor` already receive as their
last argument from `codegen_nonkernel/emit.ML:8`. With `t + p` leading binders and `has_arg`:

```
val c_ = (fn x₁ => … (fn yₜ₊ₚ => Phi_CG.frame' (Phi_CG.mangle "Thy.c" [K₁ (x₁), …, Kₜ₊ₚ (yₜ₊ₚ)]) (<rest>)) …)
```

where `<rest>` is `fn yₜ₊ₚ₊₁ => <body>` when `has_arg` (an inline definition with a λ
argument), and `<body>` otherwise; the wrapper is `frame'` when `<rest>` has type `V -> M`
(`has_arg`, or a routine body, which is `proc'`-typed) and `frame` when it is an `M`. The
body's type is the only thing left to test: `dest_procT_params (fastype_of1 (rev binderTs, body))`
gives `[_]` for `V -> M` and `[]` for `M`; any other shape, or a constant absent from the
registry, gets no wrapper. The `xᵢ` are `Var`s or `Free`s and are always instance
parameters. A `\<phi>arg`-typed instance parameter is not a special case: its head
constructor names the hook `C'G_Phi_Semantics_Framework.phi_arg_K`, which does not exist, so
the generated structure fails to compile, loudly.

The ML variable of each parameter is printed by the one function that `gen_tm` also uses:
`gen_tm'`'s two `Abs` clauses and `gen_proc`'s `param` (`emit.ML:41-44, 50-51`) are
replaced by a shared `binder`, which reproduces the *itself*-`Abs` case (the binder is named
from the type while `bi` still advances) so that the wrapper and the body cannot disagree on
a name; after stripping `m` binders the body is printed with `gen_tm (m-1)`.

Definitions without instance parameters are wrapped too (`mangle "Thy.del_mat" []`), so the
`del_mat` copies of Section 1 collapse. Definitions with an unnameable parameter set
`Anonymous`.

## 5. Naming and defining a function

### 5.1 One entry point

`fun_name` and its `id` reference are deleted; the name decision moves into `new_fun`, and
`routine.ML:5` becomes `new_fun (fn N => ...)` (one token). Why no state is needed: recursion
goes through `call` (`routine.ML:9-10`), never through naming; a closure applied more than
once is either a bare-`val` definition, which has no instance parameters and therefore always
sets the same `Named` frame, or an unnameable one, which is resolved by its content key at
every application. Deleting the reference removes the state behind the latent defect of
Section 1 instead of re-ordering its branches.

### 5.2 `new_fun`

`ftab` (`exn Symtab.table`) holds three kinds of entries under three key prefixes, so they
cannot collide: `fun_entry name = "F" ^ name ↦ FUN G` (call printer),
`typedef_entry ctext = "T" ^ ctext ↦ TY t` (in `defty'`), `key_entry content = "K" ^ content ↦ KEY name`.
`the_fun ftab m` is the `FUN` entry of `m`.

```
fun new_fun F v (c as (outs,pf,ftab,ss,vc,fr)) =
  let (*the name; at an export top the instance name in the frame becomes the alias*)
      val (name, alias) =
        case (pf, fr)
          of (SOME e, Named m) => (e, SOME m)
           | (SOME e, _)       => (e, NONE)
           | (NONE, Named n)   => (n, NONE)
           | (NONE, Anonymous) => (serial "f__", NONE)
   in case Symtab.lookup ftab (fun_entry name)
        of SOME (FUN G) => G v (outs, NONE, ftab, ss, vc, Anonymous)
         | _ =>
      let val (G, (out::outs', _, ftab', ss', _, _)) = F name ([]::outs, NONE, ftab, ss, 0, Anonymous)
          val text = rev out
          val key  = key_entry (content_key name text)
       in case (pf, Symtab.lookup ftab key)                         (* the table before this printing *)
            of (NONE, SOME (KEY m)) =>                              (* same body already defined: discard *)
                 let val G' = the_fun ftab m
                  in G' v (outs, NONE, Symtab.update (fun_entry name, FUN G') ftab, ss, vc, Anonymous) end
             | _ =>
                 (*at an export top a second copy is printed even if the body exists: an
                   export must be a function under its own name; see Section 5.4 for when
                   this happens*)
                 let val ftab'' = ftab' |> Symtab.update (fun_entry name, FUN G)
                                       |> Symtab.default (key, KEY name)
                                       |> (case alias of SOME m => Symtab.update (fun_entry m, FUN G) | NONE => I)
                  in G v (outs', NONE, ftab'', text :: ss', vc, Anonymous) end
      end
  end
```

Notes:

- The frame is `Anonymous` on every path before anything is printed and in every returned
  context.
- The content-key lookup and the resolution of `m` both use `ftab`, the table *before* this
  printing: every `m` the hit branch can name existed before the body was printed, which
  turns the argument of Section 5.3 into a structural invariant. A legitimate partner's
  `KEY` and `F` entries were registered together, strictly earlier.
- On a hit the winner is registered under the loser's name, so a named instance that loses
  to a content key is not re-printed at its next call site.
- `pf` is cleared on every path before anything is printed, so `pf` is visible only to the
  outermost routine of an export.
- `content_key name text` replaces a piece `s` of `text` by `<self>` when `s = name` and the
  next piece begins with `(`. Trust-base rule (follower side): *no hook may emit a piece whose
  text is taken from the program — a value name, an aggregate field name, a semantic literal
  via `C'G_PhiSem_Formalization_Tools.semantic_literal_` — immediately before a piece
  beginning with `(`; the only pieces followed by a `(`-initial piece are fixed hook text
  (`var`'s `" = "`, `C/base.ML:14`), `call`'s function name (`routine.ML:3`) and the routine
  header's `N` (`routine.ML:10`).* Corpus check: every `(`-initial first piece of a hook sits
  inside `var` (`int.ML:17`, `pointer.ML:8`, `pointer_arith_MI.ML`), every other
  `(`-bearing piece starts with a non-`(` character (`mem.ML:4-5`, `CF.ML:10,15`,
  `break.ML:5`, `agg_ntup.ML:5`, `slice.ML:3`), and a program-derived piece is followed by
  `"["`, `"."`, `";\n"`, `"="`, `" = "`, `","` or `");\n"`. `puts` prepends reversed pieces
  (`base.ML:17`), so `rev out` is in print order.

### 5.3 Why discarding on a hit is safe

On a hit the body just printed equals the body of `m`, which existed before the printing
(Section 5.2), and nothing the printing could have created is lost by returning to `c`:

- typedefs: `defty'` memoises by C text and the typedef's name appears in the body; a new
  typedef would have changed the text and prevented the hit;
- nested functions: `new_fun` prints the call right after the definition (`base.ML:31`), so
  a nested miss changes the outer text; on an outer hit every nested lookup was a hit;
- variable names: the body runs from `vc = 0` and the caller's counter is restored, so they
  depend on the body alone;
- serial numbers: only gaps;
- `pf`: the hit branch requires `pf = NONE`;
- the frame: saved and restored by `frame`, `Anonymous` throughout `new_fun`.

### 5.4 Export top

For a routine export, `pf = SOME e` and the frame still holds the instance name `m` when
`new_fun` runs (the export's own routine is the first hook reached). `new_fun` takes `m` as
the alias, never discards, registers the content key only if absent (`Symtab.default`), and
registers `fun_entry m ↦ FUN G`, so that later internal uses of the same instance find the
exported function by their instance name and print calls to `e`. For an inline export the
first routine reached inside its body takes `pf` and its own instance name is the alias;
sound (the alias names a function whose body was just printed) but the inline export's own
instance is not aliased. Every export in the corpus is a routine.

Decisions recorded: when an instance is exported under two names, or when an instance is
defined internally before its own export is reached (Section 6 makes this rare), the export
prints a second full copy and the alias moves to it; no warning; the comment in `new_fun`
records it. After this plan: discuss printing a forwarding call instead of the copy.

### 5.5 `interf`

```
fun interf name F ([],NONE,ftab,ss,0,Anonymous) =
  let val _ = is_generated_name name andalso
                error ("The export name " ^ quote name ^ " has the shape of a generated name ...")
      val (_,(_,_,ftab',ss',_,_)) = F V0 ([[]],SOME name,ftab,ss,0,Anonymous)
      val _ = Symtab.defined ftab' (fun_entry name) orelse
                error ("The export " ^ quote name ^ " produced no function: its body reaches no routine")
   in ([],NONE,ftab',ss',0,Anonymous) end
```

`is_generated_name` matches `^.__` or `^_v[0-9]+$`. Both checks are load-bearing: an export
named like a generated name would be found by `new_fun`'s name lookup in place of the
function it stands for; an export whose body reaches no routine hook would silently produce
no function under its name (requirement 2).

## 6. Exports are emitted in definition order (outside the trust base)

`gen_extractor` takes `intrfs` as an ordered list (`Symtab.fold` → `fold`,
`Symtab.is_empty` → `null`). The non-kernel `codegen'` (`codegen_nonkernel/emit.ML`) orders
the exports by the definition order of their head constants over the theory and its
ancestors:

```
val defs = maps (fn thy' => rev (Phi_Procedure.procedures_of (Context.Theory thy'))) (rev (Theory.nodes_of thy))
```

(`procedures_of` answers for the theory of the context it is given, `procedure.ML:52-55`;
`add_procedure` conses, so `rev` is definition order.) Each export is ranked by the position
of the head constant of its interface term, after stripping the `Abs` that `add_interface`
wraps around an export without run-time argument (`procedure.ML:308-310`); a constant not
found ranks first; the sort is stable.

Assumption stated: an Isabelle definition can only mention constants defined before it, so
definition order along the ancestor chain is a callee-first order; two separately defined
procedure constants cannot be mutually recursive (self-recursion is inside one definition,
handled by `op_rec_routine`). Limit recorded: a procedure constant that occurs only in an
*instance argument* of an export (`\<phi>export for P = bar`) is not ordered by this; if it
is itself exported later it is printed twice (Section 5.4). No export in the corpus does
this. A wrong order costs one duplicate function, never wrong code: the export path has
`pf = SOME e` and bypasses the discard branch.

## 7. Walkthroughs

**Matrix_Oprs.** Every callee export precedes its callers. `interf "add_mat" (add_mat_ 4 4)`:
the wrapper sets the frame to `Named "f__12Matrix__Oprs8add__mat1A41A4"`, `new_fun` takes
`pf = "add_mat"`, takes the frame as the alias, prints `void add_mat(...)`, registers the
`F`, `K` and alias entries. Printing `strassen`, each of the twelve `add_mat_ (b0) (b0)` sets
the same `Named`, `new_fun` hits by name and prints `add_mat(v6,v7,...)`. `strassen_mul`
(`n = 2`): `new_mat_ 4 4`, `strassen_ 4` and `del_mat_` hit their aliases and print
`new_mat()`, `strassen(...)`, `del_mat(v3)`. Expected: eight functions.

**Binary_Trees.** `lookup_bintree_ TY_K TY_V CMP Eq`: `C'G_fun_K (CMP_v)` gives `NONE`, the
wrapper sets `Anonymous`, the export top uses `pf`. `Max` and `height_of` have no unnameable
parameter, become named instances and collapse; `maintain_i_ TY_K TY_V` inside `insert_avl_i`
hits the alias of the exported `maintain_i`. Expected: seven functions.

**Dynamic_Array.** `concat_dynarr` calls `push_dynarr`; both are exported for `\<size_t>`.
Definition order emits `push_dynarr` first; inside `concat_dynarr` the instance name hits the
alias. `Max`, `len_dynarr`, `get_dynarr` likewise. Expected: nine functions.

**A generic procedure with a procedure parameter used twice** (hypothetical): both uses set
`Anonymous`, both get serial names, both print; the second hits the content key of the first
and is discarded; one function.

## 8. Cost and later work

A named instance is printed once. An unnameable instance is printed once per call site and
discarded on every hit; nested unnameable instances multiply along the nesting depth. This
is bounded by what happens today (today every copy is also emitted) and is removed only by
giving procedure-valued parameters a text: a later `proc_K` may run the value on placeholder
arguments in a scratch buffer and use the printed text (arity by nesting `fun_K argK resK`,
mirroring `gen_typ`'s recursion; `pointer_eq` as a cheap first check). Not needed for the
current examples. Adding a procedure with a parameter whose head type constructor has no
`_K` hook now requires one before the theory builds.

## 9. Change list

| File | Change |
| --- | --- |
| `library/codegen/base.ML` | `datatype frame`; `ctxt` sixth component; `get_frame`/`set_frame`, `frame`, `frame'`, `spell`, `mangle`, `key_int`, `key_bool`, `key_strs`, `content_key`, `fun_entry`/`typedef_entry`/`key_entry`, `the_fun`; `new_fun` as in Section 5.2 (`fun_name` deleted); `interf` as in Section 5.5; `serial "f__"`; `codegen'` initial `ctxt`; `cat`/`catw` moved above the new definitions |
| `library/codegen/C/base.ML` | `defty'` pattern and `typedef_entry`, `serial "T__"` |
| `library/codegen/C/misc.ML`, `C/List.ML`, `C/Phi_Semantics_Framework.ML` | `nat_K`, `bool_K`, `len_K` (in the existing `C'G_Type_Length`), `C'G_fun_K`, `prod_K`, `option_K`, `list_K`, `TY_K`, `FIX_ARITY_VALs_K` |
| `library/codegen/emit.ML` | `binder`; `gen_proc` wrapper (4.6, reads the binder record); `gen_extractor`/`codegen` take an ordered list and a `Context.generic` |
| `Phi_Semantics/codegen/C/routine.ML` | `fun_name () (new_fun …)` → `new_fun …` |
| `library/codegen_nonkernel/base.sig`, `C/base.sig` | `datatype frame`, `type ctxt`, and the new values |
| `library/system/procedure.ML` (not trust base) | the binder record: `has_arg` stored beside the parameter names, accessor `has_runtime_arg` |
| `library/codegen_nonkernel/emit.ML` | definition-order sort of the exports; passes the context |

Untouched: `IDE_CP_Core.thy`, `tr_str`, every other hook.

## 10. Verification

Results (2026-09-08, implementation as in Section 9): items 1, 3 and 4 pass on every example
theory — Matrix_Oprs 8 functions (221 lines, from 2459), Binary_Trees 7, Dynamic_Array 9,
Linked_List 10, Bucket_Hash 11, Rational_Arith 8, Quicksort 1, Binary_Search 1, no `f__`
name in any of them, all callers use export names, every file passes
`gcc -x c -Wall -Wextra -fsyntax-only`; Quicksort and Binary_Search are identical to the
previous output after renaming `f`/`T` serials. The four negative tests behave as specified
(`ai-artifacts/Scratch_Naming_{A,B,C,D}.thy`); since `codegen'` was changed to print every
function before opening the file, test D was re-run and a refused export leaves no `.C` file
behind. Item 5 (`FIX_ARITY_VALs_K`) is not exercised.
After the local variables were renamed to `_v` followed by digits (same day), every file was
regenerated from one session: the function counts are unchanged, no `v` followed by digits
remains, test C (export name `"_v12"`) is refused. `gcc -Wall -Wextra` reports three
warnings that come from the sources (a value computed and never used in `strassen_mul`,
`pop_dynarr` and `length_of`) and one error in `Quicksort.C`: the export name `qsort`
collides with the `qsort` declared by `<stdlib.h>`, which the prelude includes.
PhiTest_Arithmetic 3 (test_prime, test_prime2, GCD) after its three `mod`/`div` sites were
rewritten to the φ-language operators `%` and `/`, which are now bound to the truncating
instructions `op_asmod`/`op_asdiv`; the cartouche spellings `mod`/`div` still synthesise the
floor division (`op_adiv`/`op_amod`, no hook) because the old ℕ synthesis rules
(`op_udiv_anat_φapp`, `op_mod_anat_φapp`) still carry `φsynthesis`.

1. Each generated file contains exactly one function per export: Matrix_Oprs 8,
   Binary_Trees 7, Dynamic_Array 9, Linked_List 10, Bucket_Hash 11, Rational_Arith 8,
   PhiTest_Arithmetic 3, Quicksort 1, Binary_Search 1. Every file compiles with `gcc -x c -Wall -Wextra -fsyntax-only`.
2. The set of function bodies is unchanged: canonicalise each `.C` by replacing a function's
   own name with `<self>`, replacing each called generated name by the canonical body of its
   class (to a fixpoint), and expanding each typedef name into the text of its `typedef` line
   (to a fixpoint); the set of canonical bodies of the new file equals that of the current
   file. Byte identity is impossible: `serial_c` is one counter for the whole session,
   `key_strs` runs type printers earlier than the routine header does, and the export order
   changes from `fast_string_ord` to definition order.
3. `strassen` calls `add_mat`/`sub_mat`/`copy_mat` by name; `strassen_mul` calls
   `new_mat`/`strassen`/`del_mat` by name; `concat_dynarr` calls `push_dynarr` by name.
4. Negative tests in a scratch theory: two exports of the same instance under two names
   produce two functions; an export name matching `^.__` or `^_v[0-9]+$` is refused; an
   export whose body reaches no routine is refused.
5. Scratch test for `FIX_ARITY_VALs_K`: a definition with a `FIX_ARITY_VALs`-sorted `TYPE`
   parameter exported at `VAL`, `unit` and a product yields three distinct instance names and
   one function each.
