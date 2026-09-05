(*  Title:      context_export.ML
    Author:     Qiyuan Xu

The run boundary of PLPR: a run (one invocation of the engine) works on a
context that extends the context it was started from.  When the run ends,
the theorem is exported back onto the start context by Proof_Context.export,
and the context itself is exported by the hooks registered here: each hook
transplants the data it owns from the inner context into the outer one.

Hook contract (every registered hook must satisfy it):
  H1. A hook exports theorems only through export_aux_lemma, one theorem at
      a time; NONE means the theorem does not leave the run or block.
  H2. Re-exportable: for inner extending outer extending base,
        hook (hook inner outer) base = hook inner base.
      In particular a hook must not accumulate (append on every export);
      overwriting its slot, or merging as a set union, satisfies H2.
  H3. A hook reads only its own data from inner and writes only its own
      data into outer, so hooks are order-independent.
*)

signature PLPR_CONTEXT_EXPORT = sig

  (*A hook is  inner -> outer -> outer'.  Register with
      PLPR_Context_Export.Hooks.add priority hook
    (smaller priority runs first; one hook per priority per theory).*)
  structure Hooks : HOOKS
    where type arg = Proof.context (*inner*) and type state = Proof.context (*outer*)

  (*transplant hook-owned data from inner into outer.
    Precondition: inner extends outer (as for Proof_Context.export).*)
  val export_context : Proof.context (*inner*) -> Proof.context (*outer*) -> Proof.context

  (*the run boundary: Proof_Context.export for the theorem, export_context for the context*)
  val export_state : Proof.context (*inner*) -> Proof.context (*outer*) -> thm -> Proof.context * thm

  (*raised by the block-boundary export function of phi-system for a theorem that is not
    the state sequent but depends on a block assumption that is not of the form
    Premise _ C: the theorem cannot leave the block.  export_aux_lemma catches it.*)
  exception UNEXPORTABLE of thm

  (*the only way a hook exports a theorem (H1).  NONE: the theorem does not leave the
    run or block -- it mentions a variable fixed in inner but not in outer, or an
    assumption frame raised UNEXPORTABLE.  SOME: Proof_Context.export inner outer.*)
  val export_aux_lemma : Proof.context (*inner*) -> Proof.context (*outer*) -> thm -> thm option

end

structure PLPR_Context_Export : PLPR_CONTEXT_EXPORT = struct

structure Hooks = Hooks (type arg = Proof.context
                         type state = Proof.context)

fun export_context inner outer =
  if pointer_eq (inner, outer) then outer
  else Hooks.invoke (Context.Proof outer) inner outer

fun export_state inner outer th =
  (export_context inner outer, singleton (Proof_Context.export inner outer) th)

exception UNEXPORTABLE of thm

fun export_aux_lemma inner outer th =
  if Term.exists_subterm (fn Free (x, _) => Variable.is_newly_fixed inner outer x | _ => false)
                         (Thm.prop_of th)
  then NONE
  else SOME (singleton (Proof_Context.export inner outer) th) handle UNEXPORTABLE _ => NONE

end
