signature PHI_SLEDGEHAMMER_SOLVER = sig

include PHI_SLEDGEHAMMER_SOLVER

val assign_proof_id   : Context.generic -> int * Context.generic
val assign_proof_id'  : theory -> int * theory
val assign_proof_id'' : Proof.context -> int * Proof.context

val export  : Proof.context -> Proof.context -> Proof.context
val export' : Proof.context -> Morphism.declaration

end

structure Phi_Sledgehammer_Solver : PHI_SLEDGEHAMMER_SOLVER = struct

open Phi_Sledgehammer_Solver

structure Proof_Id = Generic_Data (
  type T = int
  val empty = 0
  val merge = K 0
)

fun assign_proof_id generic =
  let val i = Proof_Id.get generic in (i, Proof_Id.put (i+1) generic) end

fun assign_proof_id' thy =
  let val (i,generic) = assign_proof_id (Context.Theory thy)
   in (i, Context.the_theory generic) end

fun assign_proof_id'' ctxt =
  let val (i,generic) = assign_proof_id (Context.Proof ctxt)
   in (i, Context.the_proof generic) end

fun export from to =
  Context.proof_map (Proof_Id.put (Proof_Id.get (Context.Proof from))) to

fun export' from = K (Proof_Id.put (Proof_Id.get (Context.Proof from)))

end
