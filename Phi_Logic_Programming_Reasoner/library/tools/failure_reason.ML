(* AUTHOR: Anonymous Authors
   A mechanism collecting potential failures of \<phi>-LPR reasoning.
 *)

signature PHI_REASONERS = sig
include PHI_REASONERS

type failure_reason = (unit -> Pretty.T)

val report_failure_reason  : failure_reason list -> Proof.context -> Proof.context
val report_failure_reason1 : Proof.context -> failure_reason list -> unit
val report_failure_reason' : Proof.context -> failure_reason list -> unit
val failure_reasons_of : Proof.context -> Pretty.T list

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

type failure_reason = (unit -> Pretty.T)

structure Failure_Reasoners = Proof_Data (
  type T = failure_reason list Synchronized.var option (*allocate on write*)
  val init = K NONE
)


fun report_failure_reason G ctxt = (
  List.app (Phi_Reasoner.warn_pretty (Context.Proof ctxt) 2) G ;
  case Failure_Reasoners.get ctxt
    of SOME rf =>
        (Synchronized.change rf (fn L => G @ L) ; ctxt)
     | NONE =>
        Failure_Reasoners.put (SOME (Synchronized.var "\<phi>LPR.failure_reasons" G)) ctxt
)

fun report_failure_reason1 ctxt G = (
  List.app (Phi_Reasoner.warn_pretty (Context.Proof ctxt) 2) G ;
  case Failure_Reasoners.get ctxt
    of SOME rf =>
        Synchronized.change rf (fn L => G @ L)
     | NONE => error "Failure storage is not allocated!"
)

fun report_failure_reason' ctxt G = (
  List.app (Phi_Reasoner.warn_pretty (Context.Proof ctxt) 2) G ;
  case Failure_Reasoners.get ctxt
    of SOME rf => Synchronized.change rf (fn L => G @ L)
     | NONE => ()
)


fun failure_reasons_of ctxt =
  let open Pretty
   in case Failure_Reasoners.get ctxt
   of SOME rf => map (fn G => item [G ()]) (Synchronized.value rf)
    | NONE => []
  end
  

end