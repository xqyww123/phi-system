(* AUTHOR: Qiyuan Xu
   A mechanism collecting potential failures of \<phi>-LPR reasoning.
 *)

signature PHI_REASONERS = sig
include PHI_REASONERS

type failure_reason = (unit -> Pretty.T)

val report_failure_reason  : int -> failure_reason list -> Proof.context -> Proof.context
val report_failure_reason1 : Proof.context -> int -> failure_reason list -> unit
val report_failure_reason' : Proof.context -> int -> failure_reason list -> unit
val failure_reasons_of  : Proof.context -> Pretty.T list
val failure_reasons_of' : Proof.context -> Pretty.T list

val setup_failure_reason_environ : failure_reason list -> Proof.context -> Proof.context
val reset_failure_reasons : Proof.context -> Proof.context

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

type failure_reason = (unit -> Pretty.T)

structure Failure_Reasoners = Proof_Data (
  type T = failure_reason list Synchronized.var option (*allocate on write*)
  val init = K NONE
)

val reset_failure_reasons = Failure_Reasoners.put NONE
fun setup_failure_reason_environ G ctxt =
  case Failure_Reasoners.get ctxt
    of SOME rf =>
        (Synchronized.change rf (fn L => G @ L) ; ctxt)
     | NONE =>
        Failure_Reasoners.put (SOME (Synchronized.var "\<phi>LPR.failure_reasons" G)) ctxt

fun report_failure_reason level G ctxt = (
  List.app (Phi_Reasoner.warn_pretty (Context.Proof ctxt) level) G ;
  setup_failure_reason_environ G ctxt
)

fun report_failure_reason1 ctxt level G = (
  List.app (Phi_Reasoner.warn_pretty (Context.Proof ctxt) level) G ;
  case Failure_Reasoners.get ctxt
    of SOME rf =>
        Synchronized.change rf (fn L => G @ L)
     | NONE => error "Failure storage is not allocated!"
)

fun report_failure_reason' ctxt level G =
  if level <= Config.get_generic (Context.Proof ctxt) Phi_Reasoner.trace
  then List.app (fn G => warning (Pretty.string_of (G ()))) G
  else case Failure_Reasoners.get ctxt
    of SOME rf => Synchronized.change rf (fn L => G @ L)
     | NONE => List.app (fn G => warning (Pretty.string_of (G ()))) G



fun failure_reasons_of ctxt =
  let open Pretty
   in case Failure_Reasoners.get ctxt
   of SOME rf => map (fn G => item [G ()]) (Synchronized.value rf)
    | NONE => []
  end

fun failure_reasons_of' ctxt =
  let val reasons = failure_reasons_of ctxt
      open Pretty
   in case reasons
   of [] => []
    | L => (
          block (text "There are some potential reasons:") ::
          L
        )
  end


end