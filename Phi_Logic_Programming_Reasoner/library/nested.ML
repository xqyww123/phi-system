signature PLPR_NESTED_REASONING = sig

val enter_scope : context_state -> context_state Seq.seq
val exit_scope  : context_state -> context_state Seq.seq
val call : context_state -> context_state Seq.seq

end

structure PLPR_Nested_Reasoning : PLPR_NESTED_REASONING = struct

(*** Nested Reasoning ***)

structure Scope = Proof_Data (struct
  type T = int
  val init = K 0
end)

fun enter_scope (ctxt,sequent) =
  let
  val S = Scope.get ctxt
  val ctxt' = Scope.map (fn x => x + 1) ctxt
  val sequent' = @{thm \<r>BEGIN_I} RS sequent
  val _ = Phi_Reasoner.info_print ctxt 2 (fn _ =>
            "entering nested \<phi>-LPR reasoning " ^ string_of_int S ^ Position.here \<^here>)
  in case Phi_Reasoner.reason NONE (ctxt',sequent')
       of SOME (ctxt'',sequent'') =>
          if Scope.get ctxt'' = S
          then Seq.single (ctxt'',sequent'')
          else Phi_Reasoner.error "The stack of nested \<phi>-LPR reasoning is inbalanced.\n\
            \Most likely some reasoner or reasoning rule invoked \<r>Success terminating\
            \the reasoning immediately, which is prohibited in nested \<phi>-LPR reasoning."
        | NONE => Phi_Reasoner.error "Reasoning (nested \<phi>-LPR environment) fails."
  end

fun exit_scope (ctxt,sequent) = (
  Phi_Reasoner.info_print ctxt 2 (fn _ =>
    "exiting the nested \<phi>-LPR reasoning "^ string_of_int (Scope.get ctxt - 1) ^ Position.here \<^here>);
  raise Phi_Reasoner.Success (Scope.map (fn x => x - 1) ctxt,
                             @{thm \<r>END_I} RS sequent)
)

fun call (ctxt,sequent) = Seq.make (fn () =>
  Phi_Reasoner.reason (SOME 1) (ctxt, @{thm \<r>Call_I} RS sequent)
    |> Option.map (rpair Seq.empty)
)
end