signature NU_FACTS = sig
  (* `open_specthm (ctx,specthm)` puts auxiliary facts into the context by the name `\<nu>aux`
  *     and returns the focus proposition of the specification theorem.  *)
  val open_specthm  : thm -> Proof.context -> thm * Proof.context
  val open_specthm' : Position.T -> thm -> Proof.context -> thm * Proof.context
  (* get the auxiliary facts `\<nu>aux` which is usually stored by `open_specthm` *)
  val aux_facts : Proof.context -> thm list
  (* reassemble the specification theorem by the given focus proposition and the stored
  *     auxiliary facts `\<nu>aux` *)
  val close_specthm : Proof.context -> thm -> thm
end
structure NuFacts : NU_FACTS = struct
val dest_AndFact_c = dest_binop_c "NuPrim.AndFact"
fun elim_AndFact th =
  let
    val (P, Q) = dest_AndFact_c (Thm.cprop_of th)
      handle TERM (msg, _) => raise THM (msg, 0, [th]);
    val inst = Thm.instantiate ([], [(vP, P), (vQ, Q)]);
  in
   (Thm.implies_elim (inst @{thm AndFact_D1}) th,
    Thm.implies_elim (inst @{thm AndFact_D1}) th)
  end
fun elim_AndFacts th =
  (case try elim_AndFact th of
    NONE => [th]
  | SOME (th1, th2) => elim_AndFacts th1 @ elim_AndFacts th2)
end
