(* shyps.ML — check the produced discharge theorems carry no dangling sort hypotheses *)

val add_commute = Proof_Context.get_thm ctxt0 "add.commute";
val order_refl = Proof_Context.get_thm ctxt0 "order_refl";
val less_imp_le = Proof_Context.get_thm ctxt0 "less_imp_le";

fun probe name debt_prop cert =
  let
    val g = ledger_form thy0 debt_prop;
    val th = Goal.prove_internal ctxt0 [] (Thm.global_cterm_of thy0 g)
               (K (discharge_tac ctxt0 [prep_cert cert]));
    fun show_sorts Ss = commas (map (Syntax.string_of_sort ctxt0) Ss);
  in
    writeln (name ^ ": shyps = {" ^ show_sorts (Thm.shyps_of th) ^ "}" ^
             "; extra_shyps = {" ^ show_sorts (Thm.extra_shyps th) ^ "}" ^
             "; hyps = " ^ string_of_int (length (Thm.hyps_of th)))
  end;

val _ = probe "G1a" (rp "!!x y::'a::comm_monoid_add. x + y = y + x") add_commute;
val _ = probe "G2a" (rp "!!x::'a set. x <= x") order_refl;
val _ = probe "G3b" (rp "!!n m::nat. n < m ==> n <= m") less_imp_le;

val _ = writeln "SHYPS DONE";
