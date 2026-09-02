(* g5.ML — G5: mixed type: obligation OFCLASS('a * nat, equal_class) *)

val equal_eq = Proof_Context.get_thm ctxt0 "equal_eq";

(*'a::equal * nat :: equal holds via prod::(equal,equal) equal and nat::equal*)
val _ = case_run "G5 (mixed 'a * nat, class equal)"
  (rp "!!x y::('a::equal) * nat. equal_class.equal x y = (x = y)") equal_eq;

val _ = writeln "G5 DONE";
