(* Reuse-equivalence measurement (plan section 8.0; review finding K4):
   the SHIPPED gen_all_term (library-reuse form, Drule.outer_params +
   Term.strip_all_body, Debt_Axiom.ML) against the DESIGN-PHASE hand-rolled
   dest_all form (suite4-is_debt/*.ML), which additionally eta-expands an
   eta-contracted outer Pure.all.  The two may differ only on such an
   eta-contracted outer quantifier -- a shape no ledger entry can carry --
   and a disagreement can only make is_debt conservatively answer false.
   Run:  Isabelle2025-2/bin/isabelle ML_process -l HOL -f reuse_equivalence.ML *)

val thy = (Thy_Info.get_theory "Main" handle ERROR _ => Thy_Info.get_theory "HOL.Main");
val ctxt = Proof_Context.init_global thy;
fun pr s = writeln ("### " ^ s);

(*the shipped form, Debt_Axiom.ML*)
fun gen_all_shipped t =
  let
    val idx = Term.maxidx_of_term t + 1
    val vars = map (fn (a, T) => Var ((a, idx), T)) (Drule.outer_params t)
  in Term.subst_bounds (rev vars, Term.strip_all_body t) end;

(*the design-phase form, verbatim from suite4-is_debt/g1_positives.ML*)
fun gen_all_session t =
  let
    val idx = Term.maxidx_of_term t + 1;
    fun dest_all (Const ("Pure.all", _) $ Abs (a, T, b)) = SOME ((a, T), b)
      | dest_all (Const ("Pure.all", Type ("fun", [Type ("fun", [T, _]), _])) $ f) =
          SOME (("x", T), Term.incr_boundvars 1 f $ Bound 0)
      | dest_all _ = NONE;
    fun strip t =
      (case dest_all t of
        SOME ((a, T), b) => let val (vs, u) = strip b in ((a, T) :: vs, u) end
      | NONE => ([], t));
    val (vs, body) = strip t;
    val names = Name.variant_list [] (map (Name.clean o #1) vs);
    val vars = map2 (fn a => fn (_, T) => Var ((a, idx), T)) names vs;
  in Term.subst_bounds (rev vars, body) end;

fun disagree t = gen_all_shipped t <> gen_all_session t;

val spec_props = Spec_Rules.get ctxt |> maps #rules |> map Thm.prop_of;
val _ = pr ("spec-rule props (Spec_Rules.get, all classifications): " ^
            string_of_int (length spec_props) ^
            ", disagreements: " ^ string_of_int (length (filter disagree spec_props)));

val fact_props = Global_Theory.all_thms_of thy false |> map (Thm.prop_of o snd);
val _ = pr ("global-fact props (Global_Theory.all_thms_of thy false): " ^
            string_of_int (length fact_props) ^
            ", disagreements: " ^ string_of_int (length (filter disagree fact_props)));

val _ = pr "DONE";
