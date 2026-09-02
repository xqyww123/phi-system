(*  Shared harness: independent verification of the redesigned Debt_Axiom.is_debt
    comparison.  Run via: isabelle ML_process -l HOL -f <group>.ML
    ASCII only, no antiquotations.  *)

val thy0 =
  (Thy_Info.get_theory "HOL.Main"
   handle ERROR _ => Thy_Info.get_theory "Main");

fun ctxt_of thy = Proof_Context.init_global thy;

fun pr_sorts thy t =
  Syntax.string_of_term (Config.put Printer.show_sorts true (ctxt_of thy)) t;

fun raw_typ (Type (c, Ts)) =
      "Ty(" ^ c ^ (if null Ts then "" else "," ^ commas (map raw_typ Ts)) ^ ")"
  | raw_typ (TFree (a, S)) = "TFree(" ^ a ^ ",[" ^ commas S ^ "])"
  | raw_typ (TVar ((a, i), S)) =
      "TVar(" ^ a ^ "_" ^ string_of_int i ^ ",[" ^ commas S ^ "])";

fun raw_term (Const (c, _)) = "C." ^ c
  | raw_term (Free (x, T)) = "Free(" ^ x ^ ":" ^ raw_typ T ^ ")"
  | raw_term (Var ((x, i), T)) = "Var(" ^ x ^ "_" ^ string_of_int i ^ ":" ^ raw_typ T ^ ")"
  | raw_term (Bound i) = "B" ^ string_of_int i
  | raw_term (Abs (a, T, b)) = "Abs(" ^ a ^ ":" ^ raw_typ T ^ ". " ^ raw_term b ^ ")"
  | raw_term (t $ u) = "(" ^ raw_term t ^ " $ " ^ raw_term u ^ ")";


(* stripped_sorts: copied VERBATIM from Debt_Axiom.ML lines 37-46 *)

fun stripped_sorts thy t =
  let
    val tfrees = build_rev (Term.add_tfrees t);
    val tfrees' = map (fn a => (a, [])) (Name.variant_list [] (map #1 tfrees));
    val recover =
      map2 (fn (a', S') => fn (a, S) => (((a', 0), S'), Thm.global_ctyp_of thy (TVar ((a, 0), S))))
        tfrees' tfrees;
    val strip = map (apply2 TFree) (tfrees ~~ tfrees');
    val t' = Term.map_types (Term.map_atyps (perhaps (AList.lookup (op =) strip))) t;
  in (strip, recover, t') end;


(* ledger entry: exactly what add_debt_axiom stores (Debt_Axiom.ML lines 52-57) *)

fun ledger_entry thy prop =
  let
    val (strip, _, prop') = stripped_sorts thy prop;
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
  in Logic.list_implies (maps Logic.mk_of_sort constraints, prop') end;


(* the design under test *)

(*devarify type schematics injectively (index folded into the name)*)
fun devarifyT t = t |> Term.map_types (Term.map_atyps
      (fn TVar ((a, i), S) => TFree (a ^ "." ^ string_of_int i, S) | A => A));

(*term-level mirror of Variable.gen_all (variable.ML:510) + Drule.outer_params
  (drule.ML:162): strip outer !!-params into schematic Vars at one fresh index,
  names made mutually distinct exactly as outer_params does; tolerates an
  eta-contracted outer quantifier by eta-expanding it first*)
fun gen_all_term t =
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

(*the shared normal form: sort-strip + OFCLASS premises (ledger shape), then
  HHF-normalize at the term level and generalize outer !!-params into Vars --
  mirroring what the export did to the consumer's copy -- then varify tfrees*)
fun match_form thy prop =
  let
    val prop0 = devarifyT prop;
    val (strip, _, prop') = stripped_sorts thy prop0;
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
    val ledger_shaped = Logic.list_implies (maps Logic.mk_of_sort constraints, prop');
  in
    ledger_shaped
    |> Drule.norm_hhf thy
    |> gen_all_term
    |> Logic.varify_types_global
  end;

fun is_debt thy ledger t =
  let val u = match_form thy t
  in Symtab.exists (fn (_, ax) => Pattern.equiv thy (u, match_form thy ax)) ledger end;


(* the REAL export path: Named_Target.theory_init -> Goal.prove -> Spec_Rules.add
   -> Local_Theory.exit_global -> Spec_Rules.get of the new global context *)

fun real_export thy name prop tac =
  let
    (*a properly NAMED child theory, as any real consumer theory would be;
      without it, Global_Theory.transfer_theories resolves the long name "Main"
      to the heap's old Main and Spec_Rules.get fails with
      "Cannot transfer: not a super theory"*)
    val thy1 = Theory.begin_theory ("Isdebt_" ^ name, Position.none) [thy];
    val lthy = Named_Target.theory_init thy1;
    val th = Goal.prove lthy [] [] prop (fn {context = goal_ctxt, ...} => tac goal_ctxt);
    val lthy' = Spec_Rules.add (Binding.name name) Spec_Rules.Unknown [] [th] lthy;
    val thy' = Local_Theory.exit_global lthy';
    val hits =
      Spec_Rules.get (Proof_Context.init_global thy')
      |> filter (fn {name = n, rough_classification = c, ...} =>
           Spec_Rules.is_unknown c andalso String.isSubstring name n);
  in
    (case hits of
      [{rules = [th'], ...}] => Thm.prop_of th'
    | [{rules = ths, ...}] =>
        (writeln ("NOTE real_export " ^ name ^ ": " ^ string_of_int (length ths) ^
                  " rules in entry, taking hd");
         Thm.prop_of (hd ths))
    | [] => error ("real_export: no Unknown spec rule named like " ^ name)
    | _ => error ("real_export: ambiguous spec-rule name " ^ name))
  end;


(* proving helpers *)

fun rd thy s = Syntax.read_prop (ctxt_of thy) s;

fun simp_with names ctxt =
  let val ctxt' = fold (Simplifier.add_simp o Proof_Context.get_thm ctxt) names ctxt
  in ALLGOALS (Simplifier.asm_full_simp_tac ctxt') end;

fun rule_then_assume names ctxt =
  HEADGOAL (resolve_tac ctxt (map (Proof_Context.get_thm ctxt) names)
            THEN' assume_tac ctxt);


(* reporting *)

fun run_bool f =
  (case Exn.capture f () of
    Exn.Res b => Bool.toString b
  | Exn.Exn exn => "EXN: " ^ Runtime.exn_message exn);

fun verdict case_name provenance expected got note =
  writeln ("RESULT | " ^ case_name ^ " | " ^ provenance ^ " | expected=" ^
           Bool.toString expected ^ " | got=" ^ got ^ " | " ^
           (if got = Bool.toString expected then "PASS" else "*** FAIL ***") ^
           (if note = "" then "" else " | " ^ note));
(* g0: probe -- validate harness, export shape, Name.variant behavior *)

val _ = writeln ("PROBE theory = " ^ Context.theory_long_name thy0);
val _ = writeln ("PROBE variant_list [] [\"'a.0\"] = " ^
                 commas (Name.variant_list [] ["'a.0"]));
val _ = writeln ("PROBE variant_list [] [x,x] = " ^
                 commas (Name.variant_list [] ["x", "x"]));
val _ = writeln ("PROBE clean \"x_\" = " ^ Name.clean "x_");

val m2_prop = rd thy0 "!!n m::nat. n < m ==> n <= m";
val m2_exported = real_export thy0 "probe_m2" m2_prop (rule_then_assume ["less_imp_le"]);
val _ = writeln ("PROBE M2 exported (show_sorts): " ^ pr_sorts thy0 m2_exported);
val _ = writeln ("PROBE M2 exported (raw): " ^ raw_term m2_exported);

val m2_ledger = ledger_entry thy0 m2_prop;
val _ = writeln ("PROBE M2 ledger (show_sorts): " ^ pr_sorts thy0 m2_ledger);
val _ = writeln ("PROBE M2 ledger (raw): " ^ raw_term m2_ledger);

val _ = writeln ("PROBE match_form(M2 exported) raw: " ^
                 raw_term (match_form thy0 m2_exported));
val _ = writeln ("PROBE match_form(M2 ledger)   raw: " ^
                 raw_term (match_form thy0 m2_ledger));

val _ = verdict "PROBE-M2" "real-export" true
          (run_bool (fn () =>
             is_debt thy0 (Symtab.make [("m2", m2_ledger)]) m2_exported)) "";

(*HHF sanity at the term level: OFCLASS prem in front of a !!-closed body*)
val m3_prop = rd thy0 "!!x y::'a::comm_monoid_add. x + y = y + x";
val m3_ledger = ledger_entry thy0 m3_prop;
val _ = writeln ("PROBE M3 ledger (raw): " ^ raw_term m3_ledger);
val _ = writeln ("PROBE norm_hhf(M3 ledger) raw: " ^
                 raw_term (Drule.norm_hhf thy0 m3_ledger));
val _ = writeln ("PROBE match_form(M3 ledger) raw: " ^
                 raw_term (match_form thy0 m3_ledger));
