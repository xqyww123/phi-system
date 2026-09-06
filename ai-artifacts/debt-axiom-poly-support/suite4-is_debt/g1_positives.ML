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
(* g1: positives M1-M8 *)

(*declared (pre-export) forms*)
val m1 = rd thy0 "!!n::nat. n + 0 = n";
val m2 = rd thy0 "!!n m::nat. n < m ==> n <= m";
val m3 = rd thy0 "!!x y::'a::comm_monoid_add. x + y = y + x";
val m4 = rd thy0 "!!x::'a::comm_monoid_add. x = 0 ==> x + x = x";
val m5 = rd thy0 ("!!x y::'a::comm_monoid_add. !!u v::'b::comm_monoid_mult. " ^
                  "x + y = y + x & u * v = v * u");
val m6 = rd thy0 "(0::nat) + 0 = 0";

val l1 = ledger_entry thy0 m1;
val l2 = ledger_entry thy0 m2;
val l3 = ledger_entry thy0 m3;
val l4 = ledger_entry thy0 m4;
val l5 = ledger_entry thy0 m5;
val l6 = ledger_entry thy0 m6;

fun single_ledger n l = Symtab.make [(n, l)];

(*real exports*)
val e1 = real_export thy0 "m1" m1 (simp_with []);
val e2 = real_export thy0 "m2" m2 (rule_then_assume ["less_imp_le"]);
val e3 = real_export thy0 "m3" m3 (simp_with ["add.commute"]);
val e4 = real_export thy0 "m4" m4 (simp_with []);
val e5 = real_export thy0 "m5" m5 (simp_with ["add.commute", "mult.commute"]);
val e6 = real_export thy0 "m6" m6 (simp_with []);

val _ = writeln ("SHAPE M1 exported: " ^ pr_sorts thy0 e1);
val _ = writeln ("SHAPE M2 exported: " ^ pr_sorts thy0 e2);
val _ = writeln ("SHAPE M3 exported: " ^ pr_sorts thy0 e3);
val _ = writeln ("SHAPE M4 exported: " ^ pr_sorts thy0 e4);
val _ = writeln ("SHAPE M5 exported: " ^ pr_sorts thy0 e5);
val _ = writeln ("SHAPE M6 exported: " ^ pr_sorts thy0 e6);

(*M1-M6: exported query vs its own single-entry ledger*)
val _ = verdict "M1" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m1" l1) e1)) "";
val _ = verdict "M2" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m2" l2) e2)) "";
val _ = verdict "M3" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m3" l3) e3)) "";
val _ = verdict "M4" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m4" l4) e4)) "";
val _ = verdict "M5" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m5" l5) e5)) "";
val _ = verdict "M6" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m6" l6) e6)) "";

(*M7: the DECLARED forms must also match*)
val _ = verdict "M7-m1" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m1" l1) m1)) "";
val _ = verdict "M7-m2" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m2" l2) m2)) "";
val _ = verdict "M7-m3" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m3" l3) m3)) "";
val _ = verdict "M7-m4" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m4" l4) m4)) "";
val _ = verdict "M7-m5" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m5" l5) m5)) "";

(*M8: the ledger entry itself as query*)
val _ = verdict "M8-m1" "ledger-entry" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m1" l1) l1)) "";
val _ = verdict "M8-m3" "ledger-entry" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m3" l3) l3)) "";
val _ = verdict "M8-m5" "ledger-entry" true
          (run_bool (fn () => is_debt thy0 (single_ledger "m5" l5) l5)) "";

(*multi-entry ledger: query must be found among several entries*)
val big = Symtab.make [("m1", l1), ("m2", l2), ("m3", l3), ("m4", l4), ("m5", l5)];
val _ = verdict "M-multi" "real-export" true
          (run_bool (fn () => is_debt thy0 big e4)) "M4 export vs 5-entry ledger";

(*cross sanity: an export must NOT match a DIFFERENT debt's ledger*)
val _ = verdict "M-cross-1v2" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "m2" l2) e1)) "";
val _ = verdict "M-cross-3v4" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "m4" l4) e3)) "";
