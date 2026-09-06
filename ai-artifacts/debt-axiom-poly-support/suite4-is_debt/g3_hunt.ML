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
(* g3: P3 hunt beyond the matrix *)

fun funT (a, b) = Type ("fun", [a, b]);
val natT = Type ("Nat.nat", []);

fun single_ledger n l = Symtab.make [(n, l)];

(*H1: nested !! INSIDE a premise -- inner binder must not be confused with outer*)
val h1 = rd thy0 "!!y::nat. (!!x::nat. x + 0 = x) ==> y + 0 = y";
val lh1 = ledger_entry thy0 h1;
val eh1 = real_export thy0 "h1" h1 (simp_with []);
val _ = writeln ("SHAPE H1 exported: " ^ pr_sorts thy0 eh1);
val _ = verdict "H1" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h1" lh1) eh1)) "";
val _ = verdict "H1-declared" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h1" lh1) h1)) "";
(*and it must NOT collapse to the premise-free M1 debt*)
val m1 = rd thy0 "!!n::nat. n + 0 = n";
val _ = verdict "H1-vs-M1" "real-export" false
          (run_bool (fn () =>
             is_debt thy0 (single_ledger "m1" (ledger_entry thy0 m1)) eh1)) "";

(*H2: two !!-params sharing a base name (inner shadows outer, outer unused)*)
val h2 = rd thy0 "!!x::nat. !!x::nat. x + 0 = x";
val lh2 = ledger_entry thy0 h2;
val eh2 = real_export thy0 "h2" h2 (simp_with []);
val _ = writeln ("SHAPE H2 exported: " ^ pr_sorts thy0 eh2);
val _ = writeln ("SHAPE H2 exported raw: " ^ raw_term eh2);
val _ = writeln ("SHAPE H2 match_form(ledger) raw: " ^ raw_term (match_form thy0 lh2));
val _ = verdict "H2" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h2" lh2) eh2)) "";

(*H3: partially normalized query -- leftover !! mixed with Vars.
  Built by re-quantifying one Var of the REAL M2 export; the consumer never
  produces this shape, result is an observation, not a matrix expectation.*)
val m2 = rd thy0 "!!n m::nat. n < m ==> n <= m";
val l2 = ledger_entry thy0 m2;
val e2 = real_export thy0 "h3m2" m2 (rule_then_assume ["less_imp_le"]);
val e2vars = Term.add_vars e2 [];
val vn = (case find_first (fn ((a, _), _) => a = "n") e2vars of
            SOME v => v | NONE => hd e2vars);
val h3 = Logic.all_const (#2 vn) $ Abs ("n", #2 vn, Term.abstract_over (Var vn, e2));
val _ = writeln ("SHAPE H3 mixed query raw: " ^ raw_term h3);
val _ = writeln ("OBSERVE H3 (mixed !!+Var query vs M2 ledger): " ^
                 run_bool (fn () => is_debt thy0 (single_ledger "m2" l2) h3));

(*H10: leftover Var sharing its NAME with the re-quantified binder --
  gen_all_term must keep them distinct (fresh index), no conflation*)
val vm = (case find_first (fn ((a, _), _) => a = "m") e2vars of
            SOME v => v | NONE => hd e2vars);
val h10 = Logic.all_const (#2 vm) $ Abs ("m", #2 vm, Term.abstract_over (Var vn, e2));
  (*binder named "m" over the hole left by ?n, while ?m stays -- name collision*)
val _ = writeln ("SHAPE H10 collision query raw: " ^ raw_term h10);
val _ = writeln ("SHAPE H10 match_form raw: " ^ raw_term (match_form thy0 h10));
val ldiag = ledger_entry thy0 (rd thy0 "!!k::nat. k < k ==> k <= k");
val _ = writeln ("OBSERVE H10a (collision query vs M2 ledger, expect true): " ^
                 run_bool (fn () => is_debt thy0 (single_ledger "m2" l2) h10));
val _ = verdict "H10b" "hand-built-negative" false
          (run_bool (fn () => is_debt thy0 (single_ledger "diag" ldiag) h10))
          "must not conflate the two distinct variables into the diagonal";

(*H4: empty sort written explicitly by a user*)
val h4 = rd thy0 "!!x::'a::{}. x == x";
val lh4 = ledger_entry thy0 h4;
val eh4 = real_export thy0 "h4" h4
            (fn ctxt => HEADGOAL (resolve_tac ctxt [Drule.reflexive_thm]));
val _ = writeln ("SHAPE H4 exported: " ^ pr_sorts thy0 eh4);
val _ = writeln ("SHAPE H4 exported raw: " ^ raw_term eh4);
val _ = verdict "H4" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h4" lh4) eh4)) "";
val _ = verdict "H4-declared" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h4" lh4) h4)) "";

(*H5: long premise chain*)
val h5 = rd thy0 ("!!a b c d e f::nat. a = 0 ==> b = 0 ==> c = 0 ==> d = 0 ==> " ^
                  "e = 0 ==> f = 0 ==> a + b + c + d + e + f = 0");
val lh5 = ledger_entry thy0 h5;
val eh5 = real_export thy0 "h5" h5 (simp_with []);
val _ = verdict "H5" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h5" lh5) eh5)) "";

(*H6: eta-contracted outer !! with a Var head -- hand-built, must not raise*)
val m3 = rd thy0 "!!x y::'a::comm_monoid_add. x + y = y + x";
val l3 = ledger_entry thy0 m3;
val h6 = Logic.all_const natT $ Var (("P", 0), funT (natT, Type ("prop", [])));
val _ = writeln ("SHAPE H6 match_form raw: " ^
                 (case Exn.capture (fn () => raw_term (match_form thy0 h6)) () of
                    Exn.Res s => s
                  | Exn.Exn exn => "EXN: " ^ Runtime.exn_message exn));
val _ = verdict "H6" "hand-built-negative" false
          (run_bool (fn () => is_debt thy0 (single_ledger "m3" l3) h6)) "";

(*H7: multi-class sort -- two OFCLASS premises, order must agree on both sides*)
val h7 = rd thy0 "!!x::'a::{monoid_add, monoid_mult}. x + 0 = x";
val lh7 = ledger_entry thy0 h7;
val eh7 = real_export thy0 "h7" h7 (simp_with []);
val _ = writeln ("SHAPE H7 exported: " ^ pr_sorts thy0 eh7);
val _ = writeln ("SHAPE H7 ledger raw: " ^ raw_term lh7);
val _ = writeln ("SHAPE H7 match_form(export) raw: " ^ raw_term (match_form thy0 eh7));
val _ = verdict "H7" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h7" lh7) eh7)) "";
val _ = verdict "H7-declared" "declared" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h7" lh7) h7)) "";

(*H9: object-level ALL with a higher-order Var in the exported shape*)
val h9 = rd thy0 "!!P::nat => bool. (ALL x::nat. P x) ==> P 0";
val lh9 = ledger_entry thy0 h9;
val eh9 = real_export thy0 "h9" h9
            (fn ctxt => HEADGOAL (eresolve_tac ctxt
                          [Proof_Context.get_thm ctxt "allE"] THEN' assume_tac ctxt));
val _ = writeln ("SHAPE H9 exported: " ^ pr_sorts thy0 eh9);
val _ = verdict "H9" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "h9" lh9) eh9)) "";

(*H8: deliberate attack on devarifyT injectivity -- a hand-built query
  containing BOTH a TFree literally named "'a.0" AND the TVar ("'a", 0) at the
  same sort.  Such a TFree name is not even parseable in Isabelle syntax and no
  Spec_Rules fact can carry it; this probes the boundary, expected verdict per
  design intent is false.*)
val sT = ["HOL.type"];
val tf = TFree ("'a.0", sT);
val tv = TVar (("'a", 0), sT);
val vu = Var (("u", 0), tf);
val vw = Var (("w", 0), tv);
val h8_query = Logic.mk_implies (Logic.mk_equals (vu, vu), Logic.mk_equals (vw, vw));
val h8_debt = rd thy0 "!!x y::'a. x == x ==> y == y";
val lh8 = ledger_entry thy0 h8_debt;
val _ = writeln ("SHAPE H8 debt   raw: " ^ raw_term lh8);
val _ = writeln ("SHAPE H8 query  raw: " ^ raw_term h8_query);
val _ = writeln ("SHAPE H8 match_form(query) raw: " ^
                 (case Exn.capture (fn () => raw_term (match_form thy0 h8_query)) () of
                    Exn.Res s => s
                  | Exn.Exn exn => "EXN: " ^ Runtime.exn_message exn));
val _ = verdict "H8" "hand-built-negative" false
          (run_bool (fn () => is_debt thy0 (single_ledger "h8" lh8) h8_query))
          "devarifyT injectivity boundary probe";
