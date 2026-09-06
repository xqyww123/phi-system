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
(* g4: hunt follow-ups *)

fun single_ledger n l = Symtab.make [(n, l)];

fun directions thy lref q =
  (case Exn.capture (fn () =>
      let val (lm, qm) = (match_form thy lref, match_form thy q) in
        "dir(ledger-as-pattern vs query)=" ^
          Bool.toString (Pattern.matches thy (lm, qm)) ^
        " dir(query-as-pattern vs ledger)=" ^
          Bool.toString (Pattern.matches thy (qm, lm))
      end) () of
    Exn.Res s => s
  | Exn.Exn exn => "directions EXN: " ^ Runtime.exn_message exn);

(*H8b: devarifyT injectivity attack, now with the debt REALLY over one tfree*)
val h8b_debt = rd thy0 "!!(x::'a) (y::'a). x == x ==> y == y";
val lh8b = ledger_entry thy0 h8b_debt;
val _ = writeln ("SHAPE H8b debt raw: " ^ raw_term lh8b);
val sT = ["HOL.type"];
val vu = Var (("u", 0), TFree ("'a.0", sT));
val vw = Var (("w", 0), TVar (("'a", 0), sT));
val h8b_query = Logic.mk_implies (Logic.mk_equals (vu, vu), Logic.mk_equals (vw, vw));
val _ = writeln ("SHAPE H8b match_form(query) raw: " ^
                 (case Exn.capture (fn () => raw_term (match_form thy0 h8b_query)) () of
                    Exn.Res s => s
                  | Exn.Exn exn => "EXN: " ^ Runtime.exn_message exn));
val _ = verdict "H8b" "hand-built-negative" false
          (run_bool (fn () => is_debt thy0 (single_ledger "h8b" lh8b) h8b_query))
          "expected false per design intent; a true here demonstrates the devarifyT dot-name boundary";

(*N3b: instance of a MONOMORPHIC debt -- clean one-directional case*)
val m1 = rd thy0 "!!n::nat. n + 0 = n";
val l1 = ledger_entry thy0 m1;
val n3b_prop = rd thy0 "(5::nat) + 0 = 5";
val n3b_e = real_export thy0 "n3b" n3b_prop (simp_with []);
val _ = writeln ("SHAPE N3b exported: " ^ pr_sorts thy0 n3b_e);
val _ = verdict "N3b" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "m1" l1) n3b_e))
          (directions thy0 l1 n3b_e);

(*MASS: every Spec_Rules.Unknown fact of Main -- the literal consumer input
  space -- against a 5-entry ledger; all must be false, none may raise*)
val m2 = rd thy0 "!!n m::nat. n < m ==> n <= m";
val m3 = rd thy0 "!!x y::'a::comm_monoid_add. x + y = y + x";
val m4 = rd thy0 "!!x::'a::comm_monoid_add. x = 0 ==> x + x = x";
val m5 = rd thy0 ("!!x y::'a::comm_monoid_add. !!u v::'b::comm_monoid_mult. " ^
                  "x + y = y + x & u * v = v * u");
val big = Symtab.make
  [("m1", l1), ("m2", ledger_entry thy0 m2), ("m3", ledger_entry thy0 m3),
   ("m4", ledger_entry thy0 m4), ("m5", ledger_entry thy0 m5)];

val unknown_props =
  Spec_Rules.get (ctxt_of thy0)
  |> filter (Spec_Rules.is_unknown o #rough_classification)
  |> maps (map Thm.prop_of o #rules);
val _ = writeln ("MASS: " ^ string_of_int (length unknown_props) ^
                 " Unknown spec-rule props in Main");
val mass =
  fold (fn p => fn (n_true, n_exn, msgs) =>
    (case Exn.capture (fn () => is_debt thy0 big p) () of
      Exn.Res true => (n_true + 1, n_exn, msgs)
    | Exn.Res false => (n_true, n_exn, msgs)
    | Exn.Exn exn =>
        (n_true, n_exn + 1,
         if n_exn < 3 then msgs @ [Runtime.exn_message exn] else msgs)))
    unknown_props (0, 0, []);
val _ =
  let val (n_true, n_exn, msgs) = mass in
    (writeln ("MASS: matches=" ^ string_of_int n_true ^
              " exceptions=" ^ string_of_int n_exn);
     List.app (fn m => writeln ("MASS EXN: " ^ m)) msgs;
     verdict "MASS-no-exn" "library-spec-rules" true
       (Bool.toString (n_exn = 0)) "no exceptions over the whole consumer input space";
     verdict "MASS-no-match" "library-spec-rules" true
       (Bool.toString (n_true = 0)) "no spurious ledger hit")
  end;
