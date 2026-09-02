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
(* g2: negatives N1-N8 (expected false, never an exception) *)

fun funT (a, b) = Type ("fun", [a, b]);
val boolT = Type ("HOL.bool", []);
val natT = Type ("Nat.nat", []);

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

(*the M3 debt ledger (comm_monoid_add)*)
val m3 = rd thy0 "!!x y::'a::comm_monoid_add. x + y = y + x";
val l3 = ledger_entry thy0 m3;

(*N1: same statement at a weaker sort*)
val n1_prop = rd thy0 "!!x y::'a::ab_semigroup_add. x + y = y + x";
val n1_e = real_export thy0 "n1" n1_prop (simp_with ["add.commute"]);
val _ = writeln ("SHAPE N1 exported: " ^ pr_sorts thy0 n1_e);
val _ = verdict "N1" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "m3" l3) n1_e)) "";

(*N2: library add.commute (lives at ab_semigroup_add)*)
val n2_q = Thm.prop_of (Proof_Context.get_thm (ctxt_of thy0) "add.commute");
val _ = writeln ("SHAPE N2 add.commute: " ^ pr_sorts thy0 n2_q);
val _ = verdict "N2" "library-thm" false
          (run_bool (fn () => is_debt thy0 (single_ledger "m3" l3) n2_q)) "";

(*N3: the nat INSTANCE of the debt is not the debt*)
val n3_prop = rd thy0 "!!x y::nat. x + y = y + x";
val n3_e = real_export thy0 "n3" n3_prop (simp_with ["add.commute"]);
val _ = writeln ("SHAPE N3 exported: " ^ pr_sorts thy0 n3_e);
val _ = verdict "N3" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "m3" l3) n3_e))
          (directions thy0 l3 n3_e);

(*N4: diagonal -- two distinct variables vs one variable used twice*)
val n4_two = rd thy0 "!!x y::nat. x * y = y * x";
val n4_diag = rd thy0 "!!x::nat. x * x = x * x";
val l4_two = ledger_entry thy0 n4_two;
val l4_diag = ledger_entry thy0 n4_diag;
val e4_two = real_export thy0 "n4two" n4_two (simp_with ["mult.commute"]);
val e4_diag = real_export thy0 "n4diag" n4_diag (simp_with []);
val _ = writeln ("SHAPE N4 two-var exported:  " ^ pr_sorts thy0 e4_two);
val _ = writeln ("SHAPE N4 diagonal exported: " ^ pr_sorts thy0 e4_diag);
val _ = verdict "N4a" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "two" l4_two) e4_diag))
          (directions thy0 l4_two e4_diag);
val _ = verdict "N4b" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "diag" l4_diag) e4_two))
          (directions thy0 l4_diag e4_two);

(*shared ledger of several debts for N5/N6*)
val m1 = rd thy0 "!!n::nat. n + 0 = n";
val m2 = rd thy0 "!!n m::nat. n < m ==> n <= m";
val m4 = rd thy0 "!!x::'a::comm_monoid_add. x = 0 ==> x + x = x";
val m5 = rd thy0 ("!!x y::'a::comm_monoid_add. !!u v::'b::comm_monoid_mult. " ^
                  "x + y = y + x & u * v = v * u");
val big = Symtab.make
  [("m1", ledger_entry thy0 m1), ("m2", ledger_entry thy0 m2), ("m3", l3),
   ("m4", ledger_entry thy0 m4), ("m5", ledger_entry thy0 m5)];

(*N5: hand-built specify_type bijection shape, meta-equality with schematics*)
val n5_q = Logic.mk_equals
  (Const ("Isdebt.Abs_t", funT (natT, boolT)) $
     (Const ("Isdebt.Rep_t", funT (boolT, natT)) $ Var (("x", 0), boolT)),
   Var (("x", 0), boolT));
val _ = writeln ("SHAPE N5 hand-built: " ^ pr_sorts thy0 n5_q);
val _ = verdict "N5" "hand-built-negative" false
          (run_bool (fn () => is_debt thy0 big n5_q)) "";

(*N6: a definitional equation and an arbitrary unrelated library theorem*)
val n6_def = Thm.prop_of (Proof_Context.get_thm (ctxt_of thy0) "id_def");
val n6_arb = Thm.prop_of (Proof_Context.get_thm (ctxt_of thy0) "conj_commute");
val _ = writeln ("SHAPE N6 id_def: " ^ pr_sorts thy0 n6_def);
val _ = writeln ("SHAPE N6 conj_commute: " ^ pr_sorts thy0 n6_arb);
val _ = verdict "N6-def" "library-thm" false
          (run_bool (fn () => is_debt thy0 big n6_def)) "";
val _ = verdict "N6-arb" "library-thm" false
          (run_bool (fn () => is_debt thy0 big n6_arb)) "";

(*N7: permuted premises of a 2-premise debt*)
val n7_prop = rd thy0 "!!n m::nat. n = 0 ==> m = 0 ==> n + m = 0";
val n7_perm = rd thy0 "!!n m::nat. m = 0 ==> n = 0 ==> n + m = 0";
val l7 = ledger_entry thy0 n7_prop;
val n7_e = real_export thy0 "n7" n7_prop (simp_with []);
val n7_pe = real_export thy0 "n7perm" n7_perm (simp_with []);
val _ = writeln ("SHAPE N7 exported (orig order):     " ^ pr_sorts thy0 n7_e);
val _ = writeln ("SHAPE N7 exported (permuted order): " ^ pr_sorts thy0 n7_pe);
val _ = verdict "N7-same-order" "real-export" true
          (run_bool (fn () => is_debt thy0 (single_ledger "n7" l7) n7_e))
          "order-preservation control";
val _ = verdict "N7-permuted" "real-export" false
          (run_bool (fn () => is_debt thy0 (single_ledger "n7" l7) n7_pe))
          (directions thy0 l7 n7_pe);

(*N8: after discharge -- entry deleted from the ledger*)
val m4e = real_export thy0 "m4n8" m4 (simp_with []);
val _ = verdict "N8-before" "real-export" true
          (run_bool (fn () => is_debt thy0 big m4e)) "control: entry present";
val _ = verdict "N8-after" "real-export" false
          (run_bool (fn () => is_debt thy0 (Symtab.delete_safe "m4" big) m4e))
          "entry deleted";
