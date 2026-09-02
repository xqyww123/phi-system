(* common.ML — shared prelude for verifying the subgoal-directed closing step *)

val thy0 = Thy_Info.get_theory "Main";
val ctxt0 = Proof_Context.init_global thy0;


(** ledger normal form, per Debt_Axiom.ML **)

(*copied verbatim from Debt_Axiom.ML lines 37-46*)
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

fun ledger_form thy prop =
  let
    val (strip, _, prop') = stripped_sorts thy prop;
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
  in Logic.list_implies (maps Logic.mk_of_sort constraints, prop') end;


(** the subgoal-directed closer under test — verbatim from the design sketch **)

fun ofclass_close_tac ctxt = SUBGOAL (fn (sg, i) =>
  let
    val thy = Proof_Context.theory_of ctxt
    val concl = Logic.strip_assums_concl sg
    val hyps = Logic.strip_assums_hyp sg
    val cs = map_filter (try Logic.dest_of_class) hyps
    fun sort_of a = map snd (filter (fn (T, _) => T = TFree (a, [])) cs)
    val (T, c) = Logic.dest_of_class concl
    val T' = T |> Term.map_atyps
          (fn TFree (a, []) => TVar ((a, 0), sort_of a) | A => A)
    val rule = Thm.unconstrainT (Thm.of_class (Thm.global_ctyp_of thy T', c))
  in (resolve_tac ctxt [rule] THEN_ALL_NEW assume_tac ctxt) i end
  handle TERM _ => no_tac | THM _ => no_tac | TYPE _ => no_tac);

fun discharge_tac ctxt rules =
  HEADGOAL (resolve_tac ctxt rules)
  THEN ALLGOALS (TRY o (assume_tac ctxt ORELSE' ofclass_close_tac ctxt));

fun prep_cert cert = Thm.unconstrainT (Thm.varifyT_global cert);


(** harness **)

datatype outcome = PROVED of bool (*exact aconv*) | FAILED of string;

fun show (PROVED true) = "PROVED (exact aconv: yes)"
  | show (PROVED false) = "PROVED (exact aconv: NO - MISMATCH!)"
  | show (FAILED s) = "FAILED [" ^ s ^ "]";

fun run_prove goal_term tac =
  let val ct = Thm.global_cterm_of thy0 goal_term in
    PROVED (Thm.full_prop_of
              (Timeout.apply (Time.fromSeconds 10)
                 (Goal.prove_internal ctxt0 [] ct) (K tac))
            aconv goal_term)
  end
  handle Timeout.TIMEOUT _ => FAILED "TIMEOUT"
       | ERROR msg => FAILED ("ERROR: " ^ msg)
       | THM (msg, _, _) => FAILED ("THM: " ^ msg)
       | TERM (msg, _) => FAILED ("TERM: " ^ msg)
       | TYPE (msg, _, _) => FAILED ("TYPE: " ^ msg);

fun residue goal_term tac =
  let val st0 = Goal.init (Thm.global_cterm_of thy0 goal_term) in
    (case Timeout.apply (Time.fromSeconds 10) (SINGLE tac) st0 of
       NONE => "  new-recipe residue: tactic yielded no result (no_tac)"
     | SOME st =>
         "  new-recipe residue (" ^ string_of_int (Thm.nprems_of st) ^ " subgoals):\n" ^
         Pretty.string_of (Pretty.chunks (Goal_Display.pretty_goals ctxt0 st)))
    handle Timeout.TIMEOUT _ => "  residue probe TIMEOUT"
  end;

fun rp s = Syntax.read_prop ctxt0 s;

fun prove_cert prop_str tac_fn =
  Goal.prove ctxt0 [] [] (rp prop_str)
    (fn {context = goal_ctxt, ...} => tac_fn goal_ctxt);

(*run one positive/negative case: debt prop (pre-ledger) + certificate thm; both recipes*)
fun case_run name debt_prop cert =
  let
    val goal_term = ledger_form thy0 debt_prop;
    val _ = writeln ("== CASE " ^ name);
    val _ = writeln ("  ledger goal: " ^ Syntax.string_of_term ctxt0 goal_term);
    val prod = run_prove goal_term (Tactic.ares_tac ctxt0 [cert] 1);
    val newr =
      (case (SOME (prep_cert cert)
             handle THM (msg, _, _) => (writeln ("  prep_cert THM error: " ^ msg); NONE)) of
         NONE => FAILED "prep_cert failed"
       | SOME cert' => run_prove goal_term (discharge_tac ctxt0 [cert']));
    val _ = writeln ("  production ares_tac: " ^ show prod);
    val _ = writeln ("  new recipe:          " ^ show newr);
    val _ =
      (case newr of
         FAILED _ =>
           writeln (residue goal_term (discharge_tac ctxt0 [prep_cert cert]))
       | _ => ());
  in () end;

(*variant that takes an already-built ledger goal term (for hand-built goals, e.g. N-c)*)
fun case_run_goal name goal_term cert =
  let
    val _ = writeln ("== CASE " ^ name);
    val _ = writeln ("  ledger goal: " ^ Syntax.string_of_term ctxt0 goal_term);
    val prod = run_prove goal_term (Tactic.ares_tac ctxt0 [cert] 1);
    val newr = run_prove goal_term (discharge_tac ctxt0 [prep_cert cert]);
    val _ = writeln ("  production ares_tac: " ^ show prod);
    val _ = writeln ("  new recipe:          " ^ show newr);
    val _ =
      (case newr of
         FAILED _ =>
           writeln (residue goal_term (discharge_tac ctxt0 [prep_cert cert]))
       | _ => ());
  in () end;
