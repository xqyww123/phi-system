(* common.ML — shared harness for verifying the FIXED Debt_Axiom discharge recipe *)

val thy = Thy_Info.get_theory "Main"
  handle ERROR _ => Thy_Info.get_theory "HOL.Main";
val ctxt = Proof_Context.init_global thy;
val ctxt_s = Config.put show_sorts true ctxt;
fun pr s = writeln ("### " ^ s);
fun prts th = writeln (Thm.string_of_thm ctxt_s th);
fun prtm t = writeln (Syntax.string_of_term ctxt_s t);

(* local term-building helpers (no antiquotations in raw ML; HOLogic not in scope) *)
val boolT = Type ("HOL.bool", []);
fun mk_Trueprop t = Const ("HOL.Trueprop", boolT --> propT) $ t;
fun mk_eq T a b = Const ("HOL.eq", T --> T --> boolT) $ a $ b;
fun mk_conj a b = Const ("HOL.conj", boolT --> boolT --> boolT) $ a $ b;
fun mk_plus T a b = Const ("Groups.plus_class.plus", T --> T --> T) $ a $ b;
fun mk_times T a b = Const ("Groups.times_class.times", T --> T --> T) $ a $ b;

val S_cma = Syntax.read_sort ctxt "comm_monoid_add";
val S_cmm = Syntax.read_sort ctxt "comm_monoid_mult";
val S_asa = Syntax.read_sort ctxt "ab_semigroup_add";
val S_asm = Syntax.read_sort ctxt "ab_semigroup_mult";
val _ = pr ("sorts: cma=" ^ commas S_cma ^ " cmm=" ^ commas S_cmm ^
            " asa=" ^ commas S_asa ^ " asm=" ^ commas S_asm);

(* verbatim copy of contrib/phi-system/Debt_Axiom/Debt_Axiom.ML lines 37-46 *)
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

(* the ledger normal form of a debt proposition, as in add_debt_axiom *)
fun ledger thy prop =
  let
    val (strip, _, prop') = stripped_sorts thy prop;
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
  in Logic.list_implies (maps Logic.mk_of_sort constraints, prop') end;

(*** the FIXED design under test (verbatim from the task) ***)

fun classrel_bridges thy ax rules =
  let
    val debt_sorts =
      Logic.strip_imp_prems ax
      |> map_filter (try Logic.dest_of_class)
      |> AList.group (op =)
    val wanted =
      maps (Logic.strip_imp_prems o Thm.prop_of) rules
      |> map_filter (try Logic.dest_of_class)
      |> map snd |> distinct (op =)
    fun pin T bridge =
      (case Term.add_tvars (Thm.prop_of bridge) [] of
         [tv] => Thm.instantiate
                   (TVars.make [(tv, Thm.global_ctyp_of thy T)], Vars.empty) bridge
       | _ => raise THM ("classrel_bridges: unexpected bridge shape", 0, [bridge]))
  in
    maps (fn (T, S) =>
      map_filter (fn c =>
        Option.map (pin T)
          (try (fn () =>
             Thm.unconstrainT (Thm.of_class
               (Thm.global_ctyp_of thy (TVar (("'x", 0), S)), c))) ())) wanted)
      debt_sorts
  end;

fun close_tac ctxt bridges =
  ALLGOALS (TRY o (assume_tac ctxt ORELSE'
                   (resolve_tac ctxt bridges THEN_ALL_NEW assume_tac ctxt)));

fun discharge_tac ctxt rules bridges =
  HEADGOAL (resolve_tac ctxt rules) THEN close_tac ctxt bridges;

(*** contrast variants ***)

(* same generator with pin replaced by identity (the D1 defect) *)
fun classrel_bridges_unpinned thy ax rules =
  let
    val debt_sorts =
      Logic.strip_imp_prems ax
      |> map_filter (try Logic.dest_of_class)
      |> AList.group (op =)
    val wanted =
      maps (Logic.strip_imp_prems o Thm.prop_of) rules
      |> map_filter (try Logic.dest_of_class)
      |> map snd |> distinct (op =)
  in
    maps (fn (_, S) =>
      map_filter (fn c =>
        try (fn () =>
           Thm.unconstrainT (Thm.of_class
             (Thm.global_ctyp_of thy (TVar (("'x", 0), S)), c))) ()) wanted)
      debt_sorts
  end;

(* the OLD unbounded closing tail (the D2 defect) *)
fun old_close_tac ctxt bridges =
  ALLGOALS (TRY o REPEAT_ALL_NEW (assume_tac ctxt ORELSE' resolve_tac ctxt bridges));

fun old_discharge_tac ctxt rules bridges =
  HEADGOAL (resolve_tac ctxt rules) THEN old_close_tac ctxt bridges;

(* standalone bridge construction + pinning, for manufactured bridge lists *)
fun mk_bridge thy S c =
  Thm.unconstrainT (Thm.of_class (Thm.global_ctyp_of thy (TVar (("'x", 0), S)), c));

fun pin_bridge thy T bridge =
  (case Term.add_tvars (Thm.prop_of bridge) [] of
     [tv] => Thm.instantiate (TVars.make [(tv, Thm.global_ctyp_of thy T)], Vars.empty) bridge
   | _ => raise THM ("pin_bridge: unexpected bridge shape", 0, [bridge]));

(*** reporting / execution harness ***)

fun report_bridges name bridges =
  (pr (name ^ ": " ^ string_of_int (length bridges) ^ " bridge(s)");
   List.app (fn b =>
     let
       val p = Thm.prop_of b;
       val tvs = Term.add_tvars p [];
       val tfs = Term.add_tfrees p [];
     in
       (prts b;
        pr ("    schematic tvars: " ^ string_of_int (length tvs) ^
            "; fixed tfrees: [" ^ commas (map #1 tfs) ^ "]"))
     end) bridges);

fun run_case name goal_term tac =
  let
    val start = Time.now ();
    val result =
      Exn.capture (fn () =>
        Timeout.apply (Time.fromSeconds 10) (fn () =>
          Goal.prove_internal ctxt [] (Thm.global_cterm_of thy goal_term)
            (fn _ => tac)) ()) ();
    val ms = string_of_int (Time.toMilliseconds (Time.- (Time.now (), start))) ^ "ms";
  in
    (case result of
       Exn.Res th =>
         (pr (name ^ " => PROVED [" ^ ms ^ "]; exact aconv goal_term = " ^
              Bool.toString (Thm.full_prop_of th aconv goal_term));
          prts th)
     | Exn.Exn (Timeout.TIMEOUT t) =>
         pr (name ^ " => Timeout.TIMEOUT [" ^ ms ^ "] (limit " ^ Time.toString t ^ "s)")
     | Exn.Exn exn =>
         pr (name ^ " => FAILED [" ^ ms ^ "]: " ^ Runtime.exn_message exn))
  end;

fun prove_cert name prop tac =
  let val th = Goal.prove ctxt [] [] prop (fn _ => tac)
  in (pr (name ^ " proved:"); prts th; th) end;

(* the ⋀x y. x + y = y + x statement at a given type *)
fun comm_statement T =
  let
    val x = Free ("x", T); val y = Free ("y", T);
  in fold_rev Logic.all [x, y] (mk_Trueprop (mk_eq T (mk_plus T x y) (mk_plus T y x))) end;
