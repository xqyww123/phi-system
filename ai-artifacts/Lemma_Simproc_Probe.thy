theory Lemma_Simproc_Probe
  imports Main
begin

section \<open>Test constants and the three lemma shapes\<close>

axiomatization f g h k :: "nat \<Rightarrow> nat" and p :: "nat \<Rightarrow> bool" where
  fg: "f x = g x" and
  hk: "x \<noteq> 0 \<Longrightarrow> h x = k x" and
  pp: "p x" and
  gg: "g x = g (g x)"

section \<open>Context-local budget state\<close>

ML \<open>
(* the count/budget lives in a Proof_Data slot; the ref makes it writable from
   inside a simproc, which cannot thread a context back out *)
structure Budget = Proof_Data (
  type T = (int * int Unsynchronized.ref) Symtab.table;
  fun init _ = Symtab.empty
);

fun set_budget (name, n) = Budget.map (Symtab.update (name, (n, Unsynchronized.ref 0)));

fun budget_count ctxt name =
  (case Symtab.lookup (Budget.get ctxt) name of SOME (_, r) => ! r | NONE => ~1);

fun spend ctxt name =
  (case Symtab.lookup (Budget.get ctxt) name of
    NONE => false
  | SOME (lim, r) => if ! r >= lim then false else (r := ! r + 1; true));
\<close>

section \<open>Clone of the simplifier's internal premise prover\<close>

ML \<open>
(* simplifier.ML:330-338 -- solve_all_tac is NOT exported, so we rebuild it *)
fun solve_all_tac solvers ctxt =
  let
    val subgoal_tac = Raw_Simplifier.subgoal_tac (Raw_Simplifier.set_solvers solvers ctxt);
    val solve_tac = subgoal_tac THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE (solve_tac 1) end;

fun internal_prover ctxt th =
  let val (unsafe_solvers, _) = Raw_Simplifier.solvers ctxt
  in Option.map #1 (Seq.pull (solve_all_tac (rev unsafe_solvers) ctxt th)) end;
\<close>

section \<open>Lemma-as-simproc\<close>

ML \<open>
(* like decomp_simp, raw_simplifier.ML:540-551 *)
fun rule_elhs rule =
  let
    val concl = Drule.strip_imp_concl (Thm.cprop_of rule);
    val (lhs, _) = Thm.dest_equals concl;
  in Thm.dest_arg (Thm.cprop_of (Thm.eta_conversion lhs)) end;

(* like rew, raw_simplifier.ML:1035-1046 *)
fun inst_rule ct rule =
  let
    val rule1 = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule;
    val elhs = rule_elhs rule1;
    val t = Thm.term_of elhs;
    val fo = Pattern.first_order t orelse not (Pattern.pattern t);
    val insts = (if fo then Thm.first_order_match else Thm.match) (elhs, ct);
  in SOME (Thm.instantiate insts (Thm.rename_boundvars t (Thm.term_of ct) rule1)) end
  handle Pattern.MATCH => NONE;

(* Self:  discharge premises inside the simproc (recursive simplifier call)
   Deleg: hand the conditional instance back, let rewritec's own prover do it *)
datatype pmode = Self | Deleg;

fun lemma_proc mode name rules0 _ ctxt ct =
  let
    val rules = map (Thm.transfer' ctxt) rules0;
    fun attempt [] = NONE
      | attempt (r :: rs) =
          (case inst_rule ct r of
            NONE => attempt rs
          | SOME inst =>
              let
                val res =
                  if Thm.nprems_of inst = 0 then SOME inst
                  else
                    (case mode of
                      Deleg => SOME inst
                    | Self => internal_prover ctxt inst);
              in
                (case res of
                  NONE => attempt rs
                | SOME th => if spend ctxt name then SOME th else NONE)
              end);
  in attempt rules end;

fun lemma_simproc mode ctxt (name, lemma) =
  let val rules = map Thm.trim_context (Simplifier.mksimps ctxt lemma) in
    Simplifier.make_simproc ctxt
     {name = name,
      kind = Simplifier.Simproc,
      lhss = map (Thm.term_of o rule_elhs o Thm.transfer' ctxt) rules,
      proc = lemma_proc mode name rules,
      identifier = []}
  end;

fun add_lemma_simproc mode (name, lemma, budget) ctxt =
  ctxt
  |> set_budget (name, budget)
  |> Raw_Simplifier.add_proc (lemma_simproc mode ctxt (name, lemma));

(* every measurement is timeout-guarded: some of these rewrites diverge *)
fun show ctxt ct =
  Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of (Simplifier.rewrite ctxt ct)));

fun try_show ctxt ct =
  Timeout.apply (seconds 2.0) (fn () => show ctxt ct) ()
    handle Timeout.TIMEOUT _ => "<<DIVERGED: killed after 2s>>";

fun run tag ctxt name ct =
  writeln (tag ^ "  " ^ Syntax.string_of_term ctxt (Thm.term_of ct) ^ "  ==>  " ^
    try_show ctxt ct ^
    (if name = "" then "" else "   [count " ^ string_of_int (budget_count ctxt name) ^ "]"));
\<close>

section \<open>What mksimps makes of each lemma\<close>

ML \<open>
val ctxt0 = @{context};
val _ = writeln ("mksimps fg = " ^ @{make_string} (Simplifier.mksimps ctxt0 @{thm fg}));
val _ = writeln ("mksimps hk = " ^ @{make_string} (Simplifier.mksimps ctxt0 @{thm hk}));
val _ = writeln ("mksimps pp = " ^ @{make_string} (Simplifier.mksimps ctxt0 @{thm pp}));
val _ = writeln ("mksimps gg = " ^ @{make_string} (Simplifier.mksimps ctxt0 @{thm gg}));
\<close>

section \<open>(i) the lemmas as ordinary simp rules\<close>

ML \<open>
val ctxt0 = @{context};
val c_fg_r = Raw_Simplifier.add_simps [@{thm fg}] ctxt0;
val c_hk_r = Raw_Simplifier.add_simps [@{thm hk}] ctxt0;
val c_pp_r = Raw_Simplifier.add_simps [@{thm pp}] ctxt0;
val _ = run "RULE" c_fg_r "" @{cterm "f 5"};
val _ = run "RULE" c_fg_r "" @{cterm "f 1 + f 2 + f 3"};
val _ = run "RULE" c_hk_r "" @{cterm "h 3"};
val _ = run "RULE" c_hk_r "" @{cterm "h 0"};
val _ = run "RULE" c_pp_r "" @{cterm "p 7"};
\<close>

ML \<open>
(* the looping lemma as a plain simp rule: mk_rrule does NOT reorient it *)
val ctxt0 = @{context};
val c_gg_r = Raw_Simplifier.add_simps [@{thm gg}] ctxt0;
val _ = writeln ("rrules of gg = " ^ @{make_string} (map #2 (Raw_Simplifier.dest_simps
          (Raw_Simplifier.simpset_of (Raw_Simplifier.clear_simpset ctxt0
             |> Raw_Simplifier.add_simps [@{thm gg}])))));
val _ = run "RULE" c_gg_r "" @{cterm "g 1"};
\<close>

section \<open>(ii) the same lemmas as budgeted simprocs\<close>

ML \<open>
val ctxt0 = @{context};
val c_fg_p = add_lemma_simproc Self ("fg", @{thm fg}, 100) ctxt0;
val c_hk_p = add_lemma_simproc Self ("hk", @{thm hk}, 100) ctxt0;
val c_pp_p = add_lemma_simproc Self ("pp", @{thm pp}, 100) ctxt0;
val _ = run "PROC" c_fg_p "fg" @{cterm "f 5"};
val _ = run "PROC" c_fg_p "fg" @{cterm "f 1 + f 2 + f 3"};
val _ = run "PROC" c_hk_p "hk" @{cterm "h 3"};
val _ = run "PROC" c_hk_p "hk" @{cterm "h 0"};
val _ = run "PROC" c_pp_p "pp" @{cterm "p 7"};
\<close>

ML \<open>
(* (ii-b) conditional lemma: hand the conditional instance back and let
   rewritec's own prover discharge the premise *)
val ctxt0 = @{context};
val c_hk_d = add_lemma_simproc Deleg ("hk", @{thm hk}, 100) ctxt0;
val _ = run "DELEG" c_hk_d "hk" @{cterm "h 3"};
val _ = run "DELEG" c_hk_d "hk" @{cterm "h 0"};
\<close>

section \<open>Budget cut-off on the looping lemma\<close>

ML \<open>
val ctxt0 = @{context};
val _ = run "PROC(budget 3)" (add_lemma_simproc Self ("gg", @{thm gg}, 3) ctxt0) "gg" @{cterm "g 1"};
val _ = run "PROC(budget 8)" (add_lemma_simproc Self ("gg", @{thm gg}, 8) ctxt0) "gg" @{cterm "g 1"};
val c_gg_inf = add_lemma_simproc Self ("gg", @{thm gg}, 1000000000) ctxt0;
val _ = run "PROC(budget 10^9)" c_gg_inf "gg" @{cterm "g 1"};
val _ = writeln ("  applications before the 2s kill: " ^ string_of_int (budget_count c_gg_inf "gg"));
\<close>

section \<open>Cost: rrule match vs simproc call\<close>

ML \<open>
val ctxt0 = @{context};
val big = @{cterm "f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10"};
val c_r = Raw_Simplifier.add_simps [@{thm fg}] ctxt0;
val c_p = add_lemma_simproc Self ("fg", @{thm fg}, 1000000000) ctxt0;
fun rep n ctxt = funpow n (fn () => (Simplifier.rewrite ctxt big; ())) ();
val _ = rep 30 c_r;
val _ = rep 30 c_p;
val t1 = #1 (Timing.timing (fn () => rep 300 c_r) ());
val t2 = #1 (Timing.timing (fn () => rep 300 c_p) ());
val _ = writeln ("RULE 300 x 10 redexes: " ^ Timing.message t1);
val _ = writeln ("PROC 300 x 10 redexes: " ^ Timing.message t2);
\<close>

section \<open>Try order: rewrite rule and simproc for the same redex\<close>

ML \<open>
val ctxt0 = @{context};
val c_both = ctxt0
  |> Raw_Simplifier.add_simps [@{thm fg}]
  |> add_lemma_simproc Self ("fg2", @{thm fg}, 100);
val _ = run "BOTH" c_both "fg2" @{cterm "f 5"};
\<close>

end
