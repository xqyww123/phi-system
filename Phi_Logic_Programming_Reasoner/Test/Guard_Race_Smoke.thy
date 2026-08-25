theory Guard_Race_Smoke
  imports "Phi_Logic_Programming_Reasoner.PLPR"
begin

(* Probe battery for the guard race (prove_or_refute, library/reasoners.ML);
   the T3 list of Docs/GUARD_NITPICK_FALSIFY_PLAN.md \<section>7, as revised in \<section>14.3.
   Not registered in any ROOT: evaluate on demand (e.g. via Isabelle-MCP
   under session Phi_System_Base).

   Reachability constraint (measured): the race arm runs ONLY when the
   leading 30ms quick search times out -- auto_search_tac is a TRY chain and
   otherwise always yields at least the unchanged state.  Hence every guard
   below must burn through that 30ms attempt, and must survive the pre-race
   asm_full_simp + quick_cut: the atoms below carry classical rules only,
   never a simp rule, and no guard is an equation (fast_inst's trivial-form
   channel would intercept it before the race).

   NB the helpers take the calling block's \<^context> explicitly: the
   antiquotation is static, and a helper-captured context would predate the
   construct declarations below, turning them into frees (measured trap). *)

declare [[\<phi>trace_reasoning = 3]]
(*ISABELLE_TMP, not ISABELLE_TMP_PREFIX: the prefix directory is shared by
  every Isabelle process of one user, so two frontends evaluating this theory
  at once would interleave their lines into one file and each probe's
  line-count delta would pick up the other's race.  ISABELLE_TMP is
  per-process (measured: $ISABELLE_TMP_PREFIX/process<id>).*)
declare [[\<phi>guard_race_log = "$ISABELLE_TMP/guard_race_smoke.tsv"]]

ML \<open>
(*the config is the single source of truth for the log path*)
fun log_lines ctxt =
  let val path = Path.explode (Config.get ctxt Phi_Reasoners.guard_race_log)
  in if File.exists path
     then filter (fn s => s <> "") (split_lines (File.read path))
     else []
  end

(*column projections over the 7-field TSV schema (see the guard_race_log
  signature comment in reasoners.ML).  Each probe fixes exactly the columns
  it is about, keeping the timing-dependent ones out of its assertion.*)
fun verdict_winner (_ :: v :: w :: _) = (v, w)
  | verdict_winner l = error ("malformed race log line: " ^ commas l)
fun verdict_winner_exits [_, v, w, _, _, _, x] = (v, w, x)
  | verdict_winner_exits l = error ("malformed race log line: " ^ commas l)
fun verdict_winner_mode [_, v, w, _, _, m, _] = (v, w, m)
  | verdict_winner_mode l = error ("malformed race log line: " ^ commas l)

(*one engine for every probe: drive a guard through the solver, then assert
  on the projection of the TSV line(s) THIS race appended (delta against the
  line count beforehand).  expects is the SET of acceptable outcomes: a race
  between two correct refuters is decided by timing, so more than one log
  can be legitimate for one probe.*)
fun race_test {project, can_inst} ctxt name expects t =
  let val n0 = length (log_lines ctxt)
      val st = Thm.trivial (Thm.cterm_of ctxt t)
      val (time, r) = Timing.timing (fn () =>
            Phi_Reasoners.guard_condition_solver {can_inst = can_inst} ctxt st |> Seq.pull) ()
      val new = drop n0 (log_lines ctxt)
      val observed = map (project o space_explode "\t") new
      val _ = if member (op =) expects observed then ()
              else error (name ^ ": expected one of " ^ @{make_string} expects ^
                          " but logged " ^ @{make_string} observed ^
                          (*the full lines carry the columns the projection
                            dropped, which self-explain a surprise*)
                          (if null new then " (no race logged)"
                           else "\n" ^ cat_lines (map (prefix "  ") new)))
  in writeln (name ^ ": " ^ (case r of SOME _ => "state" | NONE => "empty") ^
              " in " ^ string_of_int (Time.toMilliseconds (#elapsed time)) ^ "ms" ^
              "\n  log: " ^ (if null new then "(no race logged)" else cat_lines new))
  end

(*probe modes: `plain` fixes verdict and winner; `with_exits` also fixes the
  per-racer exit column; `with_mode` also fixes forked-vs-serial; `schematic`
  keeps the guard's ?-variables schematic and drives the can_inst = true
  branch (the one that freezes them into Frees)*)
val plain = {project = verdict_winner, can_inst = false}
val with_exits = {project = verdict_winner_exits, can_inst = false}
val with_mode = {project = verdict_winner_mode, can_inst = false}
val schematic = {project = verdict_winner, can_inst = true}

fun test opts ctxt name expects prop_str =
  race_test opts ctxt name expects
    (Syntax.read_prop
       (if #can_inst opts
        then Proof_Context.set_mode Proof_Context.mode_schematic ctxt
        else ctxt)
       prop_str)
\<close>

section \<open>Constructs\<close>

text \<open>Every guard must outlast the 30ms quick attempt.  Three ways to do
that appear here: an intro! rule that loops upward (\<open>SPIN\<close>, \<open>BLIND_SPIN\<close>), a
long chain of safe intro! steps that terminates in success (\<open>CHAIN\<close>), and a
long chain of safe elim! steps that terminates in a contradiction
(\<open>FALLS\<close>).\<close>

(* BAD: false atom invisible to simp (no simp rule), instantly eliminable by
   the classical refuter (elim!).
   SPIN: goal-side-only spinner -- the intro! rule loops upward forever, so
   PROVING `SPIN n` burns any budget, while `SPIN n` as an ASSUMPTION is
   inert (no elim rule). *)
definition BAD :: bool where "BAD = False"
lemma BAD_E[elim!]: "BAD \<Longrightarrow> P" unfolding BAD_def by simp

definition SPIN :: "nat \<Rightarrow> bool" where "SPIN n = False"
lemma SPIN_I[intro!]: "SPIN (Suc n) \<Longrightarrow> SPIN n" unfolding SPIN_def by simp

(* BADN: false atom with NO rule at all -- no simp rule, no elim rule.  The
   classical refuter cannot touch it (auto cannot unfold a bare definition),
   so R-conv comes back empty; Nitpick unfolds definitions and refutes. *)
definition BADN :: "nat \<Rightarrow> bool" where "BADN n = False"

(* BLIND_SPIN: false, yet TRUE IN EVERY FINITE MODEL, so the model refuter --
   which only ever searches finite scopes -- can never exhibit a
   countermodel and comes back empty-handed (measured: "Nitpick found no
   counterexample" in 91ms at card 1-10).  The elim! rule still kills it in
   the classical refuter in one step, and the intro! rule loops upward like
   SPIN's.  This is the construct every "R-conv must win" probe needs: with a
   Nitpick-transparent conjunct anywhere in the guard, R-nitpick refutes the
   whole guard first (measured 99-154ms) and the probe measures nothing. *)
definition BLIND_SPIN :: "nat \<Rightarrow> bool"
  where "BLIND_SPIN n = finite (UNIV::nat set)"
lemma BLIND_SPIN_E[elim!]: "BLIND_SPIN n \<Longrightarrow> P" unfolding BLIND_SPIN_def by simp
lemma BLIND_SPIN_I[intro!]: "BLIND_SPIN (Suc n) \<Longrightarrow> BLIND_SPIN n"
  unfolding BLIND_SPIN_def by simp

(* CHAIN: provable, but only after one safe intro! step per list element --
   a tunable amount of successful search.  True by definition, so the model
   refuter finds nothing either. *)
definition CHAIN :: "nat list \<Rightarrow> bool" where "CHAIN xs = True"
lemma CHAIN_nil[intro!]: "CHAIN []" unfolding CHAIN_def by simp
lemma CHAIN_cons[intro!]: "CHAIN xs \<Longrightarrow> CHAIN (x # xs)" unfolding CHAIN_def by simp

(* FALLS: false, and refuted only after one safe elim! step per list element
   -- a tunable amount of search before the contradiction shows up.  Used as
   a HYPOTHESIS, it makes a guard vacuous the slow way. *)
definition FALLS :: "nat list \<Rightarrow> bool" where "FALLS xs = False"
lemma FALLS_nil[elim!]: "FALLS [] \<Longrightarrow> P" unfolding FALLS_def by simp
lemma FALLS_cons[elim!]: "FALLS (x # xs) \<Longrightarrow> (FALLS xs \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding FALLS_def by simp

(* SOMETRUE: true for exactly one argument, with an intro! rule that supplies
   that argument.  As a guard with a schematic variable it is provable BY
   INSTANTIATION and must therefore never be refuted. *)
definition SOMETRUE :: "nat \<Rightarrow> bool" where "SOMETRUE n = (n = 0)"
lemma SOMETRUE_I[intro!]: "SOMETRUE 0" unfolding SOMETRUE_def by simp

(* BADT: BAD with a type argument, the carrier for a schematic TYPE variable. *)
definition BADT :: "'a \<Rightarrow> bool" where "BADT x = False"
lemma BADT_E[elim!]: "BADT x \<Longrightarrow> P" unfolding BADT_def by simp

ML \<open>(*chain lengths, tuned by measurement: each must outlast the 30ms quick
  attempt and still finish well inside the 500ms race budget.  CHAIN's
  intro! search is superlinear (400 elements stay under 30ms and the race is
  never entered, 2000 blow the budget, 1000 = 126ms); FALLS's elim! walk is
  linear (400 = 33ms, 800 = 99ms).*)
fun chain_list n = "[" ^ commas (map string_of_int (1 upto n)) ^ "]"
val intro_chain = chain_list 1000
val elim_chain = chain_list 800\<close>

section \<open>Probes\<close>

ML \<open>test plain \<^context> "control (fast partial search, race NOT entered)" [[]]
  "\<condition> (\<forall>x::nat. \<exists>y. y * y \<le> x \<and> x < (y+1) * (y+1))"\<close>

(*NB the 'a here is read as a FIXED TFree (read_prop fixes it), so the
  R-nitpick racer is present and correctly returns none under the sound
  universal reading of TFrees (measured: exits show R-nitpick1:none).
  The TVar screen is probed separately below, on an ML-built term.*)
ML \<open>test plain \<^context> "undecided (search bomb -> race -> fail exit)" [[("undecided", "-")]]
  "\<condition> (((\<exists>x. \<forall>y. p x = p (y::'a)) = ((\<exists>x. q x) = (\<forall>y. p y))) = ((\<exists>x. \<forall>y. q x = q y) = ((\<exists>x. p x) = (\<forall>y. q (y::'a)))))"\<close>

(*BAD & SPIN is refutable by BOTH refuters: R-conv proves the negation in
  milliseconds but may only relay post-race (P-auto must finish first),
  while a genuine Nitpick model ends the race directly (~100ms measured).
  Which one the log shows is a timing race between two correct verdicts --
  both are accepted; without a Scala peer R-nitpick comes back
  empty-handed and only the R-conv outcome remains.*)
ML \<open>test plain \<^context> "false BAD&SPIN (attempt spins -> refuted by either refuter)"
  [[("refuted", "R-nitpick1")], [("refuted", "R-conv")]]
  "\<condition> (BAD \<and> SPIN 0)"\<close>

(*T3-1: ground false guard -- the model refuter is the only one that can
  see through BADN, and its win must short-circuit the field.  The exits
  column is the short-circuit evidence: P-auto is cancelled mid-spin, and
  R-conv (which cannot touch a bare definition) has already given up.
  Requires a Scala peer.*)
ML \<open>test with_exits \<^context> "T3-1 ground false guard (model refuter wins, field short-circuited)"
  [[("refuted", "R-nitpick1", "P-auto:cancelled,R-conv:none,R-nitpick1:win")]]
  "\<condition> (BADN 0 \<and> SPIN 0)"\<close>

(*T3-2: a guard that IS provable, just not within the 30ms quick attempt.
  P-auto must win it, and neither refuter may interfere.*)
ML \<open>test plain \<^context> "T3-2 provable but slow (P-auto wins)"
  [[("proved", "P-auto")]]
  ("\<condition> (CHAIN " ^ intro_chain ^ ")")\<close>

(*T3-3: vacuous hypothesis.  FALLS ... is contradictory, so BOTH `H \<Longrightarrow> C`
  and `H \<Longrightarrow> \<not>C` are provable; the design (plan \<section>2.2) says the classical
  refuter must never steal such a guard, because its refutation is only
  read when the race as a whole came back empty.  Expected: proved by
  P-auto, exactly as if no refuter existed.*)
ML \<open>test plain \<^context> "T3-3 vacuous hypothesis (proved by P-auto, not stolen)"
  [[("proved", "P-auto")]]
  ("FALLS " ^ elim_chain ^ " \<Longrightarrow> \<condition> (SPIN 0)")\<close>

(*T3-4a: can_inst = true and SOME instantiation is provable.  Neither
  refuter may kill it: R-conv freezes ?x into a Free and fails to prove the
  negation, and R-nitpick's falsify closes residual Vars universally, so a
  countermodel would have to refute EVERY instantiation.  The latter is the
  claim worth measuring -- SOMETRUE ?x is false for all but one value, so a
  per-instance reading would refute here; the exits column says
  R-nitpick1:none.  CHAIN is there only to outlast the quick attempt.*)
ML \<open>test schematic \<^context> "T3-4a instantiable guard, some instance provable (not killed)"
  [[("proved", "P-auto")]]
  ("\<condition> (CHAIN " ^ intro_chain ^ " \<and> SOMETRUE ?x)")\<close>

(*T3-4b: the control -- every instantiation false.  BLIND_SPIN keeps the
  model refuter out of it, so this probe pins the frozen-Free path of
  R-conv (the N1 ruling) rather than a Nitpick model.*)
ML \<open>test schematic \<^context> "T3-4b instantiable guard, every instance false (refuted by R-conv)"
  [[("refuted", "R-conv")]]
  "\<condition> (BLIND_SPIN ?x)"\<close>

(*the blind spinner on its own: the only refuter that can win is R-conv,
  and it wins post-race, after P-auto has burnt the whole budget.*)
ML \<open>test with_exits \<^context> "blind spinner (only the classical refuter can win)"
  [[("refuted", "R-conv", "P-auto:timeout,R-conv:none,R-nitpick1:none")]]
  "\<condition> (BLIND_SPIN 0)"\<close>

(*T3-5: a schematic TYPE variable silences the whole R-nitpick family (no
  monotonization -- substituting a typical type would be unsound).  The
  evidence is the exits column: R-nitpick must not appear at all, which is
  different from appearing with a `none` exit.  Nothing in the surface
  syntax produces a schematic ?'a (read_prop FIXES type variables), hence
  the term surgery.*)
ML \<open>
let val t = Syntax.read_prop \<^context> "\<condition> (BADT (undefined::'a) \<and> SPIN 0)"
    val t' = Term.map_types (Term.map_atyps
               (fn TFree (a, S) => TVar ((a, 0), S) | T => T)) t
 in race_test with_exits \<^context>
      "T3-5 schematic type variable (model refuter absent from the table)"
      [[("refuted", "R-conv", "P-auto:timeout,R-conv:none")]] t'
end\<close>

(*T3-7: the engine degrades to serial when the process has no spare
  threads; the verdict must not depend on that.  Flipping the global thread
  count is the only switch there is, so it is restored on every exit path.*)
ML \<open>
let val old = Multithreading.max_threads ()
    val _ = Multithreading.max_threads_update 1
    val res = Exn.capture_body (fn () =>
      test with_mode \<^context> "T3-7 serial degradation (same verdict as forked)"
        [[("refuted", "R-conv", "serial")]]
        "\<condition> (BLIND_SPIN 0)")
    val _ = Multithreading.max_threads_update old
 in Exn.release res end\<close>

(*T3-6: pollution immunity.  Everything set below would break the racer if
  the pinned parameter list (pinned_nitpick_params) did not override it:
  `expect` would raise on the genuine outcome (a Crashed exit), the 1ms
  timeout would abort the search, card 1-1 would shrink the scope, and
  verbose would break silence.  Kept LAST in the theory because it changes
  theory-level defaults for everything after it.*)
nitpick_params [expect = unknown, timeout = 0.001, card = 1-1,
                max_potential = 5, verbose]

ML \<open>test with_exits \<^context> "T3-6 nitpick_params pollution immunity"
  [[("refuted", "R-nitpick1", "P-auto:cancelled,R-conv:none,R-nitpick1:win")]]
  "\<condition> (BADN 0 \<and> SPIN 0)"\<close>

end
