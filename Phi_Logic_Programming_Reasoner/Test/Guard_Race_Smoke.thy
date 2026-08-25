theory Guard_Race_Smoke
  imports "Phi_Logic_Programming_Reasoner.PLPR"
begin

(* Smoke battery for the guard race (prove_or_refute, library/reasoners.ML)
   and seed of the T3 probe battery (Docs/GUARD_NITPICK_FALSIFY_PLAN.md \<section>7).
   Not registered in any ROOT: evaluate on demand (e.g. via Isabelle-MCP
   under session Phi_System_Base).

   Reachability constraint (measured): the race arm runs ONLY when the
   leading 30ms quick search times out -- auto_search_tac is a TRY chain and
   otherwise always yields at least the unchanged state.  Hence every test
   guard below must burn through the 30ms attempt.

   NB the test helper takes the calling block's \<^context> explicitly: the
   antiquotation is static, and a helper-captured context would predate the
   BAD/SPIN declarations below, turning them into frees (measured trap). *)

declare [[\<phi>trace_reasoning = 3]]
declare [[\<phi>guard_race_log = "$ISABELLE_TMP_PREFIX/guard_race_smoke.tsv"]]

ML \<open>
(*the config is the single source of truth for the log path; each test
  asserts on the (verdict, winner) columns of the TSV lines its race
  appended (delta against the line count beforehand; 7-field schema, see
  the guard_race_log signature comment in reasoners.ML)*)
fun log_lines ctxt =
  let val path = Path.explode (Config.get ctxt Phi_Reasoners.guard_race_log)
  in if File.exists path
     then filter (fn s => s <> "") (split_lines (File.read path))
     else []
  end
fun test ctxt name expects prop_str =
  let val n0 = length (log_lines ctxt)
      val st = Thm.trivial (Thm.cterm_of ctxt (Syntax.read_prop ctxt prop_str))
      val (t, r) = Timing.timing (fn () =>
            Phi_Reasoners.guard_condition_solver {can_inst = false} ctxt st |> Seq.pull) ()
      val new = drop n0 (log_lines ctxt)
      val observed = map (fn line =>
            case space_explode "\t" line of
              _ :: verdict :: winner :: _ => (verdict, winner)
            | _ => error (name ^ ": malformed log line: " ^ line)) new
      (*expects = the set of acceptable outcomes: a race between two
        correct refuters is decided by timing, so more than one log can
        be legitimate for one test*)
      val _ = if member (op =) expects observed then ()
              else error (name ^ ": expected one of " ^ @{make_string} expects ^
                          " but logged " ^ @{make_string} observed)
  in writeln (name ^ ": " ^ (case r of SOME _ => "state" | NONE => "empty") ^
              " in " ^ string_of_int (Time.toMilliseconds (#elapsed t)) ^ "ms" ^
              "\n  log: " ^ (if null new then "(no race logged)" else cat_lines new))
  end
\<close>

(* BAD: false atom invisible to simp (no simp rule), instantly eliminable by
   the classical refuter (elim!, placed FIRST in the conjunction so the
   eliminator meets it before the spinner).
   SPIN: goal-side-only spinner -- the intro! rule loops upward forever, so
   PROVING `SPIN n` burns any budget (guaranteeing the 30ms attempt and
   P-auto both time out), while `SPIN n` as an ASSUMPTION is inert (no elim
   rule). *)
definition BAD :: bool where "BAD = False"
lemma BAD_E[elim!]: "BAD \<Longrightarrow> P" unfolding BAD_def by simp

definition SPIN :: "nat \<Rightarrow> bool" where "SPIN n = False"
lemma SPIN_I[intro!]: "SPIN (Suc n) \<Longrightarrow> SPIN n" unfolding SPIN_def by simp

ML \<open>test \<^context> "control (fast partial search, race NOT entered)" [[]]
  "\<condition> (\<forall>x::nat. \<exists>y. y * y \<le> x \<and> x < (y+1) * (y+1))"\<close>

(*NB the 'a here is read as a FIXED TFree (read_prop fixes it), so the
  R-nitpick racer is present and correctly returns none under the sound
  universal reading of TFrees (measured: exits show R-nitpick1:none).
  The TVar silencing triggers only on genuine schematic ?'a, which needs
  an ML-constructed goal -- a T3 probe item.*)
ML \<open>test \<^context> "undecided (search bomb -> race -> fail exit)" [[("undecided", "-")]]
  "\<condition> (((\<exists>x. \<forall>y. p x = p (y::'a)) = ((\<exists>x. q x) = (\<forall>y. p y))) = ((\<exists>x. \<forall>y. q x = q y) = ((\<exists>x. p x) = (\<forall>y. q (y::'a)))))"\<close>

(*BAD & SPIN is refutable by BOTH refuters: R-conv proves the negation in
  milliseconds but may only relay post-race (P-auto must finish first),
  while a genuine Nitpick model ends the race directly (~100ms measured).
  Which one the log shows is a timing race between two correct verdicts --
  both are accepted; absent the Scala peer only the R-conv line occurs.*)
ML \<open>test \<^context> "false BAD&SPIN (attempt spins -> refuted by either refuter)"
  [[("refuted", "R-nitpick1")], [("refuted", "R-conv")]]
  "\<condition> (BAD \<and> SPIN 0)"\<close>

(* BADN: false atom with NO rule at all -- no simp rule, no elim rule.
   The classical refuter cannot touch it (auto cannot unfold a bare
   definition), so R-conv comes back empty; Nitpick unfolds definitions
   and refutes.  This is the test that only R-nitpick can win. *)
definition BADN :: "nat \<Rightarrow> bool" where "BADN n = False"

ML \<open>test \<^context> "false BADN&SPIN (only the model refuter can see it)"
  [[("refuted", "R-nitpick1")]]
  "\<condition> (BADN 0 \<and> SPIN 0)"\<close>

end
