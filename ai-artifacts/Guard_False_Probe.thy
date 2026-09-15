theory Guard_False_Probe
  imports "Phi_Logic_Programming_Reasoner.PLPR"
begin

(* TEMPORARY PROBE (2026-09-11): the \<condition> False idiom (Phi_BI.thy ToA_case_sum_src):
   the guard solver is asked to prove False from the contextual premises (the useful facts).
   Question: does a contradiction that needs classical search, not simp, get proved?
   Prediction from reading the code: no -- the "G.simpcut" pass cuts the state before
   the is_F branch's auto_search_tac ever sees the goal.
   2026-09-15: the is_F branch and the factory's pass are gone (plan section 39); the
   pass is guard_simp_tac inside the solving function, and P-auto is the search alone,
   p_auto_tac -- the last control below now runs that search, not the former
   p_auto_body (simp + search), so its outcome is not the 2026-09-11 one. *)

consts RR :: "nat \<Rightarrow> nat \<Rightarrow> bool"

declare [[\<phi>trace_reasoning = 3]]

ML \<open>
fun useful ctxt facts =
  fold (fn s => fn c =>
          Context.proof_map (Useful_Thms.add_thm (Thm.assume (Thm.cterm_of c (Syntax.read_prop c s)))) c)
       facts ctxt

fun run name ctxt facts =
  let val ctxt' = useful ctxt facts
      val st = Thm.trivial (Thm.cterm_of ctxt' (Syntax.read_prop ctxt' "\<condition> False"))
      val (time, r) = Timing.timing (fn () =>
            Phi_Reasoners.guard_condition_judge {can_inst = false} (ctxt', st) |> Seq.pull) ()
   in writeln (name ^ ": " ^ (case r of SOME _ => "PROVED (state returned)" | NONE => "FAILED (empty sequence)") ^
               " in " ^ string_of_int (Time.toMilliseconds (#elapsed time)) ^ " ms")
  end

(*controls: can the tactic alone prove  facts ==> False ?*)
fun control name ctxt facts tac =
  let val prems = map (Syntax.read_prop ctxt) facts
      val prop = Logic.list_implies (prems, \<^prop>\<open>False\<close>)
      val ok = can (fn () => Goal.prove ctxt [] [] prop (fn {context, ...} => HEADGOAL (tac context))) ()
   in writeln ("  control " ^ name ^ ": " ^ (if ok then "proves it" else "cannot")) end
\<close>

ML \<open>
val simp_facts = ["(x::nat option) = None", "(x::nat option) = Some y"]
val classical_facts = ["\<exists>x. \<forall>y. RR x y", "\<forall>x. \<not> RR x x"]
\<close>

ML \<open>run "simp-findable contradiction (x = None, x = Some y)" \<^context> simp_facts\<close>
ML \<open>control "asm_full_simp" \<^context> simp_facts Simplifier.asm_full_simp_tac\<close>

ML \<open>run "classical-only contradiction (EX x. ALL y. RR x y ; ALL x. ~ RR x x)" \<^context> classical_facts\<close>
ML \<open>control "asm_full_simp" \<^context> classical_facts Simplifier.asm_full_simp_tac;
    control "blast" \<^context> classical_facts Blast.blast_tac;
    control "auto (Clasimp)" \<^context> classical_facts (fn ctxt => fn _ => Clasimp.auto_tac ctxt);
    control "P-auto's search (p_auto_tac)" \<^context> classical_facts (fn ctxt => fn _ => Phi_Reasoners.p_auto_tac ctxt)\<close>

end
