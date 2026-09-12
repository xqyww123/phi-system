theory Guard_Export_Smoke
  imports Phi_Semantics.PhiSem_CF_Routine
          Phi_Semantics.PhiSem_CF_Breakable
          Phi_Semantics.PhiSem_Variable
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

(* Docs/GUARD_CACHE_QUICK_MODE_PLAN.md section 10 step 3, first half: the guard-cache
   export hook end to end.  A lemma the judge proposes at one guard call is enabled into
   the run's context (plan section 5 step 6) and must reach, through the hooks of
   PLPR_Context_Export, (a) the next guard call of the same run, (b) the next statement
   of the block, and (c) the enclosing block once a nested block closes -- so that the
   later guard is proved by P-auto with the lemma and the judge is never asked again.

   Not registered in any ROOT: evaluate on demand on top of the Phi_System_Base heap
   (the model is Test/Stateful_Reasoning_Smoke.thy).

   Two guard families, GX and GY: neither has a rule, so P-auto cannot prove a guard of
   theirs, R-conv cannot refute a truth and R-nitpick finds no countermodel to one -- the
   call ends with the judge, whose answer is the family's lemma.  The test judge counts
   its consultations per family; a second consultation for a family is the failure: the
   lemma did not arrive.  GX is enabled at the top level of the block and must reach the
   next statement; GY is enabled inside a nested block and must reach the enclosing block.
   Guards get fresh arguments (a process serial) because the in-memory store has no
   deletion and outlives a re-evaluation of this theory. *)

definition GX :: \<open>nat \<Rightarrow> bool\<close> where \<open>GX n = True\<close>
definition GY :: \<open>nat \<Rightarrow> bool\<close> where \<open>GY n = True\<close>
definition GX2 :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where \<open>GX2 a b = True\<close>

(*two guards of one run: the rule of the "same run" case*)
lemma GX2_rule[\<phi>reason 1000]:
  \<open> \<condition> GX a \<Longrightarrow> \<condition> GX b \<Longrightarrow> GX2 a b \<close>
  unfolding GX2_def by simp

ML \<open>
structure Export_Smoke = struct

val times = {thread_cpu = Time.fromMilliseconds 20, wall = Time.fromMilliseconds 20}
fun family_of t =
  if Term.exists_Const (fn (c, _) => c = \<^const_name>\<open>GX\<close>) t then SOME "GX"
  else if Term.exists_Const (fn (c, _) => c = \<^const_name>\<open>GY\<close>) t then SOME "GY"
  else NONE
fun lemma_of ctxt "GX" = (Syntax.read_prop ctxt "\<And>n. GX n", (times, "(simp add: GX_def)"), Phi_Guard_Cache.Normal)
  | lemma_of ctxt _    = (Syntax.read_prop ctxt "\<And>n. GY n", (times, "(simp add: GY_def)"), Phi_Guard_Cache.Normal)

(*consultations per family; any other guard of the surrounding machinery that reaches
  the judge is answered Unprovable, which backtracks exactly as Unknown would*)
val consulted = Unsynchronized.ref (Symtab.empty : int Symtab.table)
fun count fam = Symtab.lookup (!consulted) fam |> the_default 0
fun judge (arg : Phi_Reasoners.judge_arg) =
  case family_of (Thm.major_prem_of (#thm arg)) of
    NONE => Phi_Reasoners.Unprovable
  | SOME fam =>
      let val n = count fam + 1
          val _ = consulted := Symtab.update (fam, n) (!consulted)
       in if n = 1 then Phi_Reasoners.Provable [lemma_of (#outer_ctxt arg) fam]
          else error ("export smoke: the judge was consulted a " ^ string_of_int n ^
                      "th time for " ^ fam ^ ": the lemma did not reach this guard")
      end

(*the trigger's arming: the family whose guard the next run decides*)
val armed = Unsynchronized.ref (NONE : string option)
fun arm fam = armed := SOME fam
fun guard_prop ctxt fam = Syntax.read_prop ctxt ("\<condition> " ^ fam ^ " " ^ string_of_int (serial ()))

fun has_lemma fam ctxt =
  exists (fn (th, _) => family_of (Thm.prop_of th) = SOME fam) (Phi_Guard_Cache.get_lemmas ctxt)
fun expect_lemma name fam ctxt =
  if has_lemma fam ctxt then tracing (name ^ ": the " ^ fam ^ " lemma is in the context")
  else error (name ^ ": the " ^ fam ^ " lemma is NOT in the context; the list holds " ^
              commas (map (Syntax.string_of_term ctxt o Thm.prop_of o fst) (Phi_Guard_Cache.get_lemmas ctxt)))
fun expect_absent name fam ctxt =
  if has_lemma fam ctxt then error (name ^ ": the " ^ fam ^ " lemma is present too early")
  else tracing (name ^ ": the " ^ fam ^ " lemma is absent, as expected")
fun report name fam ctxt =
  tracing (name ^ ": the " ^ fam ^ " lemma is " ^ (if has_lemma fam ctxt then "PRESENT" else "ABSENT"))
fun expect_consulted name fam n =
  if count fam = n then tracing (name ^ ": the judge was consulted " ^ string_of_int n ^ " time(s) for " ^ fam)
  else error (name ^ ": expected " ^ string_of_int n ^ " consultation(s) for " ^ fam ^
              " but saw " ^ string_of_int (count fam))
fun reset () = (consulted := Symtab.empty; armed := NONE)
end
\<close>

ML \<open>Phi_Reasoners.judge := SOME Export_Smoke.judge\<close>

(*the trigger: on the first antecedent of the next run after arming, decides a fresh guard
  of the armed family through the real guard machinery -- the factory over
  prove_or_refute -- and continues the run in the context that call returns*)
\<phi>reasoner_ML GX_trigger ? 2000000000 (\<open>PROP ?P\<close>) = \<open>fn (_, (ctxt, sequent)) =>
  case ! Export_Smoke.armed of
    NONE => Seq.empty
  | SOME fam =>
      let val _ = Export_Smoke.armed := NONE
          val st = Thm.trivial (Thm.cterm_of ctxt (Export_Smoke.guard_prop ctxt fam))
       in case Seq.pull (Phi_Reasoners.guard_condition_judge {can_inst = false} (ctxt, st)) of
            SOME ((ctxt', _), _) => Seq.single (ctxt', sequent)
          | NONE => error ("export smoke: the trigger's " ^ fam ^ " guard was not proved")
      end\<close>


section \<open>(a) The next call of the same run\<close>

(*GX2_rule's two guards in one run: the first consults the judge, the second is proved
  with the lemma the first enabled; the context the run returns -- through the hook at
  the run boundary -- carries the lemma*)
ML \<open>
let val ctxt = \<^context>
    val _ = Export_Smoke.reset ()
    val goal = Thm.trivial (Thm.cterm_of ctxt (Syntax.read_prop ctxt
                 ("GX2 " ^ string_of_int (serial ()) ^ " " ^ string_of_int (serial ()))))
 in case Phi_Reasoner.reason NONE NONE (ctxt, goal) of
      NONE => error "same run: the reasoning failed"
    | SOME (ctxt', th) =>
        (if Thm.no_prems th then () else error "same run: the goal is not solved";
         Export_Smoke.expect_consulted "same run" "GX" 1;
         Export_Smoke.expect_lemma "same run: the context the run returned" "GX" ctxt')
end
\<close>


section \<open>(b) The next statement, (c) the enclosing block after a nested block\<close>

proc GX_blocks:
  input  \<open>x \<Ztypecolon> \<val> \<nat>\<close>
  output \<open>x \<Ztypecolon> \<val> \<nat>\<close>
  is [routine]
\<medium_left_bracket>
  ML_prf \<open>Export_Smoke.reset ();
          Export_Smoke.expect_absent "block entry" "GX" \<^context>;
          Export_Smoke.arm "GX"\<close>
  \<semicolon> var v \<leftarrow> $x \<semicolon>
  ML_prf \<open>Export_Smoke.expect_consulted "statement 1" "GX" 1;
          Export_Smoke.expect_lemma "after statement 1: the block context" "GX" \<^context>;
          Export_Smoke.arm "GX"\<close>
  \<semicolon> $v \<rightarrow> val w \<semicolon>
  ML_prf \<open>Export_Smoke.expect_consulted "statement 2: the next statement's guard proved with the lemma" "GX" 1;
          Export_Smoke.expect_absent "before the nested block" "GY" \<^context>\<close>
  (*GY is enabled inside the FIRST branch; the second branch reports whether it starts
    from the enclosing context as the first branch's close left it (GY present) or from
    the context before the if (GY absent); the enclosing block is asserted after the if*)
  \<semicolon> if \<open>$x = 0\<close> \<medium_left_bracket>
    $w \<rightarrow> val u \<semicolon>
    ML_prf \<open>Export_Smoke.expect_lemma "the first branch" "GX" \<^context>;
            Export_Smoke.expect_absent "the first branch, at entry" "GY" \<^context>;
            Export_Smoke.arm "GY"\<close>
    \<semicolon> $u \<rightarrow> val u' \<semicolon>
    ML_prf \<open>Export_Smoke.expect_consulted "inside the first branch" "GY" 1;
            Export_Smoke.expect_lemma "inside the first branch" "GY" \<^context>\<close>
    \<semicolon> $u'
  \<medium_right_bracket> \<medium_left_bracket>
    $w \<rightarrow> val u \<semicolon>
    ML_prf \<open>Export_Smoke.report "the second branch, at entry" "GY" \<^context>\<close>
    \<semicolon> $u
  \<medium_right_bracket> \<rightarrow> val z \<semicolon>
  ML_prf \<open>Export_Smoke.expect_lemma "the enclosing block after the nested block" "GY" \<^context>;
          Export_Smoke.arm "GY"\<close>
  \<semicolon> $z \<rightarrow> val z' \<semicolon>
  ML_prf \<open>Export_Smoke.expect_consulted "the statement after the nested block: its guard proved with the lemma" "GY" 1\<close>
  \<semicolon> $v
\<medium_right_bracket> .

ML \<open>Phi_Reasoners.judge := NONE\<close>

end
