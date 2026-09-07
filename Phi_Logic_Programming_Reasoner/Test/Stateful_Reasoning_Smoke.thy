theory Stateful_Reasoning_Smoke
  imports Phi_Semantics.PhiSem_CF_Breakable
          Phi_Semantics.PhiSem_CF_Routine
          Phi_Semantics.PhiSem_Variable
          Phi_Semantics.PhiSem_Int_ArbiPrec
          Phi_Semantics.PhiSem_Machine_Integer
          Phi_Semantics.PhiSem_Aggregate_Tuple
begin

(* V2 of ai-artifacts/STATEFUL_PLPR_REASONING_PLAN.md, section 7: the smoke test of the
   stateful PLPR reasoning -- the run boundary and the block boundary return a context
   through the hooks of PLPR_Context_Export.

   Not registered in any ROOT: evaluate on demand on top of the Phi_Semantics heap.

   Two hook-owned slots are transplanted: a counter of marks and a list of auxiliary
   theorems.  A marking reasoner fires on the first antecedent of every run, marking once
   (a run-local flag, NOT hook-owned, makes it fire once and avoids a loop).  Because the
   flag is not transplanted, every hook-crossed run starts fresh and marks; a site that
   inherits the run's context shows the mark count risen since the statement before it.
   The theorem slot checks export_aux_lemma at a run boundary (the Isar method site): a
   theorem mentioning a variable fixed inside the run is dropped, a clean one arrives.  The
   block-boundary export function block_export (its Premise-conditional and obtain-frame
   branches) is exercised on real code by the full example suite (V3), which imports an
   Isar `obtain` inside a programming block. *)

ML \<open>
structure V2 = struct

structure Marks  = Proof_Data (type T = int  val init = K 0)
structure Lemmas = Proof_Data (type T = thm list  val init = K [])
(*run-local: makes the marking reasoner fire once per run and avoids a re-loop; NOT
  transplanted by the hook, so every hook-crossed run starts fresh (flag false) and marks*)
structure Marked_This_Run = Proof_Data (type T = bool  val init = K false)

fun mark ctxt = Marks.map (fn n => n + 1) ctxt

(*the hook: overwrites its two slots (contract H2); every theorem goes through
  export_aux_lemma one by one (contract H1)*)
val _ = Theory.setup (Context.theory_map (PLPR_Context_Export.Hooks.add 100 (fn inner => fn outer =>
  outer |> Marks.put (Marks.get inner)
        |> Lemmas.put (map_filter (PLPR_Context_Export.export_aux_lemma inner outer)
                                  (Lemmas.get inner)))))

(* marks *)

val last = Unsynchronized.ref 0
fun begin name ctxt =
  (last := Marks.get ctxt; tracing (name ^ ": marks at entry = " ^ string_of_int (!last)))
fun expect_marked name ctxt =
  let val n = Marks.get ctxt
   in if n > !last
      then (tracing (name ^ ": marks " ^ string_of_int (!last) ^ " -> " ^ string_of_int n); last := n)
      else error (name ^ ": the run's context did not arrive (marks = " ^ string_of_int n ^
                  ", before = " ^ string_of_int (!last) ^ ")")
  end

(* auxiliary theorems *)

fun props ctxt = map Thm.prop_of (Lemmas.get ctxt)
fun show ctxt = commas (map (Syntax.string_of_term ctxt) (props ctxt))
fun expect_lemma name ctxt t =
  if exists (fn p => p aconv t) (props ctxt)
  then tracing (name ^ ": arrived: " ^ Syntax.string_of_term ctxt t)
  else error (name ^ ": expected lemma missing: " ^ Syntax.string_of_term ctxt t ^
              "\n  present: " ^ show ctxt)
fun expect_no_lemma name ctxt pred =
  case filter pred (props ctxt)
    of [] => tracing (name ^ ": correctly absent")
     | ps => error (name ^ ": unexpected lemma(s): " ^ commas (map (Syntax.string_of_term ctxt) ps))
fun mentions x = Term.exists_subterm (fn Free (y, _) => x = y | _ => false)

(* the facts of a block with premises: A carries the attributes' effect (tag stripped),
   that is the raw premise (tag intact) *)
fun dest_premise (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ C)) = SOME C
  | dest_premise _ = NONE
fun expect_premise_facts ctxt =
  let val a = Thm.prop_of (Proof_Context.get_thm ctxt "A")
      val thats = map Thm.prop_of (Proof_Context.get_thms ctxt "that")
   in if is_some (dest_premise a)
      then error ("premise fact A still carries the tag: " ^ Syntax.string_of_term ctxt a) else ();
      if exists (is_some o dest_premise) thats
      then tracing ("premise facts: A = " ^ Syntax.string_of_term ctxt a ^
                    "; that = " ^ commas (map (Syntax.string_of_term ctxt) thats))
      else error ("no `that` fact keeps the raw tag: " ^
                  commas (map (Syntax.string_of_term ctxt) thats))
  end

end
\<close>

subsection \<open>Test reasoners\<close>

(*fires on the first antecedent of every run: marks once, sets the run-local flag, and
  passes the goal through unchanged for the real reasoners.  Highest priority, NO_CUT.*)
\<phi>reasoner_ML V2_mark ? 2000000000 (\<open>PROP ?P\<close>) = \<open>fn (_, (ctxt, sequent)) =>
  if V2.Marked_This_Run.get ctxt then Seq.empty
  else Seq.single (ctxt |> V2.mark |> V2.Marked_This_Run.put true, sequent)\<close>

definition V2_Trigger :: bool where \<open>V2_Trigger \<equiv> True\<close>
lemma V2_Trigger_I: \<open>V2_Trigger\<close> unfolding V2_Trigger_def ..

(*fixes a variable inside the run and plants one theorem mentioning it (must be dropped)
  and one clean theorem (must arrive)*)
\<phi>reasoner_ML V2_Trigger 100 (\<open>V2_Trigger\<close>) = \<open>fn (_, (ctxt, sequent)) =>
  let val ([x], ctxt') = Variable.add_fixes ["v2x"] ctxt
      val local_thm = Thm.reflexive (Thm.cterm_of ctxt' (Free (x, \<^typ>\<open>nat\<close>)))
      val ctxt'' = ctxt' |> V2.Lemmas.map (fn L => local_thm :: @{thm V2_Trigger_I} :: L)
   in Seq.single (ctxt'', @{thm V2_Trigger_I} RS sequent)
  end\<close>

definition V2_Fail :: bool where \<open>V2_Fail \<equiv> True\<close>
lemma V2_fail_rule: \<open>V2_Fail \<Longrightarrow> (X::assn) \<transforms> X\<close> by (rule transformation_refl)

(*reports a failure reason and fails*)
\<phi>reasoner_ML V2_Fail 100 (\<open>V2_Fail\<close>) = \<open>fn (_, (ctxt, _)) =>
  (Phi_Reasoners.report_failure_reason1 ctxt 0
      [fn () => Pretty.str "V2: the failure reason planted by V2_Fail"];
   Seq.empty)\<close>

(*a modifier that marks without a run*)
attribute_setup v2_mark =
  \<open>Scan.succeed (Phi_Modifier.wrap_to_attribute (fn (ctxt, th) => (V2.mark ctxt, th)))\<close>

subsection \<open>The Isar method \<open>\<phi>reason\<close>\<close>

lemma \<open>V2_Trigger\<close>
  apply \<phi>reason
  ML_prf \<open>let val ctxt = \<^context>
           in V2.last := 0;
              V2.expect_lemma "method" ctxt (Thm.prop_of @{thm V2_Trigger_I});
              if Variable.is_fixed ctxt "v2x" then error "method: the run's fix leaked" else ();
              V2.expect_no_lemma "method" ctxt (V2.mentions "v2x")
          end\<close>
  done

subsection \<open>A deriver (a discarding site) runs with the marking reasoner active\<close>

\<phi>type_def V2_Ex :: \<open>(VAL, nat) \<phi>\<close>
  where \<open>x \<Ztypecolon> V2_Ex \<equiv> (x, d) \<Ztypecolon> \<lbrace> \<nat>, \<nat> \<rbrace> \<subj> d. d = 0\<close>
  deriving Basic

subsection \<open>Programming blocks\<close>

(*Value-construction sites reached through the operator stack (e.g. \<open>val p \<leftarrow> \<lbrace> \<dots> \<rbrace>\<close>) thread
  the context directly and are covered by the full example suite (V3), not here.*)

proc V2_blocks:
  input  \<open>x \<Ztypecolon> \<val> \<nat>\<heavy_comma> q \<Ztypecolon> \<val> V2_Ex\<close>
  premises A: \<open>x < 10\<close>
  output \<open>x \<Ztypecolon> \<val> \<nat>\<close>
  is [v2_mark]
  is [routine]
\<medium_left_bracket>
  ML_prf \<open>let val ctxt = \<^context>
           in V2.last := 0;   \<comment> \<open>the mark set by the \<open>is [v2_mark]\<close> modifier survives block setup\<close>
              V2.expect_marked "modifier chain and block initialisation" ctxt;
              V2.expect_premise_facts ctxt;
              (*a failing application still lists the reasons collected during its run*)
              (case (SOME (Phi_Apply.apply1 [@{thm V2_fail_rule}] (ctxt, Phi_Envir.the_programming_sequent' ctxt))
                     handle ERROR msg =>
                       if String.isSubstring "V2: the failure reason" msg
                       then (tracing "apply1: the failure reason arrived in the error"; NONE)
                       else error ("apply1: the collected failure reason is lost:\n" ^ msg))
                 of NONE => ()
                  | SOME _ => error "apply1: expected the application to fail")
          end\<close>
  ML_prf \<open>V2.begin "assignment" \<^context>\<close>
  \<semicolon> var v \<leftarrow> $x \<semicolon>
  ML_prf \<open>V2.expect_marked "assignment statement" \<^context>;
          V2.begin "open" \<^context>\<close>
  \<semicolon> val q' \<leftarrow> $q to \<open>OPEN _ _\<close> \<semicolon>
  ML_prf \<open>V2.expect_marked "open with existential elimination" \<^context>\<close>
  \<comment> \<open>an Isar obtain inside the block installs a frame phi does not own; the block close
     must still transplant the hook's marks through it (export_aux_lemma must not choke it)\<close>
  obtain d where f: \<open>d = (0::nat)\<close> by auto
  \<semicolon> $v
\<medium_right_bracket> .

end
