signature PHI_COP_SIMP = sig

(* check if the simplification is required *)

val is_simp_needed : Context.generic -> term -> bool
val add_simp_pattern : term -> Context.generic -> Context.generic
val add_simp_trigger : term (*pattern*) * (term -> bool) -> Context.generic -> serial * Context.generic
val del_simp_pattern : term -> Context.generic -> Context.generic
val del_simp_trigger : term (*pattern*) * serial -> Context.generic -> Context.generic

(* invoke the simplification if needed *)

val invoke_when_needed : Proof.context * Phi_Working_Mode.working_mode -> thm -> thm
val force_invoke : Proof.context * Phi_Working_Mode.working_mode -> thm -> thm (*no matter if is needed*)

(* Pass of Reasoning Rules *)

val enable_rule_pass : bool Config.T

end

structure Phi_CoP_Simp : PHI_COP_SIMP = struct

(*** Check the need of simplification ***)

datatype checker = Chk_Pattern of term | Chk_ML of serial * (term -> bool)

fun chker_eq thy (Chk_Pattern pa, Chk_Pattern pb) = Pattern.equiv thy (pa,pb)
  | chker_eq _ (Chk_ML (s1,_), Chk_ML (s2,_)) = s1 = s2
  | chker_eq _ _ = false

structure Checkers = Generic_Data (
  type T  = checker Net.net
  val empty = Net.empty
  val merge = Net.merge pointer_eq
)

fun is_simp_needed ctxt =
  let val chkers = Checkers.get ctxt
      val thy = Context.theory_of ctxt
      fun apply_chk bv_tys tm =
        Net.match_term chkers tm
          |> exists (fn Chk_Pattern pat => PLPR_Pattern.matches thy bv_tys (pat,tm)
                      | Chk_ML (_, f)   => f tm)
      fun chk bv_tys tm =
        let val (h,args) = Term.strip_comb tm
         in (case h
         of Const _ => apply_chk bv_tys tm
          | Free _  => apply_chk bv_tys tm
          | Abs (_, T, X) => if null args then chk (T::bv_tys) X
                             else raise REQUIRE_LAMBDA_NORMLAIZTION
          | _ => false)
         orelse exists (chk bv_tys) args
        end
        handle REQUIRE_LAMBDA_NORMLAIZTION =>
          chk bv_tys (Envir.beta_eta_contract tm)
   in Phi_Syntax.exists_item_of_assertion (chk [])
  end

fun chk_pattern pat =
      case Term.head_of pat
        of Const _ => ()
         | Free _ => ()
         | _ => raise TERM ("Phi_CoP_Simp.add_simp_pattern: The pattern must be leaded by a constant", [pat])

(*the (type part of) \<phi>-types matching this pattern will invoke the simplification*)
fun add_simp_pattern pat ctxt =
  (chk_pattern pat ;
   Checkers.map (Net.insert_term (chker_eq (Context.theory_of ctxt))
                                 (pat, Chk_Pattern pat)) ctxt)

fun add_simp_trigger (pat,chker) ctxt =
  let val _ = chk_pattern pat
      val id = serial()
   in (id, Checkers.map (Net.insert_term (chker_eq (Context.theory_of ctxt))
                                         (pat, Chk_ML (id,chker))) ctxt)
  end

fun del_simp_pattern pat ctxt =
  Checkers.map (Net.delete_term (chker_eq (Context.theory_of ctxt)) (pat, Chk_Pattern pat)) ctxt

fun del_simp_trigger (pat,serial) ctxt =
  Checkers.map (Net.delete_term (chker_eq (Context.theory_of ctxt)) (pat, Chk_ML (serial, K true))) ctxt


(* invoke the simplification if needed *)

fun force_invoke (ctxt, mode) sequent =
  let val sequent' = @{thm' \<A>simp_stage_1} RS (sequent RS' (ctxt, #transformation_rule mode))
   in Phi_Reasoner.reason1 (fn () => "Simplification fails") NONE (SOME 1) ctxt sequent'
  end

fun invoke_when_needed (ctxt, mode) sequent =
  let val assertion = #spec_of mode (Thm.prop_of sequent)
   in if is_simp_needed (Context.Proof ctxt) assertion
   then (Phi_Reasoner.info_print ctxt 2 (fn () => "Invoking transformation-based simplification...");
         force_invoke (ctxt, mode) sequent)
   else sequent
  end

(* Simplifier *)

fun select_trans_rule (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = select_trans_rule X
  | select_trans_rule (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = select_trans_rule X
  | select_trans_rule (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ Y $ _) = select_trans_rule Y
  | select_trans_rule (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = select_trans_rule X
  | select_trans_rule (Abs (_, _, X)) = select_trans_rule X
  | select_trans_rule (Const(\<^const_name>\<open>Subjection\<close>, _) $ _ $ X) = select_trans_rule X
  | select_trans_rule (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _) = @{thm' \<A>simp_trans'}
  | select_trans_rule (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ (
            Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _) $ _) = @{thm' \<A>simp_trans'P}
  | select_trans_rule _ = @{thm' \<A>simp_trans}

val enable_rule_pass = Config.declare_bool ("Phi_CoP_Simp.enable_rule_pass", \<^here>) (K false)
val extract_pattern_trigger = Config.declare_bool ("Phi_CoP_Simp.extract_pattern_trigger", \<^here>) (K true)

fun force_rule_pass rule ctxt =
  let fun bad_rule msg = error ("Malform rule of Transformation-based Simplification:\n" ^
                                Context.cases Thm.string_of_thm_global Thm.string_of_thm ctxt rule ^ msg)

      val has_substantial_changes =
            case Thm.concl_of rule
              of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ (_ (*\<A>simp*) $ X)) =>
                    (case X of Const(\<^const_name>\<open>True\<close>, _) => \<^cterm>\<open>False\<close>
                             | _ => \<^cterm>\<open>True\<close>)
               | _ => bad_rule ""
      val trans_rule = select_trans_rule (Thm.concl_of rule)
                    |> Thm.instantiate (TVars.empty, Vars.make [((("M",0),\<^typ>\<open>bool\<close>),has_substantial_changes)])
      val rule' = rule RS (Thm.transfer (Context.theory_of ctxt) trans_rule)

      fun get_pat (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = get_pat X
        | get_pat (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = get_pat X
        | get_pat (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ _ $ _) = get_pat X
        | get_pat (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) = T
        | get_pat X = if Phi_Syntax.is_BI_connective X
                      then bad_rule "\nThe source of the transformation should be a \<phi>-type or a BI predicate."
                      else X
      val pat = if Config.get_generic ctxt extract_pattern_trigger
                then SOME (get_pat (Thm.concl_of rule))
                else NONE
   in case pat
   of SOME pat =>
      (case try (add_simp_pattern pat) ctxt
       of SOME ctxt' => (rule', ctxt')
        | NONE => (
            warning ("Fail to extract the pattern of the source type of the rule\n" ^
                     Context.cases Thm.string_of_thm_global Thm.string_of_thm ctxt rule ^ "\n\
                     \The simplification will not be activated on the source type specified by the rule\n\
                     \You may want to add the trigger manually by ML \<open>setup \<open>Phi_CoP_Simp.add_simp_pattern\<close>\<close> or \<open>Phi_CoP_Simp.add_simp_trigger\<close>") ;
            (rule', ctxt)))
    | NONE => (rule', ctxt)
  end


val _ = Theory.setup (Context.theory_map (
  Phi_Reasoner.add_pass ("Phi_CoP_Simp", \<^pattern_prop>\<open>_ @action \<A>simp' _\<close>,
    fn pos => fn (rules, mode, pats, guard, ctxt) =>
        if Config.get_generic ctxt enable_rule_pass
        then let val (rules', ctxt') = fold_map force_rule_pass rules ctxt
              in (rules', mode, pats, guard, ctxt')
             end
        else (rules, mode, pats, guard, ctxt))
) #> Attrib.setup \<^binding>\<open>\<phi>transformation_based_simp\<close> (
  Phi_Reasoner.attr_syntax
    (Scan.lift (Scan.optional (Args.$$$ "no" |-- Args.$$$ "trigger" >> K false) true))
    (fn (pos, mode, priority, add_trigger, patterns, guard) =>
      Thm.declaration_attribute (fn rule => fn ctxt => ctxt
        |> Config.put_generic extract_pattern_trigger add_trigger
        |> Phi_Reasoner.add_rule pos mode priority patterns guard [rule]
        |> Config.restore_generic extract_pattern_trigger ctxt
    ))
) "Basically the ordinary \<phi>reason but of a special flag \<open>no trigger\<close> to prevent the left hand side \
  \of the rule being registered as a trigger activating the simplification reasoning"
)

(*

fun simplifier (ctxt0,sequent) = Seq.make (fn () =>
  let val reasoners = Phi_Reasoner.reasoners ctxt0
      val thy = Proof_Context.theory_of ctxt0

      fun simp_task_mode (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = simp_task_mode X
        | simp_task_mode (Const(\<^const_name>\<open>Action_Tag\<close>, _)
              $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _)
              $ (Const(\<^const_name>\<open>to\<close>, _) $ Const(\<^const_name>\<open>\<A>simp\<close>, _)) ) = 1
        | simp_task_mode (Const(\<^const_name>\<open>Premise\<close>, _) $ X $ _) = simp_task_mode X
        | simp_task_mode (Const(\<^const_name>\<open>\<A>simp\<close>, _)) = 2
        | simp_task_mode (Const(\<^const_name>\<open>default\<close>, _)) = 3
        | simp_task_mode _ = 0

      

      fun apply_rule rule (ctxt, sequent) =
        (ctxt, (rule RS' (ctxt, select_trans_rule (Thm.concl_of rule))) RS' (ctxt, sequent))

      fun apply_rules (rule :: L) s = (SOME (apply_rule rule s) handle THM _ => apply_rules L s)
        | apply_rules [] _ = NONE

      fun call_the_first (r :: L) s =
           (case #tactic (#4 r)
              of Phi_Reasoner.Tac_Rule rules => (
                  case apply_rules rules s of NONE => call_the_first L s
                     | some => some)
               | Phi_Reasoner.Tac_ML tac => (
                  case Seq.pull (tac s) of SOME (s', _) => SOME s'
                     | NONE => call_the_first L s))
        | call_the_first [] _ = NONE

      fun simp (ctxt,th0) =
        let val th = (if Term.could_beta_eta_contract (Thm.major_prem_of th0)
                      then Conv.gconv_rule Phi_Help.beta_eta_conversion 1 th0
                      else th0)
            val mprem = Thm.major_prem_of th
         in case simp_task_mode mprem
         of 0 => (ctxt, th)
          | 1 => (case call_the_first (Phi_Reasoner.get_reasoners' thy reasoners mprem) (ctxt, th)
                    of NONE => (ctxt, th)
                     | SOME s => simp s)
          | 2 => simp (ctxt, Phi_Reasoners.safer_obligation_solver)
        end
   in SOME (simp (ctxt0,sequent), Seq.empty)
  end)
*)

end