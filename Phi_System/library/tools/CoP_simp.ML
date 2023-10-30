signature PHI_COP_SIMP = sig

(* check if the simplification is required *)
type pattern = term
type trigger = Context.generic -> PLPR_Pattern.bv_typs * term -> bool

val is_simp_needed : Context.generic -> PLPR_Pattern.bv_typs -> term -> bool
    (*checks types and assertions recursively but never enters into objects*)
val add_simp_pattern : pattern -> Context.generic -> Context.generic
val add_simp_trigger : pattern * trigger -> Context.generic -> serial * Context.generic
val del_simp_pattern : pattern -> Context.generic -> Context.generic
val del_simp_trigger : pattern * serial -> Context.generic -> Context.generic
  (*recursively check every lambda application \<open>f a\<^sub>1 \<dots> a\<^sub>n\<close> where \<open>f\<close> is an atom
    to see if the simplification is required, by checking if matching any pattern or ML trigger*)

datatype checker = Chk_Pattern of term | Chk_ML of serial * pattern * trigger
val checkers_binding_on : Context.generic -> pattern -> checker list

(* Controllers *)

val extract_pattern_trigger : bool Config.T
    (*controls if to extract and enable simplification triggers from each new rules otherwise
      no simplification will be triggered even when the form matches the rules.*)
(*val enable_rule_pass : bool Config.T*)

(* Helpers *)

val pass_recursively : (PLPR_Pattern.bv_typs -> term -> bool)
                     -> PLPR_Pattern.bv_typs -> term -> bool

end

signature PHI_COP_SIMP_RULES = sig

val direction : bool

val select_trans_rule : term -> thm

val binding_of_extracting_trigger : binding
val binding_of_rule_declaration_attr : binding

val PLPR_pass_name : string
val pattern_of_simp_rule : term
val pattern_of_transitive_simp_rule : term

end

functor Phi_CoP_Simp_GEN (RULES: PHI_COP_SIMP_RULES) : PHI_COP_SIMP = struct

(*** Check the need of simplification ***)

type pattern = term
type trigger = Context.generic -> PLPR_Pattern.bv_typs * term -> bool

datatype checker = Chk_Pattern of term | Chk_ML of serial * pattern * trigger

fun chker_eq thy (Chk_Pattern pa, Chk_Pattern pb) = Pattern.equiv thy (pa,pb)
  | chker_eq _ (Chk_ML (s1,_,_), Chk_ML (s2,_,_)) = s1 = s2
  | chker_eq _ _ = false

structure Checkers = Generic_Data (
  type T  = checker Net.net
  val empty = Net.empty
  val merge = Net.merge pointer_eq
)

fun checkers_binding_on ctxt tm =
  let val thy = Context.theory_of ctxt
   in Net.match_term (Checkers.get ctxt) tm
   |> filter (fn Chk_Pattern pat => PLPR_Pattern.matches thy [] (pat, tm)
               | Chk_ML (_, pat, _) => PLPR_Pattern.matches thy [] (pat, tm))
  end

fun pass_recursively F =
  let fun chk bv_tys tm =
        let val (h,args) = Term.strip_comb tm
         in (case h
         of Const (\<^const_name>\<open>\<phi>Type\<close>, _) => F bv_tys tm orelse exists (chk bv_tys) (tl args)
          | Const _ => F bv_tys tm orelse exists (chk bv_tys) args
          | Free _  => F bv_tys tm orelse exists (chk bv_tys) args
          | Var _ => exists (chk bv_tys) args
          | Bound _ => exists (chk bv_tys) args
          | Abs (_, T, X) => if null args then chk (T::bv_tys) X
                             else raise REQUIRE_LAMBDA_NORMLAIZTION
          | _ => false)
        end
   in chk
  end

fun is_simp_needed ctxt =
  let val chkers = Checkers.get ctxt
      val thy = Context.theory_of ctxt
      fun apply_chk bv_tys tm =
        Net.match_term chkers tm
          |> exists (fn Chk_Pattern pat => PLPR_Pattern.matches thy bv_tys (pat,tm)
                      | Chk_ML (_, pat, f) => PLPR_Pattern.matches thy bv_tys (pat,tm)
                                      andalso f ctxt (bv_tys, tm))
   in fn bvtys => Phi_Syntax.exists_item_of_assertion (pass_recursively apply_chk bvtys)
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
                                         (pat, Chk_ML (id,pat,chker))) ctxt)
  end

fun del_simp_pattern pat ctxt =
  Checkers.map (Net.delete_term (chker_eq (Context.theory_of ctxt)) (pat, Chk_Pattern pat)) ctxt

fun del_simp_trigger (pat,serial) ctxt =
  Checkers.map (Net.delete_term (chker_eq (Context.theory_of ctxt)) (pat, Chk_ML (serial, Term.dummy, K (K true)))) ctxt


(* Simplifier *)

fun select_trans_rule' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = select_trans_rule' X
  | select_trans_rule' (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X
        $ (Const(\<^const_name>\<open>\<A>_transitive_simp'\<close>, _) $ _ $ _ )) = SOME (RULES.select_trans_rule X)
  | select_trans_rule' _ = NONE

(*val enable_rule_pass = Attrib.setup_config_bool \<^binding>\<open>\<phi>simp_rule_pass\<close> (K false)*)
val extract_pattern_trigger = Attrib.setup_config_bool RULES.binding_of_extracting_trigger (K true)

fun force_rule_pass rule ctxt =
  let fun bad_rule msg = error ("Malform rule of Transformation-based Simplification:\n" ^
                                Context.cases Thm.string_of_thm_global Thm.string_of_thm ctxt rule ^ msg)

      val has_substantial_changes =
            case Thm.concl_of rule
              of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ (_ (*\<A>simp*) $ X)) =>
                    (case X of Const(\<^const_name>\<open>True\<close>, _)  => true
                             | Const(\<^const_name>\<open>False\<close>, _) => false
                             | X => raise TERM ("Must be a literal boolean. True for making some \
                                                \substantial simplification and False for not.", [X]))
               | _ => bad_rule ""

      val trans_rule = select_trans_rule' (Thm.concl_of rule)
                    |> Option.map (Thm.instantiate (TVars.empty, Vars.make [((("M",0),\<^typ>\<open>bool\<close>),
                          if has_substantial_changes then \<^cterm>\<open>False\<close> else \<^cterm>\<open>True\<close>)]))

      val rule'= (case trans_rule
                    of SOME R => rule RS (Thm.transfer (Context.theory_of ctxt) R)
                     | NONE => if has_substantial_changes
                               then rule RS (Thm.transfer (Context.theory_of ctxt)
                                                          @{lemma' \<open>P @action \<A>simp' forward True \<Longrightarrow> P @action \<A>simp' forward Any\<close>
                                                               by (simp add: Action_Tag_def)})
                               else rule )
              |> Phi_Help.beta_eta_contract
              |> Drule.zero_var_indexes

      fun get_pat (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = get_pat X
        | get_pat (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = get_pat X
        | get_pat (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ _) =
              if RULES.direction then get_pat X else get_pat Y
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
            warning ("Fail to extract the pattern of simplification triger from the source type of the rule\n" ^
                     Context.cases Thm.string_of_thm_global Thm.string_of_thm ctxt rule ^ "\n\
                     \The simplification will not be activated on the source \<phi>-type specified by the rule\n\
                     \You may want to add the trigger manually by ML \<open>setup \<open>Phi_CoP_Simp.add_simp_pattern\<close>\<close> or \<open>Phi_CoP_Simp.add_simp_trigger\<close>") ;
            (rule', ctxt)))
    | NONE => (rule', ctxt)
  end


val _ = Theory.setup (Context.theory_map (
  Phi_Reasoner.add_pass (Const(RULES.PLPR_pass_name, TFree("",[])), RULES.pattern_of_simp_rule,
    fn pos => fn (rules, mode, pats, guard, ctxt) =>
        (*if Config.get_generic ctxt enable_rule_pass
        then*) let val (rules', ctxt') = fold_map force_rule_pass rules ctxt
              in (rules', mode, pats, guard, ctxt')
             end
        (*else (rules, mode, pats, guard, ctxt)*) )
#>Phi_Reasoner.add_pass (Const(RULES.PLPR_pass_name, TFree("",[])), RULES.pattern_of_transitive_simp_rule,
    fn pos => fn (rules, mode, pats, guard, ctxt) =>
        (*if Config.get_generic ctxt enable_rule_pass
        then*) let val (rules', ctxt') = fold_map force_rule_pass rules ctxt
              in (rules', mode, pats, guard, ctxt')
             end
        (*else (rules, mode, pats, guard, ctxt)*) )
) #> Attrib.setup RULES.binding_of_rule_declaration_attr (
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


end


structure Phi_CoP_Simp = Phi_CoP_Simp_GEN (

  val direction = true

  val binding_of_extracting_trigger = \<^binding>\<open>\<phi>simp_extract_trigger\<close>
  val binding_of_rule_declaration_attr = \<^binding>\<open>\<phi>transformation_based_simp\<close>

  val PLPR_pass_name = "Phi_CoP_Simp"
  val pattern_of_simp_rule = \<^pattern_prop>\<open>_ @action \<A>simp' True _\<close>
  val pattern_of_transitive_simp_rule = \<^pattern_prop>\<open>_ @action \<A>_transitive_simp' True _\<close>

  fun select_trans_rule (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ Y $ _) = select_trans_rule Y
    | select_trans_rule (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = select_trans_rule X
    | select_trans_rule (Abs (_, _, X)) = select_trans_rule X
    | select_trans_rule (Const(\<^const_name>\<open>Subjection\<close>, _) $ _ $ X) = select_trans_rule X
    | select_trans_rule (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _) = @{thm' \<A>simp_trans'}
    | select_trans_rule (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ (
              Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _) $ _) = @{thm' \<A>simp_trans'P}
    | select_trans_rule _ = @{thm' \<A>simp_trans }

)

structure Phi_CoP_Backward_Simp = Phi_CoP_Simp_GEN (

  val direction = false

  val binding_of_extracting_trigger = \<^binding>\<open>\<phi>backward_simp_extract_trigger\<close>
  val binding_of_rule_declaration_attr = \<^binding>\<open>\<phi>transformation_based_backward_simp\<close>

  val PLPR_pass_name = "Phi_CoP_Simp"
  val pattern_of_simp_rule = \<^pattern_prop>\<open>_ @action \<A>simp' False _\<close>
  val pattern_of_transitive_simp_rule = \<^pattern_prop>\<open>_ @action \<A>_transitive_simp' False _\<close>

  val select_trans_rule = K @{thm' \<A>simp_trans_backward}

)
