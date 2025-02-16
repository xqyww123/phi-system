signature PHI_COP_SIMP = sig

(* check if the simplification is required *)
type pattern = term
type trigger = Context.generic -> bvs * term -> bool

val is_simp_needed : Context.generic -> bvs -> term -> bool
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

val pass_recursively : (bvs -> term -> bool)
                     -> bvs -> term -> bool

end

signature PHI_COP_SIMP_RULES = sig

val direction : bool

val trans_rule_of : term -> thm

val binding_of_extracting_trigger : binding
val binding_of_rule_declaration_attr : binding

val PLPR_pass_name : string
val pattern_of_simp_rule : term
val pattern_of_transitive_simp_rule : term

end

functor Phi_CoP_Simp_GEN (RULES: PHI_COP_SIMP_RULES) : PHI_COP_SIMP = struct

(*** Check the need of simplification ***)

type pattern = term
type trigger = Context.generic -> bvs * term -> bool

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
   |> filter (fn Chk_Pattern pat => PLPR_Pattern.matches thy (K false) [] (pat, tm)
               | Chk_ML (_, pat, _) => PLPR_Pattern.matches thy (K false) [] (pat, tm))
  end

fun pass_recursively F =
  let fun chk bvs tm =
        let val (h,args) = Term.strip_comb tm
         in (case h
         of Const (\<^const_name>\<open>\<phi>Type\<close>, _) => F bvs tm orelse exists (chk bvs) (tl args)
          | Const _ => F bvs tm orelse exists (chk bvs) args
          | Free _  => F bvs tm orelse exists (chk bvs) args
          | Var _ => exists (chk bvs) args
          | Bound _ => exists (chk bvs) args
          | Abs (N, T, X) => if null args then chk ((N,T)::bvs) X
                             else raise REQUIRE_LAMBDA_NORMLAIZTION
          | _ => false)
        end
   in chk
  end

fun is_simp_needed ctxt =
  let val chkers = Checkers.get ctxt
      val thy = Context.theory_of ctxt
      fun apply_chk bvs tm =
        Net.match_term chkers tm
          |> exists (fn Chk_Pattern pat => PLPR_Pattern.matches thy (K true) bvs (pat,tm)
                      | Chk_ML (_, pat, f) => PLPR_Pattern.matches thy (K true) bvs (pat,tm)
                                      andalso f ctxt (bvs, tm))
   in Phi_Syntax.exists_item_of_assertion (pass_recursively apply_chk)
  end

fun chk_pattern pat =
      case Term.head_of pat
        of Const _ => ()
         | Free _ => ()
         | _ => raise TERM ("Phi_CoP_Simp.add_simp_pattern: The pattern must be leaded by a constant", [pat])

(*the (type part of) \<phi>-types matching this pattern will invoke the simplification*)
fun add_simp_pattern pat ctxt =
  (chk_pattern pat ;
   Checkers.map (Net.insert_term_safe (chker_eq (Context.theory_of ctxt))
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

fun trans_rule_of' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = trans_rule_of' X
  | trans_rule_of' (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X
        $ (Const(\<^const_name>\<open>\<A>_transitive_simp'\<close>, _) $ _ )) = SOME (RULES.trans_rule_of X)
  | trans_rule_of' _ = NONE

(*val enable_rule_pass = Attrib.setup_config_bool \<^binding>\<open>\<phi>simp_rule_pass\<close> (K false)*)
val extract_pattern_trigger = Attrib.setup_config_bool RULES.binding_of_extracting_trigger (K true)

fun force_rule_pass rule ctxt =
  let fun bad_rule msg = error ("Malform rule of Transformation-based Simplification:\n" ^
                                Context.cases Thm.string_of_thm_global Thm.string_of_thm ctxt rule ^ msg)

      val trans_rule = trans_rule_of' (Thm.concl_of rule)

      val rule'= (case trans_rule
                    of SOME R => rule RS (Thm.transfer (Context.theory_of ctxt) R)
                     | NONE => rule )
              |> Phi_Help.beta_eta_contract
              |> Drule.zero_var_indexes

      fun get_pat (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = get_pat X
        | get_pat (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = get_pat X
        | get_pat (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ _) =
              if RULES.direction then get_pat X else get_pat Y
        | get_pat (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) =
              if RULES.direction then T else
              bad_rule "\nThe target of the backward-transformation should be in \<open>y : Y subj y. r y\<close> form."
        | get_pat (Const(\<^const_name>\<open>ExBI\<close>, _) $ Abs (_, _,
              Const(\<^const_name>\<open>Subjection\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) $ _)) =
              if RULES.direction
              then bad_rule "\nThe source of the transformation should be a \<phi>-type or a BI predicate."
              else T
        | get_pat X = if Phi_Syntax.is_BI_connective X
                      then if RULES.direction
                           then bad_rule "\nThe source of the transformation should be a \<phi>-type or a BI predicate."
                           else bad_rule "\nThe target of the backward-transformation should be in \<open>y : Y subj y. r y\<close> form."
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
  val pattern_of_simp_rule = \<^pattern_prop>\<open>_ @tag \<A>simp' True\<close>
  val pattern_of_transitive_simp_rule = \<^pattern_prop>\<open>_ @tag \<A>_transitive_simp' True\<close>

  val simp_trans' = @{lemma'
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. y = y' @tag \<A>_transitive_simp' direction
\<Longrightarrow> y' \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w z @tag \<A>simp_if_need direction
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w z @tag \<A>simp' direction \<close>
  by (simp add: Action_Tag_def Transformation_def)}

  val simp_trans'P = @{lemma'
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. y = y' \<and> P y @tag \<A>_transitive_simp' direction
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P y' \<Longrightarrow> y' \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w z @tag \<A>simp_if_need direction)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] r' : (\<lambda>z. w z \<and> P y')
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. r' z @tag \<A>simp' direction \<close>
  by (simp add: Action_Tag_def Transformation_def Simplify_def) }

  val simp_trans = @{lemma'
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y @tag \<A>_transitive_simp' direction
\<Longrightarrow> (\<And>y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> r y \<Longrightarrow> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w y z @tag \<A>simp_if_need direction)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] r' : (\<lambda>z. \<exists>y. r y \<and> w y z)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. r' z @tag \<A>simp' direction \<close>
  by (simp add: Action_Tag_def Transformation_def Simplify_def, blast) }

  fun trans_rule_of (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ Y $ _) = trans_rule_of Y
    | trans_rule_of (Const(\<^const_name>\<open>ExBI\<close>, _) $ X) = trans_rule_of X
    | trans_rule_of (Abs (_, _, X)) = trans_rule_of X
    | trans_rule_of (Const(\<^const_name>\<open>Subjection\<close>, _) $ _ $ X) = trans_rule_of X
    | trans_rule_of (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _) = simp_trans'
    | trans_rule_of (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ (
              Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _) $ _) = simp_trans'P
    | trans_rule_of _ = simp_trans

)

structure Phi_CoP_Backward_Simp = Phi_CoP_Simp_GEN (

  val direction = false

  val binding_of_extracting_trigger = \<^binding>\<open>\<phi>backward_simp_extract_trigger\<close>
  val binding_of_rule_declaration_attr = \<^binding>\<open>\<phi>transformation_based_backward_simp\<close>

  val PLPR_pass_name = "Phi_CoP_Simp"
  val pattern_of_simp_rule = \<^pattern_prop>\<open>_ @tag \<A>simp' False\<close>
  val pattern_of_transitive_simp_rule = \<^pattern_prop>\<open>_ @tag \<A>_transitive_simp' False\<close>

  val simp_trans_backward = @{lemma'
  \<open> (\<And>x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> w x \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r x y @tag \<A>_transitive_simp' direction)
\<Longrightarrow> z \<Ztypecolon> Z \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. w x @tag \<A>simp_if_need direction
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] r' : (\<lambda>y. \<exists>x. r x y \<and> w x)
\<Longrightarrow> z \<Ztypecolon> Z \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r' y @tag \<A>simp' direction \<close>
  by (simp add: Action_Tag_def Transformation_def Simplify_def, blast) }

  val trans_rule_of = K simp_trans_backward

)
