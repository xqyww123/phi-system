chapter \<open>Theoretical Foundations\<close>

section \<open>Preliminary\<close>

theory Phi_Preliminary
  imports Main "Phi_Algebras.Algebras"
          Phi_Logic_Programming_Reasoner.PLPR
          Phi_Logic_Programming_Reasoner.PLPR_error_msg
  keywords "optional_translations" :: thy_decl
       and "\<phi>adhoc_overloading" "\<phi>no_adhoc_overloading" :: thy_decl
  abbrevs "<implies>" = "\<i>\<m>\<p>\<l>\<i>\<e>\<s>"
      and "<suffices>" = "\<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>"
begin

declare [[ML_debugger, ML_exception_debugger, ML_print_depth=100]]

subsection \<open>Named Theorems\<close>

ML \<open>structure Phi_Expansions = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>expns\<close>
  val comment = "Semantics Expansions, used to expand assertions semantically."
  val attribute = NONE
  val post_merging = I
)\<close>

declare set_mult_expn[\<phi>expns] Premise_def[\<phi>expns]

ML \<open>
structure Phi_Programming_Simp_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>programming_simps\<close>
  val comment = "Simplification rules used in the deductive programming, including the \<phi>programming_base_simps."
  val attribute = NONE
  val post_merging = I
)
\<comment> \<open>A trick: if a \<phi>programming_simp rule is also declared in the system simpset, just declare it
    by \<phi>programming_base_simps, and it can improve the performance.\<close>

structure Phi_Programming_Base_Simp_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>\<phi>programming_base_simps\<close>
  val comment = "Simplification rules used only in low level automation"
  val attribute = NONE
  val post_merging = I
)
\<close>


setup \<open>Context.theory_map (Phi_Programming_Base_Simp_SS.map (fn ctxt =>
  ctxt addsimprocs [\<^simproc>\<open>NO_MATCH\<close>, \<^simproc>\<open>defined_All\<close>, \<^simproc>\<open>defined_Ex\<close>]))\<close>



subsection \<open>Error Mechanism\<close>

ML_file \<open>library/tools/error.ML\<close>


subsection \<open>Helper ML\<close>

ML_file \<open>library/tools/Phi_Help.ML\<close>
ML_file \<open>library/tools/lift_type_sort.ML\<close>
ML_file \<open>library/syntax/helps.ML\<close>
ML_file \<open>library/system/Phi_Envir0.ML\<close>
ML_file \<open>library/system/Phi_ID.ML\<close>
ML_file \<open>library/tools/Hasher.ML\<close>
ML_file \<open>library/tools/cache_file.ML\<close>


(*
A JSON lib. Maybe one day in the cache file we will use JSON (or better some K-V data base)
instead of XML. I'm thinking of the performance of the XML, particularly we have a lot of
`<` and `>` symbols. Need some tests.

ML_file \<open>contrib/sml-json/json.sig\<close>
ML_file \<open>contrib/sml-setmap/map/MONO_MAP.sig\<close>
ML_file \<open>contrib/sml-setmap/map/OrderMapImpl.sml\<close>
ML_file \<open>contrib/sml-setmap/map/OrderMap.sml\<close>
ML_file \<open>contrib/sml-setmap/map/StringMap.sml\<close>
ML_file \<open>contrib/sml-json/json.sml\<close> *)

subsection \<open>Helper Methods\<close>

method_setup subgoal' = \<open>
     Scan.lift (Scan.option (\<^keyword>\<open>premises\<close> |-- Parse.binding))
  -- Scan.lift (Scan.option (\<^keyword>\<open>for\<close> |-- Parse.and_list (Scan.repeat1 Parse.binding) >> flat))
  -- Scan.lift (Parse.token Parse.embedded) >>
 (fn ((prem_b, fixes), text_tok) => fn ctxt => fn rules =>
  let fun FOCUS tac ctxt i st =
        if Thm.nprems_of st < i then Seq.empty
        else let val (args as {context = ctxt', params, asms, prems, ...}, st') =
                    (if is_some prem_b then Subgoal.focus else Subgoal.focus_params_fixed) ctxt i fixes st
                 val ctxt' = case prem_b of SOME b =>
                                    Proof_Context.note_thms "" ((b,[]), map (fn th => ([th],[])) prems) ctxt'
                                      |> snd
                                | _ => ctxt'
              in Seq.lifts (Subgoal.retrofit ctxt' ctxt params asms i) (tac ctxt' st') st
             end
   in Context_Tactic.CONTEXT_TACTIC (HEADGOAL (FOCUS (fn ctxt =>
      let val (text, src) = Method.read_closure_input ctxt (Token.input_of text_tok)
       in Context_Tactic.NO_CONTEXT_TACTIC ctxt (Method.evaluate_runtime text ctxt rules)
      end) ctxt))
  end)
\<close>


subsection \<open>Helper Lemmas\<close>

lemma imp_implication: "(P \<longrightarrow> Q \<Longrightarrow> PROP R) \<equiv> ((P \<Longrightarrow> Q) \<Longrightarrow> PROP R)" by rule simp+

lemma case_sum_collapse[simp]:
  \<open>case_sum Inl Inr = (\<lambda>x. x)\<close>
  unfolding fun_eq_iff
  by (clarsimp simp add: split_sum_all)

lemma snd_o_Pair_eq_id[simp]:
  \<open> snd \<circ> Pair c = (\<lambda>x. x) \<close>
  unfolding fun_eq_iff
  by simp

lemma apfst_id'[simp]:
  \<open>apfst (\<lambda>x. x) = (\<lambda>x. x)\<close>
  by (simp add: fun_eq_iff)


ML_file \<open>library/tools/help_lemmas.ML\<close>

subsection \<open>Helper Attributes \& Tactics\<close>

attribute_setup rotated = \<open>Scan.lift (Scan.optional Parse.int 1 -- Scan.optional Parse.int 0) >>
  (fn (k,j) => Thm.rule_attribute [] (fn _ => Thm.permute_prems j k))\<close>
  \<open>Enhanced version of the Pure.rotated\<close>

attribute_setup TRY_THEN = \<open>(Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- Attrib.thm
      >> (fn (i, B) => Thm.rule_attribute [B] (fn _ => fn A => A RSN (i, B) handle THM _ => A)))
    \<close> "resolution with rule, and do nothing if fail"

ML \<open>
val phi_system_ML_attribute_locker_do_not_override = Mutex.mutex ()
val phi_system_ML_attribute_sender_do_not_override : (morphism -> Thm.attribute) option Unsynchronized.ref =
      Unsynchronized.ref NONE
fun phi_system_read_ML_attribute generic src =
  let val _ = Mutex.lock phi_system_ML_attribute_locker_do_not_override
      val _ =   ML_Context.expression (Input.pos_of src)
              ( ML_Lex.read "phi_system_ML_attribute_sender_do_not_override := SOME (("
              @ ML_Lex.read_source src
              @ ML_Lex.read ") : morphism -> Thm.attribute)") generic
            handle err => (
              Mutex.unlock phi_system_ML_attribute_locker_do_not_override;
              raise err)
      val attr = the (@{print} (!phi_system_ML_attribute_sender_do_not_override))
      val _ = Mutex.unlock phi_system_ML_attribute_locker_do_not_override;
  in attr
  end
val phi_system_ML_attribute_parser = (
   Scan.lift Args.internal_attribute
|| Scan.peek (fn ctxt => Parse.token Parse.ML_source >>
    Token.evaluate Token.Attribute (fn tok => 
let val src = Token.input_of tok
in Morphism.entity (phi_system_read_ML_attribute ctxt src)
end )))
\<close>

attribute_setup ML_attribute = \<open>
  phi_system_ML_attribute_parser >> Morphism.form\<close>
  \<open>Use ML directly in an attribute without defining a new attribute if you just
  want to use it here specifically\<close>


subsection \<open>Helper Objects\<close>

subsubsection \<open>Embedding Function into Relation\<close>

definition embedded_func :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  where \<open>embedded_func f P = (\<lambda>x y. y = f x \<and> P x)\<close>

lemma embedded_func_red[iff]:
  \<open> embedded_func f P x y \<longleftrightarrow> y = f x \<and> P x \<close>
  unfolding embedded_func_def
  by simp

subsubsection \<open>Big Number\<close>

text \<open>A tag to suppress unnecessary expanding of big numbers like \<open>2^256\<close>
  (*depreciated! use \<open>declare power_numeral[simp del]\<close> instead!*)\<close>

definition \<open>Big x = x\<close>

lemma [iff]:
  \<open>(2::nat) ^ Big 8  = 256\<close>
  \<open>(2::nat) ^ Big 16 = 65536\<close>
  \<open>(2::nat) ^ Big 32 = 4294967296\<close>
  by (simp add: Big_def)+

lemma [iff]:
  \<open> numeral x < (2::'a) ^ Big n \<longleftrightarrow> numeral x < (2::'a::{numeral,power,ord}) ^ n\<close>
  \<open> 1 < (2::'a) ^ Big n \<longleftrightarrow> 1 < (2::'a::{numeral,power,ord}) ^ n\<close>
  \<open> 0 < (2::'b) ^ Big n \<longleftrightarrow> 0 < (2::'b::{numeral,power,ord,zero}) ^ n\<close>
  \<open> n < 16 \<Longrightarrow> Big n = n \<close>
  unfolding Big_def by simp+

subsubsection \<open>Product\<close>

(*if C\<^sub>R\<^sub>1 then *)
setup \<open>Sign.mandatory_path "prod"\<close>

definition assoc :: \<open>'a \<times> 'b \<times> 'c \<Rightarrow> ('a \<times> 'b) \<times> 'c\<close>
  where \<open>assoc x = ((fst x, fst (snd x)), snd (snd x))\<close>

definition assoc\<^sub>R :: \<open>('a \<times> 'b) \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c\<close>
  where \<open>assoc\<^sub>R x = (fst (fst x), snd (fst x), snd x)\<close>

lemma assoc[simp]:
  \<open>prod.assoc (a,b,c) = ((a,b),c)\<close>
  \<open>prod.assoc\<^sub>R ((a,b),c) = (a,b,c)\<close>
  unfolding prod.assoc_def prod.assoc\<^sub>R_def
  by simp_all

lemma assoc_assoc\<^sub>R[simp]:
  \<open>prod.assoc (prod.assoc\<^sub>R x) = x\<close>
  \<open>prod.assoc\<^sub>R (prod.assoc y) = y\<close>
  unfolding prod.assoc_def prod.assoc\<^sub>R_def
  by simp_all

lemma assoc_prj[simp]:
  \<open>fst (fst (prod.assoc x)) = fst x\<close>
  \<open>snd (fst (prod.assoc x)) = fst (snd x)\<close>
  \<open>snd (prod.assoc x) = snd (snd x)\<close>
  \<open>fst (prod.assoc (a, bc)) = (a, fst bc) \<close>
  \<open>snd (snd (prod.assoc\<^sub>R y)) = snd y\<close>
  \<open>fst (snd (prod.assoc\<^sub>R y)) = snd (fst y)\<close>
  \<open>fst (prod.assoc\<^sub>R y) = fst (fst y)\<close>
  \<open>snd (prod.assoc\<^sub>R (ab, c)) = (snd ab, c)\<close>
  unfolding prod.assoc_def prod.assoc\<^sub>R_def
  by simp_all

lemma ap_assoc[simp]:
  \<open>apfst f_ab (prod.assoc\<^sub>R (ab, c)) = prod.assoc\<^sub>R (apfst f_ab ab, c)\<close>
  
  unfolding prod.assoc_def prod.assoc\<^sub>R_def
  by simp_all

lemma map_prod_assoc[simp]:
  \<open>map_prod (map_prod g\<^sub>1 g\<^sub>2) g\<^sub>3 (prod.assoc x) = prod.assoc (map_prod g\<^sub>1 (map_prod g\<^sub>2 g\<^sub>3) x)\<close>
  \<open>map_prod f\<^sub>1 (map_prod f\<^sub>2 f\<^sub>3) (prod.assoc\<^sub>R y) = prod.assoc\<^sub>R (map_prod (map_prod f\<^sub>1 f\<^sub>2) f\<^sub>3 y)\<close>
  unfolding prod.assoc\<^sub>R_def prod.assoc_def
  by simp_all

lemma assoc_eq_simp[simp]:
  \<open>((a,b),c) = prod.assoc x \<longleftrightarrow> (a,b,c) = x\<close>
  \<open>(a,b,c) = prod.assoc\<^sub>R y \<longleftrightarrow> ((a,b),c) = y\<close>
  unfolding prod.assoc_def prod.assoc\<^sub>R_def
  by (clarsimp; rule; clarsimp)+

setup \<open>Sign.parent_path\<close>

lemma map_prod_eq_apfst_apsnd:
  \<open>map_prod f g = apfst f o apsnd g\<close>
  unfolding fun_eq_iff
  by clarsimp

lemma map_prod_eq_apsnd_apfst:
  \<open>map_prod f g = apsnd g o apfst f\<close>
  unfolding fun_eq_iff
  by clarsimp


subsection \<open>Helper Conversion\<close>

definition \<open>PURE_TOP \<equiv> (\<And>P::prop. PROP P \<Longrightarrow> PROP P)\<close>

lemma PURE_TOP_I[\<phi>reason 1000]: \<open>PROP PURE_TOP\<close> unfolding PURE_TOP_def .

lemma PURE_TOP_imp:
  \<open>(PROP PURE_TOP \<Longrightarrow> PROP P) \<equiv> PROP P\<close> (is \<open>PROP ?LHS \<equiv> PROP ?RHS\<close>)
proof
  assume \<open>PROP ?LHS\<close>
  from this[OF PURE_TOP_I] show \<open>PROP ?RHS\<close> .
next
  assume \<open>PROP ?RHS\<close>
  then show \<open>PROP ?LHS\<close> .
qed

ML_file \<open>library/syntax/helper_conv.ML\<close>

subsection \<open>Helper Simplification\<close>

simproc_setup Funcomp_Lambda (\<open>f o g\<close>) = \<open>fn _ => fn ctxt => fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Fun.comp\<close>, _) $ Abs _ $ _ =>
        SOME (Conv.rewr_conv @{thm' comp_def[folded atomize_eq]} ctm)
     | Const(\<^const_name>\<open>Fun.comp\<close>, _) $ _ $ Abs _ =>
        SOME (Conv.rewr_conv @{thm' comp_def[folded atomize_eq]} ctm)
     | _ => NONE
\<close>

subsection \<open>Helper Isar Commands\<close>

declare [[ML_debugger=false, ML_exception_debugger=false]]

ML_file \<open>library/tools/optional_translation.ML\<close>
ML_file \<open>library/tools/adhoc_overloading.ML\<close>

declare [[ML_debugger, ML_exception_debugger]]


subsection \<open>The Friendly Character\<close>

ML_file \<open>library/tools/the_friendly_character.ML\<close>

definition Friendly_Help :: \<open>text \<Rightarrow> bool\<close> where [iff]: \<open>Friendly_Help _ \<longleftrightarrow> True\<close>

lemma Friendly_Help_I[intro!]: \<open>Friendly_Help ANY\<close> unfolding Friendly_Help_def ..
lemma Friendly_Help_E[elim!]: \<open>Friendly_Help ANY \<Longrightarrow> C \<Longrightarrow> C\<close> .

(*TODO: move this to \<phi>lang_parser so that the help is displayed only when the IDECP ends at that*)

\<phi>reasoner_ML Friendly_Help 1000 (\<open>Friendly_Help _\<close>) = \<open>fn (_, (ctxt,sequent)) =>
 (if Config.get ctxt Phi_The_Friendly_Character.enable
  then let
        val _ $ (_ $ text) = Thm.major_prem_of sequent
        val pretty = Text_Encoding.decode_text_pretty ctxt text
       in Phi_The_Friendly_Character.info ctxt (fn _ => pretty) end
  else ();
  Seq.single (ctxt, @{thm Friendly_Help_I} RS sequent)
 )
\<close>

subsection \<open>General Reasoning Rules\<close>

declare refl[\<phi>reason 1000]

subsubsection \<open>pred_option\<close>

lemma [\<phi>reason 1000]:
  \<open> P x
\<Longrightarrow> pred_option P (Some x)\<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> pred_option P None\<close>
  by simp

subsection \<open>Some very Early Reasoning\<close>



(*

declare (* disjE[\<phi>inhabitance_rule] *) (*I don't like divergence!*)
        conjE[\<phi>inhabitance_rule]
        set_mult_inhabited[\<phi>inhabitance_rule]
        set_plus_inhabited[\<phi>inhabitance_rule]

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited 1 \<Longrightarrow> C \<Longrightarrow> C\<close> .*)

(*TODO:
lemma Membership_E_Inhabitance:
  \<open>x \<in> S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by blast*)



subsubsection \<open>Supplementary of Meta-Ball\<close>

lemma [\<phi>reason %meta_ball]:
  \<open> (Q \<Longrightarrow> (\<And>x \<in> S. PROP P x))
\<Longrightarrow> (\<And>x \<in> S \<s>\<u>\<b>\<j> Q. PROP P x)\<close>
  unfolding meta_Ball_def Premise_def Subjection_expn_set
  by (clarsimp simp add: atomize_conj[symmetric] conjunction_imp norm_hhf_eq)

lemma [\<phi>reason %meta_ball]:
  \<open> (Q \<Longrightarrow> \<forall>x \<in> S. P x)
\<Longrightarrow> (\<forall>x \<in> S \<s>\<u>\<b>\<j> Q. P x)\<close>
  unfolding Ball_def Subjection_expn_set
  by simp




subsection \<open>Very Early Mechanism\<close>

\<phi>reasoner_group local = (10000, [10000,10000])
  \<open>local reasoning rules given from the hypothese of a programming context\<close>

subsubsection \<open>Default Attributes in Programming\<close>

text \<open>Registry of default attributes of antecedents in the deductive programming.\<close>

ML_file \<open>library/system/premise_attribute.ML\<close>

paragraph \<open>Configuring Existing Antecedents\<close>

declare [[
  \<phi>premise_attribute? [\<phi>declare] for \<open>PROP _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Is_Literal _\<close>,

  \<phi>premise_attribute_ML \<open>fn _ => Thm.declaration_attribute (fn thm => fn ctxt =>
    let val term_A = case Thm.prop_of thm
                       of _ $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ _ ) => A
                        | _ $ (Const(\<^const_name>\<open>Simplify\<close>, _) $ _ $ A $ _ ) => A
        val cterm_A = Context.cases Thm.global_cterm_of Thm.cterm_of ctxt term_A
        val rule = \<^instantiate>\<open>cterm_A and 'a=\<open>Thm.ctyp_of_cterm cterm_A\<close> in
                                  lemma \<open>Is_Literal (cterm_A::'a)\<close> by (simp add: Is_Literal_def)\<close>
     in Phi_Reasoner.add_rule Position.none Phi_Reasoner.NORMAL_LOCAL_CUT' (SOME @{reasoner_group %is_literal})
            ([(Thm.concl_of rule, NONE)], []) NONE [rule] ctxt
    end
    handle MATCH => ctxt
  )\<close> for \<open>Simplify \<phi>mode_literal _ _\<close>
]]


subsection \<open>Convention of Syntax Priority\<close>


text \<open>
\<^item> 10: Labelled, Programming_CurrentConstruction, View_Shift_CurrentConstruction
      PendingConstruction, ToA_Construction, Argument tag
\<^item> 12: View_Shift, Transformation
\<^item> 13: Remains
\<^item> 14: ExSet
\<^item> 15: Comma, Subjection
\<^item> 16: Struct Tag, SYNTHESIS
\<^item> 18: Assertion_Matches
\<^item> 20: \<phi>-type colon
\<close>


(*TODO: Move this*)
end
