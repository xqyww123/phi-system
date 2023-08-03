chapter \<open>Theoretical Foundations\<close>

section \<open>Preliminary\<close>

theory Phi_Preliminary
  imports Main "Phi_Algebras.Algebras"
          Phi_Logic_Programming_Reasoner.Phi_Logic_Programming_Reasoner
          Phi_Logic_Programming_Reasoner.PLPR_error_msg
  keywords "optional_translations" :: thy_decl
       and "\<phi>adhoc_overloading" "\<phi>no_adhoc_overloading" :: thy_decl
  abbrevs "<implies>" = "\<i>\<m>\<p>\<l>\<i>\<e>\<s>"
begin

declare [ [ML_debugger, ML_exception_debugger]]

subsection \<open>Named Theorems\<close>

ML \<open>structure Phi_Expansions = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>expns\<close>
  val comment = "Semantics Expansions, used to expand assertions semantically."
)\<close>

declare set_mult_expn[\<phi>expns] Premise_def[\<phi>expns]

ML \<open>
structure Phi_Programming_Simp_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>\<phi>programming_simps\<close>
  val comment = "Simplification rules used in low automation level, which is safer than usual"
)

structure Phi_Programming_Unsafe_Simp_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>programming_unsafe_simps\<close>
  val comment = "Simplification rules used in the deductive programming"
)
\<close>

lemmas [\<phi>programming_simps] =
  mult_zero_right[where 'a=\<open>'a::sep_magma set\<close>] mult_zero_left[where 'a=\<open>'a::sep_magma set\<close>]
  mult_1_right[where 'a=\<open>'a::sep_magma_1 set\<close>] mult_1_left[where 'a=\<open>'a::sep_magma_1 set\<close>]
  add_0_right[where 'a=\<open>'a::sep_magma set\<close>] add_0_left[where 'a=\<open>'a::sep_magma set\<close>]
  zero_fun HOL.simp_thms

subsection \<open>Error Mechanism\<close>

ML_file \<open>library/tools/error.ML\<close>

subsection \<open>Helper ML\<close>

ML_file \<open>library/tools/Phi_Help.ML\<close>
ML_file \<open>library/syntax/helps.ML\<close>
ML_file \<open>library/system/Phi_Envir0.ML\<close>
ML_file \<open>library/system/Phi_ID.ML\<close>
ML_file \<open>library/tools/cache_file.ML\<close>

ML_file \<open>library/tools/Hasher.ML\<close>


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

subsection \<open>Helper Lemmas\<close>

lemma imp_implication: "(P \<longrightarrow> Q \<Longrightarrow> PROP R) \<equiv> ((P \<Longrightarrow> Q) \<Longrightarrow> PROP R)" by rule simp+

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
in phi_system_read_ML_attribute ctxt src
end )))
\<close>

attribute_setup ML_attribute = \<open>
  phi_system_ML_attribute_parser >> Morphism.form\<close>
  \<open>Use ML directly in an attribute without defining a new attribute if you just
  want to use it here specifically\<close>


subsection \<open>Helper Objects\<close>

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

subsection \<open>Helper Methods\<close>

ML_file \<open>library/tools/where_tac.ML\<close>

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

(*TODO: move this to \<phi>processor so that the help is displayed only when the IDECP ends at that*)

\<phi>reasoner_ML Friendly_Help 1000 (\<open>Friendly_Help _\<close>) = \<open>fn (ctxt,sequent) =>
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

subsubsection \<open>Inhabitance Reasoning - Part I\<close>

definition Generate_Implication_Reasoning :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Generate_Implication_Reasoning IN OUT_L OUT_R \<longleftrightarrow> (IN \<longrightarrow> OUT_L \<longrightarrow> OUT_R)\<close>

consts \<A>EIF :: action \<comment> \<open>Extract Implied Facts\<close>

declare [[
  \<phi>reason_default_pattern \<open>Generate_Implication_Reasoning ?I _ _\<close>
                        \<Rightarrow> \<open>Generate_Implication_Reasoning ?I _ _\<close> (100)
  and \<open>?X \<longrightarrow> _ @action \<A>EIF\<close>
   \<Rightarrow> \<open>?X \<longrightarrow> _ @action \<A>EIF\<close> (100)
  and \<open>_ @action \<A>EIF\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>bad form\<close>)\<close> (10)
]]

lemma Do_Generate_Implication_Reasoning:
  \<open> IN
\<Longrightarrow> Generate_Implication_Reasoning IN OUT_L OUT_R
\<Longrightarrow> OUT_R \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> \<r>Success
\<Longrightarrow> OUT_L \<longrightarrow> C\<close>
  unfolding Generate_Implication_Reasoning_def Action_Tag_def
  by blast

lemma Do_Extract_Implied_Facts:
  \<open> P
\<Longrightarrow> P \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> C\<close>
  unfolding Action_Tag_def
  by blast

(* ML_file \<open>library/tools/elimination_rule.ML\<close> *)

lemma [\<phi>reason 1000]:
  \<open> Generate_Implication_Reasoning P OL OR
\<Longrightarrow> Generate_Implication_Reasoning (P @action A) OL OR\<close>
  unfolding Generate_Implication_Reasoning_def Action_Tag_def .

lemma [\<phi>reason 1000]:
  \<open> A \<longrightarrow> A' @action \<A>EIF
\<Longrightarrow> B \<longrightarrow> B' @action \<A>EIF
\<Longrightarrow> A \<and> B \<longrightarrow> A' \<and> B' @action \<A>EIF \<close>
  unfolding Action_Tag_def by blast

lemma Extact_implied_facts_Iden[\<phi>reason default 1]:
  \<open> A \<longrightarrow> A @action \<A>EIF \<close>
  unfolding Action_Tag_def by blast

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



subsubsection \<open>Meta Ball\<close>

definition meta_Ball :: \<open>'a set \<Rightarrow> ('a \<Rightarrow> prop) \<Rightarrow> prop\<close>
  where \<open>meta_Ball S P \<equiv> (\<And>x. \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> S \<Longrightarrow> PROP P x)\<close>

lemma meta_Ball_D:
  \<open> (\<And>x. \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> S \<Longrightarrow> PROP P x)
\<Longrightarrow> PROP meta_Ball S P\<close>
  unfolding meta_Ball_def .

definition meta_case_prod :: \<open>('a \<Rightarrow> 'b \<Rightarrow> prop) \<Rightarrow> ('a \<times> 'b \<Rightarrow> prop)\<close>
  where \<open>meta_case_prod f \<equiv> (\<lambda>x. f (fst x) (snd x))\<close>

lemma meta_case_prod_simp[iff]:
  \<open>meta_case_prod f (x,y) \<equiv> f x y\<close>
  unfolding meta_case_prod_def by simp

thm prod.case[folded atomize_eq]

syntax
  "_meta_Ball" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> prop \<Rightarrow> prop" ("(3\<And>(_/\<in>_)./ _)" [0, 0, 0] 0)

translations
  ("aprop") "_meta_Ball x A P" \<rightleftharpoons> ("aprop") "CONST meta_Ball A (\<lambda>x. P)"
  ("aprop") "CONST meta_Ball A (\<lambda>(x,y,zs). P)" \<rightleftharpoons> ("aprop") "CONST meta_Ball A (CONST meta_case_prod (\<lambda>x (y, zs). P))"
  ("aprop") "CONST meta_Ball A (\<lambda>(x,y). P)" \<rightleftharpoons> ("aprop") "CONST meta_Ball A (CONST meta_case_prod (\<lambda>x y. P))"
  ("aprop") "CONST meta_case_prod (\<lambda>x (y,z,zs). P)" \<rightleftharpoons> ("aprop") "CONST meta_case_prod (\<lambda>x. CONST meta_case_prod (\<lambda>y (z,zs). P))"
  ("aprop") "CONST meta_case_prod (\<lambda>x (y,zs). P)" \<rightleftharpoons> ("aprop") "CONST meta_case_prod (\<lambda>x. CONST meta_case_prod (\<lambda>y zs. P))"

lemma meta_Ball_sing[simp]:
  \<open> (\<And>x \<in> {y}. PROP P x) \<equiv> PROP P y \<close>
  unfolding meta_Ball_def Premise_def by simp

lemma Ball_for_reason:
  \<open>Trueprop (Ball A P) \<equiv> (\<And>x. \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> A \<Longrightarrow> P x)\<close>
  unfolding atomize_imp atomize_all Ball_def Premise_def .

lemma [\<phi>reason 1000]:
  \<open> PROP P y
\<Longrightarrow> (\<And>x \<in> {y}. PROP P x)\<close>
  unfolding meta_Ball_def Premise_def by simp

lemma [\<phi>reason 1000]:
  \<open> P y
\<Longrightarrow> (\<forall>x \<in> {y}. P x)\<close>
  by simp

lemma meta_Ball_pair[\<phi>reason 1010]:
  \<open> (\<And>y \<in> {y}. PROP P x y)
\<Longrightarrow> (\<And>(x,y) \<in> {(x,y)}. PROP P x y)\<close>
  unfolding meta_Ball_def meta_case_prod_def Premise_def by simp

lemma [\<phi>reason 1010]:
  \<open> (\<forall>y \<in> {y}. P x y)
\<Longrightarrow> (\<forall>(x,y) \<in> {(x,y)}. P x y) \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> (Q \<Longrightarrow> (\<And>x \<in> S. PROP P x))
\<Longrightarrow> (\<And>x \<in> S \<s>\<u>\<b>\<j> Q. PROP P x)\<close>
  unfolding meta_Ball_def Premise_def Subjection_expn_set
  by (clarsimp simp add: atomize_conj[symmetric] conjunction_imp norm_hhf_eq)

lemma [\<phi>reason 1000]:
  \<open> (Q \<Longrightarrow> \<forall>x \<in> S. P x)
\<Longrightarrow> (\<forall>x \<in> S \<s>\<u>\<b>\<j> Q. P x)\<close>
  unfolding Ball_def Subjection_expn_set
  by simp

lemma sing_times_sing:
  \<open>{a} \<times> {b} = {(a,b)}\<close>
  unfolding set_eq_iff
  by simp

lemma sing_if:
  \<open>(if c then {a} else {b}) = {if c then a else b}\<close>
  by simp

ML_file \<open>library/tools/case_prod_conv.ML\<close>

\<phi>reasoner_ML meta_case_prod_in_meta_Ball !1 (\<open>PROP meta_Ball _ _\<close>) = \<open>
  fn (ctxt,sequent) => Seq.make (fn () =>
  let val sequent' = Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                Conv.rewr_conv @{thm meta_Ball_def} then_conv
                Phi_Conv.prod_case_meta_all_split_conv (K Conv.all_conv) ctxt
            ) ctxt) 1 sequent
   in SOME ((ctxt, sequent'), Seq.empty)
  end)
\<close>

\<phi>reasoner_ML case_prod_in_Ball !1 (\<open>Ball _ _\<close>) = \<open>
  fn (ctxt,sequent) => Seq.make (fn () =>
  let val sequent' = Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                Conv.rewr_conv @{thm Ball_for_reason} then_conv
                Phi_Conv.prod_case_meta_all_split_conv (K Conv.all_conv) ctxt
            ) ctxt) 1 sequent
   in SOME ((ctxt, sequent'), Seq.empty)
  end)
\<close>

hide_fact Ball_for_reason




subsection \<open>Very Early Mechanism\<close>

subsubsection \<open>Default Attributes in Programming\<close>

text \<open>Registry of default attributes of antecedents in the deductive programming.\<close>

ML_file \<open>library/system/premise_attribute.ML\<close>


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
