(*TODO: it is possible and would be good if we separate the entire system into a pure BI logic with reasoning,
  and that applied over a semantic framework together with IDE-CP, but I have no time now.
*)

chapter \<open>Specification Framework\<close>

theory Spec_Framework
  imports Phi_BI "Phi_Semantics_Framework.Phi_Semantics_Framework"
  keywords "fiction_space"  :: thy_goal
  abbrevs "<shifts>" = "\<s>\<h>\<i>\<f>\<t>\<s>"
    and   "<val>" = "\<v>\<a>\<l>"
    and   "<vals>" = "\<v>\<a>\<l>\<s>"
begin

subsubsection \<open>Configuration\<close>

declare [[\<phi>reason_default_pattern \<open>Valid_Proc ?F\<close> \<Rightarrow> \<open>Valid_Proc ?F\<close> (100)]]
declare Valid_Proc_bind[\<phi>reason 1200]
declare \<phi>arg.simps[\<phi>safe_simp] \<phi>arg.sel[\<phi>safe_simp]


section \<open>Fiction\<close>

unspecified_type FIC
unspecified_type FIC_N

type_synonym fiction = \<open>FIC_N \<Rightarrow> FIC\<close>
type_synonym assn = \<open>fiction set\<close>
type_synonym rassn = \<open>resource set\<close>
type_synonym 'T fiction_entry = "(FIC_N, FIC, 'T) Resource_Space.kind"

setup \<open>Sign.mandatory_path "FIC"\<close>

consts DOMAIN :: \<open>FIC_N \<Rightarrow> FIC sep_homo_set\<close>

debt_axiomatization sort: \<open>OFCLASS(FIC, sep_algebra_class)\<close>

setup \<open>Sign.parent_path\<close>

instance FIC :: sep_algebra using FIC.sort .

instantiation FIC :: sep_carrier_1 begin
definition mul_carrier_FIC :: \<open>FIC \<Rightarrow> bool\<close> where \<open>mul_carrier_FIC = (\<lambda>_. True)\<close>
  \<comment> \<open>As a type specially defined to represent the representation of fictions, it can be noisy-free.\<close>
instance by (standard; simp add: mul_carrier_FIC_def)
end

consts INTERPRET :: \<open>FIC_N \<Rightarrow> (FIC, resource) unital_homo_interp\<close>

interpretation FIC: fictional_space FIC.DOMAIN INTERPRET .

definition "INTERP_RES fic \<equiv> RES.SPACE \<inter> {_. fic \<in> FIC.SPACE } \<inter> FIC.INTERP fic"
  \<comment> \<open>Interpret a fiction\<close>

lemma In_INTERP_RES:
  \<open>r \<in> INTERP_RES fic \<longleftrightarrow> r \<in> RES.SPACE \<and> fic \<in> FIC.SPACE \<and> r \<in> FIC.INTERP fic\<close>
  unfolding INTERP_RES_def by simp

definition INTERP_SPEC :: \<open>assn \<Rightarrow> rassn\<close>
  \<comment> \<open>Interpret a fictional specification\<close>
  where "INTERP_SPEC T = { res. \<exists>fic. fic \<in> T \<and> res \<in> INTERP_RES fic }"

lemma INTERP_SPEC:
  \<open>res \<in> INTERP_SPEC T \<longleftrightarrow> (\<exists>fic. fic \<Turnstile> T \<and> res \<in> INTERP_RES fic)\<close>
  unfolding INTERP_SPEC_def Satisfaction_def
  by simp

lemma INTERP_SPEC_subset[intro, simp]: \<open>A \<subseteq> B \<Longrightarrow> INTERP_SPEC A \<subseteq> INTERP_SPEC B\<close>
  unfolding INTERP_SPEC_def subset_iff by simp blast

lemma INTERP_SPEC_plus[iff]:
  \<open>INTERP_SPEC (A + B) = INTERP_SPEC A + INTERP_SPEC B\<close>
  unfolding INTERP_SPEC_def plus_set_def by simp blast

lemma INTERP_SPEC_empty[intro, simp]:
  \<open>S = {} \<Longrightarrow> INTERP_SPEC S = {}\<close>
  unfolding INTERP_SPEC_def set_eq_iff by simp

lemma INTERP_SPEC_0[simp]:
  \<open>INTERP_SPEC 0  = 0\<close>
  \<open>INTERP_SPEC {} = {}\<close>
  unfolding INTERP_SPEC_def zero_set_def by simp+

ML_file \<open>library/spec_framework/fiction_space.ML\<close>
ML_file \<open>library/spec_framework/fiction_space_more.ML\<close>

ML \<open>Fiction_Space.define_command \<^command_keyword>\<open>fiction_space\<close> "extend fictions"\<close>

(*
lemma INTERP_mult:
  \<open> Fic_Space f1
\<Longrightarrow> Fic_Space f2
\<Longrightarrow> dom1 r1 \<inter> dom1 r2 = {}
\<Longrightarrow> dom1 f1 \<inter> dom1 f2 = {}
\<Longrightarrow> r1 \<in> \<I> INTERP f1
\<Longrightarrow> r2 \<in> \<I> INTERP f2
\<Longrightarrow> f1 ## f2
\<Longrightarrow> r1 * r2 \<in> \<I> INTERP (f1 * f2) \<and> r1 ## r2\<close>
  unfolding INTERP_def Fic_Space_def
  by (simp add: dom1_sep_mult_disjoint times_fun prod.union_disjoint
                disjoint_dom1_eq_1[of f1 f2],
      meson dom1_disjoint_sep_disj times_set_I) *)


section \<open>Specification of Value\<close>

type_synonym vassn = \<open>VAL BI\<close>

subsection \<open>Primitive \<phi>-Types\<close>

subsubsection \<open>Value\<close>

definition Val :: \<open>VAL \<phi>arg \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> ('x::one, 'a) \<phi>\<close> ("\<v>\<a>\<l>[_] _" [22,22] 21)
  where \<open>Val val T = (\<lambda>x. 1 \<s>\<u>\<b>\<j> \<phi>arg.dest val \<Turnstile> (x \<Ztypecolon> T))\<close>

definition Vals :: \<open>VAL list \<phi>arg \<Rightarrow> (VAL list, 'a) \<phi> \<Rightarrow> ('x::one, 'a) \<phi>\<close> ("\<v>\<a>\<l>\<s>[_] _" [22,22] 21)
  where \<open>Vals vals T = (\<lambda>x. 1 \<s>\<u>\<b>\<j> \<phi>arg.dest vals \<Turnstile> (x \<Ztypecolon> T))\<close>

lemma Val_expn [simp, \<phi>expns]:
  \<open>v \<Turnstile> (x \<Ztypecolon> Val val T) \<longleftrightarrow> v = 1 \<and> \<phi>arg.dest val \<Turnstile> (x \<Ztypecolon> T)\<close>
  unfolding Val_def \<phi>Type_def by simp

lemma Vals_expn [simp, \<phi>expns]:
  \<open>v \<Turnstile> (x \<Ztypecolon> Vals val T) \<longleftrightarrow> v = 1 \<and> \<phi>arg.dest val \<Turnstile> (x \<Ztypecolon> T)\<close>
  unfolding Vals_def \<phi>Type_def by simp

lemma Val_inh_rewr:
  \<open>Inhabited (x \<Ztypecolon> Val val T) \<equiv> \<phi>arg.dest val \<Turnstile> (x \<Ztypecolon> T)\<close>
  unfolding Inhabited_def by clarsimp

lemma Vals_inh_rewr:
  \<open>Inhabited (x \<Ztypecolon> Vals val T) \<equiv> \<phi>arg.dest val \<Turnstile> (x \<Ztypecolon> T)\<close>
  unfolding Inhabited_def by clarsimp


paragraph \<open>Syntax\<close>

consts anonymous :: 'a

syntax val_syntax  :: "logic \<Rightarrow> logic" ("\<v>\<a>\<l> _"  [22] 21)
       vals_syntax :: "logic \<Rightarrow> logic" ("\<v>\<a>\<l>\<s> _" [22] 21)

translations
  "\<v>\<a>\<l> x \<Ztypecolon> T" => "x \<Ztypecolon> CONST Val (CONST anonymous) T"
  "\<v>\<a>\<l> T" => "CONST Val (CONST anonymous) T"
  "\<v>\<a>\<l>\<s> x \<Ztypecolon> T" => "x \<Ztypecolon> CONST Vals (CONST anonymous) T"
  "\<v>\<a>\<l>\<s> T" => "CONST Vals (CONST anonymous) T"

ML_file \<open>library/syntax/value.ML\<close>


subsubsection \<open>Abnormal\<close>

definition AbnormalObj :: \<open>VAL \<phi>arg \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> ('x::one, 'a) \<phi>\<close>
  where \<open>AbnormalObj \<equiv> Val\<close>

(*TODO: more about exception

Any exception object will be specified by this type. and by this we clarify the difference
between a value and an exception object.
Then in exception specs, any Val is senseless and will be removed.*)


subsection \<open>Semantic Type\<close>

subsubsection \<open>Single Value\<close>

definition \<phi>SemType :: "vassn \<Rightarrow> TY \<Rightarrow> bool"
  where \<open>\<phi>SemType S TY \<longleftrightarrow> (\<forall>v. v \<Turnstile> S \<longrightarrow> v \<in> Well_Type TY)\<close>
  \<comment> \<open>Values specified by \<open>S\<close> are all of semantic type \<open>TY\<close>.\<close>

(*definition \<phi>\<phi>SemType :: "(VAL, 'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> TY) \<Rightarrow> bool"
  where \<open>\<phi>\<phi>SemType T D TY \<equiv> (\<forall>x. D x \<longrightarrow> \<phi>SemType (x \<Ztypecolon> T) (TY x))\<close>*)

declare [[
  \<phi>reason_default_pattern \<open>\<phi>SemType ?S _\<close> \<Rightarrow> \<open>\<phi>SemType ?S _\<close> (100)
]]

\<phi>reasoner_group \<phi>sem_type = (100, [0, 3000]) for (\<open>\<phi>SemType S TY\<close>)
      \<open>giving the semantic type of the concrete value satisfying the given assertion or \<phi>-type\<close>
  and \<phi>sem_type_fail = (0, [0,0]) in \<phi>sem_type
      \<open>failures\<close>
  and \<phi>sem_type_brute = (2, [2,2]) in \<phi>sem_type > \<phi>sem_type_fail
      \<open>reducing to concrete level, used only when deriving rules.\<close>
  and \<phi>sem_type_assertion = (10, [10,10]) in \<phi>sem_type and > \<phi>sem_type_brute
      \<open>asserting the given with a semantic type if any\<close>
(*and \<phi>sem_type_\<phi>typ = (10, [10,10]) in \<phi>sem_type and > \<phi>sem_type_fail
      \<open>\<open>\<phi>SemType\<close> -> \<open>\<phi>\<phi>SemType\<close>\<close>*)
  and \<phi>sem_type_derived = (50, [50,50]) in \<phi>sem_type and > \<phi>sem_type_assertion
      \<open>derived rules\<close>
  and \<phi>sem_type_cut = (1000, [1000,1030]) in \<phi>sem_type and > \<phi>sem_type_derived
      \<open>cutting rules\<close>
  and \<phi>sem_type_red = (2200, [2200,2500]) in \<phi>sem_type and > \<phi>sem_type_cut
      \<open>reduction and evaluation\<close>

(*lemma \<phi>SemType_unique:
  \<open> S \<noteq> {}
\<Longrightarrow> \<phi>SemType S T1
\<Longrightarrow> \<phi>SemType S T2
\<Longrightarrow> T1 = T2\<close>
  unfolding \<phi>SemType_def subset_iff
  using Well_Type_unique by blast *)

(* definition SemTyp_Of :: \<open>VAL set \<Rightarrow> TY\<close>
  where \<open>SemTyp_Of S = (@TY. \<phi>SemType S TY)\<close>

lemma SemTyp_Of_I[intro!, simp]:
  \<open>S \<noteq> {} \<Longrightarrow> \<phi>SemType S TY \<Longrightarrow> SemTyp_Of S = TY\<close>
  unfolding SemTyp_Of_def
  using \<phi>SemType_unique by blast *)

(*

lemma [\<phi>reason 100]:
  \<open> (\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY)
\<Longrightarrow> \<phi>\<phi>SemType T TY\<close>
  .. *)

paragraph \<open>Basic Rules\<close>

lemma [\<phi>reason default %\<phi>sem_type_fail]:
  \<open>FAIL TEXT(\<open>Fail to reason the semantic type of\<close> X)
\<Longrightarrow> \<phi>SemType X Any\<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason default %\<phi>sem_type_assertion except \<open>\<phi>SemType _ ?var\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<Longrightarrow> \<phi>SemType A TY')
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<or>\<^sub>c\<^sub>u\<^sub>t ERROR TEXT(\<open>expecting\<close> A \<open>of semantic type\<close> TY \<open>but actually of\<close> TY')
\<Longrightarrow> \<phi>SemType A TY \<close>
  unfolding Premise_def Orelse_shortcut_def ERROR_def
  by blast

lemma [\<phi>reason %\<phi>sem_type_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> v \<in> Well_Type TY
\<Longrightarrow> \<phi>SemType (v \<Ztypecolon> Itself) TY \<close>
  unfolding Premise_def \<phi>SemType_def subset_iff
  by simp

lemma \<phi>SemType_Itself_brute:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type TY
\<Longrightarrow> \<phi>SemType (v \<Ztypecolon> Itself) TY \<close>
  unfolding Premise_def \<phi>SemType_def subset_iff
  by simp

lemma \<phi>sem_type_by_sat:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>v. v \<Turnstile> S \<longrightarrow> v \<in> Well_Type TY)
\<Longrightarrow> \<phi>SemType S TY \<close>
  unfolding Premise_def \<phi>SemType_def \<r>Guard_def .

lemma \<phi>sem_type_brute_EIF:
  \<open> \<r>EIF (\<phi>SemType S TY) (\<forall>v. v \<Turnstile> S \<longrightarrow> v \<in> Well_Type TY) \<close>
  unfolding \<r>EIF_def \<phi>SemType_def
  by blast

bundle \<phi>sem_type_sat_EIF = \<phi>sem_type_by_sat[\<phi>reason default %\<phi>sem_type_brute]
                           \<phi>sem_type_brute_EIF[\<phi>reason %extract_pure]
                           \<phi>SemType_Itself_brute[\<phi>reason %\<phi>sem_type_cut+10]


paragraph \<open>Over Logic Connectives\<close>

lemma [\<phi>reason %\<phi>sem_type_cut]:
  \<open> \<phi>SemType X TY1
\<Longrightarrow> \<phi>SemType Y TY2
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> TY1 = TY2
\<Longrightarrow> \<phi>SemType (X + Y) TY1\<close>
  unfolding \<phi>SemType_def subset_iff Premise_def
  by simp

lemma [\<phi>reason %\<phi>sem_type_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<longrightarrow> \<phi>SemType X TY
\<Longrightarrow> \<phi>SemType (X \<s>\<u>\<b>\<j> P) TY\<close>
  unfolding \<phi>SemType_def subset_iff
  by simp

lemma [\<phi>reason %\<phi>sem_type_cut]:
  \<open> (\<And>x. \<phi>SemType (X x) TY)
\<Longrightarrow> \<phi>SemType (ExSet X) TY\<close>
  unfolding \<phi>SemType_def subset_iff by clarsimp


subsubsection \<open>Reduction \& Evaluation\<close>

lemma [\<phi>reason %\<phi>sem_type_red]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (fst (x,y) \<Ztypecolon> T) TY \<close>
  by simp

lemma [\<phi>reason %\<phi>sem_type_red]:
  \<open> \<phi>SemType (y \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (snd (x,y) \<Ztypecolon> T) TY \<close>
  by simp

lemma [\<phi>reason %\<phi>sem_type_red]:
  \<open> \<phi>SemType ((f x, y) \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (apfst f (x,y) \<Ztypecolon> T) TY \<close>
  by simp

lemma [\<phi>reason %\<phi>sem_type_red]:
  \<open> \<phi>SemType ((x, f y) \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (apsnd f (x,y) \<Ztypecolon> T) TY \<close>
  by simp


subsubsection \<open>Multiple Values\<close>

definition Well_Typed_Vals :: \<open>TY list \<Rightarrow> 'a::VALs \<phi>arg set\<close>
  where \<open>Well_Typed_Vals TYs = {vs. list_all2 (\<lambda>v T. v \<in> Well_Type T) (to_vals (\<phi>arg.dest vs)) TYs}\<close>

definition \<phi>_Have_Types :: \<open>('a::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> TY list \<Rightarrow> bool\<close>
  where \<open>\<phi>_Have_Types spec TYs = (\<forall>v. Inhabited (spec v) \<longrightarrow> v \<in> Well_Typed_Vals TYs)\<close>

declare [[\<phi>reason_default_pattern \<open>\<phi>_Have_Types ?S _\<close> \<Rightarrow> \<open>\<phi>_Have_Types ?S _\<close> (100)]]




subsection \<open>Zero Value\<close>

definition Semantic_Zero_Val :: "TY \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool"
  where "Semantic_Zero_Val ty T x \<longleftrightarrow> (\<exists>v. Zero ty = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T))"

declare [[\<phi>reason_default_pattern \<open>Semantic_Zero_Val _ ?T _\<close> \<Rightarrow> \<open>Semantic_Zero_Val _ ?T _\<close> (100) ]]

\<phi>reasoner_group semantic_zero_val_all = (100, [0, 3000]) for \<open>Semantic_Zero_Val TY T x\<close>
    \<open>giving the semantic zero value on the abstraction side\<close>
  and semantic_zero_val_fail = (0, [0,0]) in semantic_zero_val_all
    \<open>failure\<close>
  and semantic_zero_val_brute = (1, [1,1]) in semantic_zero_val_all and > semantic_zero_val_fail
    \<open>reducing to semantic level, only used in deriving rules\<close>
  and semantic_zero_val_cut = (1000, [1000, 1000]) in semantic_zero_val_all and > semantic_zero_val_brute
    \<open>cutting rules\<close>
  and semantic_zero_val_derived = (50, [50,50]) in semantic_zero_val_all and < semantic_zero_val_cut
    \<open>derived rules\<close>

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason default %semantic_zero_val_fail]:
  \<open> FAIL TEXT(\<open>Don't know any semantic zero value satisfying \<phi>-type\<close> T)
\<Longrightarrow> Semantic_Zero_Val TY T x \<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> Abstract_Domain T P
\<Longrightarrow> \<r>EIF (Semantic_Zero_Val TY T x) (P x) \<close>
  unfolding Abstract_Domain_def Semantic_Zero_Val_def \<r>EIF_def Inhabited_def
  by blast

(*lemma Semantic_Zero_Val_brute:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<exists>v. Zero TY = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T))
\<Longrightarrow> Semantic_Zero_Val TY T x \<close>
  unfolding Semantic_Zero_Val_def \<r>Guard_def Premise_def
  by blast
*)

lemma Semantic_Zero_Val_EIF_sat:
  \<open> \<r>EIF (Semantic_Zero_Val TY T x) (\<exists>v. Zero TY = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T)) \<close>
  unfolding \<r>EIF_def Semantic_Zero_Val_def
  by blast

bundle Semantic_Zero_Val_EIF_brute = (*Semantic_Zero_Val_brute[\<phi>reason default %semantic_zero_val_brute]*)
                                     Semantic_Zero_Val_EIF_sat[\<phi>reason %extract_pure+10]


subsection \<open>Equality\<close>

definition \<phi>Equal :: "(VAL,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "\<phi>Equal T can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 res.
    can_eq x1 x2 \<and> p1 \<Turnstile> (x1 \<Ztypecolon> T) \<and> p2 \<Turnstile> (x2 \<Ztypecolon> T)
      \<longrightarrow> Can_EqCompare res p1 p2 \<and> (EqCompare p1 p2 = eq x1 x2))"

declare [[\<phi>reason_default_pattern \<open>\<phi>Equal ?TY ?can_eq ?eq\<close> \<Rightarrow> \<open>\<phi>Equal ?TY _ _\<close> (100) ]]


subsection \<open>Functional\<close>

definition Is_Functional :: \<open>'a BI \<Rightarrow> bool\<close>
  where \<open>Is_Functional S \<longleftrightarrow> (\<forall>x y. x \<Turnstile> S \<and> y \<Turnstile> S \<longrightarrow> x = y)\<close>

definition Functionality :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Functionality T p \<longleftrightarrow> (\<forall>x u v. p x \<and> u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> u = v)\<close>
  \<comment> \<open>A lower bound of the set in which \<phi>-type assertions are functional\<close>

declare [[\<phi>reason_default_pattern \<open>Is_Functional ?S\<close> \<Rightarrow> \<open>Is_Functional ?S\<close> (100)
                              and \<open>Functionality ?T _\<close> \<Rightarrow> \<open>Functionality ?T _\<close> (100)]]

\<phi>reasoner_group \<phi>functionality_all = (%cutting, [1,3000]) for (\<open>Is_Functional S\<close>, \<open>Functionality T p\<close>)
    \<open>All reasoning rules giving functionality of \<phi>-types, meaning if the assertion uniquely fixes
     a concrete object for each abstract object.\<close>
  and \<phi>functionality = (%cutting, [%cutting, %cutting+30]) in \<phi>functionality_all
    \<open>Default rules are cutting\<close>
  and derived_\<phi>functionality = (50, [40,60]) in \<phi>functionality_all and < \<phi>functionality
    \<open>Derived rules\<close>
  and \<phi>functional_to_functionality = (10, [10,10]) in \<phi>functionality_all and < derived_\<phi>functionality
    \<open>Trunning \<open>Is_Functional (x : T)\<close> to \<open>Functionality T p\<close>\<close>
  and \<phi>functionality_brute = (2, [2,2]) in \<phi>functionality_all and < \<phi>functional_to_functionality
    \<open>reducing to concrete semantics, and only used in deriving rules\<close>

subsubsection \<open>Basic Rules\<close>

(*depreciated*)
lemma Is_Functional_premise_extraction:
  \<open>Is_Functional S \<equiv> (\<forall>u v. u \<Turnstile> S \<and> v \<Turnstile> S \<longrightarrow> u = v) \<and> True\<close>
  unfolding Is_Functional_def atomize_eq
  by blast

(*depreciated*)
lemma Functionality_premise_extraction:
  \<open>Functionality T P \<equiv> (\<forall>x u v. P x \<and> u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> u = v) \<and> True\<close>
  unfolding Functionality_def atomize_eq
  by blast


(* lemma Is_Functional_alt:
  \<open>Is_Functional S \<longleftrightarrow> (S = {} \<or> (\<exists>x. S = {x}))\<close>
  unfolding Is_Functional_def by blast *)

lemma Is_Functional_I[intro!]:
  \<open> (\<And>x y. x \<Turnstile> A \<Longrightarrow> y \<Turnstile> A \<Longrightarrow> x = y)
\<Longrightarrow> Is_Functional A \<close>
  unfolding Is_Functional_def by blast

lemma Is_Functional_imp:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S'
\<Longrightarrow> Is_Functional S'
\<Longrightarrow> Is_Functional S\<close>
  unfolding Transformation_def Is_Functional_def
  by blast

lemma [\<phi>reason no explorative backtrack 0]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show\<close> S \<open>is functional\<close>)
\<Longrightarrow> Is_Functional S\<close>
  unfolding TRACE_FAIL_def
  by blast

lemma [\<phi>reason default %\<phi>functional_to_functionality]:
  \<open> Functionality T p
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> p x
\<Longrightarrow> Is_Functional (x \<Ztypecolon> T)\<close>
  unfolding Premise_def Is_Functional_def Functionality_def
  by simp


lemma Is_Functional_brute:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>u v. u \<Turnstile> S \<and> v \<Turnstile> S \<longrightarrow> u = v)
\<Longrightarrow> Is_Functional S \<close>
  unfolding Is_Functional_def Premise_def
  by blast

lemma Is_Functional_EIF_brute:
  \<open> \<r>EIF (Is_Functional S) (\<forall>u v. u \<Turnstile> S \<and> v \<Turnstile> S \<longrightarrow> u = v) \<close>
  unfolding \<r>EIF_def Is_Functional_def
  by blast

lemma Functionality_EIF_brute:
  \<open> \<r>EIF (Functionality T D) (\<forall>x u v. D x \<and> u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> u = v) \<close>
  unfolding \<r>EIF_def Functionality_def
  by blast

bundle Is_Functional_brute = Is_Functional_brute[\<phi>reason default %\<phi>functionality_brute]
                             Is_Functional_EIF_brute[\<phi>reason %extract_pure+10]
                             Functionality_EIF_brute[\<phi>reason %extract_pure+10]


subsubsection \<open>Basic Types and Connectives\<close>

lemma [\<phi>reason %\<phi>functionality]:
  \<open>Functionality Itself (\<lambda>_. True)\<close>
  unfolding Functionality_def
  by clarsimp

lemma [\<phi>reason %\<phi>functionality]:
  \<open> Is_Functional 1 \<close>
  unfolding Is_Functional_def
  by simp

lemma [\<phi>reason %\<phi>functionality]:
  \<open> Is_Functional 0 \<close>
  unfolding Is_Functional_def
  by simp

lemma [\<phi>reason %\<phi>functionality]:
  \<open> Is_Functional A
\<Longrightarrow> Is_Functional B
\<Longrightarrow> Is_Functional (A \<and>\<^sub>B\<^sub>I B) \<close>
  unfolding Is_Functional_def
  by simp

lemma [\<phi>reason %\<phi>functionality]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Is_Functional S)
\<Longrightarrow> Is_Functional (S \<s>\<u>\<b>\<j> P) \<close>
  unfolding Is_Functional_def Premise_def
  by simp

(* \<comment> \<open>derived automatically later\<close>
lemma [\<phi>reason %\<phi>functionality]:
  \<open> Functionality T p\<^sub>T
\<Longrightarrow> Functionality U p\<^sub>U
\<Longrightarrow> Functionality (T \<^emph> U) (\<lambda>(x,y). p\<^sub>T x \<and> p\<^sub>U y)\<close>
  unfolding Functionality_def
  by clarsimp blast
*)

lemma [\<phi>reason %\<phi>functionality]:
  \<open> Is_Functional A
\<Longrightarrow> Is_Functional B
\<Longrightarrow> Is_Functional (A * B)\<close>
  unfolding Is_Functional_def set_eq_iff
  by (simp add: set_mult_expn, blast)

lemma [\<phi>reason %\<phi>functionality]:
  \<open> Is_Functional A
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Is_Functional B)
\<Longrightarrow> Is_Functional (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B)\<close>
  unfolding Is_Functional_def set_eq_iff REMAINS_def
  by (simp add: set_mult_expn, blast)

lemma [\<phi>reason %\<phi>functionality]:
  \<open> Functionality T p\<^sub>T
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Functionality U p\<^sub>U)
\<Longrightarrow> Functionality (T \<^emph>[C] U) (\<lambda>(x,y). p\<^sub>T x \<and> (C \<longrightarrow> p\<^sub>U y))\<close>
  unfolding Functionality_def
  by clarsimp blast

lemma [\<phi>reason %\<phi>functionality]:
  \<open> (\<And>i\<in>S. Is_Functional (A i))
\<Longrightarrow> Is_Functional (\<big_ast>i\<in>S. A i) \<close>
  unfolding Is_Functional_def Mul_Quant_def atomize_Ball Ball_def
proof clarsimp
  fix x y
  assume prems: \<open>\<forall>x. x \<in> S \<longrightarrow> (\<forall>xa y. xa \<Turnstile> A x \<and> y \<Turnstile> A x \<longrightarrow> xa = y)\<close> (is ?A)
                \<open>x \<Turnstile> prod A S\<close> (is ?B)
                \<open>y \<Turnstile> prod A S\<close> (is ?C)
     and \<open>finite S\<close>
  have \<open>?A \<and> ?B \<and> ?C \<longrightarrow> x = y\<close>
    by (induct arbitrary: x y rule: finite_induct[OF \<open>finite S\<close>]; clarsimp; blast)
  then show \<open>x = y\<close>
    using prems by blast
qed


subsection \<open>Carrier Set of Separation Algebra\<close>

definition Within_Carrier_Set :: \<open>'c::sep_carrier set \<Rightarrow> bool\<close>
  where \<open>Within_Carrier_Set A \<longleftrightarrow> (\<forall>v. v \<Turnstile> A \<longrightarrow> mul_carrier v)\<close>

definition Carrier_Set :: \<open>('c::sep_carrier,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Carrier_Set T D \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> Within_Carrier_Set (x \<Ztypecolon> T))\<close>

declare [[\<phi>reason_default_pattern
      \<open>Within_Carrier_Set ?A\<close> \<Rightarrow> \<open>Within_Carrier_Set ?A\<close> (100)
  and \<open>Carrier_Set ?T _\<close> \<Rightarrow> \<open>Carrier_Set ?T _\<close> (100)
]]

\<phi>reasoner_group carrier_set = (100, [10,3000]) for \<open>Within_Carrier_Set A\<close>
    \<open>Rules reasoning if the given assertion \<open>A\<close> with all its concrete objects falls in the carrier set of the separation algebra\<close>
 and carrier_set_cut = (1000, [1000, 1030]) for \<open>Within_Carrier_Set A\<close> in carrier_set
    \<open>Cutting rules\<close>
 and carrier_set_red = (2500, [2500, 2530]) for \<open>Within_Carrier_Set A\<close> in carrier_set and > carrier_set_cut
    \<open>Literal Reduction\<close>
 and derived_carrier_set = (50, [50,50]) for (\<open>Within_Carrier_Set A\<close>, \<open>Carrier_Set T D\<close>)
                                          in carrier_set and < carrier_set_cut
    \<open>Derived rules\<close>
 and carrier_set_to_within_carrier_set = (10, [10,10]) for (\<open>Within_Carrier_Set A\<close>, \<open>Carrier_Set T D\<close>)
                                                        in carrier_set and < derived_carrier_set
    \<open>Turning \<open>Within_Carrier_Set (x : T)\<close> to \<open>Carrier_Set T D\<close>\<close>

subsubsection \<open>Extracting Pure Facts\<close>

context begin

private lemma EIF_Within_Carrier_Set:
  \<open> \<r>EIF (Within_Carrier_Set A) (\<forall>v. v \<Turnstile> A \<longrightarrow> mul_carrier v) \<close>
  unfolding Within_Carrier_Set_def \<r>EIF_def
  by blast

private lemma ESC_Within_Carrier_Set:
  \<open> \<r>ESC (\<forall>v. v \<Turnstile> A \<longrightarrow> mul_carrier v) (Within_Carrier_Set A) \<close>
  unfolding Within_Carrier_Set_def \<r>ESC_def
  by blast

private lemma EIF_Carrier_Set:
  \<open> \<r>EIF (Carrier_Set T D) (\<forall>x v. D x \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> mul_carrier v) \<close>
  unfolding Carrier_Set_def Within_Carrier_Set_def \<r>EIF_def
  by blast

private lemma ESC_Carrier_Set:
  \<open> \<r>ESC (\<forall>x v. D x \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> mul_carrier v) (Carrier_Set T D) \<close>
  unfolding Carrier_Set_def Within_Carrier_Set_def \<r>ESC_def
  by blast

bundle extracting_Carrier_Set_sat =
          EIF_Within_Carrier_Set [\<phi>reason %extract_pure_sat]
          ESC_Within_Carrier_Set [\<phi>reason %extract_pure_sat]
          EIF_Carrier_Set [\<phi>reason %extract_pure_sat]
          ESC_Carrier_Set [\<phi>reason %extract_pure_sat]

end


subsubsection \<open>Rules for Logical Connectives\<close>

lemma [\<phi>reason default %carrier_set_to_within_carrier_set]:
  \<open> Carrier_Set T P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P x
\<Longrightarrow> Within_Carrier_Set (x \<Ztypecolon> T) \<close>
  unfolding Carrier_Set_def Premise_def
  by blast

lemma [\<phi>reason %carrier_set_cut]:
  \<open> Within_Carrier_Set A
\<Longrightarrow> Within_Carrier_Set B
\<Longrightarrow> Within_Carrier_Set (A * B)\<close>
  unfolding Within_Carrier_Set_def
  by (clarsimp simp add: mul_carrier_closed)

text \<open>Though the above rule is reasonable enough, it is not reversible, essentially because
  the set of concrete objects satisfying \<open>A * B\<close> is far smaller than either of that satisfying \<open>A\<close> or \<open>B\<close>.\<close>

lemma
  \<open>Within_Carrier_Set (A * B) \<Longrightarrow> Within_Carrier_Set A \<and> Within_Carrier_Set B\<close>
  oops

lemma [\<phi>reason %carrier_set_cut]:
  \<open> (\<And>i\<in>I. Within_Carrier_Set (A i))
\<Longrightarrow> Within_Carrier_Set (\<big_ast>i\<in>I. A i) \<close>
  for A :: \<open>'i \<Rightarrow> 'c :: {sep_algebra,sep_carrier_1} BI\<close>
  unfolding Within_Carrier_Set_def Mul_Quant_def meta_Ball_def Premise_def
proof clarsimp
  fix v
  assume \<open>finite I\<close>
  show \<open>(\<And>x. x \<in> I \<Longrightarrow> \<forall>v. v \<Turnstile> A x \<longrightarrow> mul_carrier v) \<Longrightarrow> v \<Turnstile> prod A I \<Longrightarrow> mul_carrier v\<close>
    by (induct arbitrary: v rule: finite_induct[OF \<open>finite I\<close>]; clarsimp; metis mul_carrier_closed)
qed

(*
lemma \<comment> \<open>derived automatically later\<close>
  \<open> Carrier_Set T P
\<Longrightarrow> Carrier_Set U Q
\<Longrightarrow> Carrier_Set (T \<^emph> U) (pred_prod P Q)\<close>
  unfolding Carrier_Set_def Within_Carrier_Set_def
  by (clarsimp simp add: mul_carrier_closed)
*)

lemma [\<phi>reason %carrier_set_cut]:
  \<open> Within_Carrier_Set A
\<Longrightarrow> Within_Carrier_Set B
\<Longrightarrow> Within_Carrier_Set (A + B)\<close>
  unfolding Within_Carrier_Set_def
  by clarsimp

lemma \<comment> \<open>The above rule is reversible\<close>
  \<open> Within_Carrier_Set (A + B) \<Longrightarrow> Within_Carrier_Set A \<and> Within_Carrier_Set B \<close>
  unfolding Within_Carrier_Set_def
  by clarsimp

lemma [\<phi>reason %carrier_set_cut]:
  \<open> (\<And>x. Within_Carrier_Set (A x))
\<Longrightarrow> Within_Carrier_Set (ExSet A) \<close>
  unfolding Within_Carrier_Set_def
  by clarsimp

lemma \<comment> \<open>The above rule is reversible\<close>
  \<open> Within_Carrier_Set (ExSet A) \<Longrightarrow> Within_Carrier_Set (A x) \<close>
  unfolding Within_Carrier_Set_def
  by clarsimp blast

lemma [\<phi>reason %carrier_set_cut]:
  \<open> Within_Carrier_Set A
\<Longrightarrow> Within_Carrier_Set B
\<Longrightarrow> Within_Carrier_Set (A \<and>\<^sub>B\<^sub>I B)\<close>
  unfolding Within_Carrier_Set_def
  by clarsimp


text \<open>The above rule is also not reversible. Essentially the rules for conjunctive connectives are not
  reversible due to the same reason as \<open>*\<close>. \<close>

lemma \<open> Within_Carrier_Set (A \<and>\<^sub>B\<^sub>I B) \<Longrightarrow> Within_Carrier_Set A \<and> Within_Carrier_Set B \<close>
  oops

lemma [\<phi>reason %carrier_set_cut]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Within_Carrier_Set A)
\<Longrightarrow> Within_Carrier_Set (A \<s>\<u>\<b>\<j> P)\<close>
  unfolding Within_Carrier_Set_def
  by clarsimp

lemma [\<phi>reason %carrier_set_cut]:
  \<open> Within_Carrier_Set 0 \<close>
  unfolding Within_Carrier_Set_def
  by simp

lemma [\<phi>reason %carrier_set_cut]:
  \<open> Within_Carrier_Set (1 :: 'a::sep_carrier_1 set) \<close>
  unfolding Within_Carrier_Set_def
  by simp

paragraph \<open>Case Split\<close>

subparagraph \<open>Reduction\<close>

lemma [\<phi>reason %carrier_set_red]:
  \<open> Within_Carrier_Set (P a)
\<Longrightarrow> Within_Carrier_Set (case_sum P Q (Inl a)) \<close>
  by simp

lemma [\<phi>reason %carrier_set_red]:
  \<open> Within_Carrier_Set (Q b)
\<Longrightarrow> Within_Carrier_Set (case_sum P Q (Inr b)) \<close>
  by simp

subparagraph \<open>Case Split\<close>

lemma [\<phi>reason %carrier_set_cut]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> Within_Carrier_Set (P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> Within_Carrier_Set (Q b))
\<Longrightarrow> Within_Carrier_Set (case_sum P Q x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)

text \<open>Also not reversible in non-trivial cases.\<close>

subsubsection \<open>Rules for Basic \<phi>-Types\<close>

lemma [\<phi>reason 1000]:
  \<open>Carrier_Set Itself mul_carrier\<close>
  unfolding Carrier_Set_def Within_Carrier_Set_def
  by simp

lemma [\<phi>reason 1000]:
  \<open>Carrier_Set (\<circle> :: ('c::sep_carrier_1, unit) \<phi>) (\<lambda>_. True)\<close>
  unfolding Carrier_Set_def Within_Carrier_Set_def
  by clarsimp


subsection \<open>Separationally Functional\<close> \<comment> \<open>A weaker and more general concept\<close>

definition Sep_Functional :: \<open>'a::sep_magma BI \<Rightarrow> bool\<close>
  where \<open>Sep_Functional S \<longleftrightarrow> (\<forall>x y. x \<Turnstile> S \<and> y \<Turnstile> S \<and> x ## y \<longrightarrow> x = y) \<close>

declare [[\<phi>reason_default_pattern \<open>Sep_Functional ?S\<close> \<Rightarrow> \<open>Sep_Functional ?S\<close> (100)]]

lemma [\<phi>reason no explorative backtrack 1]:
  \<open> Is_Functional S
\<Longrightarrow> Sep_Functional S \<close>
  unfolding Sep_Functional_def Is_Functional_def
  by simp

lemma [\<phi>reason no explorative backtrack 0]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show\<close> S \<open>is separationally functional\<close>)
\<Longrightarrow> Sep_Functional S\<close>
  unfolding TRACE_FAIL_def
  by blast

lemma [\<phi>reason 1200]:
  \<open> Sep_Functional A
\<Longrightarrow> Sep_Functional B
\<Longrightarrow> Sep_Functional (A \<and>\<^sub>B\<^sub>I B) \<close>
  unfolding Sep_Functional_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> Sep_Functional A
\<Longrightarrow> Sep_Functional B
\<Longrightarrow> Sep_Functional (A * B)\<close>
  for A :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding Sep_Functional_def
  by (clarsimp; metis sep_disj_commute sep_disj_multD1 sep_disj_multD2)

lemma [\<phi>reason 1200]:
  \<open> Sep_Functional (fst x \<Ztypecolon> T)
\<Longrightarrow> Sep_Functional (snd x \<Ztypecolon> U)
\<Longrightarrow> Sep_Functional (x \<Ztypecolon> T \<^emph> U)\<close>
  for T :: \<open>('c::sep_ab_semigroup, 'a) \<phi>\<close>
  unfolding Sep_Functional_def
  by (cases x; clarsimp;
      metis sep_disj_commute sep_disj_multD1 sep_disj_multD2)

(*
lemma [\<phi>reason 1200]:
  \<open> (\<And>i\<in>I. Sep_Functional (A i))
\<Longrightarrow> Sep_Functional (\<big_ast>i\<in>I. A i) \<close>
  unfolding Mul_Quant_def atomize_Ball Ball_def
proof clarsimp
  *)



subsection \<open>Injective\<close>

lemma is_singleton_I''[\<phi>reason 1000]:
  \<open> Inhabited A
\<Longrightarrow> Is_Functional A
\<Longrightarrow> is_singleton A\<close>
  unfolding Satisfaction_def Inhabited_def Is_Functional_def
  by (metis empty_iff is_singletonI')
  
lemma [\<phi>reason 1000]:
  \<open>is_singleton (x \<Ztypecolon> Itself)\<close>
  by (rule is_singleton_I''; simp add: Is_Functional_def)


subsection \<open>Reflexive Separation\<close>

text \<open>\<^prop>\<open>x ## x\<close> is used to represented \<open>x\<close> is in the carrier set in some algebras like permission algebra.\<close>

definition Sep_Reflexive :: \<open>'a::sep_magma BI \<Rightarrow> bool\<close>
  where \<open>Sep_Reflexive S \<longleftrightarrow> (\<forall>u. u \<Turnstile> S \<longrightarrow> u ## u) \<close>

lemma [\<phi>reason 1000]:
  \<open> Sep_Reflexive A
\<Longrightarrow> Sep_Reflexive B
\<Longrightarrow> Sep_Reflexive (A * B) \<close>
  for A :: \<open>'a::sep_refl BI\<close>
  unfolding Sep_Reflexive_def
  by (clarsimp simp add: sep_refl_mult_I)

lemma [\<phi>reason 1000]:
  \<open> Sep_Reflexive (fst x \<Ztypecolon> T)
\<Longrightarrow> Sep_Reflexive (snd x \<Ztypecolon> U)
\<Longrightarrow> Sep_Reflexive (x \<Ztypecolon> T \<^emph> U) \<close>
  for T :: \<open>('c::sep_refl, 'a) \<phi>\<close>
  unfolding Sep_Reflexive_def
  by (clarsimp simp add: sep_refl_mult_I)

lemma [\<phi>reason 1000]:
  \<open> Sep_Reflexive A
\<Longrightarrow> Sep_Reflexive B
\<Longrightarrow> Sep_Reflexive (A + B) \<close>
  unfolding Sep_Reflexive_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. Sep_Reflexive (A x))
\<Longrightarrow> Sep_Reflexive (ExSet A) \<close>
  unfolding Sep_Reflexive_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> Sep_Reflexive A
\<Longrightarrow> Sep_Reflexive B
\<Longrightarrow> Sep_Reflexive (A \<and>\<^sub>B\<^sub>I B) \<close>
  unfolding Sep_Reflexive_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> Sep_Reflexive A
\<Longrightarrow> Sep_Reflexive (A \<s>\<u>\<b>\<j> P) \<close>
  unfolding Sep_Reflexive_def
  by clarsimp


section \<open>Specification of Monadic States\<close>

definition StrictState :: "('ret \<phi>arg \<Rightarrow> rassn)
                          \<Rightarrow> (ABNM \<Rightarrow> rassn)
                          \<Rightarrow> 'ret comp set"
  where "StrictState T E = {s. case s of Success val x \<Rightarrow> x \<in> T val
                              | Abnormal val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False
                              | NonTerm \<Rightarrow> False
                              | AssumptionBroken \<Rightarrow> False
                  }"

definition LooseState  :: "('ret \<phi>arg \<Rightarrow> rassn)
                          \<Rightarrow> (ABNM \<Rightarrow> rassn)
                          \<Rightarrow> 'ret comp set"
  where  "LooseState T E = {s. case s of Success val x \<Rightarrow> x \<in> T val
                              | Abnormal val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False
                              | NonTerm \<Rightarrow> True
                              | AssumptionBroken \<Rightarrow> True
                  }"

lemma StrictState_expn[iff]:
        "Success vs x \<in> StrictState T E \<equiv> x \<in> T vs"
        "Abnormal v x \<in> StrictState T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> StrictState T E)"
        "\<not> (NonTerm \<in> StrictState T E)"
        "\<not> (AssumptionBroken \<in> StrictState T E)"
        "\<not> {Invalid} \<subseteq> StrictState T E"
        "\<not> {NonTerm} \<subseteq> StrictState T E"
        "\<not> {AssumptionBroken} \<subseteq> StrictState T E"
  and LooseState_expn[iff]:
        "Success vs x \<in> LooseState T E \<equiv> x \<in> T vs"
        "Abnormal v x \<in> LooseState T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> LooseState T E)"
        "(NonTerm \<in> LooseState T E)"
        "(AssumptionBroken \<in> LooseState T E)"
        "\<not> {Invalid} \<subseteq> LooseState T E"
        "{NonTerm} \<subseteq> LooseState T E"
        "{AssumptionBroken} \<subseteq> LooseState T E"
  by (simp_all add: StrictState_def LooseState_def)

lemma LooseState_expn' :
    "x \<in> LooseState T E \<longleftrightarrow> x = NonTerm
                 \<or> x = AssumptionBroken
                 \<or> (\<exists>x' v. x = Success v x' \<and> x' \<in> T v)
                 \<or> (\<exists>x' v. x = Abnormal v x' \<and> x' \<in> E v)"
  by (cases x) simp_all

lemma StrictState_elim[elim]:
    "s \<in> StrictState T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Abnormal v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> C" by (cases s) auto

lemma StrictState_intro[intro]:
    " x \<in> T v \<Longrightarrow> Success v x \<in> StrictState T E"
    " x \<in> E a \<Longrightarrow> Abnormal a x \<in> StrictState T E"
  by simp_all

lemma LooseState_E[elim]:
    "s \<in> LooseState T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Abnormal v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> (s = NonTerm \<Longrightarrow> C)
\<Longrightarrow> (s = AssumptionBroken \<Longrightarrow> C)
\<Longrightarrow> C"
  by (cases s) auto

lemma LooseState_I[intro]:
  "x \<in> T v \<Longrightarrow> Success v x \<in> LooseState T E"
  "x \<in> E a \<Longrightarrow> Abnormal a x \<in> LooseState T E"
  "NonTerm \<in> LooseState T E"
  "AssumptionBroken \<in> LooseState T E"
  by simp_all

lemma LooseState_upgrade:
  "s \<in> LooseState T E \<Longrightarrow> s \<noteq> AssumptionBroken \<Longrightarrow> s \<noteq> NonTerm \<Longrightarrow> s \<in> StrictState T E"
  by (cases s) auto

lemma StrictState_degrade: "s \<in> StrictState T E \<Longrightarrow> s \<in> LooseState T E" by (cases s) auto

lemma LooseState_introByStrict:
  "(s \<noteq> AssumptionBroken \<Longrightarrow> s \<noteq> NonTerm \<Longrightarrow> s \<in> StrictState T E) \<Longrightarrow> s \<in> LooseState T E"
  by (cases s) auto

lemma StrictState_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> StrictState A E \<subseteq> StrictState A' E'\<close>
  unfolding subset_iff StrictState_def by simp

lemma StrictState_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> StrictState A E \<Longrightarrow> s \<in> StrictState A' E'\<close>
  unfolding StrictState_def by (cases s; simp)

lemma LooseState_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> LooseState A E \<subseteq> LooseState A' E'\<close>
  unfolding subset_iff LooseState_def by simp
lemma LooseState_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> LooseState A E \<Longrightarrow> s \<in> LooseState A' E'\<close>
  unfolding LooseState_def by (cases s; simp)


lemma LooseState_plus[iff]:
(*  \<open>LooseState (A + B) E   = LooseState A E + LooseState B E\<close> *)
  \<open>LooseState X (\<lambda>v. EA v + EB v) = LooseState X EA + LooseState X EB\<close>
  unfolding set_eq_iff LooseState_def by simp_all
lemma StrictState_plus[iff]:
(*  \<open>StrictState (A + B) E   = StrictState A E  + StrictState B E\<close> *)
  \<open>StrictState X (\<lambda>v. EA v + EB v) = StrictState X EA + StrictState X EB\<close>
  unfolding set_eq_iff StrictState_def by simp_all

abbreviation \<open>Void \<equiv> (1::assn)\<close>


section \<open>Specification of Fictional Resource\<close>

declare INTERP_SPEC[\<phi>expns]

lemma  INTERP_SPEC_subj[\<phi>expns]:
  \<open> INTERP_SPEC (S \<s>\<u>\<b>\<j> P) = (INTERP_SPEC S \<s>\<u>\<b>\<j> P) \<close>
  unfolding INTERP_SPEC_def by (simp add: set_eq_iff Subjection_expn_set, blast)

lemma  INTERP_SPEC_ex[\<phi>expns]:
  \<open> INTERP_SPEC (ExSet S) = (\<exists>\<^sup>s x. INTERP_SPEC (S x)) \<close>
  unfolding INTERP_SPEC_def by (simp add: set_eq_iff ExSet_expn_set, blast)

abbreviation COMMA :: \<open>assn \<Rightarrow> assn \<Rightarrow> assn\<close> ("_\<heavy_comma>/ _" [15,16] 15)
  where \<open>COMMA \<equiv> (*)\<close>


section \<open>Specification of Computation\<close>

definition \<phi>Procedure :: "'ret proc
                        \<Rightarrow> assn
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> assn)
                        \<Rightarrow> (ABNM \<Rightarrow> assn)
                        \<Rightarrow> bool"
    ("\<p>\<r>\<o>\<c> (2_)/ (0\<lbrace> _/ \<longmapsto> _ \<rbrace>)/ \<t>\<h>\<r>\<o>\<w>\<s> (100_)/ " [101,2,2,100] 100)
  where "\<phi>Procedure f T U E \<longleftrightarrow>
    (\<forall>comp R. comp \<in> INTERP_SPEC (R * T) \<longrightarrow> f comp \<subseteq> LooseState (\<lambda>v. INTERP_SPEC (R * U v)) (\<lambda>v. INTERP_SPEC (R * E v)))"

abbreviation \<phi>Procedure_no_exception ("\<p>\<r>\<o>\<c> (2_)/ \<lbrace> (2_) \<longmapsto>/ (2_) \<rbrace>/ " [101,2,2] 100)
  where \<open>\<phi>Procedure_no_exception f T U \<equiv> \<phi>Procedure f T U 0\<close>

lemma \<phi>Procedure_alt:
  \<open>\<p>\<r>\<o>\<c> f \<lbrace> T \<longmapsto> U \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<longleftrightarrow> (\<forall>comp r. comp \<in> INTERP_SPEC ({r} * T) \<longrightarrow> f comp \<subseteq> LooseState (\<lambda>v. INTERP_SPEC ({r} * U v)) (\<lambda>v. INTERP_SPEC ({r} * E v)))\<close>
  apply rule
  apply ((unfold \<phi>Procedure_def)[1], blast)
  unfolding \<phi>Procedure_def INTERP_SPEC subset_iff
  apply (clarsimp simp add: times_set_def split_comp_All INTERP_SPEC_def Satisfaction_def)
  by fastforce

lemmas \<phi>Procedure_I = \<phi>Procedure_alt[THEN iffD2]

lemma \<phi>Procedure_protect_body:
  \<open> T \<equiv> T'
\<Longrightarrow> U \<equiv> U'
\<Longrightarrow> E \<equiv> E'
\<Longrightarrow> \<phi>Procedure f T U E \<equiv> \<phi>Procedure f T' U' E'\<close>
  by simp

subsubsection \<open>Syntax\<close>

ML_file \<open>library/syntax/procedure.ML\<close>

section \<open>View Shift\<close>

definition View_Shift
    :: "assn \<Rightarrow> assn \<Rightarrow> bool \<Rightarrow> bool" ("(2_/ \<s>\<h>\<i>\<f>\<t>\<s> _/ \<w>\<i>\<t>\<h> _)" [13,13,13] 12)
  where "View_Shift T U P \<longleftrightarrow> (\<forall>x R. x \<Turnstile> INTERP_SPEC (R * T) \<longrightarrow> x \<Turnstile> INTERP_SPEC (R * U) \<and> P)"

abbreviation Simple_View_Shift
    :: "assn \<Rightarrow> assn \<Rightarrow> bool" ("(2_/ \<s>\<h>\<i>\<f>\<t>\<s> _)"  [13,13] 12)
  where \<open>Simple_View_Shift T U \<equiv> View_Shift T U True\<close>

declare [[\<phi>reason_default_pattern
    \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> (10)
and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?var_y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _\<close> (20)
and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> (20)
and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?var_y \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> (30)
]]

subsection \<open>Basic Rules\<close>

lemma View_Shift_imply_P:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (P1 \<longrightarrow> P2)
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P2\<close>
  unfolding View_Shift_def
  by blast

lemma view_shift_by_implication[intro?, \<phi>reason 10]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> B \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def View_Shift_def INTERP_SPEC_def Satisfaction_def
  by (clarsimp simp add: set_mult_expn) blast

lemma view_shift_0[simp]:
  \<open> 0 \<s>\<h>\<i>\<f>\<t>\<s> X \<w>\<i>\<t>\<h> any \<close>
  by (blast intro: view_shift_by_implication zero_implies_any)

lemma [\<phi>reason 2000 for \<open>0 \<s>\<h>\<i>\<f>\<t>\<s> ?X \<w>\<i>\<t>\<h> ?P\<close>]:
  \<open> 0 \<s>\<h>\<i>\<f>\<t>\<s> X \<w>\<i>\<t>\<h> False \<close>
  by simp

lemma view_shift_refl[\<phi>reason 2000 for \<open>?A \<s>\<h>\<i>\<f>\<t>\<s> ?B \<w>\<i>\<t>\<h> ?P\<close>]:
  "A \<s>\<h>\<i>\<f>\<t>\<s> A"
  by (blast intro: view_shift_by_implication transformation_refl)

lemma [\<phi>reason 800 for \<open>?x \<Ztypecolon> ?T \<s>\<h>\<i>\<f>\<t>\<s> ?y \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> ?P\<close>]:
  " Object_Equiv T eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y
\<Longrightarrow> x \<Ztypecolon> T \<s>\<h>\<i>\<f>\<t>\<s> y \<Ztypecolon> T"
  unfolding Object_Equiv_def Premise_def
  by (insert view_shift_by_implication, presburger)

lemma view_shift_union[\<phi>reason 800]:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> X + Y \<w>\<i>\<t>\<h> P\<close>
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> X + Y \<w>\<i>\<t>\<h> P\<close>
  by (simp add: View_Shift_def distrib_left)+

lemma \<phi>view_shift_trans:
  "A \<s>\<h>\<i>\<f>\<t>\<s> B \<w>\<i>\<t>\<h> P
    \<Longrightarrow> (P \<Longrightarrow> B \<s>\<h>\<i>\<f>\<t>\<s> C \<w>\<i>\<t>\<h> Q)
    \<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> C \<w>\<i>\<t>\<h> P \<and> Q"
  unfolding View_Shift_def by blast

lemma \<phi>frame_view:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * A \<s>\<h>\<i>\<f>\<t>\<s> R * B \<w>\<i>\<t>\<h> P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc)

lemma \<phi>view_shift_intro_frame:
  "U' \<s>\<h>\<i>\<f>\<t>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> R * U' \<s>\<h>\<i>\<f>\<t>\<s> R * U \<w>\<i>\<t>\<h> P "
  by (simp add: \<phi>frame_view)

lemma \<phi>view_shift_intro_frame_R:
  "U' \<s>\<h>\<i>\<f>\<t>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> U' * R \<s>\<h>\<i>\<f>\<t>\<s> U * R \<w>\<i>\<t>\<h> P "
  by (simp add: \<phi>frame_view mult.commute)

subsection \<open>Basic Rules\<close>

subsubsection \<open>When the conditional boolean is fixed\<close>

lemma [\<phi>reason %ToA_normalizing for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> if C\<^sub>R then R = R' else R = 1
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R  \<w>\<i>\<t>\<h> P \<close>
  by (cases C\<^sub>R; simp)

lemma [\<phi>reason %ToA_normalizing for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top> \<w>\<i>\<t>\<h> P \<close>
  by simp


section \<open>Hoare Rules \& SL Rules\<close>

subsection \<open>Fundamental Rules\<close>

lemma \<phi>SKIP[simp,intro!]: "\<p>\<r>\<o>\<c> det_lift (Success v) \<lbrace> T v \<longmapsto> T \<rbrace>"
  unfolding \<phi>Procedure_def det_lift_def by clarsimp

lemma \<phi>SEQ:
   "\<p>\<r>\<o>\<c> f \<lbrace> A \<longmapsto> B \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> (\<And>vs. \<p>\<r>\<o>\<c> g vs \<lbrace> B vs \<longmapsto> C \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> (f \<bind> g) \<lbrace> A \<longmapsto> C \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E"
  unfolding \<phi>Procedure_def bind_def apply (clarsimp simp add: subset_iff)
  subgoal for comp R x s
    apply (cases s; clarsimp; cases x; clarsimp; blast) . .

lemma \<phi>frame:
  " \<p>\<r>\<o>\<c> f \<lbrace> A \<longmapsto> B \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>ex. R * E ex) "
  unfolding \<phi>Procedure_def subset_iff
  apply clarify subgoal premises prems for comp R' s
    using prems(1)[THEN spec[where x=comp], THEN spec[where x=\<open>R' * R\<close>],
          simplified mult.assoc, THEN mp, OF prems(2)] prems(3) by blast .

lemma \<phi>Inhabited:
  \<open>(Inhabited X \<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>Procedure_def Inhabited_def
  by (meson INTERP_SPEC sep_conj_expn)


subsubsection \<open>View Shift\<close>

lemma \<phi>frame_view_right:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * R \<s>\<h>\<i>\<f>\<t>\<s> B * R \<w>\<i>\<t>\<h> P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc mult.commute)

lemma \<phi>view_trans:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> B \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (P1 \<Longrightarrow> B \<s>\<h>\<i>\<f>\<t>\<s> C \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> C \<w>\<i>\<t>\<h> P1 \<and> P2\<close>
  unfolding View_Shift_def by blast

lemma \<phi>CONSEQ:
   "\<p>\<r>\<o>\<c> f \<lbrace> A  \<longmapsto> B  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> A' \<s>\<h>\<i>\<f>\<t>\<s> A \<w>\<i>\<t>\<h> Any1
\<Longrightarrow> (\<And>ret. B ret \<s>\<h>\<i>\<f>\<t>\<s> B' ret \<w>\<i>\<t>\<h> Any2)
\<Longrightarrow> (\<And>ex.  E ex \<s>\<h>\<i>\<f>\<t>\<s> E' ex \<w>\<i>\<t>\<h> Any3)
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> A' \<longmapsto> B' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' "
  unfolding \<phi>Procedure_def View_Shift_def subset_iff Satisfaction_def
  apply clarsimp
  by (smt (verit, del_insts) LooseState_expn')

subsection \<open>Helper Rules\<close>

lemma \<phi>frame0:
  "\<p>\<r>\<o>\<c> f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<rbrace>"
  using \<phi>frame[where E=0, simplified, folded zero_fun_def] .

lemma \<phi>CONSEQ'E:
   "(\<And>v. E v \<s>\<h>\<i>\<f>\<t>\<s> E' v \<w>\<i>\<t>\<h> P3)
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> A  \<longmapsto> B  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> A \<longmapsto> B \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' "
  using \<phi>CONSEQ view_shift_refl by blast

lemmas \<phi>CONSEQ'E0 = \<phi>CONSEQ'E[OF view_shift_0, unfolded zero_fun_eta]

subsubsection \<open>Case Analysis\<close>

lemma \<phi>CASE:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> A \<longmapsto> C \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> B \<longmapsto> C \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> A + B \<longmapsto> C \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>Procedure_def
  by (simp add: distrib_left)

lemma \<phi>CASE_VS:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P1
\<Longrightarrow> B \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P2
\<Longrightarrow> B + A \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P2 \<or> P1\<close>
  unfolding View_Shift_def
  by (simp add: distrib_left)

lemma \<phi>CASE_IMP:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P1
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P2
\<Longrightarrow> B + A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P2 \<or> P1\<close>
  unfolding Transformation_def
  by (simp add: distrib_left)


subsubsection \<open>Normalization in Precondition\<close>

lemma norm_precond_conj:
  "(\<p>\<r>\<o>\<c> f \<lbrace> T \<s>\<u>\<b>\<j> P \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E) = (P \<longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> T \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E )"
  unfolding \<phi>Procedure_def
  by (simp add: INTERP_SPEC_subj Subjection_expn_set) blast

lemmas norm_precond_conj_metaeq[unfolded atomize_eq[symmetric]] = norm_precond_conj

lemma norm_precond_ex:
  "(\<p>\<r>\<o>\<c> f \<lbrace> ExSet X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E) = (\<forall>x. \<p>\<r>\<o>\<c> f \<lbrace> X x \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)"
  unfolding \<phi>Procedure_def
  by (simp add: INTERP_SPEC_ex ExSet_expn_set) blast


ML_file \<open>library/syntax/syntax0.ML\<close>


section \<open>Reasoning Configuration\<close>

subsection \<open>Normalization of Assertions\<close>

consts semantic_mode :: mode
       ABNORMAL :: mode

ML \<open>
structure Assertion_SS_Abnormal = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>assertion_simps_abnormal\<close>
  val comment = "Simp rules normalizing particularly the abnormal spec of a triple."
  val attribute = NONE
  val post_merging = I
)
\<close>

\<phi>reasoner_ML assertion_simp_abnormal 1300
  (\<open>Simplify (assertion_simps ABNORMAL) ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Abnormal.get' ctxt)) {fix_vars=false}) o snd\<close>

\<phi>reasoner_ML semantic_simps 1200
  (\<open>Premise semantic_mode _\<close> | \<open>Simplify semantic_mode ?X' ?X\<close>
     )
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) (fn ctxt =>
        Simplifier.clear_simpset ctxt addsimps @{thms \<phi>V_simps \<phi>arg.sel \<phi>arg.collapse}) {fix_vars=false}) o snd\<close>

lemmas [assertion_simps] =
  \<phi>V_simps

end
