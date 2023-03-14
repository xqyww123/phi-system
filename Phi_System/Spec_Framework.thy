chapter \<open>Specification Framework\<close>

theory Spec_Framework
  imports Phi_Refinement_Algebra "Phi_Semantics_Framework.Phi_Semantics_Framework"
  abbrevs "<shifts>" = "\<s>\<h>\<i>\<f>\<t>\<s>"
    and   "<val>" = "\<v>\<a>\<l>"
begin

section \<open>Specification of Value\<close>

type_synonym rassn = \<open>resource set\<close>
type_synonym vassn = \<open>VAL set\<close>

subsection \<open>Primitive \<phi>-Types\<close>

subsubsection \<open>Value\<close>

definition Val :: \<open>VAL \<phi>arg \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> ('x::one, 'a) \<phi>\<close> ("\<v>\<a>\<l>[_] _" [22,22] 21)
  where \<open>Val val T = (\<lambda>x. 1 \<s>\<u>\<b>\<j> \<phi>arg.dest val \<in> (x \<Ztypecolon> T))\<close>

lemma Val_expn [\<phi>expns]:
  \<open>(x \<Ztypecolon> Val val T) = (1 \<s>\<u>\<b>\<j> \<phi>arg.dest val \<in> (x \<Ztypecolon> T))\<close>
  unfolding Val_def \<phi>Type_def by (simp add: \<phi>expns)

lemma Val_inhabited [\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> Val val T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma Val_inhabited_rewr:
  \<open>Inhabited (x \<Ztypecolon> Val val T) \<longleftrightarrow> \<phi>arg.dest val \<in> (x \<Ztypecolon> T)\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns)

paragraph \<open>Syntax\<close>

consts anonymous :: 'a

syntax val_syntax :: "logic \<Rightarrow> logic" ("\<v>\<a>\<l> _" [22] 21)

translations
  "\<v>\<a>\<l> x \<Ztypecolon> T" => "x \<Ztypecolon> CONST Val (CONST anonymous) T"
  "\<v>\<a>\<l> T" => "CONST Val (CONST anonymous) T"

ML_file \<open>library/syntax/value.ML\<close>


subsubsection \<open>Abnormality\<close>

definition AbnormalObj :: \<open>VAL \<phi>arg \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> ('x::one, 'a) \<phi>\<close>
  where \<open>AbnormalObj \<equiv> Val\<close>

(*TODO: more about exception

Any exception object will be specified by this type. and by this we clarify the difference
between a value and an exception object.
Then in exception specs, any Val is senseless and will be removed.*)


subsection \<open>Semantic Type\<close>

subsubsection \<open>Single Value\<close>

definition \<phi>SemType :: "vassn \<Rightarrow> TY \<Rightarrow> bool"
  where \<open>\<phi>SemType S TY \<longleftrightarrow> S \<subseteq> Well_Type TY\<close>
  \<comment> \<open>Values specified by \<open>S\<close> are all of semantic type \<open>TY\<close>.\<close>

abbreviation \<phi>\<phi>SemType :: "(VAL, 'a) \<phi> \<Rightarrow> TY \<Rightarrow> bool"
  where \<open>\<phi>\<phi>SemType T TY \<equiv> (\<forall>x. \<phi>SemType (x \<Ztypecolon> T) TY)\<close>

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

lemma [\<phi>reason 100]:
  \<open> (\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY)
\<Longrightarrow> \<phi>\<phi>SemType T TY\<close>
  ..

subsubsection \<open>Multiple Values\<close>

definition Well_Typed_Vals :: \<open>TY list \<Rightarrow> 'a::VALs \<phi>arg set\<close>
  where \<open>Well_Typed_Vals TYs = {vs. list_all2 (\<lambda>v T. v \<in> Well_Type T) (to_vals (\<phi>arg.dest vs)) TYs}\<close>

definition \<phi>_Have_Types :: \<open>('a::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> TY list \<Rightarrow> bool\<close>
  where \<open>\<phi>_Have_Types spec TYs = (\<forall>v. Inhabited (spec v) \<longrightarrow> v \<in> Well_Typed_Vals TYs)\<close>

declare [[\<phi>reason_default_pattern \<open>\<phi>_Have_Types ?S _\<close> \<Rightarrow> \<open>\<phi>_Have_Types ?S _\<close> (100)]]


subsubsection \<open>Reasoning Rules\<close>

declare [[\<phi>reason_default_pattern \<open>\<phi>SemType ?S ?TY\<close> \<Rightarrow> \<open>\<phi>SemType ?S _\<close> (100) ]]

lemma [\<phi>reason 1]:
  \<open>FAIL TEXT(\<open>Fail to reason the semantic type of\<close> X)
\<Longrightarrow> \<phi>SemType X Any\<close>
  by blast

lemma [\<phi>reason 1000]:
  \<open> \<phi>SemType X TY
\<Longrightarrow> \<phi>SemType Y TY
\<Longrightarrow> \<phi>SemType (X + Y) TY\<close>
  unfolding \<phi>SemType_def subset_iff by simp

lemma [\<phi>reason 1000]:
  \<open> \<phi>SemType X TY
\<Longrightarrow> \<phi>SemType (X \<s>\<u>\<b>\<j> P) TY\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: Subjection_expn)

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. \<phi>SemType (X x) TY)
\<Longrightarrow> \<phi>SemType (ExSet X) TY\<close>
  unfolding \<phi>SemType_def subset_iff by (clarsimp simp add: ExSet_expn)


subsection \<open>Zero Value\<close>

definition \<phi>Zero :: "TY \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool"
  where "\<phi>Zero ty T x \<longleftrightarrow> Zero ty \<in> Some ` (x \<Ztypecolon> T)"

declare [[\<phi>reason_default_pattern \<open>\<phi>Zero ?TY ?T ?x\<close> \<Rightarrow> \<open>\<phi>Zero ?TY ?T _\<close> (100) ]]

subsection \<open>Equality\<close>

definition \<phi>Equal :: "(VAL,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "\<phi>Equal T can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 res.
    can_eq x1 x2 \<and> p1 \<in> (x1 \<Ztypecolon> T) \<and> p2 \<in> (x2 \<Ztypecolon> T)
      \<longrightarrow> Can_EqCompare res p1 p2 \<and> (EqCompare p1 p2 = eq x1 x2))"

declare [[\<phi>reason_default_pattern \<open>\<phi>Equal ?TY ?can_eq ?eq\<close> \<Rightarrow> \<open>\<phi>Equal ?TY _ _\<close> (100) ]]

subsection \<open>Functional\<close>

definition is_functional :: \<open>'a set \<Rightarrow> bool\<close>
  where \<open>is_functional S \<longleftrightarrow> (\<forall>x y. x \<in> S \<and> y \<in> S \<longrightarrow> x = y)\<close>

declare [[\<phi>reason_default_pattern \<open>is_functional ?S\<close> \<Rightarrow> \<open>is_functional ?S\<close> (100)]]

lemma is_functional_alt:
  \<open>is_functional S \<longleftrightarrow> (S = {} \<or> (\<exists>x. S = {x}))\<close>
  unfolding is_functional_def by blast

lemma is_functional_I[intro!]:
  \<open> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y)
\<Longrightarrow> is_functional A \<close>
  unfolding is_functional_def by blast

lemma is_functional_imp:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'
\<Longrightarrow> is_functional S'
\<Longrightarrow> is_functional S\<close>
  unfolding Imply_def is_functional_def
  by blast

lemma is_singletonI'':
  \<open> \<exists>p. p \<in> A \<comment> \<open>TODO: model this\<close>
\<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y)
\<Longrightarrow> is_singleton A\<close>
  by (metis equals0D is_singletonI')

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>Fail to prove\<close> S \<open>is functional\<close>)
\<Longrightarrow> is_functional S\<close>
  by blast

section \<open>Specification of Monadic States\<close>

definition StrictStateSpec :: "('ret::VALs \<phi>arg \<Rightarrow> rassn)
                          \<Rightarrow> (ABNM \<Rightarrow> rassn)
                          \<Rightarrow> 'ret state set" ("!\<S>")
  where "!\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val
                              | Abnormality val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False
                              | NonTerm \<Rightarrow> False
                              | AssumptionBroken \<Rightarrow> False
                  }"

definition LooseStateSpec  :: "('ret::VALs \<phi>arg \<Rightarrow> rassn)
                          \<Rightarrow> (ABNM \<Rightarrow> rassn)
                          \<Rightarrow> 'ret state set" ("\<S>")
  where  "\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val
                              | Abnormality val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False
                              | NonTerm \<Rightarrow> True
                              | AssumptionBroken \<Rightarrow> True
                  }"

lemma StrictStateSpec_expn[iff]:
        "Success vs x \<in> !\<S> T E \<equiv> x \<in> T vs"
        "Abnormality v x \<in> !\<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> !\<S> T E)"
        "\<not> (NonTerm \<in> !\<S> T E)"
        "\<not> (AssumptionBroken \<in> !\<S> T E)"
        "\<not> {Invalid} \<subseteq> !\<S> T E"
        "\<not> {NonTerm} \<subseteq> !\<S> T E"
        "\<not> {AssumptionBroken} \<subseteq> !\<S> T E"
  and LooseStateSpec_expn[iff]:
        "Success vs x \<in> \<S> T E \<equiv> x \<in> T vs"
        "Abnormality v x \<in> \<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> \<S> T E)"
        "(NonTerm \<in> \<S> T E)"
        "(AssumptionBroken \<in> \<S> T E)"
        "\<not> {Invalid} \<subseteq> \<S> T E"
        "{NonTerm} \<subseteq> \<S> T E"
        "{AssumptionBroken} \<subseteq> \<S> T E"
  by (simp_all add: StrictStateSpec_def LooseStateSpec_def)

lemma LooseStateSpec_expn' :
    "x \<in> \<S> T E \<longleftrightarrow> x = NonTerm
                 \<or> x = AssumptionBroken
                 \<or> (\<exists>x' v. x = Success v x' \<and> x' \<in> T v)
                 \<or> (\<exists>x' v. x = Abnormality v x' \<and> x' \<in> E v)"
  by (cases x) simp_all

lemma StrictStateSpec_elim[elim]:
    "s \<in> !\<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Abnormality v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> C" by (cases s) auto

lemma StrictStateSpec_intro[intro]:
    " x \<in> T v \<Longrightarrow> Success v x \<in> !\<S> T E"
    " x \<in> E a \<Longrightarrow> Abnormality a x \<in> !\<S> T E"
  by simp_all

lemma LooseStateSpec_E[elim]:
    "s \<in> \<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Abnormality v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> (s = NonTerm \<Longrightarrow> C)
\<Longrightarrow> (s = AssumptionBroken \<Longrightarrow> C)
\<Longrightarrow> C"
  by (cases s) auto

lemma LooseStateSpec_I[intro]:
  "x \<in> T v \<Longrightarrow> Success v x \<in> \<S> T E"
  "x \<in> E a \<Longrightarrow> Abnormality a x \<in> \<S> T E"
  "NonTerm \<in> \<S> T E"
  "AssumptionBroken \<in> \<S> T E"
  by simp_all

lemma LooseStateSpec_upgrade:
  "s \<in> \<S> T E \<Longrightarrow> s \<noteq> AssumptionBroken \<Longrightarrow> s \<noteq> NonTerm \<Longrightarrow> s \<in> !\<S> T E"
  by (cases s) auto

lemma StrictStateSpec_degrade: "s \<in> !\<S> T E \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto

lemma LooseStateSpec_introByStrict:
  "(s \<noteq> AssumptionBroken \<Longrightarrow> s \<noteq> NonTerm \<Longrightarrow> s \<in> !\<S> T E) \<Longrightarrow> s \<in> \<S> T E"
  by (cases s) auto

lemma StrictStateSpec_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> !\<S> A E \<subseteq> !\<S> A' E'\<close>
  unfolding subset_iff StrictStateSpec_def by simp
lemma StrictStateSpec_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> !\<S> A E \<Longrightarrow> s \<in> !\<S> A' E'\<close>
  unfolding StrictStateSpec_def by (cases s; simp)

lemma LooseStateSpec_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> \<S> A E \<subseteq> \<S> A' E'\<close>
  unfolding subset_iff LooseStateSpec_def by simp
lemma LooseStateSpec_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> \<S> A E \<Longrightarrow> s \<in> \<S> A' E'\<close>
  unfolding LooseStateSpec_def by (cases s; simp)


lemma LooseStateSpec_plus[iff]:
(*  \<open>\<S> (A + B) E   = \<S> A E + \<S> B E\<close> *)
  \<open>\<S> X (\<lambda>v. EA v + EB v) = \<S> X EA + \<S> X EB\<close>
  unfolding set_eq_iff LooseStateSpec_def by simp_all
lemma StrictStateSpec_plus[iff]:
(*  \<open>!\<S> (A + B) E   = !\<S> A E  + !\<S> B E\<close> *)
  \<open>!\<S> X (\<lambda>v. EA v + EB v) = !\<S> X EA + !\<S> X EB\<close>
  unfolding set_eq_iff StrictStateSpec_def by simp_all

abbreviation \<open>Void \<equiv> (1::assn)\<close>


section \<open>Specification of Fictional Resource\<close>

declare INTERP_SPEC[\<phi>expns]

lemma  INTERP_SPEC_subj[\<phi>expns]:
  \<open> INTERP_SPEC (S \<s>\<u>\<b>\<j> P) = (INTERP_SPEC S \<s>\<u>\<b>\<j> P) \<close>
  unfolding INTERP_SPEC_def by (simp add: \<phi>expns set_eq_iff, blast)

lemma  INTERP_SPEC_ex[\<phi>expns]:
  \<open> INTERP_SPEC (ExSet S) = (\<exists>\<^sup>s x. INTERP_SPEC (S x)) \<close>
  unfolding INTERP_SPEC_def by (simp add: \<phi>expns set_eq_iff, blast)

abbreviation COMMA :: \<open>assn \<Rightarrow> assn \<Rightarrow> assn\<close> ("_\<heavy_comma>/ _" [15,16] 15)
  where \<open>COMMA \<equiv> (*)\<close>


section \<open>Specification of Computation\<close>

definition \<phi>Procedure :: "'ret::VALs proc
                        \<Rightarrow> assn
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> assn)
                        \<Rightarrow> (ABNM \<Rightarrow> assn)
                        \<Rightarrow> bool"
    ("\<p>\<r>\<o>\<c> (2_)/ (0\<lbrace> _/ \<longmapsto> _ \<rbrace>)/ \<t>\<h>\<r>\<o>\<w>\<s> (100_)/ " [101,2,2,100] 100)
  where "\<phi>Procedure f T U E \<longleftrightarrow>
    (\<forall>comp R. comp \<in> INTERP_SPEC (R * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_SPEC (R * U v)) (\<lambda>v. INTERP_SPEC (R * E v)))"

abbreviation \<phi>Procedure_no_exception ("\<p>\<r>\<o>\<c> (2_)/ \<lbrace> (2_) \<longmapsto>/ (2_) \<rbrace>/ " [101,2,2] 100)
  where \<open>\<phi>Procedure_no_exception f T U \<equiv> \<phi>Procedure f T U 0\<close>

lemma \<phi>Procedure_alt:
  \<open>\<p>\<r>\<o>\<c> f \<lbrace> T \<longmapsto> U \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<longleftrightarrow> (\<forall>comp r. comp \<in> INTERP_SPEC ({r} * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_SPEC ({r} * U v)) (\<lambda>v. INTERP_SPEC ({r} * E v)))\<close>
  apply rule
  apply ((unfold \<phi>Procedure_def)[1], blast)
  unfolding \<phi>Procedure_def INTERP_SPEC subset_iff
  apply (clarsimp simp add: times_set_def split_state_All INTERP_SPEC_def)
  by metis

lemmas \<phi>Procedure_I = \<phi>Procedure_alt[THEN iffD2]

subsubsection \<open>Syntax\<close>

ML_file \<open>library/syntax/procedure.ML\<close>

section \<open>View Shift\<close>

definition View_Shift
    :: "assn \<Rightarrow> assn \<Rightarrow> bool \<Rightarrow> bool" ("(2_/ \<s>\<h>\<i>\<f>\<t>\<s> _/ \<a>\<n>\<d> _)" [13,13,13] 12)
  where "View_Shift T U P \<longleftrightarrow> (\<forall>x R. x \<in> INTERP_SPEC (R * T) \<longrightarrow> x \<in> INTERP_SPEC (R * U) \<and> P)"

abbreviation Simple_View_Shift
    :: "assn \<Rightarrow> assn \<Rightarrow> bool" ("(2_/ \<s>\<h>\<i>\<f>\<t>\<s> _)"  [13,13] 12)
  where \<open>Simple_View_Shift T U \<equiv> View_Shift T U True\<close>

lemma View_Shift_imply_P:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P1
\<Longrightarrow> (P1 \<longrightarrow> P2)
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P2\<close>
  unfolding View_Shift_def
  by blast

lemma view_shift_by_implication[intro?, \<phi>reason 10]:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> B \<a>\<n>\<d> P\<close>
  unfolding Imply_def View_Shift_def INTERP_SPEC_def
  by (clarsimp, metis set_mult_expn)

lemma view_shift_0[\<phi>reason 2000 for \<open>0 \<s>\<h>\<i>\<f>\<t>\<s> ?X \<a>\<n>\<d> ?P\<close>]:
  \<open>0 \<s>\<h>\<i>\<f>\<t>\<s> X\<close>
  by (blast intro: view_shift_by_implication zero_implies_any)

lemma view_shift_refl[\<phi>reason 2000 for \<open>?A \<s>\<h>\<i>\<f>\<t>\<s> ?B \<a>\<n>\<d> ?P\<close>]:
  "A \<s>\<h>\<i>\<f>\<t>\<s> A"
  by (blast intro: view_shift_by_implication implies_refl)

lemma view_shift_refl_ty[\<phi>reason 30 for \<open>?x \<Ztypecolon> ?T \<s>\<h>\<i>\<f>\<t>\<s> ?y \<Ztypecolon> ?T \<a>\<n>\<d> ?P\<close>]:
  "\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<Longrightarrow> x \<Ztypecolon> T \<s>\<h>\<i>\<f>\<t>\<s> y \<Ztypecolon> T"
  by (blast intro: view_shift_by_implication implies_refl_ty)

lemma view_shift_union[\<phi>reason 800]:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> X + Y \<a>\<n>\<d> P\<close>
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> X + Y \<a>\<n>\<d> P\<close>
  by (simp add: View_Shift_def distrib_left)+

lemma \<phi>view_shift_trans:
  "A \<s>\<h>\<i>\<f>\<t>\<s> B \<a>\<n>\<d> P
    \<Longrightarrow> (P \<Longrightarrow> B \<s>\<h>\<i>\<f>\<t>\<s> C \<a>\<n>\<d> Q)
    \<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> C \<a>\<n>\<d> P \<and> Q"
  unfolding View_Shift_def by blast

lemma \<phi>frame_view:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> B \<a>\<n>\<d> P
\<Longrightarrow> R * A \<s>\<h>\<i>\<f>\<t>\<s> R * B \<a>\<n>\<d> P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc)

lemma \<phi>view_shift_intro_frame:
  "U' \<s>\<h>\<i>\<f>\<t>\<s> U \<a>\<n>\<d> P \<Longrightarrow> R * U' \<s>\<h>\<i>\<f>\<t>\<s> R * U \<a>\<n>\<d> P "
  by (simp add: \<phi>frame_view)

lemma \<phi>view_shift_intro_frame_R:
  "U' \<s>\<h>\<i>\<f>\<t>\<s> U \<a>\<n>\<d> P \<Longrightarrow> U' * R \<s>\<h>\<i>\<f>\<t>\<s> U * R \<a>\<n>\<d> P "
  by (simp add: \<phi>frame_view mult.commute)


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
  by (meson INTERP_SPEC set_mult_expn)

subsubsection \<open>View Shift\<close>

lemma \<phi>frame_view_right:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> B \<a>\<n>\<d> P
\<Longrightarrow> A * R \<s>\<h>\<i>\<f>\<t>\<s> B * R \<a>\<n>\<d> P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc mult.commute)

lemma \<phi>view_trans:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> B \<a>\<n>\<d> P1
\<Longrightarrow> (P1 \<Longrightarrow> B \<s>\<h>\<i>\<f>\<t>\<s> C \<a>\<n>\<d> P2)
\<Longrightarrow> A \<s>\<h>\<i>\<f>\<t>\<s> C \<a>\<n>\<d> P1 \<and> P2\<close>
  unfolding View_Shift_def by blast

lemma \<phi>CONSEQ:
   "\<p>\<r>\<o>\<c> f \<lbrace> A  \<longmapsto> B  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> A' \<s>\<h>\<i>\<f>\<t>\<s> A \<a>\<n>\<d> Any1
\<Longrightarrow> (\<And>ret. B ret \<s>\<h>\<i>\<f>\<t>\<s> B' ret \<a>\<n>\<d> Any2)
\<Longrightarrow> (\<And>ex.  E ex \<s>\<h>\<i>\<f>\<t>\<s> E' ex \<a>\<n>\<d> Any3)
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> A' \<longmapsto> B' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' "
  unfolding \<phi>Procedure_def View_Shift_def subset_iff
  apply clarsimp
  by (smt (verit, del_insts) LooseStateSpec_expn')

subsection \<open>Helper Rules\<close>

lemma \<phi>frame0:
  "\<p>\<r>\<o>\<c> f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<rbrace>"
  using \<phi>frame[where E=0, simplified, folded zero_fun_def] .

lemma \<phi>CONSEQ'E:
   "(\<And>v. E v \<s>\<h>\<i>\<f>\<t>\<s> E' v \<a>\<n>\<d> P3)
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
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P1
\<Longrightarrow> B \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P2
\<Longrightarrow> B + A \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P2 \<or> P1\<close>
  unfolding View_Shift_def
  by (simp add: distrib_left)

lemma \<phi>CASE_IMP:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P1
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P2
\<Longrightarrow> B + A \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P2 \<or> P1\<close>
  unfolding Imply_def
  by (simp add: distrib_left)


subsubsection \<open>Normalization in Precondition\<close>

lemma norm_precond_conj:
  "(\<p>\<r>\<o>\<c> f \<lbrace> T \<s>\<u>\<b>\<j> P \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E) = (P \<longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> T \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E )"
  unfolding \<phi>Procedure_def by (simp add: \<phi>expns) blast

lemmas norm_precond_conj_metaeq[unfolded atomize_eq[symmetric]] = norm_precond_conj

lemma norm_precond_ex:
  "(\<p>\<r>\<o>\<c> f \<lbrace> ExSet X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E) = (\<forall>x. \<p>\<r>\<o>\<c> f \<lbrace> X x \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)"
  unfolding \<phi>Procedure_def by (simp add: \<phi>expns) blast


ML_file \<open>library/syntax/syntax0.ML\<close>

end
