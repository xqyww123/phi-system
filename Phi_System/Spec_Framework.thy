chapter \<open>Specification Framework\<close>

theory Spec_Framework
  imports Phi_BI "Phi_Semantics_Framework.Phi_Semantics_Framework"
begin

section \<open>Specification of Value\<close>

subsection \<open>Primitive \<phi>-Types\<close>

subsubsection \<open>Value\<close>

definition Val :: \<open>VAL sem_value \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> ('x::one, 'a) \<phi>\<close> ("\<^bold>v\<^bold>a\<^bold>l[_] _" [22,22] 21)
  where \<open>Val val T = (\<lambda>x. 1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j sem_value.dest val \<in> (x \<Ztypecolon> T))\<close>

lemma Val_expn [\<phi>expns]:
  \<open>(x \<Ztypecolon> Val val T) = (1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j sem_value.dest val \<in> (x \<Ztypecolon> T))\<close>
  unfolding Val_def \<phi>Type_def by (simp add: \<phi>expns)

lemma Val_inhabited [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Val val T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast


paragraph \<open>Syntax\<close>
(* TODO: move this *)

consts anonymous :: 'a

syntax val_syntax :: "logic \<Rightarrow> logic" ("\<^bold>v\<^bold>a\<^bold>l _" [22] 21)

translations
  "\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T" => "x \<Ztypecolon> CONST Val (CONST anonymous) T"
  "\<^bold>v\<^bold>a\<^bold>l T" => "CONST Val (CONST anonymous) T"


subsection \<open>Properties\<close>

subsubsection \<open>Semantic Type\<close>

definition \<phi>SemType :: "vassn \<Rightarrow> TY \<Rightarrow> bool"
  where \<open>\<phi>SemType S TY \<longleftrightarrow> S \<subseteq> Well_Type TY\<close>
  \<comment> \<open>Values specified by \<open>S\<close> are all of semantic type \<open>TY\<close>.\<close>

abbreviation \<phi>\<phi>SemType :: "(VAL, 'a) \<phi> \<Rightarrow> TY \<Rightarrow> bool"
  where \<open>\<phi>\<phi>SemType T TY \<equiv> (\<forall>x. \<phi>SemType (x \<Ztypecolon> T) TY)\<close>

lemma \<phi>SemType_unique:
  \<open> S \<noteq> {}
\<Longrightarrow> \<phi>SemType S T1
\<Longrightarrow> \<phi>SemType S T2
\<Longrightarrow> T1 = T2\<close>
  unfolding \<phi>SemType_def subset_iff
  using Well_Type_unique by blast

definition SemTyp_Of :: \<open>VAL set \<Rightarrow> TY\<close>
  where \<open>SemTyp_Of S = (@TY. \<phi>SemType S TY)\<close>

lemma SemTyp_Of_I[intro!, simp]:
  \<open>S \<noteq> {} \<Longrightarrow> \<phi>SemType S TY \<Longrightarrow> SemTyp_Of S = TY\<close>
  unfolding SemTyp_Of_def
  using \<phi>SemType_unique by blast 

lemma [\<phi>reason]:
  \<open> (\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY)
\<Longrightarrow> \<phi>\<phi>SemType T TY\<close>
  ..

lemma [\<phi>reason 1]:
  \<open>FAIL TEXT(\<open>Fail to reason the semantic type of\<close> X)
\<Longrightarrow> \<phi>SemType X Any\<close>
  by blast

subsubsection \<open>Zero Value\<close>

definition \<phi>Zero :: "TY \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool"
  where "\<phi>Zero ty T x \<longleftrightarrow> Zero ty \<in> Some ` (x \<Ztypecolon> T)"

subsubsection \<open>Equality\<close>

definition \<phi>Equal :: "(VAL,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "\<phi>Equal T can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 res.
    can_eq x1 x2 \<and> p1 \<in> (x1 \<Ztypecolon> T) \<and> p2 \<in> (x2 \<Ztypecolon> T)
      \<longrightarrow> Can_EqCompare res p1 p2 \<and> (EqCompare p1 p2 = eq x1 x2))"


subsubsection \<open>Functional\<close>

lemma is_singletonI'':
  \<open> \<exists>p. p \<in> A
\<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y)
\<Longrightarrow> is_singleton A\<close>
  by (metis equals0D is_singletonI')



section \<open>Specification of Monadic States\<close>

definition StrictStateTy :: "('ret sem_value \<Rightarrow> rassn)
                          \<Rightarrow> (VAL sem_value \<Rightarrow> rassn)
                          \<Rightarrow> 'ret state set" ("!\<S>")
  where "!\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val
                              | Exception val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False
                              | PartialCorrect \<Rightarrow> False}"

definition LooseStateTy  :: "('ret sem_value \<Rightarrow> rassn)
                          \<Rightarrow> (VAL sem_value \<Rightarrow> rassn)
                          \<Rightarrow> 'ret state set" ("\<S>")
  where  "\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val
                              | Exception val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False
                              | PartialCorrect \<Rightarrow> True}"

lemma StrictStateTy_expn[iff]:
        "Success vs x \<in> !\<S> T E \<equiv> x \<in> T vs"
        "Exception v x \<in> !\<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> !\<S> T E)"
        "\<not> (PartialCorrect \<in> !\<S> T E)"
  and LooseStateTy_expn[iff]:
        "Success vs x \<in> \<S> T E \<equiv> x \<in> T vs"
        "Exception v x \<in> \<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> \<S> T E)"
        "(PartialCorrect \<in> \<S> T E)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)

lemma LooseStateTy_expn' :
    "x \<in> \<S> T E \<longleftrightarrow> x = PartialCorrect
                 \<or> (\<exists>x' v. x = Success v x' \<and> x' \<in> T v)
                 \<or> (\<exists>x' v. x = Exception v x' \<and> x' \<in> E v)"
  by (cases x) simp_all

lemma StrictStateTy_elim[elim]:
    "s \<in> !\<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Exception v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> C" by (cases s) auto

lemma StrictStateTy_intro[intro]:
    " x \<in> T v \<Longrightarrow> Success v x \<in> !\<S> T E"
    " x \<in> E v \<Longrightarrow> Exception v x \<in> !\<S> T E"
  by simp_all

lemma LooseStateTy_E[elim]:
    "s \<in> \<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Exception v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C)
\<Longrightarrow> C"
  by (cases s) auto

lemma LooseStateTy_I[intro]:
  "x \<in> T v \<Longrightarrow> Success v x \<in> \<S> T E"
  "x \<in> E v \<Longrightarrow> Exception v x \<in> \<S> T E"
  "PartialCorrect \<in> \<S> T E"
  by simp_all

lemma LooseStateTy_upgrade:
  "s \<in> \<S> T E \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E"
  by (cases s) auto

lemma StrictStateTy_degrade: "s \<in> !\<S> T E \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto

lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E) \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto

lemma StrictStateTy_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> !\<S> A E \<subseteq> !\<S> A' E'\<close>
  unfolding subset_iff StrictStateTy_def by simp
lemma StrictStateTy_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> !\<S> A E \<Longrightarrow> s \<in> !\<S> A' E'\<close>
  unfolding StrictStateTy_def by (cases s; simp)

lemma LooseStateTy_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> \<S> A E \<subseteq> \<S> A' E'\<close>
  unfolding subset_iff LooseStateTy_def by simp
lemma LooseStateTy_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> \<S> A E \<Longrightarrow> s \<in> \<S> A' E'\<close>
  unfolding LooseStateTy_def by (cases s; simp)


lemma LooseStateTy_plus[iff]:
(*  \<open>\<S> (A + B) E   = \<S> A E + \<S> B E\<close> *)
  \<open>\<S> X (\<lambda>v. EA v + EB v) = \<S> X EA + \<S> X EB\<close>
  unfolding set_eq_iff LooseStateTy_def by simp_all
lemma StrictStateTy_plus[iff]:
(*  \<open>!\<S> (A + B) E   = !\<S> A E  + !\<S> B E\<close> *)
  \<open>!\<S> X (\<lambda>v. EA v + EB v) = !\<S> X EA + !\<S> X EB\<close>
  unfolding set_eq_iff StrictStateTy_def by simp_all

abbreviation \<open>Void \<equiv> (1::assn)\<close>


section \<open>Specification of Fictional Resource\<close>

declare INTERP_SPEC[\<phi>expns]

lemma  INTERP_SPEC_subj[\<phi>expns]:
  \<open> INTERP_SPEC (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (INTERP_SPEC S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<close>
  unfolding INTERP_SPEC_def by (simp add: \<phi>expns set_eq_iff, blast)

lemma  INTERP_SPEC_ex[\<phi>expns]:
  \<open> INTERP_SPEC (ExSet S) = (\<exists>\<^sup>s x. INTERP_SPEC (S x)) \<close>
  unfolding INTERP_SPEC_def by (simp add: \<phi>expns set_eq_iff, blast)

abbreviation COMMA
  :: \<open>assn \<Rightarrow> assn \<Rightarrow> assn\<close> (infixl "\<heavy_comma>" 13)
  where \<open>COMMA \<equiv> (*)\<close>


section \<open>Specification of Computation\<close>

definition \<phi>Procedure :: "'ret proc
                        \<Rightarrow> assn
                        \<Rightarrow> ('ret sem_value \<Rightarrow> assn)
                        \<Rightarrow> (VAL sem_value \<Rightarrow> assn)
                        \<Rightarrow> bool"
    ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _ \<rbrace>))" [101,2,2,2] 100)
  where "\<phi>Procedure f T U E \<longleftrightarrow>
    (\<forall>comp R. comp \<in> INTERP_SPEC (R * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_SPEC (R * U v)) (\<lambda>v. INTERP_SPEC (R * E v)))"

abbreviation \<phi>Procedure_no_exception ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<rbrace>))" [101,2,2] 100)
  where \<open>\<phi>Procedure_no_exception f T U \<equiv> \<phi>Procedure f T U 0\<close>

lemma \<phi>Procedure_alt:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<longmapsto> U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<longleftrightarrow> (\<forall>comp r. comp \<in> INTERP_SPEC ({r} * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_SPEC ({r} * U v)) (\<lambda>v. INTERP_SPEC ({r} * E v)))\<close>
  apply rule
  apply ((unfold \<phi>Procedure_def)[1], blast)
  unfolding \<phi>Procedure_def INTERP_SPEC subset_iff
  apply (clarsimp simp add: times_set_def split_state_All INTERP_SPEC_def)
  by metis

lemmas \<phi>Procedure_I = \<phi>Procedure_alt[THEN iffD2]

subsubsection \<open>Syntax\<close>

ML_file \<open>library/syntax/procedure.ML\<close>

(*
subsubsection \<open>Syntax\<close>

parse_translation \<open> let
  val typ_tag = Const (\<^type_syntax>\<open>proc\<close>, dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
        $ Free ("VAL", dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
  fun do_tag_E E = Const (\<^syntax_const>\<open>_constrain\<close>, dummyT) $ E $ typ_tag
  fun tag_E (E as Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free _ $ _) = do_tag_E E
    | tag_E (E as Const (\<^syntax_const>\<open>_constrain\<close>, _) $ _ $ _) = E
    | tag_E E = do_tag_E E
in [
  ("\<^const>local.\<phi>Procedure", (fn ctxt => fn [f,T,U,E] =>
    (Const("\<^const>local.\<phi>Procedure", dummyT) $ tag_E f $ T $ U $ E))),
  ("\<^const>local.\<phi>Procedure_no_exception", (fn ctxt => fn [f,T,U] =>
    (Const("\<^const>local.\<phi>Procedure_no_exception", dummyT) $ tag_E f $ T $ U)))
] end\<close> *)


section \<open>View Shift\<close>

definition View_Shift
    :: "assn \<Rightarrow> assn \<Rightarrow> bool \<Rightarrow> bool" ("(2\<^bold>v\<^bold>i\<^bold>e\<^bold>w _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
  where "View_Shift T U P \<longleftrightarrow> (\<forall>x R. x \<in> INTERP_SPEC (R * T) \<longrightarrow> x \<in> INTERP_SPEC (R * U) \<and> P)"

abbreviation Simple_View_Shift
    :: "assn \<Rightarrow> assn \<Rightarrow> bool" ("(2\<^bold>v\<^bold>i\<^bold>e\<^bold>w _/ \<longmapsto> _)"  [13,13] 12)
  where \<open>Simple_View_Shift T U \<equiv> View_Shift T U True\<close>

lemma View_Shift_imply_P:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> (P1 \<longrightarrow> P2)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2\<close>
  unfolding View_Shift_def
  by blast

lemma view_shift_by_implication[intro?, \<phi>reason 10]:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Imply_def View_Shift_def INTERP_SPEC_def
  by (clarsimp, metis set_mult_expn)

lemma view_shift_0[\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> X\<close>
  by (blast intro: view_shift_by_implication zero_implies_any)

lemma view_shift_id[\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<longmapsto> ?B \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> A"
  by (blast intro: view_shift_by_implication implies_refl)

lemma view_shift_id_ty[\<phi>reason 30 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?x \<Ztypecolon> ?T \<longmapsto> ?y \<Ztypecolon> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> T \<longmapsto> y \<Ztypecolon> T"
  by (blast intro: view_shift_by_implication implies_refl_ty)

lemma view_shift_union[\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X + Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X + Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  by (simp add: View_Shift_def distrib_left)+

lemma \<phi>view_shift_trans:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> (P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q)
    \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding View_Shift_def by blast

lemma \<phi>frame_view:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R * A \<longmapsto> R * B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc)

lemma \<phi>view_shift_intro_frame:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R * U' \<longmapsto> R * U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  by (simp add: \<phi>frame_view)

lemma \<phi>view_shift_intro_frame_R:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w U' * R \<longmapsto> U * R \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  by (simp add: \<phi>frame_view mult.commute)


section \<open>Fundamental Hoare Rules \& SL Rules\<close>

lemma \<phi>SKIP[simp,intro!]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c det_lift (Success v) \<lbrace> T v \<longmapsto> T \<rbrace>"
  unfolding \<phi>Procedure_def det_lift_def by clarsimp

lemma \<phi>SEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> (\<And>vs. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g vs \<lbrace> B vs \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<bind> g) \<lbrace> A \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding \<phi>Procedure_def bind_def apply (clarsimp simp add: subset_iff)
  subgoal for comp R x s
    apply (cases s; clarsimp; cases x; clarsimp; blast) . .

lemma \<phi>frame:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>ex. R * E ex \<rbrace>"
  unfolding \<phi>Procedure_def subset_iff
  apply clarify subgoal premises prems for comp R' s
    using prems(1)[THEN spec[where x=comp], THEN spec[where x=\<open>R' * R\<close>],
          simplified mult.assoc, THEN mp, OF prems(2)] prems(3) by blast .

lemma \<phi>frame0:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<rbrace>"
  using \<phi>frame[where E=0, simplified, folded zero_fun_def] .

lemma \<phi>frame_view_right:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A * R \<longmapsto> B * R \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc mult.commute)

lemma \<phi>view_refl:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X \<close>
  unfolding View_Shift_def by blast

lemma \<phi>view_trans:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2\<close>
  unfolding View_Shift_def by blast

lemma \<phi>CONSEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A  \<longmapsto> B  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<rbrace>
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A' \<longmapsto> A \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1
\<Longrightarrow> (\<And>ret. \<^bold>v\<^bold>i\<^bold>e\<^bold>w B ret \<longmapsto> B' ret \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2)
\<Longrightarrow> (\<And>ex.  \<^bold>v\<^bold>i\<^bold>e\<^bold>w E ex  \<longmapsto> E' ex  \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any3)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A' \<longmapsto> B' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>"
  unfolding \<phi>Procedure_def View_Shift_def subset_iff
  apply clarsimp
  by (smt (verit, del_insts) LooseStateTy_expn')

lemma \<phi>CONSEQ'E:
   "(\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v \<^bold>w\<^bold>i\<^bold>t\<^bold>h P3)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A  \<longmapsto> B  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>"
  using \<phi>CONSEQ view_shift_id by blast


end