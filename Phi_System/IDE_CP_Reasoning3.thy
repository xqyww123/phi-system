chapter \<open>Reasoning Processes in IDE-CP - Part III\<close>

text \<open>Here we give the implementation of all large reasoning processes that are declared in
the previous part I.\<close>

theory IDE_CP_Reasoning3
  imports IDE_CP_Applications1
begin


(*subsubsection \<open>Syntax & Auxiliary\<close>

definition "addr_allocated heap addr \<longleftrightarrow> MemAddress addr \<in> dom heap"
adhoc_overloading allocated addr_allocated
                                                         
(* lemma addr_allocated_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> addr_allocated h addr \<Longrightarrow> addr_allocated h' addr"
  unfolding addr_allocated_def by auto
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto *)
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto

definition MemAddrState :: "heap \<Rightarrow> nat memaddr \<Rightarrow> 'b::lrep set \<Rightarrow> bool"
  where "MemAddrState h addr S \<longleftrightarrow> addr_allocated h addr \<and> shallowize (the (h (MemAddress addr))) \<in> S"
adhoc_overloading ResourceState MemAddrState

(*lemma MemAddrState_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> MemAddrState h' addr S"
  unfolding MemAddrState_def addr_allocated_def by auto (metis \<phi>set_mono domI map_le_def option.sel) *)

lemma MemAddrState_I_neq[intro]: "k2 \<noteq> k \<Longrightarrow> MemAddrState h k2 S \<Longrightarrow> MemAddrState (h(MemAddress k := v)) k2 S"
  and MemAddrState_I_eq[intro]: "v' \<in> S \<Longrightarrow> MemAddrState (h(MemAddress k \<mapsto> deepize v')) k S"
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_E[elim]:
  "MemAddrState h addr S \<Longrightarrow> (addr_allocated h addr \<Longrightarrow> Inhabited S \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding MemAddrState_def Inhabited_def by blast
lemma MemAddrState_I:
  "addr_allocated h addr \<Longrightarrow> shallowize (the (h (MemAddress addr))) \<in> S \<Longrightarrow> MemAddrState h addr S"
  unfolding MemAddrState_def by auto

(* lemma MemAddrState_retained_N[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<phi>Independent S claim
    \<Longrightarrow> Alive k \<in> claim \<Longrightarrow> MemAddrState (h(k:=None)) addr S"
  unfolding MemAddrState_def \<phi>Independent_def by auto
lemma MemAddrState_retained_S[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<phi>Independent S claim
    \<Longrightarrow> Write k \<in> claim \<Longrightarrow> MemAddrState (h(k \<mapsto> v)) addr S"
  unfolding MemAddrState_def \<phi>Independent_def by auto

*)


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<in> S \<Longrightarrow> h |` S \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<notin> S \<Longrightarrow> h |` (- S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)

*)

section \<open>Small Processes - I\<close>


(* subsubsection \<open>General Rules\<close>

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>VAL ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s VAL ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> VAL X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s VAL Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>OBJ ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> OBJ X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast) *)



subsection \<open>Case Analysis\<close>


lemma [\<phi>reason 1200]: "Premise mode (A = B x y) \<Longrightarrow> Premise mode (A = case_prod B (x,y))" by simp
lemma [\<phi>reason 1200]: "Premise mode (A = B x) \<Longrightarrow> Premise mode (A = case_named B (tag x))" by simp
(* lemma [\<phi>reason 1200]: "Premise mode (A = B a x) \<Longrightarrow> Premise mode (A = case_object B (a \<Zinj> x))" by simp *)

definition CaseSplit :: "bool \<Rightarrow> bool" where "CaseSplit x = x"
lemma [elim!]: "CaseSplit x \<Longrightarrow> (x \<Longrightarrow> C) \<Longrightarrow> C" unfolding CaseSplit_def .

lemma [elim!]:
  "y = case_prod f x \<Longrightarrow> (\<And>x1 x2. y = f x1 x2 \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp

(*lemma [elim!]:
  "y = (case x of a \<Zinj> b \<Rightarrow> f a b) \<Longrightarrow> (\<And>a b. y = f a b \<Longrightarrow> C (a \<Zinj> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp *)

lemma [elim!]:
  "y = (case x of tag a \<Rightarrow> f a) \<Longrightarrow> (\<And>a. y = f a \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp



subsection \<open>Same \<phi>-Type\<close>

definition SameNuTy :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " where "SameNuTy A B = True"
text \<open>Technical tag for reasoner converges \<phi>-types of two typings.\<close>

lemma [\<phi>reason 2000]: "SameNuTy (x \<Ztypecolon> T) (x' \<Ztypecolon> T) "
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy B B' \<Longrightarrow> SameNuTy (A * B) (A' * B')"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "(\<And>x. SameNuTy (A x) (A' x)) \<Longrightarrow> SameNuTy (ExSet A) (ExSet A')"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 1000]: "SameNuTy A A" \<comment> \<open>The fallback\<close>
  unfolding SameNuTy_def ..


subsection \<open>Cleaning\<close>

definition \<r>Clean :: \<open>'a::one set \<Rightarrow> bool\<close> where \<open>\<r>Clean S \<longleftrightarrow> (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1)\<close>

subsubsection \<open>Termination\<close>

lemma [\<phi>reason 3000]:
  \<open>\<r>Clean 1\<close>
  unfolding \<r>Clean_def Imply_def by simp

lemma [\<phi>reason 3000]:
  \<open>\<r>Clean (() \<Ztypecolon> \<phi>None)\<close>
  unfolding \<r>Clean_def Imply_def by simp

lemma [\<phi>reason 3000 for \<open>\<r>Clean (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C)\<close>]:
  \<open> \<r>Clean (x \<Ztypecolon> T ?\<^sub>\<phi> False) \<close>
  unfolding \<r>Clean_def Imply_def by simp

subsubsection \<open>Structural Node\<close>

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean A
\<Longrightarrow> \<r>Clean B
\<Longrightarrow> \<r>Clean (A * B)\<close>
  for A :: \<open>'a::sep_magma_1 set\<close>
  unfolding \<r>Clean_def Imply_def
  apply (simp add: \<phi>expns)
  using mult_1_class.mult_1_left by blast

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (y \<Ztypecolon> U)
\<Longrightarrow> \<r>Clean ((x,y) \<Ztypecolon> T \<^emph> U)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<r>Clean_def \<phi>Prod_expn' Imply_def
  apply (simp add: \<phi>expns)
  using mult_1_class.mult_1_left by blast

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  unfolding \<r>Clean_def Imply_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis fun_1upd1)

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T)\<close>
  unfolding \<r>Clean_def Imply_def
  apply (simp add: \<phi>expns)
  using push_map_1 by blast

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> n \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_mult, 'b) \<phi>\<close>
  unfolding \<r>Clean_def Imply_def apply (simp add: \<phi>expns)
  using share_right_one by blast


subsection \<open>Unification of \<lambda>-Abstraction\<close>

definition Function_over :: \<open>('a,'b) \<phi> \<Rightarrow> 'c \<Rightarrow> ('a, 'c \<Rightarrow> 'b) \<phi>\<close> (infix "<func-over>" 40)
  where \<open>(T <func-over> x) = (\<lambda>f. f x \<Ztypecolon> T)\<close>

text \<open>
  \<^term>\<open>f \<Ztypecolon> T <func-over> x\<close> constrains f is a function about x,
    i.e. \<^prop>\<open>f \<Ztypecolon> T <func-over> x \<equiv> f x \<Ztypecolon> T\<close>.
  It is useful to circumvent nondeterminacy in the higher-order unification between
    \<^schematic_term>\<open>?f x \<Ztypecolon> T\<close> and \<^term>\<open>g x \<Ztypecolon> T\<close> which has multiple solutions
    including \<^term>\<open>f = g\<close> or \<^term>\<open>f = (\<lambda>_. g x)\<close>.
  Concerning this, \<^term>\<open>f \<Ztypecolon> T <func-over> x\<close> clarifies the ambiguity by a specialized reasoner
    that forces the exhaustive solution, i.e., the residue of \<^schematic_term>\<open>?f\<close> contains no
    free occurrence of \<^term>\<open>x\<close>.

  This specialized reasoner is \<^term>\<open>lambda_abstraction x fx f\<close> as,

\<^prop>\<open> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s fx \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f \<Ztypecolon> T <func-over> x \<^bold>a\<^bold>n\<^bold>d P\<close>

  which does the lambda abstraction, \<open>f = \<lambda>x. fx\<close>.
\<close>

lemma Function_over_expn[\<phi>expns]:
  \<open>(f \<Ztypecolon> T <func-over> x) = (f x \<Ztypecolon> T)\<close>
  unfolding Function_over_def \<phi>Type_def by simp

lemma Function_over_case_named[simp]:
  \<open>(case_named f \<Ztypecolon> T <func-over> tag x) = (f \<Ztypecolon> T <func-over> x)\<close>
  by (simp add: \<phi>expns)

lemmas [unfolded atomize_eq[symmetric], named_expansion] = Function_over_case_named

lemma [\<phi>reason 2000]:
  \<open> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s fx \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f \<Ztypecolon> T <func-over> x \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def lambda_abstraction_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> f x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> f \<Ztypecolon> T <func-over> x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> fx \<Ztypecolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> f \<Ztypecolon> T <func-over> x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w f x \<Ztypecolon> T \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w f \<Ztypecolon> T <func-over> x \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse ?input (\<lambda>v. ?f \<Ztypecolon> ?T v <func-over> ?x :: assn)\<close>
]:
  \<open> Synthesis_Parse input (\<lambda>v. fx \<Ztypecolon> T v)
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Synthesis_Parse input (\<lambda>v. f \<Ztypecolon> T v <func-over> x :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> SYNTHESIS f x \<Ztypecolon> T v \<rbrace>  @action synthesis P
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> SYNTHESIS f \<Ztypecolon> T v <func-over> x \<rbrace>  @action synthesis P\<close>
  unfolding Synthesis_def lambda_abstraction_def by (simp add: \<phi>expns)


section \<open>Transformation of State Abstraction (ToSA)\<close>

text \<open>This is a reasoning procedure for transformations of abstraction of the whole computation
  state, which we name \<^emph>\<open>Transformation of State Abstraction (ToSA)\<close>.
  Specifications must be given in MTF.
  The procedure can recognize items specifying identical objects and
    invoke the reasoning for transforming the object from the source abstraction to the target
    abstraction.\<close>

text \<open>Priority Convention:
\<^item> 4000: Termination
\<^item> 3200: Very Safe Normalization
\<^item> 3150: Assigning Zeros
\<^item> 3000: Normalization
\<^item> 2800: Disjunction in source part
\<^item> 2700: Fixing existentially quantified variables
\<^item> 2500: Padding void holes after the last item. Rules capturing the last item in
        the \<open>\<^emph>\<close>-sequence should have priority higher than this.
\<^item> 2000~2300: Step-by-step searching
\<^item> 2300: Termination of the step-by-step searching
\<^item> 2100: Prior rules for specific patterns in the step-by-step searching
\<^item> 2000: Main rule of step-by-step searching
\<^item> \<le> 1999: Rules for searching specific object like value, variable, etc.
\<^item> 800:  Disjunction in target part
\<^item> \<le> 80: Rules for general searching. This feature is disabled in view shift
          because most of the global-state-level components are configured
          with properly search rules so the general search is not required.
\<close>


consts reason_ToSA  :: \<open>bool \<Rightarrow> subgoal \<Rightarrow> unit action\<close>
       subj_premise :: \<open>subgoal \<Rightarrow> mode\<close>


subsubsection \<open>Initialization\<close>

lemma [\<phi>reason 2020
    for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y @action ToSA' ?mode\<close>
    except \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y * \<blangle> ?YX \<brangle> @action ToSA' ?mode\<close>
]:
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> X' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> Y' \<brangle> \<^bold>a\<^bold>n\<^bold>d Any @action reason_ToSA mode G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y @action ToSA' mode\<close>
  unfolding Action_Tag_def Simplify_def FOCUS_TAG_def
  by (simp add: implies_weaken)


lemma [\<phi>reason 2000
    for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action ToSA' ?mode\<close>
    except \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y * \<blangle> ?YX \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action ToSA' ?mode\<close>
]:
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> X' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> Y' \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action ToSA' mode\<close>
  unfolding Action_Tag_def Simplify_def FOCUS_TAG_def
  by simp

lemma [\<phi>reason 2100 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action ToSA' ?mode\<close>]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action ToSA' mode\<close>
  unfolding Action_Tag_def using implies_refl .


subsubsection \<open>Termination\<close>

lemma ToSA_finish:  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> H \<brangle> @action reason_ToSA mode G"
  and ToSA_finish': "X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 * \<blangle> X \<brangle> @action reason_ToSA mode G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left FOCUS_TAG_def Action_Tag_def
  using implies_refl by this+

lemma ToSA_finish'':
  \<open> H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H'
\<Longrightarrow> H' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y @action reason_ToSA mode G
\<Longrightarrow> H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def using implies_trans by fastforce

lemma ToSA_finish''':
  \<open> R1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> R1\<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2\<heavy_comma> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P  @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def FOCUS_TAG_def
  using implies_right_prod .

ML \<open>
local
fun ToSA_unification rule1 rule2 (ctxt,sequent) =
  let
    val _ (*@action*) $ ( _ (*Trueprop*) $ ( _ (*VS*) $ _ $ X $ _ )) $ _
        = Thm.major_prem_of sequent
  in case X of Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _ =>
                  Phi_Reasoner.single_RS' rule1 (ctxt,sequent)
             | _ (*times*) $ (_ (*FOCUS*) $ _) =>
                  Phi_Reasoner.single_RS' rule2 (ctxt,sequent)
  end

fun has_subjs ctxt sequent =
  let
  val (_,prems, concl) = Phi_Help.strip_meta_hhf (Phi_Help.leading_antecedent' sequent)
  val (_ (*@action*) $ _ $ (_ $ _ $ G) (*reason_ToSA mode G*)) = concl
  in prems
  |> exists (fn (Const (\<^const_name>\<open>Action_Tag\<close>, _) $ _
                    $ (Const (\<^const_name>\<open>subj_premise\<close>, _) $ G'))
                  => Subgoal_Env.is_sub ctxt (G',G)
              | _ => false)
  end

fun collect_subjs ctxt sequent =
  let
  val (_,prems, concl) = Phi_Help.strip_meta_hhf (Phi_Help.leading_antecedent' sequent)
  val (_ (*@action*) $ _ $ (_ $ _ $ G) (*reason_ToSA mode G*)) = concl
  in prems
  |> map_filter (fn (Const (\<^const_name>\<open>Action_Tag\<close>, _) $ (\<^const>\<open>Trueprop\<close> $ P)
                        $ (Const (\<^const_name>\<open>subj_premise\<close>, _) $ G'))
                      => if Subgoal_Env.is_sub ctxt (G',G)
                         then SOME P
                         else NONE
                  | _ => NONE)
  end

fun is_Var_and_bs (Var _) = true
      | is_Var_and_bs (X $ Bound _) = is_Var_and_bs X
      | is_Var_and_bs (X $ Free _) = is_Var_and_bs X
      | is_Var_and_bs _ = false

fun ToSA_existential_unification' rule1 rule2 rule3 (ctxt,sequent) =
  let
    (*for performance, we do not check the constants*)
    val _ (*@action*) $ ( _ (*Trueprop*) $ ( _ (*VS*) $ H $ X $ _ )) $ _
        = Thm.major_prem_of sequent
    val H2 = case X of Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ H2 => H2
                     | _ (*times*) $ (_ (*FOCUS*) $ H2) => H2
  in if is_Var_and_bs H2
     then Seq.make (fn _ =>
          let
          val subjs = collect_subjs ctxt sequent

          val (vars,_,_) = Phi_Help.strip_meta_hhf (Phi_Help.leading_antecedent' sequent)
          val N = length vars
          val bs2 = snd (strip_comb H2)
                      |> map_filter (fn Bound i => SOME i | _ => NONE)
          val bads = subtract (op =) bs2 (loose_bnos H)
                |> map (fn i => (i, List.nth (vars, N - 1 - i) |> snd))
          val idx = Thm.maxidx_of sequent

          fun subst_bvar k (Bound i) = (case find_index (fn (b,_) => b = i-k) bads
                                          of ~1 => Var (("x", idx + i - k),
                                                        List.nth (vars, N - 1 - (i - k)) |> snd)
                                           | j  => Bound (k + j))
            | subst_bvar k (f$t) = subst_bvar k f $ subst_bvar k t
            | subst_bvar k (Abs(N,T,X)) = Abs (N,T,subst_bvar (k+1) X)
            | subst_bvar _ X = X
          val H' = H
              |> fold_rev (fn subj => fn X => @{const Subjection(\<open>FIC_N \<Rightarrow> FIC\<close>)} $ X $ subj) subjs
              |> not (null bads) ? subst_bvar 0
                  (*TODO: the order of the existential quantifiers is not preserved*)
              |> fold (fn (_,T) => fn X => \<^Const>\<open>ExSet T \<^typ>\<open>FIC_N \<Rightarrow> FIC\<close>\<close> $ Abs ("", T, X)) bads
              |> Thm.cterm_of ctxt

          val rule = Drule.infer_instantiate ctxt [(("H'",0), H')] rule3
          val sequent' = (rule RS sequent)
              |> funpow (length bads) (fn th => @{thm ExSet_imp_I} RS th)
              |> funpow (length subjs) (fn th =>
                      (@{thm Action_Tag_D} RS (@{thm Subjection_imp_I} RS th))
                        |> Thm.assumption (SOME ctxt) 1
                        |> Seq.hd)
              |> (fn th => @{thm implies_refl} RS th)
          in ToSA_unification rule1 rule2 (ctxt, sequent')
          |> Option.map (rpair Seq.empty)
          end)
     else Seq.empty
  end

fun tail_is_var (Const (\<^const_name>\<open>times\<close>, _) $ X $ _) = tail_is_var X
  | tail_is_var (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = tail_is_var X
  | tail_is_var (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (_,_,X)) = tail_is_var X
  | tail_is_var X = is_Var_and_bs X

in
fun ToSA_existential_unification rule1 rule2 rule3 rule4 (s as (ctxt,sequent)) =
  let
  val _ (*@action*) $ ( _ (*Trueprop*) $ ( _ (*VS*) $ _ $ X $ _ )) $ _
        = Thm.major_prem_of sequent
  val H2 = case X of Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ H2 => H2
                     | _ (*times*) $ (_ (*FOCUS*) $ H2) => H2
  in Seq.make (fn _ =>
      case ToSA_unification rule1 rule2 s
        of SOME s' =>
            (*for performance, the check is put later than the unification*)
            if has_subjs ctxt sequent (*it is the initial sequent!*)
               andalso tail_is_var H2
            then REPEAT_DETERM (HEADGOAL (Tactic.resolve_tac ctxt [rule4])
                             #> Phi_Reasoner.chop_seq_head) sequent
                  |> Seq.maps (ToSA_existential_unification' rule1 rule2 rule3 o pair ctxt)
                  |> Seq.pull
            else SOME (s', Seq.empty)
        | NONE =>
            if is_Var_and_bs H2
            then Seq.pull (ToSA_existential_unification' rule1 rule2 rule3 s)
            else NONE)
  end
end
\<close>


\<phi>reasoner_ML ToSA_finish 4000 (\<open>?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?H2 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close> |
                              \<open>?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R * \<blangle> ?H2 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>)
  = \<open>ToSA_existential_unification @{thm ToSA_finish} @{thm ToSA_finish'}
                                  @{thm ToSA_finish''} @{thm ToSA_finish'''}\<close>

hide_fact ToSA_finish ToSA_finish' ToSA_finish'' ToSA_finish'''

subsubsection \<open>Void Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 3200 ]:
  " H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G \<Longrightarrow>
    H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> X * 1 \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  " R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G \<Longrightarrow>
    R * 1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_right .

subsubsection \<open>Pad Void Holes at left\<close> \<comment> \<open>to standardize\<close>

lemma [\<phi>reason 2500
 except \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> (?X1 * ?X2) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
        \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?X1 + ?X2 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
        \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> 1 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
        \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> TAIL ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
]:
  " H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> 1 * X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G \<Longrightarrow>
    H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left .

lemma [\<phi>reason 2500
   except \<open> ?Y1 * ?Y2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
          \<open> ?Y1 + ?Y2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
          \<open> 1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
          \<open> TAIL ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
]:
  " 1 * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G \<Longrightarrow>
    Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left .

lemma [\<phi>reason 1050 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?Y \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA True ?G\<close>
   except \<open>(?X'::?'a::sep_magma_1 set) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?Y' \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA True ?G\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA True G\<close>
  \<comment> \<open>If it doesn't have one, it cannot be reasoned by this procedure, so
      a fallback here handles it.\<close>
  unfolding FOCUS_TAG_def Action_Tag_def .


subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 3200]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> U \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
    T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3200]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * U \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
    T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3200]:
  "(Q @action subj_premise G \<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G) \<Longrightarrow>
    T \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding Imply_def by (simp add: \<phi>expns) blast


subsubsection \<open>Existential\<close>

lemma [\<phi>reason 2700]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> U c \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G \<Longrightarrow>
    T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ExSet U \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding Imply_def by (simp add: \<phi>expns, metis)

lemma [\<phi>reason 2700]:
  "(\<And>x.  T x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G) \<Longrightarrow>
    ExSet T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding Imply_def by (simp add: \<phi>expns) fastforce

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> VAL x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3150 for \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R\<heavy_comma> ?var_X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R \<brangle> @action reason_ToSA mode G
\<Longrightarrow> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R\<heavy_comma> 0 \<brangle> @action reason_ToSA mode G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3140 for \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R\<heavy_comma> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R \<brangle> @action reason_ToSA mode G
\<Longrightarrow> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R\<heavy_comma> X \<brangle> @action reason_ToSA mode G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3130 for \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?var_X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> 0 \<brangle> @action reason_ToSA mode G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3100 for \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action reason_ToSA mode G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3100 for \<open> ?R * 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> R * 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action reason_ToSA mode G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3100 for \<open> 0 * ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> 0 * R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action reason_ToSA mode G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3100]:
  \<open>  Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow>  Y + 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding Imply_def by simp

lemma [\<phi>reason 3100]:
  \<open>  Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow>  0 + Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding Imply_def by simp

subsubsection \<open>Divergence of Disjunction\<close>

(*
paragraph \<open>Divide Schematic Variable\<close>

definition \<open>ALSTR_Divide_Assertion_U_Imp X A B \<equiv> Trueprop ( A + B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X)\<close>

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?var_Z::assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U_Imp (A + B) A B\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (simp add: implies_refl) 

lemma [\<phi>reason for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?Z::assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U_Imp A A A\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (simp add: implies_refl)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?ZR * ?Z1) ?A ?B\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp Z1 A1 B1
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp ZR AR BR
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp (ZR * Z1) (AR * A1) (BR * B1)\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (smt (verit, del_insts) Imply_def plus_set_in_iff set_mult_expn)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp 0 ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U_Imp 0 0 0\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (simp add: zero_implies_any)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp (ExSet ?Z) ?A ?B\<close>]:
  \<open>(\<And>c. PROP ALSTR_Divide_Assertion_U_Imp (Z c) (A c) (B c))
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp (ExSet Z) (ExSet A) (ExSet B)\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def Imply_def plus_set_def
  apply (clarsimp simp add: \<phi>expns)
  by (smt (z3) Fic_Space_Un) 

lemma [\<phi>reason 1200
    for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P) ?A ?B\<close>
]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp (Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (B \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def plus_set_def Imply_def
  by (simp add: \<phi>expns) 

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp \<blangle> ?Z \<brangle> ?A ?B\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp \<blangle> Z \<brangle>  \<blangle> A \<brangle>  \<blangle> B \<brangle>\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def plus_set_def by (simp add: \<phi>expns)


paragraph \<open>Main Rules\<close> *)

lemma [\<phi>reason 2800 for \<open>?A + ?B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> SUBGOAL G G1
\<Longrightarrow> B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1 @action reason_ToSA mode G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P2 @action reason_ToSA mode G
\<Longrightarrow> A + B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1 \<or> P2 @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def
  by (simp add: Imply_def distrib_left)

lemma [\<phi>reason 2800 for \<open>?R * (?A + ?B) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> SUBGOAL G G1
\<Longrightarrow> R * B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1 @action reason_ToSA mode G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> R * A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P2 @action reason_ToSA mode G
\<Longrightarrow> R * (A + B) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1 \<or> P2 @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def
  apply (simp add: Imply_def distrib_left)
  by (metis plus_set_in_iff set_mult_expn)

lemma [\<phi>reason 800]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> A \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding plus_set_def apply simp
  by (metis implies_union(1) plus_set_def)

lemma [\<phi>reason 800]:
  \<open>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> B \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding plus_set_def
  by (simp add: Imply_def)

lemma [\<phi>reason 800]:
  \<open>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> A \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G1
\<Longrightarrow>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def
  apply (simp add: distrib_left)
  by (metis plus_set_in_iff set_mult_expn)

lemma [\<phi>reason 800]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> B \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G1
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def
  apply (simp add: distrib_left)
  by (metis plus_set_in_iff set_mult_expn)


subsubsection \<open>Step-by-Step Searching Procedure\<close>

lemma [\<phi>reason 2000
    for \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>
(* except \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * (FIX ?X) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close> *)
]:
  " R  \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R1 * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P1 @action reason_ToSA mode G
\<Longrightarrow> R1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 \<brangle>     \<^bold>a\<^bold>n\<^bold>d P2 @action reason_ToSA mode G
\<Longrightarrow> R  \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 * X \<brangle> \<^bold>a\<^bold>n\<^bold>d P1 \<and> P2 @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All Action_Tag_def
  by (metis set_mult_expn)

(*
lemma [\<phi>reason 2010 for \<open> ?R * ?Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * (FIX ?X) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA True ?G\<close>]:
  " Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1
\<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 \<brangle> \<^bold>a\<^bold>n\<^bold>d P2 @action reason_ToSA True G
\<Longrightarrow> R * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 * (FIX X) \<brangle> \<^bold>a\<^bold>n\<^bold>d P1 \<and> P2 @action reason_ToSA True G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis set_mult_expn)

lemma [\<phi>reason 2000 for \<open> ?R * ?Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * (FIX ?X) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  " R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> R * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 * (FIX X) \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis set_mult_expn)

lemma [\<phi>reason 2000 for \<open>?R * (FIX ?Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  " R * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> R * (FIX Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding cast_def split_paired_All Fix_def
  by (simp add: \<phi>expns)
*)

lemma [\<phi>reason 2000 for \<open> ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R2 * \<blangle> SYNTHESIS ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  " R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2 * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2 * \<blangle> SYNTHESIS X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding Synthesis_def .

lemma [\<phi>reason 2000 for \<open> ?R * (SYNTHESIS ?Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  " R * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> R * (SYNTHESIS Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All
  by (simp add: \<phi>expns)


subsubsection \<open>General Search\<close>

lemma [\<phi>reason 800 for \<open> ?R * ?V \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  " R * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> X \<brangle> @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All
  by (simp add: implies_refl)

lemma [\<phi>reason 80 for \<open> ?R * ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R''' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA True ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * X \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> R * H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * H' * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA True G"
  for H :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def Action_Tag_def
  by (metis (no_types, lifting) mult.assoc set_mult_expn)

lemma [\<phi>reason 70 for \<open> ?R * ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R''' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]: \<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
  \<Longrightarrow> R * H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' * H * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G "
  for H :: \<open>'a::sep_ab_semigroup set\<close> 
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def Action_Tag_def
  by (smt (verit, del_insts) mult.assoc mult.commute set_mult_expn)

(* lemma [\<phi>reason 1200
    on \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "CHK_SUBGOAL G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>
*)

subsubsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  " R * T1 * T2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> R * (T1 * T2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * X1 * X2 \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * (X1 * X2) \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding mult.assoc[symmetric] .



(* subsection \<open>Structural Pairs\<close> (*depreciated*)

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def . *)



section \<open>ToSA for View Shift\<close>

text \<open>This is a counterpart of the ToSA for view shifts.\<close>

(* lemma [\<phi>intro0]: "x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * y \<Ztypecolon> Y \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * y\<^sub>m \<Ztypecolon> Y \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * \<blangle> y \<Ztypecolon> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * \<blangle> y\<^sub>m \<Ztypecolon> Y \<brangle> \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Heap_Subty_Goal_def . *)
(* lemma [\<phi>intro0]: "A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B" unfolding SubtyDual_def  by (simp add: implies_refl) *)

(* lemma [\<phi>intro 1000]:
  "L * H \<longmapsto> L * H \<^bold>d\<^bold>u\<^bold>a\<^bold>l L * h\<^sub>m \<Ztypecolon> \<blangle> H\<^sub>m \<brangle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s L * h\<^sub>m \<Ztypecolon> H\<^sub>m \<brangle>"
  unfolding Heap_Subty_Goal_def using cast_dual_id . *)

subsubsection \<open>Initialization\<close>

lemma [\<phi>reason 2010
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?Y @action ToSA' ?mode\<close>
]:
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> \<blangle> Y' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action reason_ToSA mode G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y @action ToSA' mode\<close>
  unfolding Action_Tag_def Simplify_def FOCUS_TAG_def
  by (simp add: View_Shift_imply_P)

lemma [\<phi>reason 2000
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action ToSA' ?mode\<close>
]:
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> \<blangle> Y' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action ToSA' mode\<close>
  unfolding Action_Tag_def Simplify_def FOCUS_TAG_def
  by simp

lemma [\<phi>reason 2100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?var_Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action ToSA' ?mode\<close>
                        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action ToSA' ?mode\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X @action ToSA' mode\<close>
  unfolding Action_Tag_def using view_shift_id .


subsubsection \<open>Termination\<close>

lemma ToSA_VS_finish : "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> H \<brangle> @action reason_ToSA mode G"
  and ToSA_VS_finish': "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> 1 * \<blangle> H \<brangle> @action reason_ToSA mode G"
  unfolding mult_1_left FOCUS_TAG_def Action_Tag_def
  using view_shift_id by this+

lemma ToSA_VS_finish'':
  \<open> H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H' \<longmapsto> Y @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H  \<longmapsto> Y @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def
  using View_Shift_def view_shift_by_implication by force

lemma ToSA_VS_finish''':
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R1 \<longmapsto> \<blangle> R2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R1\<heavy_comma> X \<longmapsto> \<blangle> R2\<heavy_comma> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P  @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def FOCUS_TAG_def
  using \<phi>view_shift_intro_frame_R .

\<phi>reasoner_ML ToSA_VS_finish 4000 (\<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?H2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close> |
                                 \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> ?R * \<blangle> ?H2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>)
  = \<open>ToSA_existential_unification @{thm ToSA_VS_finish} @{thm ToSA_VS_finish'}
                                  @{thm ToSA_VS_finish''} @{thm ToSA_VS_finish'''}\<close>

hide_fact ToSA_VS_finish ToSA_VS_finish' ToSA_VS_finish'' ToSA_VS_finish'''


lemma [\<phi>reason 4000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> \<r>Clean H
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> Void \<brangle> @action reason_ToSA mode G\<close>
  unfolding \<r>Clean_def FOCUS_TAG_def Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 4010 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> Void \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> \<r>Clean H
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> Void \<heavy_comma> \<blangle> Void \<brangle> @action reason_ToSA mode G\<close>
  unfolding \<r>Clean_def FOCUS_TAG_def Action_Tag_def
  by (simp add: view_shift_by_implication)

lemma [\<phi>reason 4000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> ?R \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> H \<heavy_comma> \<blangle> Void \<brangle> @action reason_ToSA mode G\<close>
  unfolding FOCUS_TAG_def Action_Tag_def
  by (simp add: \<phi>view_refl)

lemma [\<phi>reason 4011 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> ?R \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h (Automatic_Morphism ?RP ?RX \<and> ?P)
        @action reason_ToSA ?mode ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> H \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Automatic_Morphism True (\<^bold>v\<^bold>i\<^bold>e\<^bold>w H'\<heavy_comma> \<blangle> Void \<brangle> \<longmapsto> H' ) \<and> True
     @action reason_ToSA mode G\<close>
  unfolding FOCUS_TAG_def Morphism_def Action_Tag_def
  by (simp add: \<phi>view_refl)



subsubsection \<open>Void Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 3200 ]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<heavy_comma> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> Void \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding mult_1_right .

subsubsection \<open>Pad Void Holes\<close> \<comment> \<open>to standardize\<close>

lemma [\<phi>reason 2500
 except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> (?X1 \<heavy_comma> ?X2) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?X1 + ?X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> TAIL ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> 1 \<heavy_comma> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding mult_1_left .

lemma [\<phi>reason 2500
   except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?Y1 \<heavy_comma> ?Y2 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?Y1 + ?Y2 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 1 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w TAIL ?H \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w 1 \<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding mult_1_left .

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 3200]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3200]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2900]:
  "(Q @action subj_premise G \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns) blast


subsubsection \<open>Existential\<close>

lemma [\<phi>reason 2700]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U c \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> ExSet U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns, metis)

lemma [\<phi>reason 2700]:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w T x \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w ExSet T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding View_Shift_def Action_Tag_def
  by (simp add: \<phi>expns) fastforce

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> VAL x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3150 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> ?R\<heavy_comma> ?var_X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> R \<brangle> @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> R\<heavy_comma> 0 \<brangle> @action reason_ToSA mode G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3140 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> ?R\<heavy_comma> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> R \<brangle> @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> R\<heavy_comma> X \<brangle> @action reason_ToSA mode G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3130 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> ?var_X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> 0 \<brangle> @action reason_ToSA mode G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> X @action reason_ToSA mode G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> 0 \<longmapsto> X @action reason_ToSA mode G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0\<heavy_comma> ?R \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0\<heavy_comma> R \<longmapsto> X @action reason_ToSA mode G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3100]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y + 0 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding View_Shift_def Action_Tag_def by simp

lemma [\<phi>reason 3100]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 + Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding View_Shift_def by simp

subsubsection \<open>Divergence of Union\<close>

(* paragraph \<open>Divide Schematic Variable\<close>

definition \<open>ALSTR_Divide_Assertion_U X A B \<equiv> Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w A + B \<longmapsto> X)\<close>

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (?var_Z::assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U (A + B) A B\<close>
  for A :: \<open>assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_id) 

lemma [\<phi>reason for \<open>PROP ALSTR_Divide_Assertion_U (?Z::assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U A A A\<close>
  for A :: \<open>assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_id)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (?ZR \<heavy_comma> ?Z1) ?A ?B\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U Z1 A1 B1
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U ZR AR BR
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (ZR \<heavy_comma> Z1) (AR \<heavy_comma> A1) (BR \<heavy_comma> B1)\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (smt (z3) INTERP_SPEC_plus View_Shift_def distrib_left mult.commute mult.left_commute plus_set_in_iff)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (0::assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U 0 0 (0::assn)\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_0)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (ExSet ?Z::assn) ?A ?B\<close>]:
  \<open>(\<And>c. PROP ALSTR_Divide_Assertion_U (Z c) (A c) (B c))
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (ExSet Z) (ExSet A) (ExSet B)\<close>
  for A :: \<open>'c \<Rightarrow> assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def Imply_def plus_set_def View_Shift_def
  apply (clarsimp simp add: \<phi>expns)
  by (smt (z3) Fic_Space_Un) 

lemma [\<phi>reason 1200
    for \<open>PROP ALSTR_Divide_Assertion_U (?Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P :: assn) ?A ?B\<close>
]:
  \<open> PROP ALSTR_Divide_Assertion_U Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (B \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  for A :: \<open>assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def plus_set_def View_Shift_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U \<blangle> ?Z \<brangle> ?A (?B::assn)\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U \<blangle> Z \<brangle>  \<blangle> A \<brangle>  \<blangle> B \<brangle>\<close>
  for A :: \<open>assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def plus_set_def by (simp add: \<phi>expns)

paragraph \<open>Main Rules\<close> *)

lemma [\<phi>reason 2800 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A + ?B \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> SUBGOAL G G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 @action reason_ToSA mode G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A + B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<or> P2 @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def
  using \<phi>CASE_VS .

lemma [\<phi>reason 2800 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> (?A + ?B) \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> SUBGOAL G G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 @action reason_ToSA mode G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> A \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> A + B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<or> P2 @action reason_ToSA mode G\<close>
  unfolding distrib_left Action_Tag_def
  using \<phi>CASE_VS .

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding plus_set_def Action_Tag_def apply simp
  by (metis plus_set_def view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding plus_set_def Action_Tag_def apply simp
  by (metis plus_set_def sup_commute view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def FOCUS_TAG_def
  by (simp add: distrib_left view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding Action_Tag_def FOCUS_TAG_def
  by (simp add: distrib_left view_shift_union(2)) 

subsubsection \<open>Step-by-Step Searching Procedure\<close>

lemma [\<phi>reason 2000
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> \<blangle> ?R2 \<heavy_comma> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
(*  except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> \<blangle> ?R2 \<heavy_comma> FIX ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close> *)
]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R  \<longmapsto> R1 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R1 \<longmapsto> \<blangle> R2 \<brangle>     \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R  \<longmapsto> \<blangle> R2 \<heavy_comma> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<and> P1 @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def split_paired_All
  by (metis View_Shift_imply_P \<phi>frame_view_right \<phi>view_trans)

(*
lemma [\<phi>reason 2010 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?Y \<longmapsto> \<blangle> ?R2 \<heavy_comma> (FIX ?X) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA True ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> \<blangle> R2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 @action reason_ToSA True G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> \<blangle> R2 \<heavy_comma> FIX X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<and> P1 @action reason_ToSA True G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis \<phi>view_shift_intro_frame_R \<phi>view_shift_trans mult.commute)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?Y \<longmapsto> \<blangle> ?R2 \<heavy_comma> (FIX ?X) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> \<blangle> R2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> X \<longmapsto> \<blangle> R2 \<heavy_comma> FIX X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis \<phi>frame_view mult.commute)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> FIX ?Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> FIX Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding cast_def split_paired_All Fix_def
  by (simp add: \<phi>expns)
*)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> ?R2 \<heavy_comma> \<blangle> SYNTHESIS ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> SYNTHESIS X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding Synthesis_def .

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> SYNTHESIS ?Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> SYNTHESIS Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def split_paired_All
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> ?R2\<heavy_comma> \<blangle> SMORPH ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Automatic_Morphism RP RX \<and> P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> SMORPH X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Automatic_Morphism RP RX \<and> P @action reason_ToSA mode G\<close>
  unfolding SMorphism_def .


subsubsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1215 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?U \<longmapsto> ?R'' \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v'] ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA True ?G\<close>]:
  " y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] U \<longmapsto> R \<heavy_comma> \<blangle> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA True G"
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All View_Shift_def
  by (simp add: \<phi>expns times_list_def) metis

lemma [\<phi>reason 1210 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?U \<longmapsto> ?R'' \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v'] ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<longmapsto> R \<heavy_comma> \<blangle> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<brangle> @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All View_Shift_def Action_Tag_def
  by blast
  

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?X \<longmapsto> ?R'''\<heavy_comma> \<blangle> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R'\<heavy_comma> \<blangle> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> X \<longmapsto> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All Action_Tag_def
  by (smt (verit) \<phi>view_shift_intro_frame_R mult.assoc mult.commute)

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?V \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
  except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?V \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>
]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] V \<longmapsto> R' \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] V \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding FOCUS_TAG_def Action_Tag_def
  by (smt (verit, best) \<phi>view_shift_intro_frame_R mult.assoc mult.commute)

lemma ToSA_skip
  [\<phi>reason 70 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]: \<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> H \<longmapsto> R' \<heavy_comma> H \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G "
  unfolding FOCUS_TAG_def
  by (simp add: \<phi>view_shift_intro_frame mult.commute mult.left_commute)


subsubsection \<open>General Search\<close>

lemma [\<phi>reason 800 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?V \<longmapsto> ?R' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> X \<longmapsto> R \<heavy_comma> \<blangle> X \<brangle> @action reason_ToSA mode G"
      \<comment> \<open>successful termination of the step-by-step search\<close>
  unfolding Action_Tag_def FOCUS_TAG_def split_paired_All
  by (simp add: view_shift_id)

(* 
We don't need other general searches any more, because every resource locale configures its reasoning rules.


lemma [\<phi>reason 100 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> H'\<heavy_comma> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> H \<longmapsto> R\<heavy_comma> H'\<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def
  by (simp add: \<phi>view_shift_intro_frame mult.assoc)

lemma [\<phi>reason 10 on \<open>?a \<Zinj> ?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R''' \<heavy_comma> ?a' \<Zinj> ?x' \<Ztypecolon> ?T' \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
   a \<Zinj> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s a' \<Zinj> x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow>
   a \<Zinj> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> a' \<Zinj> x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding cast_def split_paired_All by (simp add: \<phi>expns)

*)

(* lemma [\<phi>reason 1200
    on \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "CHK_SUBGOAL G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>
*)


subsubsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> T1 \<heavy_comma> T2 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> (T1 \<heavy_comma> T2) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P  @action reason_ToSA mode G"
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> X1 \<heavy_comma> X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> (X1 \<heavy_comma> X2) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G"
  unfolding mult.assoc[symmetric] .



(*
subsubsection \<open>Other Reasoning Settings\<close>

lemma [\<phi>intro 14000]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a \<Zinj> x' " unfolding Premise_def by simp
(* lemma [\<phi>intro 13500]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a' \<Zinj> x' " unfolding Premise_def by simp *)

(*TODO: this rule is too aggressive. Maybe a assumption based flag switch?*)
lemma [\<phi>intro 13000]: "False \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a' \<Zinj> x' " unfolding Premise_def by simp
  \<comment> \<open>For any other situation (when a is not alpha equivalent to a'), reasoning is pruned early.
  The proof for \<^term>\<open>a = a'\<close> is always assigned to users, because maintaining the consistency of object identities
    is so essential that users should always keep.\<close>
*)




section \<open>Convergence of Branches\<close>

text \<open>The procedure transforms \<^term>\<open>(If P A B)\<close> into the canonical \<phi>-BI form \<^term>\<open>C\<close>.

  The strongest post-condition of a branch statement results in \<^term>\<open>If P A B\<close> typically.
  It is strongest but not good because it violates the canonical \<phi>-BI form.
  Thus an automation procedure here is presented to transform it.
  Typically it unifies refinement relations in two branches but leaves abstract objects
  in an if expression.

  The transformation is as strong as possible to minimize the loose of information.
  It is clear if two branches are in the same refinement, no information will be lost.
  If not, and any necessary information is lost in this process, user can always manually transform
  the assertion before the end of each branch, to unify the refinement of two branches.
\<close>

text \<open>This merging procedure retains the order of the left side.\<close>

typedecl branch_convergence
instance branch_convergence :: whole_target ..
consts branch_convergence :: \<open>branch_convergence action\<close>

(* text \<open>Though definitionally If is identical to If, there is semantic difference between them.
  If has a systematical meaning. If P A B means the procedure merging two assertions
  A and B, whereas If P A B means to merge two abstract objects or two refinement relations.
  A key difference in the procedure is, there is fallback for If P A B. If there is no further
  rule telling how to do with If P A B, then the result of the procedure on this is just
  If P A B itself --- it is usual that a branch statement returning 1 or 2 is specified by
  \<^term>\<open>(if P then 1 else 2) \<Ztypecolon> \<phi>Nat\<close>. In contrast, there is no fallback for If P A B, because
  a failure of If P A B means the failure of merging those two assertions A and B, which is
  the failure of the whole merging procedure.\<close> *)

subsubsection \<open>Identity\<close>

lemma [\<phi>reason 3000 for \<open>If ?P ?A ?A'' = ?X @action branch_convergence\<close>]:
  "If P A A = A @action branch_convergence"
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?A ?A'' \<longmapsto> ?X @action branch_convergence\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w If P A A \<longmapsto> A @action branch_convergence"
  unfolding Action_Tag_def by (simp add: view_shift_id)

lemma [\<phi>reason 3000 for \<open>If ?P ?A ?A'' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  "If P A A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A @action branch_convergence"
  unfolding Action_Tag_def Imply_def by simp

subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?A 0 \<longmapsto> ?X @action branch_convergence\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w If P A 0 \<longmapsto> (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by simp

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P 0 ?A \<longmapsto> ?X @action branch_convergence\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w If P 0 A \<longmapsto> (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> P) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by simp

lemma [\<phi>reason 3000 for \<open>If ?P ?A 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  "If P A 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (simp add: \<phi>expns zero_set_def)

lemma [\<phi>reason 3000 for \<open>If ?P 0 ?A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  "If P 0 A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> P) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (simp add: \<phi>expns zero_set_def)


subsubsection \<open>Fallback\<close>

lemma [\<phi>reason 10 for \<open>If ?P ?A ?B = ?X @action branch_convergence\<close>]:
  "If P A B = If P A B @action branch_convergence"
  unfolding Action_Tag_def ..

text \<open>There is no fallback for \<^const>\<open>If\<close>. The If is not allowed to be fallback.
  If the convergence for If fails, the reasoning fails.\<close>

(*
subsubsection \<open>Ad-hoc rules\<close>

lemma [\<phi>reason for \<open>If ?P (?a \<Zinj> ?x) (?b \<Zinj> ?y) = ?X @action branch_convergence\<close>]:
  " If P a b = aa @action branch_convergence
\<Longrightarrow> If P x y = z  @action branch_convergence
\<Longrightarrow> If P (a \<Zinj> x) (b \<Zinj> y) = (aa \<Zinj> z) @action branch_convergence"
  unfolding Action_Tag_def by force

 lemma branch_convergence_skip:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (R1 * X) (N * Y * \<blangle> R2 \<brangle>) \<longmapsto> R @action branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (R1 * X) (N * \<blangle> R2 * Y \<brangle>) \<longmapsto> R @action branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def Action_Tag_def Action_Tag_def
  by (metis mult.assoc mult.commute)

lemma branch_convergence_skip_imp:
  " If P (R1 * X) (N * Y * \<blangle> R2 \<brangle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R @action branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> If P (R1 * X) (N * \<blangle> R2 * Y \<brangle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R @action branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for R :: \<open>'a::sep_algebra set\<close>
  unfolding FOCUS_TAG_def Action_Tag_def Action_Tag_def
  by (metis mult.assoc mult.commute)
*)

(*
lemma [\<phi>reason 3000]:
  "If P A B = X
  \<Longrightarrow> If (MergeNeg (MergeNeg P)) A B = X"
  unfolding MergeNeg_def by simp

lemma [\<phi>reason 2800]:
  "If P B A = X
  \<Longrightarrow> If (MergeNeg P) A B = X"
  unfolding MergeNeg_def by force
*)

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 1400]:
  \<open> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z @action branch_convergence
\<Longrightarrow> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z @action branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1400]:
  \<open> If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z @action branch_convergence
\<Longrightarrow> If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z @action branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1400]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) R \<longmapsto> Z @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) R \<longmapsto> Z @action branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1400]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) \<longmapsto> Z @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) \<longmapsto> Z @action branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma
  [\<phi>reason 1300 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QL) (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QR) \<longmapsto> ?X @action branch_convergence\<close>]:
  " If P QL QR = Q @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j QL) (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j QR) \<longmapsto> (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def by force

lemma [\<phi>reason 1300 for \<open>If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QL) (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QR) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  " If P QL QR = Q @action branch_convergence
\<Longrightarrow> If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j QL) (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j QR) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by force

lemma [\<phi>reason 1200
    for \<open>If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>
]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longrightarrow> Q) @action branch_convergence"
  unfolding Imply_def Action_Tag_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) ?R \<longmapsto> ?X @action branch_convergence\<close>
]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) R \<longmapsto> (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longrightarrow> Q) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>If ?P ?L (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not>P \<longrightarrow> Q) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?L (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) \<longmapsto> ?X @action branch_convergence\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<longmapsto> (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not>P \<longrightarrow> Q) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns; blast)


subsubsection \<open>Existential\<close>

lemma Conv_Merge_Ex_both:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L x) (R x) \<longmapsto> X x @action branch_convergence)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (\<exists>* x. L x) (\<exists>* x. R x) \<longmapsto> (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; fastforce)

lemma Conv_Merge_Ex_both_imp:
  "(\<And>x. If P (L x) (R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X x @action branch_convergence)
\<Longrightarrow> If P (\<exists>* x. L x) (\<exists>* x. R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; blast)

lemma Conv_Merge_Ex_R
  [\<phi>reason 1100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?L (\<exists>* x. ?R x) \<longmapsto> ?X @action branch_convergence\<close>]:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R x) \<longmapsto> X x @action branch_convergence)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (\<exists>* x. R x) \<longmapsto> (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; fastforce)

lemma Conv_Merge_Ex_R_imp
  [\<phi>reason 1100 for \<open>If ?P ?L (\<exists>* x. ?R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  "(\<And>x. If P L (R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X x @action branch_convergence)
\<Longrightarrow> If P L (\<exists>* x. R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (cases P; simp add: set_eq_iff \<phi>expns; blast)

lemma [\<phi>reason 1100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (\<exists>* x. ?L x) ?R \<longmapsto> ?X @action branch_convergence\<close>]:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L x) R \<longmapsto> X x @action branch_convergence)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (\<exists>* x. L x) R \<longmapsto> (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; fastforce)

lemma [\<phi>reason 1100 for \<open>If ?P (\<exists>* x. ?L x) ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  "(\<And>x. If P (L x) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X x @action branch_convergence)
\<Longrightarrow> If P (\<exists>* x. L x) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by (cases P; simp add: set_eq_iff \<phi>expns; blast)

text \<open>The merging recognize two existential quantifier are identical if their type and variable name
  are the same. If so it uses Conv_Merge_Ex_both to merge the quantification,
  or else the right side is expanded first.\<close>

\<phi>reasoner_ML Merge_Existential 2000
  (\<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<longmapsto> ?X @action branch_convergence\<close>) =
\<open>fn (ctxt,sequent) =>
  let
    val ((Const (\<^const_name>\<open>If\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exa,tya,_))
                                        $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exb,tyb,_))), _, _)
        = Phi_Syntax.dest_view_shift (Thm.major_prem_of sequent)
    val sequent' = if exa = exb andalso tya = tyb
                   then @{thm Conv_Merge_Ex_both} RS sequent
                   else @{thm Conv_Merge_Ex_R} RS sequent
  in Seq.single (ctxt, sequent')
  end\<close>

\<phi>reasoner_ML Merge_Existential_imp 2000 (\<open>If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X\<close>) =
\<open>fn (ctxt,sequent) =>
  let
    val ((Const (\<^const_name>\<open>If\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exa,tya,_))
                                         $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exb,tyb,_))), _, _)
        = Phi_Syntax.dest_implication (Thm.major_prem_of sequent)
    val sequent' = if exa = exb andalso tya = tyb
                   then @{thm Conv_Merge_Ex_both_imp} RS sequent
                   else @{thm Conv_Merge_Ex_R_imp} RS sequent
  in Seq.single (ctxt, sequent')
  end\<close>



subsubsection \<open>Main Procedure\<close>

lemma [\<phi>reason 2000 for \<open>If ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  " If P x y = z @action branch_convergence
\<Longrightarrow> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (z \<Ztypecolon> Z) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by (cases P; simp)

lemma
  [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) \<longmapsto> ?X @action branch_convergence\<close>]:
  " If P x y = z @action branch_convergence
\<Longrightarrow> If P T U = Z @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<longmapsto> (z \<Ztypecolon> Z) @action branch_convergence"
  unfolding Action_Tag_def
  by (cases P; clarsimp simp add: \<phi>expns view_shift_id)

definition \<open>Branch_Convergence_Type_Pattern type the_type_to_match \<equiv> Trueprop True\<close>

lemma [\<phi>reason 10 for \<open>PROP Branch_Convergence_Type_Pattern ?X ?X'\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern X X\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200 for \<open>PROP Branch_Convergence_Type_Pattern (Val ?v ?T) (Val ?v ?T')\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern (Val v T) (Val v T')\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200 for \<open>If ?P (?L * (?x \<Ztypecolon> ?T)) ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X @action branch_convergence\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern T T'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' * \<blangle> y \<Ztypecolon> T' \<brangle> \<^bold>a\<^bold>n\<^bold>d Any @action reason_ToSA True G
\<Longrightarrow> If P x y = z @action branch_convergence
\<Longrightarrow> If P T T' = Z @action branch_convergence
\<Longrightarrow> If P L R' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P (L * (x \<Ztypecolon> T)) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X * (z \<Ztypecolon> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def Action_Tag_def FOCUS_TAG_def
  by (smt (z3) Imply_def implies_right_prod)

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?L * (?x \<Ztypecolon> ?T)) ?R \<longmapsto> ?X @action branch_convergence\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern T T'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' * \<blangle> y \<Ztypecolon> T' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action reason_ToSA True G
\<Longrightarrow> If P x y = z @action branch_convergence
\<Longrightarrow> If P T T' = Z @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R' \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L * (x \<Ztypecolon> T)) R \<longmapsto> X * (z \<Ztypecolon> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def Action_Tag_def FOCUS_TAG_def
  by (smt (z3) View_Shift_def mult.commute mult.left_commute)



subsubsection \<open>Convergence of Structural Nodes\<close>

lemma [\<phi>reason 1200 for \<open>If ?P (?n \<Znrres> ?T) (?n' \<Znrres> ?U) = ?Z @action branch_convergence\<close>]:
  \<open> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (n \<Znrres> T) (n \<Znrres> U) = n \<Znrres> Z @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (?T \<^emph> ?U) (?T' \<^emph> ?U') = ?Z @action branch_convergence\<close>]:
  \<open> If P T T' = T'' @action branch_convergence
\<Longrightarrow> If P U U' = U'' @action branch_convergence
\<Longrightarrow> If P (T \<^emph> U) (T' \<^emph> U') = (T'' \<^emph> U'') @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (?k \<^bold>\<rightarrow>\<^sub>@ ?T) (?k' \<^bold>\<rightarrow>\<^sub>@ ?U) = ?Z @action branch_convergence\<close>]:
  \<open> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (k \<^bold>\<rightarrow>\<^sub>@ T) (k \<^bold>\<rightarrow>\<^sub>@ U) = k \<^bold>\<rightarrow>\<^sub>@ Z @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (?k \<^bold>\<rightarrow> ?T) (?k' \<^bold>\<rightarrow> ?U) = ?Z @action branch_convergence\<close>]:
  \<open> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (k \<^bold>\<rightarrow> T) (k \<^bold>\<rightarrow> U) = k \<^bold>\<rightarrow> Z @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (Val ?v ?T) (Val ?v' ?U) = ?Z @action branch_convergence\<close>]:
  \<open>If P (Val v T) (Val v U) = Val v (If P T U) @action branch_convergence\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200 for \<open>If ?P (\<black_circle> ?T) (\<black_circle> ?U) = (\<black_circle> ?Z) @action branch_convergence\<close>]:
  \<open> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (\<black_circle> T) (\<black_circle> U) = (\<black_circle> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by fastforce

lemma [\<phi>reason 1200 for \<open>If ?P (Val ?v ?T) (Val ?v' ?U) = ?Z @action branch_convergence\<close>]:
  \<open> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (Val v T) (Val v U) = (Val v Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by fastforce


(* subsubsection \<open>Object\<close>

definition EqualAddress :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool "
  where "EqualAddress _ _ = True"

lemma [\<phi>reason]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a1 = a2
   \<Longrightarrow> EqualAddress (a1 \<Zinj> x1 \<Ztypecolon> T1) (a2 \<Zinj> x2 \<Ztypecolon> T2) "
  unfolding EqualAddress_def .. *)

subsubsection \<open>Unfold\<close>

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (N \<heavy_comma> R1 \<heavy_comma> R2) \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (N \<heavy_comma> (R1 \<heavy_comma> R2)) \<longmapsto> X @action branch_convergence"
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason 2000]:
  " If P L (N * R1 * R2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P L (N * (R1 * R2)) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence"
  for N :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason 2000]:
  " If P (L1 * L2 * L3) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P (L1 * (L2 * L3)) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L1 \<heavy_comma> L2 \<heavy_comma> L3) R \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L1 \<heavy_comma> (L2 \<heavy_comma> L3)) R \<longmapsto> X @action branch_convergence"
  unfolding Action_Tag_def by (metis mult.assoc)

subsubsection \<open>Eliminate Void Hole\<close>

lemma [\<phi>reason 2000]:
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P L (R * 1) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P L (1 * R) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L (R' * R) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P L (R' * 1 * R) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence
\<Longrightarrow> If P (L * 1) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<heavy_comma> 1) \<longmapsto> X @action branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (1 \<heavy_comma> R) \<longmapsto> X @action branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R' \<heavy_comma> R) \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R' \<heavy_comma> 1 \<heavy_comma> R) \<longmapsto> X @action branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X @action branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<heavy_comma> 1) R \<longmapsto> X @action branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)


(* subsection \<open>Program Interface\<close> \<comment> \<open>Interfaces exported to target LLVM module\<close>

definition Prog_Interface :: " label \<Rightarrow> 'a itself \<Rightarrow> 'b itself \<Rightarrow> ('a::lrep  \<longmapsto> 'b::lrep) \<Rightarrow> bool"
  where "Prog_Interface _ args rets proc \<longleftrightarrow> True"

lemma Prog_Interface_proc: "TERM proc \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) proc" 
  unfolding Prog_Interface_def ..

lemma Prog_Interface_func:
  "TERM f \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) f" 
  unfolding Prog_Interface_def ..
*)

section \<open>Automation for Sharing Permission\<close>

subsection \<open>Structure Info\<close>

definition Structure_Info :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Structure_Info T P \<longleftrightarrow> (\<forall>x. Inhabited (x \<Ztypecolon> T) \<longrightarrow> P)\<close>
  \<comment> \<open>Extract structure information inside an assertion, typically validity of permissions
      (i.e. large than zero), which is used in the automation procedure.\<close>

lemma [\<phi>reason 1200 for \<open>Structure_Info (?n \<Znrres> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (n \<Znrres> T) (0 < n \<and> P)\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (\<black_circle> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (\<black_circle> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?k \<^bold>\<rightarrow> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (k \<^bold>\<rightarrow> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (k \<^bold>\<rightarrow>\<^sub>@ T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?T \<^emph> ?U) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info U Q
\<Longrightarrow> Structure_Info (T \<^emph> U) (P \<and> Q)\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>Structure_Info (\<phi>perm_transformer ?\<psi> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (\<phi>perm_transformer \<psi> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 30 for \<open>Structure_Info ?T ?P\<close>]:
  \<open> Structure_Info T True \<close>
  unfolding Structure_Info_def by blast

subsection \<open>Cleaning\<close>

consts clean_automation_waste :: mode

lemma [\<phi>reason 1000 for \<open>?X = ?Z @action clean_automation_waste\<close>]:
  \<open>X = X @action clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200 for \<open>(() \<Ztypecolon> \<phi>None) = ?Z @action clean_automation_waste\<close>]:
  \<open>(() \<Ztypecolon> \<phi>None) = 1 @action clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?k \<^bold>\<rightarrow> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?y \<Ztypecolon> \<circle>) = (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> ?Z) @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<circle>) = (() \<Ztypecolon> k \<^bold>\<rightarrow> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?y \<Ztypecolon> \<circle>) = (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?Z) @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<circle>) = (() \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open> perm_transformer' \<psi>
\<Longrightarrow> (x \<Ztypecolon> \<phi>perm_transformer \<psi> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>perm_transformer_\<phi>None
  by simp

declare perm_transformer_pointwise[\<phi>reason 1200]
        perm_transformer_to_share[\<phi>reason 1200]

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?n \<Znrres> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> \<circle>) = (() \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>)) @action clean_automation_waste\<close>
  unfolding Action_Tag_def Premise_def \<phi>Share_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> ?T \<^emph> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'a::sep_magma_1 set) @action clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> \<circle> \<^emph> ?U) = ?Z @action clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'b::sep_magma_1 set) @action clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?r) \<Ztypecolon> (?T \<^emph> ?n \<Znrres> \<circle>)) = (?Z :: ?'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n
\<Longrightarrow> ((x,r) \<Ztypecolon> (T \<^emph> n \<Znrres> \<circle>)) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>((?r,?x) \<Ztypecolon> (?n \<Znrres> \<circle> \<^emph> ?T)) = (?Z :: ?'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n
\<Longrightarrow> ((r,x) \<Ztypecolon> (n \<Znrres> \<circle> \<^emph> T)) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)



subsection \<open>Extract\<close>

text \<open>The canonical form is where all permission annotation are on leaves.
  It minimizes fragments.\<close>

definition Structural_Extract :: \<open>'a::sep_magma set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Structural_Extract From Remain To Residual Aux \<longleftrightarrow> (Residual * From \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Remain * To \<^bold>a\<^bold>n\<^bold>d Aux)\<close>
  \<comment> \<open>Extract To from From, remaining Remain the unused part in From,
      and leaving Residual the part in To that fails to be obtained from From.\<close>

definition \<open>Structural_Extract' = Structural_Extract\<close>

lemma [\<phi>reason 1100]:
  \<open> Structural_Extract' X R Y W P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R = R' @action clean_automation_waste
\<Longrightarrow> W = W' @action clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract'_def Action_Tag_def
  by simp

lemma Structural_Extract_imply_P:
  \<open> Structural_Extract X R Y W P1
\<Longrightarrow> P1 \<longrightarrow> P2
\<Longrightarrow> Structural_Extract X R Y W P2\<close>
  unfolding Structural_Extract_def Imply_def by blast

lemma Structural_Extract'_imply_P:
  \<open> Structural_Extract' X R Y W P1
\<Longrightarrow> P1 \<longrightarrow> P2
\<Longrightarrow> Structural_Extract' X R Y W P2\<close>
  unfolding Structural_Extract_def Structural_Extract'_def Imply_def
  by blast


lemma Structural_Extract_reverse_morphism_I[intro?]:
  \<open> Structural_Extract X R Y W P
\<Longrightarrow> RP \<longrightarrow> RX
\<Longrightarrow> Structural_Extract X R Y W (Automatic_Morphism RP RX \<and> P)\<close>
  unfolding Morphism_def Structural_Extract_def Imply_def
  by blast

lemma Structural_Extract'_reverse_morphism_I[intro?]:
  \<open> Structural_Extract' X R Y W P
\<Longrightarrow> RP \<longrightarrow> RX
\<Longrightarrow> Structural_Extract' X R Y W (Automatic_Morphism RP RX \<and> P)\<close>
  unfolding Structural_Extract'_def Morphism_def Structural_Extract_def Imply_def
  by blast

lemma [\<phi>reason 1111 for \<open>Structural_Extract ?X ?R' ?Y ?W' (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract' X R Y W (Automatic_Morphism RP (Structural_Extract' rY rW rX rR rP) \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow>  R = R'  @action clean_automation_waste
\<Longrightarrow>  W = W'  @action clean_automation_waste
\<Longrightarrow> rR = rR' @action clean_automation_waste
\<Longrightarrow> rW = rW' @action clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' (Automatic_Morphism RP (Structural_Extract rY rW' rX rR' rP) \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract'_def Action_Tag_def
  by simp



paragraph \<open>Termination\<close>

lemma Structural_Extract_\<phi>None_right [\<phi>reason 3000
    for \<open>Structural_Extract ?X ?R (() \<Ztypecolon> \<phi>None) ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract X X (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .

lemma Structural_Extract_\<phi>None_left [\<phi>reason 3000
    for \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) ?R ?Y ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X X True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .


lemma Structural_Extract_1_right [\<phi>reason 3000
    for \<open>Structural_Extract ?X ?R 1 ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract X X 1 1 True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .

lemma Structural_Extract_1_left [\<phi>reason 3000
    for \<open>Structural_Extract 1 ?R ?Y ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract 1 1 X X True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .


(*TODO: BUG: need to check the case where Y requires only partial share permission but
    this rule may give it the total.*)
lemma Structural_Extract_exact [\<phi>reason 3000
    for \<open>Structural_Extract' ?X ?R ?Y ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>The current object X is exactly what we want to extract.\<close>
  \<open>Structural_Extract' X (() \<Ztypecolon> \<phi>None) X (() \<Ztypecolon> \<phi>None) True  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def Structural_Extract'_def
      mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .



lemma [\<phi>reason 3011
    for \<open>Structural_Extract ?X ?R (() \<Ztypecolon> \<phi>None) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract X X (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None)
   (Automatic_Morphism True (Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X' X' True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>None_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>None_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X X
    (Automatic_Morphism True (Structural_Extract X' X' (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>None_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>None_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract ?X ?R 1 ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract X X 1 1 (Automatic_Morphism True (Structural_Extract 1 1 X' X' True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_1_left [unfolded Action_Tag_def]
                   Structural_Extract_1_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract 1 ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract 1 1 X X (Automatic_Morphism True (Structural_Extract X' X' 1 1 True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_1_left [unfolded Action_Tag_def]
                   Structural_Extract_1_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract' ?X ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>The current object X is exactly what we want to extract.\<close>
  \<open>Structural_Extract' X  (() \<Ztypecolon> \<phi>None) X  (() \<Ztypecolon> \<phi>None)
    (Automatic_Morphism True (Structural_Extract' X' (() \<Ztypecolon> \<phi>None) X' (() \<Ztypecolon> \<phi>None) True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_exact [unfolded Action_Tag_def]
                   Structural_Extract'_reverse_morphism_I)



paragraph \<open>Fall back\<close>

lemma Structural_Extract_fallback
  [\<phi>reason 10 for \<open>Try ?S (Structural_Extract ?X ?X' ?Y ?Y' ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> Try False (Structural_Extract X X Y Y True)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_ab_semigroup set\<close>
  unfolding Structural_Extract_def Structural_Extract'_def
      \<phi>None_itself_is_one mult_1_left Action_Tag_def Try_def
  by (simp add: implies_refl mult.commute)

lemma [\<phi>reason 10 for \<open>Try ?S (Structural_Extract ?X ?X' ?Y ?Y' (Automatic_Morphism ?RP ?RX \<and> ?P)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> Try False (Structural_Extract X  X  Y  Y
      (Automatic_Morphism True (Structural_Extract X' X' Y' Y' True) \<and> True))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_ab_semigroup set\<close> and X' :: \<open>'aa::sep_ab_semigroup set\<close>
  unfolding Action_Tag_def Try_def
  by (blast intro: Structural_Extract_fallback[unfolded Action_Tag_def Try_def]
                   Structural_Extract_reverse_morphism_I)



paragraph \<open>Terminations for Specific Node\<close>

lemma Structural_Extract_\<phi>Some
  [\<phi>reason 1200 for \<open>Structural_Extract (?x \<Ztypecolon> \<black_circle> ?T) ?R (?y \<Ztypecolon> \<black_circle> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<black_circle> T) (() \<Ztypecolon> \<phi>None) (y \<Ztypecolon> \<black_circle> U) (() \<Ztypecolon> \<phi>None) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left Action_Tag_def
            Structural_Extract'_def
  using \<phi>Some_cast .

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract (?x \<Ztypecolon> \<black_circle> ?T) ?R (?y \<Ztypecolon> \<black_circle> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<black_circle> T) (() \<Ztypecolon> \<phi>None) (y \<Ztypecolon> \<black_circle> U) (() \<Ztypecolon> \<phi>None)
      (Automatic_Morphism (y' \<Ztypecolon> U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P')
            (Structural_Extract (y' \<Ztypecolon> \<black_circle> U') (() \<Ztypecolon> \<phi>None) (x' \<Ztypecolon> \<black_circle> T') (() \<Ztypecolon> \<phi>None) P')
      \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Some[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

(*TODO: According to @{thm Agreement_times}, there must be a reasoning mechanism for \<inter>\<^sub>\<phi>
  It scatters information using \<inter>\<^sub>\<phi> 

The bellowing reasoning is too weak! *)

lemma Structural_Extract_aggrement_to
  [\<phi>reason 1200 for \<open>Structural_Extract (?x \<Ztypecolon> Agreement ?T) ?R (?y \<Ztypecolon> Agreement ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left Action_Tag_def \<r>Feasible_def
            Structural_Extract'_def
  apply (cases C; simp)
  \<medium_left_bracket> premises A
  ;; dup
  ;;  Agreement_cast[OF A]
  \<medium_right_bracket>.
  using Agreement_cast .

lemma Structural_Extract_aggrement_from:
  \<open> y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>) (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left Action_Tag_def \<r>Feasible_def
            Structural_Extract'_def
  apply (cases C; simp)
  \<medium_left_bracket> premises A
    Agreement_cast[OF A]
    Agreement_shrink
  \<medium_right_bracket>.
  using Agreement_cast .


lemma [\<phi>reason 1211 for \<open>Structural_Extract (?x \<Ztypecolon> Agreement ?T) ?R (?y \<Ztypecolon> Agreement ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>)
      (Automatic_Morphism (y' \<Ztypecolon> U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P')
          (Structural_Extract (y' \<Ztypecolon> Agreement U') (() \<Ztypecolon> \<circle>) (x' \<Ztypecolon> Agreement T') (x' \<Ztypecolon> Agreement T' ?\<^sub>\<phi> C') P')
      \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_aggrement_to  [unfolded Action_Tag_def]
                   Structural_Extract_aggrement_from[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)



paragraph \<open>Normalize the Target\<close>

lemma Structural_Extract_to_mult
  [\<phi>reason 1200 for \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close> ]:
  \<open> Try S1 (Structural_Extract A B Y WY P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract B C X WX P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' A C (X * Y) (WX * WY) (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close>
  unfolding Structural_Extract_def Simplify_def Action_Tag_def Structural_Extract'_def Try_def
  \<medium_left_bracket> premises L and R
  ;;  L[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  ;;  R[THEN implies_right_prod]
  \<medium_right_bracket>. .

lemma Structural_Extract_\<phi>Prod_right
  [\<phi>reason 1200 for \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close> ]:
  \<open> Try S1 (Structural_Extract A B (y \<Ztypecolon> Y) (wy \<Ztypecolon> WY) P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G 
\<Longrightarrow> Try S2 (Structural_Extract B C (x \<Ztypecolon> X) (wx \<Ztypecolon> WX) P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' A C ((y,x) \<Ztypecolon> Y \<^emph> X) ((wy, wx) \<Ztypecolon> WY \<^emph> WX) (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
for A :: \<open>'a::sep_algebra set\<close>
  unfolding \<phi>Prod_expn'
  using Structural_Extract_to_mult .

paragraph \<open>Step by Step\<close>

lemma Structural_Extract_from_mult[\<phi>reason 1200 for
  \<open>Structural_Extract' (?L * ?X :: 'a::sep_algebra set) ?R ?W ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract X R2 Y Wr P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract L R Wr Wr2 P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' (L * X) (R * R2) Y Wr2 (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close>
  unfolding Structural_Extract_def Simplify_def Structural_Extract'_def Try_def
            Action_Tag_def
  \<medium_left_bracket> premises R and L
    fold mult.assoc
    L[THEN implies_right_prod]
    R[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  \<medium_right_bracket>. .

lemma Structural_Extract_\<phi>Prod_left [\<phi>reason 1200 for
  \<open>Structural_Extract' ((?x,?y) \<Ztypecolon> (?T::(?'a::sep_algebra,?'b) \<phi>) \<^emph> ?U) ?R (?y \<Ztypecolon> ?W) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract (x \<Ztypecolon> T) (r2 \<Ztypecolon> R2) Y W P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract (y \<Ztypecolon> U) (r \<Ztypecolon> R) W W2 P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' ((x,y) \<Ztypecolon> T \<^emph> U) ((r2,r) \<Ztypecolon> (R2 \<^emph> R)) Y W2 (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::sep_algebra,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' Simplify_def Action_Tag_def Structural_Extract'_def
            Try_def
  \<medium_left_bracket> premises R and L
    fold mult.assoc
    L[THEN implies_right_prod]
    R[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  \<medium_right_bracket>. .


lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W (Automatic_Morphism ?RR ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract A B (y \<Ztypecolon> Y) (wy \<Ztypecolon> WY)
      (Automatic_Morphism RP1 (Structural_Extract (y' \<Ztypecolon> Y') (wy' \<Ztypecolon> WY') A' B' P1') \<and> P1))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G 
\<Longrightarrow> Try S2 (Structural_Extract B C (x \<Ztypecolon> X) (wx \<Ztypecolon> WX)
      (Automatic_Morphism RP2 (Structural_Extract (x' \<Ztypecolon> X') (wx' \<Ztypecolon> WX') B' C' P2') \<and> P2))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' A C ((y,x) \<Ztypecolon> Y \<^emph> X) ((wy, wx) \<Ztypecolon> WY \<^emph> WX)
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2)
        (Structural_Extract' ((y',x') \<Ztypecolon> Y' \<^emph> X') ((wy', wx') \<Ztypecolon> WY' \<^emph> WX') A' C' (P1' \<and> P2'))
      \<and> P1 \<and> P2)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for A :: \<open>'a::sep_algebra set\<close> and A' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def Try_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Prod_right[unfolded Action_Tag_def Try_def]
                   Structural_Extract_\<phi>Prod_left [unfolded Action_Tag_def Try_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W (Automatic_Morphism ?RR ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract (x \<Ztypecolon> T) (r2 \<Ztypecolon> R2) Y W
      (Automatic_Morphism RP1 (Structural_Extract Y' W' (x' \<Ztypecolon> T') (r2' \<Ztypecolon> R2') P1') \<and> P1))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract (y \<Ztypecolon> U) (r \<Ztypecolon> R) W W2
      (Automatic_Morphism RP2 (Structural_Extract W' W2' (y' \<Ztypecolon> U') (r' \<Ztypecolon> R') P2') \<and> P2))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' ((x,y) \<Ztypecolon> T \<^emph> U) ((r2,r) \<Ztypecolon> (R2 \<^emph> R)) Y W2
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2) (Structural_Extract' Y' W2' ((x',y') \<Ztypecolon> T' \<^emph> U') ((r2',r') \<Ztypecolon> (R2' \<^emph> R')) (P1' \<and> P2')) \<and> P1 \<and> P2)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for Y :: \<open>'a::sep_algebra set\<close> and Y' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def Action_Tag_def Try_def
  by (blast intro: Structural_Extract_\<phi>Prod_right[unfolded Action_Tag_def Try_def]
                   Structural_Extract_\<phi>Prod_left [unfolded Action_Tag_def Try_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract A B Y WY
      (Automatic_Morphism RP1 (Structural_Extract Y' WY' A' B' P1') \<and> P1))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract B C X WX
      (Automatic_Morphism RP2 (Structural_Extract X' WX' B' C' P2') \<and> P2))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' A C (X * Y) (WX * WY)
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2) (Structural_Extract' (X' * Y') (WX' * WY') A' C' (P1' \<and> P2')) \<and> P1 \<and> P2)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close> and X' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def Action_Tag_def Try_def
  by (blast intro: Structural_Extract_to_mult  [unfolded Action_Tag_def Try_def]
                   Structural_Extract_from_mult[unfolded Action_Tag_def Try_def]
                   Structural_Extract'_imply_P)

(*TODO
lemma Structural_Extract_from_mult[\<phi>reason 1200 for
  \<open>Structural_Extract' (?L * ?X :: 'a::sep_algebra set) ?R ?W ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract X R2 Y Wr P1  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract L R Wr Wr2 P2  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (L * X) (R * R2) Y Wr2 (P1 \<and> P2)
    \<and> Automatic_Morphism
    (RP1 &&& RP2)
    (Structural_Extract' (X' * Y') (WX' * WY') A' C' (P1' \<and> P2'))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close>
*)


paragraph \<open>Structural Node\<close>

lemma Structural_Extract_\<phi>MapAt [\<phi>reason 1200 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> (?T::(?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow> ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (yr \<Ztypecolon> k \<^bold>\<rightarrow> Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  apply (simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_\<phi>Prod[symmetric])
  apply (rule \<phi>MapAt_cast) .


lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> (?T::(?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow> ?U) ?R'
    (Automatic_Morphism ?RR ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (w \<Ztypecolon> k \<^bold>\<rightarrow> W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U') (w' \<Ztypecolon> k \<^bold>\<rightarrow> W') (x' \<Ztypecolon> k \<^bold>\<rightarrow> T') (r' \<Ztypecolon> k \<^bold>\<rightarrow> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>MapAt[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)


lemma Structural_Extract_\<phi>MapAt_L [\<phi>reason 1200 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (yr \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  apply (simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric])
  thm \<phi>MapAt_L_\<phi>Prod[symmetric]
  apply (rule \<phi>MapAt_L_cast) .

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R'
      (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (yr' \<Ztypecolon> Ur') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (yr \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Ur)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (yr' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ Ur') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)




lemma Structural_Extract_\<phi>MapAt_L_pad_left [\<phi>reason 1180 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k < length k'
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k @ kd = k'
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  subgoal premises prems
    apply (insert prems(5),
       simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric]
          \<phi>MapAt_L_\<phi>MapAt_L[symmetric, of k kd, unfolded prems(3)])
    apply (rule \<phi>MapAt_L_cast) . .



lemma Structural_Extract_\<phi>MapAt_L_pad_right [\<phi>reason 1150 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k' < length k
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' @ kd = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  subgoal premises prems
    apply (insert prems(5),
       simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric]
          \<phi>MapAt_L_\<phi>MapAt_L[symmetric, of k' kd, unfolded prems(3)])
  apply (rule \<phi>MapAt_L_cast) . .


lemma [\<phi>reason 1183 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R'
      (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k < length k'
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k @ kd = k'
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1153 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R'
    (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k' < length k
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' @ kd = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)




lemma Structural_Extract_\<phi>Map_L_norm_right [\<phi>reason 1200]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Premise_def \<phi>MapAt_L_At Structural_Extract'_def .

lemma Structural_Extract_\<phi>Map_L_norm_left [\<phi>reason 1200]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Premise_def \<phi>MapAt_L_At Structural_Extract'_def .


lemma [\<phi>reason 1211 for \<open>
  Structural_Extract (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow> ?U) ?W
      (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G
\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Map_L_norm_right[unfolded Action_Tag_def]
                   Structural_Extract_\<phi>Map_L_norm_left [unfolded Action_Tag_def]
                   Structural_Extract_imply_P)

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> ?T) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Map_L_norm_right[unfolded Action_Tag_def]
                   Structural_Extract_\<phi>Map_L_norm_left [unfolded Action_Tag_def]
                   Structural_Extract_imply_P)



lemma Structural_Extract_\<phi>perm_transformer [\<phi>reason 1200
    for \<open>Structural_Extract' (?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?T) ?R (?y \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> \<phi>perm_transformer \<psi> T)
                        (r \<Ztypecolon> \<phi>perm_transformer \<psi> R)
                        (y \<Ztypecolon> \<phi>perm_transformer \<psi> U)
                        (w \<Ztypecolon> \<phi>perm_transformer \<psi> W)
                        P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Imply_def \<phi>Sep_Disj_def Structural_Extract'_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis (no_types, opaque_lifting) homo_sep_disj_semi_def homo_sep_mult.homo_mult perm_transformer'_def)

lemma [\<phi>reason 1211
    for \<open>Structural_Extract' (?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?T) ?R (?y \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?U) ?W
          (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> \<phi>perm_transformer \<psi> T)
                        (r \<Ztypecolon> \<phi>perm_transformer \<psi> R)
                        (y \<Ztypecolon> \<phi>perm_transformer \<psi> U)
                        (w \<Ztypecolon> \<phi>perm_transformer \<psi> W)
       (Automatic_Morphism (RP \<and>\<^sub>\<r> \<phi>Sep_Disj R' U')
   (Structural_Extract' (y' \<Ztypecolon> \<phi>perm_transformer \<psi> U')
                        (w' \<Ztypecolon> \<phi>perm_transformer \<psi> W')
                        (x' \<Ztypecolon> \<phi>perm_transformer \<psi> T')
                        (r' \<Ztypecolon> \<phi>perm_transformer \<psi> R')
                        P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Morphism_def Action_Tag_def Compact_Antecedent_def
  by (blast intro: Structural_Extract_\<phi>perm_transformer[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)



lemma Structural_Extract_\<phi>Optional_left
  [\<phi>reason 1200 for \<open>Structural_Extract (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C) ?R ?Y ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T ?\<^sub>\<phi> True) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  unfolding Structural_Extract'_def
  by simp

lemma Structural_Extract_\<phi>Optional_right:
  \<open> Structural_Extract Y W (x \<Ztypecolon> T) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract Y W (x \<Ztypecolon> T ?\<^sub>\<phi> True) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  unfolding Structural_Extract'_def
  by simp

lemma [\<phi>reason 1211 for \<open>Structural_Extract (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C) ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T ?\<^sub>\<phi> True) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> T' ?\<^sub>\<phi> True) R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Optional_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>Optional_right[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)



paragraph \<open>Permission Node\<close>

text \<open>Then, according to the expected permission n and the permission m that we current have,
  there are 4 rules for 4 cases:
  \<^item> m is a schematic variable. let m to be n / 2. it means we only give a half what we have,
      and preserve another half for potential future demand.
  \<^item> m = n
  \<^item> m < n
  \<^item> m > n\<close>
(*
TODO: re-enable this! *)

lemma Structural_Extract_share_half
  [\<phi>reason 1300 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> half ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
    \<comment> \<open>if only requires a half of the permission, give it a half of that currently we have.\<close>
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half(m / 2) \<Znrres> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def Structural_Extract'_def half_def Action_Tag_def
  \<medium_left_bracket> premises [\<phi>reason] and X
    share_split_\<phi>app[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod]
    fold mult.assoc
    X[THEN implies_right_prod]
   \<medium_right_bracket>. .

lemma Structural_Extract_share_half_rev:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract'_def Structural_Extract_def Action_Tag_def \<phi>Prod_expn'
  \<medium_left_bracket> premises [\<phi>reason] and X
  have t1: \<open>(r \<Ztypecolon> R) * (x \<Ztypecolon> m / 2 \<Znrres> T) * (y \<Ztypecolon> m / 2 \<Znrres> U) = (r \<Ztypecolon> R) * (y \<Ztypecolon> m / 2 \<Znrres> U) * (x \<Ztypecolon> m / 2 \<Znrres> T)\<close>
    by (metis (mono_tags, lifting) mult.assoc mult.commute)
  ;; unfold t1
     X[THEN implies_right_prod]
     share_merge_\<phi>app[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod, folded mult.assoc]
  \<medium_right_bracket>. .


lemma
  [\<phi>reason 1311 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> half ?m \<Znrres> ?U) ?R2
      (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W)
    (Automatic_Morphism RP
        (Structural_Extract (y' \<Ztypecolon> m / 2 \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m / 2 \<Znrres> T') (r' \<Ztypecolon> R') P')
    \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half (m / 2) \<Znrres> U) (w \<Ztypecolon> W)
    (Automatic_Morphism (RP \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical T')
        (Structural_Extract' (y' \<Ztypecolon> half (m / 2) \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m \<Znrres> T') ((x',r') \<Ztypecolon> m / 2 \<Znrres> T' \<^emph> R') P')
    \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Action_Tag_def Compact_Antecedent_def half_def
  by (blast intro: Structural_Extract_share_half    [unfolded Action_Tag_def half_def]
                   Structural_Extract_share_half_rev[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)



lemma Structural_Extract_share_eq
  [\<phi>reason 1200 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires exactly what we have now, typically this happens after the previous rule or n = 1.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m m = n
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn'[symmetric] Premise_def Structural_Extract'_def
  apply (simp add: \<phi>Share_\<phi>Prod[symmetric])
  using \<phi>Share_cast .

lemma [\<phi>reason 1211 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m m = n
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> m \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_share_eq[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)



lemma Structural_Extract_share_ge
  [\<phi>reason 1180 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n \<and> n < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def Structural_Extract'_def \<phi>Prod_expn' Action_Tag_def
  \<medium_left_bracket> premises _ and LE[unfolded Premise_def, useful] and [\<phi>reason] and _ and X
    share_split_\<phi>app[where n=\<open>n\<close> and m=\<open>m-n\<close>, simplified]
    fold mult.assoc
    X[folded \<phi>Prod_expn', THEN \<phi>Share_cast, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
        THEN implies_right_prod]
  have t1: \<open>(r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U) * (x \<Ztypecolon> m - n \<Znrres> T) = (x \<Ztypecolon> m - n \<Znrres> T) * (r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    using mult.assoc mult.commute by blast
  ;; unfold t1
  \<medium_right_bracket>. .

lemma Structural_Extract_share_le
  [\<phi>reason 1170 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires more than what we have, give all what we can give.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < m \<and> m < n
\<Longrightarrow> \<phi>Sep_Disj_Identical U
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' Structural_Extract'_def Action_Tag_def
  \<medium_left_bracket> premises _ and LE[unfolded Premise_def, useful] and SDI[\<phi>reason] and _ and X
    X[folded \<phi>Prod_expn', THEN \<phi>Share_cast, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
        THEN implies_left_prod, folded mult.assoc]
  
  have \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (y \<Ztypecolon> m \<Znrres> U) = (y \<Ztypecolon> n \<Znrres> U)\<close>
    using \<phi>Share_share[where n=\<open>n-m\<close> and m=m, simplified] \<phi>
    by (smt (verit) SDI)
  then have t1: \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> m \<Znrres> U) = (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute)
  ;; unfold t1
  \<medium_right_bracket>. .



lemma [\<phi>reason 1183 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2
          (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n \<and> n < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W)
      (Automatic_Morphism (RP \<and>\<^sub>\<r> (\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m m-n = mn) \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical T')
        (Structural_Extract' (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> n \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') ((r',x') \<Ztypecolon> (n \<Znrres> R' \<^emph> mn \<Znrres> T')) P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Compact_Antecedent_def Action_Tag_def Premise_def
  by (blast intro: Structural_Extract_share_ge[unfolded Action_Tag_def]
                   Structural_Extract_share_le[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1173 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < m \<and> m < n
\<Longrightarrow> \<phi>Sep_Disj_Identical U
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U)
      (Automatic_Morphism (RP \<and>\<^sub>\<r> (\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m nm = n - m) \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical U')
        (Structural_Extract' (y' \<Ztypecolon> n \<Znrres> U') ((w',y') \<Ztypecolon> m \<Znrres> W' \<^emph> nm \<Znrres> U') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Compact_Antecedent_def Action_Tag_def Premise_def
  by (blast intro: Structural_Extract_share_ge[unfolded Action_Tag_def]
                   Structural_Extract_share_le[unfolded Action_Tag_def]
                   Structural_Extract'_imply_P)


paragraph \<open>Normalization for Permission\<close>

subparagraph \<open>Extract each component in a composite structure, step by step\<close>

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2011 for
    \<open>Structural_Extract ?X ?R ((?x,?y) \<Ztypecolon> ?n \<Znrres> (?T \<^emph> ?U)) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> T' \<^emph> n \<Znrres> U') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W
      (Automatic_Morphism RP (Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> (T' \<^emph> U')) W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>Prod
  by blast

lemma [\<phi>reason 2011 for
    \<open>Structural_Extract ((?x,?y) \<Ztypecolon> ?n \<Znrres> (?T \<^emph> ?U)) ?W ?X ?R (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> T' \<^emph> n \<Znrres> U') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> (T' \<^emph> U')) W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>Prod
  by blast



lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2011 for \<open>Structural_Extract ?X ?R (?x \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow> ?T) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close> ]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt
  by blast

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x' \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow> ?T') ?W' ?X' ?R' (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract (x' \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt
  by blast



lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast

lemma [\<phi>reason 2011 for \<open>Structural_Extract ?Y ?W (?x \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?R (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract Y' W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) R Y W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract Y' W' (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) R Y W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast





lemma [\<phi>reason 2000]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract (x \<Ztypecolon> n * m \<Znrres> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Action_Tag_def
  by (metis Imply_def Inhabited_def \<phi>Share_\<phi>Share \<phi>Share_inhabited set_mult_inhabited)

lemma [\<phi>reason 2011 for \<open>Structural_Extract ?X ?R (?x \<Ztypecolon> ?n \<Znrres> ?m \<Znrres> ?T) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n * m \<Znrres> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n \<Znrres> m \<Znrres> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?m \<Znrres> ?T) ?W ?X ?R (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n * m \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n \<Znrres> m \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Premise_def by simp



text \<open>After all of these normalization, if we encounter the requirement to extract permission n,
  but there is no permission annotation for the current object, we know it is to extract from
  a total permission.\<close>

lemma Structural_Extract_pad_share_left
  [\<phi>reason 2000 for \<open>Structural_Extract (?x \<Ztypecolon> ?T) ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp

lemma Structural_Extract_pad_share_right
  [\<phi>reason 2000 for \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x \<Ztypecolon> ?T) ?R ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (y \<Ztypecolon> n \<Znrres> U) W (x \<Ztypecolon> 1 \<Znrres> T) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> n \<Znrres> U) W (x \<Ztypecolon> T) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp


lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x \<Ztypecolon> ?T) ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> 1 \<Znrres> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x \<Ztypecolon> ?T) ?R (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> 1 \<Znrres> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp


section \<open>Small Process - II\<close>

subsection \<open>Collect Return Values\<close>

definition collect_return_values' :: \<open>('vs::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> 'vs::VALs \<phi>arg \<Rightarrow> assn\<close>
  where \<open>collect_return_values' S vs = S vs\<close>

abbreviation \<open>collect_return_values S vs \<equiv> TAIL (collect_return_values' S vs)\<close>

definition Collect_Return_Values :: \<open>assn \<Rightarrow> ('vs::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> 'vs::VALs \<phi>arg \<Rightarrow> bool\<close>
  where \<open>Collect_Return_Values S S_out V_out \<longleftrightarrow> S = S_out V_out\<close>

lemma Collect_Return_Values_I: \<open>Collect_Return_Values (S V) S V\<close>
  unfolding Collect_Return_Values_def ..

\<phi>reasoner_ML Collect_Return_Values 1000 (\<open>Collect_Return_Values ?S ?var_S_out ?var_V_out\<close>) = \<open>
  fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (\<^Const_>\<open>Collect_Return_Values _\<close> $ S $ Var S' $ Var V')
          = Thm.major_prem_of sequent
    val (V'',S'') = Procedure_Syntax.abstract_return_vals
                            "\<v>\<s>" (TVar (("ret", Thm.maxidx_of sequent),\<^sort>\<open>VALs\<close>)) true S
          |> apply2 (Thm.cterm_of ctxt)
   in Drule.infer_instantiate_types ctxt [(S',S''),(V',V'')] sequent
          |> (fn th => @{thm Collect_Return_Values_I} RS th)
          |> pair ctxt |> Seq.single
  end
\<close>

lemma [\<phi>reason 2550 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> \<blangle> collect_return_values ?S ?vs \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?Any @action reason_ToSA ?mode ?G\<close>]:
  \<open> Collect_Return_Values X S vs
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> collect_return_values S vs \<brangle> @action reason_ToSA mode G\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def FOCUS_TAG_def Action_Tag_def
            TAIL_def
  by (simp add: view_shift_id)

lemma [\<phi>reason 3200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> collect_return_values ?S ?vs \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?Any @action reason_ToSA ?mode ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> \<blangle> collect_return_values 0 \<phi>V_none \<brangle> @action reason_ToSA mode G\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def FOCUS_TAG_def Action_Tag_def
            TAIL_def
  by (simp add: view_shift_id)


end
