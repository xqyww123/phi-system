chapter \<open>Reasoning Processes in IDE-CP - Part III\<close>

text \<open>Here we give the implementation of all large reasoning processes that are declared in
the previous part I.\<close>


theory IDE_CP_Reasoning3
  imports IDE_CP_App2
begin


(*subsubsection \<open>Syntax & Auxiliary\<close>

definition "addr_allocated heap addr \<longleftrightarrow> MemAddress addr \<in> dom heap"
adhoc_overloading allocated \<rightleftharpoons> addr_allocated

(* lemma addr_allocated_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> addr_allocated h addr \<Longrightarrow> addr_allocated h' addr"
  unfolding addr_allocated_def by auto
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto *)
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto

definition MemAddrState :: "heap \<Rightarrow> nat addr \<Rightarrow> 'b::lrep set \<Rightarrow> bool"
  where "MemAddrState h addr S \<longleftrightarrow> addr_allocated h addr \<and> shallowize (the (h (MemAddress addr))) \<in> S"
adhoc_overloading ResourceState \<rightleftharpoons> MemAddrState

(*lemma MemAddrState_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> MemAddrState h' addr S"
  unfolding MemAddrState_def addr_allocated_def by auto (metis \<phi>set_mono domI map_le_def option.sel) *)

lemma MemAddrState_I_neq[intro]: "k2 \<noteq> k \<Longrightarrow> MemAddrState h k2 S \<Longrightarrow> MemAddrState (h(MemAddress k := v)) k2 S"
  and MemAddrState_I_eq[intro]: "v' \<in> S \<Longrightarrow> MemAddrState (h(MemAddress k \<mapsto> deepize v')) k S"
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_E[elim]:
  "MemAddrState h addr S \<Longrightarrow> (addr_allocated h addr \<Longrightarrow> Satisfiable S \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding MemAddrState_def Satisfiable_def by blast
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


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<is> T \<Longrightarrow> MemAddress a \<in> S \<Longrightarrow> h |` S \<^bold>a\<^bold>t a \<is> T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<is> T \<Longrightarrow> MemAddress a \<notin> S \<Longrightarrow> h |` (- S) \<^bold>a\<^bold>t a \<is> T "
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<is> T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<is> T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<is> T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<is> T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)

*)

section \<open>Small Processes - I\<close>

(* TODO! not that easy! IMPORTANT!

subsection \<open>Unification of \<lambda>-Abstraction\<close>

\<phi>type_def Function_over :: \<open>('a,'b) \<phi> \<Rightarrow> 'c \<Rightarrow> ('a, 'c \<Rightarrow> 'b) \<phi>\<close> (infix "<func-over>" 40)
  where \<open>(T <func-over> x) = (\<lambda>f. f x \<Ztypecolon> T)\<close>
  deriving Basic
    (* and \<open> \<guard> \<condition> x = y (*I don't know if the functor properties are required in this \<phi>-type.
                                  *All of the ToA reasonings reduce to destruction.*)
         \<Longrightarrow> Transformation_Functor (\<lambda>T. T <func-over> x) (\<lambda>T. T <func-over> y) T U
                                    (\<lambda>f. {f x}) (\<lambda>g. UNIV) (\<lambda>r f g. r (f x) (g y)) \<close>
       and \<open>\<guard> \<condition> x = y
         \<Longrightarrow> Functional_Transformation_Functor (\<lambda>T. T <func-over> x) (\<lambda>T. T <func-over> y) T U
                                  (\<lambda>f. {f x}) (\<lambda>g. UNIV) (\<lambda>_ P f. P (f x)) (\<lambda>m _ f _. m (f x))\<close> *)

text \<open>
  \<^term>\<open>f \<Ztypecolon> T <func-over> x\<close> constrains f is a function about x,
    i.e. \<^prop>\<open>f \<Ztypecolon> T <func-over> x \<equiv> f x \<Ztypecolon> T\<close>.
  It is useful to resolve the ambiguity of higher-order unification as that occurs between
    \<^schematic_term>\<open>?f x \<Ztypecolon> T\<close> and \<^term>\<open>g x \<Ztypecolon> T\<close>.
  In addition, in the introduction transformation that constructs such \<open>?f \<Ztypecolon> T <func-over> x\<close> from
    \<open>fx \<Ztypecolon> T\<close>, the reasoning is configured as exhaustively binding all free occurrence of \<open>x\<close> in \<open>fx\<close>,
    i.e., the instantiated \<open>?f\<close> shall contain no syntactic occurrence of term \<open>x\<close>.
\<close>


thm Function_over.elim_reasoning


term \<open>Functional_Transformation_Functor (\<lambda>T. T <func-over> x) (\<lambda>T. T <func-over> y) T U
                                  (\<lambda>f. {f x}) (\<lambda>g. UNIV) (\<lambda>_ P f. P (f x)) (\<lambda>m _ f _. m (f x))\<close>
term \<open> \<guard> \<condition> x = y
   \<Longrightarrow> Transformation_Functor (\<lambda>T. T <func-over> x) (\<lambda>T. T <func-over> y) T U (\<lambda>f. {f x}) (\<lambda>g. UNIV) (\<lambda>r f g. r (f x) (g y)) \<close>

thm rel_fun_def

thm Function_over.elim_reasoning

thm Function_over.unfold

lemma Function_over_case_named [simp]:
  \<open>(case_named f \<Ztypecolon> T <func-over> tag x) = (f \<Ztypecolon> T <func-over> x)\<close>
  by (simp add: Function_over.unfold)

declare Function_over_case_named [folded atomize_eq, named_expansion]

thm Function_over.intro_reasoning

lemma [\<phi>reason %ToA_normalizing]:
  \<open> Y \<transforms> fx \<Ztypecolon> T \<with> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<transforms> f \<Ztypecolon> T <func-over> x \<with> P\<close>
  unfolding lambda_abstraction_def
  by (simp add: Function_over.intro_reasoning)

lemma [\<phi>reason %ToA_normalizing]:
  \<open> Y \<transforms> fx \<Ztypecolon> T \<^emph>[C] R \<with> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<transforms> f \<Ztypecolon> (T <func-over> x) \<^emph>[C] R \<with> P\<close>
  unfolding Transformation_def lambda_abstraction_def
  by simp



lemma [\<phi>reason 2000]:
  \<open> f x \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> f \<Ztypecolon> T <func-over> x \<transforms> Y \<with> P\<close>
  unfolding Transformation_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse ?input (\<lambda>v. ?f \<Ztypecolon> ?T v <func-over> ?x :: assn)\<close>
]:
  \<open> Synthesis_Parse input (\<lambda>v. fx \<Ztypecolon> T v)
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Synthesis_Parse input (\<lambda>v. f \<Ztypecolon> T v <func-over> x :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200]:
  \<open> \<proc> g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> \<blangle> f x \<Ztypecolon> T v \<brangle> \<rbrace> \<throws> E @tag synthesis
\<Longrightarrow> \<proc> g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> \<blangle> f \<Ztypecolon> T v <func-over> x \<brangle> \<rbrace> \<throws> E @tag synthesis\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)
*)

consts partial_add_split :: action
       non_trivial_partial_add_split :: action

declare [[
    \<phi>premise_attribute       [unfolded Action_Tag_def] for \<open>_ @tag partial_add_split\<close> (%\<phi>attr_late_normalize),
    \<phi>premise_attribute once? [useful] for \<open>_ @tag partial_add_split\<close>                  (%\<phi>attr),
    \<phi>premise_attribute       [unfolded Action_Tag_def] for \<open>_ @tag non_trivial_partial_add_split\<close> (%\<phi>attr_late_normalize),
    \<phi>premise_attribute once? [useful] for \<open>_ @tag non_trivial_partial_add_split\<close>      (%\<phi>attr)
]]

lemma fst_snt_lambda_pair[simp]:
  \<open>fst o (\<lambda>x. (f x, g x)) = f\<close>
  \<open>snd o (\<lambda>x. (f x, g x)) = g\<close>
  by (simp add: fun_eq_iff)+

lemma apfst_apsnd_lambda_x_x[simp]:
  \<open>apfst (\<lambda>x. x) = (\<lambda>x. x)\<close>
  \<open>apsnd (\<lambda>x. x) = (\<lambda>x. x)\<close>
  by (simp add: fun_eq_iff)+
(*\<Longrightarrow> Dx' T (fst x, fst (snd x))
\<Longrightarrow> Dx T (fst x) 
and [\<phi>reason add]*)



section \<open>Convergence of Branches\<close>

text \<open>The process transforms assertions of form \<^term>\<open>(If P A B)\<close> into the canonical form (\<open>\<exists>\<and>\<close>-MTF).
  Assertions \<^term>\<open>(If P A B)\<close> can be yielded from branch statements.
  Data refinements in \<phi>-BI are represented syntactically and the automation upon them is
  syntax-driven. We can call \<open>\<exists>\<and>\<close>-MTF canonical because on the form the refinements are expressed
  explicitly in a direct syntax. By converting \<^term>\<open>(If P A B)\<close> into the canonical form, we actually
  resolve the join of the refinements from two branches, i.e., we find out for each object what is
  its abstraction after the branch join, according to its abstractions in the two branches.

  The two branches may have identical \<phi>-types but may disordered. The process sorts the \<phi>-types.
  One certain object may be specified by two different refinements. The process
  recognizes which two \<phi>-types in the two branches are specifying the object, and applies ToA
  to transform one to another.
  To recognize this, we rely on syntactic rule binding on each specific \<phi>-type to give an identifier
  of the object. An identifier can be a term of any logic type. If the syntactic rule is not given
  for a \<phi>-type, we only support the case when the two branches have identical \<phi>-types.

  In the implementation, we always transform \<phi>-types in the right-side branch to those in the left side,
  i.e., from \<open>B\<close> to \<open>A\<close> for \<^term>\<open>(If P A B)\<close>.
\<close>

consts br_join :: \<open>action\<close>

definition Identifier_of :: \<open>('c,'a) \<phi> \<Rightarrow> 'id \<Rightarrow> ('c2,'a2) \<phi> \<Rightarrow> bool\<close>
  where \<open>Identifier_of T identifier pattern \<equiv> True\<close>
  \<comment> \<open>The \<open>pattern\<close> matches any \<phi>-type specifying the objects of identifier \<open>id\<close>.
      By partially transforming a BI assertion to the \<open>pattern\<close>, we can find from the BI assertion
      a \<phi>-type specifying the object \<open>id\<close>\<close>

\<phi>property_deriver Identifier_of 555 for (\<open>Identifier_of _ _ _\<close>)
  = \<open>Phi_Type_Derivers.meta_Synt_Deriver
      ("Identifier_of", @{lemma' \<open>Identifier_of T identifier pattern\<close> by (simp add: Identifier_of_def)},
       SOME @{reasoner_group %cutting})\<close>


subsubsection \<open>Conventions\<close>

declare [[\<phi>reason_default_pattern
    \<open>If ?P ?A ?B \<transforms> _ @tag br_join \<close> \<Rightarrow> \<open>If ?P ?A ?B \<transforms> _ @tag br_join \<close> (100)
and \<open>If ?P ?A ?B = _ @tag br_join \<close> \<Rightarrow> \<open>If ?P ?A ?B = _ @tag br_join \<close> (100)

and \<open>?X @tag br_join \<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Bad rule\<close> (?X @tag br_join ))\<close> (0)

and \<open>Identifier_of ?T _ _\<close> \<Rightarrow> \<open>Identifier_of ?T _ _\<close> (100)
]]

\<phi>reasoner_group \<phi>br_join_all = (100, [1,3000]) for \<open>If C A B @tag br_join\<close>
    \<open>All rules of \<phi>-type branch convergence\<close>
  and \<phi>br_join_fail = (1,[1,10]) for \<open>If C A B @tag br_join\<close> in \<phi>br_join_all
                     \<open>Fallbacks\<close>
  and \<phi>br_join_search_counterpart = (30, [28,30]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_fail
                     \<open>Looks from the false-branch for the counterpart of the heading \<phi>-type in the true-branch,
                      and enters the sub-reasoning for joining the two \<phi>-types.\<close>
  and \<phi>br_join_derived = (50,[50,50]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_search_counterpart
                     \<open>Derived from functor properties\<close>
  and \<phi>br_join_cut = (1000, [1000, 1030]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all > \<phi>br_join_derived
                     \<open>Cutting rules\<close>
  and \<phi>br_join_spec = (1100, [1100,2000]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_cut
                     \<open>Rules for specific connectives\<close>
  and \<phi>br_join_normalize = (2100, [2100,2300]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_spec
                     \<open>Normalization rules\<close>
  and \<phi>br_join_red = (2500, [2500, 2800]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_spec
                     \<open>Reductions of high priority\<close>
  and \<phi>br_join_red_zero = (2900, [2900,2900]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all > \<phi>br_join_red
                     \<open>Reductions for zero\<close>
  and \<phi>br_join_success = (2990, [2990,3000]) for \<open>If C A B @tag br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_red_zero
                     \<open>Direct success\<close>

\<phi>reasoner_group \<phi>identifier_of = (1000, [1000, 3000]) for \<open>Identifier_of T i pattern\<close>
      \<open>User rules giving identifiers of the concrete obejct refining the \<phi>-type abstraction, so that
       we can recognize \<phi>-types specifying on an identical object.\<close>
  and \<phi>identifier_of_fallback = (10, [10, 10]) for \<open>Identifier_of T i pattern\<close>
      \<open>Fallback rules of %\<phi>identifier_of\<close>

subsection \<open>Identifier_of\<close>

subsubsection \<open>Fallback\<close>

lemma [\<phi>reason %\<phi>identifier_of_fallback]:
  \<open> Identifier_of T T T \<close>
  unfolding Identifier_of_def ..

subsubsection \<open>Built-in\<close>

lemma [\<phi>reason %\<phi>identifier_of]:
  \<open> Identifier_of (Val v T) v (Val v T')\<close>
  unfolding Identifier_of_def ..


subsection \<open>Reasonings of Branch Join\<close>

subsubsection \<open>Entry Point\<close>

lemma [\<phi>reason %\<phi>br_join_success for \<open>If _ _ _ \<transforms> _ @tag invoke_br_join\<close>]:
  \<open> Simplify (assertion_simps undefined) A' A
\<Longrightarrow> Simplify (assertion_simps undefined) B' B
\<Longrightarrow> If P A' B' \<transforms> C @tag br_join
\<Longrightarrow> If P A  B  \<transforms> C @tag invoke_br_join \<close>
  unfolding Action_Tag_def Simplify_def
  by blast


subsubsection \<open>Fallback and Termination\<close>

lemma [\<phi>reason default %\<phi>br_join_fail]:
  \<open>If P A B = If P A B @tag br_join\<close>
  unfolding Action_Tag_def ..

lemma [\<phi>reason %\<phi>br_join_success for \<open>If ?P ?A ?A'' = ?X @tag br_join\<close>]:
  \<open>If P A A = A @tag br_join\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason default %\<phi>br_join_fail]:
  \<open> If P A B \<transforms> If P A B @tag br_join \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason default %\<phi>br_join_fail+4]:
  " If P T U = Z @tag br_join
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<transforms> (If P x y \<Ztypecolon> Z) @tag br_join"
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_success+5 for \<open>If _ (_ \<Ztypecolon> _) (_ \<Ztypecolon> _) \<transforms> _ @tag br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> T) \<transforms> (If P x y \<Ztypecolon> T) @tag br_join\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_success for \<open>If ?P ?A ?A'' \<transforms> ?X @tag br_join\<close>]:
  \<open>If P A A \<transforms> A @tag br_join\<close>
  unfolding Action_Tag_def Transformation_def by simp


subsubsection \<open>Zero\<close>

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open>If P A 0 \<transforms> (A \<subj> P) @tag br_join\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: zero_set_def)

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open>If P 0 A \<transforms> (A \<subj> \<not> P) @tag br_join\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: zero_set_def)

subsubsection \<open>One\<close>

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open> Identity_Element\<^sub>I A Any
\<Longrightarrow> If P A 1 \<transforms> 1 @tag br_join\<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def
  by (cases P; simp add: transformation_weaken)

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open> Identity_Element\<^sub>I A Any
\<Longrightarrow> If P 1 A \<transforms> 1 @tag br_join\<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def
  by (cases P; simp add: transformation_weaken)

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open> Identity_Element\<^sub>I A Any
\<Longrightarrow> If P A (x \<Ztypecolon> \<circle>) \<transforms> 1 @tag br_join\<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def
  by (cases P; simp add: transformation_weaken)

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open> Identity_Element\<^sub>I A Any
\<Longrightarrow> If P (x \<Ztypecolon> \<circle>) A \<transforms> 1 @tag br_join\<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def
  by (cases P; simp add: transformation_weaken)



subsubsection \<open>Subjection\<close>

\<phi>reasoner_group \<phi>br_join_subj = (%\<phi>br_join_spec+800, [%\<phi>br_join_spec+800, %\<phi>br_join_spec+820]) for \<open>If C A B @tag br_join\<close>
                                 in \<phi>br_join_spec
                                \<open>Reductions for Subejction\<close>

lemma [\<phi>reason %\<phi>br_join_subj+20]:
  \<open> If P (L \<subj> Q1 \<and> Q2) R \<transforms> Z @tag br_join
\<Longrightarrow> If P (L \<subj> Q1 \<subj> Q2) R \<transforms> Z @tag br_join \<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason %\<phi>br_join_subj+20]:
  \<open> If P L (R \<subj> Q1 \<and> Q2) \<transforms> Z @tag br_join
\<Longrightarrow> If P L (R \<subj> Q1 \<subj> Q2) \<transforms> Z @tag br_join \<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason %\<phi>br_join_subj+10]:
  \<open> If P QL QR = Q @tag br_join
\<Longrightarrow> If P L R \<transforms> X @tag br_join
\<Longrightarrow> If P (L \<subj> QL) (R \<subj> QR) \<transforms> (X \<subj> Q) @tag br_join\<close>
  unfolding Action_Tag_def Transformation_def by force

lemma [\<phi>reason %\<phi>br_join_subj]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  \<open> If P L R \<transforms> X @tag br_join
\<Longrightarrow> If P (L \<subj> Q) R \<transforms> (X \<subj> P \<longrightarrow> Q) @tag br_join\<close>
  unfolding Transformation_def Action_Tag_def by simp

lemma [\<phi>reason %\<phi>br_join_subj]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  \<open> If P L R \<transforms> X @tag br_join
\<Longrightarrow> If P L (R \<subj> Q) \<transforms> (X \<subj> \<not>P \<longrightarrow> Q) @tag br_join\<close>
  unfolding Action_Tag_def Transformation_def by simp


subsubsection \<open>Existential\<close>

\<phi>reasoner_group \<phi>br_join_ex = (%\<phi>br_join_spec+700, [%\<phi>br_join_spec+700, %\<phi>br_join_spec+720])
                                for \<open>If C A B @tag br_join\<close> in \<phi>br_join_spec and < \<phi>br_join_subj
                              \<open>Reductions for Existence\<close>

lemma Conv_Merge_Ex_both_imp:
  \<open> (\<And>x. If P (L x) (R x) \<transforms> X x @tag br_join)
\<Longrightarrow> If P (\<exists>* x. L x) (\<exists>* x. R x) \<transforms> (\<exists>* x. X x) @tag br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; clarsimp simp add: set_eq_iff; blast)

lemma Conv_Merge_Ex_R_imp [\<phi>reason %\<phi>br_join_ex]:
  \<open> (\<And>x. If P L (R x) \<transforms> X x @tag br_join)
\<Longrightarrow> If P L (\<exists>* x. R x) \<transforms> (\<exists>* x. X x) @tag br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; simp add: set_eq_iff; blast)

lemma [\<phi>reason %\<phi>br_join_ex]:
  \<open> (\<And>x. If P (L x) R \<transforms> X x @tag br_join)
\<Longrightarrow> If P (\<exists>* x. L x) R \<transforms> (\<exists>* x. X x) @tag br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; simp add: set_eq_iff; blast)

text \<open>The merging recognizes two existential quantifier are identical if their type and variable name
  are the same. If so it uses Conv_Merge_Ex_both to merge the quantification,
  or else the right side is expanded first.\<close>

\<phi>reasoner_ML Merge_Existential_imp %\<phi>br_join_ex+20 (\<open>If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<transforms> ?X\<close>) = \<open>
  fn (_, (ctxt,sequent)) =>
    let
      val ((Const (\<^const_name>\<open>If\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExBI\<close>, _) $ Abs (exa,tya,_))
                                           $ (Const (\<^const_name>\<open>ExBI\<close>, _) $ Abs (exb,tyb,_))), _, _)
          = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      val sequent' = if exa = exb andalso tya = tyb
                     then @{thm Conv_Merge_Ex_both_imp} RS sequent
                     else @{thm Conv_Merge_Ex_R_imp} RS sequent
    in Seq.single (ctxt, sequent')
    end
\<close>


subsubsection \<open>Looks for the counterpart\<close>

definition br_join_counter_part_fail :: \<open>'c BI \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
  where \<open>br_join_counter_part_fail _ _ \<equiv> False\<close>

lemma [\<phi>reason default %cutting]:
  \<open> FAIL TEXT(\<open>\<phi>-Type\<close> (x \<Ztypecolon> T) \<open>is given in the true-branch but its counterpart\<close> B \<open>is not seen in the false-branch.\<close> \<newline>
              \<open>Perhaps, I should search a more general form \<close> T'' \<open>of the counterpart and if so, feed \<phi>-LPR a rule\<close> \<newline>
              (Identifier_of T identifier T''))
\<Longrightarrow> br_join_counter_part_fail (x \<Ztypecolon> T) B \<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason default %\<phi>br_join_search_counterpart]:
  \<open> Identifier_of T identifier T'
\<Longrightarrow> (R \<transforms> y \<Ztypecolon> T' \<remains> R') \<or>\<^sub>c\<^sub>u\<^sub>t
    br_join_counter_part_fail (x \<Ztypecolon> T) (y \<Ztypecolon> T')
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> T') \<transforms> Z @tag br_join
\<Longrightarrow> If P L R' \<transforms> X @tag br_join
\<Longrightarrow> If P ((x \<Ztypecolon> T) * L) R \<transforms> Z * X @tag br_join\<close>
  unfolding Action_Tag_def Transformation_def Premise_def Orelse_shortcut_def
            br_join_counter_part_fail_def
  by (cases P; clarsimp; blast)

lemma [\<phi>reason default %\<phi>br_join_search_counterpart]:
  \<open> Identifier_of T identifier T'
\<Longrightarrow> (y, w) \<Ztypecolon> U \<OTast> W \<transforms> y' \<Ztypecolon> T' \<OTast> U'\<^sub>R @tag \<T>\<P>'
\<Longrightarrow> Identity_Element\<^sub>E (w \<Ztypecolon> W) \<or>\<^sub>c\<^sub>u\<^sub>t br_join_counter_part_fail (fst x \<Ztypecolon> T) (y'' \<Ztypecolon> T')
\<Longrightarrow> If P (fst x \<Ztypecolon> T) (fst y' \<Ztypecolon> T') \<transforms> Z @tag br_join
\<Longrightarrow> If P (snd x \<Ztypecolon> T\<^sub>R) (snd y' \<Ztypecolon> U'\<^sub>R) \<transforms> Z\<^sub>R @tag br_join
\<Longrightarrow> Z * Z\<^sub>R \<transforms> Z' @clean
\<Longrightarrow> If P (x \<Ztypecolon> T \<^emph> T\<^sub>R) (y \<Ztypecolon> U) \<transforms> Z' @tag br_join \<close>
  for Z' :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def Transformation_def Premise_def br_join_counter_part_fail_def
            Orelse_shortcut_def Ant_Seq_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def \<phi>Prod'_def
  by ((cases P; clarsimp), blast, metis mult_1_class.mult_1_right sep_magma_1_left)


lemma Br_join_atom_assertion[no_atp]:
      \<comment> \<open>For assertion \<open>A\<close> that is not a \<phi>-type\<close>
  \<open> R \<transforms> A \<remains> R'
\<Longrightarrow> If P L R' \<transforms> X @tag br_join
\<Longrightarrow> If P (A * L) R \<transforms> A * X @tag br_join \<close>
  unfolding Action_Tag_def
  by ((cases P; simp), simp add: transformation_left_frame,
      metis REMAINS_def mk_elim_transformation transformation_left_frame)

lemma Br_join_atom_assertion'[no_atp]:
  \<open> R \<transforms> A
\<Longrightarrow> If P A R \<transforms> A @tag br_join \<close>
  unfolding Action_Tag_def
  by (cases P; simp)
  



subsubsection \<open>Joapplyin Two \<phi>-Types\<close>

\<phi>reasoner_group br_join_fallback = (20, [11,20]) for \<open>If C (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<transforms> Y @tag br_join\<close> 
                                                  in \<phi>br_join_all and > \<phi>br_join_fail
      \<open>Fallbacks of joining two \<phi>-types, using ToA\<close>

paragraph \<open>Fallback by ToA\<close>

definition Common_Base_Types :: \<open>('c,'a1) \<phi> \<Rightarrow> ('c,'a2) \<phi> \<Rightarrow> ('c,'a3) \<phi> \<Rightarrow> bool\<close>
  where \<open>Common_Base_Types T U Base \<equiv> True\<close>

\<phi>reasoner_group Common_Base_Types = (1000, [1000,1100])
    \<open>specifying the common base type between two given types, used in by_join.\<close>
  and Common_Base_Types_derived = (40, [40,50]) \<open>derived\<close>
  and Common_Base_Types_fallback = (10, [10,20])
    \<open>fallbacks\<close>

declare [[
  \<phi>default_reasoner_group \<open>Common_Base_Types _ _ _\<close> : %Common_Base_Types (100),
  \<phi>reason_default_pattern \<open>Common_Base_Types ?T ?U _\<close> \<Rightarrow> \<open>Common_Base_Types ?T ?U _\<close> (100)
]]

\<phi>property_deriver Common_Base_Types 555 for (\<open>Common_Base_Types _ _ _\<close>)
  = \<open>Phi_Type_Derivers.meta_Synt_Deriver
      ("Common_Base_Types", @{lemma' \<open>Common_Base_Types T U Base\<close> by (simp add: Common_Base_Types_def)},
       SOME @{reasoner_group %cutting})\<close>

lemma [\<phi>reason default %Common_Base_Types_fallback]:
  \<open>Common_Base_Types T U T\<close>
  unfolding Common_Base_Types_def by simp

lemma [\<phi>reason default %br_join_fallback]:
  \<open> Common_Base_Types T U V
\<Longrightarrow> (\<condition> P \<Longrightarrow> \<guard> x \<Ztypecolon> T \<transforms> x' \<Ztypecolon> V)
\<Longrightarrow> (\<condition> \<not> P \<Longrightarrow> \<guard> y \<Ztypecolon> U \<transforms> y' \<Ztypecolon> V)
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<transforms> If P x' y' \<Ztypecolon> V @tag br_join \<close>
  unfolding Action_Tag_def Transformation_def \<r>Guard_def Premise_def
  by clarsimp 

\<phi>reasoner_ML br_join_fallback %br_join_fallback-4 (\<open>If _ (_ \<Ztypecolon> _) (_ \<Ztypecolon> _) \<transforms> _ @tag br_join\<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () =>
    let exception NOT_AVAILABLE
        fun conv ctm =
          let val (A,B) = case Thm.term_of ctm of Const(\<^const_name>\<open>If\<close>, _) $ _ $ A $ B => (A,B)
           in if A aconv B
              then Conv.rewr_conv @{thm' if_cancel} ctm
              else case (A,B)
                of (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T, Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x' $ T') =>
                    if Term.head_of T aconv Term.head_of T'
                    then (Conv.rewr_conv @{lemma' \<open>If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<equiv> (If P x y) \<Ztypecolon> (If P T U)\<close>
                                              by (unfold atomize_eq, cases P, simp, simp)}
                          then_conv Conv.arg_conv conv) ctm
                    else raise NOT_AVAILABLE
                 | (F $ x, G $ y) =>
                    let val Pc = Thm.dest_arg (Thm.dest_fun2 ctm)
                        val (Ac, Bc) = (Thm.dest_arg1 ctm, Thm.dest_arg ctm)
                        val (Fc, xc) = (Thm.dest_fun Ac, Thm.dest_arg Ac)
                        val (Gc, yc) = (Thm.dest_fun Bc, Thm.dest_arg Bc)
                     in if x aconv y
                        then (Conv.rewr_conv (@{print} \<^instantiate>\<open>
                                      C=Pc and fa=Fc and fb=Gc and a=xc and
                                      'b=\<open>Thm.ctyp_of_cterm xc\<close> and 'a=\<open>Thm.dest_ctyp1 (Thm.ctyp_of_cterm Fc)\<close>
                                   in lemma \<open>if C then fa a else fb a \<equiv> (if C then fa else fb) a\<close>
                                         by (simp add: if_distribR)\<close>)
                              then_conv Conv.fun_conv conv) ctm
                        else if F aconv G
                        then Conv.rewr_conv \<^instantiate>\<open>
                                      c=Pc and f=Fc and x=xc and y=yc and
                                      'b=\<open>Thm.ctyp_of_cterm xc\<close> and 'a=\<open>Thm.dest_ctyp1 (Thm.ctyp_of_cterm Fc)\<close>
                                   in lemma \<open>(if c then f x else f y) \<equiv> f (if c then x else y)\<close>
                                         by (unfold atomize_eq, cases c, simp, simp)\<close> ctm
                        else (Conv.rewr_conv \<^instantiate>\<open>
                                      C=Pc and fa=Fc and fb=Gc and va=xc and vb=yc and
                                      'b=\<open>Thm.ctyp_of_cterm xc\<close> and 'a=\<open>Thm.dest_ctyp1 (Thm.ctyp_of_cterm Fc)\<close>
                                   in lemma \<open>if C then fa va else fb vb \<equiv> (if C then fa else fb) (if C then va else vb)\<close>
                                         by (simp add: If_distrib_fx)\<close>
                              then_conv Conv.fun_conv conv) ctm
                    end
          end
     in \<^try>\<open>(let
        val sequent'1 = Conv.gconv_rule (
              Phi_Conv.hhf_concl_conv (fn ctxt =>
                Phi_Syntax.transformation_conv conv Conv.all_conv Conv.all_conv
              ) ctxt ) 1 sequent
        val sequent'2 = @{thm' transformation_refl} RS (@{thm' Action_Tag_I} RS sequent'1)
         in SOME ((ctxt, sequent'2), Seq.empty)
        end
     handle NOT_AVAILABLE => NONE)
       catch E => error "!!!"\<close>
    end)
\<close>

lemma [\<phi>reason default %br_join_fallback-8]:
  \<open> WARNING TEXT(\<open>Fail to join \<phi>type\<close> T \<open>and\<close> U)
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<transforms> If P x y \<Ztypecolon> If P T U @tag br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; clarsimp)


paragraph \<open>By Transformation Functor\<close>

definition Gen_Br_Join :: \<open> 'a \<Rightarrow> 'b \<Rightarrow> 'c
                         \<Rightarrow> bool \<Rightarrow> bool
                         \<Rightarrow> bool \<close>
  where \<open> Gen_Br_Join F\<^sub>T F\<^sub>U F' P conds \<equiv> True \<close>

setup \<open>PLPR_Template_Properties.add_property_kinds [
  \<^pattern_prop>\<open>Gen_Br_Join _ _ _ _ _\<close>
]\<close>

\<phi>property_deriver Gen_Br_Join 555 for (\<open>Gen_Br_Join _ _ _ _ _\<close>)
  = \<open>Phi_Type_Derivers.meta_Synt_Deriver
      ("Gen_Br_Join", @{lemma' \<open>Gen_Br_Join F\<^sub>T F\<^sub>U F' P conds\<close> by (simp add: Gen_Br_Join_def)},
       SOME @{reasoner_group %cutting})\<close>

\<phi>reasoner_ML Default_Simplify %cutting (\<open>\<simplify>[br_join] _ : _\<close>)
  = \<open> Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty)
                         (fn ctxt => ctxt addsimps Useful_Thms.get ctxt
                                  |> Simplifier.del_cong @{thm' if_weak_cong}
                                  |> Simplifier.add_cong @{thm' if_cong}) {fix_vars=true})
      o snd\<close>

lemma [\<phi>reason_template default %\<phi>br_join_derived]:
  \<open> Gen_Br_Join F\<^sub>T F\<^sub>U F' P conds
\<Longrightarrow> \<guard> \<condition> conds
\<Longrightarrow> (\<condition> conds \<and>   P \<Longrightarrow> Functional_Transformation_Functor F\<^sub>T F' T Z D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T)
\<Longrightarrow> (\<condition> conds \<and> \<not> P \<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F' U Z D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U)
\<Longrightarrow> \<premise> (\<forall>a \<in> D\<^sub>T x. z (Inl a) \<in> R\<^sub>T x) \<and>
           (\<forall>b \<in> D\<^sub>U y. z (Inr b) \<in> R\<^sub>U y)
\<Longrightarrow> (\<And>a \<in> (If P (Inl ` D\<^sub>T x) (Inr ` D\<^sub>U y)). If P (projl a \<Ztypecolon> T) (projr a \<Ztypecolon> U) \<transforms> z a \<Ztypecolon> Z @tag br_join)
\<Longrightarrow> (\<simplify>[\<phi>instantiation] zzz : (If P (fm\<^sub>T (\<lambda>x. z (Inl x)) (\<lambda>_. True) x) (fm\<^sub>U (\<lambda>x. z (Inr x)) (\<lambda>_. True) y))) @tag \<A>_template_reason undefined
\<Longrightarrow> NO_SIMP (If P (x \<Ztypecolon> F\<^sub>T T) (y \<Ztypecolon> F\<^sub>U U)) \<transforms> zzz \<Ztypecolon> F' Z @tag br_join \<close>
  unfolding Action_Tag_def Premise_def Functional_Transformation_Functor_def Transformation_def
            meta_Ball_def meta_case_prod_def Simplify_def \<r>Guard_def NO_SIMP_def
  by (cases P; clarsimp)

lemma [\<phi>reason_template default %\<phi>br_join_derived]:
  \<open> Gen_Br_Join F\<^sub>T F\<^sub>U F' P conds
\<Longrightarrow> \<guard> \<condition> conds
\<Longrightarrow> (\<condition> conds \<and>   P \<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> F\<^sub>T F' T Z D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T)
\<Longrightarrow> (\<condition> conds \<and> \<not> P \<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> F\<^sub>U F' U Z D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U)
\<Longrightarrow> \<premise> (\<forall>p. \<forall>a \<in> D\<^sub>T p x. z p (Inl a) \<in> R\<^sub>T p x) \<and>
           (\<forall>p. \<forall>b \<in> D\<^sub>U p y. z p (Inr b) \<in> R\<^sub>U p y)
\<Longrightarrow> (\<And>p. \<And>a \<in> (If P (Inl ` D\<^sub>T p x) (Inr ` D\<^sub>U p y)). If P (projl a \<Ztypecolon> T p) (projr a \<Ztypecolon> U p) \<transforms> z p a \<Ztypecolon> Z p @tag br_join)
\<Longrightarrow> NO_SIMP (If P (x \<Ztypecolon> F\<^sub>T T) (y \<Ztypecolon> F\<^sub>U U)) \<transforms>
    (If P (fm\<^sub>T (\<lambda>p. z p o Inl) (\<lambda>_ _. True) x) (fm\<^sub>U (\<lambda>p. z p o Inr) (\<lambda>_ _. True) y)) \<Ztypecolon> F' Z @tag br_join \<close>
  unfolding Action_Tag_def Premise_def Functional_Transformation_Functor\<^sub>\<Lambda>_def Transformation_def
            meta_Ball_def meta_case_prod_def Simplify_def \<r>Guard_def NO_SIMP_def
  by (cases P; clarsimp)

let_\<phi>type Set_Abst deriving \<open>Gen_Br_Join \<S> \<S> \<S> P True\<close>
let_\<phi>type \<phi>Composition    deriving \<open>Gen_Br_Join ((\<Zcomp>) B) ((\<Zcomp>) B') ((\<Zcomp>) B) P (B = B')\<close>
let_\<phi>type \<phi>Mul_Quant      deriving \<open>Gen_Br_Join (\<big_ast>\<^sup>\<phi>\<^sub>0 I) (\<big_ast>\<^sup>\<phi>\<^sub>0 J) (\<big_ast>\<^sup>\<phi>\<^sub>0 (If P I J)) P True\<close>
let_\<phi>type \<phi>Mul_Quant\<^sub>\<Lambda>     deriving \<open>Gen_Br_Join (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> J) (\<big_ast>\<^sup>\<phi> (If P I J)) P True\<close>
let_\<phi>type \<phi>ScalarMul      deriving \<open>Gen_Br_Join (\<phi>ScalarMul f s) (\<phi>ScalarMul f s') (\<phi>ScalarMul f s) P (s' = s)\<close>
let_\<phi>type List_Item       deriving \<open>Gen_Br_Join List_Item List_Item List_Item P True\<close>
let_\<phi>type \<phi>Fun'    deriving \<open>Gen_Br_Join ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') ((\<Zcomp>\<^sub>f) f) P (f' = f)\<close>
let_\<phi>type \<phi>Some    deriving \<open>Gen_Br_Join \<phi>Some \<phi>Some \<phi>Some P True\<close>
let_\<phi>type \<phi>MapAt   deriving \<open>Gen_Br_Join ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k') ((\<^bold>\<rightarrow>) k) P (k' = k)\<close>
let_\<phi>type \<phi>MapAt_L deriving \<open>Gen_Br_Join ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k') ((\<^bold>\<rightarrow>\<^sub>@) k) P (k' = k)\<close>
let_\<phi>type \<phi>Share   deriving \<open>Gen_Br_Join ((\<odiv>) n) ((\<odiv>) m) ((\<odiv>) (If P n m)) P True\<close>
let_\<phi>type Discrete    deriving \<open>Gen_Br_Join Discrete Discrete Discrete P True\<close>
let_\<phi>type Val      deriving \<open>Gen_Br_Join (Val v) (Val v) (Val v) P True\<close>

lemma [\<phi>reason_template default %Common_Base_Types_derived]:
  \<open> Functional_Transformation_Functor F\<^sub>T F' T V D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F' U V D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> Common_Base_Types T U V
\<Longrightarrow> Common_Base_Types (F\<^sub>T T) (F\<^sub>U U) (F' V) \<close>
  unfolding Common_Base_Types_def
  by simp

lemma [\<phi>reason add]:
  \<open> Common_Base_Types T U V
\<Longrightarrow> Common_Base_Types (\<half_blkcirc> T) (\<black_circle> U) (\<half_blkcirc> V)\<close>
  unfolding Common_Base_Types_def
  by simp

lemma [\<phi>reason add]:
  \<open> Common_Base_Types T U V
\<Longrightarrow> Common_Base_Types (\<black_circle> T) (\<half_blkcirc> U) (\<half_blkcirc> V)\<close>
  unfolding Common_Base_Types_def
  by simp

(*TODO: improve simplification*)


(* TODO:
lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> Val _ _) (_ \<Ztypecolon> Val _ _) \<transforms> _ @tag br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<transforms> (z \<Ztypecolon> Z) @tag br_join
\<Longrightarrow> If P (x \<Ztypecolon> Val v T) (y \<Ztypecolon> Val v U) \<transforms> (z \<Ztypecolon> Val v Z) @tag br_join\<close>
  unfolding Action_Tag_def by (cases P; simp add: Val_transformation)

*)


(* TODO: fix me!!!
lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<black_circle> _) (_ \<Ztypecolon> \<circle>) \<transforms> _ @tag br_join\<close>]:
  \<open> x \<Ztypecolon> T \<transforms> x' \<Ztypecolon> Itself \<with> Any
\<Longrightarrow> If P (x \<Ztypecolon> \<black_circle> T) (y \<Ztypecolon> \<circle>) \<transforms> (If P (Some x') None \<Ztypecolon> Itself) @tag br_join\<close>
  unfolding Action_Tag_def     
  \<medium_left_bracket> premises T[\<phi>reason for action \<open>to Itself\<close>]  
    cases \<medium_left_bracket> to Itself \<medium_right_bracket>. \<medium_left_bracket> to Itself \<medium_right_bracket>. ;; \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<circle>) (_ \<Ztypecolon> \<black_circle> _) \<transforms> _ @tag br_join\<close>]:
  \<open> y \<Ztypecolon> T \<transforms> y' \<Ztypecolon> Itself \<with> Any
\<Longrightarrow> If P (x \<Ztypecolon> \<circle>) (y \<Ztypecolon> \<black_circle> T) \<transforms> (If P None (Some y') \<Ztypecolon> Itself) @tag br_join\<close>
  unfolding Action_Tag_def     
  \<medium_left_bracket> premises T[\<phi>reason for action \<open>to Itself\<close>]  
    cases \<medium_left_bracket> to Itself \<medium_right_bracket>. \<medium_left_bracket> to Itself \<medium_right_bracket>. ;; \<medium_right_bracket>. .
*)


subsubsection \<open>Unfold\<close>

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L (N * (R1 * R2)) \<transforms> X @tag br_join
\<Longrightarrow> If P L (N * R1 * R2) \<transforms> X @tag br_join"
  for N :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P (L1 * (L2 * L3)) R \<transforms> X @tag br_join
\<Longrightarrow> If P (L1 * L2 * L3) R \<transforms> X @tag br_join"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def by (metis mult.assoc)


subsubsection \<open>Eliminate Void Hole\<close>

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L R \<transforms> X @tag br_join
\<Longrightarrow> If P L (R * 1) \<transforms> X @tag br_join"
  for R :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L R \<transforms> X @tag br_join
\<Longrightarrow> If P L (1 * R) \<transforms> X @tag br_join"
  for R :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L (R' * R) \<transforms> X @tag br_join
\<Longrightarrow> If P L (R' * 1 * R) \<transforms> X @tag br_join"
  for R :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L R \<transforms> X @tag br_join
\<Longrightarrow> If P (L * 1) R \<transforms> X @tag br_join"
  for R :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L R \<transforms> X @tag br_join
\<Longrightarrow> If P (1 * L) R \<transforms> X @tag br_join"
  for R :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def by (cases P; simp)

(* TODO!!!

 subsection \<open>Program Interface\<close> \<comment> \<open>Interfaces exported to target LLVM module\<close>

definition Prog_Interface :: " label \<Rightarrow> 'a itself \<Rightarrow> 'b itself \<Rightarrow> ('a::lrep  \<longmapsto> 'b::lrep) \<Rightarrow> bool"
  where "Prog_Interface _ args rets proc \<longleftrightarrow> True"

lemma Prog_Interface_proc: "TERM proc \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) proc"
  unfolding Prog_Interface_def ..

lemma Prog_Interface_func:
  "TERM f \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) f"
  unfolding Prog_Interface_def ..
*)


section \<open>Implementation of Synthesis Mechanism\<close>

subsubsection \<open>Multi-Target\<close>


lemma [\<phi>reason %\<phi>synthesis_split+20]:
  \<open> \<proc> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. A ret \<remains> R2 \<rbrace> \<throws> E1 @tag synthesis
\<Longrightarrow> \<proc> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. B ret \<remains> R3 \<rbrace> \<throws> E2 @tag synthesis
\<Longrightarrow> \<proc> (f1 \<bind> (\<lambda>v1. f2 \<bind> (\<lambda>v2. Return (\<phi>V_pair v1 v2))))
         \<lbrace> R1 \<longmapsto> \<lambda>ret. A (\<phi>V_fst ret)\<heavy_comma> B (\<phi>V_snd ret) \<remains> R3 \<rbrace>
    \<throws> (\<lambda>e. E1 e + (E2 e\<heavy_comma> ExBI A)) @tag synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<open>A \<v>0\<close>
  \<medium_right_bracket> .

lemma [\<phi>reason %\<phi>synthesis_split]:
  \<open> \<proc> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. A ret \<remains> R2 \<rbrace> \<throws> E1 @tag synthesis
\<Longrightarrow> \<proc> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. B \<remains> R3 \<rbrace> \<throws> E2 @tag synthesis
\<Longrightarrow> \<proc> (f1 \<bind> (\<lambda>v. f2 \<then> Return v)) \<lbrace> R1 \<longmapsto> \<lambda>ret. A ret \<heavy_comma> B \<remains> R3 \<rbrace>
    \<throws> (\<lambda>e. E1 e + (ExBI A \<heavy_comma> E2 e)) @tag synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2
  \<medium_right_bracket> .

lemma [\<phi>reason %\<phi>synthesis_split+10]:
  \<open> \<proc> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. A \<remains> R2 \<rbrace> \<throws> E1 @tag synthesis
\<Longrightarrow> \<proc> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. B ret \<remains> R3 \<rbrace> \<throws> E2 @tag synthesis
\<Longrightarrow> \<proc> (f1 \<then> f2) \<lbrace> R1 \<longmapsto> \<lambda>ret. A \<heavy_comma> B ret \<remains> R3 \<rbrace>
    \<throws> (\<lambda>e. E1 e + (A \<heavy_comma> E2 e)) @tag synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2
  \<medium_right_bracket> .

lemma [\<phi>reason %\<phi>synthesis_split+20]:
  \<open> \<proc> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret::unit \<phi>arg. A \<remains> R2 \<rbrace> \<throws> E1 @tag synthesis
\<Longrightarrow> \<proc> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret::unit \<phi>arg. B \<remains> R3 \<rbrace> \<throws> E2 @tag synthesis
\<Longrightarrow> \<proc> (f1 \<then> f2) \<lbrace> R1 \<longmapsto> \<lambda>ret. A \<heavy_comma> B \<remains> R3 \<rbrace>
    \<throws> (\<lambda>e. E1 e + (A \<heavy_comma> E2 e)) @tag synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2
  \<medium_right_bracket> .

(*
subsection \<open>Infer the binding pattern\<close>

definition Infer_Binding_Pattern :: \<open>'c::{} \<Rightarrow> 'a::{} \<Rightarrow> 'b::{} \<Rightarrow> prop\<close>
  where \<open>Infer_Binding_Pattern X GIVEN_PATTERN RESULTED_PATTERN \<equiv> TERM RESULTED_PATTERN\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP Infer_Binding_Pattern ?X ?G _\<close> \<Rightarrow> \<open>PROP Infer_Binding_Pattern ?X ?G _\<close> (100)
]]

lemma infer_binding_pattern:
  \<open> PROP Infer_Binding_Pattern RULE GIVEN_PATTERN RESULTED_PATTERN
\<Longrightarrow> TERM RESULTED_PATTERN\<close> .

consts morphism_syntax :: \<open>'a::{} \<Rightarrow> 'b::{} \<Rightarrow> 'c::{}\<close>
consts comma_syntax :: \<open>'a::{} \<Rightarrow> 'b::{} \<Rightarrow> 'c::{}\<close>

lemma [\<phi>reason 2000]:
  \<open> PROP Infer_Binding_Pattern B G Y
\<Longrightarrow> PROP Infer_Binding_Pattern (PROP A \<Longrightarrow> PROP B) G Y\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 2000]:
  \<open> (\<And>x. PROP Infer_Binding_Pattern (X x) G Y)
\<Longrightarrow> PROP Infer_Binding_Pattern (\<And>x. PROP X x) G Y\<close>
  unfolding Infer_Binding_Pattern_def .

definition syntax_prepend_speration :: \<open>'a::{} \<Rightarrow> 'b::{} \<Rightarrow> 'c::{} \<Rightarrow> prop\<close>
  where \<open> syntax_prepend_speration A B C \<equiv> TERM C\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP syntax_prepend_speration ?A ?B _\<close> \<Rightarrow> \<open>PROP syntax_prepend_speration ?A ?B _\<close> (100)
]]

lemma [\<phi>reason 1000]:
  \<open> PROP syntax_prepend_speration A B (A * B)\<close>
  unfolding syntax_prepend_speration_def .

lemma [\<phi>reason 1100]:
  \<open> PROP syntax_prepend_speration A B C
\<Longrightarrow> PROP syntax_prepend_speration A (B * D) (C * D)\<close>
  unfolding syntax_prepend_speration_def .

*)

section \<open>Generation of Synthesis Rule\<close>

definition Gen_Synthesis_Rule :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>Gen_Synthesis_Rule Given Antecedents Result
            \<equiv> ((PROP Antecedents \<Longrightarrow> PROP Given) \<Longrightarrow> PROP Result)\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP Gen_Synthesis_Rule ?G ?A _\<close> \<Rightarrow> \<open>PROP Gen_Synthesis_Rule ?G ?A _\<close> (100)
]]


lemma Gen_Synthesis_Rule:
  \<open> PROP G
\<Longrightarrow> PROP Gen_Synthesis_Rule G PURE_TOP R
\<Longrightarrow> \<r>Success
\<Longrightarrow> PROP R\<close>
  unfolding Gen_Synthesis_Rule_def PURE_TOP_imp .

ML_file \<open>library/additions/gen_synthesis_rule.ML\<close>

subsubsection \<open>Conventions\<close>

declare [[generate_pattern_of_synthesis_rule
      \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R \<rbrace> \<throws> _ @tag ?\<A> &&& TERM ()\<close> \<Rightarrow>
      \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R' \<rbrace> \<throws> _ @tag ?\<A>\<close>    (120)
  and \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. _ \<remains> ?R \<rbrace> \<throws> _ @tag ?\<A> &&& TERM ?Z\<close> \<Rightarrow>
      \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R' \<rbrace> \<throws> _ @tag ?\<A>\<close>    (110)
  and \<open>\<proc> _ \<lbrace> _  \<longmapsto> \<lambda>ret. _ \<remains> ?R \<rbrace> \<throws> _ @tag ?\<A> &&& (TERM ?X &&& TERM ?Z)\<close> \<Rightarrow>
      \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R' \<rbrace> \<throws> _ @tag ?\<A>\<close>    (110)
  and \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?x \<Ztypecolon> _ \<remains> ?R \<rbrace> \<throws> _ @tag ?\<A> &&& TERM ()\<close> \<Rightarrow>
      \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?x \<Ztypecolon> _ \<remains> ?R' \<rbrace> \<throws> _ @tag ?\<A>\<close>    (125)
  and \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. _ \<Ztypecolon> _ \<remains> ?R \<rbrace> \<throws> _ @tag ?\<A> &&& TERM ?z\<close> \<Rightarrow>
      \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?z \<Ztypecolon> _ \<remains> ?R' \<rbrace> \<throws> _ @tag ?\<A>\<close>    (106)
  and \<open>(?X::assn) \<transforms> ?Z \<remains> _ \<with> _ @tag ?\<A> &&& TERM ()\<close> \<Rightarrow>
      \<open>?X \<transforms> ?Z \<remains> _ \<with> _ @tag ?\<A>\<close>    (120)
  and \<open>(?X::assn) \<transforms> _ \<remains> _ \<with> _ @tag ?\<A> &&& TERM ?Z\<close> \<Rightarrow>
      \<open>?X \<transforms> ?Z \<remains> _ \<with> _ @tag ?\<A>\<close>    (110)
  and \<open> _ \<transforms> _ \<remains> _ \<with> _ @tag ?\<A> &&& (TERM ?X &&& TERM ?Z)\<close> \<Rightarrow>
      \<open>(?X::assn) \<transforms> ?Z \<remains> _ \<with> _ @tag ?\<A>\<close>    (110)
  and \<open>(?X::assn) \<transforms> ?x \<Ztypecolon> _ \<remains> _ \<with> _ @tag ?\<A> &&& TERM ()\<close> \<Rightarrow>
      \<open>?X \<transforms> ?x \<Ztypecolon> _ \<remains> _ \<with> _ @tag ?\<A>\<close>    (125)
  and \<open>(?X::assn) \<transforms> _ \<Ztypecolon> _ \<remains> _ \<with> _ @tag ?\<A> &&& TERM ?z\<close> \<Rightarrow>
      \<open>?X \<transforms> ?z \<Ztypecolon> _ \<remains> _ \<with> _ @tag ?\<A>\<close>    (106)
]]

\<phi>reasoner_group \<phi>synthesis_gen = (1000, [1, 3000]) for \<open>PROP Gen_Synthesis_Rule (PROP _) (PROP _) (PROP _)\<close>
    \<open>All rules describing how to convert a given lemma to a synthesis rule\<close>
  and \<phi>synthesis_gen_hhf = (1000, [1000, 1000]) in \<phi>synthesis_gen
    \<open>handling meta structure of the given lemma as a HHF rule, though actually only meta imp
     is considered because no meta all should occur in a normalized HHF rule.\<close>
  and \<phi>synthesis_gen_ToA = (1000, [10,3000]) in \<phi>synthesis_gen
    \<open>when the given lemma is a ToA\<close>
  and \<phi>synthesis_gen_proc = (1000, [10,3000]) in \<phi>synthesis_gen
    \<open>when the given lemma is a procedure\<close>

(*
lemma [\<phi>reason 2000]:
  \<open> PROP Infer_Binding_Pattern
      (\<proc> f  \<lbrace> X \<longmapsto> \<lambda>ret. R  \<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> \<throws> E  @tag synthesis)
      ()
      (\<proc> f' \<lbrace> X \<longmapsto> \<lambda>ret. R' \<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> \<throws> E' @tag synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1050]:
  \<open> PROP Infer_Binding_Pattern
      (\<proc> f  \<lbrace> X \<longmapsto> \<lambda>ret. R  \<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> \<throws> E  @tag synthesis)
      Z'
      (\<proc> f' \<lbrace> X \<longmapsto> \<lambda>ret. R' \<heavy_comma> \<blangle> Z' ret \<brangle> \<rbrace> \<throws> E' @tag synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .
*)

attribute_setup \<phi>synthesis = \<open>
  let val arrow = (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
      fun named_term2 read =
            Args.internal_term --| arrow -- Args.internal_term ||
            Parse.token Parse.embedded --| arrow -- Parse.token Parse.embedded
              >> (fn (tok1, tok2) =>
                  let val [term1, term2] = read [Token.inner_syntax_of tok1, Token.inner_syntax_of tok2]
                   in Token.assign (SOME (Token.Term term1)) tok1 ;
                      Token.assign (SOME (Token.Term term2)) tok2 ;
                      (term1, term2)
                  end)

      val pattern = Scan.peek (fn ctxt =>
        let val ctxt' = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of ctxt)
            fun read_term raw =
              let val raw1 = map (Syntax.parse_term ctxt') raw
                  fun chk tagged [] = Syntax.check_terms ctxt' tagged
                    | chk tagged (X::L) =
                            (chk (Type.constraint \<^typ>\<open>_::type \<phi>arg \<Rightarrow> assn\<close> X :: tagged) L
                             handle ERROR err =>
                             chk (Type.constraint \<^typ>\<open>assn\<close> X :: tagged) L
                             handle ERROR _ => raise (ERROR err))
                  val terms = chk [] (rev raw1)
                  val ctxt'' = fold Proof_Context.augment terms ctxt'
                  val terms' = Variable.export_terms ctxt'' ctxt' terms
               in terms' end
         in (Args.$$$ "_"  >> (K Phi_Synthesis.No_Pattern))
         || named_term2 read_term >> Phi_Synthesis.Arg_and_Ret
         || (Args.named_term (singleton read_term) >> Phi_Synthesis.Ret_only)
        end )
      val priority = Scan.lift (Scan.option (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>))
      val pat2 = (Scan.optional (Scan.lift \<^keyword>\<open>for\<close> |-- Parse.and_list1' (pattern -- priority)) [] --
                  Scan.optional (Scan.lift \<^keyword>\<open>except\<close> |-- Parse.and_list1' pattern) [] )
   in Phi_Reasoner.attr_syntax' pat2
      (fn (pos, mode, group, raw_pats) =>
        Thm.declaration_attribute (fn rule => fn ctxt =>
          let val pats = apfst (map (apsnd (Option.map (fst o Reasoner_Group.check_group true ctxt)))) raw_pats
           in Phi_Synthesis.declare_rule pos (mode, SOME (the_default @{reasoner_group %\<phi>synthesis} group))
                                         pats rule ctxt
          end))
  end
\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<proc> _ \<lbrace> ?X \<remains> _ \<longmapsto> ?Y \<rbrace> \<throws> _))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<proc> _ \<lbrace> ?X \<remains> _ \<longmapsto> ?Y \<rbrace> \<throws> _))
            (PROP ?P) (PROP _)\<close>  (120)
  and \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<proc> _ \<lbrace> ?X \<remains> _ \<longmapsto> \<lambda>r. ?Y r \<remains> ?RN   \<rbrace> \<throws> _))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<proc> _ \<lbrace> ?X \<remains> _ \<longmapsto> \<lambda>r. ?Y r \<remains> ?RN'' \<rbrace> \<throws> _))
            (PROP ?P) (PROP _)\<close>  (125)
  and \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<proc> ?f  v \<lbrace> ?X v \<remains> ?R  \<longmapsto> ?Y \<rbrace> \<throws> ?E))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<proc> ?f' v \<lbrace> ?X v \<remains> ?R' \<longmapsto> ?Y \<rbrace> \<throws> ?E'))
            (PROP ?P) (PROP _)\<close>  (120)
  and \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<proc> ?f  v \<lbrace> ?X  v \<remains> ?R  \<longmapsto> \<lambda>r. ?Y r \<remains> ?RN   \<rbrace> \<throws> _))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<proc> ?f' v \<lbrace> ?X' v \<remains> ?R' \<longmapsto> \<lambda>r. ?Y r \<remains> ?RN'' \<rbrace> \<throws> _))
            (PROP ?P) (PROP _)\<close>  (125)
]]

subsection \<open>General Rule\<close>

lemma [\<phi>reason %\<phi>synthesis_gen_hhf]:
  \<open> PROP Gen_Synthesis_Rule Q (PROP Ant &&& PROP P) X
\<Longrightarrow> PROP Gen_Synthesis_Rule (PROP P \<Longrightarrow> PROP Q) Ant X\<close>
  unfolding Gen_Synthesis_Rule_def conjunction_imp
  subgoal premises P by (rule P(1), rule P(2), assumption, assumption) .


subsection \<open>Synthesis Mode\<close>

definition synthesis_gen_mode :: \<open>'c BI \<Rightarrow> action \<Rightarrow> bool\<close>
  where \<open>synthesis_gen_mode Assertion Mode \<equiv> True\<close>

declare [[\<phi>reason_default_pattern \<open>synthesis_gen_mode ?A _\<close> \<Rightarrow> \<open>synthesis_gen_mode ?A _\<close> (100)]]

\<phi>reasoner_group synthesis_gen_mode_all = (1000, [10,2000]) for \<open>synthesis_gen_mode A M\<close>
    \<open>determines whether the rule to be generated is in normal mode or overloaded mode\<close>
 and synthesis_gen_mode_default = (10,[10,10]) in synthesis_gen_mode_all
    \<open>the default is normal mode\<close>
 and synthesis_gen_mode_overridded = (1000, [1000,1000]) in synthesis_gen_mode_all > synthesis_gen_mode_default \<open>\<close>
 and synthesis_gen_mode_pass = (1200, [1200, 1200]) in synthesis_gen_mode_all and > synthesis_gen_mode_overridded \<open>\<close>

lemma [\<phi>reason default %synthesis_gen_mode_default]:
  \<open> synthesis_gen_mode A synthesis \<close>
  unfolding synthesis_gen_mode_def ..

paragraph \<open>Passes\<close>

lemma [\<phi>reason %synthesis_gen_mode_pass]:
  \<open> synthesis_gen_mode A M
\<Longrightarrow> synthesis_gen_mode (A \<remains> R) M \<close>
  unfolding synthesis_gen_mode_def REMAINS_def ..

subsection \<open>ToA\<close>

\<phi>reasoner_group \<phi>synthesis_gen_ToA_default = (10, [10,10]) in \<phi>synthesis_gen_ToA \<open>\<close>
  and \<phi>synthesis_gen_ToA_convert = (50, [11,80]) in \<phi>synthesis_gen_ToA
    \<open>Synthesis ToA rules must be on fiction algebra. The group tries to convert ToAs that are not
      on the fiction algebra.\<close>

subsubsection \<open>Conversion\<close>

lemma [\<phi>reason default %\<phi>synthesis_gen_ToA_convert]:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (x \<Ztypecolon> \<val>[v] T \<transforms> (y \<Ztypecolon> \<val>[v] U :: assn) \<with> P))
      Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<with> P))
      Ant Result \<close>
  unfolding Gen_Synthesis_Rule_def Transformation_def
  by clarsimp

subsubsection \<open>Success\<close>

lemma Gen_Synthesis_Rule_transformation_12:
  \<open> synthesis_gen_mode Y mode
\<Longrightarrow> \<simplify>[assertion_simps SOURCE] X' : X  * R
\<Longrightarrow> \<simplify>[assertion_simps TARGET] Y' : Yr * R
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (X \<transforms> Y * Yr \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X' \<transforms> Y \<remains> Y' \<with> P @tag mode) \<close>
  for X :: assn
  unfolding Gen_Synthesis_Rule_def Action_Tag_def Simplify_def REMAINS_def
  by (simp; rule transformation_right_frame[where U=\<open>Y * Yr\<close>, simplified mult.assoc]; simp)

lemma Gen_Synthesis_Rule_transformation_11:
  \<open> synthesis_gen_mode Y mode
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (X \<transforms> Y \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X * R \<transforms> Y \<remains> R \<with> P @tag mode) \<close>
  for X :: assn
  unfolding Gen_Synthesis_Rule_def Action_Tag_def REMAINS_def
  by (rule transformation_right_frame, simp)

lemma Gen_Synthesis_Rule_transformation_01:
  \<open> synthesis_gen_mode Y mode
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (X \<transforms> Y * R \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X \<transforms> Y \<remains> R \<with> P @tag mode) \<close>
  for X :: assn
  unfolding Gen_Synthesis_Rule_def Action_Tag_def REMAINS_def
  by simp

lemma Gen_Synthesis_Rule_transformation_00:
  \<open> synthesis_gen_mode Y mode
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (X \<transforms> Y \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X \<transforms> Y \<with> P @tag mode) \<close>
  for X :: assn
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by simp


\<phi>reasoner_ML Gen_Synthesis_Rule_transformation %\<phi>synthesis_gen_ToA_default
    (\<open>PROP Gen_Synthesis_Rule (Trueprop ((_::assn) \<transforms> _ \<with> _)) (PROP _) (PROP _)\<close>)
  = \<open>fn (_,(ctxt,sequent)) => Seq.make (fn () =>
    let val _ (*Gen_Synthesis_Rule*) $ (_ (*Trueprop*) $ TM) $ _ $ _ = Thm.major_prem_of sequent
        fun last_ele (Const (\<^const_name>\<open>times\<close>, _) $ _ $ X ) = last_ele X
          | last_ele X = X
        fun first_ele (Const (\<^const_name>\<open>times\<close>, _) $ X $ _ ) = first_ele X
          | first_ele X = X
        val (has_R,X,Y) =
          case TM
            of Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ _ => (last_ele X = last_ele Y,X,Y)
             | Const(\<^const_name>\<open>View_Shift\<close>, _) $ X $ Y $ _ => (last_ele X = last_ele Y,X,Y)

       fun warn () = warning "You have multiple separated items and it is unclear which one is \
                     \the target to be synthesised or the residue of the synthesis.\n\
                     \We assume the synthesis target is the first item.\n\
                     \You should use \<open> Target \<remains> Residue \<close> to annotate the target."
        fun chk_target (Abs (_,_,tm)) = chk_target tm
          | chk_target (Const (\<^const_name>\<open>ExBI\<close>, _) $ _)
              = error ("Exisential quantification has not been supported in synthesis.")
          | chk_target (Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _)
              = Phi_Reasoner.bad_config "Subjection shouldn't occur here."
          | chk_target (Const (\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _)
              = @{thm' Gen_Synthesis_Rule_transformation_00} RS sequent
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _) $ _)
              = (warn () ;
                 if has_R then @{thm' Gen_Synthesis_Rule_transformation_01} RS sequent
                          else @{thm' Gen_Synthesis_Rule_transformation_12} RS sequent)
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _)
              = if has_R then @{thm' Gen_Synthesis_Rule_transformation_01} RS sequent
                         else (warn (); @{thm' Gen_Synthesis_Rule_transformation_12} RS sequent)
          | chk_target _ = @{thm Gen_Synthesis_Rule_transformation_11} RS sequent
    in case X of Const (\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _ => NONE
          | _ => SOME ((ctxt, chk_target Y), Seq.empty)
    end)\<close>


subsection \<open>View Shift\<close>

lemma Gen_Synthesis_Rule_VS_12:
  \<open> synthesis_gen_mode Y mode
\<Longrightarrow> \<simplify>[assertion_simps SOURCE] X' : X  * R
\<Longrightarrow> \<simplify>[assertion_simps TARGET] Y' : Yr * R
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (X \<shifts> Y * Yr \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X' \<shifts> Y \<remains> Y' \<with> P @tag mode) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def Simplify_def REMAINS_def
  by (simp; rule \<phi>view_shift_intro_frame[where U=\<open>Y * Yr\<close>, unfolded mult.assoc]; simp)

lemma Gen_Synthesis_Rule_VS_11:
  \<open> synthesis_gen_mode Y mode
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (X \<shifts> Y \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X * R \<shifts> Y \<remains> R \<with> P @tag mode) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def REMAINS_def
  by (rule \<phi>view_shift_intro_frame, simp)

lemma Gen_Synthesis_Rule_VS_01:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<shifts> Y * R \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X \<shifts> Y \<remains> R \<with> P @tag synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def REMAINS_def
  by simp

lemma Gen_Synthesis_Rule_VS_00:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<shifts> Y \<with> P))
      Ant
      (PROP Ant \<Longrightarrow> X \<shifts> Y \<with> P @tag synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by simp


\<phi>reasoner_ML Gen_Synthesis_Rule_VS 10
    (\<open>PROP Gen_Synthesis_Rule (Trueprop (_ \<shifts> _ \<with> _)) (PROP _) (PROP _)\<close>)
  = \<open>fn (_,(ctxt,sequent)) => Seq.make (fn () =>
    let val _ (*Gen_Synthesis_Rule*) $ (_ (*Trueprop*) $ TM) $ _ $ _ = Thm.major_prem_of sequent
        fun last_ele (Const (\<^const_name>\<open>times\<close>, _) $ _ $ X ) = last_ele X
          | last_ele X = X
        val (has_R,X,Y) =
          case TM
            of Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ _ => (last_ele X = last_ele Y,X,Y)
             | Const(\<^const_name>\<open>View_Shift\<close>, _) $ X $ Y $ _ => (last_ele X = last_ele Y,X,Y)

       fun warn () = warning "You have multiple separated items and it is unclear which one is \
                     \the target to be synthesised or the residue of the synthesis.\n\
                     \We assume the synthesis target is the last item.\n\
                     \You should use \<open> Target \<remains> Residue \<close> to annotate the target."
        fun chk_target (Abs (_,_,tm)) = chk_target tm
          | chk_target (Const (\<^const_name>\<open>ExBI\<close>, _) $ _)
              = error ("Exisential quantification has not been supported in synthesis.")
          | chk_target (Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _)
              = Phi_Reasoner.bad_config "Subjection shouldn't occur here."
          | chk_target (Const (\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _)
              = @{thm' Gen_Synthesis_Rule_VS_00} RS sequent
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _) $ _)
              = (warn () ;
                 if has_R then @{thm' Gen_Synthesis_Rule_VS_01} RS sequent
                          else @{thm' Gen_Synthesis_Rule_VS_12} RS sequent)
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _)
              = if has_R then @{thm' Gen_Synthesis_Rule_VS_01} RS sequent
                         else (warn (); @{thm' Gen_Synthesis_Rule_VS_12} RS sequent)
          | chk_target _ = @{thm Gen_Synthesis_Rule_VS_11} RS sequent
    in case X of Const (\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _ => NONE
          | _ => SOME ((ctxt, chk_target Y), Seq.empty)
    end)\<close>



subsection \<open>Procedure Application - General Methods\<close>

\<phi>reasoner_group \<phi>synthesis_gen_proc_cut = (1200, [1200, 1300]) in \<phi>synthesis_gen_proc
      \<open>cutting rules\<close>
  and \<phi>synthesis_gen_proc_normalize = (2000, [2000, 2100])
      in \<phi>synthesis_gen_proc and > \<phi>synthesis_gen_proc_cut
      \<open>normalizing rules\<close>
  and \<phi>synthesis_gen_proc_init = (10, [10, 10]) in \<phi>synthesis_gen_proc and < \<phi>synthesis_gen_proc_cut
      \<open>initiating reasoning\<close>
  and \<phi>synthesis_gen_by_overloading = (2500, [2500,2510]) in \<phi>synthesis_gen_proc and > \<phi>synthesis_gen_proc_normalize \<open>\<close>


lemma [\<phi>reason %\<phi>synthesis_gen_proc_cut for \<open>PROP Gen_Synthesis_Rule
      (Trueprop (\<forall>v. \<proc> _ \<lbrace> ?X v\<heavy_comma> _ \<remains> ?R \<longmapsto> ?Y \<rbrace> \<throws> ?E )) _ _\<close>]:
  \<comment> \<open>Gen_Synthesis_Rule_step_value\<close>
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> (f \<bind> (\<lambda>v. F (\<phi>V_pair v vs)))
                                 \<lbrace> Xr vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> (\<lambda>e. (E1 e\<heavy_comma> ExBI Xr) + EF e)))
            ((\<proc> f \<lbrace> R \<longmapsto> \<lambda>ret. X ret \<remains> R1 \<rbrace> \<throws> E1 @tag synthesis) &&& PROP Ant)
            Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X (\<phi>V_fst vs)\<heavy_comma> Xr (\<phi>V_snd vs) \<remains> R1 \<longmapsto> Y \<rbrace> \<throws> EF))
            Ant Result \<close>
  unfolding Gen_Synthesis_Rule_def conjunction_imp REMAINS_def
  subgoal premises prems apply (rule prems(1))
  \<medium_left_bracket> premises f and A
    f
    apply_rule prems(2)[OF A]
  \<medium_right_bracket>. .

lemma [\<phi>reason %\<phi>synthesis_gen_proc_cut]: \<comment> \<open>Gen_Synthesis_Rule_step_value the last\<close>
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>_::unit \<phi>arg. \<proc> (f \<bind> F) \<lbrace> Xr \<remains> R \<longmapsto> Y \<rbrace> \<throws> (\<lambda>e. (E1 e\<heavy_comma> Xr) + EF e)))
            (\<proc> f \<lbrace> R \<longmapsto> \<lambda>ret. X ret \<remains> R1 \<rbrace> \<throws> E1 @tag synthesis &&& PROP Ant)
            Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<proc> F v \<lbrace> X v\<heavy_comma> Xr \<remains> R1 \<longmapsto> Y \<rbrace> \<throws> EF))
            Ant Result \<close>
  unfolding Gen_Synthesis_Rule_def conjunction_imp
  subgoal premises prems apply (rule prems(1))
  \<medium_left_bracket> premises f and A
    f
    apply_rule prems(2)[OF A]
  \<medium_right_bracket> . .

lemma [\<phi>reason %\<phi>synthesis_gen_proc_cut]: \<comment> \<open>Gen_Synthesis_Rule final\<close>
  \<open> (\<And>e. Remove_Values (E e) (E' e))
\<Longrightarrow> Simplify (assertion_simps ABNORMAL) E'' E'
\<Longrightarrow> PROP Gen_Synthesis_Rule
      (Trueprop (\<forall>_::unit \<phi>arg. \<proc> F \<lbrace> Void \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
      Ant
      (PROP Ant \<Longrightarrow> \<proc> F \<lbrace> R \<longmapsto> Y \<rbrace> \<throws> E'' @tag synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Remove_Values_def Simplify_def Action_Tag_def REMAINS_def
  subgoal premises P
    apply (unfold P(2))
    using P(3)[OF P(4), THEN spec, THEN \<phi>CONSEQ'E[OF view_shift_by_implication, OF P(1)],
            simplified] . .

lemma [\<phi>reason %\<phi>synthesis_gen_proc_cut+10]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<proc> (f \<then> F v) \<lbrace> Xr v \<remains> R \<longmapsto> Y \<rbrace> \<throws> (\<lambda>e. (E1 e\<heavy_comma> ExBI Xr) + EF e)))
            (\<proc> f \<lbrace> R \<longmapsto> X \<remains> R1 \<rbrace> \<throws> E1 @tag synthesis &&& PROP Ant)
            Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<proc> F v \<lbrace> X\<heavy_comma> Xr v \<remains> R1 \<longmapsto> Y \<rbrace> \<throws> EF))
            Ant Result \<close>
  unfolding Gen_Synthesis_Rule_def conjunction_imp
  subgoal premises prems apply (rule prems(1))
    \<medium_left_bracket> premises f and A
      f
      apply_rule prems(2)[OF A]
    \<medium_right_bracket> . .


lemma [\<phi>reason %\<phi>synthesis_gen_proc_normalize]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> Rx vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> Void\<heavy_comma> Rx vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def by simp

lemma [\<phi>reason %\<phi>synthesis_gen_proc_normalize]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs\<heavy_comma> Rx vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> (X vs \<remains> Rx vs) \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def REMAINS_def by simp

(* TODO: SMORPH
lemma [\<phi>reason 2000]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F \<lbrace> Rx vs\<heavy_comma> X vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F \<lbrace> Rx vs\<heavy_comma> SMORPH X vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def by simp
*)

lemma [\<phi>reason %\<phi>synthesis_gen_proc_normalize]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> A vs\<heavy_comma> B vs\<heavy_comma> Rx vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> (A vs\<heavy_comma> B vs)\<heavy_comma> Rx vs \<remains> R \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def by (simp add: mult.assoc)


subsection \<open>Entry Point\<close>

context begin

private lemma Gen_Synthesis_Rule_start_proc:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs\<heavy_comma> Void \<remains> R \<longmapsto> \<lambda>ret. Y ret \<remains> R \<rbrace> \<throws> (\<lambda>e. E e\<heavy_comma> R)))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def REMAINS_def
  by (simp add: \<phi>frame)

private lemma Gen_Synthesis_Rule_start_proc_focus_the_last:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs\<heavy_comma> Void \<remains> R \<longmapsto> \<lambda>ret. Y ret \<remains> Yr ret\<heavy_comma> R \<rbrace> \<throws> (\<lambda>e. E e\<heavy_comma> R )))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> Yr ret \<rbrace> \<throws> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def REMAINS_def
  by (simp add: \<phi>frame mult.assoc[symmetric])

private lemma Gen_Synthesis_Rule_start_proc_having_target:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs\<heavy_comma> Void \<remains> R \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> R \<rbrace> \<throws> (\<lambda>e. E e\<heavy_comma> R )))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<throws> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def REMAINS_def
  by (simp add: \<phi>frame)

\<phi>reasoner_ML Gen_Synthesis_Rule_init_for_proc %\<phi>synthesis_gen_proc_init
    (\<open>PROP Gen_Synthesis_Rule (Trueprop (\<forall>vs. \<proc> _ \<lbrace> _ \<longmapsto> ?Y \<rbrace> \<throws> ?E)) (PROP _) (PROP _)\<close>)
  = \<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
    let fun dest_proc (Const (\<^const_name>\<open>Gen_Synthesis_Rule\<close>, _) $ tm $ _ $ _) = dest_proc tm
          | dest_proc (Const (\<^const_name>\<open>Trueprop\<close>, _) $ tm) = dest_proc tm
          | dest_proc (Const (\<^const_name>\<open>All\<close>, _) $ tm) = dest_proc tm
          | dest_proc (Abs (_,_,tm)) = dest_proc tm
          | dest_proc tm = Phi_Syntax.dest_procedure tm
        val (_,X,Y,_) = dest_proc (Thm.major_prem_of sequent)
        fun chk_target (Abs (_,_,tm)) = chk_target tm
          | chk_target (Const (\<^const_name>\<open>ExBI\<close>, _) $ _)
              = error ("Exisential quantification has not been supported in synthesis.")
          | chk_target (Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _)
              = Phi_Reasoner.bad_config "Subjection shouldn't occur here."
          | chk_target (Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _)
              = @{thm Gen_Synthesis_Rule_start_proc_having_target}
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _)
              = (warning "You have multiple separated items and it is unclear which one is \
                     \the target to be synthesised or the residue of the synthesis.\n\
                     \We assume the synthesis target is the last item.\n\
                     \You should use \<open> Residue \<heavy_comma> \<blangle> Target \<brangle> \<close> to annotate the target, \
                     \or \<open> \<blangle> Target \<brangle> \<close> if there is no residue.";
                 @{thm Gen_Synthesis_Rule_start_proc_focus_the_last})
          | chk_target _ = @{thm Gen_Synthesis_Rule_start_proc}
     in case X
          of Const (\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _ => NONE
           | _ => SOME ((ctxt, (chk_target Y) RS sequent), Seq.empty)
    end)\<close>

end

lemma [\<phi>reason %\<phi>synthesis_gen_proc_cut]:
  \<open> WARNING TEXT(\<open>Pure fact\<close> P \<open>will be discarded during the synthesis.\<close>)
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<proc> F \<lbrace> X \<longmapsto> Y \<rbrace> \<throws> E)) Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<proc> F \<lbrace> X \<longmapsto> \<lambda>v. Y v \<subj> P v \<rbrace> \<throws> E)) Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def
  subgoal premises prems apply (rule prems(2))
    \<medium_left_bracket> premises Ant
      apply_rule prems(3)[OF Ant]
    \<medium_right_bracket> . .

subsection \<open>Tools\<close>

lemma make_synthesis_rule:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. E e\<heavy_comma> R)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<throws> E))
          Ant
          ((\<And>vs. X' vs \<transforms> X vs \<remains> R \<with> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<proc> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. Y ret \<remains> R \<rbrace> \<throws> E'
           @tag synthesis)\<close>
  unfolding Gen_Synthesis_Rule_def
  \<medium_left_bracket> premises E[assertion_simps] and F and X and A
    X
    apply_rule F[OF A]
  \<medium_right_bracket> .

lemma make_synthesis_rule':
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. E e\<heavy_comma> R')
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. Y ret \<remains> R \<rbrace> \<throws> E))
          Ant
          ((\<And>vs. X' vs \<transforms> X vs \<remains> R' \<with> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<proc> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. Y ret \<remains> R\<heavy_comma> R' \<rbrace> \<throws> E'
           @tag synthesis)\<close>
  unfolding REMAINS_def
  using make_synthesis_rule[unfolded REMAINS_def, where Y = \<open>\<lambda>v. Y v\<heavy_comma> R\<close>, unfolded mult.assoc] .




subsection \<open>Overloaded Synthesis\<close>

consts overloaded_synthesis :: action

lemma synthesis_gen_mode_overloaded_I:
  \<open> synthesis_gen_mode A overloaded_synthesis \<close>
  unfolding synthesis_gen_mode_def ..

subsubsection \<open>Conventions\<close>

declare [[\<phi>reason_default_pattern
      \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?x \<Ztypecolon> ?Y  ret \<remains> ?R  \<rbrace> \<throws> ?E  @tag overloaded_synthesis\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?x \<Ztypecolon> ?Y' ret \<remains> ?R' \<rbrace> \<throws> ?E' @tag overloaded_synthesis\<close> (100)
  and \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?Y ret \<remains> ?R  \<rbrace> \<throws> ?E  @tag overloaded_synthesis\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?Y ret \<remains> ?R' \<rbrace> \<throws> ?E' @tag overloaded_synthesis\<close> (90)

  and \<open>(?A::assn) \<transforms> ?X \<remains> _ \<with> _ @tag overloaded_synthesis\<close>
   \<Rightarrow> \<open>(?A::assn) \<transforms> ?X \<remains> _ \<with> _ @tag overloaded_synthesis\<close> (100)
  and \<open>(?A::assn) \<shifts> ?X \<remains> _ \<with> _ @tag overloaded_synthesis\<close>
   \<Rightarrow> \<open>(?A::assn) \<shifts> ?X \<remains> _ \<with> _ @tag overloaded_synthesis\<close> (100)

  and \<open>?X @tag overloaded_synthesis\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Bad form of overloaded synthesis\<close> ?X)\<close> (0),


   generate_pattern_of_synthesis_rule
      \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R  \<rbrace> \<throws> _ @tag overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R' \<rbrace> \<throws> _ @tag overloaded_synthesis\<close>  (110)
  and \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R  \<rbrace> \<throws> _ @tag overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Z ret \<remains> ?R' \<rbrace> \<throws> _ @tag overloaded_synthesis\<close>  (110)
  and \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?x \<Ztypecolon> _ \<remains> ?R  \<rbrace> \<throws> _ @tag overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<proc> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?x \<Ztypecolon> _ \<remains> ?R' \<rbrace> \<throws> _ @tag overloaded_synthesis\<close>  (120)
  and \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?x \<Ztypecolon> _ \<remains> ?R  \<rbrace> \<throws> _ @tag overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?x \<Ztypecolon> _ \<remains> ?R' \<rbrace> \<throws> _ @tag overloaded_synthesis\<close>  (120)
  and \<open>\<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<remains> ?R  \<rbrace> \<throws> ?E  @tag overloaded_synthesis &&& TERM ?Y'\<close>
   \<Rightarrow> \<open>\<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y' ret \<remains> ?R' \<rbrace> \<throws> ?E' @tag overloaded_synthesis\<close> (110)
  and \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<remains> ?R  \<rbrace> \<throws> ?E  @tag overloaded_synthesis &&& TERM ?Y'\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y' ret \<remains> ?R' \<rbrace> \<throws> ?E' @tag overloaded_synthesis\<close> (110)
  and \<open>\<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<remains> ?R  \<rbrace> \<throws> ?E  @tag overloaded_synthesis &&& (TERM ?X' &&& TERM ?Y')\<close>
   \<Rightarrow> \<open>\<proc> _ \<lbrace> ?X' \<longmapsto> \<lambda>ret. ?Y' ret \<remains> ?R' \<rbrace> \<throws> ?E' @tag overloaded_synthesis\<close> (110)
  and \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<remains> ?R  \<rbrace> \<throws> ?E  @tag overloaded_synthesis &&& (TERM ?X' &&& TERM ?Y')\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<proc> _ \<lbrace> ?X' vs \<longmapsto> \<lambda>ret. ?Y' ret \<remains> ?R' \<rbrace> \<throws> ?E' @tag overloaded_synthesis\<close> (110)
]]

\<phi>reasoner_group \<phi>overloaded_synthesis_all = (100, [10, 3000]) for \<open>\<proc> f \<lbrace> X \<longmapsto> Y \<rbrace> \<throws> E @tag overloaded_synthesis\<close>
    \<open>Synthesizes an overloaded given operator\<close>
  and \<phi>overloaded_synthesis = (100, [100,100]) in \<phi>overloaded_synthesis_all
    \<open>the default reasoner group\<close>
  and \<phi>overloaded_synthesis_fallback = (10, [10,10]) in \<phi>overloaded_synthesis_all
    \<open>fallbacks\<close>


consts synthesis_pattern1 :: \<open>'ret::{} \<Rightarrow> 'any::{}\<close>
consts synthesis_pattern2 :: \<open>'arg::{} \<Rightarrow> 'ret::{} \<Rightarrow> 'any::{}\<close>

(*
lemma [\<phi>reason 2000]:
  \<open> (\<And>vs. PROP Infer_Binding_Pattern
      (\<proc> f vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<throws> E @tag overloaded_synthesis)
      GIVEN
      (\<proc> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<throws> E' @tag overloaded_synthesis))
\<Longrightarrow> PROP Infer_Binding_Pattern
      (\<forall>vs. \<proc> f  vs \<lbrace> X  vs \<longmapsto> Y  \<rbrace> \<throws> E  @tag overloaded_synthesis)
      GIVEN
      (\<forall>vs. \<proc> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<throws> E' @tag overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 2100]:
  \<open> (\<And>vs. PROP Infer_Binding_Pattern
      (\<proc> f vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<throws> E @tag overloaded_synthesis)
      (synthesis_pattern2 (XX vs) YY)
      (\<proc> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<throws> E' @tag overloaded_synthesis))
\<Longrightarrow> PROP Infer_Binding_Pattern
      (\<forall>vs. \<proc> f  vs \<lbrace> X  vs \<longmapsto> Y  \<rbrace> \<throws> E  @tag overloaded_synthesis)
      (synthesis_pattern2 XX YY)
      (\<forall>vs. \<proc> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<throws> E' @tag overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1050]:
  \<open> PROP Infer_Binding_Pattern
      (\<proc> f  \<lbrace> X  \<longmapsto> \<lambda>ret. Y ret \<remains> R  \<rbrace> \<throws> E  @tag overloaded_synthesis)
      ()
      (\<proc> f' \<lbrace> X' \<longmapsto> \<lambda>ret. Y ret \<remains> R' \<rbrace> \<throws> E' @tag overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1100]:
  \<open> PROP Infer_Binding_Pattern
      (\<proc> f  \<lbrace> X  \<longmapsto> \<lambda>ret. Y  ret \<remains> R  \<rbrace> \<throws> E  @tag overloaded_synthesis)
      (synthesis_pattern1 Y')
      (\<proc> f' \<lbrace> X' \<longmapsto> \<lambda>ret. Y' ret \<remains> R' \<rbrace> \<throws> E' @tag overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1100]:
  \<open> PROP syntax_prepend_speration RX X' X''
\<Longrightarrow> PROP Infer_Binding_Pattern
      (\<proc> f  \<lbrace> X   \<longmapsto> \<lambda>ret. Y  ret \<remains> R  \<rbrace> \<throws> E  @tag overloaded_synthesis)
      (synthesis_pattern2 X' Y')
      (\<proc> f' \<lbrace> X'' \<longmapsto> \<lambda>ret. Y' ret \<remains> R' \<rbrace> \<throws> E' @tag overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1100]:
  \<open> PROP Infer_Binding_Pattern
      (\<proc> f  \<lbrace> X  \<longmapsto> \<lambda>ret. x \<Ztypecolon> Y  ret \<remains> R  \<rbrace> \<throws> E  @tag overloaded_synthesis)
      ()
      (\<proc> f' \<lbrace> X' \<longmapsto> \<lambda>ret. x \<Ztypecolon> Y' ret \<remains> R' \<rbrace> \<throws> E' @tag overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1050]:
  \<open> PROP Infer_Binding_Pattern
      (\<proc> f  \<lbrace> X  \<longmapsto> \<lambda>ret. x  \<Ztypecolon> Y  ret \<remains> R  \<rbrace> \<throws> E  @tag overloaded_synthesis)
      (synthesis_pattern1 x')
      (\<proc> f' \<lbrace> X' \<longmapsto> \<lambda>ret. x' \<Ztypecolon> Y' ret \<remains> R' \<rbrace> \<throws> E' @tag overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .
*)



(* \<forall>vs. \<proc> op_add LENGTH(?'b) vs \<lbrace> ?X' vs \<longmapsto> \<lambda>ret. ?x + ?y \<Ztypecolon> \<val>[ret] \<nat>(?'b) \<remains> ?R \<rbrace> \<throws> (\<lambda>e. ?R\<heavy_comma> 0 e)
    @tag overloaded_synthesis *)

subsubsection \<open>Rules of Overloaded Synthesis\<close>

lemma [\<phi>reason default %\<phi>overloaded_synthesis_fallback]:
  \<open> (\<And>vs. S1 vs\<heavy_comma> R \<shifts> YY vs \<remains> R2 \<with> Any @tag overloaded_synthesis)
\<Longrightarrow> \<forall>vs. \<proc> Return vs \<lbrace> S1 vs\<heavy_comma> R \<longmapsto> \<lambda>ret. YY ret \<remains> R2 \<rbrace> @tag overloaded_synthesis\<close>
  \<medium_left_bracket> premises I
    I
  \<medium_right_bracket> .

lemma [\<phi>reason default %\<phi>overloaded_synthesis_fallback]:
  \<open> A \<transforms> X \<remains> R \<with> P @tag overloaded_synthesis
\<Longrightarrow> A \<shifts> X \<remains> R \<with> P @tag overloaded_synthesis \<close>
  unfolding Action_Tag_def
  by (simp add: view_shift_by_implication)

lemma overloaded_synthesis_nullary:
  \<open> \<proc> H \<lbrace> R1 \<longmapsto> \<lambda>ret. YY ret \<remains> R1 \<rbrace> \<throws> E @tag overloaded_synthesis
\<Longrightarrow> \<proc> H \<lbrace> R1 \<longmapsto> \<lambda>ret. YY ret \<remains> R1 \<rbrace> \<throws> E @tag synthesis\<close>
  unfolding Action_Tag_def .

lemma overloaded_synthesis_unary:
  \<open> \<proc> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret. S1 ret \<remains> R2 \<rbrace> \<throws> E1 @tag synthesis
\<Longrightarrow> \<forall>vs. \<proc> H vs \<lbrace> S1 vs\<heavy_comma> R2 \<longmapsto> \<lambda>ret. YY ret \<remains> R3 \<rbrace>
         \<throws> E @tag overloaded_synthesis
\<Longrightarrow> \<proc> (h1 \<bind> H) \<lbrace> R1 \<longmapsto> \<lambda>ret. YY ret \<remains> R3 \<rbrace>
    \<throws> (E1 + E) @tag synthesis\<close>
  \<medium_left_bracket> premises H1 and H
    H1 H
  \<medium_right_bracket> .

lemma overloaded_synthesis_binary:
  \<open> \<proc> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret. S1 ret \<remains> R2 \<rbrace> \<throws> E1 @tag synthesis
\<Longrightarrow> \<proc> h2 \<lbrace> R2 \<longmapsto> \<lambda>ret. S2 ret \<remains> R3 \<rbrace> \<throws> E2 @tag synthesis
\<Longrightarrow> \<forall>vs. \<proc> H vs \<lbrace> S1 (\<phi>V_fst vs)\<heavy_comma> S2 (\<phi>V_snd vs)\<heavy_comma> R3 \<longmapsto> \<lambda>ret. YY ret \<remains> R4 \<rbrace>
         \<throws> E @tag overloaded_synthesis
\<Longrightarrow> \<proc> (h1 \<bind> (\<lambda>v1. h2 \<bind> (\<lambda>v2. H (\<phi>V_pair v1 v2))))
      \<lbrace> R1 \<longmapsto> \<lambda>ret. YY ret \<remains> R4 \<rbrace>
    \<throws> (\<lambda>e. E1 e + (E2 e\<heavy_comma> (\<exists>*v. S1 v)) + E e) @tag synthesis\<close>
  \<medium_left_bracket> premises H1 and H2 and H
    H1 H2 H
  \<medium_right_bracket> .

lemma overloaded_synthesis_ternary:
  \<open> \<proc> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret::VAL \<phi>arg. S1 ret \<remains> R2 \<rbrace> \<throws> E1 @tag synthesis
\<Longrightarrow> \<proc> h2 \<lbrace> R2 \<longmapsto> \<lambda>ret::VAL \<phi>arg. S2 ret \<remains> R3 \<rbrace> \<throws> E2 @tag synthesis
\<Longrightarrow> \<proc> h3 \<lbrace> R3 \<longmapsto> \<lambda>ret::VAL \<phi>arg. S3 ret \<remains> R4 \<rbrace> \<throws> E3 @tag synthesis
\<Longrightarrow> \<forall>vs. \<proc> H vs \<lbrace> S1 (\<phi>V_fst vs)\<heavy_comma> S2 (\<phi>V_fst (\<phi>V_snd vs))\<heavy_comma> S3 (\<phi>V_snd (\<phi>V_snd vs))\<heavy_comma> R4
                  \<longmapsto> \<lambda>ret. YY ret \<remains> R5 \<rbrace>
         \<throws> E @tag overloaded_synthesis
\<Longrightarrow> \<proc> (h1 \<bind> (\<lambda>v1. h2 \<bind> (\<lambda>v2. h3 \<bind> (\<lambda>v3. H (\<phi>V_pair v1 (\<phi>V_pair v2 v3))))))
      \<lbrace> R1 \<longmapsto> \<lambda>ret. YY ret \<remains> R5 \<rbrace>
    \<throws> (\<lambda>e. E1 e + ((\<exists>*v. S1 v)\<heavy_comma> E2 e) + ((\<exists>*v. S1 v)\<heavy_comma> (\<exists>*v. S2 v)\<heavy_comma> E3 e) + E e)
    @tag synthesis\<close>
  \<medium_left_bracket> premises H1 and H2 and H3 and H
    H1 H2 H3 H
  \<medium_right_bracket> .

lemma make_overloaded_synthesis_rule:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. E e\<heavy_comma> R)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<throws> E))
          Ant
          ((\<And>vs. X' vs \<transforms> X vs \<remains> R \<with> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<proc> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. Y ret \<remains> R \<rbrace> \<throws> E'
           @tag overloaded_synthesis)\<close>
  unfolding Gen_Synthesis_Rule_def
  \<medium_left_bracket> premises E[assertion_simps] and F and X and A
    X
    apply_rule F[OF A]
  \<medium_right_bracket> .

lemma make_overloaded_synthesis_rule':
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. E e\<heavy_comma> R')
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<proc> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. Y ret \<remains> R \<rbrace> \<throws> E))
          Ant
          ((\<And>vs. X' vs \<transforms> X vs \<remains> R' \<with> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<proc> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. Y ret \<remains> R\<heavy_comma> R' \<rbrace> \<throws> E'
           @tag overloaded_synthesis)\<close>
  unfolding REMAINS_def
  using make_overloaded_synthesis_rule[unfolded REMAINS_def, where Y = \<open>\<lambda>v. Y v\<heavy_comma> R\<close>, unfolded mult.assoc] .




ML_file \<open>library/additions/overloaded_synthesis.ML\<close>

attribute_setup overloaded_operator_in_synthesis = \<open>
  let val signat = Scan.peek (fn ctxt =>
            (( (\<^keyword>\<open>(\<close> -- \<^keyword>\<open>)\<close>) >> (K []) || Scan.repeat Parse.term)
           --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) -- Parse.term
              >> (fn (A,Y) =>
                  let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic (Context.proof_of ctxt)
                      val terms = map (Type.constraint \<^typ>\<open>_ \<phi>arg \<Rightarrow> assn\<close> o Syntax.parse_term ctxt') (Y::A)
                               |> Syntax.check_terms ctxt'
                      val ctxt'' = fold Proof_Context.augment terms ctxt'
                      val (Y'::A') = Variable.export_terms ctxt'' ctxt' terms
                   in Phi_Synthesis.Signature (A',Y')
                  end))
            || (Parse.term >>
                  (Phi_Synthesis.Operator o Context.cases Syntax.read_term_global Syntax.read_term ctxt)))
   in Phi_Reasoner.attr_syntax' signat
        (fn (pos, mode, group, signat) =>
          Thm.declaration_attribute (K (
            Phi_Synthesis.declare_overloaded_operator signat pos
                (mode, SOME (the_default @{reasoner_group %\<phi>overloaded_synthesis} group)))))
  end
\<close>
\<open>Declare the given term will be parsed as an overloaded operator in generating synthesis rules\<close>


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
  fn (_, (ctxt,sequent)) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (\<^Const_>\<open>Collect_Return_Values _\<close> $ S $ Var S' $ Var V')
          = Thm.major_prem_of sequent
    val (V'',S'') = Procedure_Syntax.package_values0
                            "\<v>\<s>" (TVar (("ret", Thm.maxidx_of sequent),\<^sort>\<open>VALs\<close>)) false NONE S
          |> apply2 (Thm.cterm_of ctxt)
   in Drule.infer_instantiate_types ctxt [(S',S''),(V',V'')] sequent
          |> (fn th => @{thm Collect_Return_Values_I} RS th)
          |> pair ctxt |> Seq.single
  end
\<close>

lemma [\<phi>reason 2550]:
  \<open> Collect_Return_Values X S vs
\<Longrightarrow> X \<transforms> collect_return_values S vs\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def TAIL_def
  by simp

lemma [\<phi>reason 3200]:
  \<open> 0 \<transforms> collect_return_values 0 \<phi>V_none\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def TAIL_def
  by simp


subsection \<open>Compilibility / Validity of Semantics\<close>

definition \<open>chk_semantics_validity x \<longleftrightarrow> True\<close> \<comment> \<open>A pure syntactic check and have no logical semantics\<close>


section \<open>Finale\<close>

hide_const synthesis_gen_mode

end
