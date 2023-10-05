chapter \<open>Reasoning Processes in IDE-CP - Part III\<close>

text \<open>Here we give the implementation of all large reasoning processes that are declared in
the previous part I.\<close>


theory IDE_CP_Reasoning3
  imports Phi_Types
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


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<i>\<s> T \<Longrightarrow> MemAddress a \<in> S \<Longrightarrow> h |` S \<^bold>a\<^bold>t a \<i>\<s> T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<i>\<s> T \<Longrightarrow> MemAddress a \<notin> S \<Longrightarrow> h |` (- S) \<^bold>a\<^bold>t a \<i>\<s> T "
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<i>\<s> T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<i>\<s> T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<i>\<s> T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<i>\<s> T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)

*)

section \<open>Small Processes - I\<close>

(* TODO! not that easy! IMPORTANT!

subsection \<open>Unification of \<lambda>-Abstraction\<close>

declare [[\<phi>trace_reasoning = 3]]

\<phi>type_def Function_over :: \<open>('a,'b) \<phi> \<Rightarrow> 'c \<Rightarrow> ('a, 'c \<Rightarrow> 'b) \<phi>\<close> (infix "<func-over>" 40)
  where \<open>(T <func-over> x) = (\<lambda>f. f x \<Ztypecolon> T)\<close>
  deriving Basic
    (* and \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = y (*I don't know if the functor properties are required in this \<phi>-type.
                                  *All of the ToA reasonings reduce to destruction.*)
         \<Longrightarrow> Transformation_Functor (\<lambda>T. T <func-over> x) (\<lambda>T. T <func-over> y) T U
                                    (\<lambda>f. {f x}) (\<lambda>g. UNIV) (\<lambda>r f g. r (f x) (g y)) \<close>
       and \<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = y
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
term \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = y
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
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fx \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f \<Ztypecolon> T <func-over> x \<w>\<i>\<t>\<h> P\<close>
  unfolding lambda_abstraction_def
  by (simp add: Function_over.intro_reasoning)

lemma [\<phi>reason %ToA_normalizing]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fx \<Ztypecolon> T \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f \<Ztypecolon> (T <func-over> x) \<^emph>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def lambda_abstraction_def
  by simp



lemma [\<phi>reason 2000]:
  \<open> f x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> f \<Ztypecolon> T <func-over> x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse ?input (\<lambda>v. ?f \<Ztypecolon> ?T v <func-over> ?x :: assn)\<close>
]:
  \<open> Synthesis_Parse input (\<lambda>v. fx \<Ztypecolon> T v)
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Synthesis_Parse input (\<lambda>v. f \<Ztypecolon> T v <func-over> x :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<o>\<c> g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> \<blangle> f x \<Ztypecolon> T v \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> \<blangle> f \<Ztypecolon> T v <func-over> x \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)
*)

text \<open>TODO!\<close>

(*TODO!
lemma [\<phi>reason 1200]:
  \<open> \<g>\<u>\<a>\<r>\<d> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Agreement T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, fst x) \<Ztypecolon> Agreement U \<^emph> (Agreement T ?\<^sub>\<phi> C) \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  unfolding Action_Tag_def \<r>Guard_def
  apply (cases C; cases x; simp add: \<phi>Prod_expn')
  \<medium_left_bracket> premises A
    dup
    apply_rule Agreement_cast[OF A]
  \<medium_right_bracket>
  using Agreement_cast .

lemma [\<phi>reason 1211]:
  \<open> \<g>\<u>\<a>\<r>\<d> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Agreement T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, fst x) \<Ztypecolon> Agreement U \<^emph> (Agreement T ?\<^sub>\<phi> C) \<w>\<i>\<t>\<h> (
      Reverse_Transformation (fst y' \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd y' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P') (
        y' \<Ztypecolon> Agreement U' \<^emph> (Agreement T' ?\<^sub>\<phi> C) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd y', ()) \<Ztypecolon> Agreement T' \<^emph> \<circle> \<w>\<i>\<t>\<h> P')
    \<and> P) @action \<A>SE True \<close>
  unfolding Action_Tag_def \<r>Guard_def Generated_Rule_def
  apply (rule transformation_weaken[where P=P], defer_tac)
  apply (cases C; cases x; simp add: \<phi>Prod_expn')
  \<medium_left_bracket> premises A
    dup
    apply_rule Agreement_cast[OF A]
  \<medium_right_bracket>
  apply (simp add: transformation_weaken Agreement_cast)
  apply (clarsimp; cases C; cases y'; simp add: \<phi>Prod_expn')
  \<medium_left_bracket> premises _ and _ and A and _
    apply_rule Agreement_cast[OF A]
    Agreement_shrink
  \<medium_right_bracket>
  using Agreement_cast .
*)



consts partial_add_split :: action
       non_trivial_partial_add_split :: action

declare [[
    \<phi>premise_attribute [unfolded Action_Tag_def] for \<open>_ @action partial_add_split\<close>,
    \<phi>premise_attribute? [useful] for \<open>_ @action partial_add_split\<close>,
    \<phi>premise_attribute [unfolded Action_Tag_def] for \<open>_ @action non_trivial_partial_add_split\<close>,
    \<phi>premise_attribute? [useful] for \<open>_ @action non_trivial_partial_add_split\<close>
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



declare [[\<phi>trace_reasoning = 0]]




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

subsubsection \<open>Conventions\<close>

declare [[\<phi>reason_default_pattern
    \<open>If ?P ?A ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join \<close> \<Rightarrow> \<open>If ?P ?A ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join \<close> (100)
and \<open>If ?P ?A ?B = _ @action br_join \<close> \<Rightarrow> \<open>If ?P ?A ?B = _ @action br_join \<close> (100)
and \<open>?X @action br_join \<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Bad rule\<close> (?X @action br_join ))\<close> (0)

and \<open>Identifier_of ?T _ _\<close> \<Rightarrow> \<open>Identifier_of ?T _ _\<close> (100)
]]

\<phi>reasoner_group \<phi>br_join_all = (100, [1,3000]) for \<open>If C A B @action br_join\<close>
    \<open>All rules of \<phi>-type branch convergence\<close>
  and \<phi>br_join_fail = (1,[1,10]) for \<open>If C A B @action br_join\<close> in \<phi>br_join_all
                     \<open>Fallbacks\<close>
  and \<phi>br_join_search_counterpart = (30, [30,30]) for \<open>If C A B @action br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_fail
                     \<open>Looks from the false-branch for the counterpart of the heading \<phi>-type in the true-branch,
                      and enters the sub-reasoning for joining the two \<phi>-types.\<close>
  and \<phi>br_join_derived = (50,[50,50]) for \<open>If C A B @action br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_search_counterpart
                     \<open>Derived from functor properties\<close>
  and \<phi>br_join_cut = (1000, [1000, 1030]) for \<open>If C A B @action br_join\<close>
                       in \<phi>br_join_all > \<phi>br_join_derived
                     \<open>Cutting rules\<close>
  and \<phi>br_join_spec = (1100, [1100,2000]) for \<open>If C A B @action br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_cut
                     \<open>Rules for specific connectives\<close>
  and \<phi>br_join_normalize = (2100, [2100,2300]) for \<open>If C A B @action br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_spec
                     \<open>Normalization rules\<close>
  and \<phi>br_join_red = (2500, [2500, 2800]) for \<open>If C A B @action br_join\<close>
                       in \<phi>br_join_all and > \<phi>br_join_spec
                     \<open>Reductions of high priority\<close>
  and \<phi>br_join_red_zero = (2900, [2900,2900]) for \<open>If C A B @action br_join\<close>
                       in \<phi>br_join_all > \<phi>br_join_red
                     \<open>Reductions for zero\<close>
  and \<phi>br_join_success = (2990, [2990,3000]) for \<open>If C A B @action br_join\<close>
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

lemma [\<phi>reason %\<phi>br_join_success for \<open>If _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action invoke_br_join\<close>]:
  \<open> Simplify (assertion_simps undefined) A' A
\<Longrightarrow> Simplify (assertion_simps undefined) B' B
\<Longrightarrow> If P A' B' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C @action br_join
\<Longrightarrow> If P A  B  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C @action invoke_br_join \<close>
  unfolding Action_Tag_def Simplify_def
  by blast


subsubsection \<open>Fallback and Termination\<close>

lemma [\<phi>reason default %\<phi>br_join_fail]:
  \<open>If P A B = If P A B @action br_join\<close>
  unfolding Action_Tag_def ..

lemma [\<phi>reason %\<phi>br_join_success for \<open>If ?P ?A ?A'' = ?X @action br_join\<close>]:
  \<open>If P A A = A @action br_join\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason default %\<phi>br_join_fail+4]:
  " If P T U = Z @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P x y \<Ztypecolon> Z) @action br_join"
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_success+5 for \<open>If _ (_ \<Ztypecolon> _) (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P x y \<Ztypecolon> T) @action br_join\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_success for \<open>If ?P ?A ?A'' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X @action br_join\<close>]:
  \<open>If P A A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A @action br_join\<close>
  unfolding Action_Tag_def Transformation_def by simp


subsubsection \<open>Zero\<close>

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open>If P A 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (A \<s>\<u>\<b>\<j> P) @action br_join\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: zero_set_def)

lemma [\<phi>reason %\<phi>br_join_red_zero]:
  \<open>If P 0 A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (A \<s>\<u>\<b>\<j> \<not> P) @action br_join\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: zero_set_def)


subsubsection \<open>Subjection\<close>

\<phi>reasoner_group \<phi>br_join_subj = (%\<phi>br_join_spec+800, [%\<phi>br_join_spec+800, %\<phi>br_join_spec+820]) for \<open>If C A B @action br_join\<close>
                                 in \<phi>br_join_spec
                                \<open>Reductions for Subejction\<close>

lemma [\<phi>reason %\<phi>br_join_subj+20]:
  \<open> If P (L \<s>\<u>\<b>\<j> Q1 \<and> Q2) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action br_join
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> Q1 \<s>\<u>\<b>\<j> Q2) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action br_join \<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason %\<phi>br_join_subj+20]:
  \<open> If P L (R \<s>\<u>\<b>\<j> Q1 \<and> Q2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action br_join
\<Longrightarrow> If P L (R \<s>\<u>\<b>\<j> Q1 \<s>\<u>\<b>\<j> Q2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action br_join \<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason %\<phi>br_join_subj+10]:
  \<open> If P QL QR = Q @action br_join
\<Longrightarrow> If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> QL) (R \<s>\<u>\<b>\<j> QR) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<s>\<u>\<b>\<j> Q) @action br_join\<close>
  unfolding Action_Tag_def Transformation_def by force

lemma [\<phi>reason %\<phi>br_join_subj]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  \<open> If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> Q) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<s>\<u>\<b>\<j> P \<longrightarrow> Q) @action br_join\<close>
  unfolding Transformation_def Action_Tag_def by simp

lemma [\<phi>reason %\<phi>br_join_subj]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  \<open> If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P L (R \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<s>\<u>\<b>\<j> \<not>P \<longrightarrow> Q) @action br_join\<close>
  unfolding Action_Tag_def Transformation_def by simp


subsubsection \<open>Existential\<close>

\<phi>reasoner_group \<phi>br_join_ex = (%\<phi>br_join_spec+700, [%\<phi>br_join_spec+700, %\<phi>br_join_spec+720])
                                for \<open>If C A B @action br_join\<close> in \<phi>br_join_spec and < \<phi>br_join_subj
                              \<open>Reductions for Existence\<close>

lemma Conv_Merge_Ex_both_imp:
  \<open> (\<And>x. If P (L x) (R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X x @action br_join)
\<Longrightarrow> If P (\<exists>* x. L x) (\<exists>* x. R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. X x) @action br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; clarsimp simp add: set_eq_iff; blast)

lemma Conv_Merge_Ex_R_imp [\<phi>reason %\<phi>br_join_ex]:
  \<open> (\<And>x. If P L (R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X x @action br_join)
\<Longrightarrow> If P L (\<exists>* x. R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. X x) @action br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; simp add: set_eq_iff; blast)

lemma [\<phi>reason %\<phi>br_join_ex]:
  \<open> (\<And>x. If P (L x) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X x @action br_join)
\<Longrightarrow> If P (\<exists>* x. L x) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. X x) @action br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; simp add: set_eq_iff; blast)

text \<open>The merging recognizes two existential quantifier are identical if their type and variable name
  are the same. If so it uses Conv_Merge_Ex_both to merge the quantification,
  or else the right side is expanded first.\<close>

\<phi>reasoner_ML Merge_Existential_imp %\<phi>br_join_ex+20 (\<open>If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X\<close>) = \<open>
  fn (_, (ctxt,sequent)) =>
    let
      val ((Const (\<^const_name>\<open>If\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exa,tya,_))
                                           $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exb,tyb,_))), _, _)
          = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      val sequent' = if exa = exb andalso tya = tyb
                     then @{thm Conv_Merge_Ex_both_imp} RS sequent
                     else @{thm Conv_Merge_Ex_R_imp} RS sequent
    in Seq.single (ctxt, sequent')
    end
\<close>


subsubsection \<open>Looks for the counterpart\<close>

lemma [\<phi>reason default %\<phi>br_join_search_counterpart]:
  \<open> Identifier_of T identifier T'
\<Longrightarrow> (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' @action NToA) \<or>\<^sub>c\<^sub>u\<^sub>t
    FAIL TEXT(\<open>\<phi>-Type\<close> (x \<Ztypecolon> T) \<open>is given in the true-branch but its counterpart\<close> (y \<Ztypecolon> T') \<open>is not seen in the false-branch.\<close> \<newline>
              \<open>Perhaps, I should search a more general form \<close> T'' \<open>of the counterpart and if so, feed \<phi>-LPR a rule\<close> \<newline>
              (Identifier_of T identifier T''))
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> T') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action br_join
\<Longrightarrow> If P L R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P (L * (x \<Ztypecolon> T)) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Z @action br_join\<close>
  unfolding Action_Tag_def Transformation_def Premise_def Orelse_shortcut_def FAIL_def
  by (cases P; clarsimp; blast)

subsubsection \<open>Join Two \<phi>-Types\<close>

\<phi>reasoner_group br_join_\<phi>ty = (20, [20,20]) for \<open>If C (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action br_join\<close> 
                               in \<phi>br_join_all and > \<phi>br_join_fail
                              \<open>Fallbacks of joining two \<phi>-types, using ToA\<close>

paragraph \<open>Fallback by ToA\<close>

lemma [\<phi>reason %br_join_\<phi>ty]:
  \<open> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> T @action NToA
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If P x y' \<Ztypecolon> T @action br_join \<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp

paragraph \<open>By Transformation Functor\<close>

declare [[\<phi>trace_reasoning = 1]]

declare if_cancel[simp]

lemma [\<phi>reason_template %\<phi>br_join_derived]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Functional_Transformation_Functor F\<^sub>T F' T Z D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> P \<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F' U Z D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (D\<^sub>T x = {} \<longleftrightarrow> D\<^sub>U y = {}) \<and>
           (\<forall>a \<in> D\<^sub>T x. z a (@b. b \<in> D\<^sub>U y) \<in> R\<^sub>T x) \<and>
           (\<forall>b \<in> D\<^sub>U y. z (@a. a \<in> D\<^sub>T x) b \<in> R\<^sub>U y)
\<Longrightarrow> (\<And>(a,b) \<in> (D\<^sub>T x \<times> D\<^sub>U y). If P (a \<Ztypecolon> T) (b \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z a b \<Ztypecolon> Z @action br_join)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> z' : If P (fm\<^sub>T (\<lambda>a. z a (@b. b \<in> D\<^sub>U y)) (\<lambda>_. True) x) (fm\<^sub>U (\<lambda>b. z (@a. a \<in> D\<^sub>T x) b) (\<lambda>_. True) y) @action \<A>_template_reason
\<Longrightarrow> If P (x \<Ztypecolon> F\<^sub>T T) (y \<Ztypecolon> F\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z' \<Ztypecolon> F' Z @action br_join \<close>
  unfolding Action_Tag_def Premise_def Functional_Transformation_Functor_def Transformation_def
            meta_Ball_def meta_case_prod_def Simplify_def
  apply (cases \<open>D\<^sub>T x = {}\<close>; clarsimp; cases P; clarsimp)
  subgoal premises prems for v proof -
    have t1: \<open>(@b. b \<in> D\<^sub>U y) \<in> D\<^sub>U y\<close>
      by (simp add: prems(5) some_in_eq)
    show ?thesis
      by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>a. z a (@b. b \<in> D\<^sub>U y)\<close>],
                          THEN spec[where x=\<open>\<lambda>_. True\<close>]]
                 prems(2-)
                 t1,
          clarsimp)
  qed
  subgoal premises prems for v proof -
    have t1: \<open>(@a. a \<in> D\<^sub>T x) \<in> D\<^sub>T x\<close>
      by (simp add: prems(4) some_in_eq)
    show ?thesis
      by (insert prems(1)[THEN spec[where x=y], THEN spec[where x=\<open>\<lambda>b. z (@a. a \<in> D\<^sub>T x) b\<close>],
                          THEN spec[where x=\<open>\<lambda>_. True\<close>]]
                 prems(2-)
                 t1,
          clarsimp)
  qed .


subsubsection \<open>Convergence of Structural Nodes\<close>

lemma [\<phi>reason 1200 for \<open>If ?P (_ \<Ztypecolon> _ \<odiv> _) (_ \<Ztypecolon> _ \<odiv> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action br_join
\<Longrightarrow> If P n m = nm @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> n \<odiv> T) (y \<Ztypecolon> m \<odiv> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> nm \<odiv> Z) @action br_join\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>Share_transformation)

lemma [\<phi>reason 1200 for \<open>If _ ((_,_) \<Ztypecolon> _ \<^emph> _) ((_,_) \<Ztypecolon> _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (x' \<Ztypecolon> T') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x'' \<Ztypecolon> T'' @action br_join
\<Longrightarrow> If P (y \<Ztypecolon> U) (y' \<Ztypecolon> U') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y'' \<Ztypecolon> U'' @action br_join
\<Longrightarrow> If P ((x,y) \<Ztypecolon> T \<^emph> U) ((x',y') \<Ztypecolon> T' \<^emph> U') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((x'',y'') \<Ztypecolon> T'' \<^emph> U'') @action br_join\<close>
  unfolding Action_Tag_def apply (cases P; simp add: \<phi>Prod_transformation)
   apply (rule \<phi>Prod_transformation[where Pa=True and Pb=True, simplified], assumption, assumption)
  by (rule \<phi>Prod_transformation[where Pa=True and Pb=True, simplified], assumption, assumption)

(* (*TESTING... re-enable them for performance*)
lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> _ \<^bold>\<rightarrow>\<^sub>@ _) (_ \<Ztypecolon> _ \<^bold>\<rightarrow>\<^sub>@ _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Z) @action br_join\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>MapAt_L_cast)

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> _ \<^bold>\<rightarrow> _) (_ \<Ztypecolon> _ \<^bold>\<rightarrow> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (y \<Ztypecolon> k \<^bold>\<rightarrow> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> k \<^bold>\<rightarrow> Z) @action br_join\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>MapAt_cast)

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> Val _ _) (_ \<Ztypecolon> Val _ _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> Val v T) (y \<Ztypecolon> Val v U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Val v Z) @action br_join\<close>
  unfolding Action_Tag_def by (cases P; simp add: Val_transformation)

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<black_circle> _) (_ \<Ztypecolon> \<black_circle> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> \<black_circle> T) (y \<Ztypecolon> \<black_circle> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> \<black_circle> Z) @action br_join\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>Some_cast)
*)

(* fix me!!!
lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<black_circle> _) (_ \<Ztypecolon> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> Any
\<Longrightarrow> If P (x \<Ztypecolon> \<black_circle> T) (y \<Ztypecolon> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P (Some x') None \<Ztypecolon> Itself) @action br_join\<close>
  unfolding Action_Tag_def     
  \<medium_left_bracket> premises T[\<phi>reason for action \<open>to Itself\<close>]  
    cases \<medium_left_bracket> to Itself \<medium_right_bracket>. \<medium_left_bracket> to Itself \<medium_right_bracket>. ;; \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<circle>) (_ \<Ztypecolon> \<black_circle> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> y \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> Any
\<Longrightarrow> If P (x \<Ztypecolon> \<circle>) (y \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P None (Some y') \<Ztypecolon> Itself) @action br_join\<close>
  unfolding Action_Tag_def     
  \<medium_left_bracket> premises T[\<phi>reason for action \<open>to Itself\<close>]  
    cases \<medium_left_bracket> to Itself \<medium_right_bracket>. \<medium_left_bracket> to Itself \<medium_right_bracket>. ;; \<medium_right_bracket>. .
*)

declare [[\<phi>trace_reasoning = 0]]

lemma [\<phi>reason_template add]:
  \<open> Functional_Transformation_Functor Fa Fz Da rma Prem_a pma ma
\<Longrightarrow> Functional_Transformation_Functor Fb Fz Db rmb Prem_b pmb mb
\<Longrightarrow> (P \<Longrightarrow> Prem_a)
\<Longrightarrow> (\<not> P \<Longrightarrow> Prem_b)
\<Longrightarrow> (\<And>x' y'. \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> x' \<in> Da x) \<and> (\<not> P \<longrightarrow> y' \<in> Db y) \<Longrightarrow>
        If P (x' \<Ztypecolon> T) (y' \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If P (za x') (zb y') \<Ztypecolon> Z @action br_join)
\<Longrightarrow> If P (x \<Ztypecolon> Fa T) (y \<Ztypecolon> Fb U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If P (ma za x) (mb zb y) \<Ztypecolon> Fz Z @action br_join \<close>
  unfolding Action_Tag_def
  apply (cases P; simp)
  \<medium_left_bracket> premises FTF_a and FTF_b and _ and Tr and _
    interpret Functional_Transformation_Functor Fa Fz Da rma True pma ma using FTF_a . ;;
    apply_rule functional_transformation[where T=T and U=Z and f=za]
    \<medium_left_bracket> Tr \<medium_right_bracket>
  \<medium_right_bracket>
  \<medium_left_bracket> premises FTF_a and FTF_b and _ and Tr and _
    interpret Functional_Transformation_Functor Fb Fz Db rmb True pmb mb using FTF_b . ;;
    apply_rule functional_transformation[where T=U and U=Z and f=zb]
    \<medium_left_bracket> Tr \<medium_right_bracket>
  \<medium_right_bracket> .

(*
lemma br_join_general_rule:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> If P (fa x \<Ztypecolon> T) (fa y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fb z \<Ztypecolon> Z) @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> Fa T) (y \<Ztypecolon> Fa U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Fb Z) @action br_join \<close>
  unfolding Action_Tag_def Transformation_Functor_def
  by (cases P; simp)

\<phi>reasoner_ML br_join_general_rule 50 (\<open>If _ (_ \<Ztypecolon> _) (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>) = \<open>
fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ ( _ (*Action_Tag*) $ (_ (*Transformation*)
            $ ( _ (*If*) $ _ $ (_(*\<phi>Type*) $ _ $ T) $ (_(*\<phi>Type*) $ _ $ U))
            $ _
            $ _
      ) $ _ )
        = snd (Phi_Help.varified_leading_antecedent_meta_quantifiers ctxt (Thm.prop_of sequent))
   in case (Phi_Functor_Detect.detect 1 ctxt T,
            Phi_Functor_Detect.detect 1 ctxt U)
        of (SOME [Ft,_], SOME [Fu, _]) => let
            val rule = Drule.infer_instantiate ctxt
                          [(("Fa",0), Thm.cterm_of ctxt Ft), (("Fb",0), Thm.cterm_of ctxt Fu)]
                          @{thm "br_join_general_rule"}
             in SOME ((ctxt, rule RS sequent), Seq.empty) end
            handle THM _ => NONE
         | _ => NONE
  end)
\<close>
*)


lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> Nosep _) (_ \<Ztypecolon> Nosep _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action br_join\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action br_join
\<Longrightarrow> If P (x \<Ztypecolon> Nosep T) (y \<Ztypecolon> Nosep U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Nosep Z) @action br_join\<close>
  unfolding Action_Tag_def by (cases P; simp add: Nosep_cast)

(* subsubsection \<open>Object\<close>

definition EqualAddress :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool "
  where "EqualAddress _ _ = True"

lemma [\<phi>reason]:
  "\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a1 = a2
   \<Longrightarrow> EqualAddress (a1 \<Zinj> x1 \<Ztypecolon> T1) (a2 \<Zinj> x2 \<Ztypecolon> T2) "
  unfolding EqualAddress_def .. *)

subsubsection \<open>Unfold\<close>

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L (N * R1 * R2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P L (N * (R1 * R2)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join"
  for N :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P (L1 * L2 * L3) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P (L1 * (L2 * L3)) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)


subsubsection \<open>Eliminate Void Hole\<close>

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P L (R * 1) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P L (1 * R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L (R' * R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P L (R' * 1 * R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason %\<phi>br_join_normalize]:
  " If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join
\<Longrightarrow> If P (L * 1) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action br_join"
  for R :: \<open>'a::sep_magma_1 set\<close>
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


section \<open>Synthesis\<close>

subsubsection \<open>Multi-Target\<close>

lemma [\<phi>reason 1250]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> A ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> B ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<bind> (\<lambda>v1. f2 \<bind> (\<lambda>v2. Return (\<phi>V_pair v2 v1))))
         \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A (\<phi>V_snd ret)\<heavy_comma> B (\<phi>V_fst ret) \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (ExSet A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2  \<medium_right_bracket> .

lemma [\<phi>reason 1230]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> A \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> B ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<ggreater> f2) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A \<heavy_comma> B ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<medium_right_bracket> .

lemma [\<phi>reason 1240]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> A ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> B \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<bind> (\<lambda>v. f2 \<ggreater> Return v)) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A ret \<heavy_comma> B \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (ExSet A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<medium_right_bracket> .

lemma [\<phi>reason 1250]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret::unit \<phi>arg. R2\<heavy_comma> \<blangle> A \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret::unit \<phi>arg. R3\<heavy_comma> \<blangle> B \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<ggreater> f2) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A \<heavy_comma> B \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<medium_right_bracket> .


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

definition \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration :: \<open>'a::{} \<Rightarrow> 'b::{} \<Rightarrow> 'c::{} \<Rightarrow> prop\<close>
  where \<open> \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration A B C \<equiv> TERM C\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration ?A ?B _\<close> \<Rightarrow> \<open>PROP \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration ?A ?B _\<close> (100)
]]

lemma [\<phi>reason 1000]:
  \<open> PROP \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration A B (A * B)\<close>
  unfolding \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration_def .

lemma [\<phi>reason 1100]:
  \<open> PROP \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration A B C
\<Longrightarrow> PROP \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration A (B * D) (C * D)\<close>
  unfolding \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration_def .



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

declare [[generate_pattern_of_synthesis_rule
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis &&& TERM ()\<close> \<Rightarrow>
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>    (120)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis &&& TERM ?Z\<close> \<Rightarrow>
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>    (110)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _  \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis &&& (TERM ?X &&& TERM ?Z)\<close> \<Rightarrow>
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>    (110)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis &&& TERM ()\<close> \<Rightarrow>
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>    (125)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> _ \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis &&& TERM ?z\<close> \<Rightarrow>
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?z \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>    (106)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?Z \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis &&& TERM ()\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?Z \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis\<close>    (120)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis &&& TERM ?Z\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?Z \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis\<close>    (110)
  and \<open> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis &&& (TERM ?X &&& TERM ?Z)\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?Z \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis\<close>    (110)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?x \<Ztypecolon> _ \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis &&& TERM ()\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?x \<Ztypecolon> _ \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis\<close>    (125)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<Ztypecolon> _ \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis &&& TERM ?z\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?z \<Ztypecolon> _ \<brangle> \<w>\<i>\<t>\<h> _ @action synthesis\<close>    (106)
]]

(*
lemma [\<phi>reason 2000]:
  \<open> PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f  \<lbrace> X \<longmapsto> \<lambda>ret. R  \<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action synthesis)
      ()
      (\<p>\<r>\<o>\<c> f' \<lbrace> X \<longmapsto> \<lambda>ret. R' \<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1050]:
  \<open> PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f  \<lbrace> X \<longmapsto> \<lambda>ret. R  \<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action synthesis)
      Z'
      (\<p>\<r>\<o>\<c> f' \<lbrace> X \<longmapsto> \<lambda>ret. R' \<heavy_comma> \<blangle> Z' ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .
*)

attribute_setup \<phi>synthesis = \<open>
  Scan.peek (fn ctxt =>
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
        val pattern = (Args.$$$ "_"  >> (K Phi_Synthesis.No_Pattern))
                   || ((Parse.term --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) -- Parse.term)
                          >> (fn (a,b) => case read_term [a,b] of [a',b'] =>
                                                  Phi_Synthesis.Arg_and_Ret (a',b')))
                   || (Parse.term >> (singleton read_term #> Phi_Synthesis.Ret_only))
        val priority = Scan.option (\<^keyword>\<open>(\<close> |-- Parse.int --| \<^keyword>\<open>)\<close>)
     in Phi_Help.pos_parser "\<phi>synthesis" --| Scan.option Args.add --
        Scan.optional Parse.int 100 --
       (Scan.optional (\<^keyword>\<open>for\<close> |-- Parse.and_list1 (pattern -- priority)) [] --
        Scan.optional (\<^keyword>\<open>except\<close> |-- Parse.and_list1 pattern) [] )
>> (fn ((pos, priority), pattern) =>
      Thm.declaration_attribute (fn rule =>
        Phi_Synthesis.declare_rule pos priority pattern rule))
    end
)\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<p>\<r>\<o>\<c> _ \<lbrace> _ \<heavy_comma> \<blangle> ?X \<brangle> \<longmapsto> ?Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<p>\<r>\<o>\<c> _ \<lbrace> _ \<heavy_comma> \<blangle> ?X \<brangle> \<longmapsto> ?Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _))
            (PROP ?P) (PROP _)\<close>  (120)
  and \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<p>\<r>\<o>\<c> _ \<lbrace> _ \<heavy_comma> \<blangle> ?X \<brangle> \<longmapsto> \<lambda>r. ?RN   \<heavy_comma> \<blangle> ?Y r \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<p>\<r>\<o>\<c> _ \<lbrace> _ \<heavy_comma> \<blangle> ?X \<brangle> \<longmapsto> \<lambda>r. ?RN'' \<heavy_comma> \<blangle> ?Y r \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _))
            (PROP ?P) (PROP _)\<close>  (125)
  and \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> ?f  v \<lbrace> ?R  \<heavy_comma> \<blangle> ?X v \<brangle> \<longmapsto> ?Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> ?f' v \<lbrace> ?R' \<heavy_comma> \<blangle> ?X v \<brangle> \<longmapsto> ?Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E'))
            (PROP ?P) (PROP _)\<close>  (120)
  and \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> ?f  v \<lbrace> ?R  \<heavy_comma> \<blangle> ?X  v \<brangle> \<longmapsto> \<lambda>r. ?RN   \<heavy_comma> \<blangle> ?Y r \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _))
            (PROP ?P) (PROP _)\<close>
   \<Rightarrow> \<open>PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> ?f' v \<lbrace> ?R' \<heavy_comma> \<blangle> ?X' v \<brangle> \<longmapsto> \<lambda>r. ?RN'' \<heavy_comma> \<blangle> ?Y r \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _))
            (PROP ?P) (PROP _)\<close>  (125)
]]

subsection \<open>General Rule\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP Gen_Synthesis_Rule Q (PROP Ant &&& PROP P) X
\<Longrightarrow> PROP Gen_Synthesis_Rule (PROP P \<Longrightarrow> PROP Q) Ant X\<close>
  unfolding Gen_Synthesis_Rule_def conjunction_imp
  subgoal premises P by (rule P(1), rule P(2), assumption, assumption) .

subsection \<open>Transformation \& View Shift\<close>

lemma Gen_Synthesis_Rule_transformation_12:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yr * Y \<w>\<i>\<t>\<h> P))
      Ant
      (PROP Ant \<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Yr * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P @action synthesis) \<close>
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by (simp; rule transformation_left_frame[where U=\<open>Yr * Y\<close>, simplified mult.assoc[symmetric]]; simp)

lemma Gen_Synthesis_Rule_transformation_11:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P))
      Ant
      (PROP Ant \<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P @action synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by (simp; rule transformation_left_frame; simp)

lemma Gen_Synthesis_Rule_transformation_10:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P))
      Ant
      (PROP Ant \<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<w>\<i>\<t>\<h> P @action synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by (rule transformation_left_frame; simp)

lemma Gen_Synthesis_Rule_transformation_01:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yr * Y \<w>\<i>\<t>\<h> P))
      Ant
      (PROP Ant \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yr * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P @action synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by simp

lemma Gen_Synthesis_Rule_transformation_00:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P))
      Ant
      (PROP Ant \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by simp

\<phi>reasoner_ML Gen_Synthesis_Rule_transformation 10
    (\<open>PROP Gen_Synthesis_Rule (Trueprop (_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _)) (PROP _) (PROP _)\<close>)
  = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
    let val _ (*Gen_Synthesis_Rule*) $ (_ (*Trueprop*) $ TM) $ _ $ _ = Thm.major_prem_of sequent
        fun last_ele (Const (\<^const_name>\<open>ExSet\<close>, _) $ X) = last_ele X
          | last_ele (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = last_ele X
          | last_ele (Const (\<^const_name>\<open>times\<close>, _) $ X $ _ ) = last_ele X
          | last_ele X = X
        val (mode,X,Y) =
          case TM
            of Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ _ =>
                  if last_ele X = last_ele Y then (01,X,Y) else (00,X,Y)
             | Const(\<^const_name>\<open>View_Shift\<close>, _) $ X $ Y $ _ =>
                  if last_ele X = last_ele Y then (11,X,Y) else (10,X,Y)

        fun warn () = warning "You have multiple separated items and it is unclear which one is \
                     \the target to be synthesised or the residue of the synthesis.\n\
                     \We assume the synthesis target is the last item.\n\
                     \You should use \<open> Residue \<heavy_comma> \<blangle> Target \<brangle> \<close> to annotate the target, \
                     \or \<open> \<blangle> Target \<brangle> \<close> if there is no residue."
        fun chk_target (Abs (_,_,tm)) = chk_target tm
          | chk_target (Const (\<^const_name>\<open>ExSet\<close>, _) $ _)
              = error ("Exisential quantification has not been supported in synthesis.")
          | chk_target (Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _)
              = Phi_Reasoner.bad_config "Subjection shouldn't occur here."
          | chk_target (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _)
              = (case mode of 00 => @{thm Gen_Synthesis_Rule_transformation_10}
                            | 01 => @{thm Gen_Synthesis_Rule_transformation_10})
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _))
              = (case mode of 01 => @{thm Gen_Synthesis_Rule_transformation_00}
                            | 00 => @{thm Gen_Synthesis_Rule_transformation_10})
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ A $ B)
              = (case mode of 00 => @{thm Gen_Synthesis_Rule_transformation_12}
                            | 01 => @{thm Gen_Synthesis_Rule_transformation_01})
          | chk_target _ = @{thm Gen_Synthesis_Rule_transformation_11}
     in case X
          of Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _)
               => NONE
           | _ => SOME ((ctxt, (chk_target Y) RS sequent), Seq.empty)
    end)\<close>



subsection \<open>Procedure Application - General Methods\<close>


lemma [\<phi>reason 1200 for \<open>PROP Gen_Synthesis_Rule
      (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<heavy_comma> ?X v \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<longmapsto> ?Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) _ _\<close>]:
  \<comment> \<open>Gen_Synthesis_Rule_step_value\<close>
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> (f \<bind> (\<lambda>v. F (\<phi>V_pair v vs)))
                                 \<lbrace> R\<heavy_comma> \<blangle> Xr vs \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. (ExSet Xr \<heavy_comma> E1 e) + EF e)))
            ((\<p>\<r>\<o>\<c> f \<lbrace> R \<longmapsto> \<lambda>ret. R1\<heavy_comma> \<blangle> X ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis) &&& PROP Ant)
            Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R1 \<heavy_comma> \<blangle> Xr (\<phi>V_snd vs) \<heavy_comma> X (\<phi>V_fst vs) \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EF))
            Ant Result \<close>
  unfolding Gen_Synthesis_Rule_def FOCUS_TAG_def conjunction_imp
  subgoal premises prems apply (rule prems(1))
\<medium_left_bracket> premises f and A
  f
  apply_rule prems(2)[OF A]
\<medium_right_bracket>. .

lemma [\<phi>reason 1200]: \<comment> \<open>Gen_Synthesis_Rule_step_value the last\<close>
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>_::unit \<phi>arg. \<p>\<r>\<o>\<c> (f \<bind> F) \<lbrace> R\<heavy_comma> \<blangle> Xr \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. (Xr\<heavy_comma> E1 e) + EF e)))
            (\<p>\<r>\<o>\<c> f \<lbrace> R \<longmapsto> \<lambda>ret. R1\<heavy_comma> \<blangle> X ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis &&& PROP Ant)
            Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> F v \<lbrace> R1\<heavy_comma> \<blangle> Xr\<heavy_comma> X v \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EF))
            Ant Result \<close>
  unfolding Gen_Synthesis_Rule_def FOCUS_TAG_def conjunction_imp
  subgoal premises prems apply (rule prems(1))
    \<medium_left_bracket> premises f and A
      f
      apply_rule prems(2)[OF A]
    \<medium_right_bracket> . .

lemma [\<phi>reason 1200]: \<comment> \<open>Gen_Synthesis_Rule final\<close>
  \<open> (\<And>e. Remove_Values (E e) (E' e))
\<Longrightarrow> Simplify (assertion_simps ABNORMAL) E'' E'
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>_::unit \<phi>arg. \<p>\<r>\<o>\<c> F \<lbrace> R\<heavy_comma> \<blangle> Void \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant
            (PROP Ant \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> R \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'' @action synthesis)\<close>
  unfolding Gen_Synthesis_Rule_def FOCUS_TAG_def Remove_Values_def Simplify_def Action_Tag_def
  subgoal premises P
    apply (unfold P(2))
    using P(3)[OF P(4), THEN spec, THEN \<phi>CONSEQ'E[OF view_shift_by_implication, OF P(1)],
            simplified] . .

lemma [\<phi>reason 1210]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> (f \<ggreater> F v) \<lbrace> R\<heavy_comma> \<blangle> Xr v \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. (ExSet Xr\<heavy_comma> E1 e) + EF e)))
            (\<p>\<r>\<o>\<c> f \<lbrace> R \<longmapsto> R1\<heavy_comma> \<blangle> X \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis &&& PROP Ant) Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>v. \<p>\<r>\<o>\<c> F v \<lbrace> R1\<heavy_comma> \<blangle> Xr v\<heavy_comma> X \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EF))
            Ant Result \<close>
  unfolding Gen_Synthesis_Rule_def FOCUS_TAG_def conjunction_imp
  subgoal premises prems apply (rule prems(1))
    \<medium_left_bracket> premises f and A
      f
      apply_rule prems(2)[OF A]
    \<medium_right_bracket> . .


lemma [\<phi>reason 2000]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Rx vs \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Rx vs\<heavy_comma> Void \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def by simp

lemma [\<phi>reason 2000]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Rx vs\<heavy_comma> X vs \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Rx vs\<heavy_comma> \<blangle> X vs \<brangle> \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def FOCUS_TAG_def by simp

lemma [\<phi>reason 2000]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F \<lbrace> R\<heavy_comma> \<blangle> Rx vs\<heavy_comma> X vs \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F \<lbrace> R\<heavy_comma> \<blangle> Rx vs\<heavy_comma> SMORPH X vs \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def FOCUS_TAG_def by simp

lemma [\<phi>reason 2000]:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Rx vs\<heavy_comma>  A vs\<heavy_comma> B vs  \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Rx vs\<heavy_comma> (A vs\<heavy_comma> B vs) \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def FOCUS_TAG_def by (simp add: mult.assoc)


subsection \<open>Entry Point\<close>

lemma Gen_Synthesis_Rule_start_proc:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Void\<heavy_comma> X vs \<brangle> \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. R \<heavy_comma> E e)))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def by (simp add: \<phi>frame)

lemma Gen_Synthesis_Rule_start_proc_focus_the_last:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Void\<heavy_comma> X vs \<brangle> \<longmapsto> \<lambda>ret. R\<heavy_comma> Yr ret\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. R \<heavy_comma> E e)))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. Yr ret\<heavy_comma> Y ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def by (simp add: \<phi>frame mult.assoc)

lemma Gen_Synthesis_Rule_start_proc_having_target:
  \<open> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> R\<heavy_comma> \<blangle> Void\<heavy_comma> X vs \<brangle> \<longmapsto> \<lambda>ret. R\<heavy_comma> Y ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. R \<heavy_comma> E e)))
            Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def by (simp add: \<phi>frame)

\<phi>reasoner_ML Gen_Synthesis_Rule_start_proc 10
    (\<open>PROP Gen_Synthesis_Rule (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> ?Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E)) (PROP _) (PROP _)\<close>)
  = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
    let fun dest_proc (Const (\<^const_name>\<open>Gen_Synthesis_Rule\<close>, _) $ tm $ _ $ _) = dest_proc tm
          | dest_proc (Const (\<^const_name>\<open>Trueprop\<close>, _) $ tm) = dest_proc tm
          | dest_proc (Const (\<^const_name>\<open>All\<close>, _) $ tm) = dest_proc tm
          | dest_proc (Abs (_,_,tm)) = dest_proc tm
          | dest_proc tm = Phi_Syntax.dest_procedure tm
        val (_,X,Y,_) = dest_proc (Thm.major_prem_of sequent)
        fun chk_target (Abs (_,_,tm)) = chk_target tm
          | chk_target (Const (\<^const_name>\<open>ExSet\<close>, _) $ _)
              = error ("Exisential quantification has not been supported in synthesis.")
          | chk_target (Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _)
              = Phi_Reasoner.bad_config "Subjection shouldn't occur here."
          | chk_target (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _)
              = @{thm Gen_Synthesis_Rule_start_proc_having_target}
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _))
              = @{thm Gen_Synthesis_Rule_start_proc_having_target}
          | chk_target (Const (\<^const_name>\<open>times\<close>, _) $ A $ B)
              = (warning "You have multiple separated items and it is unclear which one is \
                     \the target to be synthesised or the residue of the synthesis.\n\
                     \We assume the synthesis target is the last item.\n\
                     \You should use \<open> Residue \<heavy_comma> \<blangle> Target \<brangle> \<close> to annotate the target, \
                     \or \<open> \<blangle> Target \<brangle> \<close> if there is no residue.";
                 @{thm Gen_Synthesis_Rule_start_proc_focus_the_last})
          | chk_target _ = @{thm Gen_Synthesis_Rule_start_proc}
     in case X
          of Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _)
               => NONE
           | _ => SOME ((ctxt, (chk_target Y) RS sequent), Seq.empty)
    end)\<close>

hide_fact Gen_Synthesis_Rule_start_proc_having_target Gen_Synthesis_Rule_start_proc

lemma [\<phi>reason 1200]:
  \<open> WARNING TEXT(\<open>Pure fact\<close> P \<open>will be discarded in the synthesis.\<close>)
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)) Ant Result
\<Longrightarrow> PROP Gen_Synthesis_Rule
            (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> \<lambda>v. Y v \<s>\<u>\<b>\<j> P v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)) Ant Result\<close>
  unfolding Gen_Synthesis_Rule_def
  subgoal premises prems apply (rule prems(2))
    \<medium_left_bracket> premises Ant
      apply_rule prems(3)[OF Ant]
    \<medium_right_bracket> . .

subsection \<open>Tools\<close>

lemma make_synthesis_rule:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          ((\<And>vs. X' vs \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X vs \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action synthesis)\<close>
  unfolding Gen_Synthesis_Rule_def
  \<medium_left_bracket> premises E[assertion_simps] and F and X and A
    X
    apply_rule F[OF A]
  \<medium_right_bracket> .

lemma make_synthesis_rule':
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R'\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          ((\<And>vs. X' vs \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X vs \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<w>\<i>\<t>\<h> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. R'\<heavy_comma> R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action synthesis)\<close>
  unfolding FOCUS_TAG_def
  using make_synthesis_rule[unfolded FOCUS_TAG_def, where Y = \<open>\<lambda>v. R\<heavy_comma> Y v\<close>, folded mult.assoc] .




subsection \<open>Overloaded Synthesis\<close>


consts overloaded_synthesis :: action

declare [[\<phi>reason_default_pattern
      \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?x \<Ztypecolon> ?Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action overloaded_synthesis\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?x \<Ztypecolon> ?Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' @action overloaded_synthesis\<close> (100)
and   \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action overloaded_synthesis\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' @action overloaded_synthesis\<close> (90),

   generate_pattern_of_synthesis_rule
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis\<close>  (110)
  and \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis\<close>  (110)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis\<close>  (120)
  and \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis &&& TERM ()\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action overloaded_synthesis\<close>  (120)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action overloaded_synthesis &&& TERM ?Y'\<close>
   \<Rightarrow> \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' @action overloaded_synthesis\<close> (110)
  and \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action overloaded_synthesis &&& TERM ?Y'\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' @action overloaded_synthesis\<close> (110)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action overloaded_synthesis &&& (TERM ?X' &&& TERM ?Y')\<close>
   \<Rightarrow> \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X' \<longmapsto> \<lambda>ret. ?Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' @action overloaded_synthesis\<close> (110)
  and \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action overloaded_synthesis &&& (TERM ?X' &&& TERM ?Y')\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> ?X' vs \<longmapsto> \<lambda>ret. ?Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' @action overloaded_synthesis\<close> (110)
]]


consts synthesis_pattern1 :: \<open>'ret::{} \<Rightarrow> 'any::{}\<close>
consts synthesis_pattern2 :: \<open>'arg::{} \<Rightarrow> 'ret::{} \<Rightarrow> 'any::{}\<close>

lemma [\<phi>reason 2000]:
  \<open> (\<And>vs. PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
      GIVEN
      (\<p>\<r>\<o>\<c> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis))
\<Longrightarrow> PROP Infer_Binding_Pattern
      (\<forall>vs. \<p>\<r>\<o>\<c> f  vs \<lbrace> X  vs \<longmapsto> Y  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action overloaded_synthesis)
      GIVEN
      (\<forall>vs. \<p>\<r>\<o>\<c> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 2100]:
  \<open> (\<And>vs. PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
      (synthesis_pattern2 (XX vs) YY)
      (\<p>\<r>\<o>\<c> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis))
\<Longrightarrow> PROP Infer_Binding_Pattern
      (\<forall>vs. \<p>\<r>\<o>\<c> f  vs \<lbrace> X  vs \<longmapsto> Y  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action overloaded_synthesis)
      (synthesis_pattern2 XX YY)
      (\<forall>vs. \<p>\<r>\<o>\<c> f' vs \<lbrace> X' vs \<longmapsto> Y' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1050]:
  \<open> PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f  \<lbrace> X  \<longmapsto> \<lambda>ret. Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action overloaded_synthesis)
      ()
      (\<p>\<r>\<o>\<c> f' \<lbrace> X' \<longmapsto> \<lambda>ret. Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1100]:
  \<open> PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f  \<lbrace> X  \<longmapsto> \<lambda>ret. Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action overloaded_synthesis)
      (synthesis_pattern1 Y')
      (\<p>\<r>\<o>\<c> f' \<lbrace> X' \<longmapsto> \<lambda>ret. Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1100]:
  \<open> PROP \<s>\<y>\<n>\<t>\<a>\<x>_prepend_speration RX X' X''
\<Longrightarrow> PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f  \<lbrace> X   \<longmapsto> \<lambda>ret. Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action overloaded_synthesis)
      (synthesis_pattern2 X' Y')
      (\<p>\<r>\<o>\<c> f' \<lbrace> X'' \<longmapsto> \<lambda>ret. Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1100]:
  \<open> PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f  \<lbrace> X  \<longmapsto> \<lambda>ret. x \<Ztypecolon> Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action overloaded_synthesis)
      ()
      (\<p>\<r>\<o>\<c> f' \<lbrace> X' \<longmapsto> \<lambda>ret. x \<Ztypecolon> Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .

lemma [\<phi>reason 1050]:
  \<open> PROP Infer_Binding_Pattern
      (\<p>\<r>\<o>\<c> f  \<lbrace> X  \<longmapsto> \<lambda>ret. x  \<Ztypecolon> Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  @action overloaded_synthesis)
      (synthesis_pattern1 x')
      (\<p>\<r>\<o>\<c> f' \<lbrace> X' \<longmapsto> \<lambda>ret. x' \<Ztypecolon> Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' @action overloaded_synthesis)\<close>
  unfolding Infer_Binding_Pattern_def .




(* \<forall>vs. \<p>\<r>\<o>\<c> op_add LENGTH(?'b) vs \<lbrace> ?X' vs \<longmapsto> \<lambda>ret. ?x + ?y \<Ztypecolon> \<v>\<a>\<l>[ret] \<nat>(?'b) \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. ?R\<heavy_comma> 0 e)
    @action overloaded_synthesis *)


(*IMPROVE ME!: for now we limit the optimal synthesis to be readonly.
But it is a deficiency! Use a larger range of search to address this!*)

lemma overloaded_synthesis_nullary:
  \<open> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R1 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R1\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding Action_Tag_def .


lemma overloaded_synthesis_unary:
  \<open> \<p>\<r>\<o>\<c> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> S1 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> H vs \<lbrace> R2 \<heavy_comma> S1 vs \<longmapsto> \<lambda>ret. R3 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
         \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (h1 \<bind> H) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (E1 + E) @action synthesis\<close>
  \<medium_left_bracket> premises H1 and H
    H1 H \<medium_right_bracket> .

lemma [\<phi>reason add]:
  \<open> (\<And>vs. S1 vs \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YY vs \<w>\<i>\<t>\<h> Any)
\<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> Return vs \<lbrace> R2 \<heavy_comma> S1 vs \<longmapsto> \<lambda>ret. R2 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace> @action overloaded_synthesis\<close>
  \<medium_left_bracket> premises I
    I
    \<medium_right_bracket> .


lemma overloaded_synthesis_binary:
  \<open> \<p>\<r>\<o>\<c> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> S1 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> h2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> S2 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> H vs \<lbrace> R3 \<heavy_comma> S1 (\<phi>V_snd vs) \<heavy_comma> S2 (\<phi>V_fst vs) \<longmapsto> \<lambda>ret. R4\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
         \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (h1 \<bind> (\<lambda>v1. h2 \<bind> (\<lambda>v2. H (\<phi>V_pair v2 v1))))
      \<lbrace> R1 \<longmapsto> \<lambda>ret. R4\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + ((\<exists>*v. S1 v)\<heavy_comma> E2 e) + E e) @action synthesis\<close>
  \<medium_left_bracket> premises H1 and H2 and H
    H1 H2 H \<medium_right_bracket> .

lemma overloaded_synthesis_ternary:
  \<open> \<p>\<r>\<o>\<c> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret::VAL \<phi>arg. R2\<heavy_comma> \<blangle> S1 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> h2 \<lbrace> R2 \<longmapsto> \<lambda>ret::VAL \<phi>arg. R3\<heavy_comma> \<blangle> S2 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> h3 \<lbrace> R3 \<longmapsto> \<lambda>ret::VAL \<phi>arg. R4\<heavy_comma> \<blangle> S3 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E3 @action synthesis
\<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> H vs \<lbrace> R4 \<heavy_comma> S1 (\<phi>V_snd (\<phi>V_snd vs)) \<heavy_comma> S2 (\<phi>V_fst (\<phi>V_snd vs)) \<heavy_comma> S3 (\<phi>V_fst vs)
                  \<longmapsto> \<lambda>ret. R5 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
         \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (h1 \<bind> (\<lambda>v1. h2 \<bind> (\<lambda>v2. h3 \<bind> (\<lambda>v3. H (\<phi>V_pair v3 (\<phi>V_pair v2 v1))))))
      \<lbrace> R1 \<longmapsto> \<lambda>ret. R5\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + ((\<exists>*v. S1 v)\<heavy_comma> E2 e) + ((\<exists>*v. S1 v)\<heavy_comma> (\<exists>*v. S2 v)\<heavy_comma> E3 e) + E e)
    @action synthesis\<close>
  \<medium_left_bracket> premises H1 and H2 and H3 and H
    H1 H2 H3 H
  \<medium_right_bracket> .

lemma make_overloaded_synthesis_rule:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          ((\<And>vs. X' vs \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X vs \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action overloaded_synthesis)\<close>
  unfolding Gen_Synthesis_Rule_def
  \<medium_left_bracket> premises E[assertion_simps] and F and X and A
    X
    apply_rule F[OF A]
  \<medium_right_bracket> .

lemma make_overloaded_synthesis_rule':
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R'\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          ((\<And>vs. X' vs \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X vs \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<w>\<i>\<t>\<h> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. R'\<heavy_comma> R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action overloaded_synthesis)\<close>
  unfolding FOCUS_TAG_def
  using make_overloaded_synthesis_rule[unfolded FOCUS_TAG_def, where Y = \<open>\<lambda>v. R\<heavy_comma> Y v\<close>, folded mult.assoc] .

ML_file \<open>library/additions/overloaded_synthesis.ML\<close>

attribute_setup overloaded_operator_in_synthesis = \<open>
  Scan.peek (fn ctxt =>
    Scan.optional Parse.int 60 --
    Parse.position (
        (( (\<^keyword>\<open>(\<close> -- \<^keyword>\<open>)\<close>) >> (K []) || Scan.repeat Parse.term)
       --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) -- Parse.term
          >> (fn (A,Y) =>
              let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic (Context.proof_of ctxt)
                  val terms = map (Type.constraint \<^typ>\<open>_ \<phi>arg \<Rightarrow> assn\<close> o Syntax.parse_term ctxt') (Y::A)
                           |> Syntax.check_terms ctxt'
                  val ctxt'' = fold Proof_Context.augment terms ctxt'
                  val (Y'::A') = Variable.export_terms ctxt'' ctxt' terms
               in Phi_Synthesis.Signat (A',Y')
              end))
      || (Parse.term >>
            (Phi_Synthesis.Operator o Context.cases Syntax.read_term_global Syntax.read_term ctxt)))
>> (fn (priority, (signat, pos)) =>
      Thm.declaration_attribute (K (
        Phi_Synthesis.declare_overloaded_operator signat pos priority))))
\<close>


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
    val (V'',S'') = Procedure_Syntax.package_values0
                            "\<v>\<s>" (TVar (("ret", Thm.maxidx_of sequent),\<^sort>\<open>VALs\<close>)) true NONE S
          |> apply2 (Thm.cterm_of ctxt)
   in Drule.infer_instantiate_types ctxt [(S',S''),(V',V'')] sequent
          |> (fn th => @{thm Collect_Return_Values_I} RS th)
          |> pair ctxt |> Seq.single
  end
\<close>

lemma [\<phi>reason 2550]:
  \<open> Collect_Return_Values X S vs
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> collect_return_values S vs\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def FOCUS_TAG_def TAIL_def
  by simp

lemma [\<phi>reason 3200]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> collect_return_values 0 \<phi>V_none\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def FOCUS_TAG_def TAIL_def
  by simp


subsection \<open>Literal Evaluation\<close>

subsubsection \<open>Check\<close>

(*TODO: should use axiomatization since it is semantic-related*)
(*TODO: move me!*)

declare [[\<phi>premise_attribute? [\<phi>reason add] for \<open>Is_Literal _\<close>]]


subsubsection \<open>Evaluation\<close>

consts \<phi>mode_literal :: mode

lemma [\<phi>reason 1000]:
  \<open> Simplify default A B
\<Longrightarrow> Is_Literal A
\<Longrightarrow> Simplify \<phi>mode_literal A B\<close>
  unfolding Simplify_def atomize_eq .

lemma simplify_literal_implies_literal:
  \<open>Simplify \<phi>mode_literal A B \<Longrightarrow> Is_Literal A\<close>
  unfolding Is_Literal_def ..

declare [[
  \<phi>premise_attribute_ML \<open>fn _ => Thm.declaration_attribute (fn thm => fn ctxt =>
    let val term_A = case Thm.prop_of thm
                       of _ $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ _ ) => A
                        | _ $ (Const(\<^const_name>\<open>Simplify\<close>, _) $ _ $ A $ _ ) => A
        val cterm_A = Context.cases Thm.global_cterm_of Thm.cterm_of ctxt term_A
        val rule = Drule.infer_instantiate (Context.proof_of ctxt) [(("any",0), cterm_A)]
                                           @{thm Is_Literal_internal_rule}
     in Phi_Reasoner.add_rule Position.none Phi_Reasoner.LOCAL_CUT 1000
            ([(Thm.concl_of rule, NONE)], []) NONE [rule] ctxt
    end
    handle MATCH => ctxt
  )\<close> for \<open>Simplify \<phi>mode_literal _ _\<close>
]]

subsection \<open>Compilibility / Validity of Semantics\<close>

definition \<open>chk_semantics_validity x \<longleftrightarrow> True\<close> \<comment> \<open>A pure syntactic check and have no logical semantics\<close>

end
