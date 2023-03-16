chapter \<open>Reasoning Processes in IDE-CP - Part III\<close>

text \<open>Here we give the implementation of all large reasoning processes that are declared in
the previous part I.\<close>

theory IDE_CP_Reasoning3
  imports IDE_CP_App2 "HOL-Library.Word"
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


(* subsubsection \<open>General Rules\<close>

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>VAL ?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> VAL ?Y \<a>\<n>\<d> ?P\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> VAL X \<i>\<m>\<p>\<l>\<i>\<e>\<s> VAL Y \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>OBJ ?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> OBJ ?Y \<a>\<n>\<d> ?P\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> OBJ X \<i>\<m>\<p>\<l>\<i>\<e>\<s> OBJ Y \<a>\<n>\<d> P\<close>
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

lemma [\<phi>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy (A \<s>\<u>\<b>\<j> P) (A' \<s>\<u>\<b>\<j> P)"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 1000]: "SameNuTy A A" \<comment> \<open>The fallback\<close>
  unfolding SameNuTy_def ..


subsection \<open>Equation-based Cleaning\<close>

consts clean_automation_waste :: mode

declare [[\<phi>reason_default_pattern
    \<open>?X = _ @action clean_automation_waste\<close> \<Rightarrow> \<open>?X = _ @action clean_automation_waste\<close> (100)
]]

lemma [\<phi>reason 1000]:
  \<open>X = X @action clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200]:
  \<open>(() \<Ztypecolon> \<phi>None) = 1 @action clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_\<phi>None by simp

lemma [\<phi>reason 1200]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_\<phi>None by simp

(*TODO: the two rules are bad?*)
lemma [\<phi>reason 1200 for \<open>(?y \<Ztypecolon> \<circle>) = (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> ?Z) @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<circle>) = (() \<Ztypecolon> k \<^bold>\<rightarrow> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?y \<Ztypecolon> \<circle>) = (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?Z) @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<circle>) = (() \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi>perm_ins_homo ?\<psi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open> perm_ins_homo' \<psi>
\<Longrightarrow> (x \<Ztypecolon> \<phi>perm_ins_homo \<psi> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>perm_ins_homo_\<phi>None
  by simp

declare perm_ins_homo_pointwise[\<phi>reason 1200]
        perm_ins_homo_to_share[\<phi>reason 1200]

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?n \<Znrres> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> 0 < n
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> \<circle>) = (() \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>)) @action clean_automation_waste\<close>
  unfolding Action_Tag_def Premise_def \<phi>Share_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> ?T \<^emph> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'a::sep_magma_1 set) @action clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> \<circle> \<^emph> ?U) = ?Z @action clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'b::sep_magma_1 set) @action clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?r) \<Ztypecolon> (?T \<^emph> ?n \<Znrres> \<circle>)) = (?Z :: ?'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>]:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> 0 < n
\<Longrightarrow> ((x,r) \<Ztypecolon> (T \<^emph> n \<Znrres> \<circle>)) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>((?r,?x) \<Ztypecolon> (?n \<Znrres> \<circle> \<^emph> ?T)) = (?Z :: ?'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>]:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> 0 < n
\<Longrightarrow> ((r,x) \<Ztypecolon> (n \<Znrres> \<circle> \<^emph> T)) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)




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

\<^prop>\<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> fx \<Ztypecolon> T \<a>\<n>\<d> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> f \<Ztypecolon> T <func-over> x \<a>\<n>\<d> P\<close>

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
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> fx \<Ztypecolon> T \<a>\<n>\<d> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> f \<Ztypecolon> T <func-over> x \<a>\<n>\<d> P\<close>
  unfolding Imply_def lambda_abstraction_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> f x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> f \<Ztypecolon> T <func-over> x \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

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



section \<open>Transformation of Structural Abstraction\<close>

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

lemma [\<phi>reason 1200 for \<open>Structure_Info (\<phi>perm_ins_homo ?\<psi> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (\<phi>perm_ins_homo \<psi> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 30 for \<open>Structure_Info ?T ?P\<close>]:
  \<open> Structure_Info T True \<close>
  unfolding Structure_Info_def by blast


subsection \<open>Extract\<close>

text \<open>It is Separation of Abstraction!\<close>

text \<open>The canonical form is where all permission annotation are on leaves.
  It minimizes fragments. (TODO: move this)\<close>

definition Structural_Extract :: \<open>'a::sep_magma set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Structural_Extract From Remain To Residual Aux \<longleftrightarrow> (Residual * From \<i>\<m>\<p>\<l>\<i>\<e>\<s> Remain * To \<a>\<n>\<d> Aux)\<close>
  \<comment> \<open>Extract To from From, remaining Remain the unused part in From,
      and leaving Residual the part in To that fails to be obtained from From.\<close>

declare [[\<phi>reason_default_pattern
      \<open>Structural_Extract ?X _ ?Y _ _\<close> \<Rightarrow> \<open>Structural_Extract ?X _ ?Y _ _\<close> (100)
  and \<open>Structural_Extract ?X _ ?Y _ (Automatic_Morphism _ _ \<and> _)\<close> \<Rightarrow>
      \<open>Structural_Extract ?X _ ?Y _ (Automatic_Morphism _ _ \<and> _)\<close>          (110)
]]

lemma SE_clean_waste:
  \<open> Structural_Extract X R Y W P
\<Longrightarrow> R = R' @action clean_automation_waste
\<Longrightarrow> W = W' @action clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' P\<close>
  by simp

lemma SE_clean_waste':
  \<open> Structural_Extract X R Y W (Automatic_Morphism RP (Structural_Extract rY rW rX rR rP) \<and> P)
\<Longrightarrow>  R = R'  @action clean_automation_waste
\<Longrightarrow>  W = W'  @action clean_automation_waste
\<Longrightarrow> rR = rR' @action clean_automation_waste
\<Longrightarrow> rW = rW' @action clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' (Automatic_Morphism RP (Structural_Extract rY rW' rX rR' rP) \<and> P)\<close>
  by simp


lemma Structural_Extract_imply_P:
  \<open> Structural_Extract X R Y W P1
\<Longrightarrow> P1 \<longrightarrow> P2
\<Longrightarrow> Structural_Extract X R Y W P2\<close>
  unfolding Structural_Extract_def Imply_def by blast


lemma Structural_Extract_reverse_morphism_I[intro?]:
  \<open> Structural_Extract X R Y W P
\<Longrightarrow> RP \<longrightarrow> RX
\<Longrightarrow> Structural_Extract X R Y W (Automatic_Morphism RP RX \<and> P)\<close>
  unfolding Morphism_def Structural_Extract_def Imply_def
  by blast


paragraph \<open>Termination\<close>

lemma Structural_Extract_\<phi>None_right [\<phi>reason 3000]:
  \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract X X (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) True\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .

lemma Structural_Extract_\<phi>None_left [\<phi>reason 3000]:
  \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X X True\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .

lemma Structural_Extract_1_right [\<phi>reason 3000]:
  \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract X X 1 1 True\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .

lemma Structural_Extract_1_left [\<phi>reason 3000]:
  \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract 1 1 X X True\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .


(*TODO: BUG: need to check the case where Y requires only partial share permission but
    this rule may give it the total.*)
lemma Structural_Extract_exact:
  \<comment> \<open>The current object X is exactly what we want to extract.\<close>
  \<open>Structural_Extract X (() \<Ztypecolon> \<phi>None) X (() \<Ztypecolon> \<phi>None) True\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right Action_Tag_def
  using implies_refl .

declare Structural_Extract_exact
  [THEN SE_clean_waste, \<phi>reason 3000 for \<open>Structural_Extract ?X ?R ?Y ?W ?P\<close>]

lemma [
  THEN SE_clean_waste',
  \<phi>reason 3011 for \<open>Structural_Extract ?X ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>
]: \<comment> \<open>The current object X is exactly what we want to extract.\<close>
  \<open>Structural_Extract X  (() \<Ztypecolon> \<phi>None) X  (() \<Ztypecolon> \<phi>None)
    (Automatic_Morphism True (Structural_Extract X' (() \<Ztypecolon> \<phi>None) X' (() \<Ztypecolon> \<phi>None) True) \<and> True)\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_exact [unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)


lemma [\<phi>reason 3011]:
  \<open>Structural_Extract X X (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None)
   (Automatic_Morphism True (Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X' X' True) \<and> True)\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>None_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>None_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011]:
  \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X X
    (Automatic_Morphism True (Structural_Extract X' X' (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) True) \<and> True)\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>None_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>None_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011]:
  \<open>Structural_Extract X X 1 1 (Automatic_Morphism True (Structural_Extract 1 1 X' X' True) \<and> True)\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_1_left [unfolded Action_Tag_def]
                   Structural_Extract_1_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011]:
  \<open>Structural_Extract 1 1 X X (Automatic_Morphism True (Structural_Extract X' X' 1 1 True) \<and> True)\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding Action_Tag_def
  by (blast intro: Structural_Extract_1_left [unfolded Action_Tag_def]
                   Structural_Extract_1_right[unfolded Action_Tag_def]
                   Structural_Extract_reverse_morphism_I)




paragraph \<open>Fall back\<close>

lemma Structural_Extract_fallback
  [\<phi>reason 10 for \<open>Try ?S (Structural_Extract _ _ _ _ _)\<close>]:
  \<open> Try False (Structural_Extract X X Y Y True) \<close>
  for X :: \<open>'a::sep_ab_semigroup set\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left Action_Tag_def Try_def
  by (simp add: implies_refl mult.commute)

lemma [\<phi>reason 10 for \<open>Try ?S (Structural_Extract _ _ _ _ (Automatic_Morphism _ _ \<and> _))\<close>]:
  \<open> Try False (Structural_Extract X  X  Y  Y
      (Automatic_Morphism True (Structural_Extract X' X' Y' Y' True) \<and> True)) \<close>
  for X :: \<open>'a::sep_ab_semigroup set\<close> and X' :: \<open>'aa::sep_ab_semigroup set\<close>
  unfolding Action_Tag_def Try_def
  by (blast intro: Structural_Extract_fallback[unfolded Action_Tag_def Try_def]
                   Structural_Extract_reverse_morphism_I)



paragraph \<open>Terminations for Specific Node\<close>

lemma Structural_Extract_\<phi>Some [\<phi>reason 1200]:
  \<open> \<r>REQUIRE x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<black_circle> T) (() \<Ztypecolon> \<phi>None) (y \<Ztypecolon> \<black_circle> U) (() \<Ztypecolon> \<phi>None) P\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left Action_Tag_def \<r>Require_def
  using \<phi>Some_cast .

lemma [\<phi>reason 1211]:
  \<open> \<r>REQUIRE x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<black_circle> T) (() \<Ztypecolon> \<phi>None) (y \<Ztypecolon> \<black_circle> U) (() \<Ztypecolon> \<phi>None)
      (Automatic_Morphism (y' \<Ztypecolon> U' \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P')
            (Structural_Extract (y' \<Ztypecolon> \<black_circle> U') (() \<Ztypecolon> \<phi>None) (x' \<Ztypecolon> \<black_circle> T') (() \<Ztypecolon> \<phi>None) P')
      \<and> P)\<close>
  unfolding Action_Tag_def \<r>Require_def
  by (blast intro: Structural_Extract_\<phi>Some[unfolded Action_Tag_def \<r>Require_def]
                   Structural_Extract_reverse_morphism_I)

(*TODO: According to @{thm Agreement_times}, there must be a reasoning mechanism for \<inter>\<^sub>\<phi>
  It scatters information using \<inter>\<^sub>\<phi>

The bellowing reasoning is too weak! *)


lemma Structural_Extract_aggrement_to [\<phi>reason 1200]:
  \<open> \<r>REQUIRE x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>) P\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left Action_Tag_def \<r>Require_def
  apply (cases C; simp)
  \<medium_left_bracket> premises A
    dup
    Agreement_cast[OF A]
  \<medium_right_bracket>.
  using Agreement_cast .


lemma Structural_Extract_aggrement_from:
  \<open> \<r>REQUIRE y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T \<a>\<n>\<d> P
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>) (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) P\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left Action_Tag_def \<r>Require_def
  apply (cases C; simp)
  \<medium_left_bracket> premises A
    Agreement_cast[OF A]
    Agreement_shrink
  \<medium_right_bracket>.
  using Agreement_cast .


lemma [\<phi>reason 1211]:
  \<open> \<r>REQUIRE x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>)
      (Automatic_Morphism (y' \<Ztypecolon> U' \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P')
          (Structural_Extract (y' \<Ztypecolon> Agreement U') (() \<Ztypecolon> \<circle>) (x' \<Ztypecolon> Agreement T') (x' \<Ztypecolon> Agreement T' ?\<^sub>\<phi> C') P')
      \<and> P)\<close>
  unfolding Action_Tag_def \<r>Require_def
  by (blast intro: Structural_Extract_aggrement_to  [unfolded Action_Tag_def \<r>Require_def]
                   Structural_Extract_aggrement_from[unfolded Action_Tag_def \<r>Require_def]
                   Structural_Extract_reverse_morphism_I)



paragraph \<open>Normalize the Target\<close>

lemma Structural_Extract_to_mult:
  \<open> Try S1 (Structural_Extract A B Y WY P1)
\<Longrightarrow> Try S2 (Structural_Extract B C X WX P2)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<r>\<e>\<m> S1 \<or> S2
\<Longrightarrow> Structural_Extract A C (X * Y) (WX * WY) (P1 \<and> P2)\<close>
  for X :: \<open>'a::sep_algebra set\<close>
  unfolding Structural_Extract_def Simplify_def Action_Tag_def Try_def
  \<medium_left_bracket> premises L and R
    L[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
    R[THEN implies_right_prod]
  \<medium_right_bracket>. .

declare Structural_Extract_to_mult [THEN SE_clean_waste, \<phi>reason 1200]

lemma Structural_Extract_\<phi>Prod_right:
  \<open> Try S1 (Structural_Extract A B (y \<Ztypecolon> Y) (wy \<Ztypecolon> WY) P1)
\<Longrightarrow> Try S2 (Structural_Extract B C (x \<Ztypecolon> X) (wx \<Ztypecolon> WX) P2)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<r>\<e>\<m> S1 \<or> S2
\<Longrightarrow> Structural_Extract A C ((y,x) \<Ztypecolon> Y \<^emph> X) ((wy, wx) \<Ztypecolon> WY \<^emph> WX) (P1 \<and> P2)\<close>
for A :: \<open>'a::sep_algebra set\<close>
  unfolding \<phi>Prod_expn'
  using Structural_Extract_to_mult .

declare Structural_Extract_\<phi>Prod_right [THEN SE_clean_waste, \<phi>reason 1200]

paragraph \<open>Step by Step\<close>

lemma Structural_Extract_from_mult:
  \<open> Try S1 (Structural_Extract X R2 Y Wr P1)
\<Longrightarrow> Try S2 (Structural_Extract L R Wr Wr2 P2)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<r>\<e>\<m> S1 \<or> S2
\<Longrightarrow> Structural_Extract (L * X) (R * R2) Y Wr2 (P1 \<and> P2)\<close>
  for X :: \<open>'a::sep_algebra set\<close>
  unfolding Structural_Extract_def Simplify_def Try_def
  \<medium_left_bracket> premises R and L
    fold mult.assoc
    L[THEN implies_right_prod]
    R[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  \<medium_right_bracket>. .

declare Structural_Extract_from_mult [THEN SE_clean_waste,  \<phi>reason 1200]

lemma Structural_Extract_\<phi>Prod_left:
  \<open> Try S1 (Structural_Extract (x \<Ztypecolon> T) (r2 \<Ztypecolon> R2) Y W P1)
\<Longrightarrow> Try S2 (Structural_Extract (y \<Ztypecolon> U) (r \<Ztypecolon> R) W W2 P2)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<r>\<e>\<m> S1 \<or> S2
\<Longrightarrow> Structural_Extract ((x,y) \<Ztypecolon> T \<^emph> U) ((r2,r) \<Ztypecolon> (R2 \<^emph> R)) Y W2 (P1 \<and> P2)\<close>
  for T :: \<open>('a::sep_algebra,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' Simplify_def Try_def
  \<medium_left_bracket> premises R and L
    fold mult.assoc
    L[THEN implies_right_prod]
    R[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  \<medium_right_bracket>. .

declare Structural_Extract_\<phi>Prod_left [THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Try S1 (Structural_Extract A B (y \<Ztypecolon> Y) (wy \<Ztypecolon> WY)
      (Automatic_Morphism RP1 (Structural_Extract (y' \<Ztypecolon> Y') (wy' \<Ztypecolon> WY') A' B' P1') \<and> P1))
\<Longrightarrow> Try S2 (Structural_Extract B C (x \<Ztypecolon> X) (wx \<Ztypecolon> WX)
      (Automatic_Morphism RP2 (Structural_Extract (x' \<Ztypecolon> X') (wx' \<Ztypecolon> WX') B' C' P2') \<and> P2))
\<Longrightarrow> \<s>\<i>\<m>\<p>\<r>\<e>\<m> S1 \<or> S2
\<Longrightarrow> Structural_Extract A C ((y,x) \<Ztypecolon> Y \<^emph> X) ((wy, wx) \<Ztypecolon> WY \<^emph> WX)
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2)
        (Structural_Extract ((y',x') \<Ztypecolon> Y' \<^emph> X') ((wy', wx') \<Ztypecolon> WY' \<^emph> WX') A' C' (P1' \<and> P2'))
      \<and> P1 \<and> P2)\<close>
  for A :: \<open>'a::sep_algebra set\<close> and A' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def Try_def
  by (blast intro: Structural_Extract_\<phi>Prod_right[unfolded Action_Tag_def Try_def]
                   Structural_Extract_\<phi>Prod_left [unfolded Action_Tag_def Try_def]
                   Structural_Extract_imply_P)

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Try S1 (Structural_Extract (x \<Ztypecolon> T) (r2 \<Ztypecolon> R2) Y W
      (Automatic_Morphism RP1 (Structural_Extract Y' W' (x' \<Ztypecolon> T') (r2' \<Ztypecolon> R2') P1') \<and> P1))
\<Longrightarrow> Try S2 (Structural_Extract (y \<Ztypecolon> U) (r \<Ztypecolon> R) W W2
      (Automatic_Morphism RP2 (Structural_Extract W' W2' (y' \<Ztypecolon> U') (r' \<Ztypecolon> R') P2') \<and> P2))
\<Longrightarrow> Structural_Extract ((x,y) \<Ztypecolon> T \<^emph> U) ((r2,r) \<Ztypecolon> (R2 \<^emph> R)) Y W2
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2)
          (Structural_Extract Y' W2' ((x',y') \<Ztypecolon> T' \<^emph> U') ((r2',r') \<Ztypecolon> (R2' \<^emph> R')) (P1' \<and> P2')) \<and> P1 \<and> P2)\<close>
  for Y :: \<open>'a::sep_algebra set\<close> and Y' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def Try_def
  by (blast intro: Structural_Extract_\<phi>Prod_right[unfolded Action_Tag_def Try_def]
                   Structural_Extract_\<phi>Prod_left [unfolded Action_Tag_def Try_def]
                   Structural_Extract_imply_P)

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Try S1 (Structural_Extract A B Y WY
      (Automatic_Morphism RP1 (Structural_Extract Y' WY' A' B' P1') \<and> P1))
\<Longrightarrow> Try S2 (Structural_Extract B C X WX
      (Automatic_Morphism RP2 (Structural_Extract X' WX' B' C' P2') \<and> P2))
\<Longrightarrow> Structural_Extract A C (X * Y) (WX * WY)
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2) (Structural_Extract (X' * Y') (WX' * WY') A' C' (P1' \<and> P2')) \<and> P1 \<and> P2)\<close>
  for X :: \<open>'a::sep_algebra set\<close> and X' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def Try_def
  by (blast intro: Structural_Extract_to_mult  [unfolded Action_Tag_def Try_def]
                   Structural_Extract_from_mult[unfolded Action_Tag_def Try_def]
                   Structural_Extract_imply_P)

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

lemma Structural_Extract_\<phi>MapAt:
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> k' = k
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (yr \<Ztypecolon> k \<^bold>\<rightarrow> Ur) P\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def
  apply (simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_\<phi>Prod[symmetric])
  by (rule \<phi>MapAt_cast)

declare Structural_Extract_\<phi>MapAt[THEN SE_clean_waste, \<phi>reason 1200]


lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> k' = k
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (w \<Ztypecolon> k \<^bold>\<rightarrow> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U') (w' \<Ztypecolon> k \<^bold>\<rightarrow> W') (x' \<Ztypecolon> k \<^bold>\<rightarrow> T') (r' \<Ztypecolon> k \<^bold>\<rightarrow> R') P') \<and> P)\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def \<r>Require_def
  by (blast intro: Structural_Extract_\<phi>MapAt[unfolded Action_Tag_def \<r>Require_def]
                   Structural_Extract_imply_P)


lemma Structural_Extract_\<phi>MapAt_L:
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> k' = k
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (yr \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Ur) P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def
  apply (simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric])
  thm \<phi>MapAt_L_\<phi>Prod[symmetric]
  by (rule \<phi>MapAt_L_cast)

declare Structural_Extract_\<phi>MapAt_L [THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> k' = k
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (yr' \<Ztypecolon> Ur') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (yr \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Ur)
      (Automatic_Morphism RP
        (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (yr' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ Ur') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)\<close>
for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def \<r>Require_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L[unfolded Action_Tag_def \<r>Require_def]
                   Structural_Extract_imply_P)



lemma Structural_Extract_\<phi>MapAt_L_pad_left:
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> length k < length k'
&&& \<s>\<i>\<m>\<p>\<r>\<e>\<m> k @ kd = k'
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W) P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def \<r>Require_def conjunction_imp
  subgoal premises prems
    apply (insert prems(3),
       simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric]
          \<phi>MapAt_L_\<phi>MapAt_L[symmetric, of k kd, unfolded prems(2)])
    by (rule \<phi>MapAt_L_cast) .

declare Structural_Extract_\<phi>MapAt_L_pad_left [THEN SE_clean_waste, \<phi>reason 1180]


lemma Structural_Extract_\<phi>MapAt_L_pad_right:
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> length k' < length k
&&& \<s>\<i>\<m>\<p>\<r>\<e>\<m> k' @ kd = k
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W) P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def \<r>Require_def conjunction_imp
  subgoal premises prems
    apply (insert prems(3),
       simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric]
          \<phi>MapAt_L_\<phi>MapAt_L[symmetric, of k' kd, unfolded prems(2)])
    by (rule \<phi>MapAt_L_cast) .

declare Structural_Extract_\<phi>MapAt_L_pad_right [THEN SE_clean_waste, \<phi>reason 1150]


lemma [THEN SE_clean_waste', \<phi>reason 1183]:
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> length k < length k'
&&& \<s>\<i>\<m>\<p>\<r>\<e>\<m> k @ kd = k'
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP
        (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)

lemma [THEN SE_clean_waste', \<phi>reason 1153]:
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> length k' < length k
&&& \<s>\<i>\<m>\<p>\<r>\<e>\<m> k' @ kd = k
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP
        (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)


lemma Structural_Extract_\<phi>Map_L_norm_right [\<phi>reason 1200]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U) W P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) W P\<close>
  unfolding Structural_Extract_def Premise_def \<phi>MapAt_L_At .

lemma Structural_Extract_\<phi>Map_L_norm_left [\<phi>reason 1200]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W P\<close>
  unfolding Structural_Extract_def Premise_def \<phi>MapAt_L_At .


lemma [\<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Map_L_norm_right[unfolded Action_Tag_def]
                   Structural_Extract_\<phi>Map_L_norm_left [unfolded Action_Tag_def]
                   Structural_Extract_imply_P)

lemma [\<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T') R' P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow> T') R' P') \<and> P)\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Map_L_norm_right[unfolded Action_Tag_def]
                   Structural_Extract_\<phi>Map_L_norm_left [unfolded Action_Tag_def]
                   Structural_Extract_imply_P)



lemma Structural_Extract_\<phi>perm_ins_homo:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T)
                       (r \<Ztypecolon> \<phi>perm_ins_homo \<psi> R)
                       (y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U)
                       (w \<Ztypecolon> \<phi>perm_ins_homo \<psi> W)
                       P\<close>
  unfolding Structural_Extract_def Imply_def \<phi>Sep_Disj_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis (no_types, opaque_lifting) homo_sep_disj_semi_def homo_sep_mult.homo_mult perm_ins_homo'_def)

declare Structural_Extract_\<phi>perm_ins_homo[THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T)
                       (r \<Ztypecolon> \<phi>perm_ins_homo \<psi> R)
                       (y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U)
                       (w \<Ztypecolon> \<phi>perm_ins_homo \<psi> W)
       (Automatic_Morphism (RP \<and>\<^sub>\<r> \<phi>Sep_Disj R' U')
           (Structural_Extract (y' \<Ztypecolon> \<phi>perm_ins_homo \<psi> U')
                               (w' \<Ztypecolon> \<phi>perm_ins_homo \<psi> W')
                               (x' \<Ztypecolon> \<phi>perm_ins_homo \<psi> T')
                               (r' \<Ztypecolon> \<phi>perm_ins_homo \<psi> R')
                                P') \<and> P)\<close>
  unfolding Morphism_def Action_Tag_def Compact_Antecedent_def
  by (blast intro: Structural_Extract_\<phi>perm_ins_homo[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)



lemma Structural_Extract_\<phi>Optional_left [\<phi>reason 1200]:
  \<open> Structural_Extract (x \<Ztypecolon> T) R Y W P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T ?\<^sub>\<phi> True) R Y W P\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  by simp

lemma Structural_Extract_\<phi>Optional_right:
  \<open> Structural_Extract Y W (x \<Ztypecolon> T) R P
\<Longrightarrow> Structural_Extract Y W (x \<Ztypecolon> T ?\<^sub>\<phi> True) R P\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  by simp

lemma [\<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> T') R' P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T ?\<^sub>\<phi> True) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> T' ?\<^sub>\<phi> True) R' P') \<and> P)\<close>
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

lemma Structural_Extract_share_half:
    \<comment> \<open>if only requires a half of the permission, give it a half of that currently we have.\<close>
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half(m / 2) \<Znrres> U) (w \<Ztypecolon> W) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def half_def Action_Tag_def
  \<medium_left_bracket> premises [\<phi>reason] and X
    share_split_\<phi>app[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod]
    fold mult.assoc
    X[THEN implies_right_prod]
  \<medium_right_bracket>. .

declare Structural_Extract_share_half[THEN SE_clean_waste,
    \<phi>reason 1300 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?T) _ (?y \<Ztypecolon> half ?mmm \<Znrres> ?U) _ _\<close>]

lemma Structural_Extract_share_half_rev:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) P
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def Action_Tag_def \<phi>Prod_expn'
  \<medium_left_bracket> premises [\<phi>reason] and X
  have t1: \<open>(r \<Ztypecolon> R) * (x \<Ztypecolon> m / 2 \<Znrres> T) * (y \<Ztypecolon> m / 2 \<Znrres> U) = (r \<Ztypecolon> R) * (y \<Ztypecolon> m / 2 \<Znrres> U) * (x \<Ztypecolon> m / 2 \<Znrres> T)\<close>
    by (metis (mono_tags, lifting) mult.assoc mult.commute)
  ;; unfold t1
     X[THEN implies_right_prod]
     share_merge_\<phi>app[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod, folded mult.assoc]
  \<medium_right_bracket>. .

(* declare Structural_Extract_share_half_rev[THEN SE_clean_waste] *)

lemma
  [THEN SE_clean_waste',
   \<phi>reason 1311 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> half ?mmm \<Znrres> ?U) ?R2
      (Automatic_Morphism _ _ \<and> _)\<close>]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W)
    (Automatic_Morphism RP
        (Structural_Extract (y' \<Ztypecolon> m / 2 \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m / 2 \<Znrres> T') (r' \<Ztypecolon> R') P')
    \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half (m / 2) \<Znrres> U) (w \<Ztypecolon> W)
    (Automatic_Morphism (RP \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical T')
        (Structural_Extract (y' \<Ztypecolon> half (m / 2) \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m \<Znrres> T') ((x',r') \<Ztypecolon> m / 2 \<Znrres> T' \<^emph> R') P')
    \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Compact_Antecedent_def half_def
  by (blast intro: Structural_Extract_share_half    [unfolded Action_Tag_def half_def]
                   Structural_Extract_share_half_rev[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)



lemma Structural_Extract_share_eq:
  \<comment> \<open>If requires exactly what we have now, typically this happens after the previous rule or n = 1.\<close>
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> m = n
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W) P \<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn'[symmetric] Premise_def \<r>Require_def conjunction_imp
  apply (simp add: \<phi>Share_\<phi>Prod[symmetric])
  using \<phi>Share_transformation .

declare Structural_Extract_share_eq [THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> m = n
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W)
      (Automatic_Morphism RP
          (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> m \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Action_Tag_def \<r>Require_def conjunction_imp
  by (blast intro: Structural_Extract_share_eq[unfolded Action_Tag_def \<r>Require_def conjunction_imp]
                   Structural_Extract_imply_P)



lemma Structural_Extract_share_ge:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> 0 < n \<and> n < m
&&& \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' Action_Tag_def conjunction_imp \<r>Require_def
  \<medium_left_bracket> premises LE[unfolded Premise_def, useful] and [\<phi>reason] and X
    share_split_\<phi>app[where n=\<open>n\<close> and m=\<open>m-n\<close>, simplified]
    fold mult.assoc
    X[folded \<phi>Prod_expn', THEN \<phi>Share_transformation, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
        THEN implies_right_prod]
  have t1: \<open>(r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U) * (x \<Ztypecolon> m - n \<Znrres> T) = (x \<Ztypecolon> m - n \<Znrres> T) * (r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    using mult.assoc mult.commute by blast
  ;; unfold t1
  \<medium_right_bracket>. .

declare Structural_Extract_share_ge [THEN SE_clean_waste, \<phi>reason 1180]

lemma Structural_Extract_share_le:
  \<comment> \<open>If requires more than what we have, give all what we can give.\<close>
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> 0 < m \<and> m < n
&&& \<phi>Sep_Disj_Identical U
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' conjunction_imp \<r>Require_def
  \<medium_left_bracket> premises LE[unfolded Premise_def, useful] and SDI[\<phi>reason] and X
    X[folded \<phi>Prod_expn', THEN \<phi>Share_transformation, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
        THEN implies_left_prod, folded mult.assoc]

  have \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (y \<Ztypecolon> m \<Znrres> U) = (y \<Ztypecolon> n \<Znrres> U)\<close>
    using \<phi>Share_share[where n=\<open>n-m\<close> and m=m, simplified] \<phi>
    by (smt (verit) SDI)
  then have t1: \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> m \<Znrres> U) = (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute)
  ;; unfold t1
  \<medium_right_bracket>. .

declare Structural_Extract_share_le[THEN SE_clean_waste, \<phi>reason 1170]



lemma [THEN SE_clean_waste', \<phi>reason 1183]:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> 0 < n \<and> n < m
&&& \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W)
      (Automatic_Morphism (RP \<and>\<^sub>\<r> (\<s>\<i>\<m>\<p>\<r>\<e>\<m> m-n = mn) \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical T')
        (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> n \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') ((r',x') \<Ztypecolon> (n \<Znrres> R' \<^emph> mn \<Znrres> T')) P') \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Compact_Antecedent_def Premise_def
            conjunction_imp \<r>Require_def
  by (blast intro: Structural_Extract_share_ge[unfolded Action_Tag_def \<r>Require_def conjunction_imp]
                   Structural_Extract_share_le[unfolded Action_Tag_def \<r>Require_def conjunction_imp]
                   Structural_Extract_imply_P)

lemma [THEN SE_clean_waste', \<phi>reason 1173]:
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> 0 < m \<and> m < n
&&& \<phi>Sep_Disj_Identical U
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U)
      (Automatic_Morphism (RP \<and>\<^sub>\<r> (\<s>\<i>\<m>\<p>\<r>\<e>\<m> nm = n - m) \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical U')
        (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') ((w',y') \<Ztypecolon> m \<Znrres> W' \<^emph> nm \<Znrres> U') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Compact_Antecedent_def Premise_def conjunction_imp \<r>Require_def
  by (blast intro: Structural_Extract_share_ge[unfolded Action_Tag_def conjunction_imp \<r>Require_def]
                   Structural_Extract_share_le[unfolded Action_Tag_def conjunction_imp \<r>Require_def]
                   Structural_Extract_imply_P)


paragraph \<open>Normalization for Permission\<close>

subparagraph \<open>Extract each component in a composite structure, step by step\<close>

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W P
\<Longrightarrow> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W P\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) R Y W P
\<Longrightarrow> Structural_Extract ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) R Y W P\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2011]:
  \<open> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> T' \<^emph> n \<Znrres> U') W' X' R' P') \<and> P)
\<Longrightarrow> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W
      (Automatic_Morphism RP (Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> (T' \<^emph> U')) W' X' R' P') \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>Prod
  by blast

lemma [\<phi>reason 2011]:
  \<open> Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> T' \<^emph> n \<Znrres> U') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W P) \<and> P')
\<Longrightarrow> Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> (T' \<^emph> U')) W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W P) \<and> P')\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>Prod
  by blast


lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W P
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W P\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) R Y W P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) R Y W P\<close>
  for T :: \<open>('a::{share_one,sep_magma},'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2011]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T') W' X' R' P') \<and> P)
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T') W' X' R' P') \<and> P)\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt
  by blast

lemma [\<phi>reason 2011]:
  \<open> Structural_Extract (x' \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W P) \<and> P')
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W P) \<and> P')\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt
  by blast


lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) W P
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) W P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::{share_one,sep_magma}, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 2011]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T') R' P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::{share_one,sep_magma}, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast

lemma [\<phi>reason 2011]:
  \<open> Structural_Extract Y' W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) R Y W P) \<and> P')
\<Longrightarrow> Structural_Extract Y' W' (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) R Y W P) \<and> P')\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::{share_one,sep_magma}, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast



lemma [\<phi>reason 2000]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W P
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W P\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract (x \<Ztypecolon> n * m \<Znrres> T) R Y W P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) R Y W P\<close>
  unfolding Structural_Extract_def Action_Tag_def
  by (metis Imply_def Inhabited_def \<phi>Share_\<phi>Share \<phi>Share_inhabited set_mult_inhabited)

lemma [\<phi>reason 2011]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n * m \<Znrres> T') W' X' R' P') \<and> P)
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n \<Znrres> m \<Znrres> T') W' X' R' P') \<and> P)\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2011]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n * m \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W P) \<and> P')
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n \<Znrres> m \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W P) \<and> P')\<close>
  unfolding Premise_def by simp



text \<open>After all of these normalization, if we encounter the requirement to extract permission n,
  but there is no permission annotation for the current object, we know it is to extract from
  a total permission.\<close>

lemma Structural_Extract_pad_share_left
  [\<phi>reason 2000 except \<open>Structural_Extract (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W ?P\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W P\<close>
  by simp

lemma Structural_Extract_pad_share_right
  [\<phi>reason 2000 except \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R ?P\<close>]:
  \<open> Structural_Extract (y \<Ztypecolon> n \<Znrres> U) W (x \<Ztypecolon> 1 \<Znrres> T) R P
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> n \<Znrres> U) W (x \<Ztypecolon> T) R P\<close>
  by simp


lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x \<Ztypecolon> ?T) ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>
                 except \<open>Structural_Extract (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> 1 \<Znrres> T') R' P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> T') R' P') \<and> P)\<close>
  by simp

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x \<Ztypecolon> ?T) ?R (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>
                 except \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> 1 \<Znrres> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W P) \<and> P')
\<Longrightarrow> Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W P) \<and> P')\<close>
  by simp

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

consts branch_convergence :: \<open>action\<close>
       invoke_branch_convergence :: \<open>action\<close>

lemma [\<phi>reason 3000 for \<open>If _ _ _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ @action invoke_branch_convergence\<close>]:
  " Simplify (assertion_simps undefined) A' A
\<Longrightarrow> Simplify (assertion_simps undefined) B' B
\<Longrightarrow> If P A' B' \<i>\<m>\<p>\<l>\<i>\<e>\<s> C @action branch_convergence
\<Longrightarrow> If P A  B  \<i>\<m>\<p>\<l>\<i>\<e>\<s> C @action invoke_branch_convergence"
  unfolding Action_Tag_def Simplify_def
  by blast 

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

lemma [\<phi>reason 3000 for \<open>If ?P ?A ?A'' \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  "If P A A \<i>\<m>\<p>\<l>\<i>\<e>\<s> A @action branch_convergence"
  unfolding Action_Tag_def Imply_def by simp

subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3000 for \<open>If ?P ?A 0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  "If P A 0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> (A \<s>\<u>\<b>\<j> P) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (simp add: \<phi>expns zero_set_def)

lemma [\<phi>reason 3000 for \<open>If ?P 0 ?A \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  "If P 0 A \<i>\<m>\<p>\<l>\<i>\<e>\<s> (A \<s>\<u>\<b>\<j> \<not> P) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (simp add: \<phi>expns zero_set_def)


subsubsection \<open>Fallback\<close>

lemma [\<phi>reason 10 for \<open>If ?P ?A ?B = ?X @action branch_convergence\<close>]:
  "If P A B = If P A B @action branch_convergence"
  unfolding Action_Tag_def ..

text \<open>There is no fallback for \<^const>\<open>If\<close>. The If is not allowed to be fallback.
  If the convergence for If fails, the reasoning fails.\<close>

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 1400]:
  \<open> If P (L \<s>\<u>\<b>\<j> Q1 \<and> Q2) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> Z @action branch_convergence
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> Q1 \<s>\<u>\<b>\<j> Q2) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> Z @action branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1400]:
  \<open> If P L (R \<s>\<u>\<b>\<j> Q1 \<and> Q2) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Z @action branch_convergence
\<Longrightarrow> If P L (R \<s>\<u>\<b>\<j> Q1 \<s>\<u>\<b>\<j> Q2) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Z @action branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1300 for \<open>If ?P (?L \<s>\<u>\<b>\<j> ?QL) (?R \<s>\<u>\<b>\<j> ?QR) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  " If P QL QR = Q @action branch_convergence
\<Longrightarrow> If P L R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> QL) (R \<s>\<u>\<b>\<j> QR) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (X \<s>\<u>\<b>\<j> Q) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by force

lemma [\<phi>reason 1200
    for \<open>If ?P (?L \<s>\<u>\<b>\<j> ?Q) ?R \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>
]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " If P L R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> Q) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> (X \<s>\<u>\<b>\<j> P \<longrightarrow> Q) @action branch_convergence"
  unfolding Imply_def Action_Tag_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>If ?P ?L (?R \<s>\<u>\<b>\<j> ?Q) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " If P L R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P L (R \<s>\<u>\<b>\<j> Q) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (X \<s>\<u>\<b>\<j> \<not>P \<longrightarrow> Q) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by (simp add: \<phi>expns)


subsubsection \<open>Existential\<close>

lemma Conv_Merge_Ex_both_imp:
  "(\<And>x. If P (L x) (R x) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X x @action branch_convergence)
\<Longrightarrow> If P (\<exists>* x. L x) (\<exists>* x. R x) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; blast)

lemma Conv_Merge_Ex_R_imp
  [\<phi>reason 1100 for \<open>If ?P ?L (\<exists>* x. ?R x) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  "(\<And>x. If P L (R x) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X x @action branch_convergence)
\<Longrightarrow> If P L (\<exists>* x. R x) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (cases P; simp add: set_eq_iff \<phi>expns; blast)

lemma [\<phi>reason 1100 for \<open>If ?P (\<exists>* x. ?L x) ?R \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  "(\<And>x. If P (L x) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X x @action branch_convergence)
\<Longrightarrow> If P (\<exists>* x. L x) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<exists>* x. X x) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by (cases P; simp add: set_eq_iff \<phi>expns; blast)

text \<open>The merging recognize two existential quantifier are identical if their type and variable name
  are the same. If so it uses Conv_Merge_Ex_both to merge the quantification,
  or else the right side is expanded first.\<close>

\<phi>reasoner_ML Merge_Existential_imp 2000 (\<open>If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X\<close>) =
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

lemma [\<phi>reason 2000 for \<open>If ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  " If P x y = z @action branch_convergence
\<Longrightarrow> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (z \<Ztypecolon> Z) @action branch_convergence"
  unfolding Action_Tag_def Imply_def by (cases P; simp)

definition \<open>Branch_Convergence_Type_Pattern type the_type_to_match \<equiv> Trueprop True\<close>

lemma [\<phi>reason 10 for \<open>PROP Branch_Convergence_Type_Pattern ?X ?X'\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern X X\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200 for \<open>PROP Branch_Convergence_Type_Pattern (Val ?v ?T) (Val ?v ?T')\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern (Val v T) (Val v T')\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200 for \<open>If ?P (?L * (?x \<Ztypecolon> ?T)) ?R \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X @action branch_convergence\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern T T'
\<Longrightarrow> R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' * \<blangle> y \<Ztypecolon> T' \<brangle> \<a>\<n>\<d> Any
\<Longrightarrow> If P x y = z @action branch_convergence
\<Longrightarrow> If P T T' = Z @action branch_convergence
\<Longrightarrow> If P L R' \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P (L * (x \<Ztypecolon> T)) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * (z \<Ztypecolon> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def FOCUS_TAG_def
  by (smt (z3) Imply_def implies_right_prod)


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
  "\<s>\<i>\<m>\<p>\<r>\<e>\<m> a1 = a2
   \<Longrightarrow> EqualAddress (a1 \<Zinj> x1 \<Ztypecolon> T1) (a2 \<Zinj> x2 \<Ztypecolon> T2) "
  unfolding EqualAddress_def .. *)

subsubsection \<open>Unfold\<close>

lemma [\<phi>reason 2000]:
  " If P L (N * R1 * R2) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P L (N * (R1 * R2)) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence"
  for N :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason 2000]:
  " If P (L1 * L2 * L3) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P (L1 * (L2 * L3)) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)


subsubsection \<open>Eliminate Void Hole\<close>

lemma [\<phi>reason 2000]:
  " If P L R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P L (R * 1) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P L (1 * R) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L (R' * R) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P L (R' * 1 * R) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence
\<Longrightarrow> If P (L * 1) R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
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


section \<open>Synthesis\<close>

subsubsection \<open>Multi-Target\<close>

lemma [\<phi>reason 1250]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> A ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> B ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<bind> (\<lambda>v1. f2 \<bind> (\<lambda>v2. Return (\<phi>V_pair v2 v1))))
         \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A (\<phi>V_snd ret)\<heavy_comma> B (\<phi>V_fst ret) \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (ExSet A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<medium_right_bracket> .. .

lemma [\<phi>reason 1230]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> A \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> B ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<ggreater> f2) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A \<heavy_comma> B ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<medium_right_bracket> .. .

lemma [\<phi>reason 1240]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> A ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> B \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<bind> (\<lambda>v. f2 \<ggreater> Return v)) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A ret \<heavy_comma> B \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (ExSet A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<medium_right_bracket> .. .

lemma [\<phi>reason 1250]:
  \<open> \<p>\<r>\<o>\<c> f1 \<lbrace> R1 \<longmapsto> \<lambda>ret::unit \<phi>arg. R2\<heavy_comma> \<blangle> A \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f2 \<lbrace> R2 \<longmapsto> \<lambda>ret::unit \<phi>arg. R3\<heavy_comma> \<blangle> B \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> (f1 \<ggreater> f2) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> A \<heavy_comma> B \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + (A \<heavy_comma> E2 e)) @action synthesis\<close>
  \<medium_left_bracket> premises F1 and F2
    F1 F2 \<medium_right_bracket> .. .

(*
subsection \<open>Infer the binding pattern\<close>

definition Infer_Binding_Pattern :: \<open>'c::{} \<Rightarrow> 'a::{} \<Rightarrow> 'b::{} \<Rightarrow> prop\<close>
  where \<open>Infer_Binding_Pattern X GIVEN_PATTERN RESULTED_PATTERN \<equiv> TERM RESULTED_PATTERN\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP Infer_Binding_Pattern ?X ?G _\<close> \<Rightarrow> \<open>PROP Infer_Binding_Pattern ?X ?G _\<close> (100)
]]

declare [[\<phi>trace_reasoning = 1]]

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
                        (chk (Type.constraint \<^typ>\<open>(_::VALs) \<phi>arg \<Rightarrow> assn\<close> X :: tagged) L
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
     in Phi_Reasoner_Helpers.pos_parser "\<phi>synthesis" --| Scan.option Args.add --
        Scan.optional Parse.int 100 --
       (Scan.optional (\<^keyword>\<open>for\<close> |-- Parse.and_list1 (pattern -- priority)) [] --
        Scan.optional (\<^keyword>\<open>except\<close> |-- Parse.and_list1 pattern) [] )
>> (fn ((pos, priority), pattern) =>
      Thm.declaration_attribute (fn rule =>
        Phi_Synthesis.declare_rule pos priority pattern rule))
    end
)\<close>


subsection \<open>General Methods\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP Gen_Synthesis_Rule Q (PROP Ant &&& PROP P) X
\<Longrightarrow> PROP Gen_Synthesis_Rule (PROP P \<Longrightarrow> PROP Q) Ant X\<close>
  unfolding Gen_Synthesis_Rule_def conjunction_imp
  subgoal premises P by (rule P(1), rule P(2), assumption, assumption) .

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
      f prems(2)[OF A] \<medium_right_bracket>. . .

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
      f prems(2)[OF A] \<medium_right_bracket> .. . .

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
      f prems(2)[OF A] \<medium_right_bracket> .. . .


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


subsubsection \<open>Entry Point of Procedures\<close>

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
              = @{thm Gen_Synthesis_Rule_start_proc}
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
      prems(3)[OF Ant] \<medium_right_bracket>. . .


subsection \<open>Overloaded Synthesis\<close>


consts overloaded_synthesis :: action

declare [[\<phi>reason_default_pattern
      \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?x \<Ztypecolon> ?Y  ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action overloaded_synthesis\<close>
   \<Rightarrow> \<open>\<forall>vs::?'a. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret::_ \<phi>arg. ?x \<Ztypecolon> ?Y' ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' @action overloaded_synthesis\<close> (100),
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

(*
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
*)



(* \<forall>vs. \<p>\<r>\<o>\<c> op_add LENGTH(?'b) vs \<lbrace> ?X' vs \<longmapsto> \<lambda>ret. ?x + ?y \<Ztypecolon> \<v>\<a>\<l>[ret] \<nat>(?'b) \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. ?R\<heavy_comma> 0 e)
    @action overloaded_synthesis *)

lemma overloaded_synthesis_nullary:
  \<open>OPTIMAL_SYNTHESIS
   (\<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
\<Longrightarrow> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding Optimal_Synthesis_def Action_Tag_def .


lemma overloaded_synthesis_unary:
  \<open> \<p>\<r>\<o>\<c> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> S1 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> OPTIMAL_SYNTHESIS
    (\<forall>vs. \<p>\<r>\<o>\<c> H vs \<lbrace> R2 \<heavy_comma> S1 vs \<longmapsto> \<lambda>ret. R3 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
          \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
\<Longrightarrow> \<p>\<r>\<o>\<c> (h1 \<bind> H) \<lbrace> R1 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (E1 + E) @action synthesis\<close>
  unfolding Optimal_Synthesis_def
  \<medium_left_bracket> premises H1 and H
    H1 H \<medium_right_bracket> .. .

lemma overloaded_synthesis_binary:
  \<open> \<p>\<r>\<o>\<c> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> S1 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> h2 \<lbrace> R2 \<longmapsto> \<lambda>ret. R3\<heavy_comma> \<blangle> S2 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> OPTIMAL_SYNTHESIS
    (\<forall>vs. \<p>\<r>\<o>\<c> H vs \<lbrace> R3 \<heavy_comma> S1 (\<phi>V_snd vs) \<heavy_comma> S2 (\<phi>V_fst vs) \<longmapsto> \<lambda>ret. R4 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
          \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
\<Longrightarrow> \<p>\<r>\<o>\<c> (h1 \<bind> (\<lambda>v1. h2 \<bind> (\<lambda>v2. H (\<phi>V_pair v2 v1))))
      \<lbrace> R1 \<longmapsto> \<lambda>ret. R4\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + ((\<exists>*v. S1 v)\<heavy_comma> E2 e) + E e) @action synthesis\<close>
  unfolding Optimal_Synthesis_def
  \<medium_left_bracket> premises H1 and H2 and H
    H1 H2 H \<medium_right_bracket> .. .

lemma overloaded_synthesis_ternary:
  \<open> \<p>\<r>\<o>\<c> h1 \<lbrace> R1 \<longmapsto> \<lambda>ret::VAL \<phi>arg. R2\<heavy_comma> \<blangle> S1 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> h2 \<lbrace> R2 \<longmapsto> \<lambda>ret::VAL \<phi>arg. R3\<heavy_comma> \<blangle> S2 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> h3 \<lbrace> R3 \<longmapsto> \<lambda>ret::VAL \<phi>arg. R4\<heavy_comma> \<blangle> S3 ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E3 @action synthesis
\<Longrightarrow> OPTIMAL_SYNTHESIS
    (\<forall>vs. \<p>\<r>\<o>\<c> H vs \<lbrace> R4 \<heavy_comma> S1 (\<phi>V_snd (\<phi>V_snd vs)) \<heavy_comma> S2 (\<phi>V_fst (\<phi>V_snd vs)) \<heavy_comma> S3 (\<phi>V_fst vs)
                  \<longmapsto> \<lambda>ret. R5 \<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
          \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
\<Longrightarrow> \<p>\<r>\<o>\<c> (h1 \<bind> (\<lambda>v1. h2 \<bind> (\<lambda>v2. h3 \<bind> (\<lambda>v3. H (\<phi>V_pair v3 (\<phi>V_pair v2 v1))))))
      \<lbrace> R1 \<longmapsto> \<lambda>ret. R5\<heavy_comma> \<blangle> YY ret \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E1 e + ((\<exists>*v. S1 v)\<heavy_comma> E2 e) + ((\<exists>*v. S1 v)\<heavy_comma> (\<exists>*v. S2 v)\<heavy_comma> E3 e) + E e)
    @action synthesis\<close>
  unfolding Optimal_Synthesis_def
  \<medium_left_bracket> premises H1 and H2 and H3 and H
    H1 H2 H3 H
  \<medium_right_bracket> .. .

lemma make_overloaded_synthesis_rule:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          ((\<And>vs. X' vs \<i>\<m>\<p>\<l>\<i>\<e>\<s> X vs \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<a>\<n>\<d> Any1 vs)
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X' vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action overloaded_synthesis)\<close>
  unfolding Gen_Synthesis_Rule_def
  \<medium_left_bracket> premises E[assertion_simps] and F and X and A
    X F[OF A]
  \<medium_right_bracket> .. .

lemma make_overloaded_synthesis_rule':
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R'\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          ((\<And>vs. X' vs \<i>\<m>\<p>\<l>\<i>\<e>\<s> X vs \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<a>\<n>\<d> Any1 vs)
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
    val (V'',S'') = Procedure_Syntax.package_values
                            "\<v>\<s>" (TVar (("ret", Thm.maxidx_of sequent),\<^sort>\<open>VALs\<close>)) true NONE S
          |> apply2 (Thm.cterm_of ctxt)
   in Drule.infer_instantiate_types ctxt [(S',S''),(V',V'')] sequent
          |> (fn th => @{thm Collect_Return_Values_I} RS th)
          |> pair ctxt |> Seq.single
  end
\<close>

lemma [\<phi>reason 2550]:
  \<open> Collect_Return_Values X S vs
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> collect_return_values S vs\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def FOCUS_TAG_def TAIL_def
  by (simp add: implies_refl)

lemma [\<phi>reason 3200]:
  \<open> 0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> collect_return_values 0 \<phi>V_none\<close>
  unfolding Collect_Return_Values_def collect_return_values'_def FOCUS_TAG_def TAIL_def
  by (simp add: implies_refl)


subsection \<open>Literal Evaluation\<close>

subsubsection \<open>Check\<close>

definition Check_Literal :: \<open>'a \<Rightarrow> bool\<close> where \<open>Check_Literal _ \<longleftrightarrow> True\<close>

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(x \<open>should be a literal\<close>)
\<Longrightarrow> Check_Literal x\<close> unfolding Check_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Check_Literal True\<close> unfolding Check_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Check_Literal False\<close> unfolding Check_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Check_Literal 0\<close> unfolding Check_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open> Check_Literal x
\<Longrightarrow> Check_Literal (Suc x)\<close> unfolding Check_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Check_Literal 1\<close> unfolding Check_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Check_Literal (numeral x)\<close> unfolding Check_Literal_def ..

declare [[\<phi>premise_attribute? [\<phi>reason add] for \<open>Check_Literal _\<close>]]


subsubsection \<open>Evaluation\<close>

consts literal :: mode

lemma Do_Literal_Simplification:
  \<open> PROP Do_Simplificatin A B
\<Longrightarrow> Check_Literal A
\<Longrightarrow> Simplify s A B\<close>
  unfolding Do_Simplificatin_def Simplify_def atomize_eq .

\<phi>reasoner_ML \<open>Simplify literal\<close> 1000 (\<open>Simplify literal _ _\<close>) =
  \<open>PLPR_Simplifier.simplifier (SOME @{thm Do_Literal_Simplification}) I\<close>

hide_fact Do_Literal_Simplification


end
