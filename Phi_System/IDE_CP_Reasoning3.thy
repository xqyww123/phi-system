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

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>VAL ?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> VAL ?Y \<w>\<i>\<t>\<h> ?P\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> VAL X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> VAL Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (simp add: \<phi>expns, blast)

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>OBJ ?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> OBJ ?Y \<w>\<i>\<t>\<h> ?P\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> OBJ X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> OBJ Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (simp add: \<phi>expns, blast) *)



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


subsection \<open>Cleaning Waste Generated During Automation\<close>

(*

consts clean_automation_waste :: mode

declare [[\<phi>reason_default_pattern
    \<open>?X = _ @action clean_automation_waste\<close> \<Rightarrow> \<open>?X = _ @action clean_automation_waste\<close> (100)
]]

lemma [\<phi>reason 1]:
  \<open>X = X @action clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200]:
  \<open>(any \<Ztypecolon> \<phi>None) = 1 @action clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200]:
  \<open>(x \<Ztypecolon> T \<^emph> \<phi>None :: 'a::sep_magma_1 set) = (fst x \<Ztypecolon> T) @action clean_automation_waste\<close>
  unfolding Action_Tag_def
  by (cases x; clarsimp simp add: set_eq_iff \<phi>Prod_expn)

(* lemma clean_automation_waste_general_rule:
  \<open> Unit_Functor F
\<Longrightarrow> (x \<Ztypecolon> F \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Unit_Functor_def Transformation_def Action_Tag_def \<phi>None_itself_is_one
  by (clarsimp simp add: set_eq_iff; rule, insert \<phi>None_expn, blast, blast) *)

\<phi>reasoner_ML clean_automation_waste_general_rule 50 (\<open>_ = _ @action clean_automation_waste\<close>) = \<open>
fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (_ (*Action_Tag*) $ ( _ (*equal*) $ (_ (*\<phi>Type*) $ _ $ T) $ _) $ _) 
        = Thm.major_prem_of sequent
   in case Phi_Type_Algebra.detect_type_operator 1 ctxt T
        of SOME [Ft,_] => let
            val rule = Drule.infer_instantiate ctxt [(("F",0), Thm.cterm_of ctxt Ft)]
                          @{thm "clean_automation_waste_general_rule"}
             in SOME ((ctxt, rule RS sequent), Seq.empty) end
         | NONE => NONE
  end)
\<close>

(*TODO!*)
lemma clean_automation_waste_general_rule':
  \<open> Unit_Functor F
\<Longrightarrow> (x \<Ztypecolon> T \<^emph> F \<circle>) = (x \<Ztypecolon> T \<^emph> \<circle>) @action clean_automation_waste\<close>
  unfolding Unit_Functor_def Transformation_def Action_Tag_def \<phi>None_itself_is_one
  by (cases x; clarsimp simp add: set_eq_iff \<phi>Prod_expn; rule; insert \<phi>None_expn; blast)

lemma clean_automation_waste_general_rule'':
  \<open> Unit_Functor F
\<Longrightarrow> (F \<circle>) = \<circle> @action clean_automation_waste\<close>
  unfolding Unit_Functor_def Transformation_def Action_Tag_def \<phi>None_itself_is_one
  by (rule \<phi>Type_eqI; clarsimp simp add: set_eq_iff \<phi>Prod_expn; rule; insert \<phi>None_expn; blast)


(* (*TESTING... re-enable them for performance*)

 lemma [\<phi>reason 1200]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_\<phi>None by simp

lemma [\<phi>reason 1200]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?n \<Znrres> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> \<circle>) = (() \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>)) @action clean_automation_waste\<close>
  unfolding Action_Tag_def Premise_def \<phi>Share_\<phi>None by simp
*)


lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi>insertion ?\<psi> _ \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open> sep_orthogonal_monoid \<psi> D
\<Longrightarrow> (x \<Ztypecolon> \<phi>insertion \<psi> D \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>insertion_\<phi>None
  by simp

declare share_orthogonal_homo_pointwise[\<phi>reason 1200]
        share_orthogonal_homo_to_share[\<phi>reason 1200]

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> ?T \<^emph> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'a::sep_magma_1 set) @action clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> \<circle> \<^emph> ?U) = ?Z @action clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'b::sep_magma_1 set) @action clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?r) \<Ztypecolon> ?T \<^emph> (?n \<Znrres> \<circle>)) = (?Z :: ?'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n
\<Longrightarrow> ((x,r) \<Ztypecolon> T \<^emph> (n \<Znrres> \<circle>)) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>((?r,?x) \<Ztypecolon> (?n \<Znrres> \<circle>) \<^emph> ?T) = (?Z :: ?'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n
\<Longrightarrow> ((r,x) \<Ztypecolon> (n \<Znrres> \<circle>) \<^emph> T) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) @action clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)

*)


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

\<^prop>\<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fx \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f \<Ztypecolon> T <func-over> x \<w>\<i>\<t>\<h> P\<close>

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
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fx \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f \<Ztypecolon> T <func-over> x \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def lambda_abstraction_def by (simp add: \<phi>expns)

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



section \<open>Transformation of Structural Abstraction\<close>

(* subsection \<open>Structure Info\<close>

(*This design is entirely bad!
  It should be some mechanism to explicitly update implication DB, and every contextual info
  should be stored in that DB.*)


text \<open>Instantiate your \<phi>-type functor with \<^const>\<open>Inhabitance_Functor\<close>
  so that the automation relating to this reasoning task will be configured.\<close>

definition Structure_Info :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Structure_Info T P \<longleftrightarrow> (\<forall>x. Inhabited (x \<Ztypecolon> T) \<longrightarrow> P)\<close>
  \<comment> \<open>Extract structure information inside an assertion, typically validity of permissions
      (i.e. large than zero), which is used in the automation procedure.\<close>

lemma [\<phi>reason 1200 for \<open>Structure_Info (?n \<Znrres> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (n \<Znrres> T) (0 < n \<and> P)\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?T \<^emph> ?U) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info U Q
\<Longrightarrow> Structure_Info (T \<^emph> U) (P \<and> Q)\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?T \<Zcomp> ?U) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info U Q
\<Longrightarrow> Structure_Info (T \<Zcomp> U) (P \<and> Q)\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns \<phi>Composition_expn) blast

lemma [\<phi>reason 1200 for \<open>Structure_Info (\<phi>insertion ?\<psi> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (\<phi>insertion \<psi> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (clarsimp simp add: \<phi>expns)

lemma "_Structure_Info_general_rule_":
  \<open> Inhabitance_Functor F any
\<Longrightarrow> Structure_Info T P
\<Longrightarrow> Structure_Info (F T) P \<close>
  unfolding Inhabitance_Functor_def Structure_Info_def
  by blast

\<phi>reasoner_ML Structure_Info_general 50 (\<open>Structure_Info _ _\<close>) = \<open>
fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (Const(\<^const_name>\<open>Structure_Info\<close>, _) $ T $ _ )
        = Thm.major_prem_of sequent
   in case Phi_Functor_Detect.detect 1 ctxt T
        of SOME [Ft,Tt] => let
              val rule = Drule.infer_instantiate ctxt
                            [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                            @{thm "_Structure_Info_general_rule_"}
              in SOME ((ctxt, rule RS sequent), Seq.empty) end
          | _ => NONE
  end
)\<close>

lemma [\<phi>reason 30 for \<open>Structure_Info ?T ?P\<close>]:
  \<open> Structure_Info T True \<close>
  unfolding Structure_Info_def by blast

(*
(*TESTING... re-enable them for performance*)

(* The following 3 rules are redundant, but is given for the sake of performance. *)

lemma [\<phi>reason 1200 for \<open>Structure_Info (\<black_circle> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (\<black_circle> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (k \<^bold>\<rightarrow>\<^sub>@ T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?k \<^bold>\<rightarrow> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (k \<^bold>\<rightarrow> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)
*)
*)

subsection \<open>Structural Extract\<close>


(*definition Structural_Extract :: \<open>'a::sep_magma set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Structural_Extract From Remain To Residual Aux \<longleftrightarrow> (Residual * From \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Remain * To \<w>\<i>\<t>\<h> Aux)\<close>
  \<comment> \<open>Extract \<open>To\<close> from \<open>From\<close>, remaining \<open>Remain\<close> the unused part in From,
      and leaving \<open>Residual\<close> the part in \<open>To\<close> that fails to be obtained from From, and so needs
      further reasoning to get \<open>Residual\<close> from the remaining unanalysised part of the source.\<close>

declare [[\<phi>reason_default_pattern
      \<open>Structural_Extract ?X _ ?Y _ _\<close> \<Rightarrow> \<open>Structural_Extract ?X _ ?Y _ _\<close> (100)
  and \<open>Structural_Extract ?X _ ?Y _ (Reverse_Transformation _ _ \<and> _)\<close> \<Rightarrow>
      \<open>Structural_Extract ?X _ ?Y _ (Reverse_Transformation _ _ \<and> _)\<close>          (110)
]]*)

(*
lemma SE_clean_waste:
  \<open> x \<Ztypecolon> T \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> W \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> R = R' @action clean_automation_waste
\<Longrightarrow> W = W' @action clean_automation_waste
\<Longrightarrow> x \<Ztypecolon> T \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> W' \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  unfolding Action_Tag_def
  by simp *)

(*lemma SE_clean_waste:
  \<open> Structural_Extract X R Y W P
\<Longrightarrow> R = R' @action clean_automation_waste
\<Longrightarrow> W = W' @action clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' P\<close>
  unfolding Action_Tag_def
  by simp

lemma SE_clean_waste':
  \<open> Structural_Extract X R Y W (Reverse_Transformation RP (Structural_Extract rY rW rX rR rP) \<and> P)
\<Longrightarrow>  R = R'  @action clean_automation_waste
\<Longrightarrow>  W = W'  @action clean_automation_waste
\<Longrightarrow> rR = rR' @action clean_automation_waste
\<Longrightarrow> rW = rW' @action clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' (Reverse_Transformation RP (Structural_Extract rY rW' rX rR' rP) \<and> P)\<close>
  unfolding Action_Tag_def
  by simp*)

(*
lemma SE_clean_waste':
  \<open> x \<Ztypecolon> T \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> W \<w>\<i>\<t>\<h> (Reverse_Transformation RP (yr \<Ztypecolon> Ur \<^emph> Wr \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xr \<Ztypecolon> Tr \<^emph> Rr \<w>\<i>\<t>\<h> Pr) \<and> P) @action \<A>SE True
\<Longrightarrow> R = R' @action clean_automation_waste
\<Longrightarrow> W = W' @action clean_automation_waste
\<Longrightarrow> rR = rR' @action clean_automation_waste
\<Longrightarrow> rW = rW' @action clean_automation_waste
\<Longrightarrow> x \<Ztypecolon> T \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> W' \<w>\<i>\<t>\<h> (Reverse_Transformation RP (yr \<Ztypecolon> Ur \<^emph> Wr \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xr \<Ztypecolon> Tr \<^emph> Rr \<w>\<i>\<t>\<h> Pr) \<and> P) @action \<A>SE True\<close>
  unfolding Action_Tag_def
  by simp
*)

(*
lemma Structural_Extract_imply_P:
  \<open> Structural_Extract X R Y W P1
\<Longrightarrow> P1 \<longrightarrow> P2
\<Longrightarrow> Structural_Extract X R Y W P2\<close>
  unfolding Structural_Extract_def Transformation_def by blast

lemma Structural_Extract_reverse_transformation_I[intro?]:
  \<open> Structural_Extract X R Y W P
\<Longrightarrow> RP \<longrightarrow> RX
\<Longrightarrow> Structural_Extract X R Y W (Reverse_Transformation RP RX \<and> P)\<close>
  unfolding Generated_Rule_def Structural_Extract_def Transformation_def
  by blast*)

subsubsection \<open>Installation -- Rules initializing the SE reasoning\<close>

lemma NToA_by_structural_extraction:
  " Object_Equiv T eq
\<Longrightarrow> Try Any ((y,w) \<Ztypecolon> U \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xr \<Ztypecolon> T \<^emph> R \<w>\<i>\<t>\<h> P2 @action \<A>SE True)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (fst xr) x
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 \<heavy_comma> \<blangle> w \<Ztypecolon> W \<brangle> \<w>\<i>\<t>\<h> P1
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2\<heavy_comma> snd xr \<Ztypecolon> R\<heavy_comma> \<blangle> x \<Ztypecolon> T \<brangle> \<w>\<i>\<t>\<h> P1 \<and> P2"
  unfolding FOCUS_TAG_def Try_def
  \<medium_left_bracket> premises _ and SE and _ and A
    apply_rule A[THEN implies_right_prod]
    SE
  \<medium_right_bracket> .

lemma NToA_by_structural_extraction__reverse_transformation:
  " Object_Equiv T eq
\<Longrightarrow> Try Any (
      (y,w) \<Ztypecolon> U \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xr \<Ztypecolon> T \<^emph> R \<w>\<i>\<t>\<h> (
        (True \<longrightarrow> Reverse_Transformation RP2 ((x',r') \<Ztypecolon> T' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yw' \<Ztypecolon> U' \<^emph> W' \<w>\<i>\<t>\<h> P2')
        ) \<and> P2))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (fst xr) x
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 \<heavy_comma> \<blangle> w \<Ztypecolon> W \<brangle> \<w>\<i>\<t>\<h> (Reverse_Transformation RP1 (R2'\<heavy_comma> \<blangle> snd yw' \<Ztypecolon> W' \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<w>\<i>\<t>\<h> P1') \<and> P1)
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2\<heavy_comma> snd xr \<Ztypecolon> R\<heavy_comma> \<blangle> x \<Ztypecolon> T \<brangle> \<w>\<i>\<t>\<h>
      (Reverse_Transformation (Object_Equiv U' eq' \<and> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> eq' (fst yw') y') \<and> RP2 \<and> RP1) (
              R2'\<heavy_comma> r' \<Ztypecolon> R'\<heavy_comma> \<blangle> x' \<Ztypecolon> T' \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A'\<heavy_comma> y' \<Ztypecolon> U' \<w>\<i>\<t>\<h> P1' \<and> P2')
          \<and> P1 \<and> P2)"
  unfolding FOCUS_TAG_def Generated_Rule_def Try_def
  \<medium_left_bracket> premises _ and SE and _ and A
    apply_rule A[THEN implies_right_prod]
    SE
  \<medium_right_bracket> certified apply (clarsimp simp add: \<phi>)
  \<medium_left_bracket> premises _ and _ and [simp] and [simp]
    have A : \<open>R2' \<heavy_comma> snd yw' \<Ztypecolon> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<w>\<i>\<t>\<h> P1'\<close> using \<phi>_previous by simp
    have SE: \<open>(r' \<Ztypecolon> R' \<heavy_comma> x' \<Ztypecolon> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yw' \<Ztypecolon> U' \<^emph> W' \<w>\<i>\<t>\<h> P2')\<close> using \<phi>_previous by (simp add: \<phi>Prod_expn') ;;
    SE 
    apply_rule A
  \<medium_right_bracket> . .


(*TODO: BUG: need to check the case where Y requires only partial share permission but
    this rule may give it the total.*)

subsubsection \<open>Termination\<close>


subsubsection \<open>Fall back\<close>




(*
lemma [\<phi>reason 5]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Reverse_Transformation Pr (y' \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P2) \<and> P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (() \<Ztypecolon> \<phi>None) (y \<Ztypecolon> U) (() \<Ztypecolon> \<phi>None) (
        Reverse_Transformation Pr (Structural_Extract (y' \<Ztypecolon> U') (() \<Ztypecolon> \<phi>None) (x' \<Ztypecolon> T') (() \<Ztypecolon> \<phi>None) P2) \<and> P) \<close>
  unfolding Action_Tag_def
  by (metis Generated_Rule_def Structural_Extract_fallback transformation_weaken)
*)



subsubsection \<open>Terminations for Specific Node\<close>

lemma [\<phi>reason 1200]:
  \<open> \<g>\<u>\<a>\<r>\<d> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, ()) \<Ztypecolon> \<black_circle> U \<^emph> \<circle> \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  unfolding Action_Tag_def \<r>Guard_def
  by (cases x; simp add: \<phi>Prod_expn' \<phi>Some_cast)

lemma [\<phi>reason 1201]:
  \<open> \<g>\<u>\<a>\<r>\<d> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, ()) \<Ztypecolon> \<black_circle> U \<^emph> \<circle> \<w>\<i>\<t>\<h> (
      Reverse_Transformation (fst y' \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P')
        (y' \<Ztypecolon> \<black_circle> U' \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x', ()) \<Ztypecolon> \<black_circle> T' \<^emph> \<circle> \<w>\<i>\<t>\<h> P')
    \<and> P) @action \<A>SE True\<close>
  unfolding Action_Tag_def \<r>Guard_def Generated_Rule_def
  by (cases x; cases y'; simp add: \<phi>Prod_expn' \<phi>Some_cast)

(*TODO: According to @{thm Agreement_times}, there must be a reasoning mechanism for \<inter>\<^sub>\<phi>
  It scatters information using \<inter>\<^sub>\<phi>

The bellowing reasoning is too weak! *)

(*TODO!*)
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



subsubsection \<open>Stepwise of Separations\<close>



(*
lemma Structural_Extract_from_mult:
  \<open> Try S1 (Structural_Extract X R2 Y Wr P1)
\<Longrightarrow> Try S2 (Structural_Extract L R Wr Wr2 P2)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> Structural_Extract (L * X) (R * R2) Y Wr2 (P1 \<and> P2)\<close>
  for X :: \<open>'a::sep_algebra set\<close>
  unfolding Structural_Extract_def Simplify_def Try_def
  \<medium_left_bracket> premises R and L
    fold mult.assoc
    apply_rule L[THEN implies_right_prod]
    apply_rule R[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  \<medium_right_bracket> .

declare Structural_Extract_from_mult [THEN SE_clean_waste,  \<phi>reason 1200] *)




subsubsection \<open>Type Algebra\<close>

(* TODO!!!!!
\<phi>reasoner_ML "Structural_Extract_general_rule" 50 (\<open>Structural_Extract (_ \<Ztypecolon> _) _ (_ \<Ztypecolon> _) _ _\<close>) = \<open>

fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (Const(\<^const_name>\<open>Structural_Extract\<close>, _)
        $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T)
        $ _
        $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ U)
        $ _
        $ P
      ) = Thm.major_prem_of sequent
      val mode_automatic_transformation =
            (case P of Const(\<^const_name>\<open>conj\<close>, _) $ (
                       Const(\<^const_name>\<open>Generated_Rule\<close>, _) $ _ $ _ $ _) $ _ => true
                | _ => false)
   in case (Phi_Functor_Detect.detect 1 ctxt T,
            Phi_Functor_Detect.detect 1 ctxt U)
        of (SOME [Ft,Tt], SOME [Fu, Uu]) => let
              val rule = if mode_automatic_transformation
                         then let (*This branch needs test*)
                           val [varified_T, varified_U] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [T,U]
                           val [vFt, vTt] = Phi_Functor_Detect.detect1 1 ctxt varified_T
                           val [vFu, vUu] = Phi_Functor_Detect.detect1 1 ctxt varified_U
                           in Drule.infer_instantiate ctxt
                                  [(("F1",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt),
                                   (("F3",0), Thm.cterm_of ctxt Fu), (("U",0), Thm.cterm_of ctxt Uu),
                                   (("F1'",0), Thm.cterm_of ctxt vFt), (("T'",0), Thm.cterm_of ctxt vTt),
                                   (("F3'",0), Thm.cterm_of ctxt vFu), (("U'",0), Thm.cterm_of ctxt vUu)]
                                  @{thm "_Structural_Extract_general_rule'_"}
                              RS @{thm SE_clean_waste'}
                           end
                         else Drule.infer_instantiate ctxt
                                  [(("F1",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt),
                                   (("F3",0), Thm.cterm_of ctxt Fu), (("U",0), Thm.cterm_of ctxt Uu)]
                                  @{thm "_Structural_Extract_general_rule_"}
                               RS @{thm SE_clean_waste}
              in SOME ((ctxt, rule RS sequent), Seq.empty) end
          | _ => NONE
   end
)
\<close>
*)

(*
(*use \<open>k \<^bold>\<rightarrow>\<close> to test*)
lemma Structural_Extract_\<phi>MapAt:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (yr \<Ztypecolon> k \<^bold>\<rightarrow> Ur) P\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def
  apply (simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_\<phi>Prod[symmetric])
  by (rule \<phi>MapAt_cast)*)

(* Disabled for TESTING. Should be re-enabled for performance.

declare Structural_Extract_\<phi>MapAt[THEN SE_clean_waste, \<phi>reason 1200]


lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (w \<Ztypecolon> k \<^bold>\<rightarrow> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U') (w' \<Ztypecolon> k \<^bold>\<rightarrow> W') (x' \<Ztypecolon> k \<^bold>\<rightarrow> T') (r' \<Ztypecolon> k \<^bold>\<rightarrow> R') P') \<and> P)\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Generated_Rule_def \<r>Guard_def
  by (blast intro: Structural_Extract_\<phi>MapAt[unfolded Action_Tag_def \<r>Guard_def]
                   Structural_Extract_imply_P) *)

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


(* [-----a-----][--d--]
   [--c--][-----b-----] 
   Give a, expect b; Need d, remain c.*)
lemma SE_Near_Semimodule_adcb[(*THEN SE_clean_waste,*) \<phi>reason_template add]:
  \<open> Near_Semimodule_Functor_unzip F1 Ds Dx uz
\<Longrightarrow> Near_Semimodule_Functor_zip_rev F1 Ds Dx' z
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F1 F3
\<Longrightarrow> \<r>Success
\<Longrightarrow> a + d = c + b @action non_trivial_partial_add_split
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<in> Ds \<and> d \<in> Ds \<and> c \<in> Ds \<and> b \<in> Ds \<and> c ##\<^sub>+ b \<and> a ##\<^sub>+ d
\<Longrightarrow> Dx' T (fst x, fst (snd x))
\<Longrightarrow> Dx T (z a d (fst x, fst (snd x)))
\<Longrightarrow> (fst (uz c b (z a d (fst x, fst (snd x)))), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz c b (z a d (fst x, fst (snd x)))), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  \<medium_left_bracket> premises _ and _ and _ and _ and [useful,simp] and _ and [\<phi>reason add] and [\<phi>reason add] and Tr
    apply_rule apply_Near_Semimodule_Functor_zip_rev[where t=a and s=d and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    apply_rule apply_Near_Semimodule_Functor_unzip[where t=c and s=b and F=F1]
    Tr
  \<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 0]]

lemma (*SE_Near_Semimodule_adcb equipped with the reverse transformation*)
      [(*THEN SE_clean_waste',*) \<phi>reason_template add]:
  \<open> Near_Semimodule_Functor_unzip F1 Ds Dx uz
\<Longrightarrow> Near_Semimodule_Functor_zip_rev F1 Ds Dx' z
\<Longrightarrow> Near_Semimodule_Functor_zip F1' Ds Dx'' z'
\<Longrightarrow> Near_Semimodule_Functor_unzip F1' Ds Dx'c uz'
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F1 F3
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F1' F3'
\<Longrightarrow> \<r>Success
\<Longrightarrow> a + d = c + b @action non_trivial_partial_add_split
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<in> Ds \<and> d \<in> Ds \<and> c \<in> Ds \<and> b \<in> Ds \<and> c ##\<^sub>+ b \<and> a ##\<^sub>+ d
\<Longrightarrow> Dx' T (fst x, fst (snd x))
\<Longrightarrow> Dx T (z a d (fst x, fst (snd x)))
\<Longrightarrow> (fst (uz c b (z a d (fst x, fst (snd x)))), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> (
      Reverse_Transformation RP (
          (fst x', snd (snd x')) \<Ztypecolon> F3' b U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> F1' b T' \<^emph> W' \<w>\<i>\<t>\<h> P')
      \<and> P)
      @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz c b (z a d (fst x, fst (snd x)))), snd y) \<Ztypecolon> F3 b U \<^emph> F1 c T \<^emph> R \<w>\<i>\<t>\<h> (
      Reverse_Transformation (Dx'' T' (fst y', fst (snd x')) \<and> Dx'c T' (z' c b (fst y', fst (snd x'))) \<and> RP) (
          x' \<Ztypecolon> F3' b U' \<^emph> F1' c T' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd (uz' a d (z' c b (fst y', fst (snd x')))), fst (uz' a d (z' c b (fst y', fst (snd x')))), snd y') \<Ztypecolon> F1' a T' \<^emph> F1' d T' \<^emph> W' \<w>\<i>\<t>\<h> P')
      \<and> P)
    @action \<A>SE True \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close> and W' :: \<open>('c'::sep_ab_semigroup,'d') \<phi>\<close>
  unfolding Action_Tag_def
  apply (rule transformation_weaken, defer_tac)
  apply (rule SE_Near_Semimodule_adcb[of F1, unfolded Action_Tag_def])
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  (*apply simp
  apply simp*)
  apply (clarsimp simp add: Generated_Rule_def \<r>Success_def Parameter_Variant_of_the_Same_Type_def)
  \<medium_left_bracket> premises _ and _ and _ and _ and [symmetric,simp] and _ and _ and _ and _ and _
         and [\<phi>reason add] and [\<phi>reason add] and _ and Tr
    Tr
    apply_rule apply_Near_Semimodule_Functor_zip[where t=c and s=b and F=F1' and x=\<open>(fst y',fst (snd x'))\<close>]
    apply_rule apply_Near_Semimodule_Functor_unzip[where t=a and s=d and F=F1']
  \<medium_right_bracket> .

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c. *)
lemma SE_Near_Semimodule_dabc[(*THEN SE_clean_waste,*) \<phi>reason_template add]:
  \<open> Near_Semimodule_Functor_unzip F1 Ds Dx uz
\<Longrightarrow> Near_Semimodule_Functor_zip F1 Ds Dx' z
\<Longrightarrow> d + a = b + c @action non_trivial_partial_add_split
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<in> Ds \<and> d \<in> Ds \<and> c \<in> Ds \<and> b \<in> Ds \<and> b ##\<^sub>+ c \<and> d ##\<^sub>+ a
\<Longrightarrow> Dx' T (fst x,fst (snd x))
\<Longrightarrow> Dx T (z d a (fst x, fst (snd x)))
\<Longrightarrow> (snd (uz b c (z d a (fst x, fst (snd x)))), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, fst (uz b c (z d a (fst x, fst (snd x)))), snd y) \<Ztypecolon> F3 b U \<^emph> F1 c T \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  \<medium_left_bracket> premises _ and _ and [useful,simp] and _ and [\<phi>reason add] and [\<phi>reason add] and Tr
    apply_rule apply_Near_Semimodule_Functor_zip[where t=d and s=a and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    apply_rule apply_Near_Semimodule_Functor_unzip[where t=b and s=c and F=F1]
    Tr
  \<medium_right_bracket> .


(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma [(*THEN SE_clean_waste,*) \<phi>reason_template add]:
  \<open> Near_Semimodule_Functor_unzip F1 Ds Dx uz
\<Longrightarrow> a = d + b + c @action non_trivial_partial_add_split
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> d + b \<in> Ds \<and> c \<in> Ds \<and> b \<in> Ds \<and> d \<in> Ds \<and> d + b ##\<^sub>+ c \<and> d ##\<^sub>+ b
\<Longrightarrow> Dx T (fst x)
\<Longrightarrow> Dx T (snd (uz (d + b) c (fst x)))
\<Longrightarrow> (fst (uz d b (snd (uz (d + b) c (fst x)))), snd x) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz d b (snd (uz (d + b) c (fst x)))), fst (uz (d + b) c (fst x)), snd y) \<Ztypecolon> F3 b U \<^emph> F1 d T \<^emph> F1 c T \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  \<medium_left_bracket> premises _ and a and _ and [\<phi>reason add] and [\<phi>reason add] and Tr
    apply_rule apply_Near_Semimodule_Functor_unzip[where t=\<open>d + b\<close> and s=c and F=F1, folded a]
    apply_rule apply_Near_Semimodule_Functor_unzip[where t=\<open>d\<close> and s=b and F=F1]
    Tr
  \<medium_right_bracket> .

(*schematic_goal
  \<open>A ?x \<Longrightarrow> A ?x \<Longrightarrow> B\<close>
  ML_val \<open>#goal @{Isar.goal} |> Simplifier.asm_lr_simplify \<^context>\<close> *)

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c. *)
lemma [(*THEN SE_clean_waste,*) \<phi>reason_template add]:
  \<open> Near_Semimodule_Functor_zip F1 Ds Dx z
\<Longrightarrow> Near_Semimodule_Functor_zip_rev F1 Ds Dx' z'
\<Longrightarrow> d + a + c = b @action non_trivial_partial_add_split
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<in> Ds \<and> d \<in> Ds \<and> c \<in> Ds \<and> d + a \<in> Ds \<and> d ##\<^sub>+ a \<and> d + a ##\<^sub>+ c
\<Longrightarrow> Dx T (fst x,fst (snd x))
\<Longrightarrow> Dx' T (z d a (fst x, fst (snd x)), fst (snd (snd x)))
\<Longrightarrow> (z' (d + a) c (z d a (fst x, fst (snd x)), fst (snd (snd x))), snd (snd (snd x))) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> F1 c T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  \<medium_left_bracket> premises _ and _ and [useful,simp] and _ and [\<phi>reason add] and [\<phi>reason add] and Tr
    apply_rule apply_Near_Semimodule_Functor_zip[where t=d and s=a and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    apply_rule apply_Near_Semimodule_Functor_zip_rev[where t=\<open>d+a\<close> and s=c and F=F1 and x=\<open>(z d a (fst x, fst (snd x)), fst (snd (snd x)))\<close>]
    Tr
>>>>>>> 820417f (Improve constructions of implication)
  \<medium_right_bracket> .


paragraph \<open>Structural Nodes\<close>

(*discarded, no need

lemma Structural_Extract_\<phi>MapAt_L_pad_left:
  \<open> \<g>\<u>\<a>\<r>\<d>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> length k < length k'
&&& \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k @ kd = k'
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W) P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def \<r>Guard_def conjunction_imp
  subgoal premises prems
    apply (insert prems(3),
       simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L.sep_homo_type
          \<phi>MapAt_L_\<phi>MapAt_L[symmetric, of k kd, unfolded prems(2)])
    by (rule \<phi>MapAt_L_cast) .

declare Structural_Extract_\<phi>MapAt_L_pad_left [THEN SE_clean_waste, \<phi>reason 1180]

lemma [THEN SE_clean_waste', \<phi>reason 1183]:
  \<open> \<g>\<u>\<a>\<r>\<d>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> length k < length k'
&&& \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k @ kd = k'
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Reverse_Transformation RP
        (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Generated_Rule_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)

lemma [THEN SE_clean_waste', \<phi>reason 1153]:
  \<open> \<g>\<u>\<a>\<r>\<d>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> length k' < length k
&&& \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' @ kd = k
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Reverse_Transformation RP
        (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Generated_Rule_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)*)


lemma Structural_Extract_\<phi>Map_L_norm_right [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow> U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_At .

lemma Structural_Extract_\<phi>Map_L_norm_left [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  unfolding Action_Tag_def \<phi>MapAt_L_At .

lemma [\<phi>reason 1211]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T' \<^emph> W' \<w>\<i>\<t>\<h> P')
      \<and> P) @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow> U \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T' \<^emph> W' \<w>\<i>\<t>\<h> P')
      \<and> P) @action \<A>SE True\<close>
  unfolding Generated_Rule_def Action_Tag_def
  by (rule transformation_weaken, defer_tac,
      rule Structural_Extract_\<phi>Map_L_norm_right[unfolded Action_Tag_def], assumption, clarify,
      rule Structural_Extract_\<phi>Map_L_norm_left [unfolded Action_Tag_def], blast)

lemma [\<phi>reason 1211]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T' \<^emph> W' \<w>\<i>\<t>\<h> P')
      \<and> P) @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> k \<^bold>\<rightarrow> T' \<^emph> W' \<w>\<i>\<t>\<h> P')
      \<and> P) @action \<A>SE True\<close>
  unfolding Generated_Rule_def Action_Tag_def
  by (rule transformation_weaken, defer_tac,
      rule Structural_Extract_\<phi>Map_L_norm_left [unfolded Action_Tag_def], assumption, clarify,
      rule Structural_Extract_\<phi>Map_L_norm_right[unfolded Action_Tag_def], blast)

hide_fact Structural_Extract_\<phi>Map_L_norm_left Structural_Extract_\<phi>Map_L_norm_right

(*Discarded, no need any more, replaced by algebraic generation

lemma Structural_Extract_\<phi>insertion:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi>insertion \<psi> D T)
                       (r \<Ztypecolon> \<phi>insertion \<psi> D R)
                       (y \<Ztypecolon> \<phi>insertion \<psi> D U)
                       (w \<Ztypecolon> \<phi>insertion \<psi> D W)
                       P\<close>
  unfolding Structural_Extract_def Transformation_def \<phi>Sep_Disj_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis (no_types, lifting) homo_sep _def homo_sep_disj_def homo_sep_mult.homo_mult sep_orthogonal_1_def sep_orthogonal_def sep_orthogonal_monoid_def share_orthogonal_homo.axioms(1))

declare Structural_Extract_\<phi>insertion[THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi>insertion \<psi> D T)
                       (r \<Ztypecolon> \<phi>insertion \<psi> D R)
                       (y \<Ztypecolon> \<phi>insertion \<psi> D U)
                       (w \<Ztypecolon> \<phi>insertion \<psi> D W)
       (Reverse_Transformation (RP \<and>\<^sub>\<r> \<phi>Sep_Disj R' U')
           (Structural_Extract (y' \<Ztypecolon> \<phi>insertion \<psi> D U')
                               (w' \<Ztypecolon> \<phi>insertion \<psi> D W')
                               (x' \<Ztypecolon> \<phi>insertion \<psi> D T')
                               (r' \<Ztypecolon> \<phi>insertion \<psi> D R')
                                P') \<and> P)\<close>
  unfolding Generated_Rule_def Action_Tag_def Compact_Antecedent_def
  by (blast intro: Structural_Extract_\<phi>insertion[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)
*)

(* TODO: still required, need repair!

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
      (Reverse_Transformation RP (Structural_Extract Y' W' (x' \<Ztypecolon> T') R' P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T ?\<^sub>\<phi> True) R Y W
      (Reverse_Transformation RP (Structural_Extract Y' W' (x' \<Ztypecolon> T' ?\<^sub>\<phi> True) R' P') \<and> P)\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  unfolding Generated_Rule_def Action_Tag_def
  by (blast intro: Structural_Extract_\<phi>Optional_left [unfolded Action_Tag_def]
                   Structural_Extract_\<phi>Optional_right[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)
*)


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

(* consider this half tag!!!

lemma Structural_Extract_share_half:
    \<comment> \<open>if only requires a half of the permission, give it a half of that currently we have.\<close>
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half(m / 2) \<Znrres> U) (w \<Ztypecolon> W) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def half_def Action_Tag_def
  \<medium_left_bracket> premises [\<phi>reason] and X
    apply_rule share_split_\<phi>app[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod]
    fold mult.assoc
    apply_rule X[THEN implies_right_prod]
  \<medium_right_bracket> .

declare Structural_Extract_share_half[THEN SE_clean_waste,
    \<phi>reason 1300 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?T) _ (?y \<Ztypecolon> half ?mmm \<Znrres> ?U) _ _\<close>]

lemma Structural_Extract_share_half_rev:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) P
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def Action_Tag_def \<phi>Prod_expn'
  \<medium_left_bracket> premises [\<phi>reason] and X
  have t1: \<open>(r \<Ztypecolon> R) * (x \<Ztypecolon> m / 2 \<Znrres> T) * (y \<Ztypecolon> m / 2 \<Znrres> U) = (r \<Ztypecolon> R) * (y \<Ztypecolon> m / 2 \<Znrres> U) * (x \<Ztypecolon> m / 2 \<Znrres> T)\<close>
    by (metis (mono_tags, lifting) mult.assoc mult.commute)
  ;; unfold t1
     apply_rule X[THEN implies_right_prod]
     apply_rule share_merge[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod, folded mult.assoc]
  \<medium_right_bracket> .

(* declare Structural_Extract_share_half_rev[THEN SE_clean_waste] *)

lemma
  [THEN SE_clean_waste',
   \<phi>reason 1311 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> half ?mmm \<Znrres> ?U) ?R2
      (Reverse_Transformation _ _ \<and> _)\<close>]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W)
    (Reverse_Transformation RP
        (Structural_Extract (y' \<Ztypecolon> m / 2 \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m / 2 \<Znrres> T') (r' \<Ztypecolon> R') P')
    \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half (m / 2) \<Znrres> U) (w \<Ztypecolon> W)
    (Reverse_Transformation (RP \<and>\<^sub>\<r> \<phi>Sep_Disj_Inj (x' \<Ztypecolon> T'))
        (Structural_Extract (y' \<Ztypecolon> half (m / 2) \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m \<Znrres> T') ((x',r') \<Ztypecolon> m / 2 \<Znrres> T' \<^emph> R') P')
    \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Generated_Rule_def Compact_Antecedent_def half_def
  by (blast intro: Structural_Extract_share_half    [unfolded Action_Tag_def half_def]
                   Structural_Extract_share_half_rev[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)



lemma Structural_Extract_share_eq:
  \<comment> \<open>If requires exactly what we have now, typically this happens after the previous rule or n = 1.\<close>
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> m = n
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W) P \<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn'[symmetric] Premise_def \<r>Guard_def conjunction_imp
  apply (simp add: \<phi>Share_\<phi>Prod[symmetric])
  using \<phi>Share_transformation .

declare Structural_Extract_share_eq [THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> m = n
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W)
      (Reverse_Transformation RP
          (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> m \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Generated_Rule_def Action_Tag_def \<r>Guard_def conjunction_imp
  by (blast intro: Structural_Extract_share_eq[unfolded Action_Tag_def \<r>Guard_def conjunction_imp]
                   Structural_Extract_imply_P)



lemma Structural_Extract_share_ge:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> n < m
&&& \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' Action_Tag_def conjunction_imp \<r>Guard_def
  \<medium_left_bracket> premises LE[unfolded Premise_def, useful] and [\<phi>reason] and _ and X
    apply_rule share_split_\<phi>app[where n=\<open>n\<close> and m=\<open>m-n\<close>, simplified]
    fold mult.assoc
    apply_rule X[folded \<phi>Prod_expn', THEN \<phi>Share_transformation, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
                 THEN implies_right_prod]
  have t1: \<open>(r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U) * (x \<Ztypecolon> m - n \<Znrres> T) = (x \<Ztypecolon> m - n \<Znrres> T) * (r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    using mult.assoc mult.commute by blast
  ;; unfold t1
  \<medium_right_bracket> .

declare Structural_Extract_share_ge [THEN SE_clean_waste, \<phi>reason 1180]

lemma Structural_Extract_share_le:
  \<comment> \<open>If requires more than what we have, give all what we can give.\<close>
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> m < n
&&& \<phi>Sep_Disj_Inj (y \<Ztypecolon> U)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < m
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U) P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' conjunction_imp \<r>Guard_def
  \<medium_left_bracket> premises LE[unfolded Premise_def, useful] and SDI[\<phi>reason] and _ and X
    apply_rule X[folded \<phi>Prod_expn', THEN \<phi>Share_transformation, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
                 THEN implies_left_prod, folded mult.assoc]

  have \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (y \<Ztypecolon> m \<Znrres> U) = (y \<Ztypecolon> n \<Znrres> U)\<close>
    using \<phi>Share_share[where n=\<open>n-m\<close> and m=m, simplified] \<phi>
    by (smt (verit) SDI)
  then have t1: \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> m \<Znrres> U) = (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute)
  ;; unfold t1
  \<medium_right_bracket> .

declare Structural_Extract_share_le[THEN SE_clean_waste, \<phi>reason 1170]



lemma [THEN SE_clean_waste', \<phi>reason 1183]:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> n < m
&&& \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W)
      (Reverse_Transformation (RP \<and>\<^sub>\<r> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> m-n = mn) \<and>\<^sub>\<r> \<phi>Sep_Disj_Inj (x' \<Ztypecolon> T'))
        (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> n \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') ((r',x') \<Ztypecolon> (n \<Znrres> R' \<^emph> mn \<Znrres> T')) P') \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Generated_Rule_def Compact_Antecedent_def Premise_def
            conjunction_imp \<r>Guard_def
  by (blast intro: Structural_Extract_share_ge[unfolded Action_Tag_def \<r>Guard_def conjunction_imp]
                   Structural_Extract_share_le[unfolded Action_Tag_def \<r>Guard_def conjunction_imp]
                   Structural_Extract_imply_P)

lemma [THEN SE_clean_waste', \<phi>reason 1173]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> m < n
&&& \<phi>Sep_Disj_Inj (y \<Ztypecolon> U)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < m
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U)
      (Reverse_Transformation (RP \<and>\<^sub>\<r> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> nm = n - m) \<and>\<^sub>\<r> \<phi>Sep_Disj_Inj (y' \<Ztypecolon> U'))
        (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') ((w',y') \<Ztypecolon> m \<Znrres> W' \<^emph> nm \<Znrres> U') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Generated_Rule_def Compact_Antecedent_def Premise_def conjunction_imp \<r>Guard_def
  by (blast intro: Structural_Extract_share_ge[unfolded Action_Tag_def conjunction_imp \<r>Guard_def]
                   Structural_Extract_share_le[unfolded Action_Tag_def conjunction_imp \<r>Guard_def]
                   Structural_Extract_imply_P)
*)

subsubsection \<open>Optimization\<close>

text \<open>The below rules are not necessary but reduce fragments in the result of the reasoning.\<close>

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> X \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> T \<^emph> n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> X \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> (T \<^emph> U)) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> (n \<odiv> T \<^emph> n \<odiv> U) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Y \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> (n \<odiv> (T \<^emph> U)) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Y \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2011]:
  \<open> x \<Ztypecolon> X \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> T \<^emph> n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h>
        (Reverse_Transformation RP (x' \<Ztypecolon> (n \<odiv> T' \<^emph> n \<odiv> U') \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> Y' \<^emph> R' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> X \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> (T \<^emph> U)) \<^emph> R \<w>\<i>\<t>\<h>
       (Reverse_Transformation RP (x' \<Ztypecolon> (n \<odiv> (T' \<^emph> U')) \<^emph>  W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> Y' \<^emph> R' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Generated_Rule_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>Prod
  by blast

lemma [\<phi>reason 2011]:
  \<open> x' \<Ztypecolon> (n \<odiv> T' \<^emph> n \<odiv> U') \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> Y' \<^emph> R' \<w>\<i>\<t>\<h>
        (Reverse_Transformation RP (y \<Ztypecolon> Y \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> T \<^emph> n \<odiv> U) \<^emph> W \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True
\<Longrightarrow> x' \<Ztypecolon> (n \<odiv> (T' \<^emph> U')) \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> Y' \<^emph> R' \<w>\<i>\<t>\<h>
        (Reverse_Transformation RP (y \<Ztypecolon> Y \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> (T \<^emph> U)) \<^emph> W \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Generated_Rule_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>Prod
  by blast


lemma [\<phi>reason 2000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (k \<^bold>\<rightarrow> n \<odiv> T) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow> T) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> (k \<^bold>\<rightarrow> n \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  for T :: \<open>('a::{share_one,sep_magma},'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2011]:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (k \<^bold>\<rightarrow> n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h>
        (Reverse_Transformation RP (y' \<Ztypecolon> (k \<^bold>\<rightarrow> n \<odiv> U') \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow> U) \<^emph> R \<w>\<i>\<t>\<h>
        (Reverse_Transformation RP (y' \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow> U') \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True\<close>
  for T :: \<open>('k \<Rightarrow> 'a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('k \<Rightarrow> 'aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Generated_Rule_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt
  by blast

lemma [\<phi>reason 2011]:
  \<open> x' \<Ztypecolon> (k \<^bold>\<rightarrow> n \<odiv> T') \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Y' \<^emph> R' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y \<Ztypecolon> Y \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (k \<^bold>\<rightarrow> n \<odiv> T) \<^emph> W \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True
\<Longrightarrow> x' \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow> T') \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Y' \<^emph> R' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y \<Ztypecolon> Y \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow> T) \<^emph> W \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True \<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Generated_Rule_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt
  by blast


lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ U) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::{share_one,sep_magma}, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 2011]:
  \<open> x \<Ztypecolon> (k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> (k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T') \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T') \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::{share_one,sep_magma}, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Generated_Rule_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast

lemma [\<phi>reason 2011]:
  \<open> y' \<Ztypecolon> U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> (k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T') \<^emph> W' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (x \<Ztypecolon> (k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True
\<Longrightarrow> y' \<Ztypecolon> U' \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T') \<^emph> W' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (x \<Ztypecolon> (n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::{share_one,sep_magma}, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Generated_Rule_def atomize_imp atomize_conj Action_Tag_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast


lemma [\<phi>reason 2000]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> ((m * n) \<odiv> T) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> m \<odiv> T) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> ((m * n) \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> (n \<odiv> m \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE True \<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn'; metis Transformation_def Inhabited_def \<phi>Share_\<phi>Share \<phi>Share_inhabited set_mult_inhabited)

lemma [\<phi>reason 2011]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> ((m * n) \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> ((m * n) \<odiv> U') \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> m \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> ((n \<odiv> m \<odiv> U') \<^emph> R') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2011]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> x' \<Ztypecolon> ((m * n) \<odiv> T') \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<^emph> R' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y \<Ztypecolon> U \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> ((m * n) \<odiv> T) \<^emph> W \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True
\<Longrightarrow> x' \<Ztypecolon> (n \<odiv> m \<odiv> T') \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<^emph> R' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y \<Ztypecolon> U \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> m \<odiv> T) \<^emph> W \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True\<close>
  unfolding Premise_def by simp



text \<open>After all of these normalization, if we encounter the requirement to extract permission n,
  but there is no permission annotation for the current object, we know it is to extract from
  a total permission.\<close>

lemma Structural_Extract_pad_share_left
  [\<phi>reason 2000 except \<open>_ \<Ztypecolon> (_ \<odiv> _) \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True\<close>]:
  \<open> x \<Ztypecolon> (1 \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  by simp

lemma Structural_Extract_pad_share_right
  [\<phi>reason 2000 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<odiv> _) \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True\<close>]:
  \<open> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (1 \<odiv> T) \<^emph> W \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph> W \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  by simp


lemma [\<phi>reason 2011 except \<open>_ \<Ztypecolon> (_ \<odiv> _) \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True\<close>]:
  \<open> x \<Ztypecolon> (1 \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> (n \<odiv> U') \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> (1 \<odiv> T') \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (y' \<Ztypecolon> (n \<odiv> U') \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<^emph> W' \<w>\<i>\<t>\<h> P') \<and> P) @action \<A>SE True\<close>
  by simp

lemma [\<phi>reason 2011 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<odiv> _) \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True\<close>]:
  \<open> y' \<Ztypecolon> (n \<odiv> U') \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> (1 \<odiv> T') \<^emph> W' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (x \<Ztypecolon> (1 \<odiv> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True
\<Longrightarrow> y' \<Ztypecolon> (n \<odiv> U') \<^emph> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<^emph> W' \<w>\<i>\<t>\<h>
      (Reverse_Transformation RP (x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (n \<odiv> U) \<^emph> R \<w>\<i>\<t>\<h> P) \<and> P') @action \<A>SE True\<close>
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

consts branch_convergence :: \<open>action\<close> \<comment> \<open>main stage\<close>
       branch_convergence':: \<open>action\<close> \<comment> \<open>pre stage\<close>

declare [[\<phi>reason_default_pattern
    \<open>If ?P ?A ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence \<close> \<Rightarrow> \<open>If ?P ?A ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence \<close> (100)
and \<open>If ?P ?A ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence'\<close> \<Rightarrow> \<open>If ?P ?A ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence'\<close> (100)
and \<open>If ?P ?A ?B = _ @action branch_convergence \<close> \<Rightarrow> \<open>If ?P ?A ?B = _ @action branch_convergence \<close> (100)
]]

lemma [\<phi>reason 3000 for \<open>If _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action invoke_branch_convergence\<close>]:
  \<open> Simplify (assertion_simps undefined) A' A
\<Longrightarrow> Simplify (assertion_simps undefined) B' B
\<Longrightarrow> If P A' B' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C @action branch_convergence'
\<Longrightarrow> If P A  B  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C @action invoke_branch_convergence \<close>
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


subsubsection \<open>Fallback and Termination\<close>

lemma [\<phi>reason 10]:
  \<open>If P A B = If P A B @action branch_convergence\<close>
  unfolding Action_Tag_def ..

lemma [\<phi>reason 3000 for \<open>If ?P ?A ?A'' = ?X @action branch_convergence\<close>]:
  \<open>If P A A = A @action branch_convergence\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 20]:
  " If P T U = Z @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P x y \<Ztypecolon> Z) @action branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 3000 for \<open>If _ (_ \<Ztypecolon> _) (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P x y \<Ztypecolon> T) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 3000 for \<open>If ?P ?A ?A'' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X @action branch_convergence'\<close>]:
  \<open>If P A A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A @action branch_convergence'\<close>
  unfolding Action_Tag_def Transformation_def by simp


subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3000]:
  \<open>If P A 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (A \<s>\<u>\<b>\<j> P) @action branch_convergence'\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: \<phi>expns zero_set_def)

lemma [\<phi>reason 3000]:
  \<open>If P 0 A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (A \<s>\<u>\<b>\<j> \<not> P) @action branch_convergence'\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: \<phi>expns zero_set_def)


subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 1400]:
  \<open> If P (L \<s>\<u>\<b>\<j> Q1 \<and> Q2) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action branch_convergence'
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> Q1 \<s>\<u>\<b>\<j> Q2) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action branch_convergence' \<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1400]:
  \<open> If P L (R \<s>\<u>\<b>\<j> Q1 \<and> Q2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action branch_convergence'
\<Longrightarrow> If P L (R \<s>\<u>\<b>\<j> Q1 \<s>\<u>\<b>\<j> Q2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action branch_convergence' \<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1380]:
  \<open> If P QL QR = Q @action branch_convergence
\<Longrightarrow> If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence'
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> QL) (R \<s>\<u>\<b>\<j> QR) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<s>\<u>\<b>\<j> Q) @action branch_convergence'\<close>
  unfolding Action_Tag_def Transformation_def by force

lemma [\<phi>reason 1300]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  \<open> If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence'
\<Longrightarrow> If P (L \<s>\<u>\<b>\<j> Q) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<s>\<u>\<b>\<j> P \<longrightarrow> Q) @action branch_convergence'\<close>
  unfolding Transformation_def Action_Tag_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1300]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  \<open> If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence'
\<Longrightarrow> If P L (R \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<s>\<u>\<b>\<j> \<not>P \<longrightarrow> Q) @action branch_convergence'\<close>
  unfolding Action_Tag_def Transformation_def by (simp add: \<phi>expns)


subsubsection \<open>Existential\<close>

lemma Conv_Merge_Ex_both_imp:
  \<open> (\<And>x. If P (L x) (R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X x @action branch_convergence')
\<Longrightarrow> If P (\<exists>* x. L x) (\<exists>* x. R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. X x) @action branch_convergence' \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; blast)

lemma Conv_Merge_Ex_R_imp [\<phi>reason 1100]:
  \<open> (\<And>x. If P L (R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X x @action branch_convergence')
\<Longrightarrow> If P L (\<exists>* x. R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. X x) @action branch_convergence' \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; simp add: set_eq_iff \<phi>expns; blast)

lemma [\<phi>reason 1100]:
  \<open> (\<And>x. If P (L x) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X x @action branch_convergence)
\<Longrightarrow> If P (\<exists>* x. L x) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. X x) @action branch_convergence \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases P; simp add: set_eq_iff \<phi>expns; blast)

text \<open>The merging recognizes two existential quantifier are identical if their type and variable name
  are the same. If so it uses Conv_Merge_Ex_both to merge the quantification,
  or else the right side is expanded first.\<close>

\<phi>reasoner_ML Merge_Existential_imp 2000 (\<open>If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X\<close>) =
\<open>fn (ctxt,sequent) =>
  let
    val ((Const (\<^const_name>\<open>If\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exa,tya,_))
                                         $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exb,tyb,_))), _, _)
        = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
    val sequent' = if exa = exb andalso tya = tyb
                   then @{thm Conv_Merge_Ex_both_imp} RS sequent
                   else @{thm Conv_Merge_Ex_R_imp} RS sequent
  in Seq.single (ctxt, sequent')
  end\<close>



subsubsection \<open>Main Procedure\<close>

(*
lemma [\<phi>reason 2000 for \<open>If ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X @action branch_convergence\<close>]:
  " If P x y = z @action branch_convergence
\<Longrightarrow> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence"
  unfolding Action_Tag_def Transformation_def by (cases P; simp) *)

definition \<open>Branch_Convergence_Type_Pattern type the_type_to_match \<equiv> Trueprop True\<close>
  \<comment> \<open>Given a \<open>type\<close>, what is the pattern of the correspondence type to be merged from the opposite branch?\<close>

lemma [\<phi>reason 10 for \<open>PROP Branch_Convergence_Type_Pattern ?X ?X'\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern X X\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200 for \<open>PROP Branch_Convergence_Type_Pattern (Val ?v ?T) (Val ?v ?T')\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern (Val v T) (Val v T')\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200]:
  \<open> PROP Branch_Convergence_Type_Pattern T T'
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * \<blangle> y \<Ztypecolon> T' \<brangle> \<w>\<i>\<t>\<h> Any
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> T') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Z @action branch_convergence
\<Longrightarrow> If P L R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence'
\<Longrightarrow> If P (L * (x \<Ztypecolon> T)) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Z @action branch_convergence'\<close>
  unfolding Action_Tag_def FOCUS_TAG_def
  by (smt (z3) Transformation_def set_mult_expn)


subsubsection \<open>Convergence of Structural Nodes\<close>

lemma [\<phi>reason 1200 for \<open>If ?P (_ \<Ztypecolon> _ \<odiv> _) (_ \<Ztypecolon> _ \<odiv> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P n m = nm @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> n \<odiv> T) (y \<Ztypecolon> m \<odiv> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> nm \<odiv> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>Share_transformation)

lemma [\<phi>reason 1200 for \<open>If _ ((_,_) \<Ztypecolon> _ \<^emph> _) ((_,_) \<Ztypecolon> _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (x' \<Ztypecolon> T') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x'' \<Ztypecolon> T'' @action branch_convergence
\<Longrightarrow> If P (y \<Ztypecolon> U) (y' \<Ztypecolon> U') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y'' \<Ztypecolon> U'' @action branch_convergence
\<Longrightarrow> If P ((x,y) \<Ztypecolon> T \<^emph> U) ((x',y') \<Ztypecolon> T' \<^emph> U') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((x'',y'') \<Ztypecolon> T'' \<^emph> U'') @action branch_convergence\<close>
  unfolding Action_Tag_def apply (cases P; simp add: \<phi>Prod_transformation)
   apply (rule \<phi>Prod_transformation[where Pa=True and Pb=True, simplified], assumption, assumption)
  by (rule \<phi>Prod_transformation[where Pa=True and Pb=True, simplified], assumption, assumption)

(* (*TESTING... re-enable them for performance*)
lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> _ \<^bold>\<rightarrow>\<^sub>@ _) (_ \<Ztypecolon> _ \<^bold>\<rightarrow>\<^sub>@ _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>MapAt_L_cast)

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> _ \<^bold>\<rightarrow> _) (_ \<Ztypecolon> _ \<^bold>\<rightarrow> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (y \<Ztypecolon> k \<^bold>\<rightarrow> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> k \<^bold>\<rightarrow> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>MapAt_cast)

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> Val _ _) (_ \<Ztypecolon> Val _ _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> Val v T) (y \<Ztypecolon> Val v U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Val v Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: Val_transformation)

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<black_circle> _) (_ \<Ztypecolon> \<black_circle> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> \<black_circle> T) (y \<Ztypecolon> \<black_circle> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> \<black_circle> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>Some_cast)
*)

(* fix me!!!
lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<black_circle> _) (_ \<Ztypecolon> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> Any
\<Longrightarrow> If P (x \<Ztypecolon> \<black_circle> T) (y \<Ztypecolon> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P (Some x') None \<Ztypecolon> Itself) @action branch_convergence\<close>
  unfolding Action_Tag_def     
  \<medium_left_bracket> premises T[\<phi>reason for action \<open>to Itself\<close>]  
    cases \<medium_left_bracket> to Itself \<medium_right_bracket>. \<medium_left_bracket> to Itself \<medium_right_bracket>. ;; \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<circle>) (_ \<Ztypecolon> \<black_circle> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> y \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> Any
\<Longrightarrow> If P (x \<Ztypecolon> \<circle>) (y \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (If P None (Some y') \<Ztypecolon> Itself) @action branch_convergence\<close>
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
        If P (x' \<Ztypecolon> T) (y' \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If P (za x') (zb y') \<Ztypecolon> Z @action branch_convergence)
\<Longrightarrow> If P (x \<Ztypecolon> Fa T) (y \<Ztypecolon> Fb U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If P (ma za x) (mb zb y) \<Ztypecolon> Fz Z @action branch_convergence \<close>
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
lemma branch_convergence_general_rule:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> If P (fa x \<Ztypecolon> T) (fa y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fb z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> Fa T) (y \<Ztypecolon> Fa U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Fb Z) @action branch_convergence \<close>
  unfolding Action_Tag_def Transformation_Functor_def
  by (cases P; simp)

\<phi>reasoner_ML branch_convergence_general_rule 50 (\<open>If _ (_ \<Ztypecolon> _) (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>) = \<open>
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
                          @{thm "branch_convergence_general_rule"}
             in SOME ((ctxt, rule RS sequent), Seq.empty) end
            handle THM _ => NONE
         | _ => NONE
  end)
\<close>
*)


lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> Nosep _) (_ \<Ztypecolon> Nosep _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> Nosep T) (y \<Ztypecolon> Nosep U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Nosep Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: Nosep_cast)

(* subsubsection \<open>Object\<close>

definition EqualAddress :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool "
  where "EqualAddress _ _ = True"

lemma [\<phi>reason]:
  "\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a1 = a2
   \<Longrightarrow> EqualAddress (a1 \<Zinj> x1 \<Ztypecolon> T1) (a2 \<Zinj> x2 \<Ztypecolon> T2) "
  unfolding EqualAddress_def .. *)

subsubsection \<open>Unfold\<close>

lemma [\<phi>reason 2000]:
  " If P L (N * R1 * R2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence
\<Longrightarrow> If P L (N * (R1 * R2)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence"
  for N :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason 2000]:
  " If P (L1 * L2 * L3) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence
\<Longrightarrow> If P (L1 * (L2 * L3)) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)


subsubsection \<open>Eliminate Void Hole\<close>

lemma [\<phi>reason 2000]:
  " If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence
\<Longrightarrow> If P L (R * 1) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence
\<Longrightarrow> If P L (1 * R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L (R' * R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence
\<Longrightarrow> If P L (R' * 1 * R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence
\<Longrightarrow> If P (L * 1) R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action branch_convergence"
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
  by (simp; rule implies_left_prod[where U=\<open>Yr * Y\<close>, simplified mult.assoc[symmetric]]; simp)

lemma Gen_Synthesis_Rule_transformation_11:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P))
      Ant
      (PROP Ant \<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P @action synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by (simp; rule implies_left_prod; simp)

lemma Gen_Synthesis_Rule_transformation_10:
  \<open> PROP Gen_Synthesis_Rule
      (Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P))
      Ant
      (PROP Ant \<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<w>\<i>\<t>\<h> P @action synthesis) \<close>
  unfolding Gen_Synthesis_Rule_def Action_Tag_def
  by (rule implies_left_prod; simp)

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

definition Is_Literal :: \<open>'a \<Rightarrow> bool\<close> where \<open>Is_Literal _ \<longleftrightarrow> True\<close>

lemma Is_Literal_internal_rule:
  \<open>Is_Literal any\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(x \<open>should be a literal\<close>)
\<Longrightarrow> Is_Literal x\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Is_Literal True\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Is_Literal False\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Is_Literal 0\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open> Is_Literal x
\<Longrightarrow> Is_Literal (Suc x)\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Is_Literal 1\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open>Is_Literal (numeral x)\<close> unfolding Is_Literal_def ..

lemma [\<phi>reason 1000]:
  \<open> Is_Literal x
\<Longrightarrow> Is_Literal (- x)\<close>
  unfolding Is_Literal_def ..

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
