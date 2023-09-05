chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

(*Entirely depreciated!*)

theory IDE_CP_Reasoning2
  imports IDE_CP_Applications1
begin


(*
subsection \<open>Extract a Value\<close>

definition \<open>Extract_a_Value (S_in::assn) S_out val_out \<longleftrightarrow> (S_in \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S_out \<w>\<i>\<t>\<h> val_out)\<close>

text \<open>\<^prop>\<open>Extract_a_Value S_in S_out val_out\<close> removes the first (right-most) value from the
  input assertion \<open>S_in\<close> and gives the specification theorem of the removed value in \<open>val_out\<close>.

  The process is used during assigning a local value to a binding which
    enables user to access the value later.
  The specification theorem of the value is in form \<^prop>\<open>\<phi>arg.dest raw_val \<in> (x \<Ztypecolon> T)\<close>.
  The binding is bound with this theorem which is used when later loading this value back
    to the state sequent when user is accessing the value.
\<close>

lemma [\<phi>reason 1200 for \<open>Extract_a_Value (?R \<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T) ?R ?V\<close>]:
  \<open>Extract_a_Value (R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T) R (\<phi>arg.dest v \<in> (x \<Ztypecolon> T))\<close>
  unfolding Extract_a_Value_def Transformation_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> Extract_a_Value R R' V
\<Longrightarrow> Extract_a_Value (R\<heavy_comma> X) (R'\<heavy_comma> X) V\<close>
  unfolding Extract_a_Value_def
  by (rule transformation_right_frame)

lemma [\<phi>reason 1000]:
  \<open> ERROR TEXT(\<open>The assertion has no value.\<close>)
\<Longrightarrow> Extract_a_Value R R' V\<close>
  by blast

lemma apply_extract_a_value:
  \<open> \<c>\<u>\<r>\<r>\<e>\<n>\<t> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S
\<Longrightarrow> Extract_a_Value S S' V
\<Longrightarrow> (\<c>\<u>\<r>\<r>\<e>\<n>\<t> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S') \<and> V\<close>
  unfolding Extract_a_Value_def
  using \<phi>apply_implication . *)







(*moved*)
section \<open>\<exists>-free ToA Reasoning with Normalization\<close>

(*TODO: move me*)

text \<open>The section and the next section present the main reasoning procedure for transformations of
  abstraction in the system. The section gives the part passing every element in the right hand side
  of a transformation goal, i.e., find the transformation of the target objects one by one, using
  the remained source objects of (the transformation of) the previous object as the source of the
  next transformation goal for the next object.

  The next section gives the other part that passes the left hand side, i.e., for a certain target
  object, search the source objects one by one to complete the transformation towards the target,
  using the remained unsolved target proportion of the previous search as the goal of
  the next search in the next source object.

  In the reasoning processes, we only consider logical connectives that have an interpretation of refinement.
  They include, \<open>\<or>, \<exists>, \<^emph>, \<and>\<close>. \<open>\<forall>\<close> is planned.
  \<open>\<not>\<close> and \<open>\<rightarrow>\<close> are depreciated, because we cannot interpret from them what is the exact refinement
  relation and the abstract object. \<open>@\<close> is only used in propositional constraints.
\<close>



(*
lemma "_NToA_init_focus_":
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y' \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Simplify_def
  by simp

lemma "_NToA_init_by_focus_":
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y' \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Simplify (assertion_simps undefined) R' R
\<Longrightarrow> Identity_Element\<^sub>I R' Q
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> Q\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def Simplify_def Identity_Element\<^sub>I_def
  by (simp; metis Transformation_def transformation_right_frame mult_1_class.mult_1_left) *)









(* lemma [\<phi>reason 25 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  " \<r>RECURSION_GUARD(ToA_Annotation X) (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R1 * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> Identity_Element\<^sub>I R1
\<Longrightarrow> R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding FOCUS_TAG_def Transformation_def split_paired_All Identity_Element\<^sub>I_def \<r>Recursion_Guard_def
  by (metis mult_1_class.mult_1_left set_mult_expn) *)

(* lemma [\<phi>reason 1050 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> ?Y \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA True ?G\<close>
   except \<open>(?X'::?'a::sep_magma_1 set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> ?Y' \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA True ?G\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P @action reason_NToA True G\<close>
  \<comment> \<open>If it isn't unital, it cannot be reasoned by this procedure, so
      a fallback here handles it.\<close>
  unfolding FOCUS_TAG_def Action_Tag_def . *)

subsection \<open>For Specific \<phi>-Types\<close>

subsubsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-beta-eta-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1215 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  "R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R"
  unfolding REMAINS_def Transformation_def by simp

lemma [\<phi>reason 1210 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                    if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]:
  " y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def
  by (simp add: Val_expn times_list_def) metis

lemma [\<phi>reason 1200]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R'\<heavy_comma> X \<w>\<i>\<t>\<h> P"
  unfolding REMAINS_def split_paired_All
  by (simp; metis transformation_left_frame mult.assoc mult.commute)

lemma [\<phi>reason 1200 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?V \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<w>\<i>\<t>\<h> P"
  unfolding REMAINS_def
  by (metis (no_types, opaque_lifting) transformation_right_frame mult.assoc mult.commute)



subsection \<open>General Search\<close>

lemma [\<phi>reason default 12 except \<open> (_ :: ?'a :: sep_semigroup set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P"
  unfolding REMAINS_def Transformation_def
  by clarsimp blast


(*
lemma NToA_skip [\<phi>reason 65 for \<open> _ * _ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?X \<brangle> \<w>\<i>\<t>\<h> _\<close>
                            ]:
\<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * H * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P"
  for H :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding FOCUS_TAG_def Transformation_def
  by clarsimp
     (smt (verit, best) sep_disj_commuteI sep_disj_multD1 sep_disj_multI1 sep_mult_assoc' sep_mult_commute)

lemma [\<phi>reason 60 for \<open> _ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> ?P\<close>
                  except \<open> _ * _ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> ?P\<close>
                        ]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> H * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P"
  for H :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding FOCUS_TAG_def Transformation_def
  by (clarsimp, insert sep_disj_commute sep_mult_commute, blast)
*)  

(* lemma [\<phi>reason 1200
    on \<open>?R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<w>\<i>\<t>\<h> ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m @GOAL ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m @GOAL G
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V @GOAL G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>
*)


subsection \<open>Entry Point of Next Procedures\<close>

text \<open>The entry point of Structural Extraction is given in the section for SE.
      It covers all the form of \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T\<close> and \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>\<close>



(*DO NOT REMOVE, for Auto_Transform_Hint
lemma [\<phi>reason 2000]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X <changes-to> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P\<close>
  \<comment> \<open>This is the entry point of Auto_Transform_Hint !\<close>
  unfolding Changes_To_def .

lemma [\<phi>reason 2000]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X <changes-to> Y \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P\<close>
  \<comment> \<open>This is the entry point of Automatic_Rule !\<close>
  unfolding Changes_To_def .
*)

(* subsection \<open>Structural Pairs\<close> (*depreciated*)

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def . *)


section \<open>Separation Extraction\<close>

text \<open>Extract a \<phi>-type assertion with potential remainders from a \<open>*\<close>-sequence of \<phi>-types.
  Extracting a \<phi>-type assertion (with potential remainders) from a \<phi>-type assertion, is not
  its job, but the usual transformation reasoning (the one having no tags) of the source \<phi>-type.
\<close>

text \<open>The canonical form is where all permission annotation are on leaves.
  It minimizes fragments. (TODO: move this)\<close>

text \<open>Log:
The assumption of identity element is bad. Consider a transformation functor whose container algebra
is unital but element algebra is not. The container goes to \<A>SE and leads us to apply \<A>SE on the
elements also, but that is wrong. We cannot assume the element algebra is also unital.
So then, instead of splitting the case of unitral elements or not, why not from the very beginning
we only assume non-unital algebra and use \<A>SEi only?
\<close>

(*
consts (*\<A>SE  :: action  \<comment> \<open>Monoidal\<close>*)
       (*\<A>SEi :: action \<comment> \<open>Non-unital semigroup\<close>*)
       (*\<A>SEa :: action \<comment> \<open>Non-Associative\<close>*)
       \<A>merge :: action \<comment> \<open>internal rules used in \<A>SE reasoning\<close> *)

text \<open>\<A>SEi is for algebras having no identity element.
  The reasoning cannot assume the it always remains something and set that
  to the identity element if it actually doesn't remain anything.
  It causes the reasoning essentially changed because we need to use a conditional boolean flag
  \<open>\<half_blkcirc>[Cw] W\<close> to case-analysis if the remainder is produced or not.

  \<open>\<A>SEa\<close> is for the algebras that are not even associative. The separation extraction is totally
  degenerated to one-to-one transformation of each separated cells.

  We use the two actions because they are essentially three different reasoning procedures.
  Their forms of goal are different.

\<comment> \<open>\<A>SE : \<^prop>\<open>x \<Ztypecolon> Source \<^emph> Further_Work \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> Target \<^emph> Remain \<w>\<i>\<t>\<h> some @action \<A>SE\<close>\<close>
\<^item> \<A>SEi: \<open>x \<Ztypecolon> \<black_circle> Source \<^emph> \<half_blkcirc>[Cw] Further \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> \<black_circle> Target \<^emph> \<half_blkcirc>[Cr] Remain \<w>\<i>\<t>\<h> some @action \<A>SEi\<close>
    \<open>\<black_circle>\<close> inserts it into a unital algebra.
(*\<A>SEa: \<^prop>\<open>x \<Ztypecolon> Source \<^emph> Further \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> Target \<w>\<i>\<t>\<h> some @action \<A>SEa\<close>
    It doesn't has the remain part because it cannot has because it is non-associative.
    It must has some unsolved further work because it is separation extraction, of form
      \<^prop>\<open>A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>, not the simple transformation of form \<^prop>\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>.
      To consume \<open>A\<close>, the transformation of \<open>B\<close> to \<open>y \<Ztypecolon> U\<close> must remain some further work.*)

    Note non-associativity also implies non-commutativity, as in our formalization there is no
    algebra that is non-associative but commutative.
\<close>


subsubsection \<open>\<phi>Type Insertion into Unital Algebra\<close>


(*subsubsection \<open>Bi-conditioned Separation\<close>

definition biCond_\<phi>Prod :: \<open> ('v,'x) \<phi> \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('v,'y) \<phi> \<Rightarrow> ('v::sep_magma,'x \<times> 'y) \<phi> \<close> ("_ [_]\<^emph>[_] _" [71,40,40,70] 70)
    \<comment> \<open>\<phi>Type embedding of conditional remainder\<close>
  where \<open>(T [Ca]\<^emph>[Cb] U) \<equiv> if Ca then T \<^emph>[Cb] U else if Cb then (\<lambda>x. snd x \<Ztypecolon> U) else \<top>\<close>

lemma biCond_\<phi>Prod_expn:
  \<open> (x \<Ztypecolon> T [C']\<^emph>[C] U) = (if C' then (x \<Ztypecolon> T \<^emph>[C] U) else if C then (snd x \<Ztypecolon> U) else \<top>) \<close>
  unfolding biCond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

lemma biCond_\<phi>Prod_expn'[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> T [Ca]\<^emph>[C] U) = (if Ca then p \<Turnstile> (x \<Ztypecolon> T \<^emph>[C] U) else if C then p \<Turnstile> (snd x \<Ztypecolon> U) else True) \<close>
  unfolding biCond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

lemma biCond_\<phi>Prod_expn_const[simp]:
  \<open> T [True]\<^emph>[C] U \<equiv> T \<^emph>[C] U \<close>
  \<open> x \<Ztypecolon> T [False]\<^emph>[True] U \<equiv> snd x \<Ztypecolon> U \<close>
  \<open> x \<Ztypecolon> T [False]\<^emph>[False] U \<equiv> \<top> \<close>
  unfolding biCond_\<phi>Prod_def \<phi>Type_def
  by clarsimp+*)

(*
lemma biCond_\<phi>Prod_expn_\<phi>Some:
  \<open>\<black_circle> (T [Ca]\<^emph>[C] U) \<equiv> \<half_blkcirc>[Ca] T \<^emph> \<half_blkcirc>[C] U\<close>
  unfolding atomize_eq
  apply (rule \<phi>Type_eqI; cases C; cases Ca; clarsimp)
  apply force
*)

subsubsection \<open>Auxiliary Rules\<close>



text \<open>Information is always given from left to right below.
      They accept argument from LHS and assign the result to RHS\<close>


subsubsection \<open>Configuration\<close>
(*
ML \<open>fun chk_SE_pattern ctxt tm =
  let fun chk_phityp (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ Var _ $ _) = true
        | chk_phityp (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ v $ _) =
              error ("In a rule of structural extraction, the abstract object of the source has to be a schematic variable\
                     \ but given\n" ^ Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt v)
      fun pattern (\<^Const>\<open>Trueprop\<close> $ X) = pattern X
        | pattern (\<^Const>\<open>Attempt_Fallback\<close> $ _ $ X) = pattern X
        | pattern (\<^Const>\<open>Action_Tag\<close> $ X $ _) = pattern X
        | pattern (Const(\<^const_name>\<open>Transformation\<close>, _) $ A $ B $ _)
            = is_Var (Term.head_of B) orelse is_Var (Term.head_of A) orelse chk_phityp A
   in (pattern tm; NONE)
   handle Match => error ("Malform Structural Extraction rule: \n" ^
                          Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt tm)
  end\<close>
*)

(* TODO!
declare [[ (*TODO!*)
  (*\<phi>reason_default_pattern_ML \<open> _ @action \<A>SEi\<close> \<Rightarrow> \<open>chk_SE_pattern\<close> (1000),*)
  \<phi>reason_default_pattern
      \<open> _ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) \<close>   (105)
  and \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) ) \<close> \<Rightarrow>
      \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) ) \<close>   (105)
  and \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _ ) \<close> \<Rightarrow>
      \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _ ) \<close>   (100)

(*
  and \<open> ?XX @action \<A>SEi \<close> \<Rightarrow>
      \<open> ERROR TEXT(\<open>Malformed Separation Extraction rule\<close> (?XX @action \<A>SEi))\<close> (0)*)
]]
*)

text \<open>TODO!\<close>

text \<open>Task of Structural Extract \<^prop>\<open>(x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y,r) \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P2 @action \<A>SE \<close>,
  given \<^term>\<open>x \<Ztypecolon> T\<close>, expecting \<^term>\<open>y \<Ztypecolon> U\<close>, the reasoner finds the further element \<^term>\<open>w \<Ztypecolon> W\<close>
  that needs to be extracted further and the remain \<^term>\<open>r \<Ztypecolon> R\<close> that remains from the extraction.
  \<^prop>\<open>x \<Ztypecolon> (Source \<^emph> Further_Task) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> (Target \<^emph> Remain) \<w>\<i>\<t>\<h> some_info\<close>.

  The original assertion was in a good form, but after the structural extraction, the form is destroyed.
  Many procedure application or ToA application just change the value (the abstract object) while
  the type structure is basically unchanged. If we can, after the application, recover the original
  form by some reverse transformation, it would be great.

  \<^term>\<open>Auto_Transform_Hint\<close> is for this.
  \<^prop>\<open> x \<Ztypecolon> (Source \<^emph> Further_Task) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> (Target \<^emph> Remain) \<w>\<i>\<t>\<h> (
        Auto_Transform_Hint (y' \<Ztypecolon> From_the_Target \<^emph> With_the_Remains)
                            (x' \<Ztypecolon> Recover_the_Source \<^emph> With_works_to_be_recovered_further) \<and> True
    ) @action \<A>SE \<close>
  The \<open>the_Target\<close> is a pattern having same constant and the rough structure with the \<open>Target\<close>.
  Many SE rules are equipped with a version with Auto_Transform_Hint. The rules maintains the patterns
  \<open>the_Target\<close> and \<open>the_Source\<close>, and later the system can pattern-match \<open>the_Target\<close> after
  the application to instantiate the original form \<open>the_Source\<close> and then recover it by a To-Transformation.

  The \<open>Auto_Transform_Hint\<close> only gives syntactic hint. The \<open>y'\<close> and \<open>x'\<close> are never used and can be any thing.
\<close>

paragraph \<open>Simplification Protect\<close>

(*definition \<open>\<A>SE_Simp_Protect x T W y U R P\<close> 

TODO!!!*)




subsection \<open>Termination\<close>

paragraph \<open>\<open>T \<longrightarrow> \<circle>\<close>\<close>

(* preserved for documenting
lemma [\<phi>reason 3010]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((), fst x) \<Ztypecolon> (\<circle> \<^emph> T) @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3011]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((), fst x) \<Ztypecolon> (\<circle> \<^emph> T) \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> \<circle> \<^emph> T) (x' \<Ztypecolon> T \<^emph> \<circle>) \<and> True) @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')
*)

paragraph \<open>\<open>\<circle> \<longrightarrow> T\<close>\<close>

(* preserved for documenting
subparagraph \<open>Monoidal\<close>

lemma [\<phi>reason 3000]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph> \<circle>) (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3010]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> @action \<A>SE) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3011]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph> \<circle>) (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SE) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')
*)

(*
subparagraph \<open>Non-unital semigroup\<close>

lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (U \<^emph>[False] \<top>\<^sub>\<phi>) @action \<A>SEi \<close>
  unfolding Action_Tag_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (U \<^emph>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> U' \<^emph>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> T' [False]\<^emph>[True] U') \<and> True) @action \<A>SEi \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3010 for \<open> Attempt_Fallback (_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (U \<^emph>[False] \<top>\<^sub>\<phi>) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3011 for \<open> Attempt_Fallback (_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> ( U \<^emph>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
                     (Auto_Transform_Hint (y' \<Ztypecolon> U' \<^emph>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> T' [False]\<^emph>[True] U') \<and> True) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)
*)


(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> _ @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SEi \<close>
  unfolding Action_Tag_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U') \<and> True) @action \<A>SEi \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3010 for \<open> Attempt_Fallback (_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> _ @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3011 for \<open> Attempt_Fallback (_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
                     (Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U') \<and> True) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)
*)

(*subparagraph \<open>Non-associative\<close>

lemma [\<phi>reason 3000]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T @action \<A>SEa \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T') (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SEa \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3010]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T @action \<A>SEa) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3011]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T') (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SEa) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')
*)

paragraph \<open>\<open>T \<longrightarrow> T\<close>\<close>

(* preserved for documenting
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph> \<circle>) @action \<A>SE \<close>
  unfolding Action_Tag_def
  using transformation_refl .

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph> \<circle>) \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph> \<circle>) (x'' \<Ztypecolon> T' \<^emph> \<circle>) \<and> True) @action \<A>SE \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  using transformation_refl .
*)
(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph>[_] _ \<w>\<i>\<t>\<h> _ \<close>]:
  \<open> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) \<close>]:
  \<open> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> T' \<^emph>[False] \<top>\<^sub>\<phi>) \<and> True) \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')
*)
(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?T' \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SEi \<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?T' \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<and> True) @action \<A>SEi \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')
*)

(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> _ @action \<A>SEa \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst x \<Ztypecolon> T @action \<A>SEa \<close>
  for T :: \<open>'b \<Rightarrow> 'a :: sep_magma_1 set\<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEa \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst x \<Ztypecolon> T \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T') (x'' \<Ztypecolon> T' \<^emph> \<circle>) \<and> True) @action \<A>SEa \<close>
  for T :: \<open>'b \<Rightarrow> 'a :: sep_magma_1 set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Action_Tag_def Transformation_def
  by clarsimp
*)

subsection \<open>Normalization\<close>

subsubsection \<open>Non-Unital Algebra\<close>

(*convention: \<A>SEi reasoning can send upward the Cw/Cr*)

(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[True] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[Cw] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cw
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[True] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[False] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[Cw] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> Cw
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[False] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 3000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[True] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[Cr] R) \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cr
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[True] R) \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 3000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[False] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[Cr] R) \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> Cr
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[False] R) \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp
*)

subsection \<open>Fall back\<close>

(*
Structural Extraction (SE) is free from backtrack because any \<phi>-type can have a (weakest)
rule that does nothing and just send the Y (the target) to the W (the further request).
Therefore, the fallback rules here are just those not configured with SE.
*)

subsubsection \<open>Monoidal\<close>

(* preserved for documenting
lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 2 for \<open>Attempt_Fallback ((_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _ @action \<A>SE)\<close>]:
  \<open> Attempt_Fallback ((x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 3]:
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 4 for \<open>Attempt_Fallback ((_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> Auto_Transform_Hint _ _ \<and> _ @action \<A>SE)\<close>]:
  \<open> Attempt_Fallback ((x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (simp add: mult.commute \<phi>Prod_expn')
 
lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 2 for \<open>(_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _ @action \<A>SE\<close>]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> (x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 3]:
  \<open> x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 4 for \<open>(_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> Auto_Transform_Hint _ _ \<and> _ @action \<A>SE\<close>]:
  \<open> (x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (simp add: mult.commute \<phi>Prod_expn')
*)


subsection \<open>Trim Waste\<close>

text \<open>Do we still need it?\<close>

definition \<open>\<A>SE_trim\<^sub>I y R y' R' Q \<equiv> \<forall>U. y \<Ztypecolon> U \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> Q\<close>
definition \<open>\<A>SE_trim\<^sub>E x W x' W' \<equiv> \<forall>T. x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph> W\<close>
definition \<open>\<A>SE_trim\<^sub>I_TH y R y' R' Q (R'\<^sub>H :: 'b2 \<Rightarrow> 'c2 set) (R\<^sub>H :: 'd2 \<Rightarrow> 'c2 set) \<equiv> \<forall>U. y \<Ztypecolon> U \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> Q\<close>
definition \<open>\<A>SE_trim\<^sub>E_TH x W x' W' (W\<^sub>H :: 'b2 \<Rightarrow> 'c2 set) (W'\<^sub>H :: 'd2 \<Rightarrow> 'c2 set) \<equiv> \<forall>T. x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph> W\<close>

declare [[ \<phi>reason_default_pattern
      \<open> \<A>SE_trim\<^sub>E _ ?W _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>E _ ?W _ _ \<close>   (100)
  and \<open> \<A>SE_trim\<^sub>I ?y ?R _ _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>I ?y ?R _ _ _ \<close>   (100)
  and \<open> \<A>SE_trim\<^sub>E_TH _ ?W _ _ _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>E_TH _ ?W _ _ _ _ \<close>   (110)
  and \<open> \<A>SE_trim\<^sub>I_TH ?y ?R _ _ _ _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>I_TH ?y ?R _ _ _ _ _ \<close>   (110)
]]

(* preserved for documenting
lemma \<A>SE_clean_waste:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> \<A>SE_trim\<^sub>I y R y' R' Q
\<Longrightarrow> \<A>SE_trim\<^sub>E x W x' W'
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> P \<and> Q @action \<A>SE\<close>
  unfolding Action_Tag_def Transformation_def \<A>SE_trim\<^sub>I_def \<A>SE_trim\<^sub>E_def
  by blast

lemma \<A>SE_clean_waste_TH:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> U\<^sub>H \<^emph> R\<^sub>H) (x'1 \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P @action \<A>SE
\<Longrightarrow> \<A>SE_trim\<^sub>I_TH y R y' R' Q R'\<^sub>H R\<^sub>H
\<Longrightarrow> \<A>SE_trim\<^sub>E_TH x W x' W' W'\<^sub>H W\<^sub>H
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'4 \<Ztypecolon> U\<^sub>H \<^emph> R'\<^sub>H) (x'4 \<Ztypecolon> T\<^sub>H \<^emph> W'\<^sub>H) \<and> P \<and> Q @action \<A>SE\<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def HOL.simp_thms(22) Transformation_def
            \<A>SE_trim\<^sub>I_TH_def \<A>SE_trim\<^sub>E_TH_def
  by blast
*)

(*\<A>SEi doesn't need trim.  not now... when we also use \<A>SEi for monoidal algebra*)

(*
lemma \<A>SEa_clean_waste:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> \<A>SE_trim\<^sub>E x W x' W'
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>SEa\<close>
  unfolding Action_Tag_def Transformation_def \<A>SE_trim\<^sub>E_def
  by blast

lemma \<A>SEa_clean_waste_TH:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y\<^sub>H \<Ztypecolon> U\<^sub>H) (x\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P @action \<A>SEa
\<Longrightarrow> \<A>SE_trim\<^sub>E_TH x W x' W' W'\<^sub>H W\<^sub>H
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y\<^sub>H \<Ztypecolon> U\<^sub>H) (x'\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W'\<^sub>H) \<and> P @action \<A>SEa\<close>
  unfolding Action_Tag_def Transformation_def Auto_Transform_Hint_def HOL.simp_thms(22) \<A>SE_trim\<^sub>E_TH_def
  by blast
*)

lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>I y R y R True \<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I (x,y) \<circle> (x, ()) \<circle> True \<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I (x,(r,())) (R \<^emph> \<circle>) (x,r) R True\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I (x,((),r)) (\<circle> \<^emph> R) (x,r) R True\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>I_TH y R y R True R\<^sub>H R\<^sub>H \<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def HOL.simp_thms(22)
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I_TH (x,y) \<circle> (x, ()) \<circle> True \<circle> \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I_TH (x,(r,())) (R \<^emph> \<circle>) (x,r) R True (\<circle> \<^emph> R\<^sub>H) R\<^sub>H\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I_TH (x,(r,())) (R \<^emph> \<circle>) (x,r) R True (R\<^sub>H \<^emph> \<circle>) R\<^sub>H\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  by (simp add: \<phi>Prod_expn')


lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>E x W x W \<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E (x,()) \<circle> (x,()) \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E (fst xw,(snd xw,())) (W \<^emph> \<circle>) xw W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E (x,(w,())) (W \<^emph> \<circle>) (x,w) W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E (fst xw,((), snd xw)) (\<circle> \<^emph> W) xw W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E (x,((),w)) (\<circle> \<^emph> W) (x,w) W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (simp add: \<phi>Prod_expn')


lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>E_TH x W x W W\<^sub>H W\<^sub>H \<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def HOL.simp_thms(22)
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E_TH (x,()) \<circle> (x,()) \<circle> \<circle> \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def HOL.simp_thms(22)
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E_TH (fst xw,((), snd xw)) (\<circle> \<^emph> W) xw W W\<^sub>H (\<circle> \<^emph> W\<^sub>H)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E_TH (x,((),w)) (\<circle> \<^emph> W) (x,w) W W\<^sub>H (\<circle> \<^emph> W\<^sub>H)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E_TH (fst xw,(snd xw,())) (W \<^emph> \<circle>) xw W W\<^sub>H (W\<^sub>H \<^emph> \<circle>)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E_TH (x,(w,())) (W \<^emph> \<circle>) (x,w) W W\<^sub>H (W\<^sub>H \<^emph> \<circle>)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (simp add: \<phi>Prod_expn')



subsection \<open>Stepwise of Product Separations\<close>

(* preserved for documenting
paragraph \<open>Monoidal\<close>

declare [[\<phi>trace_reasoning = 2]]

lemma Structural_Extract_\<phi>Prod_right:
  \<open> Try S1 ((fst a, fst (snd a)) \<Ztypecolon> A \<^emph> WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph> B \<w>\<i>\<t>\<h> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd b, snd (snd a)) \<Ztypecolon> B \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<^emph> C \<w>\<i>\<t>\<h> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> a \<Ztypecolon> A \<^emph> WY \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph> C \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SE \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
\<medium_left_bracket> premises Y and X
  apply_rule Y[THEN transformation_left_frame, where R=\<open>snd (snd a) \<Ztypecolon> WX\<close>]
  apply_rule X[THEN transformation_right_frame, where R=\<open>fst b \<Ztypecolon> Y\<close>]
\<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_right [THEN \<A>SE_clean_waste, \<phi>reason 1200]

lemma [THEN \<A>SE_clean_waste_TH, \<phi>reason 1201]:
  \<open> Try S1 ((fst a, fst (snd a)) \<Ztypecolon> A \<^emph> WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph> B \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y' \<^emph> B') (x'1 \<Ztypecolon> A' \<^emph> WY') \<and> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd b, snd (snd a)) \<Ztypecolon> B \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<^emph> C \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> X' \<^emph> C') (x'2 \<Ztypecolon> B' \<^emph> WX') \<and> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> a \<Ztypecolon> A \<^emph> WY \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph> C \<w>\<i>\<t>\<h> 
      Auto_Transform_Hint (y'3 \<Ztypecolon> (Y' \<^emph> X') \<^emph> C') (x'3 \<Ztypecolon> A' \<^emph> WY' \<^emph> WX') \<and> P1 \<and> P2 @action \<A>SE \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and A' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_right .


lemma Structural_Extract_\<phi>Prod_left:
  \<open> Try S1 ((fst (fst x), fst w_ru) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<^emph> Rt \<w>\<i>\<t>\<h> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> U \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w_ru \<Ztypecolon> W \<^emph> Ru \<w>\<i>\<t>\<h> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y_rt, snd y_rt, snd w_ru) \<Ztypecolon> Y \<^emph> (Rt \<^emph> Ru) \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SE \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
  \<medium_left_bracket> premises T and U
    apply_rule U[THEN transformation_right_frame, where R=\<open>fst (fst x) \<Ztypecolon> T\<close>]
    apply_rule T[THEN transformation_left_frame, where R=\<open>snd w_ru \<Ztypecolon> Ru\<close>]
  \<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_left [THEN \<A>SE_clean_waste, \<phi>reason 1200]

lemma [THEN \<A>SE_clean_waste_TH, \<phi>reason 1201]:
  \<open> Try S1 ((fst (fst x), fst w_ru) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<^emph> Rt \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y' \<^emph> Rt') (x'1 \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> U \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w_ru \<Ztypecolon> W \<^emph> Ru \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> W' \<^emph> Ru') (x'2 \<Ztypecolon> U' \<^emph> W2') \<and> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y_rt, snd y_rt, snd w_ru) \<Ztypecolon> Y \<^emph> (Rt \<^emph> Ru) \<w>\<i>\<t>\<h>
      Auto_Transform_Hint (y'3 \<Ztypecolon> Y' \<^emph> (Rt' \<^emph> Ru')) (x'3 \<Ztypecolon> (T' \<^emph> U') \<^emph> W2')
      \<and> P1 \<and> P2 @action \<A>SE \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and T' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_left .
*)



subsection \<open>Entry Point\<close>

(* preserved for documenting
lemma enter_SE:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P1 @action \<A>SE
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR \<w>\<i>\<t>\<h> P2 \<comment> \<open>Here, we force the reasoning entering a mode where
                                    it always yields a remainder. We can do so as \<A>SE reasoning
                                    assumes unital algebra.\<close>
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR * (snd y \<Ztypecolon> R) \<w>\<i>\<t>\<h> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def REMAINS_simp
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    apply_rule T1[THEN transformation_left_frame, where R=RR]
  \<medium_right_bracket> .

lemma enter_SE_TH:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> U' \<^emph> R') (x'1 \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'2 \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR * (snd y \<Ztypecolon> R) \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'3 \<Ztypecolon> U') (A' * (x'3 \<Ztypecolon> T')) \<and> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SE .
*)



(* no need
lemma enter_SEi_\<phi>Some:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P1 @action \<A>SEi
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h> P2) else (P2, Crr) = (True, False)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> \<black_circle> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> \<black_circle> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> \<black_circle> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup option BI\<close>
  unfolding Action_Tag_def REMAINS_def Simplify_def
  apply (cases Cw; cases Cr; cases Crr;
         simp add: \<phi>Some_\<phi>None_freeobj \<phi>Prod_expn')
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1[THEN transformation_left_frame, where R=RR]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1[THEN transformation_left_frame, where R=RR]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1
    apply_rule T1[THEN transformation_left_frame, where R=A]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1
    apply_rule T1[THEN transformation_left_frame, where R=A]
  \<medium_right_bracket> .

lemma enter_SEi_\<phi>Some_TH:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[Cr] R') (x'1 \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[Cw] W') \<and> P1 @action \<A>SEi
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> \<black_circle> W') A' \<and> P2)
          else (P2, Crr) = (True, False)
\<Longrightarrow> if Cw then ATH = (A' * (x'3 \<Ztypecolon> \<black_circle> T')) else ATH = (x'3 \<Ztypecolon> \<black_circle> T')
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> \<black_circle> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> \<black_circle> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> \<black_circle> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'3 \<Ztypecolon> \<black_circle> U) ATH \<and> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup option BI\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEi_\<phi>Some .
*)




(* preserved for documenting
lemma enter_SEb:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P1 @action \<A>SE
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 \<and> P2 \<and> Q\<close>
  for A :: \<open>'a :: sep_magma_1 set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def
  \<medium_left_bracket> premises T and R and A
    apply_rule A[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    T
    apply_rule R[THEN transformation_right_frame, where R=\<open>fst y \<Ztypecolon> U\<close>]
  \<medium_right_bracket> .

lemma enter_SEb_TH:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> U') (x' \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (w' \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 \<and> P2 \<and> Q\<close>
  for A :: \<open>'a :: sep_magma_1 set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEb .
*)



(* no need
lemma enter_SEbi_\<phi>Some:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P1 @action \<A>SEi
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> \<half_blkcirc>[Cr] R) Q
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma option set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def Premise_def
            Transformation_def
  by clarsimp fastforce

lemma enter_SEbi_\<phi>Some_TH:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U') (x' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[C] W') \<and> P1 @action \<A>SEi
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> \<half_blkcirc>[Cr] R) Q
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (w' \<Ztypecolon> \<black_circle> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U') (A' * (x'' \<Ztypecolon> \<black_circle> T')) \<and> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma option set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEbi_\<phi>Some .
*)




end
