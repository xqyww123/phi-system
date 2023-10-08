chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

(*Entirely depreciated!*)

theory IDE_CP_Reasoning2
  imports IDE_CP_Applications1
begin

subsection \<open>For Specific \<phi>-Types\<close>

subsubsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-beta-eta-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1215 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  "R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R"
  unfolding REMAINS_def Transformation_def by simp

lemma [\<phi>reason 1210 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                    if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o Context.Proof o fst\<close>]:
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

section \<open>Separation Extraction\<close>

(*TODO: move*)

text \<open>Extract a \<phi>-type assertion with potential remainders from a \<open>*\<close>-sequence of \<phi>-types.
  Extracting a \<phi>-type assertion (with potential remainders) from a \<phi>-type assertion, is not
  its job, but the usual transformation reasoning (the one having no tags) of the source \<phi>-type.
\<close>

text \<open>The canonical form is where all permission annotation are on leaves.
  It minimizes fragments. (TODO: move this)\<close>

text \<open>Log:
The assumption of identity element is strong. Consider a transformation functor whose container algebra
is unital but element algebra is not. The container goes to \<A>SE and leads us to apply \<A>SE on the
elements also, but that is wrong. We cannot assume the element algebra is also unital.
So then, instead of splitting the case of unitral elements or not, why not from the very beginning
we only assume non-unital algebra and use \<A>SEi only?
\<close>

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

text \<open>TODO: move\<close>

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

subsection \<open>Fall back\<close>

(*
Structural Extraction (SE) is free from backtrack because any \<phi>-type can have a (weakest)
rule that does nothing and just send the Y (the target) to the W (the further request).
Therefore, the fallback rules here are just those not configured with SE.
*)

text \<open>Do we still need it?\<close>

(*
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

*)

(*
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
*)


end
