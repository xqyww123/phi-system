chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

(*Entirely depreciated!*)

theory IDE_CP_Reasoning2
  imports IDE_CP_Applications1
begin

subsection \<open>For Specific \<phi>-Types\<close>

subsubsection \<open>Value\<close>


text \<open>Priority shouldn't exceed 2000.\<close>


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


section \<open>Derivatives of Transformation \<close>

definition ToA_Getter :: \<open>'a \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 'c::sep_magma BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
           ("\<g>\<e>\<t> _ \<Ztypecolon> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _")
  where \<open>\<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<equiv> Src = (x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R)\<close>

definition ToA_Getter' :: \<open>'a \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 'c::sep_magma BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'w \<Rightarrow> ('c,'w) \<phi> \<Rightarrow> bool\<close>
           ("\<g>\<e>\<t> _ \<Ztypecolon> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _" [21,21,19,19,19,19,21,21] 18)
  where \<open>\<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<equiv> (Src \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>W] w \<Ztypecolon> W) = (x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R)\<close>

definition ToA_Mapper :: \<open>'a \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 'b \<Rightarrow> ('c,'b) \<phi> \<Rightarrow> 'c::sep_magma BI \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
           ("\<s>\<u>\<b>\<s>\<t> _ \<Ztypecolon> _ \<f>\<o>\<r> _ \<Ztypecolon> _ \<f>\<r>\<o>\<m> _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _")
  where \<open>\<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<equiv>
            (Src \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R) \<and> (y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ret)\<close>

definition ToA_Mapper' :: \<open>'b \<Rightarrow> ('c,'b) \<phi> \<Rightarrow> 'a \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 'c::sep_magma BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'w \<Rightarrow> ('c,'w) \<phi> \<Rightarrow> 'c BI \<Rightarrow> 'w' \<Rightarrow> ('c,'w') \<phi> \<Rightarrow> bool\<close>
           ("\<s>\<u>\<b>\<s>\<t> _ \<Ztypecolon> _ \<f>\<o>\<r> _ \<Ztypecolon> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<Ztypecolon> _" [19,21,21,21,19,19,19,19,21,21,19,21,21] 18)
  where \<open> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Target \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<equiv>
            (Src \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>W] w \<Ztypecolon> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R) \<and>
            (y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Target \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>W] w' \<Ztypecolon> W') \<close>

subsection \<open>Conventions\<close>

declare [[\<phi>reason_default_pattern
      \<open>\<s>\<u>\<b>\<s>\<t> ?var_y \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<Ztypecolon> _ \<close> \<Rightarrow>
      \<open>\<s>\<u>\<b>\<s>\<t> ?var_y \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<Ztypecolon> _ \<close>    (100)
  and \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _\<close> \<Rightarrow>
      \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _\<close>   (100)
  and \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<close> \<Rightarrow>
      \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<close>    (100)
  and \<open>\<s>\<u>\<b>\<s>\<t> ?var_y \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _\<close> \<Rightarrow>
      \<open>\<s>\<u>\<b>\<s>\<t> ?var_y \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _\<close>    (100)

  and \<open>\<s>\<u>\<b>\<s>\<t> ?y \<Ztypecolon> ?U \<f>\<o>\<r> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[?C\<^sub>W] ?w \<Ztypecolon> ?W \<t>\<o> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> ?w' \<Ztypecolon> ?W'\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (\<s>\<u>\<b>\<s>\<t> ?y \<Ztypecolon> ?U \<f>\<o>\<r> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[?C\<^sub>W] ?w \<Ztypecolon> ?W \<t>\<o> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> ?w' \<Ztypecolon> ?W'))\<close> (0)
  and \<open>\<g>\<e>\<t> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[?C\<^sub>W] ?w \<Ztypecolon> ?W\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (\<g>\<e>\<t> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[?C\<^sub>W] ?w \<Ztypecolon> ?W))\<close> (0)
  and \<open>\<g>\<e>\<t> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (\<g>\<e>\<t> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R))\<close> (0)
  and \<open>\<s>\<u>\<b>\<s>\<t> ?y \<Ztypecolon> ?U \<f>\<o>\<r> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<t>\<o> ?Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (\<s>\<u>\<b>\<s>\<t> ?y \<Ztypecolon> ?U \<f>\<o>\<r> ?x \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<t>\<o> ?Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R))\<close> (0)
]]

\<phi>reasoner_group \<phi>mapToA_all = (100, [0, 3000])
      \<open>Transformation Mappers\<close>
  and \<phi>mapToA_init = (1000, [1000,1020]) in \<phi>mapToA_all
      \<open>initializaton\<close>

subsection \<open>Preliminary Helpers\<close>

lemma \<phi>Some_mult_contract:
  \<open>(x \<Ztypecolon> \<black_circle> T) * (y \<Ztypecolon> \<black_circle> U) = ((y,x) \<Ztypecolon> \<black_circle> (U \<^emph> T)) \<close>
  by (metis \<phi>Prod_expn' \<phi>Some_\<phi>Prod)

lemma \<phi>Some_not_1:
  \<open>(x \<Ztypecolon> \<black_circle> T) \<noteq> 1\<close>
  by (metis One_expn \<phi>Some_expn one_option_def option.distinct(1))

lemma Cond_Unital_Ins_BI_contract:
  \<open> \<half_blkcirc>\<^sub>B\<^sub>I[C] A * \<half_blkcirc>\<^sub>B\<^sub>I[C] B = \<half_blkcirc>\<^sub>B\<^sub>I[C] (A * B) \<close>
  unfolding BI_eq_iff
  by clarsimp force

lemma Cond_Unital_Ins_BI_eq_1:
  \<open> \<half_blkcirc>\<^sub>B\<^sub>I[C] A = 1 \<longleftrightarrow> C = False \<close>
  unfolding BI_eq_iff
  by clarsimp force

subsection \<open>Reasoning\<close>

subsubsection \<open>Initialization\<close>

lemma [\<phi>reason %\<phi>mapToA_init]:
  \<open> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<or>\<^sub>c\<^sub>u\<^sub>t
    ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W))
\<Longrightarrow> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  unfolding ToA_Getter_def ToA_Getter'_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def
  by (cases C\<^sub>R; clarsimp)

lemma [\<phi>reason %\<phi>mapToA_init+10]:
  \<open> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W
\<Longrightarrow> if C\<^sub>W then (Identity_Elements W D \<or>\<^sub>c\<^sub>u\<^sub>t
                ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W)))
            \<and>\<^sub>\<r> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> D w)
          else True
\<Longrightarrow> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  for Src :: \<open>'c::sep_magma_1 BI\<close>
  unfolding ToA_Getter_def ToA_Getter'_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def
  by (cases C\<^sub>W; cases C\<^sub>R; clarsimp)

lemma [\<phi>reason %\<phi>mapToA_init]:
  \<open> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W'
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<or>\<^sub>c\<^sub>u\<^sub>t ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W))
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  for Src :: \<open>'c::sep_magma_1 BI\<close>
  unfolding ToA_Mapper_def ToA_Mapper'_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def
  by (cases C\<^sub>R; clarsimp)

lemma [\<phi>reason %\<phi>mapToA_init+10]:
  \<open> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W'
\<Longrightarrow> if C\<^sub>W then (Identity_Element\<^sub>E (w \<Ztypecolon> W)
             \<and>\<^sub>\<r> Identity_Element\<^sub>I (w' \<Ztypecolon> W') Any)
             \<or>\<^sub>c\<^sub>u\<^sub>t ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W))
          else True
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  for Src :: \<open>'c::sep_magma_1 BI\<close>
  unfolding ToA_Mapper_def ToA_Mapper'_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def
  by (cases C\<^sub>W; cases C\<^sub>R; clarsimp;
      smt (verit, ccfv_threshold)
        transformation_trans[where P=True and Q=True, simplified]
        transformation_left_frame transformation_right_frame
        mult.assoc transformation_weaken mult_1_left mult_1_right)


subsubsection \<open>Product\<close>

lemma
  \<open> \<s>\<u>\<b>\<s>\<t> fst y \<Ztypecolon> U\<^sub>1 \<f>\<o>\<r> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1 \<t>\<o> Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w\<^sub>1' \<Ztypecolon> W\<^sub>1'
\<Longrightarrow> if C\<^sub>R\<^sub>1 then \<s>\<u>\<b>\<s>\<t> snd y \<Ztypecolon> U\<^sub>2 \<f>\<o>\<r> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<f>\<r>\<o>\<m> R\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2 \<t>\<o> R\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w\<^sub>2' \<Ztypecolon> W\<^sub>2'
          else (w\<^sub>2, W\<^sub>2, C\<^sub>W\<^sub>2, w\<^sub>2', W\<^sub>2', C\<^sub>R, R, R') = (x\<^sub>2, T\<^sub>2, True, snd y, U\<^sub>2, False, \<top>, \<top>)
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1, w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @action \<A>merge
\<Longrightarrow> (w' \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W') = ((w\<^sub>1', w\<^sub>2') \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1' \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2') @action \<A>merge
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U\<^sub>1 \<^emph> U\<^sub>2 \<f>\<o>\<r> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<close>
  for S :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Mapper'_def Action_Tag_def
  by (cases C\<^sub>R\<^sub>1; cases C\<^sub>R; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Prod_expn'' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      smt (verit, ccfv_threshold)
        transformation_trans[where P=True and Q=True, simplified]
        transformation_left_frame transformation_right_frame
        mult.assoc)

lemma
  \<open> \<g>\<e>\<t> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] M \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1
\<Longrightarrow> if C\<^sub>R\<^sub>1 then \<g>\<e>\<t> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<f>\<r>\<o>\<m> M \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2
          else (w\<^sub>2, W\<^sub>2, C\<^sub>W\<^sub>2, C\<^sub>R\<^sub>2, R) = (x\<^sub>2, T\<^sub>2, True, False, \<top>)
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1,w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @action \<A>merge
\<Longrightarrow> \<g>\<e>\<t> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Getter'_def Premise_def Action_Tag_def
  by (cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      metis mult.assoc)

lemma
  \<open> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R\<^sub>2 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2 \<t>\<o> Y\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w\<^sub>2' \<Ztypecolon> W\<^sub>2'
\<Longrightarrow> if C\<^sub>W\<^sub>2 then \<s>\<u>\<b>\<s>\<t> w\<^sub>2' \<Ztypecolon> W\<^sub>2' \<f>\<o>\<r> w\<^sub>2 \<Ztypecolon> W\<^sub>2 \<f>\<r>\<o>\<m> S\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Y\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W'
           else (C\<^sub>R\<^sub>1, R\<^sub>1, C\<^sub>W, w, W, w', W', R\<^sub>1) = (True, S\<^sub>1, False, undefined, \<top>\<^sub>\<phi>, undefined, \<top>\<^sub>\<phi>, Y\<^sub>1)
\<Longrightarrow> \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R] R = \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>1] R\<^sub>1 * \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>2] R\<^sub>2 @action \<A>merge
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>1 * S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Y\<^sub>1 * Y\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<close>
  for S\<^sub>1 :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Mapper'_def Action_Tag_def
  by (cases C\<^sub>R; cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W; cases C\<^sub>W\<^sub>2;
      clarsimp simp add: \<phi>Cond_Unital_BI_eq_strip Cond_Unital_Ins_BI_contract Cond_Unital_Ins_BI_eq_1;
      smt (verit, ccfv_threshold)
        transformation_trans[where P=True and Q=True, simplified]
        transformation_left_frame transformation_right_frame
        mult.assoc)

lemma
  \<open> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R\<^sub>2 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2
\<Longrightarrow> if C\<^sub>W\<^sub>2 then \<g>\<e>\<t> w\<^sub>2 \<Ztypecolon> W\<^sub>2 \<f>\<r>\<o>\<m> S\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W
          else (C\<^sub>R\<^sub>1, R\<^sub>1, C\<^sub>W, w, W) = (True, S\<^sub>1, False, undefined, \<top>\<^sub>\<phi>)
\<Longrightarrow> \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R] R = \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>1] R\<^sub>1 * \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>2] R\<^sub>2 @action \<A>merge
\<Longrightarrow> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>1 * S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S\<^sub>1 :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Getter'_def Action_Tag_def
  by (cases C\<^sub>R; cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W; cases C\<^sub>W\<^sub>2;
      clarsimp simp add: \<phi>Cond_Unital_BI_eq_strip Cond_Unital_Ins_BI_contract Cond_Unital_Ins_BI_eq_1;
      metis mult.assoc)



(*

lemma
  \<open> \<g>\<e>\<t> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] M \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R\<^sub>1
\<Longrightarrow> \<g>\<e>\<t> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<f>\<r>\<o>\<m> M \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1,w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @action \<A>merge
\<Longrightarrow> \<g>\<e>\<t> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Getter'_def Premise_def Action_Tag_def
  by (cases C\<^sub>R\<^sub>2; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      metis mult.assoc)

lemma
  \<open> \<g>\<e>\<t> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] M \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1
\<Longrightarrow> if C\<^sub>R\<^sub>1 then \<g>\<e>\<t> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<f>\<r>\<o>\<m> M \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2
           else Identity_Elements T\<^sub>2 D
             \<and>\<^sub>\<r> (Hint_Identity_Element T x\<^sub>2 \<or>\<^sub>c\<^sub>u\<^sub>t True)
             \<and>\<^sub>\<r> (w\<^sub>2, W\<^sub>2, C\<^sub>W\<^sub>2, C\<^sub>R\<^sub>2, R) = (undefined, \<top>\<^sub>\<phi>, False, False, \<top>)
             \<and>\<^sub>\<r> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> (D x\<^sub>2))
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1,w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @action \<A>merge
\<Longrightarrow> \<g>\<e>\<t> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S :: \<open>'c::sep_monoid BI\<close>
  unfolding ToA_Getter'_def Premise_def Action_Tag_def Ant_Seq_def
            Identity_Elements_alt_def
  by (cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      metis mult.assoc)

*)



lemma
  \<open> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> R\<^sub>2 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> w\<^sub>2 \<Ztypecolon> W\<^sub>2
\<Longrightarrow> \<g>\<e>\<t> w\<^sub>2 \<Ztypecolon> W\<^sub>2 \<f>\<r>\<o>\<m> S\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> w \<Ztypecolon> W
\<Longrightarrow> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>1 * S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> R\<^sub>1 * R\<^sub>2 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> w \<Ztypecolon> W \<close>
  for S\<^sub>1 :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Getter'_def
  by (clarsimp, metis mult.assoc)



lemma
  \<open> ToA_Getter' S\<^sub>2 W\<^sub>1 w\<^sub>1 R\<^sub>2 T x
\<Longrightarrow> ToA_Getter' S\<^sub>1 W w R\<^sub>1 T x
\<Longrightarrow> ToA_Getter' (S\<^sub>1 * S\<^sub>2) W w (R\<^sub>1 * R\<^sub>2) T x \<close>


end
