chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

(*Entirely deprecated!*)

theory IDE_CP_Reasoning2
  imports IDE_CP_Applications1 Phi_Domainoid
begin

subsection \<open>For Specific \<phi>-Types\<close>

subsubsection \<open>Value\<close>



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

\<comment> \<open>\<A>SE : \<^prop>\<open>x \<Ztypecolon> Source \<^emph> Further_Work \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> Target \<^emph> Remain \<w>\<i>\<t>\<h> some @tag \<A>SE\<close>\<close>
\<^item> \<A>SEi: \<open>x \<Ztypecolon> \<black_circle> Source \<^emph> \<half_blkcirc>[Cw] Further \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> \<black_circle> Target \<^emph> \<half_blkcirc>[Cr] Remain \<w>\<i>\<t>\<h> some @tag \<A>SEi\<close>
    \<open>\<black_circle>\<close> inserts it into a unital algebra.
(*\<A>SEa: \<^prop>\<open>x \<Ztypecolon> Source \<^emph> Further \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> Target \<w>\<i>\<t>\<h> some @tag \<A>SEa\<close>
    It doesn't has the remain part because it cannot has because it is non-associative.
    It must has some unsolved further work because it is separation extraction, of form
      \<^prop>\<open>A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>, not the simple transformation of form \<^prop>\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>.
      To consume \<open>A\<close>, the transformation of \<open>B\<close> to \<open>y \<Ztypecolon> U\<close> must remain some further work.*)

    Note non-associativity also implies non-commutativity, as in our formalization there is no
    algebra that is non-associative but commutative.
\<close>

text \<open>TODO: move\<close>

text \<open>Task of Structural Extract \<^prop>\<open>(x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y,r) \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P2 @tag \<A>SE \<close>,
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
    ) @tag \<A>SE \<close>
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

subsection \<open>Preliminary Helpers\<close>

lemma \<phi>Some_mult_contract:
  \<open>(x \<Ztypecolon> \<black_circle> T) * (y \<Ztypecolon> \<black_circle> U) = ((x,y) \<Ztypecolon> \<black_circle> (T \<^emph> U)) \<close>
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



subsubsection \<open>Bi-Conditioned Product\<close>

text \<open> Motivation: 
The process presented in this section does not enlarge decision-ability of the reasoning system.
However, it can keep the expressions of abstract objects clean and neat, improving the chance of
successes of automatic proving over the objects, and reducing the proving time.

Many operations such as memory load and store does not change the structure of the abstract objects
nor the \<open>\<phi>\<close>-types, but at most changing the values of certain elements of the objects in place.
Standard reasoning process, however, have to destruct the structure and later reconstruct the structure
maybe by user hints, causing the expression of the abstract objects got messed and lost of control.

The section presents structure-preserving transformation mappers allowing specifying abstract mapping
function by which we can apply the mapping over the abstract objects to carry out the operation without
modifying the structure nor the \<open>\<phi>\<close>-type at all. It also supports change-free reading operation which
extracts the values of certain elements, as the reading is a mapping of identity morphism.

A limitation over the mapping is, it must be independent between the elements of the object, i.e,
if separations of the elements are represented by \<open>(\<^emph>)\<close> and related to tuples, a mapping \<open>f\<close> over
the tuples must can be represented as \<open>f = map_prod f\<^sub>1 f\<^sub>2\<close>  where \<open>f\<^sub>1, f\<^sub>2\<close> are independent mappings
for each elements. The limitation is because, the object \<open>x \<Ztypecolon> T\<close> can be separated \<open>x \<Ztypecolon> T \<equiv> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2\<close>
with its elements \<open>x\<^sub>i \<Ztypecolon> T\<^sub>i\<close> scattered over everywhere. The reasoning of transformation mappers can gather
the elements together but the mappings over the elements still have to be independent because later
we need to translate the mapping onto the scattered elements in the original form, where each scattered
element does not know where are the other elements so hard to fetch the value of the other elements if
we still want the expressions of the elements neat (otherwise, one can directly use the existing
destructing-and-reconstructing method).

\<close>

subsection \<open>Definitions\<close>

definition ToA_Extract :: \<open>'c::sep_magma BI \<Rightarrow> 'c BI \<Rightarrow> bool\<close> ("\<g>\<e>\<t> _ \<f>\<r>\<o>\<m> _" [19,19] 18)
  where \<open>\<g>\<e>\<t> object \<f>\<r>\<o>\<m> source \<equiv> source = object\<close>

abbreviation ToA_Extract' :: \<open>'c::sep_magma BI \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
                            ("\<g>\<e>\<t> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _" [19,19,19,19] 18)
    \<comment> \<open>\<open>ToA_Extract\<close> is very limited. \<open>ToA_Extract'\<close> is the major entry point\<close>
  where \<open>\<g>\<e>\<t> object \<f>\<r>\<o>\<m> source \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<equiv> \<g>\<e>\<t> (object \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R) \<f>\<r>\<o>\<m> source\<close>

abbreviation ToA_Extract'' :: \<open>'c::sep_magma BI \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
                             ("\<g>\<e>\<t> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _" [19,19,19,19,19,19] 18)
  where \<open>\<g>\<e>\<t> object \<f>\<r>\<o>\<m> source \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] W \<equiv> \<g>\<e>\<t> (object \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R) \<f>\<r>\<o>\<m>(source \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>W] W)\<close>

term \<open>\<g>\<e>\<t> f(x) \<Ztypecolon> U \<^emph>[C\<^sub>R] R \<f>\<r>\<o>\<m> x \<Ztypecolon> T \<^emph>[C\<^sub>W] W\<close>
term \<open>\<g>\<e>\<t> f(x) \<Ztypecolon> U \<^emph>[C\<^sub>R] R \<f>\<r>\<o>\<m> x \<Ztypecolon> (T\<^sub>1 \<^emph> T\<^sub>2) \<^emph>[C\<^sub>W] W\<close>
term \<open>\<g>\<e>\<t> f(x) \<Ztypecolon> (U\<^sub>1 \<^emph> U\<^sub>2) \<^emph>[C\<^sub>R] R \<f>\<r>\<o>\<m> x \<Ztypecolon> T \<^emph>[C\<^sub>W] W\<close>

definition ToA_Subst :: \<open>'c BI \<Rightarrow> 'c BI \<Rightarrow> 'c::sep_magma BI \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
                       ("\<s>\<u>\<b>\<s>\<t> _ \<f>\<o>\<r> _ \<f>\<r>\<o>\<m> _ \<t>\<o> _" [19,19,19,19] 18)
  where \<open>\<s>\<u>\<b>\<s>\<t> residue \<f>\<o>\<r> redex \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<equiv> (Src \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> redex) \<and> (residue \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ret)\<close>

abbreviation ToA_Subst' :: \<open>'c BI \<Rightarrow> 'c BI \<Rightarrow> 'c::sep_magma BI \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
                       ("\<s>\<u>\<b>\<s>\<t> _ \<f>\<o>\<r> _ \<f>\<r>\<o>\<m> _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _" [19,19,19,19,19,19] 18)
  where \<open>\<s>\<u>\<b>\<s>\<t> residue \<f>\<o>\<r> redex \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<equiv>
            \<s>\<u>\<b>\<s>\<t> (residue \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R) \<f>\<o>\<r> (redex \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R) \<f>\<r>\<o>\<m> Src \<t>\<o> Ret\<close>

abbreviation ToA_Subst'' :: \<open>'c BI \<Rightarrow> 'c BI \<Rightarrow> 'c::sep_magma BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> bool \<Rightarrow> 'c BI \<Rightarrow> 'c BI \<Rightarrow> 'c BI \<Rightarrow> 'c BI \<Rightarrow> bool\<close>
                          ("\<s>\<u>\<b>\<s>\<t> _ \<f>\<o>\<r> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> _" [19,19,19,19,19,19,19,19,19,19] 18)
  where \<open>\<s>\<u>\<b>\<s>\<t> residue \<f>\<o>\<r> redex \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] W \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R' \<equiv>
            \<s>\<u>\<b>\<s>\<t> (residue \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R') \<f>\<o>\<r> (redex \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R) \<f>\<r>\<o>\<m> (Src \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>W] W) \<t>\<o> (Ret \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>W] W')\<close>

definition ToA_Mapper :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('c::sep_magma, 'a) \<phi> \<Rightarrow> ('c,'b) \<phi>
                       \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('c,'x) \<phi> \<Rightarrow> ('c,'y) \<phi> \<Rightarrow> ('x \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> bool\<close>
                          ("\<m>\<a>\<p> (_ :/ _ \<mapsto>/ _)/ \<o>\<v>\<e>\<r> (_ :/ _ \<mapsto>/ _)/ \<w>\<i>\<t>\<h> (\<g>\<e>\<t>\<t>\<e>\<r> _/ \<s>\<e>\<t>\<t>\<e>\<r> _)/ \<i>\<n> _" [21,21,21,21,21,21,21,21,21] 18)
  where \<open>\<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> domain \<equiv>
            (\<forall>x \<in> domain. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> h x \<Ztypecolon> U) \<and>
            (\<forall>y \<in> g ` h ` domain. y \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s y \<Ztypecolon> T') \<and>
            (\<forall>x \<in> domain. f x = s (g (h x)))\<close>

lemma ToA_Mapper_rev_def[no_atp]:
  \<open>(\<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> domain) \<longleftrightarrow>
      (\<forall>x \<in> domain. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> h x \<Ztypecolon> U) \<and>
      (\<forall>y \<in> g ` h ` domain. y \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s y \<Ztypecolon> T') \<and>
      (\<forall>x \<in> domain. s (g (h x)) = f x)\<close>
  unfolding ToA_Mapper_def by clarsimp fastforce

abbreviation ToA_Getter :: \<open>('x \<Rightarrow> 'a) \<Rightarrow> ('c::sep_magma, 'x) \<phi> \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 'x set \<Rightarrow> ('a \<Rightarrow> 'x) \<Rightarrow> bool\<close>
                           ("\<g>\<e>\<t>\<t>\<e>\<r> _ : _ \<mapsto> _ \<i>\<n> _ \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> _" [21,21,21,21,21] 18)
  where \<open>\<g>\<e>\<t>\<t>\<e>\<r> h : T \<mapsto> U \<i>\<n> domain \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> s \<equiv>
          \<m>\<a>\<p> id : U \<mapsto> U \<o>\<v>\<e>\<r> id : T \<mapsto> T \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> domain\<close>

ML_file \<open>library/syntax/ToA_mapper.ML\<close>

subsection \<open>Conventions\<close>

\<phi>reasoner_group \<phi>mapToA_all = (100, [0, 4000])
      \<open>Transformation Mappers\<close>
  and \<phi>mapToA_init = (1000, [1000,1020]) in \<phi>mapToA_all
      \<open>initializaton\<close>
  and \<phi>mapToA_refl = (3800, [3800, 3849]) in \<phi>mapToA_all
      \<open>reflexive\<close>
  and \<phi>mapToA_norm = (2600, [2600,2899]) in \<phi>mapToA_all
      \<open>normalizations like removing empty slots\<close>
  and \<phi>mapToA_varify_maps = (2650, [2650,2699]) in \<phi>mapToA_all
      \<open>varify the mapping functions\<close>
  and \<phi>mapToA_split_goal = (2520, [2520, 2530]) in \<phi>mapToA_all
      \<open>splitting the goal of the extraction\<close>
  and \<phi>mapToA_split_source = (2500, [2500, 2500]) in \<phi>mapToA_all and < \<phi>mapToA_split_goal
      \<open>splitting the source assertion\<close>
  and \<phi>mapToA_post_split = (2480, [2480, 2480]) in \<phi>mapToA_all and < \<phi>mapToA_split_source
      \<open>removing helper stuffs after the splitting\<close>
  and \<phi>mapToA_mapper = (1000, [1000,1000]) in \<phi>mapToA_all \<open>\<close>
(*  and \<phi>mapToA_getter = (1000, [1000,1000]) in \<phi>mapToA_all \<open>\<close> *)
  and \<phi>mapToA_aux = (1000, [1000,1030]) in \<phi>mapToA_all \<open>system auxiliaries\<close>
  and \<phi>mapToA_sysbot = (10, [0,10]) in \<phi>mapToA_all \<open>sysme rule of the bottom priority\<close>
  and \<phi>mapToA_derived = (50, [25,70]) in \<phi>mapToA_all > \<phi>mapToA_sysbot \<open>derived\<close>
  and \<phi>mapToA_derived_TF = (65, [65,65]) in \<phi>mapToA_derived
      \<open>ToA mapper derived from Transformation Functor\<close>
  and \<phi>mapToA_derived_module_SDistri = (37, [37,38]) in \<phi>mapToA_derived and < \<phi>mapToA_derived_TF
      \<open>derived ToA mapper for module scalar distributivity\<close>
  and \<phi>mapToA_derived_module_assoc = (30, [30,30]) in \<phi>mapToA_derived and < \<phi>mapToA_derived_module_SDistri
      \<open>derived ToA mapper for module scalar associativity\<close>
  and \<phi>mapToA_derived_module_wrapper = (27, [27,28]) in \<phi>mapToA_derived and < \<phi>mapToA_derived_module_assoc
      \<open>derived ToA mapper for warpping by module one\<close>
  and \<phi>mapToA_unify = (5, [5,6]) in \<phi>mapToA_sysbot
      \<open>apply lambda unification\<close>
  and \<phi>mapToA_fallbacks = (1,[1,4]) in \<phi>mapToA_sysbot and < \<phi>mapToA_unify
      \<open>fallbacks\<close>


declare [[
  \<phi>reason_default_pattern
      \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _\<close> \<Rightarrow>
      \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _\<close>   (110)
  and \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<close> \<Rightarrow>
      \<open>\<g>\<e>\<t> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<close>    (100)
  and \<open>\<s>\<u>\<b>\<s>\<t> ?var_y \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<Ztypecolon> _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> _\<close> \<Rightarrow>
      \<open>\<s>\<u>\<b>\<s>\<t> _ \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<Ztypecolon> _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<Ztypecolon> _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> _\<close>    (110)
  and \<open>\<s>\<u>\<b>\<s>\<t> ?var_y \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _\<close> \<Rightarrow>
      \<open>\<s>\<u>\<b>\<s>\<t> _ \<Ztypecolon> ?U \<f>\<o>\<r> _ \<Ztypecolon> ?T \<f>\<r>\<o>\<m> ?Src \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _\<close>    (100)
  and \<open>\<m>\<a>\<p> _ : ?U \<^emph>[_,_] (?out_R, ?var_E) \<mapsto> ?U' \<^emph>[_,_] (?out_R', ?var_E')
       \<o>\<v>\<e>\<r> _ : ?T \<^emph>[_,_] (_, ?var_E) \<mapsto> _ \<^emph>[_,_] (_, ?var_E')
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>
   \<Rightarrow> \<open>\<m>\<a>\<p> _ : ?U \<^emph>[_,_] (_,_) \<mapsto> ?U' \<^emph>[_,_] (_,_)
       \<o>\<v>\<e>\<r> _ : ?T \<^emph>[_,_] (_,_) \<mapsto> _ \<^emph>[_,_] (_,_)
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>    (120)
  and \<open>\<m>\<a>\<p> ?in_g  : ?U \<^emph>[_] ?out_R \<mapsto> ?U' \<^emph>[_] ?out_R'
       \<o>\<v>\<e>\<r> ?out_f : ?T \<^emph>[_] ?out_W \<mapsto> ?out_T' \<^emph>[_] ?out_W'
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>
   \<Rightarrow> \<open>\<m>\<a>\<p> _ : ?U \<^emph>[_] _ \<mapsto> ?U' \<^emph>[_] _
       \<o>\<v>\<e>\<r> _ : ?T \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>    (110)
  and \<open>\<m>\<a>\<p> _ : ?U \<^emph> _ \<mapsto> ?U' \<^emph> _ \<o>\<v>\<e>\<r> _ : ?T \<mapsto> _
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>
   \<Rightarrow> \<open>\<m>\<a>\<p> _ : ?U \<^emph> _ \<mapsto> ?U' \<^emph> _ \<o>\<v>\<e>\<r> _ : ?T \<mapsto> _
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>    (90)
  and \<open>\<m>\<a>\<p> _ : ?U \<mapsto> ?U' \<o>\<v>\<e>\<r> _ : ?T \<mapsto> _
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>
   \<Rightarrow> \<open>\<m>\<a>\<p> _ : ?U \<mapsto> ?U' \<o>\<v>\<e>\<r> _ : ?T \<mapsto> _
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>    (80)
(*  and \<open>\<g>\<e>\<t>\<t>\<e>\<r> _ : ?T \<^emph>[_] _ \<mapsto> ?U \<^emph>[_] _ \<i>\<n> ?D \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> _\<close> \<Rightarrow>
      \<open>\<g>\<e>\<t>\<t>\<e>\<r> _ : ?T \<^emph>[_] _ \<mapsto> ?U \<^emph>[_] _ \<i>\<n> ?D \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> _\<close>   (200) *)

  and \<open>\<g>\<e>\<t> ?obj \<f>\<r>\<o>\<m> ?src\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (\<g>\<e>\<t> ?obj \<f>\<r>\<o>\<m> ?src))\<close> (0)
  and \<open>\<s>\<u>\<b>\<s>\<t> ?redex \<f>\<o>\<r> ?residue \<f>\<r>\<o>\<m> ?Src \<t>\<o> ?Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (\<s>\<u>\<b>\<s>\<t> ?redex \<f>\<o>\<r> ?residue \<f>\<r>\<o>\<m> ?Src \<t>\<o> ?Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[?C\<^sub>R] ?R))\<close> (0)
  and \<open>\<m>\<a>\<p> ?g : ?U \<mapsto> ?U' \<o>\<v>\<e>\<r> ?f : ?T \<mapsto> ?T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> ?h \<s>\<e>\<t>\<t>\<e>\<r> ?s \<i>\<n> ?D\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (\<m>\<a>\<p> ?g : ?U \<mapsto> ?U' \<o>\<v>\<e>\<r> ?f : ?T \<mapsto> ?T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> ?h \<s>\<e>\<t>\<t>\<e>\<r> ?s \<i>\<n> ?D))\<close> (0),

  \<phi>default_reasoner_group
      \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close> : %\<phi>mapToA_mapper (100)
(*  and \<open>\<g>\<e>\<t>\<t>\<e>\<r> _ : _ \<mapsto> _  \<i>\<n> _ \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> _\<close> : %\<phi>mapToA_getter (100) *)
]]



subsection \<open>Basic Rules\<close>

lemma ToA_Extract_onward:
  \<open> \<g>\<e>\<t> target \<f>\<r>\<o>\<m> source \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R
\<Longrightarrow> source \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> target \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<close>
  unfolding ToA_Extract_def
  by simp

lemma ToA_Extract_backward:
  \<open> \<g>\<e>\<t> target \<f>\<r>\<o>\<m> source \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R
\<Longrightarrow> target \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> source \<close>
  unfolding ToA_Extract_def
  by simp

lemma ToA_Subst_onward:
  \<open> \<s>\<u>\<b>\<s>\<t> residue \<f>\<o>\<r> redex \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R
\<Longrightarrow> Src \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> redex \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<close>
  unfolding ToA_Subst_def
  by blast

lemma ToA_Subst_backward:
  \<open> \<s>\<u>\<b>\<s>\<t> residue \<f>\<o>\<r> redex \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R
\<Longrightarrow> residue \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ret \<close>
  unfolding ToA_Subst_def
  by blast


lemma ToA_Mapper_onward:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> h x \<Ztypecolon> U\<close>
  unfolding ToA_Mapper_def Premise_def
  by (clarsimp simp add: \<phi>Prod_expn'')

lemma ToA_Mapper_backward:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> g ` h ` D
\<Longrightarrow> x \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s x \<Ztypecolon> T'\<close>
  unfolding ToA_Mapper_def Premise_def
  by (clarsimp simp add: \<phi>Prod_expn'')

lemma ToA_Mapper_f_expn:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> \<forall>x \<in> D. f x = s (g (h x)) \<close>
  unfolding ToA_Mapper_def
  by clarsimp

lemma ToA_Mapper_f_expn_rev[no_atp]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> \<forall>x \<in> D. s (g (h x)) = f x \<close>
  unfolding ToA_Mapper_def
  by clarsimp

lemma ToA_Mapper_cong:
  \<open> U \<equiv> U'
\<Longrightarrow> U\<^sub>1 \<equiv> U\<^sub>1'
\<Longrightarrow> T \<equiv> T'
\<Longrightarrow> T\<^sub>1 \<equiv> T\<^sub>1'
\<Longrightarrow> D \<equiv> D'
\<Longrightarrow> (\<And>x. x \<in> D' \<Longrightarrow> f x \<equiv> f' x)
\<Longrightarrow> (\<And>x. x \<in> D' \<Longrightarrow> h x \<equiv> h' x)
\<Longrightarrow> (\<And>x. x \<in> h' ` D' \<Longrightarrow> g x \<equiv> g' x)
\<Longrightarrow> (\<And>x. x \<in> g' ` h' ` D' \<Longrightarrow> s x \<equiv> s' x)
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U\<^sub>1 \<o>\<v>\<e>\<r> f : T \<mapsto> T\<^sub>1 \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
 \<equiv> \<m>\<a>\<p> g' : U' \<mapsto> U\<^sub>1' \<o>\<v>\<e>\<r> f' : T' \<mapsto> T\<^sub>1' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h' \<s>\<e>\<t>\<t>\<e>\<r> s' \<i>\<n> D'\<close>
  unfolding ToA_Mapper_def atomize_eq
  by (clarsimp simp add: image_iff Bex_def; rule; clarsimp; metis)

lemma ToA_Mapper_\<phi>Some_rewr_origin[no_atp]:
  \<open> NO_MATCH (\<black_circle> UUU) U
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> domain
 \<equiv> \<m>\<a>\<p> g : \<black_circle> U \<mapsto> \<black_circle> U' \<o>\<v>\<e>\<r> f : \<black_circle> T \<mapsto> \<black_circle> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> domain \<close>
  unfolding ToA_Mapper_def \<phi>Some_transformation_strip .


lemma ToA_Mapper_LPR_gen_cong:
  \<open> D \<equiv> D'
\<Longrightarrow> (\<And>x. x \<in> D' \<Longrightarrow> h x \<equiv> h' x)
\<Longrightarrow> (\<And>x. x \<in> g ` h' ` D' \<Longrightarrow> s x \<equiv> s' x)
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U\<^sub>1 \<o>\<v>\<e>\<r> f : T \<mapsto> T\<^sub>1 \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
  \<equiv> \<m>\<a>\<p> g : U \<mapsto> U\<^sub>1 \<o>\<v>\<e>\<r> f : T \<mapsto> T\<^sub>1 \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h' \<s>\<e>\<t>\<t>\<e>\<r> s' \<i>\<n> D'\<close>
  unfolding ToA_Mapper_def atomize_eq
  by (clarsimp simp add: image_iff Bex_def; rule; clarsimp; metis)

setup \<open>Context.theory_map (PLPR_Rule_Gen.Rule_Gen_SS.map (
  Simplifier.add_cong @{thm' ToA_Mapper_LPR_gen_cong}))\<close>

hide_fact ToA_Mapper_LPR_gen_cong


subsubsection \<open>Extracting Implied Facts\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x. \<r>EIF (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x \<in> D \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> h x \<Ztypecolon> U)) (Q\<^sub>1 x))
\<Longrightarrow> (\<And>x. \<r>EIF (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x \<in> g ` h ` D \<longrightarrow> (x \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s x \<Ztypecolon> T')) (Q\<^sub>2 x))
\<Longrightarrow> \<r>EIF (\<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D)
         ((\<forall>x. Q\<^sub>1 x \<and> Q\<^sub>2 x) \<and> (\<forall>x \<in> D. f x = s (g (h x)))) \<close>
  unfolding \<r>EIF_def ToA_Mapper_def ToA_Subst_def Premise_def Ball_def
  by (clarsimp simp add: \<phi>Prod_expn'')

subsubsection \<open>Programming Method\<close>

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method
      (\<forall>x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x \<in> D \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> h x \<Ztypecolon> U) &&&
       \<forall>x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x \<in> g ` h ` D \<longrightarrow> (x \<Ztypecolon> U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s x \<Ztypecolon> T') &&&
       \<forall>x \<in> D. f x = s (g (h x)))
      MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method
      (Trueprop (\<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D)) MM DD RR FF \<close>
  unfolding \<phi>Programming_Method_def Premise_def
  subgoal premises prems
    by (insert prems(1)[OF \<open>PROP DD\<close> \<open>PROP RR\<close> \<open>PROP FF\<close>];
        clarsimp simp add: conjunction_imp ToA_Mapper_def ToA_Subst_def) .

subsection \<open>Reasoning Auxiliaries\<close>

subsubsection \<open>Assign Id\<close>

definition mapToA_assign_id
  where \<open>mapToA_assign_id f \<longleftrightarrow> f = id\<close>
  \<comment> \<open>I am thinking if we should replace this to be just a normal obligation\<close>

\<phi>reasoner_group mapToA_assign_id = (1000, [1000, 3000]) for \<open>mapToA_assign_id f\<close>
      \<open>assign \<open>id\<close> to separated mappings \<open>?f \<otimes>\<^sub>f ?g\<close>\<close>
  and mapToA_assign_id_success = (3000, [3000,3000]) in mapToA_assign_id \<open>success\<close>

declare [[
  \<phi>reason_default_pattern \<open>mapToA_assign_id ?f\<close> \<Rightarrow> \<open>mapToA_assign_id ?f\<close> (100),
  \<phi>default_reasoner_group \<open>mapToA_assign_id _\<close> : %mapToA_assign_id (100)
]]

paragraph \<open>Rules\<close>

lemma [\<phi>reason add]:
  \<open> mapToA_assign_id f
\<Longrightarrow> mapToA_assign_id g
\<Longrightarrow> mapToA_assign_id (f \<otimes>\<^sub>f g) \<close>
  unfolding fun_eq_iff mapToA_assign_id_def
  by simp

lemma [\<phi>reason %mapToA_assign_id_success for \<open>mapToA_assign_id ?var\<close> \<open>mapToA_assign_id id\<close>]:
  \<open> mapToA_assign_id id \<close>
  unfolding mapToA_assign_id_def ..

lemma [\<phi>reason %mapToA_assign_id_success]:
  \<open> mapToA_assign_id (\<lambda>x. x) \<close>
  unfolding mapToA_assign_id_def fun_eq_iff
  by simp

lemma [\<phi>reason add]:
  \<open> mapToA_assign_id f
\<Longrightarrow> mapToA_assign_id g
\<Longrightarrow> mapToA_assign_id (f o g) \<close>
  unfolding mapToA_assign_id_def fun_eq_iff
  by simp

lemma [\<phi>reason for \<open>mapToA_assign_id (\<lambda>_::?'a. unspec)\<close>]:
  \<open> mapToA_assign_id (\<lambda>_::unit. unspec) \<close>
  unfolding mapToA_assign_id_def fun_eq_iff
  by simp


lemma [\<phi>reason add]:
  \<open> mapToA_assign_id f
\<Longrightarrow> mapToA_assign_id (sublist_map_L len f) \<close>
  unfolding mapToA_assign_id_def sublist_map_L_def fun_eq_iff
  by clarsimp

lemma [\<phi>reason add]:
  \<open> mapToA_assign_id f
\<Longrightarrow> mapToA_assign_id (sublist_map_R len f) \<close>
  unfolding mapToA_assign_id_def sublist_map_R_def fun_eq_iff
  by clarsimp

lemma [\<phi>reason add]:
  \<open> mapToA_assign_id f
\<Longrightarrow> mapToA_assign_id (list_upd_map i f) \<close>
  unfolding mapToA_assign_id_def list_upd_map_def fun_eq_iff
  by clarsimp



subsubsection \<open>Unify Assertion\<close>

definition mapToA_unify_A :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool\<close>
  where \<open>mapToA_unify_A Tgt Src A B \<longleftrightarrow> A = B\<close>

lemma [\<phi>reason %cutting+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = B
\<Longrightarrow> mapToA_unify_A Tgt Src A B \<close>
  unfolding Premise_def mapToA_unify_A_def \<r>Guard_def
  by simp

lemma [\<phi>reason %cutting]:
  \<open> ERROR TEXT(\<open>Transformation Mapper fails to extract\<close> Tgt \<open>from\<close> Src
               \<open>because fails to unify\<close> R \<open>with\<close> R'
               \<open>It typically suggests the substitution is not structure-preserving\<close>)
\<Longrightarrow> mapToA_unify_A Tgt Src A B \<close>
  unfolding ERROR_def
  by blast

subsubsection \<open>Conditioned Map ToA\<close>

definition \<open>mapToA_cond A B C D \<equiv> (A \<or> B \<or> C) \<and> D\<close>

subsubsection \<open>Mapper Equation\<close>

definition \<open>lookup_a_mapper g x y \<equiv> g x = y\<close>

\<phi>reasoner_group lookup_a_mapper_all = (1000, [10, 3000]) for \<open>lookup_a_mapper g x y\<close>
      \<open>look up a \<open>g\<close> such that \<open>g x = y\<close> for given \<open>x, y\<close>\<close>
  and lookup_a_mapper = (1000, [1000,1100]) in lookup_a_mapper_all
      \<open>default group\<close>
  and lookup_a_mapper_default = (10, [10, 30]) in lookup_a_mapper_all < lookup_a_mapper
      \<open>default rules\<close>

declare [[
  \<phi>reason_default_pattern \<open>lookup_a_mapper ?f ?x ?y\<close> \<Rightarrow> \<open>lookup_a_mapper ?f ?x ?y\<close> (100),
  \<phi>default_reasoner_group \<open>lookup_a_mapper _ _ _\<close> : %lookup_a_mapper (100)
]]

paragraph \<open>Rules\<close>

lemma [\<phi>reason %lookup_a_mapper+10]:
  \<open> lookup_a_mapper f x\<^sub>1 y\<^sub>1
\<Longrightarrow> lookup_a_mapper g x\<^sub>2 y\<^sub>2
\<Longrightarrow> lookup_a_mapper (f \<otimes>\<^sub>f g) (x\<^sub>1, x\<^sub>2) (y\<^sub>1, y\<^sub>2) \<close>
  unfolding lookup_a_mapper_def
  by simp

lemma [\<phi>reason %lookup_a_mapper]:
  \<open> lookup_a_mapper f (fst x) (fst y)
\<Longrightarrow> lookup_a_mapper g (snd x) (snd y)
\<Longrightarrow> lookup_a_mapper (f \<otimes>\<^sub>f g) x y \<close>
  unfolding lookup_a_mapper_def
  by (cases x; cases y; simp)

lemma [\<phi>reason %lookup_a_mapper for \<open>lookup_a_mapper (comb.K _) _ _\<close>,
       \<phi>reason %lookup_a_mapper_default+10 for \<open>lookup_a_mapper ?var _ _\<close> ]:
  \<open> lookup_a_mapper (comb.K y) x y \<close>
  unfolding lookup_a_mapper_def comb.K_def ..

lemma [\<phi>reason default %lookup_a_mapper_default+20 for \<open>lookup_a_mapper ?var _ _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] x = y
\<Longrightarrow> lookup_a_mapper id x y \<close>
  unfolding \<r>Guard_def Premise_def lookup_a_mapper_def
  by simp

lemma [\<phi>reason default %lookup_a_mapper_default]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = y
\<Longrightarrow> lookup_a_mapper f x y \<close>
  unfolding Premise_def lookup_a_mapper_def .


subsubsection \<open>Split Map\<close>

definition \<open>split_map f f\<^sub>1 f\<^sub>2 \<longleftrightarrow> f = f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2\<close>

\<phi>reasoner_group mapToA_split_map_all = (1000, [0, 3000]) for \<open>split_map f f\<^sub>1 f\<^sub>2\<close> \<open>\<close>
  and mapToA_split_map_fail = (0, [0,0]) in mapToA_split_map_all \<open>\<close>
  and mapToA_split_map_default = (10, [10,10]) in mapToA_split_map_all and > mapToA_split_map_fail \<open>\<close>
  and mapToA_split_map = (1000, [1000, 1050]) in mapToA_split_map_all and > mapToA_split_map_default \<open>\<close>
  and mapToA_split_map_norm = (2500, [2500, 2599]) in mapToA_split_map_all and > mapToA_split_map \<open>\<close>
  and mapToA_split_map_success = (2800, [2800, 2899]) in mapToA_split_map_all and > mapToA_split_map_norm \<open>\<close>

declare [[
  \<phi>reason_default_pattern \<open>split_map ?f _ _\<close> \<Rightarrow> \<open>split_map ?f _ _\<close> (100),
  \<phi>default_reasoner_group \<open>split_map ?f _ _\<close> : %mapToA_split_map  (100)
]]

paragraph \<open>Rules\<close>

lemma [\<phi>reason %mapToA_split_map_success for \<open>split_map (_ \<otimes>\<^sub>f _) _ _\<close>
                                             \<open>split_map ?var _ _\<close> ]:
  \<open> split_map (f \<otimes>\<^sub>f g) f g \<close>
  unfolding split_map_def
  by simp

lemma [\<phi>reason %mapToA_split_map_fail]:
  \<open> FAIL TEXT(\<open>Fail to split\<close> f \<open>into pairwise maps for each projection\<close>)
\<Longrightarrow> split_map f f\<^sub>1 f\<^sub>2 \<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason %mapToA_split_map_norm]:
  \<open> split_map f f\<^sub>1 f\<^sub>2
\<Longrightarrow> split_map (f o (\<lambda>x. x)) f\<^sub>1 f\<^sub>2 \<close>
  by simp

lemma [\<phi>reason %mapToA_split_map_norm]:
  \<open> split_map f f\<^sub>1 f\<^sub>2
\<Longrightarrow> split_map (f o id) f\<^sub>1 f\<^sub>2 \<close>
  by simp

lemma [\<phi>reason %mapToA_split_map_norm]:
  \<open> split_map f f\<^sub>1 f\<^sub>2
\<Longrightarrow> split_map ((\<lambda>x. x) o f) f\<^sub>1 f\<^sub>2 \<close>
  by simp

lemma [\<phi>reason %mapToA_split_map_norm]:
  \<open> split_map f f\<^sub>1 f\<^sub>2
\<Longrightarrow> split_map (id o f) f\<^sub>1 f\<^sub>2 \<close>
  by simp





subsection \<open>Reasoning\<close>


(*
lemma [\<phi>reason %\<phi>mapToA_init+10]:
  \<open> \<g>\<e>\<t>\<t>\<e>\<r> h : T \<^emph>[C\<^sub>W] W \<mapsto> U \<^emph>[C\<^sub>R] R \<i>\<n> {(x,w)} \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> not_matter
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst (h (x, w)) = y
\<Longrightarrow> \<g>\<e>\<t> y \<Ztypecolon> U \<f>\<r>\<o>\<m> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] snd (h (x, w)) \<Ztypecolon> R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  unfolding ToA_Extract_def ToA_Mapper_def BI_eq_ToA Premise_def
  by (cases C\<^sub>R; cases C\<^sub>W; clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')
*)


subsubsection \<open>Normalization\<close>

lemma [\<phi>reason %\<phi>mapToA_varify_maps+30
          for \<open>\<m>\<a>\<p> id : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>
              \<open>\<m>\<a>\<p> id : _ \<^emph> _ \<mapsto> _ \<^emph> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> mapToA_assign_id g
\<Longrightarrow> mapToA_assign_id r
\<Longrightarrow> \<m>\<a>\<p> id : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding mapToA_assign_id_def
  by (simp add: map_prod.id)

lemma [\<phi>reason %\<phi>mapToA_varify_maps+30
          for \<open>\<m>\<a>\<p> id \<otimes>\<^sub>f _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> mapToA_assign_id g
\<Longrightarrow> \<m>\<a>\<p> id \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding mapToA_assign_id_def
  by (simp add: map_prod.id)

lemma [\<phi>reason %\<phi>mapToA_varify_maps+30
          for \<open>\<m>\<a>\<p> _ \<otimes>\<^sub>f id : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> mapToA_assign_id r
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f id : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding mapToA_assign_id_def
  by (simp add: map_prod.id)


lemma [\<phi>reason %\<phi>mapToA_varify_maps+30
          for \<open>\<m>\<a>\<p> id \<otimes>\<^sub>f _ : _ \<^emph> _ \<mapsto> _ \<^emph> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph> R \<mapsto> U' \<^emph> R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> mapToA_assign_id g
\<Longrightarrow> \<m>\<a>\<p> id \<otimes>\<^sub>f r : U \<^emph> R \<mapsto> U' \<^emph> R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding mapToA_assign_id_def
  by (simp add: map_prod.id)

lemma [\<phi>reason %\<phi>mapToA_varify_maps+30
          for \<open>\<m>\<a>\<p> _ \<otimes>\<^sub>f id : _ \<^emph> _ \<mapsto> _ \<^emph> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph> R \<mapsto> U' \<^emph> R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> mapToA_assign_id r
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f id : U \<^emph> R \<mapsto> U' \<^emph> R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding mapToA_assign_id_def
  by (simp add: map_prod.id)

(*
lemma [\<phi>reason %\<phi>mapToA_varify_maps
          for \<open>\<m>\<a>\<p> _ \<otimes>\<^sub>f _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _ \<close>
          except \<open>\<m>\<a>\<p> ?var \<otimes>\<^sub>f _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
                  \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _ \<close>]:
  \<open> \<m>\<a>\<p> g' \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> g' = g
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding Premise_def
  by simp

lemma [\<phi>reason %\<phi>mapToA_varify_maps
          for \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ \<otimes>\<^sub>f _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _ \<close>
          except \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> ?var \<otimes>\<^sub>f _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
                  \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _ \<close>]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> f' = f
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding Premise_def
  by simp
*)

lemma [\<phi>reason %\<phi>mapToA_varify_maps
          for \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> id \<otimes>\<^sub>f _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _ \<close> ]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> mapToA_assign_id f'
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> id \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding mapToA_assign_id_def
  by simp


subsubsection \<open>Internal System\<close>

paragraph \<open>Filter out empty slots\<close>

context
  includes prevent_eliminate_IE_\<phi>Cond_Unital
  notes \<phi>Prod_expn''[simp] prod.split[split]
      (*ToA_splitting_source_no_remainder_first[\<phi>reason del]
        ToA_splitting_source_has_remainder_first[\<phi>reason %ToA_splitting_source except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ :: ?'a :: sep_semigroup set) \<w>\<i>\<t>\<h> _\<close>]*)
begin

lemma [\<phi>reason %\<phi>mapToA_norm for \<open>\<m>\<a>\<p> _ : (_ [False]\<^emph> _) \<^emph>[_] _ \<mapsto> (_ [False]\<^emph> _) \<^emph>[_] _
                                  \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g\<^sub>2 \<otimes>\<^sub>f r : U\<^sub>2 \<^emph>[C\<^sub>R] R \<mapsto> U\<^sub>2' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> ((\<lambda>_. unspec) \<otimes>\<^sub>f g\<^sub>2) \<otimes>\<^sub>f r : (U\<^sub>1 [False]\<^emph> U\<^sub>2) \<^emph>[C\<^sub>R] R \<mapsto> (U\<^sub>1' [False]\<^emph> U\<^sub>2') \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>x. case h x of (x,r) \<Rightarrow> ((unspec, x), r))
        \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>((_,x),r). s (x, r))
      \<i>\<n> D \<close>
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some
                   BiCond_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises Tr[]
    apply_rule ToA_Mapper_onward[OF Tr , where x=x]
  \<medium_right_bracket> apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises Tr[]
    apply_rule ToA_Mapper_backward[OF Tr , where x=\<open>apfst snd x\<close>, simplified]
    certified by (insert useful, simp add: image_iff,
                  smt (verit, ccfv_threshold) apfst_conv case_prod_conv map_prod_def prod.collapse prod.inject) ;;
  \<medium_right_bracket> apply (rule conjunctionI, rule, rule)
    subgoal premises prems for y
      by (insert ToA_Mapper_f_expn[OF prems(1), THEN bspec[OF _ prems(2)]],
          clarsimp split: prod.split) .


lemma [\<phi>reason %\<phi>mapToA_norm for \<open>\<m>\<a>\<p> _ : (_ [False]\<^emph> _) \<^emph>[_] _ \<mapsto> (_ [False]\<^emph> _) \<^emph>[_] _
                                  \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g\<^sub>2 \<otimes>\<^sub>f r : U\<^sub>2 \<^emph>[C\<^sub>R] R \<mapsto> U\<^sub>2' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> ((\<lambda>_. unspec) \<otimes>\<^sub>f g\<^sub>2) \<otimes>\<^sub>f r : (U\<^sub>1 [False]\<^emph> U\<^sub>2) \<^emph>[C\<^sub>R] R \<mapsto> (U\<^sub>1' [False]\<^emph> U\<^sub>2') \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>x. case h x of (y,r) \<Rightarrow> ((unspec,y),r))
        \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>((_,x),r). s (x,r))
      \<i>\<n> D \<close>

  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some
                   BiCond_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises Tr[]
    apply_rule ToA_Mapper_onward[OF Tr , where x=x]
  \<medium_right_bracket> apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises Tr[]
    apply_rule ToA_Mapper_backward[OF Tr , where x=\<open>apfst snd x\<close>, simplified]
    certified by (insert useful, clarsimp simp add: image_iff, force) ;;
  \<medium_right_bracket> by (rule conjunctionI, rule, simp,
        smt (verit, best) ToA_Mapper_f_expn apfst_conv apfst_convE map_prod_simp snd_conv)


lemma [\<phi>reason %\<phi>mapToA_norm for \<open>\<m>\<a>\<p> _ : (_ \<^emph>[False] _) \<^emph>[_] _ \<mapsto> (_ \<^emph>[False] _) \<^emph>[_] _
                                  \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g\<^sub>1 \<otimes>\<^sub>f r : U\<^sub>1 \<^emph>[C\<^sub>R] R \<mapsto> U\<^sub>1' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> (g\<^sub>1 \<otimes>\<^sub>f (\<lambda>_. unspec)) \<otimes>\<^sub>f r : (U\<^sub>1 \<^emph>[False] U\<^sub>2) \<^emph>[C\<^sub>R] R \<mapsto> (U\<^sub>1' \<^emph>[False] U\<^sub>2') \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>x. case h x of (x,r) \<Rightarrow> ((x,unspec),r))
        \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>((x,_),r). s (x,r))
      \<i>\<n> D \<close>

  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some
                   BiCond_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises Tr[]
    apply_rule ToA_Mapper_onward[OF Tr , where x=x]
  \<medium_right_bracket> apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises Tr[]
    apply_rule ToA_Mapper_backward[OF Tr , where x=\<open>apfst fst x\<close>, simplified]
    certified by (insert useful, clarsimp simp add: image_iff, force)
  \<medium_right_bracket> apply (rule conjunctionI, rule, rule)
    subgoal premises prems for y
      by (insert ToA_Mapper_f_expn[OF prems(1), THEN bspec[OF _ prems(2)]],
          clarsimp split: prod.split) .

end


paragraph \<open>Conditioned Targets\<close>

lemma [\<phi>reason %\<phi>mapToA_aux for \<open>mapToA_cond True _ _ (\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ [True]\<^emph>[_] _ \<mapsto> _ [True]\<^emph>[_] _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _)\<close>]:
  \<open> \<m>\<a>\<p> g : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : R\<^sub>1 \<^emph>[C\<^sub>W] W \<mapsto> R\<^sub>1' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> mapToA_cond True Any Any2
   (\<m>\<a>\<p> g : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : R\<^sub>1 [True]\<^emph>[C\<^sub>W] W \<mapsto> R\<^sub>1' [True]\<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D) \<close>
  unfolding mapToA_cond_def
  by simp

lemma [\<phi>reason %\<phi>mapToA_aux for \<open>mapToA_cond True _ _
                                    (\<m>\<a>\<p> _ : _ [True]\<^emph>[_] _ \<mapsto> _ [True]\<^emph>[_] _
                                     \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _)\<close>]:
  \<open> \<m>\<a>\<p> w : W\<^sub>1 \<^emph>[C\<^sub>R] R \<mapsto> W\<^sub>1' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> mapToA_cond True Any Any'
   (\<m>\<a>\<p> w : W\<^sub>1 [True]\<^emph>[C\<^sub>R] R \<mapsto> W\<^sub>1' [True]\<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D) \<close>
  unfolding mapToA_cond_def
  by simp

lemma ttt[\<phi>reason %\<phi>mapToA_aux for \<open>mapToA_cond False _ _
                                  (\<m>\<a>\<p> _ : _ [False]\<^emph>[_] _ \<mapsto> _ [False]\<^emph>[_] _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
                                   \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _)\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] (gg = (\<lambda>_. unspec) \<otimes>\<^sub>f f \<otimes>\<^sub>f e) \<and> (ff = f \<otimes>\<^sub>f (\<lambda>_. unspec) \<otimes>\<^sub>f e)
\<Longrightarrow> mapToA_cond False True C\<^sub>E
   (\<m>\<a>\<p> gg : W [False]\<^emph>[True,C\<^sub>E] (T,E) \<mapsto> W' [False]\<^emph>[True,C\<^sub>E] (T',E')
    \<o>\<v>\<e>\<r> ff : T \<^emph>[False,C\<^sub>E] (\<top>\<^sub>\<phi>,E) \<mapsto> T' \<^emph>[False,C\<^sub>E] (\<top>\<^sub>\<phi>,E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>(x,_,e). (unspec,x,e))
        \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>(_,x,e). (x,unspec,e))
      \<i>\<n> D) \<close>
  unfolding ToA_Mapper_def mapToA_cond_def Premise_def
  by (cases C\<^sub>E; clarsimp simp add: \<phi>Prod_expn'' Ball_def)


lemma [\<phi>reason %\<phi>mapToA_norm
           for \<open>\<m>\<a>\<p> _ : _ \<mapsto> _
                \<o>\<v>\<e>\<r> _ : (_ [True]\<^emph> _ ) \<^emph>[_] _ \<mapsto> (_ [True]\<^emph> _) \<^emph>[_] _
                \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U'
    \<o>\<v>\<e>\<r> f : (T\<^sub>1 \<^emph> T\<^sub>2 ) \<^emph>[C\<^sub>W] W \<mapsto> (T\<^sub>1' \<^emph> T\<^sub>2') \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U'
    \<o>\<v>\<e>\<r> f : (T\<^sub>1  [True]\<^emph> T\<^sub>2 ) \<^emph>[C\<^sub>W] W
          \<mapsto> (T\<^sub>1' [True]\<^emph> T\<^sub>2') \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  by simp

lemma [\<phi>reason %\<phi>mapToA_norm
        for \<open>\<m>\<a>\<p> _ : _ \<mapsto> _
             \<o>\<v>\<e>\<r> _ : (_ [False]\<^emph> _ ) \<^emph>[_] _ \<mapsto> (_ [False]\<^emph> _) \<^emph>[_] _
             \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] f\<^sub>1' : f\<^sub>1
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>((x,_),_) \<in> D. f\<^sub>1' x = unspec)
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U'
    \<o>\<v>\<e>\<r> f\<^sub>2 \<otimes>\<^sub>f f\<^sub>3 : T\<^sub>2 \<^emph>[C\<^sub>W] W \<mapsto> T\<^sub>2' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>((a,b),c). (b,c)) ` D

\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U'
    \<o>\<v>\<e>\<r> (f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2) \<otimes>\<^sub>f f\<^sub>3 : (T\<^sub>1  [False]\<^emph> T\<^sub>2 ) \<^emph>[C\<^sub>W] W
                        \<mapsto> (T\<^sub>1' [False]\<^emph> T\<^sub>2') \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h o (\<lambda>((a,b),c). (b,c))
         \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>(b,c). ((unspec,b),c)) o s
      \<i>\<n> D \<close>
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some
                   BiCond_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [] and [] and Tr[]
    note \<phi>Prod_expn''[simp] ;;  ;;
    apply_rule ToA_Mapper_onward[OF Tr , where x=\<open>case x of ((a,b),c) \<Rightarrow> (b,c)\<close>]
    certified by (insert \<open>x \<in> D\<close>; cases x; auto simp: image_iff Bex_def)
  \<medium_right_bracket> certified by (insert \<open>x \<in> D\<close>; cases x; auto simp: image_iff Bex_def)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises [] and [] and Tr[]
    apply_rule ToA_Mapper_backward[OF Tr]
    certified by (insert useful; auto simp: image_iff)
  \<medium_right_bracket> certified by (insert useful; auto simp: image_iff split: prod.split)
    by (rule conjunctionI, rule, drule ToA_Mapper_f_expn,
        auto simp: Simplify_def Premise_def split: prod.split)




paragraph \<open>Fallback when the external objects are not used\<close>


context 
  notes BiCond_assoc[simp] BiCond_assoc'[simp] \<phi>Prod_expn''[simp, \<phi>programming_simps]
        prod_opr_norm[simp] comp_assoc[symmetric, simp]
        boolean_conversions(1,2)[simp]
begin
  

lemma [\<phi>reason %\<phi>mapToA_post_split
          for \<open>\<m>\<a>\<p> _ : _ \<^emph>[_,_] (_,_) \<mapsto> _ \<^emph>[_,_] (_,_)
               \<o>\<v>\<e>\<r> _ : _ \<^emph>[_,_] (_,_) \<mapsto> _ \<^emph>[_,_] (_,_)
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> (\<lambda>(x,w,e). (x,w)) ` D
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f e : U \<^emph>[C\<^sub>R,C\<^sub>E] (R,E) \<mapsto> U' \<^emph>[C\<^sub>R,C\<^sub>E] (R',E')
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w \<otimes>\<^sub>f e : T \<^emph>[C\<^sub>W,C\<^sub>E] (W,E) \<mapsto> T' \<^emph>[C\<^sub>W,C\<^sub>E] (W',E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>(x,w,e). case h (x,w) of (y,r) \<Rightarrow> (y,r,e))
         \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>(y,r,e). case s (y,r) of (x,w) \<Rightarrow> (x,w,e))
      \<i>\<n> D \<close>
  for T :: \<open>('e::sep_semigroup,'f) \<phi>\<close>

  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: BiCond_expn_BiCond BiCond_expn_\<phi>Some Cond_\<phi>Prod_expn_\<phi>Some \<phi>Some_\<phi>Prod[symmetric])
  \<medium_left_bracket> premises MP
    apply_rule ToA_Mapper_onward[OF MP, where x=\<open>case x of (x,w,e) \<Rightarrow> (x,w)\<close>]
    certified by (clarsimp split: prod.split simp add: image_iff, insert the_\<phi>(4), blast)
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule conjunctionI, simp add: image_image del: split_paired_All)
  \<medium_left_bracket> premises MP
    apply_rule ToA_Mapper_backward[OF MP, where x=\<open>fst (prod.rotL x)\<close>]
    certified by (insert useful, clarsimp simp add: image_iff split: prod.split, force)
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    by (drule ToA_Mapper_f_expn, clarsimp split: prod.split, fastforce)


lemma ToA_mapper_intro_Ex[no_atp]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> h' : (\<lambda>(x,w). case h (x,w,unspec) of (y,r,_) \<Rightarrow> (y,r))
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> s' : (\<lambda>(y,r). case s (y,r,unspec) of (x,w,_) \<Rightarrow> (x,w))
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f (\<lambda>_. unspec) : U \<^emph>[C\<^sub>R,False] (R,\<top>\<^sub>\<phi>) \<mapsto> U' \<^emph>[C\<^sub>R,False] (R',\<top>\<^sub>\<phi>)
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w \<otimes>\<^sub>f (\<lambda>_. unspec) : T \<^emph>[C\<^sub>W,False] (W,\<top>\<^sub>\<phi>) \<mapsto> T' \<^emph>[C\<^sub>W,False] (W',\<top>\<^sub>\<phi>)
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x,w). (x,w,unspec)) ` D
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h' \<s>\<e>\<t>\<t>\<e>\<r> s' \<i>\<n> D \<close>
  for T :: \<open>('e::sep_semigroup,'f) \<phi>\<close>
  unfolding Simplify_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: BiCond_expn_BiCond BiCond_expn_\<phi>Some Cond_\<phi>Prod_expn_\<phi>Some \<phi>Some_\<phi>Prod[symmetric])
  \<medium_left_bracket> premises [] and [] and MP
    apply_rule ToA_Mapper_onward[OF MP, where x=\<open>case x of (x,w) \<Rightarrow> (x,w,unspec)\<close>]
    certified by (clarsimp simp add: image_iff split: prod.split, insert the_\<phi>(3), blast)
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises [] and [] and MP
    apply_rule ToA_Mapper_backward[OF MP, where x=\<open>(prod.rotR \<circ> prod.swap \<circ> Pair unspec) x\<close>]
    certified by (insert useful, clarsimp simp add: image_iff split: prod.split, force)
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule)
    subgoal premises prems for y
      by (insert ToA_Mapper_f_expn[OF prems(3), simplified, THEN bspec[OF _ prems(4)]],
          clarsimp split: prod.split) .

end

subsubsection \<open>Product\<close>

paragraph \<open>Type Level\<close>

declare [[ML_print_depth = 100]]

context
  notes BiCond_assoc[simp] BiCond_assoc'[simp] \<phi>Prod_expn''[simp, \<phi>programming_simps]
        prod_opr_norm[simp] comp_assoc[symmetric, simp]
        boolean_conversions[simp]
begin

lemma \<phi>mapToA_split_goal_Ty[
      no_atp,
      \<phi>reason %\<phi>mapToA_split_goal
          for \<open>\<m>\<a>\<p> _ : (_ \<^emph> _) \<^emph>[_, _] (_, _) \<mapsto> (_ \<^emph> _) \<^emph>[_, _] (_, _)
               \<o>\<v>\<e>\<r> _ : _ \<^emph>[_, _] (_, _) \<mapsto> _ \<^emph>[_, _] (_, _)
               \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> split_map g g\<^sub>1 g\<^sub>2
\<Longrightarrow> \<m>\<a>\<p> g\<^sub>1 \<otimes>\<^sub>f f\<^sub>2 : U\<^sub>1 \<^emph>[C\<^sub>R\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (R\<^sub>1, W\<^sub>2, E) \<mapsto> U\<^sub>1' \<^emph>[C\<^sub>R\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (R\<^sub>1', W\<^sub>2', E')
    \<o>\<v>\<e>\<r> f\<^sub>1 \<otimes>\<^sub>f w\<^sub>1 \<otimes>\<^sub>f w\<^sub>2 \<otimes>\<^sub>f e : T \<^emph>[C\<^sub>W\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>1, W\<^sub>2, E) \<mapsto> T' \<^emph>[C\<^sub>W\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>1', W\<^sub>2', E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>1 \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>1 \<i>\<n> (\<lambda>(x,(w\<^sub>1,w\<^sub>2),e). (x,w\<^sub>1,w\<^sub>2,e)) ` D
\<Longrightarrow> mapToA_cond C\<^sub>R\<^sub>1 C\<^sub>W\<^sub>2 C\<^sub>E
   (\<m>\<a>\<p> g\<^sub>2 \<otimes>\<^sub>f r\<^sub>2 : U\<^sub>2 \<^emph>[C\<^sub>R, C\<^sub>E] (R, E) \<mapsto> U\<^sub>2' \<^emph>[C\<^sub>R, C\<^sub>E] (R', E') \<comment> \<open>goto, \<section>\<open>Conditioned Targets\<close>\<close>
    \<o>\<v>\<e>\<r> f\<^sub>2 : R\<^sub>1 [C\<^sub>R\<^sub>1]\<^emph>[C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>2, E) \<mapsto> R\<^sub>1' [C\<^sub>R\<^sub>1]\<^emph>[C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>2', E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>2 \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>2 \<i>\<n> (\<lambda>(x,(w\<^sub>1,w\<^sub>2),e). snd (h\<^sub>1 (x,w\<^sub>1,w\<^sub>2,e))) ` D)
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W  = \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1  \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2  @tag \<A>merge \<comment> \<open>goto, \<section>\<open>Filter out empty slots\<close>\<close>
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W' = \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1' \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2' @tag \<A>merge
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r\<^sub>2: (U\<^sub>1 \<^emph> U\<^sub>2) \<^emph>[C\<^sub>R, C\<^sub>E] (R, E) \<mapsto> (U\<^sub>1' \<^emph> U\<^sub>2') \<^emph>[C\<^sub>R, C\<^sub>E] (R', E')
    \<o>\<v>\<e>\<r> f\<^sub>1 \<otimes>\<^sub>f (w\<^sub>1 \<otimes>\<^sub>f w\<^sub>2) \<otimes>\<^sub>f e : T \<^emph>[C\<^sub>W, C\<^sub>E] (W, E) \<mapsto> T' \<^emph>[C\<^sub>W, C\<^sub>E] (W', E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>(x,(w\<^sub>1,w\<^sub>2),e). case h\<^sub>1 (x,w\<^sub>1,w\<^sub>2,e) of (y\<^sub>1,r\<^sub>1) \<Rightarrow>
                               case h\<^sub>2 r\<^sub>1 of (y\<^sub>2,r,e) \<Rightarrow> ((y\<^sub>1,y\<^sub>2),r,e))
        \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>((y\<^sub>1,y\<^sub>2),r). case s\<^sub>1 (y\<^sub>1, s\<^sub>2 (y\<^sub>2,r)) of (x,w\<^sub>1,w\<^sub>2,e) \<Rightarrow> (x,(w\<^sub>1,w\<^sub>2),e))
    \<i>\<n> D \<close>
  for T :: \<open>('e::sep_semigroup, 'f) \<phi>\<close>

  unfolding conj_imp_eq_imp_imp Action_Tag_def mapToA_cond_def split_map_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: BiCond_expn_BiCond BiCond_expn_\<phi>Some Cond_\<phi>Prod_expn_\<phi>Some \<phi>Some_\<phi>Prod[symmetric])
  \<medium_left_bracket> premises [] and MP\<^sub>1 and _ and MP\<^sub>2
    apply_rule ToA_Mapper_onward[OF MP\<^sub>1, where x=\<open>case x of (x,(w\<^sub>1,w\<^sub>2),e) \<Rightarrow> (x,w\<^sub>1,w\<^sub>2,e)\<close>]
    certified by (clarsimp simp add: image_iff split: prod.split, insert the_\<phi>(5), blast) \<semicolon>
  
    apply_rule ToA_Mapper_onward[OF MP\<^sub>2,
        where x=\<open>(case x of (x,(w\<^sub>1,w\<^sub>2),e) \<Rightarrow> case h\<^sub>1 (x,w\<^sub>1,w\<^sub>2,e) of (y\<^sub>1,r\<^sub>1) \<Rightarrow> r\<^sub>1)\<close>,
        THEN transformation_left_frame, simplified]
    certified by (insert the_\<phi>(5), clarsimp simp add: image_iff split: prod.split, force)
  \<medium_right_bracket> certified by (clarsimp simp add: image_iff split: prod.split)
    apply (rule conjunctionI, rule, rule conjunctionI)
  \<medium_left_bracket> premises [] and MP\<^sub>1 and _ and MP\<^sub>2
    apply_rule ToA_Mapper_backward[OF MP\<^sub>2,
        where x=\<open>case x of ((y\<^sub>1,y\<^sub>2),r) \<Rightarrow> (y\<^sub>2,r)\<close>,
        THEN transformation_left_frame, simplified]
    certified by (insert useful(1), clarsimp simp add: image_iff case_prod_beta prod.map_beta, force) ;;

    apply_rule ToA_Mapper_backward[OF MP\<^sub>1, where x=\<open>case x of ((y\<^sub>1,y\<^sub>2),r) \<Rightarrow> (y\<^sub>1,s\<^sub>2 (y\<^sub>2,r))\<close>]
    certified by (insert useful(1) ToA_Mapper_f_expn[OF MP\<^sub>2],
                clarsimp simp add: image_iff case_prod_beta prod.map_beta, force)
      
  \<medium_right_bracket> certified by (insert useful(1), clarsimp simp add: image_iff case_prod_beta prod.map_beta)
    apply (drule ToA_Mapper_f_expn, drule ToA_Mapper_f_expn, simp, rule)
    subgoal premises prems for y
      by (insert prems(5,6)[THEN bspec[OF _ prems(7)]],
          cases y, clarsimp, case_tac \<open>h\<^sub>1 (a, aa, b, c)\<close>, simp, case_tac \<open>h\<^sub>2 (ba, ca, d)\<close>, simp,
          case_tac \<open>s\<^sub>1 (g\<^sub>1 ab, s\<^sub>2 (g\<^sub>2 ac, r\<^sub>2 (bb, cb)))\<close>, simp) .

declare ToA_mapper_intro_Ex
        [OF _ _ \<phi>mapToA_split_goal_Ty, \<phi>reasoned 2,
         \<phi>reason %\<phi>mapToA_split_goal
            for \<open>\<m>\<a>\<p> _ : (_ \<^emph> _) \<^emph>[?var_C\<^sub>R] ?var_R \<mapsto> (_ \<^emph> _) \<^emph>[?var_C\<^sub>R] ?var_R'
                 \<o>\<v>\<e>\<r> _ : _ \<^emph>[?var_C\<^sub>W] ?var_W \<mapsto> _ \<^emph>[?var_C\<^sub>W] ?var_W'
                 \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]

(*
lemma [\<phi>reason %\<phi>mapToA_split_goal,
       THEN ToA_mapper_intro_Ex, simplified]:
  \<open> \<m>\<a>\<p> g\<^sub>1 \<otimes>\<^sub>f f\<^sub>2 : U\<^sub>1 \<^emph>[C\<^sub>R\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (R\<^sub>1, W\<^sub>2, E) \<mapsto> U\<^sub>1' \<^emph>[C\<^sub>R\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (R\<^sub>1', W\<^sub>2', E')
    \<o>\<v>\<e>\<r> f\<^sub>1 \<otimes>\<^sub>f w\<^sub>1 \<otimes>\<^sub>f w\<^sub>2 \<otimes>\<^sub>f e : T \<^emph>[C\<^sub>W\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>1, W\<^sub>2, E) \<mapsto> T' \<^emph>[C\<^sub>W\<^sub>1, C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>1', W\<^sub>2', E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>1 \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>1 \<i>\<n> apsnd prod.rotR ` D
\<Longrightarrow> (C\<^sub>R\<^sub>1 \<or> C\<^sub>W\<^sub>2 \<or> C\<^sub>E) \<and>
   (\<m>\<a>\<p> g\<^sub>2 \<otimes>\<^sub>f r\<^sub>2 : U\<^sub>2 \<^emph>[C\<^sub>R, C\<^sub>E] (R, E) \<mapsto> U\<^sub>2' \<^emph>[C\<^sub>R, C\<^sub>E] (R', E') \<comment> \<open>goto, \<section>\<open>Conditioned Targets\<close>\<close>
    \<o>\<v>\<e>\<r> f\<^sub>2 : R\<^sub>1 [C\<^sub>R\<^sub>1]\<^emph>[C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>2, E) \<mapsto> R\<^sub>1' [C\<^sub>R\<^sub>1]\<^emph>[C\<^sub>W\<^sub>2, C\<^sub>E] (W\<^sub>2', E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>2 \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>2 \<i>\<n> snd ` h\<^sub>1 ` apsnd prod.rotR ` D)
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W  = \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1  \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2  @tag \<A>merge \<comment> \<open>goto, \<section>\<open>Filter out empty slots\<close>\<close>
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W' = \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1' \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2' @tag \<A>merge
\<Longrightarrow> \<m>\<a>\<p> (g\<^sub>1 \<otimes>\<^sub>f g\<^sub>2) \<otimes>\<^sub>f r\<^sub>2: (U\<^sub>1 \<^emph> U\<^sub>2) \<^emph>[C\<^sub>R, C\<^sub>E] (R, E) \<mapsto> (U\<^sub>1' \<^emph> U\<^sub>2') \<^emph>[C\<^sub>R, C\<^sub>E] (R', E')
    \<o>\<v>\<e>\<r> f\<^sub>1 \<otimes>\<^sub>f (w\<^sub>1 \<otimes>\<^sub>f w\<^sub>2) \<otimes>\<^sub>f e : T \<^emph>[C\<^sub>W, C\<^sub>E] (W, E) \<mapsto> T' \<^emph>[C\<^sub>W, C\<^sub>E] (W', E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> prod.rotL o apsnd h\<^sub>2 o h\<^sub>1 o apsnd prod.rotR
        \<s>\<e>\<t>\<t>\<e>\<r> apsnd prod.rotL o s\<^sub>1 o apsnd s\<^sub>2 o prod.rotR
    \<i>\<n> D \<close>
  for T :: \<open>('e::sep_semigroup, 'f) \<phi>\<close>
  \<comment> \<open>E denotes \<open>external\<close>, which reflects frame rule and represents unchanging stuffs from outside.
      The subsequent target \<open>W\<^sub>2\<close> is given as the unchanging external objects in the transformation of \<open>U\<^sub>1\<close>.
      From the remainder \<open>R\<^sub>1\<close> together with \<open>W\<^sub>2\<close>, the transformation of \<open>U\<^sub>2\<close> can proceed.\<close>
  \<comment> \<open>map_prod is necessary in this rule. the mapping of the U and the remainder must be independent\<close>
  \<comment> \<open>the \<open>E\<close> is only used for passing items of neighbors horizontally and discarded between
      hierarchical levels because it is useless and actually impossible as its number is undetermined.
      Convention: \<open>T \<^emph>[W or R, E]\<close>\<close>

  unfolding conj_imp_eq_imp_imp Action_Tag_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: BiCond_expn_BiCond BiCond_expn_\<phi>Some Cond_\<phi>Prod_expn_\<phi>Some \<phi>Some_\<phi>Prod[symmetric])
  \<medium_left_bracket> premises MP\<^sub>1 and _ and MP\<^sub>2
    apply_rule ToA_Mapper_onward[OF MP\<^sub>1, where x=\<open>apsnd prod.rotR x\<close>]
    apply_rule ToA_Mapper_onward[OF MP\<^sub>2, where x=\<open>snd (h\<^sub>1 (apsnd prod.rotR x))\<close>, THEN transformation_right_frame, simplified]
  \<medium_right_bracket> apply (rule conjunctionI, rule, rule conjunctionI)
  \<medium_left_bracket> premises MP\<^sub>1 and _ and MP\<^sub>2
    apply_rule ToA_Mapper_backward[OF MP\<^sub>2, where x=\<open>snd (prod.rotR x)\<close>, THEN transformation_right_frame, simplified]
    certified by (insert useful(1), simp add: image_iff, force) ;;
    apply_rule ToA_Mapper_backward[OF MP\<^sub>1, where x=\<open>apsnd s\<^sub>2 (prod.rotR x)\<close>]
    certified by (insert useful(1) ToA_Mapper_f_expn[OF MP\<^sub>2],
                  clarsimp simp add: image_iff map_prod_eq_apfst_apsnd; force)
  \<medium_right_bracket> apply (drule ToA_Mapper_f_expn, drule ToA_Mapper_f_expn, simp, rule)
    subgoal premises prems for y
      by (insert prems(4,5)[THEN bspec[OF _ prems(6)]],
          cases y, clarsimp, case_tac \<open>h\<^sub>1 (a, aa, b, c)\<close>, simp, case_tac \<open>h\<^sub>2 (ba, ca, d)\<close>, simp,
          case_tac \<open>s\<^sub>1 (g\<^sub>1 ab, s\<^sub>2 (g\<^sub>2 ac, r\<^sub>2 (bb, cb)))\<close>, simp) .
*)

lemma \<phi>mapToA_split_source
  [\<phi>reason %\<phi>mapToA_split_source
      for \<open>\<m>\<a>\<p> _ : _ \<^emph>[_,_] (_,_) \<mapsto> _ \<^emph>[_,_] (_,_)
           \<o>\<v>\<e>\<r> _ : (_ \<^emph> _) \<^emph>[_,_] (_,_) \<mapsto> _ \<^emph>[_,_] (_,_)
           \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:

  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r\<^sub>1 \<otimes>\<^sub>f r\<^sub>2 \<otimes>\<^sub>f e : U  \<^emph>[C\<^sub>R\<^sub>1,C\<^sub>R\<^sub>2,C\<^sub>E] (R\<^sub>1,R\<^sub>2,E) \<mapsto> U' \<^emph>[C\<^sub>R\<^sub>1,C\<^sub>R\<^sub>2,C\<^sub>E] (R\<^sub>1',R\<^sub>2',E')
    \<o>\<v>\<e>\<r> f\<^sub>1 \<otimes>\<^sub>f w\<^sub>1 : T\<^sub>1 \<^emph>[C\<^sub>W\<^sub>1,C\<^sub>R\<^sub>2,C\<^sub>E] (W\<^sub>1,R\<^sub>2,E) \<mapsto> T\<^sub>1' \<^emph>[C\<^sub>W\<^sub>1,C\<^sub>R\<^sub>2,C\<^sub>E] (W\<^sub>1',R\<^sub>2',E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>1 \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>1 \<i>\<n> (\<lambda>((x\<^sub>1,x\<^sub>2),w\<^sub>2e). (x\<^sub>1, h\<^sub>2 (x\<^sub>2, w\<^sub>2e))) ` D
\<Longrightarrow> mapToA_cond C\<^sub>W\<^sub>1 C\<^sub>R\<^sub>2 C\<^sub>E
   (\<m>\<a>\<p> w\<^sub>1 : W\<^sub>1 [C\<^sub>W\<^sub>1]\<^emph>[C\<^sub>R\<^sub>2,C\<^sub>E] (R\<^sub>2,E) \<mapsto> W\<^sub>1' [C\<^sub>W\<^sub>1]\<^emph>[C\<^sub>R\<^sub>2,C\<^sub>E] (R\<^sub>2',E')
    \<o>\<v>\<e>\<r> f\<^sub>2 \<otimes>\<^sub>f w\<^sub>2 : T\<^sub>2 \<^emph>[C\<^sub>W,C\<^sub>E] (W,E) \<mapsto> T\<^sub>2' \<^emph>[C\<^sub>W,C\<^sub>E] (W',E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>2 \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>2 \<i>\<n> (\<lambda>((x\<^sub>1,x\<^sub>2),w\<^sub>2e). (x\<^sub>2, w\<^sub>2e)) ` D)
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R  = \<half_blkcirc>[C\<^sub>R\<^sub>1] R\<^sub>1  \<^emph> \<half_blkcirc>[C\<^sub>R\<^sub>2] R\<^sub>2  @tag \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>1] R\<^sub>1' \<^emph> \<half_blkcirc>[C\<^sub>R\<^sub>2] R\<^sub>2' @tag \<A>merge
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f (r\<^sub>1 \<otimes>\<^sub>f r\<^sub>2) \<otimes>\<^sub>f e : U \<^emph>[C\<^sub>R,C\<^sub>E] (R,E) \<mapsto> U' \<^emph>[C\<^sub>R,C\<^sub>E] (R',E')
    \<o>\<v>\<e>\<r> (f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2) \<otimes>\<^sub>f w\<^sub>2 : (T\<^sub>1 \<^emph> T\<^sub>2) \<^emph>[C\<^sub>W,C\<^sub>E] (W,E) \<mapsto> (T\<^sub>1' \<^emph> T\<^sub>2') \<^emph>[C\<^sub>W,C\<^sub>E] (W',E')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>((x\<^sub>1,x\<^sub>2),w\<^sub>2e). case h\<^sub>1 (x\<^sub>1, h\<^sub>2 (x\<^sub>2, w\<^sub>2e)) of (y,r\<^sub>1,r\<^sub>2,e) \<Rightarrow> (y,(r\<^sub>1,r\<^sub>2),e))
         \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>(y,(r\<^sub>1,r\<^sub>2),e). case s\<^sub>1 (y,r\<^sub>1,r\<^sub>2,e) of (x\<^sub>1,w\<^sub>2e) \<Rightarrow>
                               case s\<^sub>2 w\<^sub>2e of (x\<^sub>2,we) \<Rightarrow> ((x\<^sub>1,x\<^sub>2),we))
      \<i>\<n> D \<close>
  for U :: \<open>('i::sep_semigroup, 'a) \<phi>\<close>

  unfolding conj_imp_eq_imp_imp Action_Tag_def mapToA_cond_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: BiCond_expn_BiCond BiCond_expn_\<phi>Some Cond_\<phi>Prod_expn_\<phi>Some \<phi>Some_\<phi>Prod[symmetric])
  \<medium_left_bracket> premises MP\<^sub>1 and _ and MP\<^sub>2
    apply_rule ToA_Mapper_onward[OF MP\<^sub>2, where x=\<open>case x of ((x\<^sub>1,x\<^sub>2),w\<^sub>2e) \<Rightarrow> (x\<^sub>2, w\<^sub>2e)\<close>, THEN transformation_left_frame, simplified]
    certified by (clarsimp split: prod.split simp: image_iff, insert the_\<phi>(5), force) ;;
    apply_rule ToA_Mapper_onward[OF MP\<^sub>1, where x=\<open>case x of ((x\<^sub>1,x\<^sub>2),w\<^sub>2e) \<Rightarrow> (x\<^sub>1, h\<^sub>2 (x\<^sub>2, w\<^sub>2e))\<close>]
    certified by (clarsimp split: prod.split simp: image_iff, insert the_\<phi>(5), force)
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule conjunctionI)
  \<medium_left_bracket> premises MP\<^sub>1 and _ and MP\<^sub>2
    apply_rule ToA_Mapper_backward[OF MP\<^sub>1, where x=\<open>case x of (y,(r\<^sub>1,r\<^sub>2),e) \<Rightarrow> (y,r\<^sub>1,r\<^sub>2,e)\<close>]
    certified apply (insert useful(1), clarsimp split: prod.split simp add: image_iff)
      subgoal premises prems
        by (rule bexI[OF _ prems(1)], insert prems, clarsimp split: prod.split simp add: prod.map_beta) . ;;

    apply_rule ToA_Mapper_backward[OF MP\<^sub>2,
        where x=\<open>case x of (y,(r\<^sub>1,r\<^sub>2),e) \<Rightarrow> case s\<^sub>1 (y,r\<^sub>1,r\<^sub>2,e) of (x\<^sub>1,w\<^sub>2e) \<Rightarrow> w\<^sub>2e\<close>,
        THEN transformation_left_frame, simplified]
    certified apply (insert useful(1) ToA_Mapper_f_expn[OF MP\<^sub>1],
          clarsimp split: prod.split simp add: image_iff)
      subgoal premises prems for a b aa ba x1 ab bb bc x1a ac ad bd
        by (rule bexI[OF _ prems(2)],
            insert prems(1)[THEN bspec[OF _ prems(2)]] prems(3-),
            clarsimp split: prod.split,
            case_tac \<open>h\<^sub>1 (a, h\<^sub>2 (b, aa, ba))\<close>, simp) .
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply(drule ToA_Mapper_f_expn, drule ToA_Mapper_f_expn,
          clarsimp split: prod.split)
    subgoal premises prems
      by (insert prems(4,5)[THEN bspec[OF _ \<open>_ \<in> D\<close>]],
          insert prems(7-), clarsimp) .

declare ToA_mapper_intro_Ex
    [OF _ _ \<phi>mapToA_split_source, \<phi>reasoned 2,
     \<phi>reason %\<phi>mapToA_split_source
      for \<open>\<m>\<a>\<p> _ : _ \<^emph>[?var_C\<^sub>R] ?var_R \<mapsto> _ \<^emph>[?var_C\<^sub>R] ?var_R'
           \<o>\<v>\<e>\<r> _ : (_ \<^emph> _) \<^emph>[?var_C\<^sub>W] ?var_W \<mapsto> _ \<^emph>[?var_C\<^sub>W] ?var_W'
           \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]

end

paragraph \<open>Assertion Level\<close>


definition \<open>subst_sp C U T S S' direction \<comment> \<open>True for splitting target\<close>
                     C\<^sub>R R R' C\<^sub>W W W'
  \<longleftrightarrow>  (if C
        then \<s>\<u>\<b>\<s>\<t> U \<f>\<o>\<r> T \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] W \<t>\<o> S' \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R'
        else if direction
        then (C\<^sub>R, R, R', C\<^sub>W, W, W') = (False, \<top>, \<top>, True, T, U)
        else (C\<^sub>R, R, R', R, C\<^sub>W, W, W') = (True, S, S', S', False, \<top>, \<top>))\<close>

definition \<open>getter_sp C T M C\<^sub>R R C\<^sub>W W direction
  \<longleftrightarrow> (if C
       then \<g>\<e>\<t> T \<f>\<r>\<o>\<m> M \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] W
       else if direction
       then (W, C\<^sub>W, C\<^sub>R, R) = (T, True, False, \<top>)
       else (W, C\<^sub>W, C\<^sub>R, R) = (\<top>, False, True, M)) \<close>

\<phi>reasoner_group subst_sp = (1000, [1000,1030]) \<open>\<close>

declare [[
  \<phi>reason_default_pattern \<open>subst_sp ?C _ _ _ _ ?direction  _ _ _  _ _ _ \<close> \<Rightarrow>
                          \<open>subst_sp ?C _ _ _ _ ?direction  _ _ _  _ _ _ \<close>    (100)
                      and \<open>getter_sp ?C _ _ _ _ _ _ ?direction\<close> \<Rightarrow>
                          \<open>getter_sp ?C _ _ _ _ _ _ ?direction\<close>              (100)
]]

lemma [\<phi>reason %subst_sp]:
  \<open> \<s>\<u>\<b>\<s>\<t> U \<f>\<o>\<r> T \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] W \<t>\<o> S' \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R'
\<Longrightarrow> subst_sp True U T S S' Any
              C\<^sub>R R R' C\<^sub>W W W' \<close>
  unfolding subst_sp_def Action_Tag_def
  by (clarsimp simp: Cond_Unital_Ins_BI_\<phi>Type \<phi>Prod_expn')

lemma [\<phi>reason %subst_sp]:
  \<open> subst_sp False (y \<Ztypecolon> U) (x \<Ztypecolon> T) S S' True
             False \<top> \<top> True (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<close>
  unfolding subst_sp_def Action_Tag_def
  by (clarsimp simp: Cond_Unital_Ins_BI_\<phi>Type \<phi>Prod_expn')

lemma [\<phi>reason %subst_sp]:
  \<open> subst_sp False (y \<Ztypecolon> U) (x \<Ztypecolon> T) S S False
             True S S False (unspec \<Ztypecolon> \<top>\<^sub>\<phi>) (unspec \<Ztypecolon> \<top>\<^sub>\<phi>) \<close>
  unfolding subst_sp_def Action_Tag_def
  by (clarsimp simp: Cond_Unital_Ins_BI_\<phi>Type \<phi>Prod_expn' \<phi>Any.unfold)

lemma [\<phi>reason %subst_sp]:
  \<open> \<g>\<e>\<t> T \<f>\<r>\<o>\<m> M \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] W
\<Longrightarrow> getter_sp True T M C\<^sub>R R C\<^sub>W W direction \<close>
  unfolding getter_sp_def
  by (clarsimp simp: Cond_Unital_Ins_BI_\<phi>Type \<phi>Prod_expn')

lemma [\<phi>reason %subst_sp]:
  \<open> getter_sp False T M False \<top> True T True \<close>
  unfolding getter_sp_def
  by simp

lemma [\<phi>reason %subst_sp]:
  \<open> getter_sp False T M True M False (unspec \<Ztypecolon> \<top>\<^sub>\<phi>) False \<close>
  unfolding getter_sp_def \<phi>Any.unfold
  by simp









lemma [\<phi>reason %\<phi>mapToA_split_goal]:
  \<open> \<s>\<u>\<b>\<s>\<t> fst y \<Ztypecolon> U\<^sub>1 \<f>\<o>\<r> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1 \<t>\<o> Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w\<^sub>1' \<Ztypecolon> W\<^sub>1' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R\<^sub>1'
\<Longrightarrow> subst_sp C\<^sub>R\<^sub>1 (snd y \<Ztypecolon> U\<^sub>2) (x\<^sub>2 \<Ztypecolon> T\<^sub>2) R\<^sub>1 R\<^sub>1' True
             C\<^sub>R R R' C\<^sub>W\<^sub>2 (w\<^sub>2 \<Ztypecolon> W\<^sub>2) (w\<^sub>2' \<Ztypecolon> W\<^sub>2')
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1, w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @tag \<A>merge
\<Longrightarrow> (w' \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W') = ((w\<^sub>1', w\<^sub>2') \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1' \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2') @tag \<A>merge
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U\<^sub>1 \<^emph> U\<^sub>2 \<f>\<o>\<r> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R' \<close>
  for S :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Subst_def Action_Tag_def subst_sp_def
  by (cases C\<^sub>R\<^sub>1; cases C\<^sub>R; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Prod_expn'' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      smt (verit, ccfv_threshold)
      transformation_trans[where P=True and Q=True, simplified]
      transformation_left_frame transformation_right_frame
      mult.assoc)

lemma [\<phi>reason %\<phi>mapToA_split_goal+5]:
  \<open> \<s>\<u>\<b>\<s>\<t> y\<^sub>1 \<Ztypecolon> U\<^sub>1 \<f>\<o>\<r> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1 \<t>\<o> Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w\<^sub>1' \<Ztypecolon> W\<^sub>1' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R\<^sub>1'
\<Longrightarrow> subst_sp C\<^sub>R\<^sub>1 (y\<^sub>2 \<Ztypecolon> U\<^sub>2) (x\<^sub>2 \<Ztypecolon> T\<^sub>2) R\<^sub>1 R\<^sub>1' True
             C\<^sub>R R R' C\<^sub>W\<^sub>2 (w\<^sub>2 \<Ztypecolon> W\<^sub>2) (w\<^sub>2' \<Ztypecolon> W\<^sub>2')
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1, w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @tag \<A>merge
\<Longrightarrow> (w' \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W') = ((w\<^sub>1', w\<^sub>2') \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1' \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2') @tag \<A>merge
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> (y\<^sub>1, y\<^sub>2) \<Ztypecolon> U\<^sub>1 \<^emph> U\<^sub>2 \<f>\<o>\<r> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Y \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R' \<close>
  for S :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Subst_def Action_Tag_def subst_sp_def
  by (cases C\<^sub>R\<^sub>1; cases C\<^sub>R; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Prod_expn'' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      smt (verit, ccfv_threshold)
      transformation_trans[where P=True and Q=True, simplified]
      transformation_left_frame transformation_right_frame
      mult.assoc)


lemma [\<phi>reason %\<phi>mapToA_split_goal]:
  \<open> \<g>\<e>\<t> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] M \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1
\<Longrightarrow> getter_sp C\<^sub>R\<^sub>1 (x\<^sub>2 \<Ztypecolon> T\<^sub>2) M C\<^sub>R\<^sub>2 R C\<^sub>W\<^sub>2 (w\<^sub>2 \<Ztypecolon> W\<^sub>2) True
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1,w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @tag \<A>merge
\<Longrightarrow> \<g>\<e>\<t> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Extract_def Premise_def Action_Tag_def getter_sp_def
  by (cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      metis mult.assoc)


lemma [\<phi>reason %\<phi>mapToA_split_source]:
  \<open> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1 \<t>\<o> Y\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w\<^sub>1' \<Ztypecolon> W\<^sub>1' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R\<^sub>1'
\<Longrightarrow> subst_sp C\<^sub>W\<^sub>1 (w\<^sub>1' \<Ztypecolon> W\<^sub>1') (w\<^sub>1 \<Ztypecolon> W\<^sub>1) S\<^sub>2 Y\<^sub>2 False
             C\<^sub>R\<^sub>2 R\<^sub>2 R\<^sub>2' C\<^sub>W (w \<Ztypecolon> W) (w' \<Ztypecolon> W')
\<Longrightarrow> \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R] R  = \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>1] R\<^sub>1  * \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>2] R\<^sub>2  @tag \<A>merge
\<Longrightarrow> \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R] R' = \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>1] R\<^sub>1' * \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>2] R\<^sub>2' @tag \<A>merge
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>1 * S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Y\<^sub>1 * Y\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R' \<close>
  for S\<^sub>1 :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Subst_def Action_Tag_def subst_sp_def
  by (cases C\<^sub>R; cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W; cases C\<^sub>W\<^sub>1;
      clarsimp simp add: \<phi>Cond_Unital_BI_eq_strip Cond_Unital_Ins_BI_contract Cond_Unital_Ins_BI_eq_1;
      smt (verit, ccfv_threshold)
        transformation_trans[where P=True and Q=True, simplified]
        transformation_right_frame transformation_left_frame
        mult.assoc)


lemma [\<phi>reason %\<phi>mapToA_split_source]:
  \<open> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] R\<^sub>1 \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2
\<Longrightarrow> getter_sp C\<^sub>W\<^sub>2 (w\<^sub>2 \<Ztypecolon> W\<^sub>2) S\<^sub>2 C\<^sub>R\<^sub>2 R\<^sub>2 C\<^sub>W (w \<Ztypecolon> W) False
\<Longrightarrow> \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R] R = \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>1] R\<^sub>1 * \<half_blkcirc>\<^sub>B\<^sub>I[C\<^sub>R\<^sub>2] R\<^sub>2 @tag \<A>merge
\<Longrightarrow> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> S\<^sub>1 * S\<^sub>2 \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S\<^sub>1 :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Extract_def Action_Tag_def getter_sp_def
  by (cases C\<^sub>R; cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W; cases C\<^sub>W\<^sub>2;
      clarsimp simp add: \<phi>Cond_Unital_BI_eq_strip Cond_Unital_Ins_BI_contract Cond_Unital_Ins_BI_eq_1;
      metis mult.assoc)

(*

lemma
  \<open> \<g>\<e>\<t> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] M \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R\<^sub>1
\<Longrightarrow> \<g>\<e>\<t> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<f>\<r>\<o>\<m> M \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1,w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @tag \<A>merge
\<Longrightarrow> \<g>\<e>\<t> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S :: \<open>'c::sep_semigroup BI\<close>
  unfolding ToA_Extract'_def Premise_def Action_Tag_def
  by (cases C\<^sub>R\<^sub>2; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      metis mult.assoc)

lemma
  \<open> \<g>\<e>\<t> x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>1] M \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>1] w\<^sub>1 \<Ztypecolon> W\<^sub>1
\<Longrightarrow> if C\<^sub>R\<^sub>1 then \<g>\<e>\<t> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<f>\<r>\<o>\<m> M \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W\<^sub>2] w\<^sub>2 \<Ztypecolon> W\<^sub>2
           else Identity_Elements T\<^sub>2 D
             \<and>\<^sub>\<r> (Hint_Identity_Element T x\<^sub>2 \<or>\<^sub>c\<^sub>u\<^sub>t True)
             \<and>\<^sub>\<r> (w\<^sub>2, W\<^sub>2, C\<^sub>W\<^sub>2, C\<^sub>R\<^sub>2, R) = (unspec, \<top>\<^sub>\<phi>, False, False, \<top>)
             \<and>\<^sub>\<r> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> (D x\<^sub>2))
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) = ((w\<^sub>1,w\<^sub>2) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W\<^sub>1] W\<^sub>1 \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>2] W\<^sub>2) @tag \<A>merge
\<Longrightarrow> \<g>\<e>\<t> (x\<^sub>1, x\<^sub>2) \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2 \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R\<^sub>2] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  for S :: \<open>'c::sep_monoid BI\<close>
  unfolding ToA_Extract'_def Premise_def Action_Tag_def Ant_Seq_def
            Identity_Elements_alt_def
  by (cases C\<^sub>R\<^sub>1; cases C\<^sub>R\<^sub>2; cases C\<^sub>W\<^sub>1; cases C\<^sub>W\<^sub>2; cases C\<^sub>W;
      clarsimp simp add: \<phi>Prod_expn' \<phi>Some_mult_contract \<phi>Some_eq_term_strip \<phi>Some_not_1;
      metis mult.assoc)

*)


subsubsection \<open>Reflexive\<close>

lemma [\<phi>reason %\<phi>mapToA_refl for \<open>\<m>\<a>\<p> _ : ?T \<mapsto> ?U \<o>\<v>\<e>\<r> _ : ?T \<mapsto> ?U \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>,
       \<phi>reason default %\<phi>mapToA_unify for \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> f : T \<mapsto> U \<o>\<v>\<e>\<r> f : T \<mapsto> U \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> id \<s>\<e>\<t>\<t>\<e>\<r> id \<i>\<n> D \<close>
  unfolding ToA_Mapper_def
  by clarsimp

lemma [\<phi>reason %\<phi>mapToA_refl+1 for \<open>\<m>\<a>\<p> _ : ?T \<^emph>[_] _ \<mapsto> ?U \<^emph>[_] _ \<o>\<v>\<e>\<r> _ : ?T \<^emph>[_] _ \<mapsto> ?U \<^emph>[_] _
                                    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>,
       \<phi>reason default %\<phi>mapToA_unify+1 for \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> f : T \<^emph>[False] \<top>\<^sub>\<phi> \<mapsto> U \<^emph>[False] \<top>\<^sub>\<phi>
    \<o>\<v>\<e>\<r> f : T \<^emph>[False] \<top>\<^sub>\<phi> \<mapsto> U \<^emph>[False] \<top>\<^sub>\<phi>
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> id \<s>\<e>\<t>\<t>\<e>\<r> id \<i>\<n> D \<close>
  unfolding ToA_Mapper_def
  by clarsimp


subsubsection \<open>Fallback\<close>

lemma [\<phi>reason %\<phi>mapToA_fallbacks]:
  \<open> \<m>\<a>\<p> f \<otimes>\<^sub>f g : U \<^emph>[True] T \<mapsto> U' \<^emph>[True] T'
    \<o>\<v>\<e>\<r> g \<otimes>\<^sub>f f : T \<^emph>[True] U \<mapsto> T' \<^emph>[True] U'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> prod.swap \<s>\<e>\<t>\<t>\<e>\<r> prod.swap \<i>\<n> D \<close>
  for T :: \<open>'b \<Rightarrow> 'e::sep_ab_semigroup set\<close>
  unfolding ToA_Mapper_def Transformation_def
  by (auto; insert sep_disj_commuteI sep_mult_commute; blast)

lemma [\<phi>reason %\<phi>mapToA_fallbacks
           for \<open>\<g>\<e>\<t> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _\<close>]:
  \<open> \<g>\<e>\<t> X \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[True] S \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[True] X \<close>
  for X :: \<open>'c::sep_ab_semigroup BI\<close>
  unfolding ToA_Extract_def
  by (clarsimp simp: mult.commute)

lemma [\<phi>reason %\<phi>mapToA_fallbacks
           for \<open>\<s>\<u>\<b>\<s>\<t> _ \<f>\<o>\<r> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> _\<close>]:
  \<open> \<s>\<u>\<b>\<s>\<t> X \<f>\<o>\<r> Y \<f>\<r>\<o>\<m> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[True] S \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[True] Y \<t>\<o> S \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> X \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> S \<close>
  for X :: \<open>'c::sep_ab_semigroup BI\<close>
  unfolding ToA_Subst_def
  by (clarsimp simp: mult.commute)



subsection \<open>Entry Points\<close>

paragraph \<open>From \<open>\<s>\<u>\<b>\<s>\<t>\<close> or \<open>\<g>\<e>\<t>\<close>\<close>

definition \<open>ToA_get_IE w W D \<longleftrightarrow> Identity_Elements W D \<and> D w\<close>

lemma [\<phi>reason %\<phi>mapToA_init except \<open>\<g>\<e>\<t> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _\<close>]:
  \<open> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<or>\<^sub>c\<^sub>u\<^sub>t
    ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W))
\<Longrightarrow> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  unfolding ToA_Extract_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def
  by (cases C\<^sub>R; clarsimp)

lemma [\<phi>reason %\<phi>mapToA_init+10 except \<open>\<g>\<e>\<t> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _\<close>]:
  \<open> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W
\<Longrightarrow> if C\<^sub>W then Identity_Elements W D
                \<comment> \<open>ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W))\<close>
            \<and>\<^sub>\<r> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D w
          else True
\<Longrightarrow> \<g>\<e>\<t> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  for Src :: \<open>'c::sep_magma_1 BI\<close>
  unfolding ToA_Extract_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def
  by (cases C\<^sub>W; cases C\<^sub>R; clarsimp)

lemma [\<phi>reason %\<phi>mapToA_init except \<open>\<s>\<u>\<b>\<s>\<t> _ \<f>\<o>\<r> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> _\<close>]:
  \<open> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R'
\<Longrightarrow> mapToA_unify_A (x \<Ztypecolon> T) Src R R'
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<or>\<^sub>c\<^sub>u\<^sub>t ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W))
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  for Src :: \<open>'c::sep_magma_1 BI\<close>
  unfolding ToA_Subst_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def mapToA_unify_A_def
  by (cases C\<^sub>R; clarsimp)

lemma [\<phi>reason %\<phi>mapToA_init+10 except \<open>\<s>\<u>\<b>\<s>\<t> _ \<f>\<o>\<r> _ \<f>\<r>\<o>\<m> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[_] _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[_] _ \<t>\<o> _ \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> _ \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> _\<close>]:
  \<open> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> w' \<Ztypecolon> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> R'
\<Longrightarrow> mapToA_unify_A (x \<Ztypecolon> T) Src R R'
\<Longrightarrow> if C\<^sub>W then (Identity_Element\<^sub>E (w \<Ztypecolon> W)
             \<and>\<^sub>\<r> Identity_Element\<^sub>I (w' \<Ztypecolon> W') Any)
            \<comment> \<open>\<open>\<or>\<^sub>c\<^sub>u\<^sub>t ERROR TEXT(\<open>Fail to extract\<close> (x \<Ztypecolon> T) \<open>from\<close> Src \<open>due to the absence of\<close> (w \<Ztypecolon> W)\<close>\<close>
          else True
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> U \<f>\<o>\<r> x \<Ztypecolon> T \<f>\<r>\<o>\<m> Src \<t>\<o> Ret \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R \<close>
  for Src :: \<open>'c::sep_magma_1 BI\<close>
  unfolding ToA_Subst_def Identity_Elements_alt_def Orelse_shortcut_def Ant_Seq_def
            ERROR_def Premise_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def mapToA_unify_A_def
  by (cases C\<^sub>W; cases C\<^sub>R; clarsimp;
      smt (verit, ccfv_threshold)
        transformation_trans[where P=True and Q=True, simplified]
        transformation_left_frame transformation_right_frame
        mult.assoc transformation_weaken mult_1_left mult_1_right)


lemma [\<phi>reason %\<phi>mapToA_init]:
  \<open> \<m>\<a>\<p> g : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W' \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> {(x,w)}
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret : h (x, w)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret\<^sub>f : f (x, w)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret\<^sub>1 : fst ret
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret\<^sub>2 : snd ret
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret\<^sub>f\<^sub>1 : fst ret\<^sub>f
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret\<^sub>f\<^sub>2 : snd ret\<^sub>f
\<Longrightarrow> \<d>\<o> lookup_a_mapper g ret (y', r')
\<Longrightarrow> \<s>\<u>\<b>\<s>\<t> y' \<Ztypecolon> U' \<f>\<o>\<r> ret\<^sub>1 \<Ztypecolon> U \<f>\<r>\<o>\<m> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] ret\<^sub>2 \<Ztypecolon> R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W
      \<t>\<o> ret\<^sub>f\<^sub>1 \<Ztypecolon> T' \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g> ret\<^sub>f\<^sub>2 \<Ztypecolon> W' \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g> r' \<Ztypecolon> R' \<close>
  unfolding ToA_Mapper_def ToA_Subst_def Premise_def Simplify_def
            lookup_a_mapper_def Simplify_def
  by (cases C\<^sub>R; cases C\<^sub>W; clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn'; metis fst_eqD snd_conv)

lemma [\<phi>reason %\<phi>mapToA_init+10]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r\<^sub>f : U \<^emph>[C\<^sub>R] R \<mapsto> U \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w\<^sub>f : T \<^emph>[C\<^sub>W] W \<mapsto> T \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> {(x,w)}
\<Longrightarrow> mapToA_assign_id g
\<Longrightarrow> mapToA_assign_id f
\<Longrightarrow> if C\<^sub>R then mapToA_assign_id r\<^sub>f else True
\<Longrightarrow> if C\<^sub>W then mapToA_assign_id w\<^sub>f else True
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret : h (x, w)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret\<^sub>1 : fst ret
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ret\<^sub>2 : snd ret
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> ret\<^sub>1 = y
\<Longrightarrow> \<g>\<e>\<t> y \<Ztypecolon> U \<f>\<r>\<o>\<m> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] ret\<^sub>2 \<Ztypecolon> R \<d>\<e>\<m>\<a>\<n>\<d>\<i>\<n>\<g>[C\<^sub>W] w \<Ztypecolon> W \<close>
  unfolding ToA_Extract_def ToA_Mapper_def BI_eq_ToA Premise_def mapToA_assign_id_def
            Simplify_rev_def
  by (cases C\<^sub>R; cases C\<^sub>W; clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn'; metis fst_eqD snd_conv)


paragraph \<open>Direct use of ToA_Mapper\<close>

definition \<open>ToAmap_assign_empty C\<^sub>R r h s R R' r\<^sub>x h\<^sub>x s\<^sub>x R\<^sub>x R'\<^sub>x \<longleftrightarrow>
  (\<forall>g f D U U' T T'.
     (\<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
      \<o>\<v>\<e>\<r> f : T \<mapsto> T'
      \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D) \<longrightarrow>
     (\<m>\<a>\<p> g \<otimes>\<^sub>f r\<^sub>x : U \<^emph> R\<^sub>x \<mapsto> U' \<^emph> R'\<^sub>x
      \<o>\<v>\<e>\<r> f : T \<mapsto> T'
      \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>x \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>x \<i>\<n> D))\<close>

definition \<open>ToAmap_assign_empty_src C\<^sub>W h s W W' D w h\<^sub>x s\<^sub>x D\<^sub>x \<longleftrightarrow>
  (\<forall>g f U U' T T'.
      (\<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D\<^sub>x) \<longrightarrow>
      (\<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>x \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>x \<i>\<n> D))\<close>

\<phi>reasoner_group ToAmap_assign_empty = (1100, [10, 2000]) for \<open>ToAmap_assign_empty C\<^sub>R r h s R R' r\<^sub>x h\<^sub>x s\<^sub>x R\<^sub>x R'\<^sub>x\<close> \<open>\<close>
         and ToAmap_assign_empty_src = (1100, [10, 2000]) for \<open>ToAmap_assign_empty_src C\<^sub>W h s W W' D w h\<^sub>x s\<^sub>x D\<^sub>x\<close> \<open>\<close>

declare [[
  \<phi>reason_default_pattern \<open>ToAmap_assign_empty ?C\<^sub>R ?r ?h ?s ?R ?R' _ _ _ _ _\<close>
                       \<Rightarrow> \<open>ToAmap_assign_empty ?C\<^sub>R ?r ?h ?s ?R ?R' _ _ _ _ _\<close>     (100)
    and                   \<open>ToAmap_assign_empty_src ?C\<^sub>W ?h ?s ?W ?W' ?D _ _ _ _\<close>
                       \<Rightarrow> \<open>ToAmap_assign_empty_src ?C\<^sub>W ?h ?s ?W ?W' ?D _ _ _ _\<close>   (100)
]]

lemma [\<phi>reason %ToAmap_assign_empty]:
  \<open> ToAmap_assign_empty False r h s R R' id (apsnd (\<lambda>_. ()) o h) (s o apsnd (\<lambda>_. ())) \<circle> \<circle> \<close>
  for R :: \<open>('c::sep_magma_1, 'r) \<phi>\<close>
  unfolding ToAmap_assign_empty_def
  by (auto simp: ToA_Mapper_def Transformation_def prod.map_beta)

lemma [\<phi>reason %ToAmap_assign_empty]:
  \<open> ToAmap_assign_empty True r h s R R' r h s R R' \<close>
  unfolding ToAmap_assign_empty_def
  by simp

lemma [\<phi>reason %ToAmap_assign_empty_src]:
  \<open> ToAmap_assign_empty_src False h s W W' D any (\<lambda>x. h (x, unspec)) (fst o s) (D \<times> {unspec}) \<close>
  unfolding ToAmap_assign_empty_src_def
  by (auto simp: ToA_Mapper_def Transformation_def prod.map_beta, metis fst_conv)

lemma [\<phi>reason %ToAmap_assign_empty_src]:
  \<open> Identity_Elements\<^sub>E W  D\<^sub>E
\<Longrightarrow> Identity_Elements\<^sub>I W' D\<^sub>I P\<^sub>I
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x. D\<^sub>E x \<longleftrightarrow> x = \<epsilon>) \<and> (D\<^sub>I (w \<epsilon>))
\<Longrightarrow> ToAmap_assign_empty_src True h s W W' D w (\<lambda>x. h (x, \<epsilon>)) (fst o s) (D \<times> {\<epsilon>}) \<close>
  for W :: \<open>('c::sep_magma_1, 'w) \<phi>\<close>
  unfolding ToAmap_assign_empty_src_def Identity_Elements\<^sub>E_def Identity_Elements\<^sub>I_def
            Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def Premise_def
  by (auto simp: ToA_Mapper_def Transformation_def prod.map_beta,
      metis mult_1_class.mult_1_right sep_magma_1_left,
      metis mult_1_class.mult_1_right snd_conv,
      metis fst_conv)


lemma [\<phi>reason %\<phi>mapToA_norm
           for \<open>\<m>\<a>\<p> _ \<otimes>\<^sub>f _ : _ \<^emph> _ \<mapsto> _ \<^emph> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
                \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D
\<Longrightarrow> ToAmap_assign_empty C\<^sub>R r h s R R' r\<^sub>x h\<^sub>x s\<^sub>x R\<^sub>x R'\<^sub>x
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r\<^sub>x : U \<^emph> R\<^sub>x \<mapsto> U' \<^emph> R'\<^sub>x \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>x \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>x \<i>\<n> D \<close>
  for T :: \<open>('c::sep_magma,'x) \<phi>\<close>
  unfolding ToAmap_assign_empty_def
  by blast

lemma [\<phi>reason %\<phi>mapToA_norm
           for \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _
                \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>
           except \<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
                   \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D'
\<Longrightarrow> ToAmap_assign_empty_src C\<^sub>W h s W W' D w h' s' D'
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U' \<o>\<v>\<e>\<r> f : T \<mapsto> T'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h' \<s>\<e>\<t>\<t>\<e>\<r> s' \<i>\<n> D \<close>
  unfolding ToAmap_assign_empty_src_def
  by blast


subsection \<open>Finale\<close>

hide_const(open) mapToA_cond mapToA_unify_A lookup_a_mapper split_map
                 ToAmap_assign_empty_src ToAmap_assign_empty

ML \<open>
fun transformation_counter' bvtys concl =
  case try Phi_Syntax.dest_transformation concl
    of SOME (S,T,_) => SOME (Phi_Syntax.number_of_typ_operators_in_assertion bvtys S +
                             Phi_Syntax.number_of_typ_operators_in_assertion bvtys T )
     | _ => (
  case try Phi_Syntax.dest_ToA_Extract concl
    of SOME (S, T) => SOME (Phi_Syntax.number_of_typ_operators_in_assertion bvtys S +
                            Phi_Syntax.number_of_typ_operators_in_assertion bvtys T )
     | _ => (
  case try Phi_Syntax.dest_ToA_Subst concl
    of SOME (A,B,C,D) => SOME ( Phi_Syntax.number_of_typ_operators_in_assertion bvtys A +
                                Phi_Syntax.number_of_typ_operators_in_assertion bvtys B +
                                Phi_Syntax.number_of_typ_operators_in_assertion bvtys C +
                                Phi_Syntax.number_of_typ_operators_in_assertion bvtys D )
     | _ => (
  case try Phi_Syntax.dest_ToA_Mapper concl
    of SOME (_,U,U',_,T,T',_,_,_) =>
          SOME (Phi_Syntax.number_of_typ_operators bvtys U +
                Phi_Syntax.number_of_typ_operators bvtys T )
     | _ => NONE
  )))

fun transformation_counter thm =
  let val (bvtys, concl) = Phi_Help.strip_meta_hhf_bvtys (Phi_Help.leading_antecedent' thm)
   in transformation_counter' bvtys concl
   |> Option.map (fn n => (if n = 0 then () else (); n))
  end

val _ = (
  PLPR_Statistics.add_subgoal_counter (\<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>, transformation_counter) ;
  PLPR_Statistics.add_subgoal_counter (\<^pattern_prop>\<open>\<g>\<e>\<t> _ \<f>\<r>\<o>\<m> _\<close>, transformation_counter) ;
  PLPR_Statistics.add_subgoal_counter (\<^pattern_prop>\<open>\<s>\<u>\<b>\<s>\<t> _ \<f>\<o>\<r> _ \<f>\<r>\<o>\<m> _ \<t>\<o> _\<close>, transformation_counter) ;
  PLPR_Statistics.add_subgoal_counter (\<^pattern_prop>\<open>\<m>\<a>\<p> _ : _ \<mapsto> _ \<o>\<v>\<e>\<r> _ : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>, transformation_counter)
)

\<close>

end
