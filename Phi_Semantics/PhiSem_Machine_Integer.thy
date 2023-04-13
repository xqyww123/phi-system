theory PhiSem_Machine_Integer
  imports PhiSem_Common_Int PhiSem_Generic_Boolean
          "Word_Lib.More_Word" (*We use the word lib from seL4*)
          "Word_Lib.Signed_Division_Word"
          "Word_Lib.Word_Lemmas"
begin

chapter \<open>Semantics for Machine Integers\<close>

section \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype \<phi>machine_int_ty =
  T_int     :: nat \<comment> \<open>in unit of bits\<close>

debt_axiomatization T_int :: \<open>nat type_entry\<close>
  where \<phi>machine_int_ty_ax: \<open>\<phi>machine_int_ty TY_CONS_OF T_int\<close>

interpretation \<phi>machine_int_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_int using \<phi>machine_int_ty_ax .

hide_fact \<phi>machine_int_ty_ax \<phi>machine_int_ty_axioms \<phi>machine_int_ty_names_def \<phi>machine_int_ty_def
  \<phi>machine_int_ty_prjs_axioms \<phi>machine_int_ty_prjs_def \<phi>machine_int_ty.axioms \<phi>machine_int_ty.intro
  \<phi>machine_int_ty__names.\<phi>machine_int_ty_names_axioms \<phi>machine_int_ty_prjs.axioms

syntax "_int_semty_" :: \<open>type \<Rightarrow> TY\<close> ("int'(_')")

translations "int('b)" <= "CONST T_int.mk LENGTH('b)"

ML \<open>local open Ast in
  fun need_add_sort (Appl [Constant \<^syntax_const>\<open>_ofsort\<close>, Variable _, _]) = true
    | need_add_sort (Variable _) = true
    | need_add_sort _ = false
  fun add_sort X =
    if need_add_sort X
    then Appl [Constant \<^syntax_const>\<open>_ofsort\<close>, X, Constant \<^class_syntax>\<open>len\<close>]
    else X
end\<close>

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>_int_semty_\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>T_int.mk\<close>, Appl [Constant \<^syntax_const>\<open>_type_length\<close>, add_sort V]]))] end\<close>


subsubsection \<open>Value\<close>

virtual_datatype \<phi>machine_int_val =
  V_int     :: \<open>nat \<times> nat\<close> \<comment> \<open>bits \<times> value\<close>

debt_axiomatization V_int :: \<open>(nat \<times> nat) value_entry\<close>
  where \<phi>machine_int_val_ax: \<open>\<phi>machine_int_val VAL_CONS_OF V_int\<close>

interpretation \<phi>machine_int_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_int using \<phi>machine_int_val_ax .

hide_fact \<phi>machine_int_val_ax \<phi>machine_int_val_axioms

subsubsection \<open>Semantics\<close>

debt_axiomatization
    WT_int[simp]: \<open>Well_Type (T_int.mk b)     = { V_int.mk (b,x)    |x. x < 2 ^ b } \<close>
and can_eqcmp_int[simp]: "Can_EqCompare res (V_int.mk (b1,x1)) (V_int.mk (b2,x2)) \<longleftrightarrow> b1 = b2"
and eqcmp_int[simp]: "EqCompare (V_int.mk i1) (V_int.mk i2) \<longleftrightarrow> i1 = i2"
and  zero_int[simp]: \<open>Zero (T_int.mk b)    = Some (V_int.mk (b,0))\<close>

(*lemma Valid_Types[simp]:
  \<open>Valid_Type (T_int.mk n)\<close>
  unfolding Inhabited_def
  apply simp
  using less_exp by blast *)


section \<open>\<phi>-Types\<close>

text \<open>Thresholds between \<phi>-Types
\<^item> 9 \<open>Word \<longrightarrow> \<nat>\<^sup>r\<close>
\<^item> 9 \<open>Word \<longrightarrow> \<nat>\<close>
\<^item> 9 \<open>Word \<longrightarrow> \<int>\<close>
\<^item> 7 \<open>\<nat>\<^sup>r \<longrightarrow> Word\<close>
\<^item> 7 \<open>\<nat> \<longrightarrow> Word\<close>
\<^item> 7 \<open>\<int> \<longrightarrow> Word\<close>
\<^item> 6 \<open>\<int> \<longrightarrow> \<nat>\<close>
\<^item> 5 \<open>\<nat> \<longrightarrow> \<int>\<close>
\<^item> 4 \<open>\<nat>\<^sup>r \<longrightarrow> \<nat>\<close>
\<^item> 2 \<open>\<nat> \<longrightarrow> \<nat>\<^sup>r\<close>

There is no direct transformation between \<open>\<nat>\<^sup>r\<close> and \<open>\<int>\<close> because of complexity in the expression.

\<close>

subsection \<open>Words\<close>

definition Word :: \<open>'b itself \<Rightarrow> (VAL, 'b::len word) \<phi>\<close>
  where \<open>Word _ x = { V_int.mk (LENGTH('b), unat x) }\<close>

syntax Word_syntax :: "type \<Rightarrow> (VAL, 'b::len word) \<phi>" ("Word'(_')")

translations "Word('x)" <= "CONST Word TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>Word_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>Word\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>



lemma Word_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Word('b)) \<longleftrightarrow> p = V_int.mk (LENGTH('b), unat x)\<close>
  unfolding \<phi>Type_def Word_def by simp

lemma [elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> Word('b)) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> Word('b)) int('b)\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: Word_expn)

lemma [\<phi>reason 1000]:
  "\<phi>Equal Word('b) (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: word_unat_eq_iff Word_expn)

lemma [\<phi>reason 1000]:
  "\<phi>Zero int('b) Word('b) (0::'b::len word)"
  unfolding \<phi>Zero_def by (simp add: Word_expn image_iff)



subsection \<open>Natural Numbers\<close>

subsubsection \<open>Rounded Natural Number\<close>

definition \<phi>RoundedNat :: "'b::len itself \<Rightarrow> (VAL, nat) \<phi>"
  where [\<phi>defs]: "\<phi>RoundedNat _ x = ((of_nat x :: 'b word) \<Ztypecolon> Word('b))"

syntax \<phi>RoundedNat_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<nat>\<^sup>r'(_')")

translations "\<nat>\<^sup>r('x)" <= "CONST \<phi>RoundedNat TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>RoundedNat_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>RoundedNat\<close>,
                Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

lemma [
  \<phi>reason 1000 for \<open>?x \<Ztypecolon> \<nat>\<^sup>r(?'b1) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> _ \<a>\<n>\<d> _\<close>
]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x mod 2^LENGTH('b) = y mod 2^LENGTH('b)
\<Longrightarrow> x \<Ztypecolon> \<nat>\<^sup>r('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<nat>\<^sup>r('b)\<close>
  \<medium_left_bracket> destruct\<phi> _
    construct\<phi> \<open>y \<Ztypecolon> \<nat>\<^sup>r('b)\<close> 
    affirm by (simp add: the_\<phi> unat_of_nat word_unat_eq_iff)
  ;;
  \<medium_right_bracket>. 
  .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>\<^sup>r(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> Word(_) \<a>\<n>\<d> _\<close>]:
  \<open> Threshold_Cost 7
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = of_nat x
\<Longrightarrow> x \<Ztypecolon> \<nat>\<^sup>r('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Word('b)\<close>
  for y :: \<open>'b::len word\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [
  \<phi>reason 800 for \<open>_ \<Ztypecolon> \<phi>RoundedNat _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (Word _)\<close>,
  \<phi>inhabitance_rule
]:
  \<open>x \<Ztypecolon> \<nat>\<^sup>r('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (of_nat x :: 'b::len word) \<Ztypecolon> Word('b) @action to Word('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Word(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> \<nat>\<^sup>r(_) \<a>\<n>\<d> _\<close>]:
  \<open> Threshold_Cost 9
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y mod 2^LENGTH('b) = unat x
\<Longrightarrow> x \<Ztypecolon> Word('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<nat>\<^sup>r('b)\<close>
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> construct\<phi> \<open>unat x \<Ztypecolon> \<nat>\<^sup>r('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Word _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (\<phi>RoundedNat _)\<close>]:
  \<open> x \<Ztypecolon> Word('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> unat x \<Ztypecolon> \<nat>\<^sup>r('b) @action to \<nat>\<^sup>r('b)\<close>
  for x :: \<open>'b::len word\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>\<^sup>r('b)) int('b)\<close>
  \<medium_left_bracket> to \<open>Word _\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  \<open>\<phi>Zero int('b) \<nat>\<^sup>r('b) 0\<close>
  \<medium_left_bracket> \<open>0 \<Ztypecolon> Word('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  "\<phi>Equal (\<nat>\<^sup>r('b::len)) (\<lambda>x y. True) (\<lambda>x y. x mod 2^LENGTH('b) = y mod 2^LENGTH('b))"
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket>
    by (simp add: unat_of_nat word_unat_eq_iff) .


subsubsection \<open>Natural Number\<close>

definition \<phi>Nat :: "'b::len itself \<Rightarrow> (VAL, nat) \<phi>"
  where [\<phi>defs]: "\<phi>Nat _ x = (x \<Ztypecolon> \<nat>\<^sup>r('b) \<s>\<u>\<b>\<j> x \<in> {0..< 2 ^ LENGTH('b)})"

syntax \<phi>Nat_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<nat>'(_')")

translations "\<nat>('x)" <= "CONST \<phi>Nat TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>Nat_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>Nat\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> \<nat>\<^sup>r(_) \<a>\<n>\<d> _\<close>]:
  \<open> Threshold_Cost 2
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = x
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<nat>\<^sup>r('b) \<a>\<n>\<d> x < 2 ^ LENGTH('b)\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [
  \<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (\<phi>RoundedNat _)\<close>,
  \<phi>inhabitance_rule
]:
  \<open>x \<Ztypecolon> \<nat>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<nat>\<^sup>r('b) \<a>\<n>\<d> x < 2 ^ LENGTH('b) @action to \<nat>\<^sup>r('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .


lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>\<^sup>r(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (\<phi>Nat _)\<close>]:
  \<open> x \<Ztypecolon> \<nat>\<^sup>r('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x mod 2 ^ LENGTH('b) \<Ztypecolon> \<nat>('b) @action to \<nat>('b)\<close>
  \<medium_left_bracket> construct\<phi> \<open>x mod 2 ^ LENGTH('b) \<Ztypecolon> \<nat>('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>\<^sup>r(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> \<nat>(_) \<a>\<n>\<d> _ \<close>]:
  \<open> Threshold_Cost 4
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x mod 2 ^ LENGTH('b) = y
\<Longrightarrow> x \<Ztypecolon> \<nat>\<^sup>r('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<nat>('b) \<close>
  \<medium_left_bracket> to \<open>\<nat>(_)\<close> \<medium_right_bracket>. .


lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> Word(_) \<a>\<n>\<d> _\<close>]:
  \<open> Threshold_Cost 7
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = of_nat x
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Word('b) \<a>\<n>\<d> x < 2 ^ LENGTH('b)\<close>
  for y :: \<open>'b::len word\<close>
  \<medium_left_bracket> to \<open>\<nat>\<^sup>r(_)\<close> \<medium_right_bracket>. .

lemma [
  \<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (Word _)\<close>,
  \<phi>inhabitance_rule
]:
  \<open>x \<Ztypecolon> \<nat>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (of_nat x :: 'b::len word) \<Ztypecolon> Word('b) \<a>\<n>\<d> x < 2 ^ LENGTH('b)
   @action to Word('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .


lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Word(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> \<nat>(_) \<a>\<n>\<d> _\<close>]:
  \<open> Threshold_Cost 9
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = unat x
\<Longrightarrow> x \<Ztypecolon> Word('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<nat>('b)\<close>
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> to \<open>\<nat>\<^sup>r('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Word _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (\<phi>Nat _)\<close>]:
  \<open> x \<Ztypecolon> Word('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> unat x \<Ztypecolon> \<nat>('b) @action to \<nat>('b)\<close>
  for x :: \<open>'b::len word\<close> \<medium_left_bracket> \<medium_right_bracket>. .



lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>('b)) int('b)\<close>
  \<medium_left_bracket> to \<open>Word _\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  \<open>\<phi>Zero int('b) \<nat>('b) 0\<close>
  \<medium_left_bracket> \<open>0 \<Ztypecolon> Word('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  "\<phi>Equal (\<nat>('b::len)) (\<lambda>x y. True) (=)"
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket> using \<phi>lemmata of_nat_inverse by blast .


subsection \<open>Integer\<close>

definition \<phi>Int :: "'b::len itself \<Rightarrow> (VAL, int) \<phi>"
  where [\<phi>defs]: "\<phi>Int _ x = ((of_int x :: 'b word) \<Ztypecolon> Word('b)
                              \<s>\<u>\<b>\<j> x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)})"

syntax \<phi>Int_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<int>'(_')")

translations "\<int>('x)" == "CONST \<phi>Int TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>Int_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>Int\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> Word(_) \<a>\<n>\<d> _\<close>]:
  " Threshold_Cost 7
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = of_int x
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Word('b) \<a>\<n>\<d> x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)}"
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [
  \<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to Word(_)\<close>,
  \<phi>inhabitance_rule
]:
  \<open>x \<Ztypecolon> \<int>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (of_int x :: 'b::len word) \<Ztypecolon> Word('b) \<a>\<n>\<d> x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)}
   @action to Word('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>?x \<Ztypecolon> Word(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> \<int>(_) \<a>\<n>\<d> _\<close>]:
  " Threshold_Cost 9
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = sint x
\<Longrightarrow> x \<Ztypecolon> Word('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<int>('b)"
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> construct\<phi> \<open>y \<Ztypecolon> \<int>('b)\<close>
    affirm apply (simp add: \<open>y = sint x\<close>) using sint_greater_eq sint_less by blast
  \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> Word(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (Word _)\<close>]:
  \<open> x \<Ztypecolon> Word('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> sint x \<Ztypecolon> \<int>('b) @action to Word('b) \<close>
  \<medium_left_bracket> \<medium_right_bracket>. .
 
lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (\<phi>Nat _)\<close>]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> x \<and> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> nat x \<Ztypecolon> \<nat>('b) @action to \<nat>('b)\<close>
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket>
    by (smt (verit, best) \<open>0 \<le> x \<and> x < 2 ^ (LENGTH('b) - 1)\<close> sint_of_int_eq unat_eq_nat_uint word_arith_wis(7) word_of_int_2p_len word_of_int_inverse zero_less_power) .
  

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> \<nat>(_) \<a>\<n>\<d> _\<close>]:
  \<open> Threshold_Cost 6
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> x \<and> x < 2 ^ (LENGTH('b)-1) \<and> y = nat x
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<nat>('b)\<close>
  \<medium_left_bracket> to \<open>\<nat>('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to \<int>(_)\<close>]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> of_nat x \<Ztypecolon> \<int>('b) @action to \<int>(_) \<close>
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket> by (metis int_eq_sint the_\<phi>(2)) .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> \<int>(_) \<a>\<n>\<d> _ \<close>]:
  \<open> Threshold_Cost 5
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x < 2 ^ (LENGTH('b)-1) \<and> y = of_nat x
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<int>('b) \<close>
  \<medium_left_bracket> to \<open>\<int>(_)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<int>('b)) int('b)\<close> \<medium_left_bracket> to \<open>Word(_)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  "\<phi>Zero int('b) \<int>('b) 0" \<medium_left_bracket> \<open>0 \<Ztypecolon> Word('b)\<close> \<medium_right_bracket>. .


lemma [\<phi>reason 1000]:
  "\<phi>Equal \<int>('b) (\<lambda>x y. True) (=)"
  \<medium_left_bracket> to \<open>Word(_)\<close> \<medium_right_bracket>
  by (metis One_nat_def atLeastLessThan_iff the_\<phi>lemmata signed_take_bit_int_eq_self_iff sint_sbintrunc') .



section \<open>Instructions\<close>

definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> VAL proc"
  where "op_const_int bits const = Return (\<phi>arg (V_int.mk (bits,const)))"

(* definition op_const_size_t :: "nat \<Rightarrow> (VAL,VAL,'RES_N,'RES) proc"
  where "op_const_size_t c = \<phi>M_assume (c < 2 ^ addrspace_bits)
                          \<ggreater> Return (\<phi>arg (V_int.mk (addrspace_bits,c)))"
  \<comment> \<open> `op_const_size_t` checks the overflow during the compilation towards certain decided platform.  \<close>
*)

definition op_add :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_add bits =
      \<phi>M_caseV (\<lambda>vb va.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      Return (\<phi>arg (V_int.mk (bits, ((val_a + val_b) mod 2^bits))))
  )))"

definition op_sub :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_sub bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_int.mk (bits, ((2^bits + val_b - val_a) mod 2^bits))))
  )))"

definition op_umul :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_umul bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_int.mk (bits, ((val_b * val_a) mod 2^bits))))
  )))"

definition op_udiv :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_udiv bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      \<phi>M_assert (val_a \<noteq> 0) \<ggreater>
      Return (\<phi>arg (V_int.mk (bits, (val_b div val_a))))
  )))"

definition op_sdiv :: "'b::len itself \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_sdiv _ =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) va (\<lambda>val_a::'b word.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) vb (\<lambda>val_b::'b word.
      \<phi>M_assert (val_a \<noteq> 0) \<ggreater>
      Return (\<phi>arg (V_int.mk (LENGTH('b), unat (val_b sdiv val_a))))
  )))"

definition op_umod :: "'b::len itself \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_umod _ =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) va (\<lambda>val_a::'b word.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) vb (\<lambda>val_b::'b word.
      \<phi>M_assert (val_a \<noteq> 0) \<ggreater>
      Return (\<phi>arg (V_int.mk (LENGTH('b), unat (val_b mod val_a))))
  )))"

definition op_smod :: "'b::len itself \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_smod _ =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) va (\<lambda>val_a::'b word.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) vb (\<lambda>val_b::'b word.
      \<phi>M_assert (val_a \<noteq> 0) \<ggreater>
      Return (\<phi>arg (V_int.mk (LENGTH('b), unat (val_b smod val_a))))
  )))"

definition op_lshr :: "nat \<Rightarrow> nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_lshr b_b b_a =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk b_a) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk b_b) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_int.mk (b_b, (val_b div 2 ^ val_a))))
  )))"

definition op_lshl :: "nat \<Rightarrow> nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_lshl b_b b_a =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk b_a) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk b_b) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_int.mk (b_b, (val_b * 2 ^ val_a mod 2^b_b))))
  )))"

definition op_ult :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_ult bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b < val_a)))
  )))"

definition op_ule :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_ule bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b \<le> val_a)))
  )))"

definition op_slt :: "'b::len itself \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_slt _ =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) va (\<lambda>val_a::'b word.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b <s val_a)))
  )))"

definition op_sle :: "'b::len itself \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_sle _ =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) va (\<lambda>val_a::'b word.
      \<phi>M_getV (T_int.mk LENGTH('b)) (of_nat o snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b \<le>s val_a)))
  )))"


definition op_cast_uint :: \<open>'b1::len itself \<Rightarrow> 'b2::len itself \<Rightarrow> (VAL, VAL) proc'\<close>
  where \<open>op_cast_uint _ _ va =
    \<phi>M_getV (T_int.mk LENGTH('b1)) (of_nat o snd o V_int.dest) va (\<lambda>val::'b1 word.
    Return (\<phi>arg (V_int.mk (LENGTH('b2), unat (Word.cast val :: 'b2 word)))))\<close>

definition op_cast_int :: \<open>'b1::len itself \<Rightarrow> 'b2::len itself \<Rightarrow> (VAL, VAL) proc'\<close>
  where \<open>op_cast_int _ _ va =
    \<phi>M_getV (T_int.mk LENGTH('b1)) (of_nat o snd o V_int.dest) va (\<lambda>val::'b1 word.
    Return (\<phi>arg (V_int.mk (LENGTH('b2), unat (Word.scast val :: 'b2 word)))))\<close>


section \<open>Abstraction of Instructions\<close>

subsection \<open>Arithmetic Operations\<close>

subsubsection \<open>Constant Integer\<close>

lemma op_const_word_\<phi>app[\<phi>synthesis 300]:
  \<open> Simplify literal n (unat n')
\<Longrightarrow> \<p>\<r>\<o>\<c> op_const_int LENGTH('b) n \<lbrace> Void \<longmapsto> \<v>\<a>\<l> n' \<Ztypecolon> Word('b) \<rbrace> \<close>
  unfolding op_const_int_def Premise_def Simplify_def
  by (rule, simp add: \<phi>expns)

lemma op_const_nat_\<phi>app[\<phi>synthesis 200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n < 2 ^ LENGTH('b)
\<Longrightarrow> Simplify literal n' n
\<Longrightarrow> \<p>\<r>\<o>\<c> op_const_int LENGTH('b::len) n' \<lbrace> Void \<longmapsto> \<v>\<a>\<l> n \<Ztypecolon> \<nat>('b) \<rbrace> \<close>
  \<medium_left_bracket> have [simp]: \<open>unat (word_of_nat n :: 'b word) = n\<close> using \<phi> of_nat_inverse by blast
  ;; op_const_word_\<phi>app[where 'b='b and n'=\<open>of_nat n\<close> and n=n']
    affirm by (simp add: \<open>n' = n\<close>)
  \<medium_right_bracket> by simp .

lemma op_const_natR_\<phi>app[\<phi>synthesis 120]:
  \<open> Simplify literal n' (n mod 2 ^ LENGTH('b))
\<Longrightarrow> \<p>\<r>\<o>\<c> op_const_int LENGTH('b::len) n' \<lbrace> Void \<longmapsto> \<v>\<a>\<l> n \<Ztypecolon> \<nat>\<^sup>r('b) \<rbrace> \<close>
  \<medium_left_bracket> op_const_word[where 'b='b and n=n' and n' = \<open>of_nat n\<close>, simplified]
    affirm by (simp add: the_\<phi>(1) unat_of_nat)
  \<medium_right_bracket> by (simp add: unat_of_nat) .

lemma [\<phi>reason 50
    for \<open>Synthesis_Parse (numeral ?n::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (1::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (0::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<nat>(32)) X
\<Longrightarrow> Synthesis_Parse n X\<close>
  for X :: \<open>'ret \<Rightarrow> assn\<close>
  unfolding Synthesis_Parse_def ..


(* lemma op_const_size_t:
  \<open>\<p>\<r>\<o>\<c> op_const_size_t n \<lbrace> Void \<longmapsto> \<v>\<a>\<l> n \<Ztypecolon> Size \<rbrace>\<close>
  unfolding op_const_size_t_def Premise_def
  by (\<phi>reason, simp add: \<phi>expns Big_def) *)


(* lemma [\<phi>reason 1200
    for \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<v>\<a>\<l> (numeral ?n) \<Ztypecolon> Size \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action synthesis ?G\<close>
       \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<v>\<a>\<l> 0 \<Ztypecolon> Size \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action synthesis ?G\<close>
       \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<v>\<a>\<l> 1 \<Ztypecolon> Size \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action synthesis ?G\<close>
]:
  \<open>\<p>\<r>\<o>\<c> op_const_size_t n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<v>\<a>\<l> n \<Ztypecolon> Size \<rbrace> @action synthesis G\<close>
  unfolding Synthesis_def Action_Tag_def
  using op_const_size_t[THEN \<phi>frame, simplified] . *)


subsubsection \<open>Addition\<close>

lemma op_add_word_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_add LENGTH('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_add_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns unat_word_ariths)

lemma op_add_nat_\<phi>app[\<phi>overload add,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x + y < 2 ^ LENGTH('b)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<nat>('b) \<rbrace> \<close>
  \<medium_left_bracket> op_add_word[where 'b='b] \<medium_right_bracket> using \<phi> by (metis of_nat_add of_nat_inverse) .

lemma op_add_natR_\<phi>app[\<phi>overload add,
                       \<phi>synthesis for _ (100)
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<nat>\<^sup>r('b) \<rbrace> \<close>
  \<medium_left_bracket> op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis of_nat_add unat_of_nat) .

lemma op_add_int_\<phi>app[\<phi>overload add,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<p>\<r>\<o>\<c> op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> op_add_word[where 'b='b] \<medium_right_bracket>
    using sint_of_int_eq that(1) by fastforce .
 
declare op_add_word_\<phi>app[\<phi>overload add]


subsubsection \<open>Subtraction\<close>

lemma op_sub_word_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_sub_def Premise_def
  apply (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)
  by (metis (no_types, opaque_lifting) Nat.add_diff_assoc2 add.commute add_0 mod_add_self2 unat_of_nat unat_sub_if' unsigned_0 word_arith_nat_add)

lemma op_sub_nat_\<phi>app[\<phi>overload sub,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<le> x
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_sub_word[where 'b='b] \<medium_right_bracket>
    by (metis diff_le_self le_unat_uoi of_nat_diff the_\<phi>(3) the_\<phi>lemmata(2) unat_of_nat_eq) .

lemma op_sub_natR_\<phi>app[\<phi>overload sub,
                       \<phi>synthesis for _ (100)
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<le> x
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<nat>\<^sup>r('b) \<rbrace>\<close>
  \<medium_left_bracket> op_sub_word[where 'b='b] \<medium_right_bracket>
    by (metis of_nat_diff the_\<phi>(1) unat_of_nat) .

lemma op_sub_int_\<phi>app[\<phi>overload sub,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x - y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_sub_word[where 'b='b] \<medium_right_bracket>
    using sint_of_int_eq the_\<phi>(5) by fastforce .

declare op_sub_word_\<phi>app[\<phi>overload sub]


subsubsection \<open>Multiplication\<close>


lemma op_mul_word_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_umul_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns unat_word_ariths(2))

lemma op_mul_nat_\<phi>app[\<phi>overload mul,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * y < 2^LENGTH('b)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_mul_word[where 'b='b] \<medium_right_bracket>
    using the_\<phi>(3) unat_of_nat_eq by fastforce .

lemma op_mul_natR_\<phi>app[\<phi>overload mul,
                       \<phi>synthesis for _ (100)
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<nat>\<^sup>r('b) \<rbrace>\<close>
  \<medium_left_bracket> op_mul_word[where 'b='b] \<medium_right_bracket>
    by (metis of_nat_mult unat_of_nat) .

lemma op_mul_int_\<phi>app[\<phi>overload mul,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_mul_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff of_int_mult sint_of_int_eq the_\<phi>(5)) .

declare op_mul_word_\<phi>app[\<phi>overload mul]


subsubsection \<open>Division\<close>

lemma op_udiv_word_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_udiv LENGTH('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_udiv_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
      rule \<phi>M_assert, simp add: \<phi>expns unat_gt_0, rule, simp add: \<phi>expns unat_div)

lemma op_div_nat_\<phi>app[\<phi>overload div,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_udiv LENGTH('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_udiv_word_\<phi>app[where 'b='b]
    affirm using More_Word.of_nat_0 the_\<phi>(2) the_\<phi>(3) by blast
  \<medium_right_bracket> by (simp add: the_\<phi>lemmata(1) the_\<phi>lemmata(2) of_nat_inverse unat_div) .

declare op_udiv_word_\<phi>app[\<phi>overload div]


lemma op_sdiv_word_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x sdiv y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sdiv TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x sdiv y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_sdiv_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
        rule \<phi>M_assert, simp add: \<phi>expns unat_gt_0, rule, simp add: \<phi>expns)

lemma op_div_int_\<phi>app[\<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x sdiv y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<noteq> - (2 ^ (LENGTH('b) - 1)) \<and> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sdiv TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x sdiv y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_sdiv_word
    affirm using sint_of_int_eq the_\<phi>(3) the_\<phi>(4) the_\<phi>(5) by force \<medium_right_bracket>
    unfolding sdiv_word_def
  proof simp
    have [simp]: \<open>sint (word_of_int x::'b word) = x\<close>
      by (simp add: sint_of_int_eq the_\<phi>lemmata(3) the_\<phi>lemmata(4))
    have [simp]: \<open>sint (word_of_int y::'b word) = y\<close>
      by (simp add: sint_of_int_eq the_\<phi>(4) the_\<phi>lemmata(1))

    have t1: \<open>x < 2 ^ (LENGTH('b)-1)\<close>
      using One_nat_def the_\<phi>lemmata(4) by presburger
    have t2: \<open>- (2 ^ (LENGTH('b)-1)) < x\<close>
      using the_\<phi>(10) the_\<phi>lemmata(3) by fastforce
    have t3: \<open>\<bar>x\<bar> < 2 ^ (LENGTH('b)-1)\<close>
      using t1 t2 by linarith
    have t4: \<open>\<bar>x sdiv y\<bar> < 2 ^ (LENGTH('b)-1)\<close>
      unfolding signed_divide_int_def
      apply (cases \<open>x = 0\<close>) apply simp
      apply (cases \<open>y = 0\<close>) apply simp
      apply (simp add: abs_mult)
      by (smt (verit, best) One_nat_def int_div_less_self int_div_same_is_1 pos_imp_zdiv_neg_iff t3)
    show \<open>x sdiv y = sint (word_of_int (sint (word_of_int x::'b word) sdiv sint (word_of_int y::'b word))::'b word)\<close>
      apply simp
      by (smt (verit, del_insts) t4 sint_of_int_eq)
  qed .

lemma op_div_int_fail[\<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (1200)]:
  \<open> FAIL TEXT(\<open>About integers, there is no rule available for unsigned division\<close> (div)
              \<open>Please use the signed\<close> (sdiv)
              \<open>Note the C semantics is\<close> (sdiv) \<open>instead of\<close> (div)
              \<open>and they are different in negative numbers\<close>)
\<Longrightarrow> \<p>\<r>\<o>\<c> fail \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  by blast

subsubsection \<open>Modulo\<close>

lemma op_umod_word_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x mod y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umod TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x mod y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_umod_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
      rule \<phi>M_assert, simp add: \<phi>expns unat_gt_0, rule, simp add: \<phi>expns unat_div)

lemma op_mod_nat_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x mod y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umod TYPE('b) (\<phi>V_pair vy vx)
      \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x mod y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_umod_word
    affirm using More_Word.of_nat_0 the_\<phi>(2) the_\<phi>(3) by blast \<medium_right_bracket>
  by (simp add: of_nat_inverse the_\<phi>lemmata(1) the_\<phi>lemmata(2) unat_mod_distrib) .

lemma op_smod_word_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda> v. x smod y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_smod TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x smod y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_smod_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
      rule \<phi>M_assert, simp add: \<phi>expns unat_gt_0, rule, simp add: \<phi>expns unat_div)

lemma op_mod_int_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x smod y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_smod TYPE('b) (\<phi>V_pair vy vx)
      \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x smod y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket>  op_smod_word affirm using sint_of_int_eq the_\<phi>(3) the_\<phi>(4) the_\<phi>(5) by fastforce \<medium_right_bracket>
  by (metis One_nat_def sint_of_int_eq smod_word_def smod_word_max smod_word_min the_\<phi>(1) the_\<phi>(2) the_\<phi>(3) the_\<phi>(4)) .

lemma op_mod_int_fail[\<phi>synthesis 100]:
  \<open> FAIL TEXT(\<open>About integers, there is no rule available for unsigned modulo\<close> (mod)
              \<open>Please use the signed\<close> (smod)
              \<open>Note the C semantics is\<close> (smod) \<open>instead of\<close> (mod)
              \<open>and they are different in negative numbers\<close>)
\<Longrightarrow> \<p>\<r>\<o>\<c> fail \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x mod y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  by blast


subsubsection \<open>Shift\<close>

paragraph \<open>Right Shift\<close>

lemma op_lshr_word_pre_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_lshr LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] Word('bb) \<longmapsto> \<v>\<a>\<l> drop_bit (unat y) x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  unfolding op_lshr_def
  apply (cases v1; cases v2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)
  by (metis drop_bit_eq_div unat_drop_bit_eq)

lemma op_lshr_word_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. drop_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_lshr LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> drop_bit y x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  \<medium_left_bracket> op_lshr_word_pre_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
    by (simp add: the_\<phi>(1) unat_of_nat) .

lemma op_lshr_nat_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. drop_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_lshr LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> drop_bit y x \<Ztypecolon> \<nat>('ba) \<rbrace>\<close>
  \<medium_left_bracket> op_lshr_word_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
    by (simp add: the_\<phi>(1) of_nat_inverse unat_drop_bit_eq) .


lemma drop_bit_nat_le:
  \<open>drop_bit n x \<le> x\<close> for x :: nat
  using div_le_dividend drop_bit_nat_def by presburger

lemma op_lshr_int_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. drop_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> x
\<Longrightarrow> \<p>\<r>\<o>\<c> op_lshr LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] \<int>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> drop_bit y x \<Ztypecolon> \<int>('ba) \<rbrace>\<close>
  \<medium_left_bracket>
  ;; $v1
  have t1: \<open>x < 2 ^ (LENGTH('ba) - 1)\<close>
    using One_nat_def the_\<phi>(2) by presburger
  have t2: \<open>nat x < 2 ^ (LENGTH('ba) - 1)\<close>
    using t1 by fastforce

  ;; $v1 $v2 op_lshr_nat_\<phi>app[where 'ba='ba and 'bb='bb]
  \<medium_right_bracket>
  apply rule+ using t2 drop_bit_nat_le order.strict_trans1 apply blast
  apply (simp add: of_nat_drop_bit the_\<phi>(2)) .. .

paragraph \<open>Left Shift\<close>

lemma op_lshl_word_pre_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] Word('bb) \<longmapsto> \<v>\<a>\<l> push_bit (unat y) x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  unfolding op_lshl_def
  apply (cases v1; cases v2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)
  by (simp add: push_bit_nat_def take_bit_nat_def unsigned_push_bit_eq)

lemma op_lshl_word_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> push_bit y x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  \<medium_left_bracket> op_lshl_word_pre_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
    by (simp add: of_nat_inverse the_\<phi>(1)) .

lemma op_lshl_nat_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * 2 ^ y < LENGTH('ba)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> push_bit y x \<Ztypecolon> \<nat>('ba) \<rbrace>\<close>
  \<medium_left_bracket> op_lshl_word_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
  unfolding push_bit_nat_def
  by (metis Abs_fnat_hom_mult le_eq_less_or_eq le_less_trans n_less_equal_power_2 of_nat_inverse the_\<phi>(2) word_eqI_folds(1) word_unat_power) .

lemma op_lshl_natR_\<phi>app
  [\<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * 2 ^ y < LENGTH('ba)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] \<nat>\<^sup>r('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> push_bit y x \<Ztypecolon> \<nat>\<^sup>r('ba) \<rbrace>\<close>
  \<medium_left_bracket> op_lshl_word_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
  unfolding push_bit_nat_def
  by (metis push_bit_nat_def push_bit_of_nat unat_of_nat) .


subsubsection \<open>Comparison\<close>

paragraph \<open>Unsigned Less Than\<close>

lemma op_lt_word_\<phi>app
  [\<phi>overload less, \<phi>synthesis for _ (100)
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_ult LENGTH('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_ult_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns word_less_nat_alt)

lemma op_lt_nat_\<phi>app
  [\<phi>overload less, \<phi>synthesis for _ (100)
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_ult LENGTH('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_lt_word[where 'b='b] \<medium_right_bracket>
    by (simp add: of_nat_inverse the_\<phi>lemmata(1) the_\<phi>lemmata(2) word_less_nat_alt) .

paragraph \<open>Signed Less Than\<close>

lemma op_slt_word_\<phi>app
  [\<phi>overload less, \<phi>synthesis for _ (100)
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x <s y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_slt TYPE('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x <s y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_slt_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_slt_int_\<phi>app
  [\<phi>overload less, \<phi>synthesis for _ (100)
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_slt TYPE('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_slt_word[where 'b='b] \<medium_right_bracket>
    by (simp add: sint_of_int_eq the_\<phi>(1) the_\<phi>lemmata(1) the_\<phi>lemmata(2) the_\<phi>lemmata(3) word_sless_alt) .


paragraph \<open>Unsigned Less Equal\<close>

lemma op_le_word_\<phi>app
  [\<phi>overload less_equal, \<phi>synthesis for _ (100)
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_ule LENGTH('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] Word('b) \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_ule_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns word_le_nat_alt)

lemma op_le_nat_\<phi>app
  [\<phi>overload less_equal, \<phi>synthesis for _ (100)
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_ule LENGTH('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_le_word \<medium_right_bracket>
    by (simp add: the_\<phi>lemmata(1) the_\<phi>lemmata(2) unat_of_nat word_le_nat_alt) .

paragraph \<open>Signed Less Equal\<close>

lemma op_sle_word_\<phi>app
  [\<phi>overload less_equal, \<phi>synthesis for _ (100)
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le>s y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_sle TYPE('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] Word('b) \<longmapsto> \<v>\<a>\<l> x \<le>s y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_sle_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns word_le_nat_alt)

lemma op_le_int_\<phi>app
  [\<phi>overload less_equal, \<phi>synthesis for _ (100)
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_sle TYPE('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_sle_word \<medium_right_bracket>
    by (simp add: sint_of_int_eq the_\<phi>lemmata(1) the_\<phi>lemmata(2) the_\<phi>lemmata(3) the_\<phi>lemmata(4) word_sle_eq) .

subsubsection \<open>Cast\<close>

lemma op_cast_uint_word_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_uint TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] Word('ba) \<longmapsto> Word.cast x \<Ztypecolon> \<v>\<a>\<l> Word('bb) \<rbrace>\<close>
  unfolding op_cast_uint_def
  by (cases v, simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_cast_nat_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_uint TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('ba) \<longmapsto> take_bit LENGTH('bb) x \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb) \<rbrace>\<close>
  \<medium_left_bracket> op_cast_uint_word[where 'bb='bb] \<medium_right_bracket>
    by (simp add: of_nat_inverse the_\<phi>lemmata unsigned_ucast_eq) .

lemma op_cast_int_word_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_int TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] Word('ba) \<longmapsto> Word.scast x \<Ztypecolon> \<v>\<a>\<l> Word('bb) \<rbrace>\<close>
  unfolding op_cast_int_def
  by (cases v, simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_cast_int_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_int TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<int>('ba) \<longmapsto> signed_take_bit (LENGTH('bb)-1) x \<Ztypecolon> \<v>\<a>\<l> \<int>('bb) \<rbrace>\<close>
  \<medium_left_bracket> op_cast_int_word[where 'bb='bb] \<medium_right_bracket>
    by (metis One_nat_def atLeastLessThan_iff signed_scast_eq signed_take_bit_int_eq_self sint_sbintrunc' the_\<phi>lemmata) .

lemma op_upcast_nat_\<phi>app:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> LENGTH('ba) \<le> LENGTH('bb)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_cast_uint TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('ba) \<longmapsto> x \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb) \<rbrace>\<close>
  \<medium_left_bracket> have [useful]: \<open>x < 2 ^ LENGTH('ba)\<close> using \<phi> by blast
  ;; $v op_cast_nat[where 'bb='bb] \<medium_right_bracket>
    by (metis min_def order_antisym_conv take_bit_nat_eq_self_iff take_bit_take_bit the_\<phi>(1) the_\<phi>(2)) .

lemma op_upcast_int_\<phi>app:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> LENGTH('ba) \<le> LENGTH('bb)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_cast_int TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<int>('ba) \<longmapsto> x \<Ztypecolon> \<v>\<a>\<l> \<int>('bb) \<rbrace>\<close>
  \<medium_left_bracket> op_cast_int_word[where 'bb='bb] \<medium_right_bracket>
  proof simp
    have t1: \<open>is_up (Word.scast :: 'ba word \<Rightarrow> 'bb word)\<close>
      using is_up that(1) by blast
    show \<open>x = sint (Word.scast (word_of_int x :: 'ba word) :: 'bb word)\<close>
      by (simp add: signed_take_bit_int_eq_self sint_sbintrunc' sint_up_scast t1 the_\<phi>lemmata(1) the_\<phi>lemmata(2))
  qed .


end