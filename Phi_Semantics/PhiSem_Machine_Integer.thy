theory PhiSem_Machine_Integer
  imports PhiSem_Common_Int
          "Word_Lib.More_Word" (*We use the word lib from seL4*)
          "Word_Lib.Signed_Division_Word"
          "Word_Lib.Word_Lemmas"
  abbrevs "<int>" = "\<i>\<n>\<t>"
begin

chapter \<open>Semantics for Machine Integers\<close>

setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put
                                  (SOME Generic_Variable_Access.store_value_no_clean))\<close>

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
       "_int_semty_" :: \<open>type \<Rightarrow> TY\<close> ("\<i>\<n>\<t>'(_')")


definition \<open>mk_int_T = T_int.mk o len0_class.len_of\<close>

(*translations "int('b)" => "CONST mk_int_T (CONST Pure.type :: 'b itself)" *)

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
          Appl [Constant \<^const_syntax>\<open>mk_int_T\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

print_translation \<open>
  let
    fun len_of_itself_tr' ctxt [Const (\<^const_syntax>\<open>Pure.type\<close>, Type (_, [T]))] =
      Syntax.const \<^syntax_const>\<open>_int_semty_\<close> $ Syntax_Phases.term_of_typ ctxt T
  in [(\<^const_syntax>\<open>mk_int_T\<close>, len_of_itself_tr')] end
\<close>

syntax BITS_syntax :: "type \<Rightarrow> logic" ("BITS'(_')")

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>BITS_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]))] end\<close>

(* term \<open>int(32)\<close> *)

typedecl \<i>\<n>\<t> \<comment> \<open>size of address space\<close>

consts \<i>\<n>\<t>_bits :: "nat" \<comment> \<open>bit width of address space, in unit of bits\<close>
specification (\<i>\<n>\<t>_bits) \<i>\<n>\<t>_bits_L0: "0 < \<i>\<n>\<t>_bits" by blast
  \<comment> \<open>We leave it unspecified and only require it is positive\<close>


instantiation \<i>\<n>\<t> :: len begin
definition "len_of_\<i>\<n>\<t> (_::\<i>\<n>\<t> itself) = \<i>\<n>\<t>_bits"
instance by (standard, simp add: \<i>\<n>\<t>_bits_L0 len_of_\<i>\<n>\<t>_def)
end

abbreviation \<open>\<i>\<n>\<t> \<equiv> \<i>\<n>\<t>(\<i>\<n>\<t>)\<close>


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
and \<phi>Sem_machine_int_to_logic_nat[simp]: \<open>\<phi>Sem_int_to_logic_nat (V_int.mk (b,x)) = Some (of_nat x)\<close>
and \<phi>Sem_machine_int_to_logic_int[simp]:
      \<open>\<phi>Sem_int_to_logic_int (V_int.mk (b,x)) = Some (if x < 2^(b - 1) then of_nat x
                                                      else - of_nat (2^b - x))\<close>

lemma [\<phi>reason %logical_spec_of_semantics]:
  \<open>get_logical_int_from_semantic_int (V_int.mk (b,x) \<Ztypecolon> Itself) (if x < 2^(b - 1) then of_nat x else - of_nat (2^b - x))\<close>
  unfolding get_logical_int_from_semantic_int_def
  by simp

lemma [\<phi>reason %logical_spec_of_semantics]:
  \<open>get_logical_nat_from_semantic_int (V_int.mk (b,x) \<Ztypecolon> Itself) x\<close>
  unfolding get_logical_nat_from_semantic_int_def
  by simp


(*lemma Valid_Types[simp]:
  \<open>Valid_Type (T_int.mk n)\<close>
  unfolding Inhabited_def
  apply simp
  using less_exp by blast *)


section \<open>\<phi>-Types\<close>

text \<open>Thresholds between \<phi>-Types
\<^item> 9 \<open>Word \<longrightarrow> \<int>\<^sup>r\<close>
\<^item> 9 \<open>Word \<longrightarrow> \<nat>\<close>
\<^item> 9 \<open>Word \<longrightarrow> \<int>\<close>
\<^item> 7 \<open>\<int>\<^sup>r \<longrightarrow> Word\<close>
\<^item> 7 \<open>\<nat> \<longrightarrow> Word\<close>
\<^item> 7 \<open>\<int> \<longrightarrow> Word\<close>
\<^item> 6 \<open>\<int> \<longrightarrow> \<nat>\<close>
\<^item> 5 \<open>\<nat> \<longrightarrow> \<int>\<close>
\<^item> 4 \<open>\<int>\<^sup>r \<longrightarrow> \<nat>\<close>
\<^item> 2 \<open>\<nat> \<longrightarrow> \<nat>\<^sup>r\<close>

There is no direct transformation between \<open>\<nat>\<^sup>r\<close> and \<open>\<int>\<close> because of complexity in the expression.

\<close>

subsection \<open>Words\<close>

\<phi>type_def Word :: \<open>'b itself \<Rightarrow> (VAL, 'b::len word) \<phi>\<close>
  where \<open>x \<Ztypecolon> Word _ \<equiv> V_int.mk (LENGTH('b), unat x) \<Ztypecolon> Itself\<close>
  deriving Basic
       and \<open>Object_Equiv (Word ?uu) (=)\<close>
       and \<open>\<phi>SemType (x \<Ztypecolon> Word TYPE('b)) int('b)\<close>
       and \<open>Semantic_Zero_Val int('b) (Word ?uu) (0::'b::len word)\<close>

syntax Word_syntax :: "type \<Rightarrow> (VAL, 'b::len word) \<phi>" ("Word'(_')")

translations "Word('x)" <= "CONST Word TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>Word_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>Word\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

declare [[\<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (Word _)\<close> \<Rightarrow>
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (Word _)\<close>    (200)
  and \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Word _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow>
      \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Word _ \<w>\<i>\<t>\<h> _ \<close>    (200)]]

lemma [\<phi>reason 1000]:
  "\<phi>Equal Word('b) (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: word_unat_eq_iff)


subsection \<open>Natural Numbers\<close>

subsubsection \<open>Rounded Natural Number\<close>

\<phi>type_def \<phi>RoundedNat :: "'b::len itself \<Rightarrow> (VAL, nat) \<phi>"
  where \<open>x \<Ztypecolon> \<phi>RoundedNat _ \<equiv> ((of_nat x :: 'b word) \<Ztypecolon> Word('b))\<close>
  deriving Basic
       and \<open>Object_Equiv (\<phi>RoundedNat (TY::'b::len itself)) (\<lambda>x y. x mod 2^LENGTH('b) = y mod 2^LENGTH('b))\<close>
       and Semantic_Type
       and \<open>Semantic_Zero_Val int('b) (\<phi>RoundedNat TYPE('b)) 0\<close>


syntax \<phi>RoundedNat_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<nat>\<^sup>r'(_')")

translations "\<nat>\<^sup>r('x)" <= "CONST \<phi>RoundedNat TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>RoundedNat_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>RoundedNat\<close>,
                Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

declare [[\<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (\<phi>RoundedNat _)\<close> \<Rightarrow>
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (\<phi>RoundedNat _)\<close>    (200)
  and \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<phi>RoundedNat _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow>
      \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<phi>RoundedNat _ \<w>\<i>\<t>\<h> _ \<close>    (200) ]]


declare \<phi>RoundedNat.elim[condition \<open>Threshold_Cost 7\<close>,
                         \<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<nat>\<^sup>r(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Word(_) \<w>\<i>\<t>\<h> _\<close>]

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open>x \<Ztypecolon> \<nat>\<^sup>r('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Word('b) \<s>\<u>\<b>\<j> y. y = (of_nat x :: 'b::len word) @tag to Word('b)\<close>
  \<medium_left_bracket>  \<medium_right_bracket>.
 
lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> Threshold_Cost 9
\<Longrightarrow> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> unat x \<Ztypecolon> \<nat>\<^sup>r('b)\<close>
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> \<open>unat x \<Ztypecolon> MAKE _ (\<nat>\<^sup>r('b))\<close> \<medium_right_bracket> .

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> unat x \<Ztypecolon> \<nat>\<^sup>r('b) @tag to \<nat>\<^sup>r('b)\<close>
  for x :: \<open>'b::len word\<close> \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason 1000]:
  "\<phi>Equal (\<nat>\<^sup>r('b::len)) (\<lambda>x y. True) (\<lambda>x y. x mod 2^LENGTH('b) = y mod 2^LENGTH('b))"
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket>
      certified by (metis the_\<phi>lemmata unat_eq_of_nat unat_lt2p unat_of_nat)  .


subsubsection \<open>Natural Number\<close>

\<phi>type_def \<phi>Nat :: "'b::len itself \<Rightarrow> (VAL, nat) \<phi>"
  where \<open>x \<Ztypecolon> \<phi>Nat _ \<equiv> (x \<Ztypecolon> \<nat>\<^sup>r('b) \<s>\<u>\<b>\<j> x \<in> {0..< 2 ^ LENGTH('b)})\<close>
  deriving Basic
       and \<open>Object_Equiv (\<phi>Nat uu) (=)\<close>

syntax \<phi>Nat_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<nat>'(_')")

translations "\<nat>('x)" <= "CONST \<phi>Nat TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>Nat_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>Nat\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

declare [[\<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (\<phi>Nat _)\<close> \<Rightarrow>
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (\<phi>Nat _)\<close>    (200)
  and \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<phi>Nat _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow>
      \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<phi>Nat _ \<w>\<i>\<t>\<h> _ \<close>    (200) ]]

let_\<phi>type \<phi>Nat
  deriving Semantic_Type
       and \<open>Semantic_Zero_Val int('b) \<nat>('b) 0\<close>

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> Threshold_Cost 2
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<nat>\<^sup>r('b) \<w>\<i>\<t>\<h> x < 2 ^ LENGTH('b)\<close>
  \<medium_left_bracket> \<phi>Nat.elim \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open>x \<Ztypecolon> \<nat>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<nat>\<^sup>r('b) \<s>\<u>\<b>\<j> y. y = x \<and> x < 2 ^ LENGTH('b) @tag to \<nat>\<^sup>r('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> x \<Ztypecolon> \<nat>\<^sup>r('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<nat>('b) \<s>\<u>\<b>\<j> y. y = x mod 2 ^ LENGTH('b) @tag to \<nat>('b)\<close>
  \<medium_left_bracket> \<open>x mod 2 ^ LENGTH('b) \<Ztypecolon> MAKE _ (\<nat>('b))\<close> \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> Threshold_Cost 4
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x mod 2 ^ LENGTH('b) = y
\<Longrightarrow> x \<Ztypecolon> \<nat>\<^sup>r('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<nat>('b) \<close>
  \<medium_left_bracket> to \<open>\<nat>(_)\<close> \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> Threshold_Cost 7
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> of_nat x \<Ztypecolon> Word('b) \<w>\<i>\<t>\<h> x < 2 ^ LENGTH('b)\<close>
  for y :: \<open>'b::len word\<close>
  \<medium_left_bracket> to \<open>\<nat>\<^sup>r(_)\<close> \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open>x \<Ztypecolon> \<nat>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (of_nat x :: 'b::len word) \<Ztypecolon> Word('b) \<w>\<i>\<t>\<h> x < 2 ^ LENGTH('b) @tag to Word('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> Threshold_Cost 9
\<Longrightarrow> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> unat x \<Ztypecolon> \<nat>('b)\<close>
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> to \<open>\<nat>\<^sup>r('b)\<close> \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> unat x \<Ztypecolon> \<nat>('b) @tag to \<nat>('b)\<close>
  for x :: \<open>'b::len word\<close> \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason 1000]:
  "\<phi>Equal (\<nat>('b::len)) (\<lambda>x y. True) (=)"
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket> certified using \<phi>lemmata of_nat_inverse by blast .

lemma [\<phi>reason %logical_spec_of_semantics]:
  \<open>get_logical_int_from_semantic_int (n \<Ztypecolon> \<nat>('b::len))
        (if n < 2^(LENGTH('b) - 1) then of_nat n else - of_nat (2^LENGTH('b) - n))\<close>
  unfolding get_logical_int_from_semantic_int_def Ball_def
  by (clarsimp; metis uint_nat unat_of_nat_len)

lemma [\<phi>reason %logical_spec_of_semantics]:
  \<open>get_logical_nat_from_semantic_int (n \<Ztypecolon> \<nat>('b::len)) n\<close>
  unfolding get_logical_nat_from_semantic_int_def Ball_def
  by (clarsimp simp add: unat_of_nat_len)


subsection \<open>Integers\<close>

subsubsection \<open>Integer\<close>

\<phi>type_def \<phi>Int :: "'b::len itself \<Rightarrow> (VAL, int) \<phi>"
  where \<open>x \<Ztypecolon> \<phi>Int _ \<equiv> ((of_int x :: 'b word) \<Ztypecolon> Word('b)
                              \<s>\<u>\<b>\<j> x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)})\<close>
  deriving Basic
       and \<open>Object_Equiv (\<phi>Int uu) (=)\<close>
       and Semantic_Type

syntax \<phi>Int_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<int>'(_')")

translations "\<int>('x)" == "CONST \<phi>Int TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>Int_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>Int\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

let_\<phi>type \<phi>Int
  deriving \<open>Semantic_Zero_Val int('b) \<int>('b) 0\<close>

declare \<phi>Int.expansion[simp del, \<phi>expns del]

lemma \<phi>Int_expn[simp, \<phi>expns]:
  \<open>p \<Turnstile> (n \<Ztypecolon> \<int>('b)) \<longleftrightarrow> p = V_int.mk (LENGTH('b), (if 0 \<le> n then nat n else nat (2^LENGTH('b) + n)))
          \<and> n < 2 ^ (LENGTH('b) - 1) \<and> - (2 ^ (LENGTH('b) - 1)) \<le> n\<close>
  unfolding \<phi>Int.expansion
  by (auto,
      smt (verit) of_int_0 sint_ge sint_int_max_plus_1 sint_of_int_eq two_less_eq_exp_length unat_eq_nat_uint word_of_int_2p_len word_of_int_inverse,
      smt (verit, ccfv_SIG) diff_Suc_less len_gt_0 uint_power_lower unat_eq_nat_uint unsigned_less word_of_int_inverse,
      smt (verit, ccfv_SIG) More_Word.power_not_zero Word.of_nat_unat diff_Suc_less int_eq_iff len_gt_0 of_int_add power_increasing_iff power_overflow word_of_int_0 word_of_int_2p_len word_of_int_inverse,
      smt (verit, ccfv_SIG) diff_less le_less len_gt_0 lessI of_int_add power_increasing_iff unat_eq_nat_uint word_arith_wis(7) word_of_int_2p_len word_of_int_inverse)

hide_fact \<phi>Int.expansion

thm \<phi>Int.elim

lemma [\<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<int>(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Word(_) \<w>\<i>\<t>\<h> _\<close>]:
  " Threshold_Cost 7
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> of_int x \<Ztypecolon> Word('b) \<w>\<i>\<t>\<h> x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)}"
  \<medium_left_bracket> \<phi>Int.elim \<medium_right_bracket> .


lemma [
  \<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<int>(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to Word(_)\<close>
]:
  \<open>x \<Ztypecolon> \<int>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (of_int x :: 'b::len word) \<Ztypecolon> Word('b) \<w>\<i>\<t>\<h> x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)}
   @tag to Word('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket> .

lemma [\<phi>reason %ToA_num_conv for \<open>?x \<Ztypecolon> Word(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<int>(_) \<w>\<i>\<t>\<h> _\<close>]:
  " Threshold_Cost 9
\<Longrightarrow> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sint x \<Ztypecolon> \<int>('b)"
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> \<open>sint x \<Ztypecolon> MAKE _ (\<int>('b))\<close>
    certified using sint_greater_eq sint_less by blast
  \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> Word(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (Word _)\<close>]:
  \<open> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sint x \<Ztypecolon> \<int>('b) @tag to Word('b) \<close>
  \<medium_left_bracket> \<medium_right_bracket>.
 
lemma [\<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<int>(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (\<phi>Nat _)\<close>]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> x \<and> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> nat x \<Ztypecolon> \<nat>('b) @tag to \<nat>('b)\<close>
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket>
    certified by (smt (verit, best) \<open>0 \<le> x \<and> x < 2 ^ (LENGTH('b) - 1)\<close> sint_of_int_eq unat_eq_nat_uint word_arith_wis(7) word_of_int_2p_len word_of_int_inverse zero_less_power) .
  

lemma [\<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<int>(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<nat>(_) \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Threshold_Cost 6
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> x \<and> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> nat x \<Ztypecolon> \<nat>('b)\<close>
  \<medium_left_bracket> to \<open>\<nat>('b)\<close> \<medium_right_bracket>.

lemma [\<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<nat>(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to \<int>(_)\<close>]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> of_nat x \<Ztypecolon> \<int>('b) @tag to \<int>(_) \<close>
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket> certified by auto_sledgehammer .

lemma [\<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<nat>(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<int>(_) \<w>\<i>\<t>\<h> _ \<close>]:
  \<open> Threshold_Cost 5
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> of_nat x \<Ztypecolon> \<int>('b) \<close>
  \<medium_left_bracket> to \<open>\<int>(_)\<close> \<medium_right_bracket>.

lemma [\<phi>reason 1000]:
  "\<phi>Equal \<int>('b) (\<lambda>x y. True) (=)"
  \<medium_left_bracket> to \<open>Word(_)\<close> \<medium_right_bracket>
      certified by (metis One_nat_def atLeastLessThan_iff the_\<phi>lemmata signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>reason %logical_spec_of_semantics]:
  \<open>get_logical_int_from_semantic_int (n \<Ztypecolon> \<int>('b::len)) n\<close>
  unfolding get_logical_int_from_semantic_int_def Ball_def
  apply (auto simp add: One_nat_def[symmetric] not_le  simp del: One_nat_def)
  subgoal premises prems proof -
    have \<open>n < 2 ^ (LENGTH('b) - 1) - 2 ^ LENGTH('b)\<close>
      using prems(3) by force
    then have \<open>n < 2 ^ (LENGTH('b) - 1) - 2 * 2 ^ (LENGTH('b) - 1)\<close>
      by (metis One_nat_def decr_length_less_iff less_eq_Suc_le order.refl power.simps(2) verit_la_disequality)
    then show ?thesis
      by linarith
  qed
  by (simp add: int_ops(6),
      smt (verit, best) less_imp_diff_less power_strict_increasing_iff)

lemma [\<phi>reason %logical_spec_of_semantics]:
  \<open>get_logical_nat_from_semantic_int (n \<Ztypecolon> \<int>('b::len)) (if 0 \<le> n then nat n else nat (2^LENGTH('b) + n))\<close>
  unfolding get_logical_nat_from_semantic_int_def Ball_def
  by clarsimp

subsubsection \<open>Rounded Integers\<close>

subsubsection \<open>Rounded Natural Number\<close>

\<phi>type_def \<phi>RoundedInt :: "'b::len itself \<Rightarrow> (VAL, int) \<phi>"
  where \<open>x \<Ztypecolon> \<phi>RoundedInt _ \<equiv> ((of_int x :: 'b word) \<Ztypecolon> Word('b))\<close>
  deriving Basic
       and \<open>Object_Equiv (\<phi>RoundedInt (TY::'b::len itself)) (\<lambda>x y. x mod 2^LENGTH('b) = y mod 2^LENGTH('b))\<close>
       and Semantic_Type
       and \<open>Semantic_Zero_Val int('b) (\<phi>RoundedInt TYPE('b)) 0\<close>


syntax \<phi>RoundedInt_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<int>\<^sup>r'(_')")

translations "\<int>\<^sup>r('x)" <= "CONST \<phi>RoundedInt TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>RoundedInt_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>RoundedInt\<close>,
                Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

declare [[\<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (\<phi>RoundedInt _)\<close> \<Rightarrow>
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag to (\<phi>RoundedInt _)\<close>    (200)
  and \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<phi>RoundedInt _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow>
      \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<phi>RoundedInt _ \<w>\<i>\<t>\<h> _ \<close>    (200) ]]


declare \<phi>RoundedInt.elim[condition \<open>Threshold_Cost 7\<close>,
                         \<phi>reason %ToA_num_conv for \<open>_ \<Ztypecolon> \<int>\<^sup>r(_) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Word(_) \<w>\<i>\<t>\<h> _\<close>]

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open>x \<Ztypecolon> \<int>\<^sup>r('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Word('b) \<s>\<u>\<b>\<j> y. y = (of_int x :: 'b::len word) @tag to Word('b)\<close>
  \<medium_left_bracket>  \<medium_right_bracket>.
 
lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> Threshold_Cost 9
\<Longrightarrow> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uint x \<Ztypecolon> \<int>\<^sup>r('b)\<close>
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> \<open>uint x \<Ztypecolon> MAKE _ (\<int>\<^sup>r('b))\<close> \<medium_right_bracket> .

lemma [\<phi>reason %ToA_num_conv_cut]:
  \<open> x \<Ztypecolon> Word('b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uint x \<Ztypecolon> \<int>\<^sup>r('b) @tag to \<int>\<^sup>r('b)\<close>
  for x :: \<open>'b::len word\<close> \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason 1000]:
  "\<phi>Equal (\<int>\<^sup>r('b::len)) (\<lambda>x y. True) (\<lambda>x y. x mod 2^LENGTH('b) = y mod 2^LENGTH('b))"
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket>
      certified by (metis the_\<phi>lemmata uint_word_of_int word_of_int_uint)   .


section \<open>Instructions\<close>

(*
definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> VAL proc"
  where "op_const_int bits const = Return (\<phi>arg (V_int.mk (bits,const)))"
*)
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

lemma op_const_word_\<phi>app[\<phi>reason %\<phi>synthesis_literal_number]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode_literal] n : unat n'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> n' \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (V_int.mk (LENGTH('b),n))] Word('b) \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
\<medium_left_bracket>
  semantic_literal \<open>V_int.mk (LENGTH('b),n) \<Turnstile> (n' \<Ztypecolon> Word('b))\<close>
\<medium_right_bracket> .

lemma op_const_nat_\<phi>app[\<phi>reason %\<phi>synthesis_literal_number]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n < 2 ^ LENGTH('b)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode_literal] n' : n
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> n \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (V_int.mk (LENGTH('b),n'))] \<nat>('b) \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
\<medium_left_bracket>
  semantic_literal \<open>V_int.mk (LENGTH('b),n') \<Turnstile> (n \<Ztypecolon> \<nat>('b))\<close>
  certified by (simp add: \<phi> unat_of_nat_len)
\<medium_right_bracket> .

lemma op_const_natR_\<phi>app[\<phi>reason %\<phi>synthesis_literal_number]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode_literal] n' : n mod 2 ^ LENGTH('b)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> n \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (V_int.mk (LENGTH('b),n'))] \<nat>\<^sup>r('b) \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
\<medium_left_bracket>
  apply_rule op_const_word[where 'b='b and n=n' and n' = \<open>of_nat n\<close>, simplified, OF Simplify_to_Premise]
  certified by (simp add: the_\<phi>(2) unat_of_nat) 
\<medium_right_bracket> certified by (simp add: unat_of_nat) .

lemma op_const_int_\<phi>app[\<phi>reason %\<phi>synthesis_literal_number]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> - (2 ^ (LENGTH('b)-1)) \<le> n \<and> n < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode_literal] n' : (if 0 \<le> n then nat n else nat (2^LENGTH('b) + n))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> n \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (V_int.mk (LENGTH('b),n'))] \<int>('b) \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
\<medium_left_bracket>
  semantic_literal \<open>V_int.mk (LENGTH('b),n') \<Turnstile> (n \<Ztypecolon> \<int>('b))\<close>
  certified by (simp add: \<phi> unat_of_nat_len)
\<medium_right_bracket> .

lemma op_const_intR_\<phi>app[\<phi>reason %\<phi>synthesis_literal_number]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode_literal] n' : (let n = n mod 2 ^ LENGTH('b) in if 0 \<le> n then nat n else nat (2^LENGTH('b) + n))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> n \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (V_int.mk (LENGTH('b),n'))] \<int>\<^sup>r('b) \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
\<medium_left_bracket>
  apply_rule op_const_word[where 'b='b and n=n' and n' = \<open>of_int n\<close>, simplified, OF Simplify_to_Premise]
  certified by auto_sledgehammer
\<medium_right_bracket> certified by auto_sledgehammer .

lemma [\<phi>reason %\<phi>synthesis_parse_number
    for \<open>Synthesis_Parse (numeral ?n::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (1::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (0::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<nat>(\<i>\<n>\<t>)) X
\<Longrightarrow> Synthesis_Parse n X\<close>
  for X :: \<open>'ret \<Rightarrow> assn\<close>
  unfolding Synthesis_Parse_def ..


(* lemma op_const_size_t:
  \<open>\<p>\<r>\<o>\<c> op_const_size_t n \<lbrace> Void \<longmapsto> \<v>\<a>\<l> n \<Ztypecolon> Size \<rbrace>\<close>
  unfolding op_const_size_t_def Premise_def
  by (\<phi>reason, simp add: \<phi>expns Big_def) *)


(* lemma [\<phi>reason 1200
    for \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<v>\<a>\<l> (numeral ?n) \<Ztypecolon> Size \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @tag synthesis ?G\<close>
       \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<v>\<a>\<l> 0 \<Ztypecolon> Size \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @tag synthesis ?G\<close>
       \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<v>\<a>\<l> 1 \<Ztypecolon> Size \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @tag synthesis ?G\<close>
]:
  \<open>\<p>\<r>\<o>\<c> op_const_size_t n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<v>\<a>\<l> n \<Ztypecolon> Size \<rbrace> @tag synthesis G\<close>
  unfolding Synthesis_def Action_Tag_def
  using op_const_size_t[THEN \<phi>frame, simplified] . *)


subsubsection \<open>Addition\<close>
 
lemma op_add_word_\<phi>app[\<phi>synthesis %synthesis_arith for _
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_add LENGTH('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_add_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp add: Premise_def unat_word_ariths)

lemma op_add_nat_\<phi>app[\<phi>overload +,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x + y < 2 ^ LENGTH('b)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<nat>('b) \<rbrace> \<close>
  \<medium_left_bracket> apply_rule op_add_word[where 'b='b] \<medium_right_bracket>
      certified using \<phi> by (metis of_nat_add of_nat_inverse) .

lemma op_add_natR_\<phi>app[\<phi>overload +,
                       \<phi>synthesis %synthesis_arith for _
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<nat>\<^sup>r('b) \<rbrace> \<close>
  \<medium_left_bracket> apply_rule op_add_word[where 'b='b] \<medium_right_bracket>
      certified by (metis of_nat_add unat_of_nat) .

lemma op_add_int_\<phi>app[\<phi>overload +,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<p>\<r>\<o>\<c> op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> apply_rule op_add_word[where 'b='b] \<medium_right_bracket>
      certified by auto_sledgehammer .
 
lemma op_add_intR_\<phi>app[\<phi>overload +,
                       \<phi>synthesis %synthesis_arith for _
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<int>\<^sup>r('b) \<rbrace> \<close>
  \<medium_left_bracket> apply_rule op_add_word[where 'b='b] \<medium_right_bracket>
      certified by (metis of_int_add uint_word_of_int)  .

declare op_add_word_\<phi>app[\<phi>overload +]


subsubsection \<open>Subtraction\<close>

lemma op_sub_word_\<phi>app[\<phi>synthesis %synthesis_arith for _
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_sub_def Premise_def
  apply (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)
  by (metis (no_types, opaque_lifting) Nat.add_diff_assoc2 add.commute add_0 mod_add_self2 unat_of_nat unat_sub_if' unsigned_0 word_arith_nat_add)

lemma op_sub_nat_\<phi>app[\<phi>overload -,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<le> x
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_sub_word[where 'b='b] \<medium_right_bracket>
      certified by (metis of_nat_mono_maybe_le the_\<phi>(3) the_\<phi>lemmata(1) the_\<phi>lemmata(2) unat_of_nat_eq unat_sub) .

lemma op_sub_natR_\<phi>app[\<phi>overload -,
                       \<phi>synthesis %synthesis_arith for _
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<le> x
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<nat>\<^sup>r('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_sub_word[where 'b='b] \<medium_right_bracket>
      certified by (metis of_nat_diff the_\<phi> unat_of_nat) .

lemma op_sub_int_\<phi>app[\<phi>overload -,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x - y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_sub_word[where 'b='b] \<medium_right_bracket>
      certified by auto_sledgehammer .

lemma op_sub_intR_\<phi>app[\<phi>overload -,
                       \<phi>synthesis %synthesis_arith for _
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_sub LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<int>\<^sup>r('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_sub_word[where 'b='b] \<medium_right_bracket>
      certified by (metis of_int_diff uint_word_of_int)  .

declare op_sub_word_\<phi>app[\<phi>overload -]


subsubsection \<open>Multiplication\<close>


lemma op_mul_word_\<phi>app[\<phi>synthesis %synthesis_arith for _
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_umul_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp add: unat_word_ariths(2))

lemma op_mul_nat_\<phi>app[\<phi>overload *,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * y < 2^LENGTH('b)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_mul_word[where 'b='b] \<medium_right_bracket>
      certified by (simp add: the_\<phi>(3) unat_eq_of_nat) .

lemma op_mul_natR_\<phi>app[\<phi>overload *,
                       \<phi>synthesis %synthesis_arith for _
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<nat>\<^sup>r('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_mul_word[where 'b='b] \<medium_right_bracket>
      certified by (metis of_nat_mult unat_of_nat) .
 
lemma op_mul_int_\<phi>app[\<phi>overload *,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_mul_word[where 'b='b] \<medium_right_bracket>
      certified by auto_sledgehammer .

lemma op_mul_intR_\<phi>app[\<phi>overload *,
                       \<phi>synthesis %synthesis_arith for _
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<^sup>r('b)\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_umul LENGTH('b::len) (\<phi>V_pair vy vx)
         \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>\<^sup>r('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>\<^sup>r('b) \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<int>\<^sup>r('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_mul_word[where 'b='b] \<medium_right_bracket>
      certified by (metis of_int_mult uint_word_of_int)  .

declare op_mul_word_\<phi>app[\<phi>overload *]


subsubsection \<open>Division\<close>

lemma op_udiv_word_\<phi>app[\<phi>synthesis %synthesis_arith for _
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_udiv LENGTH('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_udiv_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule,
      rule \<phi>M_assert, simp add: unat_gt_0, rule, simp add: unat_div)

lemma op_div_nat_\<phi>app[\<phi>overload /,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_udiv LENGTH('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_udiv_word_\<phi>app[where 'b='b]
    certified thm \<phi> using More_Word.of_nat_0 the_\<phi>(2) the_\<phi>(3) by blast
  \<medium_right_bracket> certified by (simp add: the_\<phi>lemmata(1) the_\<phi>lemmata(2) of_nat_inverse unat_div) .

declare op_udiv_word_\<phi>app[\<phi>overload /]


lemma op_sdiv_word_\<phi>app[\<phi>synthesis %synthesis_arith for _
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x sdiv y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sdiv TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x sdiv y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_sdiv_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule,
        rule \<phi>M_assert, simp add: unat_gt_0, rule, simp)

lemma op_div_int_\<phi>app[\<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x sdiv y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<noteq> - (2 ^ (LENGTH('b) - 1)) \<and> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_sdiv TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x sdiv y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket>
    op_sdiv_word
    certified using sint_of_int_eq the_\<phi>(3) the_\<phi>(4) the_\<phi>(5) by force
  \<medium_right_bracket>
    certified unfolding sdiv_word_def
    by (metis One_nat_def sdiv_word_max' sdiv_word_min' sint_int_min sint_of_int_eq the_\<phi>(1) the_\<phi>(3) the_\<phi>(6) the_\<phi>lemmata(1) the_\<phi>lemmata(3))  .


lemma op_div_int_fail[\<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> FAIL TEXT(\<open>About integers, there is no rule available for unsigned division\<close> (div)
              \<open>Please use the signed\<close> (sdiv)
              \<open>Note the C semantics is\<close> (sdiv) \<open>instead of\<close> (div)
              \<open>and they are different in negative numbers\<close>)
\<Longrightarrow> \<p>\<r>\<o>\<c> fail \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  unfolding FAIL_def
  by blast

subsubsection \<open>Modulo\<close>

lemma op_umod_word_\<phi>app
  [\<phi>overload %,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x mod y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umod TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x mod y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_umod_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule,
      rule \<phi>M_assert, simp add: unat_gt_0, rule, simp add: unat_div)

lemma op_mod_nat_\<phi>app
  [\<phi>overload %,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x mod y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_umod TYPE('b) (\<phi>V_pair vy vx)
      \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x mod y \<Ztypecolon> \<nat>('b) \<rbrace>\<close>
  \<medium_left_bracket> op_umod_word
    certified using More_Word.of_nat_0 the_\<phi>(2) the_\<phi>(3) by blast
  \<medium_right_bracket>
    certified by (simp add: of_nat_inverse the_\<phi>lemmata(1) the_\<phi>lemmata(2) unat_mod_distrib) .

lemma op_smod_word_\<phi>app
  [\<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda> v. x smod y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_smod TYPE('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x smod y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_smod_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule,
      rule \<phi>M_assert, simp add: unat_gt_0, rule, simp add: unat_div)

lemma op_mod_int_\<phi>app
  [\<phi>overload %,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x smod y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<noteq> 0
\<Longrightarrow> \<p>\<r>\<o>\<c> op_smod TYPE('b) (\<phi>V_pair vy vx)
      \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x smod y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  \<medium_left_bracket> 
    op_smod_word certified using sint_of_int_eq the_\<phi>(3) the_\<phi>(4) the_\<phi>(5) by fastforce
  \<medium_right_bracket> 
  certified
    by (metis One_nat_def signed_take_bit_int_eq_self sint_sbintrunc' smod_word_def smod_word_max smod_word_min the_\<phi>(1) the_\<phi>lemmata(1) the_\<phi>lemmata(2) the_\<phi>lemmata(3))  .

lemma op_mod_int_fail[\<phi>synthesis %synthesis_arith_cut]:
  \<open> FAIL TEXT(\<open>About integers, there is no rule available for unsigned modulo\<close> (mod)
              \<open>Please use the signed\<close> (smod)
              \<open>Note in C semantics it is\<close> (smod) \<open>instead of\<close> (mod)
              \<open>and they are different in negative numbers\<close>)
\<Longrightarrow> \<p>\<r>\<o>\<c> fail \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x mod y \<Ztypecolon> \<int>('b) \<rbrace>\<close>
  unfolding FAIL_def
  by blast


subsubsection \<open>Shift\<close>

paragraph \<open>Right Shift\<close>

lemma op_lshr_word_pre_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_lshr LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] Word('bb) \<longmapsto> \<v>\<a>\<l> drop_bit (unat y) x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  unfolding op_lshr_def
  by (cases v1; cases v2; simp; rule, rule, simp, rule, simp, rule, simp,
      metis drop_bit_eq_div unat_drop_bit_eq)

lemma op_lshr_word_\<phi>app
  [\<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. drop_bit y x \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_lshr LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> drop_bit y x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_lshr_word_pre_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
      certified by (simp add: the_\<phi>lemmata unat_of_nat_eq) .

lemma op_lshr_nat_\<phi>app
  [\<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. drop_bit y x \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_lshr LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> drop_bit y x \<Ztypecolon> \<nat>('ba) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_lshr_word_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
      certified by (simp add: the_\<phi>lemmata unat_drop_bit_eq unat_of_nat_eq) .


lemma drop_bit_nat_le:
  \<open>drop_bit n x \<le> x\<close> for x :: nat
  using div_le_dividend drop_bit_nat_def by presburger

proc op_lshr_int
  [\<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. drop_bit y x \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  input \<open>x \<Ztypecolon> \<v>\<a>\<l>[v1] \<int>('ba)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb)\<close>
  premises \<open>0 \<le> x\<close>
  output \<open>\<v>\<a>\<l> drop_bit y x \<Ztypecolon> \<int>('ba)\<close>
\<medium_left_bracket>
  apply_rule op_lshr_nat_\<phi>app[where 'ba='ba and 'bb='bb]
\<medium_right_bracket> .

paragraph \<open>Left Shift\<close>

lemma op_lshl_word_pre_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] Word('bb) \<longmapsto> \<v>\<a>\<l> push_bit (unat y) x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  unfolding op_lshl_def
  by (cases v1; cases v2; simp; rule, rule, simp, rule, simp, rule,
      simp add: push_bit_nat_def take_bit_nat_def unsigned_push_bit_eq)

lemma op_lshl_word_\<phi>app
  [\<phi>overload <<,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] Word('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> push_bit y x \<Ztypecolon> Word('ba) \<rbrace>\<close>
  \<medium_left_bracket>
    apply_rule op_lshl_word_pre_\<phi>app[where 'ba='ba and 'bb='bb]
  \<medium_right_bracket>
    certified by (simp add: the_\<phi>lemmata unat_of_nat_eq) .

lemma op_lshl_nat_\<phi>app
  [\<phi>overload <<,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * 2 ^ y < 2 ^ LENGTH('ba)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] \<nat>('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> x * 2 ^ y \<Ztypecolon> \<nat>('ba) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_lshl_word_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
      certified unfolding push_bit_nat_def
      by (metis dual_order.strict_trans n_less_equal_power_2 of_nat_push_bit push_bit_eq_mult the_\<phi>(2) unat_eq_of_nat) .

lemma op_lshl_natR_\<phi>app
  [\<phi>overload <<,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<^sup>r('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb)\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x * 2 ^ y < 2 ^ LENGTH('ba)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_lshl LENGTH('ba) LENGTH('bb) (\<phi>V_pair v2 v1)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v1] \<nat>\<^sup>r('ba) \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v2] \<nat>('bb) \<longmapsto> \<v>\<a>\<l> x * 2 ^ y \<Ztypecolon> \<nat>\<^sup>r('ba) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_lshl_word_\<phi>app[where 'ba='ba and 'bb='bb] \<medium_right_bracket>
      certified unfolding push_bit_nat_def
      by (metis of_nat_push_bit push_bit_eq_mult unat_of_nat) .


subsubsection \<open>Comparison\<close>

paragraph \<open>Unsigned Less Than\<close>

lemma op_lt_word_\<phi>app
  [\<phi>overload <, \<phi>synthesis %synthesis_arith for _
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_ult LENGTH('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_ult_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp add: word_less_nat_alt)

lemma op_lt_nat_\<phi>app
  [\<phi>overload <, \<phi>synthesis %synthesis_arith for _
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_ult LENGTH('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_lt_word[where 'b='b] \<medium_right_bracket>
      certified by (simp add: of_nat_inverse the_\<phi>lemmata(1) the_\<phi>lemmata(2) word_less_nat_alt) .

paragraph \<open>Signed Less Than\<close>

lemma op_slt_word_\<phi>app
  [\<phi>overload <, \<phi>synthesis %synthesis_arith for _
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x <s y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_slt TYPE('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] Word('b) \<longmapsto> \<v>\<a>\<l> x <s y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_slt_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp)

lemma op_slt_int_\<phi>app
  [\<phi>overload <, \<phi>synthesis %synthesis_arith for _
                           and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_slt TYPE('b) (\<phi>V_pair vy vx)
       \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_slt_word[where 'b='b] \<medium_right_bracket>
      certified by (simp add: sint_of_int_eq the_\<phi>(1) the_\<phi>lemmata(1) the_\<phi>lemmata(2) the_\<phi>lemmata(3) word_sless_alt) .


paragraph \<open>Unsigned Less Equal\<close>

lemma op_le_word_\<phi>app
  [\<phi>overload \<le>, \<phi>synthesis %synthesis_arith for _
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_ule LENGTH('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] Word('b) \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_ule_def
  by (cases rawx; cases rawy; simp, rule, rule, simp, rule, simp, rule, simp add: word_le_nat_alt)

lemma op_le_nat_\<phi>app
  [\<phi>overload \<le>, \<phi>synthesis %synthesis_arith for _
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_ule LENGTH('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<nat>('b) \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_le_word \<medium_right_bracket>
      certified by (simp add: the_\<phi>lemmata(1) the_\<phi>lemmata(2) unat_of_nat word_le_nat_alt) .

paragraph \<open>Signed Less Equal\<close>

lemma op_sle_word_\<phi>app
  [\<phi>overload \<le>, \<phi>synthesis %synthesis_arith for _
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> Word('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le>s y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_sle TYPE('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] Word('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] Word('b) \<longmapsto> \<v>\<a>\<l> x \<le>s y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_sle_def
  by (cases rawx; cases rawy; simp, rule, rule, simp, rule, simp, rule, simp add: word_le_nat_alt)

lemma op_le_int_\<phi>app
  [\<phi>overload \<le>, \<phi>synthesis %synthesis_arith for _
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_sle TYPE('b) (\<phi>V_pair rawy rawx)
        \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<int>('b) \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_sle_word \<medium_right_bracket>
      certified by (simp add: sint_of_int_eq the_\<phi>lemmata(1) the_\<phi>lemmata(2) the_\<phi>lemmata(3) the_\<phi>lemmata(4) word_sle_eq) .

subsubsection \<open>Cast\<close>

lemma op_cast_uint_word_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_uint TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] Word('ba) \<longmapsto> Word.cast x \<Ztypecolon> \<v>\<a>\<l> Word('bb) \<rbrace>\<close>
  unfolding op_cast_uint_def
  by (cases v, simp, rule, simp, rule, simp)

lemma op_cast_nat_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_uint TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('ba) \<longmapsto> take_bit LENGTH('bb) x \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_cast_uint_word[where 'bb='bb] \<medium_right_bracket>
      certified by (simp add: of_nat_inverse the_\<phi>lemmata unsigned_ucast_eq) .

lemma op_cast_int_word_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_int TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] Word('ba) \<longmapsto> Word.scast x \<Ztypecolon> \<v>\<a>\<l> Word('bb) \<rbrace>\<close>
  unfolding op_cast_int_def
  by (cases v, simp, rule, simp, rule, simp)

lemma op_cast_int_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_cast_int TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<int>('ba) \<longmapsto> signed_take_bit (LENGTH('bb)-1) x \<Ztypecolon> \<v>\<a>\<l> \<int>('bb) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_cast_int_word[where 'bb='bb] \<medium_right_bracket>
      certified by (simp add: signed_scast_eq sint_of_int_eq the_\<phi>(1) the_\<phi>(2)) .

lemma op_upcast_nat_\<phi>app:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> LENGTH('ba) \<le> LENGTH('bb)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_cast_uint TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('ba) \<longmapsto> x \<Ztypecolon> \<v>\<a>\<l> \<nat>('bb) \<rbrace>\<close>
  \<medium_left_bracket> have [useful]: \<open>x < 2 ^ LENGTH('ba)\<close> using \<phi> by blast
  ;; apply_rule op_cast_nat[where 'bb='bb] ($v) \<medium_right_bracket>
      certified by auto_sledgehammer .

lemma op_upcast_int_\<phi>app:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> LENGTH('ba) \<le> LENGTH('bb)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_cast_int TYPE('ba) TYPE('bb) v
     \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] \<int>('ba) \<longmapsto> x \<Ztypecolon> \<v>\<a>\<l> \<int>('bb) \<rbrace>\<close>
  \<medium_left_bracket> apply_rule op_cast_int_word[where 'bb='bb] \<medium_right_bracket>
      certified by (simp add: is_up.rep_eq sint_of_int_eq sint_up_scast the_\<phi>(1) the_\<phi>(3) the_\<phi>lemmata(1)) .

setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put NONE)\<close>

end