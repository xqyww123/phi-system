theory PhiSem_Machine_Integer
  imports PhiSem_Common_Int PhiSem_Generic_Boolean "HOL-Library.Word"
begin

chapter \<open>Semantics for Machine Integers\<close>

section \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype \<phi>machine_int_ty = \<phi>empty_ty +
  T_int     :: nat \<comment> \<open>in unit of bits\<close>

debt_axiomatization T_int :: \<open>nat type_entry\<close>
  where \<phi>machine_int_ty_ax: \<open>\<phi>machine_int_ty TY_CONS_OF T_int\<close>

interpretation \<phi>machine_int_ty TY_CONS_OF _ _ T_int using \<phi>machine_int_ty_ax .

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

virtual_datatype \<phi>machine_int_val = \<phi>empty_val +
  V_int     :: \<open>nat \<times> nat\<close> \<comment> \<open>bits \<times> value\<close>

debt_axiomatization V_int :: \<open>(nat \<times> nat) value_entry\<close>
  where \<phi>machine_int_val_ax: \<open>\<phi>machine_int_val VAL_CONS_OF V_int\<close>

interpretation \<phi>machine_int_val VAL_CONS_OF _ _ V_int using \<phi>machine_int_val_ax .

hide_fact \<phi>machine_int_val_ax \<phi>machine_int_val_axioms

subsubsection \<open>Semantics\<close>

debt_axiomatization
    WT_int[simp]: \<open>Well_Type (T_int.mk b)     = { V_int.mk (b,x)    |x. x < 2 ^ b } \<close>
and can_eqcmp_int[simp]: "Can_EqCompare res (V_int.mk (b1,x1)) (V_int.mk (b2,x2)) \<longleftrightarrow> b1 = b2"
and eqcmp_int[simp]: "EqCompare (V_int.mk i1) (V_int.mk i2) \<longleftrightarrow> i1 = i2"
and  zero_int[simp]: \<open>Zero (T_int.mk b)    = Some (V_int.mk (b,0))\<close>

lemma Valid_Types[simp]:
  \<open>Valid_Type (T_int.mk n)\<close>
  unfolding Inhabited_def
  apply simp
  using less_exp by blast


section \<open>\<phi>-Types\<close>

subsection \<open>Integer\<close>

subsubsection \<open>Words\<close>

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



subsubsection \<open>Natural Numbers\<close>

paragraph \<open>Natural Number\<close>

definition \<phi>Nat :: "'b::len itself \<Rightarrow> (VAL, nat) \<phi>"
  where [\<phi>defs]: "\<phi>Nat _ x = ((of_nat x :: 'b word) \<Ztypecolon> Word('b) \<^bold>s\<^bold>u\<^bold>b\<^bold>j x \<in> {0..< 2 ^ LENGTH('b)})"

syntax \<phi>Nat_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<nat>'(_')")

translations "\<nat>('x)" <= "CONST \<phi>Nat TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>Nat_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>Nat\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>


lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<Ztypecolon> Word(_) \<^bold>a\<^bold>n\<^bold>d _\<close>]:
  \<open> Threshold_Cost 7
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = of_nat x
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> Word('b) \<^bold>a\<^bold>n\<^bold>d x < 2 ^ LENGTH('b)\<close>
  for y :: \<open>'b::len word\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [
  \<phi>reason 800 for \<open>_ \<Ztypecolon> \<phi>Nat _ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to (Word _)\<close>,
  \<phi>inhabitance_rule
]:
  \<open>x \<Ztypecolon> \<nat>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (of_nat x :: 'b::len word) \<Ztypecolon> Word('b) \<^bold>a\<^bold>n\<^bold>d x < 2 ^ LENGTH('b)
   @action to Word('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .


lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Word(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<Ztypecolon> \<nat>(_) \<^bold>a\<^bold>n\<^bold>d _\<close>]:
  \<open> Threshold_Cost 9
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = unat x
\<Longrightarrow> x \<Ztypecolon> Word('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<nat>('b)\<close>
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> construct\<phi> \<open>unat x \<Ztypecolon> \<nat>('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Word _ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to (\<phi>Nat _)\<close>]:
  \<open> x \<Ztypecolon> Word('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s unat x \<Ztypecolon> \<nat>('b) @action to \<nat>('b)\<close>
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
                              \<^bold>s\<^bold>u\<^bold>b\<^bold>j x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)})"

syntax \<phi>Int_syntax :: "type \<Rightarrow> (VAL, nat) \<phi>" ("\<int>'(_')")

translations "\<int>('x)" == "CONST \<phi>Int TYPE('x)"

parse_ast_translation \<open>
  let open Ast
   in [(\<^syntax_const>\<open>\<phi>Int_syntax\<close>, (fn _ => fn [V] =>
          Appl [Constant \<^const_syntax>\<open>\<phi>Int\<close>, Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, add_sort V]]))] end\<close>

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<Ztypecolon> Word(_) \<^bold>a\<^bold>n\<^bold>d _\<close>]:
  " Threshold_Cost 7
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = of_int x
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> Word('b) \<^bold>a\<^bold>n\<^bold>d x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)}"
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [
  \<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to Word(_)\<close>,
  \<phi>inhabitance_rule
]:
  \<open>x \<Ztypecolon> \<int>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (of_int x :: 'b::len word) \<Ztypecolon> Word('b) \<^bold>a\<^bold>n\<^bold>d x \<in> { -(2^(LENGTH('b)-1)) ..< 2^(LENGTH('b)-1)}
   @action to Word('b)\<close>
  \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>?x \<Ztypecolon> Word(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<Ztypecolon> \<int>(_) \<^bold>a\<^bold>n\<^bold>d _\<close>]:
  " Threshold_Cost 9
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = sint x
\<Longrightarrow> x \<Ztypecolon> Word('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<int>('b)"
  for x :: \<open>'b::len word\<close>
  \<medium_left_bracket> construct\<phi> \<open>y \<Ztypecolon> \<int>('b)\<close>
    affirm apply (simp add: \<open>y = sint x\<close>) using sint_greater_eq sint_less by blast
  \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> Word(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to Word(_)\<close>]:
  \<open> x \<Ztypecolon> Word('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sint x \<Ztypecolon> \<int>('b) @action to Word('b) \<close>
  \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to \<nat>(_)\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 \<le> x \<and> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s nat x \<Ztypecolon> \<nat>('b) @action to \<nat>('b)\<close>
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket>
  by (smt (verit, ccfv_SIG) diff_le_self local.\<phi>(2) power_increasing_iff unat_eq_nat_uint word_of_int_inverse) .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<int>(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _\<close>]:
  \<open> Threshold_Cost 6
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 \<le> x \<and> x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<int>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s nat x \<Ztypecolon> \<nat>('b)\<close>
  \<medium_left_bracket> to \<open>\<nat>('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to \<int>(_)\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s of_nat x \<Ztypecolon> \<int>('b) @action to \<int>(_) \<close>
  \<medium_left_bracket> to \<open>Word('b)\<close> \<medium_right_bracket>
  by (metis One_nat_def id_apply local.\<phi>(2) negative_zle of_int_eq_id of_nat_less_numeral_power_cancel_iff real_of_nat_eq_numeral_power_cancel_iff signed_of_nat signed_take_bit_int_eq_self_iff) .

lemma [\<phi>reason 800 for \<open>_ \<Ztypecolon> \<nat>(_) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ \<close>]:
  \<open> Threshold_Cost 4
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2 ^ (LENGTH('b)-1)
\<Longrightarrow> x \<Ztypecolon> \<nat>('b) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s of_nat x \<Ztypecolon> \<int>('b) \<close>
  \<medium_left_bracket> to \<open>\<int>(_)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<int>('b)) int('b)\<close> \<medium_left_bracket> to \<open>Word(_)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  "\<phi>Zero int('b) \<int>('b) 0" \<medium_left_bracket> \<open>0 \<Ztypecolon> Word('b)\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  "\<phi>Equal \<int>('b) (\<lambda>x y. True) (=)"
  \<medium_left_bracket> to \<open>Word(_)\<close> \<medium_right_bracket>
  by (metis One_nat_def atLeastLessThan_iff local.\<phi>lemmata signed_take_bit_int_eq_self_iff sint_sbintrunc') .



section \<open>Instructions\<close>

subsection \<open>Arithmetic Operations\<close>

subsubsection \<open>Integer arithmetic\<close>

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
      Return (\<phi>arg (V_int.mk (bits, (val_b div val_a))))
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
      Return (\<phi>arg (V_int.mk (b_b, (val_b * 2 ^ val_a))))
  )))"

definition op_lt :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_lt bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b < val_a)))
  )))"

definition op_le :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_le bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (T_int.mk bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b \<le> val_a)))
  )))"



section \<open>Abstraction of Instructions\<close>

definition Bits_Tag :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix "<bits>" 25) where [iff]: \<open>(x <bits> n) = x\<close>

subsection \<open>Arithmetic Operations\<close>

bundle unfold_Big = Big_def[iff]

subsubsection \<open>Constant Integer\<close>

lemma op_const_word_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int LENGTH('b) (unat n) \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> Word('b) \<rbrace> \<close>
  unfolding op_const_int_def Premise_def Synthesis_def
  by (rule, simp add: \<phi>expns)

lemma
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2 ^ LENGTH('b)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int LENGTH('b::len) n \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>('b) \<rbrace> \<close>
  \<medium_left_bracket> have [simp]: \<open>unat (word_of_nat n :: 'b word) = n\<close> using \<phi> of_nat_inverse by blast 
    ;; op_const_word[where 'b='b and n=\<open>of_nat n\<close>, simplified]
  \<medium_right_bracket>. .

lemma [\<phi>reason 1200
    for \<open>Synthesis_Parse (numeral ?n::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (1::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (0::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<nat>[32]) X
\<Longrightarrow> Synthesis_Parse n X\<close>
  for X :: \<open>'ret \<Rightarrow> assn\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200
    for \<open>Synthesis_Parse ((numeral ?n::nat) <bits> ?b) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse ((1::nat) <bits> ?b) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse ((0::nat) <bits> ?b) (?X :: ?'ret \<Rightarrow> assn)\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<nat>[b]) X
\<Longrightarrow> Synthesis_Parse (n <bits> b) X\<close>
  for X :: \<open>'ret \<Rightarrow> assn\<close>
  unfolding Synthesis_Parse_def ..


lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l numeral ?n \<Ztypecolon> \<nat>[?b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
        \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> \<nat>[?b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
        \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 0 \<Ztypecolon> \<nat>[?b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2 ^ Big b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int b n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<rbrace> @action synthesis G\<close>
  unfolding Synthesis_def Action_Tag_def
  using op_const_int_\<phi>app[THEN \<phi>frame, simplified] .


lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> ?R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (?n <bits> ?b') \<Ztypecolon> \<nat>[?b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action synthesis G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (n <bits> b) \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action synthesis G\<close>
  unfolding Bits_Tag_def .


(* lemma op_const_size_t:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> Size \<rbrace>\<close>
  unfolding op_const_size_t_def Premise_def
  by (\<phi>reason, simp add: \<phi>expns Big_def) *)


(* lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (numeral ?n) \<Ztypecolon> Size \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 0 \<Ztypecolon> Size \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> Size \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> Size \<rbrace> @action synthesis G\<close>
  unfolding Synthesis_def Action_Tag_def
  using op_const_size_t[THEN \<phi>frame, simplified] . *)


subsubsection \<open>Integer Arithmetic\<close>

paragraph \<open>Addition\<close>

lemma op_add_word_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] Word('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] Word('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> Word('b) \<rbrace>\<close>
  unfolding op_add_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns unat_word_ariths)

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2 ^ LENGTH('b)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<nat>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<nat>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<nat>('b) \<rbrace> \<close>
  \<medium_left_bracket> $vx $vy op_add_word[where 'b='b] \<medium_right_bracket> using \<phi> by (metis of_nat_add of_nat_inverse) .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $vx $vy op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

declare op_add_word_\<phi>app[\<phi>overload +]

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vxx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vxx] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx1) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx1] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx2) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx2] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx3) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx3] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx4) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx4] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx5) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx5] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx6) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx6] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx7) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx7] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx8) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx8] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx9) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx9] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx10) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx10] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx11) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx11] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx12) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx12] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .

lemma [\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y \<in> {- (2 ^ (LENGTH('b)-1)) ..< 2 ^ (LENGTH('b)-1) }
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add LENGTH('b::len) (\<phi>V_pair vy vx13) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx13] \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int>('b) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int>('b) \<rbrace> \<close>
  \<medium_left_bracket> $x $y op_add_word[where 'b='b] \<medium_right_bracket>
    by (metis atLeastLessThan_iff local.\<phi>(2) of_int_add signed_take_bit_int_eq_self_iff sint_sbintrunc') .


thm "+_\<phi>app"

proc
  input \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<int>('b)\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<nat>('b)\<close>
  output \<open>\<dots>\<close>  
  \<medium_left_bracket> $x $y +

lemma op_add[\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2 ^ Big b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<nat>[b]\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def Premise_def including unfold_Big
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x + ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b]  \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  premises \<open>x + y < 2 ^ Big b\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x + y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 + \<medium_right_bracket>. .

lemma op_add_mod:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l (x + y) mod 2 ^ Big b \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def including unfold_Big
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)

paragraph \<open>Subtraction\<close>

lemma op_sub[\<phi>overload -]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x - y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_sub_def Premise_def including unfold_Big
  apply (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)
  by (metis Nat.add_diff_assoc2 add.commute less_imp_diff_less mod_add_self2 mod_less)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x - ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  premises \<open>y \<le> x\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x - y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 - \<medium_right_bracket>. .


paragraph \<open>Times\<close>

lemma op_omul[\<phi>overload *]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x * y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_umul b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x * y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_umul_def Premise_def including unfold_Big
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x * ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  premises \<open>x*y < 2^b\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x * y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 * \<medium_right_bracket>. .


paragraph \<open>Division\<close>

lemma op_udiv[\<phi>overload /]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_udiv b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x div y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_udiv_def Premise_def
  apply (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)
  using div_le_dividend le_less_trans by blast

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x div ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x div y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 / \<medium_right_bracket>. .

paragraph \<open>Shift\<close>

lemma op_lshr_nat_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lshr b1 b2 (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> Val raw1 \<nat>[b1] \<heavy_comma> y \<Ztypecolon> Val raw2 \<nat>[b2] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x div 2 ^ Big y \<Ztypecolon> \<nat>[b1] \<rbrace>\<close>
  unfolding op_lshr_def
  apply (cases raw1; cases raw2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns Big_def)
  using div_le_dividend le_less_trans by blast

lemma op_lshl_nat_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x * 2 ^ Big y < 2 ^ Big b1
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lshl b1 b2 (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> Val raw1 \<nat>[b1] \<heavy_comma> y \<Ztypecolon> Val raw2 \<nat>[b2] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x * 2 ^ Big y \<Ztypecolon> \<nat>[b1] \<rbrace>\<close>
  unfolding op_lshl_def
  by (cases raw1; cases raw2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns Big_def)

proc [
    \<phi>reason 1300 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x LSHR ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b1] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b2] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHR y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 op_lshr_nat \<medium_right_bracket>. .

proc [
    \<phi>reason 1300 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x LSHL ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  premises \<open>x * 2 ^ Big y < 2 ^ Big b1\<close>
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b1] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b2] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHL y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 op_lshl_nat \<medium_right_bracket>. .


paragraph \<open>Less Than\<close>

lemma op_lt[\<phi>overload <]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt b (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> Val rawx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val rawy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_lt_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x < ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x < y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 < \<medium_right_bracket>. .


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x > ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x > y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket>
    F1 \<rightarrow> val v1
    F2 \<rightarrow> val v2
    $v2 $v1 <
  \<medium_right_bracket>. .

(* Service Obligation !!!!! Last Day!!!! *)

paragraph \<open>Less Equal\<close>

lemma op_le[\<phi>overload \<le>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le b (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> Val rawx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val rawy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_le_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<le> ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b]  \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<le> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> F1 F2 \<le> \<medium_right_bracket>. .


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<ge> ?y) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1   @action synthesis G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2   @action synthesis G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<ge> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  @action \<open>synthesis G\<close>
  \<medium_left_bracket> 
    F1 \<rightarrow> val v1
    F2 \<rightarrow> val v2
    $v2 $v1 \<le>
  \<medium_right_bracket>. .



end