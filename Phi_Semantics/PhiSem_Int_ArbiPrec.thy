theory PhiSem_Int_ArbiPrec
  imports PhiSem_Common_Int PhiSem_Generic_Boolean
begin

chapter \<open>Integer of Arbitrary Precision\<close>

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")

section \<open>Models\<close>

subsection \<open>Type\<close>

virtual_datatype \<phi>spec_int_ty = \<phi>empty_ty +
  T_aint    ::  unit

debt_axiomatization T_aint :: \<open>unit type_entry\<close>
  where \<phi>spec_int_ty_ax: \<open>\<phi>spec_int_ty TY_CONS_OF T_aint\<close>

interpretation \<phi>spec_int_ty TY_CONS_OF _ _ T_aint using \<phi>spec_int_ty_ax .

hide_fact \<phi>spec_int_ty_ax

subsection \<open>Value\<close>

virtual_datatype \<phi>spec_int_val = \<phi>empty_val +
  V_aint     :: \<open>int\<close>

debt_axiomatization V_aint :: \<open>int value_entry\<close>
  where \<phi>spec_int_val_ax: \<open>\<phi>spec_int_val VAL_CONS_OF V_aint\<close>

interpretation \<phi>spec_int_val VAL_CONS_OF _ _ V_aint using \<phi>spec_int_val_ax .

hide_fact \<phi>spec_int_val_ax \<phi>spec_int_val_axioms

abbreviation aint where \<open>aint \<equiv> T_aint.mk ()\<close>

subsection \<open>Semantics\<close>

debt_axiomatization
    WT_aint[simp]: \<open>Well_Type aint = { V_aint.mk i |i. True } \<close>
and can_eqcmp_aint[simp]: "Can_EqCompare res (V_aint.mk i1) (V_aint.mk i2)"
and eqcmp_aint[simp]: "EqCompare (V_aint.mk i1) (V_aint.mk i2) \<longleftrightarrow> i1 = i2"
and  zero_aint[simp]: \<open>Zero aint   = Some (V_aint.mk 0)\<close>

lemma Valid_Types[simp]:
  \<open>Valid_Type aint\<close>
  unfolding Inhabited_def
  apply simp
  using less_exp by blast


section \<open>\<phi>-Types\<close>

subsection \<open>Natural Nmber\<close>

definition \<phi>ANat :: "(VAL, nat) \<phi>" ("\<nat>")
  where "\<nat> = (\<lambda>n. {V_aint.mk (of_nat n)})"

lemma \<phi>ANat_expn[\<phi>expns]:
  "p \<in> (n \<Ztypecolon> \<nat>) \<longleftrightarrow> (p = V_aint.mk (of_nat n))"
  unfolding \<phi>Type_def Big_def by (simp add: \<phi>ANat_def)

lemma \<phi>ANat_elim[elim!,\<phi>inhabitance_rule]:
  "Inhabited (n \<Ztypecolon> \<nat>) \<Longrightarrow> C \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>ANat_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (n \<Ztypecolon> \<nat>) aint\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns Big_def)

lemma [\<phi>reason 1000]:
  "\<phi>Equal \<nat> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (auto simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  "\<phi>Zero aint \<nat> 0" unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  \<open> is_singleton (n \<Ztypecolon> \<nat>)\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)


subsection \<open>Integer in the normal sense\<close>

definition \<phi>AInt :: "(VAL, int) \<phi>" ("\<int>")
  where "\<phi>AInt = (\<lambda>z. { V_aint.mk z})"

lemma \<phi>AInt_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<int>) \<longleftrightarrow> p = V_aint.mk x"
  unfolding \<phi>Type_def by (simp add: \<phi>AInt_def)

lemma \<phi>AInt_inhabited[elim!,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> \<int>) \<Longrightarrow> C \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) 

lemma [\<phi>reason 1000]:
    "\<phi>Equal \<int> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns eq_nat_nat_iff)

lemma [\<phi>reason 1000]:
    "\<phi>Zero aint \<int> 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Int_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<int>) aint\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns)


subsubsection \<open>Subtyping\<close>

lemma subty_Z_N[\<phi>overload nat]: 
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < x \<Longrightarrow> x \<Ztypecolon> \<int> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s nat x \<Ztypecolon> \<nat>"
  unfolding Imply_def Premise_def
  by (simp add: \<phi>expns Big_def del: One_nat_def)

lemma subty_N_Z[\<phi>overload int]:
  "x \<Ztypecolon> \<nat> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Int.int x \<Ztypecolon> \<int>"
  unfolding Imply_def Premise_def by (simp add: \<phi>expns Big_def del: One_nat_def)


section \<open>Instructions\<close>

subsection \<open>Arithmetic Operations\<close>

definition op_const_aint :: "int \<Rightarrow> VAL proc"
  where "op_const_aint const = Return (\<phi>arg (V_aint.mk const))"

definition op_add :: "(VAL \<times> VAL, VAL) proc'"
  where "op_add =
      \<phi>M_caseV (\<lambda>vb va.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      Return (\<phi>arg (V_aint.mk (val_a + val_b)))
  )))"

definition op_asub :: "(VAL \<times> VAL, VAL) proc'"
  where "op_asub =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      Return (\<phi>arg (V_aint.mk (val_b - val_a)))
  )))"

definition op_aumul :: "(VAL \<times> VAL, VAL) proc'"
  where "op_aumul =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      Return (\<phi>arg (V_aint.mk (val_b * val_a)))
  )))"

definition op_audiv :: "(VAL \<times> VAL, VAL) proc'"
  where "op_audiv =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      Return (\<phi>arg (V_aint.mk (val_b div val_a)))
  )))"

definition op_alshr :: "(VAL \<times> VAL, VAL) proc'"
  where "op_alshr =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      \<phi>M_assert (0 \<le> val_a) \<ggreater>
      Return (\<phi>arg (V_aint.mk (val_b div 2 ^ (Int.nat val_a))))
  )))"

definition op_alshl :: "nat \<Rightarrow> nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_alshl b_b b_a =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      \<phi>M_assert (0 \<le> val_a) \<ggreater>
      Return (\<phi>arg (V_aint.mk (val_b * 2 ^ (Int.nat val_a))))
  )))"

definition op_a_lt :: "(VAL \<times> VAL, VAL) proc'"
  where "op_a_lt =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b < val_a)))
  )))"

definition op_a_le :: "(VAL \<times> VAL, VAL) proc'"
  where "op_a_le =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV aint V_aint.dest va (\<lambda>val_a.
      \<phi>M_getV aint V_aint.dest vb (\<lambda>val_b.
      Return (\<phi>arg (V_bool.mk (val_b \<le> val_a)))
  )))"



end