theory PhiSem_Int_ArbiPrec
  imports PhiSem_Generic_Boolean PhiSem_Common_Int
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


subsection \<open>Natural Nmber\<close>

definition \<phi>ANat ("\<nat>") where [\<phi>defs]: "\<nat> n = (of_nat n \<Ztypecolon> \<int>)"

lemma [\<phi>reason 1000]: 
  " Threshold_Cost 4
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 \<le> x \<and> y = nat x
\<Longrightarrow> x \<Ztypecolon> \<int> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<nat>"
  \<medium_left_bracket> construct\<phi> \<open>nat x \<Ztypecolon> \<nat>\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 \<le> x
\<Longrightarrow> x \<Ztypecolon> \<int> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s nat x \<Ztypecolon> \<nat> @action to \<nat>\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  " Threshold_Cost 2
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Int.int x = y
\<Longrightarrow> x \<Ztypecolon> \<nat> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<int>" \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  " x \<Ztypecolon> \<nat> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Int.int x \<Ztypecolon> \<int> @action to \<int> " \<medium_left_bracket> \<medium_right_bracket>. .

lemma \<phi>ANat_elim[elim!,\<phi>inhabitance_rule]:
  "Inhabited (n \<Ztypecolon> \<nat>) \<Longrightarrow> C \<Longrightarrow> C" .

lemma [\<phi>reason 1000]: \<open>\<phi>SemType (n \<Ztypecolon> \<nat>) aint\<close> \<medium_left_bracket> to \<int> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: "\<phi>Zero aint \<nat> 0" \<medium_left_bracket> \<open>0 \<Ztypecolon> \<int>\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]: \<open>\<phi>Equal \<nat> (\<lambda>_ _. True) (=)\<close> \<medium_left_bracket> to \<int> \<medium_right_bracket>. .
 

section \<open>Instructions\<close>

subsection \<open>Arithmetic Operations\<close>

definition op_const_aint :: "int \<Rightarrow> VAL proc"
  where "op_const_aint const = Return (\<phi>arg (V_aint.mk const))"

definition op_aadd :: "(VAL \<times> VAL, VAL) proc'"
  where "op_aadd =
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

definition op_amul :: "(VAL \<times> VAL, VAL) proc'"
  where "op_amul =
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

definition op_alshl :: "(VAL \<times> VAL, VAL) proc'"
  where "op_alshl =
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


section \<open>Abstraction of Instructions\<close>


subsection \<open>Arithmetic Operations\<close>

subsubsection \<open>Constant Integer\<close>

lemma op_const_aint_\<phi>app[
    \<phi>synthesis 300 for \<open>\<lambda>ret. (numeral ?n::int) \<Ztypecolon> _\<close>
                       \<open>\<lambda>ret. (0::int) \<Ztypecolon> _\<close>
                       \<open>\<lambda>ret. (1::int) \<Ztypecolon> _\<close>]:
  \<open> Check_Literal x
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_aint x \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_const_aint_def Premise_def
  by (rule, simp add: \<phi>expns)

lemma op_const_anat_\<phi>app[
    \<phi>synthesis 300 for \<open>\<lambda>ret. numeral ?n \<Ztypecolon> _\<close>
                       \<open>\<lambda>ret. 0 \<Ztypecolon> _\<close>
                       \<open>\<lambda>ret. 1 \<Ztypecolon> _\<close>]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y x' : of_nat x \<comment>\<open>TODO: improve this!\<close>
\<Longrightarrow> Check_Literal x'
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_aint x' \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat> \<rbrace>\<close> 
  \<medium_left_bracket> op_const_aint[where x=x'] \<medium_right_bracket>. .


lemma [\<phi>reason 1210
    for \<open>Synthesis_Parse (numeral ?n::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (1::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (0::nat) (?X :: ?'ret \<Rightarrow> assn)\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<nat>) X
\<Longrightarrow> Synthesis_Parse n X\<close>
  for X :: \<open>'ret \<Rightarrow> assn\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1210
    for \<open>Synthesis_Parse (numeral ?n::int) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (1::int) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (0::int) (?X :: ?'ret \<Rightarrow> assn)\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<int>) X
\<Longrightarrow> Synthesis_Parse n X\<close>
  for X :: \<open>'ret \<Rightarrow> assn\<close>
  unfolding Synthesis_Parse_def ..


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

lemma op_add_aint_\<phi>app[\<phi>overload +, \<phi>synthesis 100]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_aadd (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<int> \<rbrace> \<close>
  unfolding op_aadd_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_add_anat_\<phi>app[\<phi>overload +, \<phi>synthesis 100]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_aadd (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<nat> \<rbrace> \<close>
      \<medium_left_bracket> $vx $vy op_add_aint \<medium_right_bracket> by fastforce .

paragraph \<open>Subtraction\<close>

lemma op_sub_aint_\<phi>app[\<phi>overload -, \<phi>synthesis 100]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_asub (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x - y \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_asub_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_sub_anat_\<phi>app[\<phi>overload -, \<phi>synthesis 100]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_asub (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x - y \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> $vx $vy op_sub_aint \<medium_right_bracket>
    using nat_minus_as_int the_\<phi>(2) by presburger .

paragraph \<open>Times\<close>

lemma op_mul_aint[\<phi>overload *, \<phi>synthesis 100]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_amul (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x * y \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_amul_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_mul_anat[\<phi>overload *, \<phi>synthesis 100]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_amul (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x * y \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> $vx $vy op_mul_aint \<medium_right_bracket>
    by (simp add: nat_mult_distrib) .


paragraph \<open>Division\<close>

lemma op_udiv_aint_\<phi>app[\<phi>overload /]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_audiv (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x div y \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_audiv_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)

lemma op_udiv_anat_\<phi>app[\<phi>overload /]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_audiv (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vy] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x div y \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> $vx $vy op_udiv_aint \<medium_right_bracket>
    by (simp add: div_int_pos_iff nat_div_distrib) .


paragraph \<open>Right Shift\<close>

lemma op_lshr_aint_pre_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 \<le> y
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alshr (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw2] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l drop_bit (nat y) x \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_alshr_def Premise_def
  apply (cases raw1; cases raw2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
      rule \<phi>M_assert, simp add: \<phi>expns, rule, simp add: \<phi>expns)
  using drop_bit_int_def by presburger

lemma op_lshr_aint_\<phi>app[\<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alshr (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw2] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l drop_bit y x \<Ztypecolon> \<int> \<rbrace>\<close>
  \<medium_left_bracket> $x $y op_lshr_aint_pre \<medium_right_bracket>. .

lemma op_lshr_anat_\<phi>app[\<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alshr (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw1] \<nat> \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw2] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l drop_bit y x \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> $x $y op_lshr_aint \<medium_right_bracket>
    by (simp add: drop_bit_of_nat)  .

paragraph \<open>Left Shift\<close>

lemma op_lshl_aint_pre_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 \<le> y
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alshl (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw2] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l push_bit (nat y) x \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_alshl_def Premise_def
  by (cases raw1; cases raw2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
      rule \<phi>M_assert, simp add: \<phi>expns, rule, simp add: \<phi>expns push_bit_int_def)

lemma op_lshl_aint_\<phi>app[\<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alshl (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw2] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l push_bit y x \<Ztypecolon> \<int> \<rbrace>\<close>
  \<medium_left_bracket> $x $y op_lshl_aint_pre \<medium_right_bracket>. .

lemma op_lshl_anat_\<phi>app[\<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alshl (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw1] \<nat> \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw2] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l push_bit y x \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> $x $y op_lshl_aint \<medium_right_bracket>
    by (simp add: push_bit_of_nat) .


paragraph \<open>Less Than\<close>

lemma op_lt_aint[\<phi>overload <, \<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_a_lt (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawx] \<int>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawy] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_a_lt_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_lt_anat[\<phi>overload <, \<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_a_lt (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawx] \<nat>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawy] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> $x $y op_lt_aint \<medium_right_bracket>. .


paragraph \<open>Less Equal\<close>

lemma op_le_aint_\<phi>app[\<phi>overload \<le>, \<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_a_le (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawx] \<int>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawy] \<int> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_a_le_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_le_anat_\<phi>app[\<phi>overload \<le>, \<phi>synthesis 100]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_a_le (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawx] \<nat>\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawy] \<nat> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> $x $y op_le_aint \<medium_right_bracket>. .


end