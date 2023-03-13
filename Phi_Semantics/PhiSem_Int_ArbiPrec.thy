theory PhiSem_Int_ArbiPrec
  imports PhiSem_Generic_Boolean PhiSem_Common_Int
begin

chapter \<open>Integer of Arbitrary Precision\<close>

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")

section \<open>Semantics\<close>

subsection \<open>Type\<close>

virtual_datatype \<phi>spec_int_ty =
  T_aint    ::  unit

debt_axiomatization T_aint :: \<open>unit type_entry\<close>
  where \<phi>spec_int_ty_ax: \<open>\<phi>spec_int_ty TY_CONS_OF T_aint\<close>

interpretation \<phi>spec_int_ty TY_CONS_OF _ _ T_aint using \<phi>spec_int_ty_ax .

hide_fact \<phi>spec_int_ty_ax

abbreviation aint where \<open>aint \<equiv> T_aint.mk ()\<close>

subsection \<open>Value\<close>

virtual_datatype \<phi>spec_int_val =
  V_aint     :: \<open>int\<close>

debt_axiomatization V_aint :: \<open>int value_entry\<close>
  where \<phi>spec_int_val_ax: \<open>\<phi>spec_int_val VAL_CONS_OF V_aint\<close>

interpretation \<phi>spec_int_val VAL_CONS_OF _ _ V_aint using \<phi>spec_int_val_ax .

hide_fact \<phi>spec_int_val_ax \<phi>spec_int_val_axioms


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
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> x \<and> y = nat x
\<Longrightarrow> x \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<nat>"
  \<medium_left_bracket> construct\<phi> \<open>nat x \<Ztypecolon> \<nat>\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> x
\<Longrightarrow> x \<Ztypecolon> \<int> \<i>\<m>\<p>\<l>\<i>\<e>\<s> nat x \<Ztypecolon> \<nat> @action to \<nat>\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  " Threshold_Cost 2
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Int.int x = y
\<Longrightarrow> x \<Ztypecolon> \<nat> \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<int>" \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1000]:
  " x \<Ztypecolon> \<nat> \<i>\<m>\<p>\<l>\<i>\<e>\<s> Int.int x \<Ztypecolon> \<int> @action to \<int> " \<medium_left_bracket> \<medium_right_bracket>. .

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

lemma op_const_aint_\<phi>app[\<phi>synthesis 300]:
  \<open> Check_Literal x
\<Longrightarrow> \<p>\<r>\<o>\<c> op_const_aint x \<lbrace> Void \<longmapsto> \<v>\<a>\<l> x \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_const_aint_def Premise_def
  by (rule, simp add: \<phi>expns)

lemma op_const_anat_\<phi>app[\<phi>synthesis 300]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y x' : of_nat x \<comment>\<open>TODO: improve this!\<close>
\<Longrightarrow> Check_Literal x'
\<Longrightarrow> \<p>\<r>\<o>\<c> op_const_aint x' \<lbrace> Void \<longmapsto> \<v>\<a>\<l> x \<Ztypecolon> \<nat> \<rbrace>\<close>
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


subsubsection \<open>Integer Arithmetic\<close>

paragraph \<open>Addition\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma op_add_aint_\<phi>app
  [\<phi>overload add,
   \<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_aadd (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int> \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<int> \<rbrace> \<close>
  unfolding op_aadd_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)
   
lemma op_add_anat_\<phi>app
  [\<phi>overload add,
   \<phi>synthesis for _ (100)
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_aadd (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat> \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<nat> \<rbrace> \<close>
  \<medium_left_bracket> op_add_aint \<medium_right_bracket> by fastforce .

paragraph \<open>Subtraction\<close>

lemma op_sub_aint_\<phi>app[\<phi>overload sub,
                       \<phi>synthesis for _ (100)
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_asub (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int> \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_asub_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_sub_anat_\<phi>app[\<phi>overload sub,
                       \<phi>synthesis for _ (100)
                                  and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y \<le> x
\<Longrightarrow> \<p>\<r>\<o>\<c> op_asub (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat> \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> op_sub_aint \<medium_right_bracket> using nat_minus_as_int the_\<phi> by presburger .

paragraph \<open>Times\<close>

lemma op_mul_aint[\<phi>overload mul,
                  \<phi>synthesis for _ (100)
                             and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_amul (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int> \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_amul_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_mul_anat[\<phi>overload mul,
                  \<phi>synthesis for _ (100)
                             and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_amul (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat> \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> op_mul_aint \<medium_right_bracket>
    by (simp add: nat_mult_distrib) .


paragraph \<open>Division\<close>

lemma op_udiv_aint_\<phi>app[\<phi>overload div,
                        \<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_audiv (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<int> \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_audiv_def
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)

lemma op_udiv_anat_\<phi>app[\<phi>overload div,
                        \<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_audiv (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<nat> \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> op_udiv_aint \<medium_right_bracket>
    by (simp add: div_int_pos_iff nat_div_distrib) .


paragraph \<open>Right Shift\<close>

lemma op_lshr_aint_pre_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> y
\<Longrightarrow> \<p>\<r>\<o>\<c> op_alshr (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw2] \<int> \<longmapsto> \<v>\<a>\<l> drop_bit (nat y) x \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_alshr_def Premise_def
  apply (cases raw1; cases raw2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
      rule \<phi>M_assert, simp add: \<phi>expns, rule, simp add: \<phi>expns)
  using drop_bit_int_def by presburger

lemma op_lshr_aint_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. drop_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_alshr (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw2] \<nat> \<longmapsto> \<v>\<a>\<l> drop_bit y x \<Ztypecolon> \<int> \<rbrace>\<close>
  \<medium_left_bracket> op_lshr_aint_pre \<medium_right_bracket>. .

lemma op_lshr_anat_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>ret. drop_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_alshr (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw1] \<nat> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw2] \<nat> \<longmapsto> \<v>\<a>\<l> drop_bit y x \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> op_lshr_aint \<medium_right_bracket>
    by (simp add: drop_bit_of_nat)  .

paragraph \<open>Left Shift\<close>

lemma op_lshl_aint_pre_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<le> y
\<Longrightarrow> \<p>\<r>\<o>\<c> op_alshl (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw2] \<int> \<longmapsto> \<v>\<a>\<l> push_bit (nat y) x \<Ztypecolon> \<int> \<rbrace>\<close>
  unfolding op_alshl_def Premise_def
  by (cases raw1; cases raw2; simp; rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule,
      rule \<phi>M_assert, simp add: \<phi>expns, rule, simp add: \<phi>expns push_bit_int_def)

lemma op_lshl_aint_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_alshl (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw1] \<int> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw2] \<nat> \<longmapsto> \<v>\<a>\<l> push_bit y x \<Ztypecolon> \<int> \<rbrace>\<close>
  \<medium_left_bracket> op_lshl_aint_pre \<medium_right_bracket>. .

lemma op_lshl_anat_\<phi>app[\<phi>synthesis for _ (100)
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. push_bit y x \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_alshl (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw1] \<nat> \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw2] \<nat> \<longmapsto> \<v>\<a>\<l> push_bit y x \<Ztypecolon> \<nat> \<rbrace>\<close>
  \<medium_left_bracket> op_lshl_aint \<medium_right_bracket> by (simp add: push_bit_of_nat) .


paragraph \<open>Less Than\<close>

lemma op_lt_aint[\<phi>overload less,
                 \<phi>synthesis for _ (100)
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_a_lt (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<int> \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_a_lt_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_lt_anat[\<phi>overload less,
                 \<phi>synthesis for _ (100)
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_a_lt (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<nat> \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_lt_aint \<medium_right_bracket>. .


paragraph \<open>Less Equal\<close>

lemma op_le_aint_\<phi>app[\<phi>overload less_equal,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<int>\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_a_le (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<int>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<int> \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_a_le_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_le_anat_\<phi>app[\<phi>overload less_equal,
                      \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (1200)]:
  \<open>\<p>\<r>\<o>\<c> op_a_le (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<nat> \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> op_le_aint \<medium_right_bracket>. .


end