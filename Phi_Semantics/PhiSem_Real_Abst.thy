theory PhiSem_Real_Abst
  imports PhiSem_Common_Int HOL.Real
  abbrevs "<areal>" = "\<a>\<r>\<e>\<a>\<l>"
begin

chapter \<open>Abstract Real Numbers\<close>

section \<open>Semantics\<close>

debt_axiomatization \<a>\<r>\<e>\<a>\<l> :: TY
                and sem_mk_areal  :: \<open>real \<Rightarrow> VAL\<close>
                and sem_dest_areal :: \<open>VAL \<Rightarrow> real\<close>
where sem_dest_mk_areal[simp]: \<open>sem_dest_areal (sem_mk_areal i) = i\<close>
  and WT_areal[simp]: \<open>Well_Type \<a>\<r>\<e>\<a>\<l> = { sem_mk_areal i |i. True } \<close>
  and can_eqcmp_areal[simp]: "Can_EqCompare res (sem_mk_areal i1) (sem_mk_areal i2)"
  and eqcmp_areal[simp]: "EqCompare (sem_mk_areal i1) (sem_mk_areal i2) \<longleftrightarrow> i1 = i2"
  and  zero_areal[simp]: \<open>Zero \<a>\<r>\<e>\<a>\<l> = Some (sem_mk_areal 0)\<close>

lemma sem_mk_areal_inj[simp]:
  \<open>sem_mk_areal i = sem_mk_areal j \<longleftrightarrow> i = j\<close>
  by (metis sem_dest_mk_areal)
  

section \<open>\<phi>-Types\<close>

\<phi>type_def \<phi>AReal :: "(VAL, real) \<phi>" ("\<real>")
  where \<open>x \<Ztypecolon> \<phi>AReal \<equiv> sem_mk_areal x \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality
       and \<open>\<t>\<y>\<p>\<e>\<o>\<f> \<real> = \<a>\<r>\<e>\<a>\<l>\<close>
       and \<open>Semantic_Zero_Val \<a>\<r>\<e>\<a>\<l> \<real> 0\<close>
       and Inhabited

lemma [\<phi>reason 1000]:
    "\<phi>Equal \<real> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns eq_nat_nat_iff)


section \<open>Instructions\<close>

subsection \<open>Arithmetic Operations\<close>

(*
definition op_const_areal :: "real \<Rightarrow> VAL proc"
  where "op_const_areal const = Return (\<phi>arg (sem_mk_areal const))"
*)

definition op_add_ar :: "(VAL \<times> VAL, VAL) proc'"
  where "op_add_ar =
      \<phi>M_caseV (\<lambda>vb va.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal vb (\<lambda>val_b.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal va (\<lambda>val_a.
      Return (\<phi>arg (sem_mk_areal (val_a + val_b)))
  )))"

definition op_sub_ar :: "(VAL \<times> VAL, VAL) proc'"
  where "op_sub_ar =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal va (\<lambda>val_a.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal vb (\<lambda>val_b.
      Return (\<phi>arg (sem_mk_areal (val_a - val_b)))
  )))"

definition op_neg_ar :: "(VAL, VAL) proc'"
  where "op_neg_ar rv =
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal rv (\<lambda>v.
      Return (\<phi>arg (sem_mk_areal (-v))))"

definition op_mul_ar :: "(VAL \<times> VAL, VAL) proc'"
  where "op_mul_ar =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal va (\<lambda>val_a.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal vb (\<lambda>val_b.
      Return (\<phi>arg (sem_mk_areal (val_a * val_b)))
  )))"

definition op_div_ar :: "(VAL \<times> VAL, VAL) proc'"
  where "op_div_ar =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal va (\<lambda>val_a.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal vb (\<lambda>val_b.
      Return (\<phi>arg (sem_mk_areal (val_a / val_b)))
  )))"

definition op_ar_lt :: "(VAL \<times> VAL, VAL) proc'"
  where "op_ar_lt =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal va (\<lambda>val_a.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal vb (\<lambda>val_b.
      Return (\<phi>arg (sem_mk_bool (val_a < val_b)))
  )))"

definition op_ar_le :: "(VAL \<times> VAL, VAL) proc'"
  where "op_ar_le =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal va (\<lambda>val_a.
      \<phi>M_getV \<a>\<r>\<e>\<a>\<l> sem_dest_areal vb (\<lambda>val_b.
      Return (\<phi>arg (sem_mk_bool (val_a \<le> val_b)))
  )))"


section \<open>Abstraction of Instructions\<close>

subsubsection \<open>Constant\<close>

lemma op_const_areal_\<phi>app[\<phi>reason %\<phi>synthesis_literal_number]:
  \<open> Is_Literal x
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Val (semantic_literal (sem_mk_areal x)) \<real> \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
\<medium_left_bracket>
  semantic_literal \<open>sem_mk_areal x \<Turnstile> (x \<Ztypecolon> \<real>)\<close>
\<medium_right_bracket> .

lemma [\<phi>reason %\<phi>synthesis_parse_number
    for \<open>Synthesis_Parse (numeral ?n::real) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (1::real) (?X :: ?'ret \<Rightarrow> assn)\<close>
       \<open>Synthesis_Parse (0::real) (?X :: ?'ret \<Rightarrow> assn)\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<real>) X
\<Longrightarrow> Synthesis_Parse n X\<close>
  for X :: \<open>'ret \<Rightarrow> assn\<close>
  unfolding Synthesis_Parse_def ..


subsubsection \<open>Integer Arithmetic\<close>

paragraph \<open>Addition\<close>
 
lemma op_add_areal_\<phi>app
  [\<phi>overload +,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close> \<Rightarrow> \<open>\<lambda>v. x + y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_add_ar (vx\<^bold>, vy) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<real> \<longmapsto> \<v>\<a>\<l> x + y \<Ztypecolon> \<real> \<rbrace> \<close>
  unfolding op_add_ar_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp)

paragraph \<open>Subtraction\<close>

lemma op_sub_areal_\<phi>app
  [\<phi>overload -,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close> \<Rightarrow> \<open>\<lambda>v. x - y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_sub_ar (vx\<^bold>, vy) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<real> \<longmapsto> \<v>\<a>\<l> x - y \<Ztypecolon> \<real> \<rbrace>\<close>
  unfolding op_sub_ar_def Premise_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp)

paragraph \<open>Negation\<close>

lemma op_neg_areal_\<phi>app
  [\<phi>overload ~,
   \<phi>synthesis %synthesis_arith for _
              and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<close> \<Rightarrow> \<open>\<lambda>v. - x \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_neg_ar rv \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> \<v>\<a>\<l> -x \<Ztypecolon> \<real> \<rbrace> \<close>
  unfolding op_neg_ar_def Premise_def
  by (cases rv; simp, rule, simp, rule, simp)


paragraph \<open>Times\<close>

lemma op_mul_areal[\<phi>overload *,
                  \<phi>synthesis %synthesis_arith for _
                             and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close> \<Rightarrow> \<open>\<lambda>v. x * y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open> \<p>\<r>\<o>\<c> op_mul_ar (vx\<^bold>, vy) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<real> \<longmapsto> \<v>\<a>\<l> x * y \<Ztypecolon> \<real> \<rbrace>\<close>
  unfolding op_mul_ar_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp)


paragraph \<open>Division\<close>

lemma op_div_areal_\<phi>app[\<phi>overload /,
                        \<phi>synthesis %synthesis_arith for _
                                   and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close> \<Rightarrow> \<open>\<lambda>v. x div y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_div_ar (vx\<^bold>, vy) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[vx] \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] \<real> \<longmapsto> \<v>\<a>\<l> x div y \<Ztypecolon> \<real> \<rbrace>\<close>
  unfolding op_div_ar_def
  by (cases vx; cases vy; simp, rule, rule, simp, rule, simp, rule, simp)


paragraph \<open>Less Than\<close>

lemma op_lt_areal[\<phi>overload <,
                 \<phi>synthesis %synthesis_arith for _
                            and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close> \<Rightarrow> \<open>\<lambda>v. x < y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_ar_lt (rawx\<^bold>, rawy) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<real> \<longmapsto> \<v>\<a>\<l> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_ar_lt_def
  by (cases rawx; cases rawy; simp, rule, rule, simp, rule, simp, rule, simp)
 
proc (nodef) op_gt_areal[\<phi>overload >]:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  output \<open>\<v>\<a>\<l> x > y \<Ztypecolon> \<bool>\<close>
\<medium_left_bracket>
  $y < $x
\<medium_right_bracket>.

paragraph \<open>Less Equal\<close>

lemma op_le_areal_\<phi>app[\<phi>overload \<le>,
                      \<phi>synthesis %synthesis_arith for _
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close> \<Rightarrow> \<open>\<lambda>v. x \<le> y \<Ztypecolon> _\<close> (%synthesis_arith_cut)]:
  \<open>\<p>\<r>\<o>\<c> op_ar_le (rawx\<^bold>, rawy) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rawx] \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[rawy] \<real> \<longmapsto> \<v>\<a>\<l> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_ar_le_def
  by (cases rawx; cases rawy; simp, rule, rule, simp, rule, simp, rule, simp)

proc (nodef) op_ge_areal[\<phi>overload \<ge>]:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  output \<open>\<v>\<a>\<l> x \<ge> y \<Ztypecolon> \<bool>\<close>
\<medium_left_bracket>
  $y \<le> $x
\<medium_right_bracket>.


end