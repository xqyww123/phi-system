theory PhiSem_Machine_Integer_Lib
  imports PhiSem_Machine_Integer
begin

section \<open>Preliminary\<close>

\<phi>overloads singular and plural
\<phi>overloads split and split_cast and merge and pop and pop_cast and push

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

abbreviation LshR (infixl "LSHR" 70) where \<open>x LSHR y \<equiv> x div 2 ^ Big y\<close>
abbreviation LshL (infixl "LSHL" 70) where \<open>x LSHL y \<equiv> x  *  2 ^ Big y\<close>

definition Bits_Tag :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix "<bits>" 25) where [iff]: \<open>(x <bits> n) = x\<close>


subsection \<open>Arithmetic Operations\<close>

\<phi>overloads "+" and "-" and "*" and "/" and "<" and "\<le>" and ">" and "\<ge>" and "=" and "\<not>"
  and "\<and>" and "\<or>"

subsubsection \<open>Boolean Arithmetic\<close>

paragraph \<open>Not\<close>

bundle unfold_Big = Big_def[iff]

lemma op_not[\<phi>overload \<not>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_not raw \<lbrace> x \<Ztypecolon> Val raw \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l \<not> x \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_not_def
  including unfold_Big
  by (cases raw, simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R1\<heavy_comma> SYNTHESIS \<not>?b \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l b \<Ztypecolon> \<bool> \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l \<not>b \<Ztypecolon> \<bool>\<close>
  \<medium_left_bracket> F1 \<not> \<medium_right_bracket> .. .

paragraph \<open>And\<close>

lemma op_and[\<phi>overload \<and>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_and (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> Val va \<bool>\<heavy_comma> b \<Ztypecolon> Val vb \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l a \<and> b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_and_def including unfold_Big
  by (cases va; cases vb; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<and> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<and> y) \<Ztypecolon> \<bool>\<close>
  throws   \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 \<and> \<medium_right_bracket>. .

paragraph \<open>Or\<close>

lemma op_or[\<phi>overload \<or>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_or (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> Val va \<bool>\<heavy_comma> b \<Ztypecolon> Val vb \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l a \<or> b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_or_def including unfold_Big
  by(cases va; cases vb, simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<or> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<or> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 \<or> \<medium_right_bracket>. .

subsubsection \<open>Constant Integer\<close>

lemma op_const_int_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2 ^ Big b \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int b n \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_const_int_def Premise_def Synthesis_def
  by (rule, simp add: \<phi>expns)

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
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l numeral ?n \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 0 \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2 ^ Big b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int b n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_def GOAL_CTXT_def
  using op_const_int_\<phi>app[THEN \<phi>frame, simplified] .


lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> ?R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (?n <bits> ?b') \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (n <bits> b) \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Bits_Tag_def .


(* lemma op_const_size_t:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> Size \<rbrace>\<close>
  unfolding op_const_size_t_def Premise_def
  by (\<phi>reason, simp add: \<phi>expns Big_def) *)


(* lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (numeral ?n) \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 0 \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> Size \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_def GOAL_CTXT_def
  using op_const_size_t[THEN \<phi>frame, simplified] . *)


subsubsection \<open>Integer Arithmetic\<close>

paragraph \<open>Addition\<close>

lemma op_add[\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2 ^ Big b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def Premise_def including unfold_Big
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x + ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b]  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>x + y < 2 ^ Big b\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x + y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
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
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x - ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>y \<le> x\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x - y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 - \<medium_right_bracket>. .


paragraph \<open>Times\<close>

lemma op_omul[\<phi>overload *]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x * y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_umul b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x * y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_umul_def Premise_def including unfold_Big
  by (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x * ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>x*y < 2^b\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x * y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 * \<medium_right_bracket>. .


paragraph \<open>Division\<close>

lemma op_udiv[\<phi>overload /]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_udiv b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x div y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_udiv_def Premise_def
  apply (cases vx; cases vy; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)
  using div_le_dividend le_less_trans by blast

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x div ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x div y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
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
    \<phi>reason 1300 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x LSHR ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b1] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b2] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHR y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 op_lshr_nat \<medium_right_bracket>. .

proc [
    \<phi>reason 1300 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x LSHL ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  premises \<open>x * 2 ^ Big y < 2 ^ Big b1\<close>
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b1] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b2] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHL y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 op_lshl_nat \<medium_right_bracket>. .


paragraph \<open>Less Than\<close>

lemma op_lt[\<phi>overload <]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt b (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> Val rawx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val rawy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_lt_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns, rule,
      simp add: \<phi>expns, rule, simp add: \<phi>expns)


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x < ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x < y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 < \<medium_right_bracket>. .

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x > ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x > y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2
  ;;  \<open>\<v>1\<close> ;; \<open>\<v>0\<close> <
  \<medium_right_bracket>. .

(* Service Obligation !!!!! Last Day!!!! *)

paragraph \<open>Less Equal\<close>

lemma op_le[\<phi>overload \<le>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le b (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> Val rawx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val rawy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_le_def
  by (cases rawx; cases rawy; simp, rule, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<le> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b]  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<le> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 \<le> \<medium_right_bracket>. .


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<ge> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<ge> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1
    F2
    \<open>\<v>1\<close> \<open>\<v>0\<close> \<le> \<medium_right_bracket>. .


subsubsection \<open>General Arithmetic\<close>

paragraph \<open>Equal\<close>

lemma op_equal_\<phi>app[\<phi>overload =]:
  \<open> \<phi>SemType (a \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Equal T can_eq eq
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e can_eq a b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal TY (\<phi>V_pair rawb rawa) \<lbrace> a \<Ztypecolon> Val rawa T\<heavy_comma> b \<Ztypecolon> Val rawb T \<longmapsto> \<^bold>v\<^bold>a\<^bold>l eq a b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_equal_def
  apply (cases rawa; cases rawb; simp, rule, rule)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, rule)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, rule)
   apply (unfold \<phi>Equal_def Premise_def, simp)
  by (rule \<phi>M_Success', rule, simp add: \<phi>expns)

proc \<phi>__synthesis_eq[
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x = ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  assumes [\<phi>reason for \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason for \<open>\<phi>SemType (y \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (y \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason for \<open>\<phi>Equal T ?can_eq ?eq\<close>]: \<open>\<phi>Equal T can_eq (=)\<close>
  premises \<open>can_eq x y\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x = y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 = \<medium_right_bracket>. .

subsection \<open>Branches & Loops\<close>


lemma op_sel_\<phi>app:
  \<open> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> B) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sel TY (\<phi>V_pair rawc (\<phi>V_pair rawb rawa))
      \<lbrace> a \<Ztypecolon> Val rawa A\<heavy_comma> b \<Ztypecolon> Val rawb B\<heavy_comma> c \<Ztypecolon> Val rawc \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l (if c then a else b) \<Ztypecolon> (if c then A else B) \<rbrace>\<close>
  unfolding op_sel_def including unfold_Big
  by (cases rawc; cases rawb; cases rawa; cases c; simp add: \<phi>SemType_def subset_iff,
      rule, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>expns)

lemma branch_\<phi>app:
  \<open> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>T \<lbrace> X \<longmapsto> Y\<^sub>T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>)
\<Longrightarrow> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>F \<lbrace> X \<longmapsto> Y\<^sub>F \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>)
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T v) (Y\<^sub>F v) \<longmapsto> Y v \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if br\<^sub>T br\<^sub>F rawc \<lbrace> X\<heavy_comma> C \<Ztypecolon> Val rawc \<bool> \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. (E\<^sub>T e \<^bold>s\<^bold>u\<^bold>b\<^bold>j C) + (E\<^sub>F e \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> C) \<rbrace>\<close>
  unfolding op_if_def Premise_def Action_Tag_def including unfold_Big
  apply (cases rawc; cases C; simp; rule; simp add: \<phi>expns)
  using \<phi>CONSEQ view_shift_id by blast+


proc "if":
  assumes C: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c cond \<lbrace> X \<longmapsto> X1\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l C \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
      and brT: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brT \<lbrace> X1 \<longmapsto> Y\<^sub>T (ret::'a sem_value) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>\<close>
      and brF: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brF \<lbrace> X1 \<longmapsto> Y\<^sub>F (ret::'a sem_value) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>\<close>
      and [\<phi>reason 9999 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T ?v) (Y\<^sub>F ?v) \<longmapsto> ?Y \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
              \<open>(\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T v) (Y\<^sub>F v) \<longmapsto> Y v \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)\<close>
  argument \<open>X\<close>
  return \<open>Y (ret::'a sem_value)\<close>
  throws \<open>\<lambda>e. E e + (E\<^sub>T e \<^bold>s\<^bold>u\<^bold>b\<^bold>j C) + (E\<^sub>F e \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> C)\<close>
  \<medium_left_bracket> C branch brT brF \<medium_right_bracket>. .


section \<open>Procedures and Operations\<close>

subsection \<open>Control Flow\<close>

subsubsection \<open>Syntax for Annotations\<close>

consts Invariant :: \<open>bool \<Rightarrow> bool\<close> ("Inv: _" [37] 36)
consts Guard :: \<open>bool \<Rightarrow> bool\<close> ("Guard: _" [37] 36)


subsubsection \<open>Loops\<close>

lemma "__DoWhile__rule_\<phi>app":
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> (\<exists>*x'. X x' \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l P x' \<Ztypecolon> \<bool>) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding op_do_while_def \<phi>Procedure_def
  apply (simp add: subset_iff LooseStateTy_expn')
  apply (rule allI impI conjI)+
  subgoal for comp R s
  apply (rotate_tac 2)
    apply (induct body comp s rule: SemDoWhile.induct; clarsimp simp add: \<phi>expns times_list_def)
    apply fastforce
    subgoal premises prems for res f s s'' c u v proof -
      have t1: \<open>\<exists>c. (\<exists>fic. (\<exists>u v. fic = u * v \<and> u \<in> R \<and> v \<in> X c \<and> u ## v) \<and> s \<in> INTERP_RES fic) \<and> P c\<close>
        using prems(5) prems(6) prems(7) prems(8) prems(9) by blast
      show ?thesis
        apply (insert \<open>\<forall>_ _. (\<exists>_. _) \<longrightarrow> _\<close>[THEN spec[where x=s], THEN spec[where x=R], THEN mp, OF t1])
        using prems(1) prems(3) by fastforce
    qed
    apply fastforce
    by blast .

text \<open>Note the While rule we mentioned in the paper is just a special case of the above
      __DoWhile__rule_\<phi>app\<close>

lemma
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l P x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x'\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<and> \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<rbrace>"
  using "__DoWhile__rule_\<phi>app"[where X=\<open>\<lambda>x. X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j I x\<close> and P=P,
            simplified Subjection_times, simplified] .

proc (nodef) do_while:
assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x)\<close>
    and V: \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> cond x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA\<close>
assumes B: \<open>\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X' x \<longmapsto> (X' x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x') \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
argument \<open>X\<close>
return   \<open>X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> \<not> cond x'\<close>
throws E
  \<medium_left_bracket>
  V[unfolded Action_Tag_def]
  "__DoWhile__rule_\<phi>app"[where P=cond and X=\<open>\<lambda>x'. X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j invariant x'\<close>, simplified]
  \<medium_left_bracket> B \<medium_right_bracket>.
  \<medium_right_bracket> by simp .

(*
We fail to infer the abstract loop guard automatically but require users to give.
The main problem is about nondeterminancy in higher-order unification.
In the below rule, in \<^term>\<open>cond x' \<Ztypecolon> \<bool>\<close>, both \<open>cond\<close> and \<open>x'\<close> are schematic variables,
which means we cannot determine either of them via unification.
Even though the abstract state \<open>x'\<close> may be determined possibly in the unification of \<open>X x'\<close>,
to infer \<open>cond x'\<close> it is still a problem especially when \<open>x'\<close> is not a variable but a composite
term and its composite expression may be shattered in the expression of \<open>cond\<close> after
rewrites and simplifications, causing it is very difficult to recover the actual abstract guard
\<open>cond\<close> from simplified composition \<open>cond x'\<close>.
*)
proc while:
  assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x)\<close>
  assumes V[unfolded Action_Tag_def]:
           "\<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA"
    and C: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<lbrace> X x \<longmapsto> X x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace>"
    and B: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<lbrace> X x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace>"
  argument \<open>X'\<close>
  return \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> \<not> cond x\<close>
  \<medium_left_bracket> V C
    branch \<medium_left_bracket>
      do_while \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. Inv: invariant vars \<and> Guard: cond vars\<close>
      \<medium_left_bracket> B C \<medium_right_bracket>.
      \<medium_right_bracket>.
    \<medium_left_bracket> \<medium_right_bracket> for \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. invariant vars \<and> \<not> cond vars\<close> ..
  \<medium_right_bracket>. .



end