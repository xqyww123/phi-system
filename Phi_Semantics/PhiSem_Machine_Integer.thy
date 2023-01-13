theory PhiSem_Machine_Integer
  imports Phi_System.PhiSem_Formalization_Tools PhiSem_Generic_Boolean
begin

chapter \<open>Semantics for Machine Integers\<close>

section \<open>Preliminary\<close>

no_notation inter (infixl "Int" 70) and union (infixl "Un" 65)

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype \<phi>min_ty = \<phi>empty_ty +
  T_int     :: nat \<comment> \<open>in unit of bits\<close>

context \<phi>min_ty begin
abbreviation int where \<open>int \<equiv> T_int.mk\<close>
end

debt_axiomatization T_int :: \<open>nat type_entry\<close>
  where \<phi>min_ty_ax: \<open>\<phi>min_ty TY_CONS_OF T_int\<close>

interpretation \<phi>min_ty TY_CONS_OF _ _ T_int using \<phi>min_ty_ax .

hide_fact \<phi>min_ty_ax \<phi>min_ty_axioms \<phi>min_ty_names_def \<phi>min_ty_def
  \<phi>min_ty_prjs_axioms \<phi>min_ty_prjs_def \<phi>min_ty.axioms \<phi>min_ty.intro
  \<phi>min_ty__names.\<phi>min_ty_names_axioms \<phi>min_ty_prjs.axioms

subsubsection \<open>Value\<close>

virtual_datatype \<phi>min_val = \<phi>empty_val +
  V_int     :: \<open>nat \<times> nat\<close> \<comment> \<open>bits \<times> value\<close>

debt_axiomatization V_int :: \<open>(nat \<times> nat) value_entry\<close>
  where \<phi>min_val_ax: \<open>\<phi>min_val VAL_CONS_OF V_int\<close>

interpretation \<phi>min_val VAL_CONS_OF _ _ V_int using \<phi>min_val_ax .

hide_fact \<phi>min_val_ax \<phi>min_val_axioms

subsubsection \<open>Semantics\<close>

debt_axiomatization
    WT_int[simp]: \<open>Well_Type (int b)     = { V_int.mk (b,x)    |x. x < 2 ^ Big b } \<close>
and can_eqcmp_int[simp]: "Can_EqCompare res (V_int.mk (b1,x1)) (V_int.mk (b2,x2)) \<longleftrightarrow> b1 = b2"
and eqcmp_int[simp]: "EqCompare (V_int.mk i1) (V_int.mk i2) \<longleftrightarrow> i1 = i2"
and  zero_int[simp]: \<open>Zero (int b)    = Some (V_int.mk (b,0))\<close>

lemma Valid_Types[simp]:
  \<open>Valid_Type (int n)\<close>
  unfolding Inhabited_def
  apply simp
  using less_exp by blast


section \<open>\<phi>-Types\<close>

\<phi>overloads nat and int

subsection \<open>Integer\<close>

subsubsection \<open>Natural Nmbers\<close>

paragraph \<open>Natural Number\<close>

definition \<phi>Nat :: "nat \<Rightarrow> (VAL, nat) \<phi>" ("\<nat>[_]")
  where "\<nat>[b] x = (if x < 2^b then { V_int.mk (b,x) } else {})"

lemma \<phi>Nat_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>[b]) \<longleftrightarrow> (p = V_int.mk (b,x)) \<and> x < 2 ^ Big b"
  unfolding \<phi>Type_def Big_def by (simp add: \<phi>Nat_def)

lemma \<phi>Nat_elim[elim!,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> \<nat>[b]) \<Longrightarrow> (x < 2 ^ Big b \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<open>Inhabited (x \<Ztypecolon> \<nat>[b]) \<longleftrightarrow> x < 2^Big b\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Nat_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>[b]) (int b)\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns Big_def)

lemma [\<phi>reason 1000]:
  "\<phi>Equal (\<nat>[b]) (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (auto simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  "\<phi>Zero (int b) (\<nat>[b]) 0" unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^Big b
\<Longrightarrow> is_singleton (x \<Ztypecolon> \<nat>[b])\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)

paragraph \<open>Rounded Natural Number\<close>

definition \<phi>NatRound :: "nat \<Rightarrow> (VAL, nat) \<phi>" ("\<nat>\<^sup>r[_]")
  where "\<nat>\<^sup>r[b] x = { V_int.mk (b, (x mod 2 ^ Big b)) }"

lemma \<phi>NatRound_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>\<^sup>r[b]) \<longleftrightarrow> p = V_int.mk (b, (x mod 2 ^ Big b))"
  unfolding \<phi>Type_def \<phi>NatRound_def by simp

lemma \<open>Inhabited (x \<Ztypecolon> \<nat>\<^sup>r[b]) \<longleftrightarrow> True\<close>
  unfolding Inhabited_def by (auto simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  "\<phi>Zero (int b) (\<nat>\<^sup>r[b]) 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>NatRound_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>\<^sup>r[b]) (int b)\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)


subsubsection \<open>Integer in the normal sense\<close>

definition \<phi>Int :: "nat \<Rightarrow> (VAL, int) \<phi>" ("\<int>[_]")
  where "\<phi>Int b x =(if x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0)
                    then { V_int.mk (b, (if x \<ge> 0 then nat x else nat (2^b + x))) }
                    else {})"

lemma \<phi>Int_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<int>[b]) \<longleftrightarrow> p = V_int.mk (b, (if x \<ge> 0 then nat x else nat (2^b + x)))
                      \<and> x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0)"
  unfolding \<phi>Type_def by (simp add: \<phi>Int_def)

lemma \<phi>Int_inhabited[elim!,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> \<int>[b]) \<Longrightarrow> (x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) 

lemma [simp]: \<open>- (2^(b - 1)) \<le> x \<Longrightarrow> 0 \<le> 2 ^ b + x\<close> for x :: int
  by (smt (verit, best) diff_le_self power_increasing_iff)

lemma [\<phi>reason 1000]:
    "\<phi>Equal \<int>[b] (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (cases b) (auto simp add: \<phi>expns eq_nat_nat_iff)

lemma [\<phi>reason 1000]:
    "\<phi>Zero (int b) \<int>[b] 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)


lemma \<phi>Int_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<int>[b]) (int b)\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns Big_def) (smt (verit, ccfv_SIG) diff_le_self power_increasing_iff)


subsubsection \<open>Subtyping\<close>

lemma subty_Z_N[\<phi>overload nat]: 
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < x \<Longrightarrow> x \<Ztypecolon> \<int>[b] \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s nat x \<Ztypecolon> \<nat>[b]"
  unfolding Imply_def Premise_def apply (simp add: \<phi>expns Big_def del: One_nat_def)
  by (smt (verit, del_insts) diff_less less_numeral_extra(1) power_strict_increasing_iff)

lemma subty_N_Z[\<phi>overload int]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^(b - 1) \<Longrightarrow> x \<Ztypecolon> \<nat>[b] \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Int.int x \<Ztypecolon> \<int>[b]"
  unfolding Imply_def Premise_def apply (simp add: \<phi>expns Big_def del: One_nat_def)
  by (metis less_one linorder_le_cases neg_0_le_iff_le not_exp_less_eq_0_int of_nat_0_le_iff order_trans power_0)


section \<open>Instructions\<close>

subsection \<open>Arithmetic Operations\<close>

subsubsection \<open>Integer arithmetic\<close>

definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> VAL proc"
  where "op_const_int bits const = Return (sem_value (V_int.mk (bits,const)))"

(* definition op_const_size_t :: "nat \<Rightarrow> (VAL,VAL,'RES_N,'RES) proc"
  where "op_const_size_t c = \<phi>M_assume (c < 2 ^ addrspace_bits)
                          \<ggreater> Return (sem_value (V_int.mk (addrspace_bits,c)))"
  \<comment> \<open> `op_const_size_t` checks the overflow during the compilation towards certain decided platform.  \<close>
*)

definition op_add :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_add bits =
      \<phi>M_caseV (\<lambda>vb va.
      \<phi>M_getV (int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      \<phi>M_getV (int bits) (snd o V_int.dest) va (\<lambda>val_a.
      Return (sem_value (V_int.mk (bits, ((val_a + val_b) mod 2^bits))))
  )))"

definition op_sub :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_sub bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (bits, ((2^bits + val_b - val_a) mod 2^bits))))
  )))"

definition op_umul :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_umul bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (bits, ((val_b * val_a) mod 2^bits))))
  )))"

definition op_udiv :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_udiv bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (bits, (val_b div val_a))))
  )))"

definition op_lshr :: "nat \<Rightarrow> nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_lshr b_b b_a =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int b_a) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int b_b) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (b_b, (val_b div 2 ^ val_a))))
  )))"

definition op_lshl :: "nat \<Rightarrow> nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_lshl b_b b_a =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int b_a) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int b_b) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (b_b, (val_b * 2 ^ val_a))))
  )))"

definition op_lt :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_lt bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_bool.mk (val_b < val_a)))
  )))"

definition op_le :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_le bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_bool.mk (val_b \<le> val_a)))
  )))"



section \<open>Abstraction of Instructions\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

abbreviation LshR (infixl "LSHR" 70) where \<open>x LSHR y \<equiv> x div 2 ^ Big y\<close>
abbreviation LshL (infixl "LSHL" 70) where \<open>x LSHL y \<equiv> x  *  2 ^ Big y\<close>

definition Bits_Tag :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix "<bits>" 25) where [iff]: \<open>(x <bits> n) = x\<close>


subsection \<open>Arithmetic Operations\<close>

\<phi>overloads "+" and "-" and "*" and "/" and "<" and "\<le>" and ">" and "\<ge>" and "=" and "\<not>"
  and "\<and>" and "\<or>"

bundle unfold_Big = Big_def[iff]

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
  unfolding Synthesis_def Action_Tag_def
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
  unfolding Synthesis_def Action_Tag_def
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
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x + y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
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
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x - y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
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
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x * y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
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
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x div y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
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
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHR y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
  \<medium_left_bracket> F1 F2 op_lshr_nat \<medium_right_bracket>. .

proc [
    \<phi>reason 1300 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x LSHL ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  premises \<open>x * 2 ^ Big y < 2 ^ Big b1\<close>
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b1] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b2] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHL y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
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
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x < y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
  \<medium_left_bracket> F1 F2 < \<medium_right_bracket>. .


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x > ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x > y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
  \<medium_left_bracket> F1 \<rightarrow> val v1
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
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<le> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b]  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<le> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
  \<medium_left_bracket> F1 F2 \<le> \<medium_right_bracket>. .


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<ge> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  input \<open>R\<close>
  output   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<ge> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  goal \<open>subgoal_context G\<close>
  \<medium_left_bracket> 
    F1 \<rightarrow> val v1
    F2 \<rightarrow> val v2
    $v2 $v1 \<le>
  \<medium_right_bracket>. .



end