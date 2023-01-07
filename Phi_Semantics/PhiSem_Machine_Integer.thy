theory PhiSem_Machine_Integer
  imports Phi_System.PhiSem_Formalization_Tools
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

lemma \<phi>Nat_semty[\<phi>reason for \<open>\<phi>SemType (?x \<Ztypecolon> \<nat>[?b]) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>[b]) (int b)\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns Big_def)

lemma [\<phi>reason for \<open>\<phi>Equal (\<nat>[?b]) ?c ?eq\<close>]:
  "\<phi>Equal (\<nat>[b]) (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (auto simp add: \<phi>expns)

lemma [\<phi>reason for \<open>\<phi>Zero (int ?b) (\<nat>[?b]) ?zero\<close>]:
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

lemma [\<phi>reason for \<open>\<phi>Zero (int ?b) \<nat>\<^sup>r[?b] ?z\<close>]:
  "\<phi>Zero (int b) (\<nat>\<^sup>r[b]) 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>NatRound_semty[\<phi>reason for \<open>\<phi>SemType (?x \<Ztypecolon> \<nat>\<^sup>r[?b]) ?ty\<close>]:
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

lemma [\<phi>reason for \<open>\<phi>Equal \<int>[b] ?c ?eq\<close>]:
    "\<phi>Equal \<int>[b] (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (cases b) (auto simp add: \<phi>expns eq_nat_nat_iff)

lemma [\<phi>reason for \<open>\<phi>Zero (int ?b) \<int>[?b] ?x\<close>]:
    "\<phi>Zero (int b) \<int>[b] 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)


lemma \<phi>Int_semty[\<phi>reason for \<open>\<phi>SemType (?x \<Ztypecolon> \<int>[?b]) ?ty\<close>]:
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


subsubsection \<open>Boolean\<close>

(* lemma [simp]: "(x \<noteq> 1) = (x = 0)" for x :: "1 word" proof -
  have "(UNIV:: 1 word set) = {0,1}" unfolding UNIV_word_eq_word_of_nat
  using less_2_cases apply auto apply force
  by (metis UNIV_I UNIV_word_eq_word_of_nat len_num1 power_one_right)
  then show ?thesis  by auto
qed *)

definition \<phi>Bool :: "(VAL, bool) \<phi>" ("\<bool>")
  where "\<bool> x = { V_int.mk (1, (if x then 1 else 0)) }"

lemma \<phi>Bool_expn[\<phi>expns]:
  " p \<in> (x \<Ztypecolon> \<bool>) \<longleftrightarrow> p = V_int.mk (1, (if x then 1 else 0))"
  unfolding \<phi>Type_def \<phi>Bool_def by simp

lemma \<phi>Bool_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<bool>) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>Bool_eqcmp[\<phi>reason for \<open>\<phi>Equal \<bool> ?c ?eq\<close>]:
  "\<phi>Equal \<bool> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns)

lemma \<phi>Bool_zero[\<phi>reason for \<open>\<phi>Zero (int 1) \<bool> ?z\<close>]:
  "\<phi>Zero (int 1) \<bool> False"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Bool_semty[\<phi>reason for \<open>\<phi>SemType (?x \<Ztypecolon> \<bool>) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<bool>) (int 1)\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns Big_def)

lemma [\<phi>reason]:
  \<open>is_singleton (x \<Ztypecolon> \<bool>)\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)

abbreviation \<open>Predicate_About x \<equiv> (\<bool> <func-over> x)\<close>


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
      Return (sem_value (V_int.mk (1, (if val_b < val_a then 1 else 0))))
  )))"

definition op_le :: "nat \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_le bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (1, (if val_b \<le> val_a then 1 else 0))))
  )))"


definition op_not :: "(VAL, VAL) proc'"
  where "op_not v =
    \<phi>M_getV (int 1) (snd o V_int.dest) v (\<lambda>v.
    Return (sem_value (V_int.mk (1, 1 - v)))
  )"

definition op_and :: "(VAL \<times> VAL, VAL) proc'"
  where "op_and =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (int 1) (snd o V_int.dest) va (\<lambda>v.
    \<phi>M_getV (int 1) (snd o V_int.dest) vb (\<lambda>u.
    Return (sem_value (V_int.mk (1, v+u-1)))
  )))"

definition op_or :: "(VAL \<times> VAL, VAL) proc'"
  where "op_or =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (int 1) (snd o V_int.dest) va (\<lambda>v.
    \<phi>M_getV (int 1) (snd o V_int.dest) vb (\<lambda>u.
    Return (sem_value (V_int.mk (1, min 1 (v+u))))
  )))"

definition op_equal :: "TY \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_equal TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV TY id va (\<lambda>v.
    \<phi>M_getV TY id vb (\<lambda>u.
    (\<lambda>res. \<phi>M_assert (Can_EqCompare res u v) res) \<ggreater>
    Return (sem_value (V_int.mk (1, (if EqCompare u v then 1 else 0))))
)))"


subsection \<open>Branches & Loops\<close>

paragraph \<open>Non-Branching Selection\<close>

definition op_sel :: "TY \<Rightarrow> (VAL \<times> VAL \<times> VAL, VAL) proc'"
  where "op_sel TY =
    \<phi>M_caseV (\<lambda>vc. \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (int 1) V_int.dest vc (\<lambda>c.
    \<phi>M_getV TY id va (\<lambda>a.
    \<phi>M_getV TY id vb (\<lambda>b.
    Return (sem_value (if snd c = 1 then b else a)))))))"

paragraph \<open>Branch\<close>

definition op_if :: "'ret proc
                  \<Rightarrow> 'ret proc
                  \<Rightarrow> (VAL,'ret) proc'"
  where "op_if brT brF v =
    \<phi>M_getV (int 1) V_int.dest v (\<lambda>c. (if snd c = 1 then brT else brF))"

paragraph \<open>While Loop\<close>

inductive SemDoWhile :: "VAL proc \<Rightarrow> resource \<Rightarrow> unit state \<Rightarrow> bool" where
  "Success (sem_value (V_int.mk (1,0))) res \<in> f s \<Longrightarrow> SemDoWhile f s (Success (sem_value ()) res)"
| "Success (sem_value (V_int.mk (1,1))) res \<in> f s \<Longrightarrow> SemDoWhile f res s'' \<Longrightarrow> SemDoWhile f s s''"
| "Exception v e \<in> f s \<Longrightarrow> SemDoWhile f s (Exception v e)"
| "PartialCorrect \<in> f s \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "Invalid \<in> f s \<Longrightarrow> SemDoWhile f s Invalid"

lemma "\<nexists> y. SemDoWhile ((\<lambda>res. Return (sem_value (V_int.mk (1,1))) res) :: VAL proc) res y"
  apply rule apply (elim exE) subgoal for y
    apply (induct "((\<lambda>res. Return (sem_value (V_int.mk (1,1))) (res::resource)) :: VAL proc)" res y
           rule: SemDoWhile.induct)
       apply (simp_all add: Return_def det_lift_def) . .

definition op_do_while :: " VAL proc \<Rightarrow> unit proc"
  where "op_do_while f s = Collect (SemDoWhile f s)"

(* lemma SemDoWhile_deterministic:
  assumes "SemDoWhile c s s1"
      and "SemDoWhile c s s2"
    shows "s1 = s2"
proof -
  have "SemDoWhile c s s1 \<Longrightarrow> (\<forall>s2. SemDoWhile c s s2 \<longrightarrow> s1 = s2)"
    apply (induct rule: SemDoWhile.induct)
    by (subst SemDoWhile.simps, simp)+
  thus ?thesis
    using assms by simp
qed

lemma SemDoWhile_deterministic2:
    "SemDoWhile body s x \<Longrightarrow> The ( SemDoWhile body s) = x"
  using SemDoWhile_deterministic by blast *)


paragraph \<open>Recursion\<close>

inductive SemRec :: "(('a,'a) proc' \<Rightarrow> ('a,'a) proc')
            \<Rightarrow> 'a sem_value \<Rightarrow> resource \<Rightarrow> 'a state set \<Rightarrow> bool"
where
  SemRec_I0: "(\<And>g. F g x res = y) \<Longrightarrow> SemRec F x res y"
| SemRec_IS: "SemRec (F o F) x res y \<Longrightarrow> SemRec F x res y"

definition op_recursion :: "TY list \<Rightarrow> TY list
                         \<Rightarrow> (('a,'a) proc' \<Rightarrow> ('a,'a) proc')
                         \<Rightarrow> ('a,'a) proc'"
  where "op_recursion _ _ F x s = (if (\<exists>t. SemRec F x s t) then The (SemRec F x s) else {})"


end