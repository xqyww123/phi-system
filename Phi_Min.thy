theory Phi_Min
  imports NuSys NuInstructions
begin

chapter \<open>Minimal Semantics\<close>

text \<open>This minimal semantics contains integer and variable.\<close>

section \<open>Semantic\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype \<phi>min_ty = \<phi>empty_ty +
  T_int     :: nat \<comment> \<open>in unit of bits\<close>

context \<phi>min_ty begin
abbreviation \<open>\<tau>Int \<equiv> T_int.mk\<close>
end

subsubsection \<open>Value\<close>

virtual_datatype 'TY \<phi>min_val :: "nonsepable_semigroup" = 'TY \<phi>empty_val +
  V_int     :: \<open>nat \<times> nat\<close> \<comment> \<open>bits \<times> value\<close>

subsubsection \<open>Resource\<close>

typedef varname = \<open>UNIV::nat set\<close> ..
type_synonym ('TY,'VAL) R_var = \<open>varname \<rightharpoonup> 'VAL\<close>

lemma infinite_varname:
  \<open>infinite (UNIV::varname set)\<close>
  by (metis (mono_tags, opaque_lifting) Rep_varname_cases UNIV_I finite_imageI infinite_UNIV_char_0 surj_def)

resource_space ('VAL::nonsepable_semigroup,'TY) \<phi>min_res = ('VAL,'TY) \<phi>empty_res +
  R_var :: \<open>('TY,'VAL) R_var\<close>

subsubsection \<open>Pure Semantics\<close>

locale \<phi>min_sem =
  \<phi>empty_sem where TYPES = TYPES
+ \<phi>min_ty  where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ \<phi>min_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ \<phi>min_res where TYPE'VAL  = \<open>TYPE('VAL)\<close>
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('RES_N)\<close>
            and TYPE'REP  = \<open>TYPE('RES::sep_algebra)\<close>
+ \<phi>resource_sem where Resource_Validator = Resource_Validator
for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N => 'VAL::nonsepable_semigroup)
                \<times> ('RES_N => 'RES::sep_algebra)) itself\<close>
+
assumes WT_int[simp]: \<open>Well_Type (\<tau>Int b)     = { V_int.mk (b,x)    |x. x < 2 ^ Big b } \<close>
assumes res_valid_var[simp]: \<open>Resource_Validator R_var.name = {R_var.inject vars |vars. finite (dom vars)}\<close>
assumes can_eqcmp_int[simp]: "Can_EqCompare res (V_int.mk (b1,x1)) (V_int.mk (b2,x2)) \<longleftrightarrow> b1 = b2"
assumes eqcmp_int[simp]: "EqCompare (V_int.mk i1) (V_int.mk i2) \<longleftrightarrow> i1 = i2"
assumes zero_int[simp]: \<open>Zero (T_int.mk b)    = Some (V_int.mk (b,0))\<close>

begin

lemma Valid_Types[simp]:
  \<open>Valid_Type (\<tau>Int n)\<close>
  unfolding Inhabited_def
  apply (simp)
  using less_exp by blast

sublocale R_var: partial_map_resource \<open>{vars. finite (dom vars)}\<close> R_var
  by (standard; simp add: set_eq_iff image_iff; blast)

end

fiction_space (in \<phi>min_sem) \<phi>min_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> =
  FIC_var :: \<open>R_var.raw_basic_fiction fiction.it\<close>

locale \<phi>min =
  \<phi>min_fic where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                            \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra))\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::sep_algebra)\<close> 
+ \<phi>empty where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                          \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                          \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra)
                          \<times> ('FIC_N \<Rightarrow> 'FIC))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>
begin

sublocale FIC_var: identity_fiction \<open>{vars. finite (dom vars)}\<close> R_var
    Resource_Validator INTERPRET FIC_var ..

end

section \<open>\<phi>-Types\<close>

context \<phi>min_sem begin

subsection \<open>Integer\<close>

\<phi>overloads nat and int

subsubsection \<open>Natural Nmbers\<close>

paragraph \<open>Natural Number\<close>

definition \<phi>Nat :: "nat \<Rightarrow> ('VAL, nat) \<phi>" ("\<nat>[_]")
  where "\<nat>[b] x = (if x < 2^b then { V_int.mk (b,x) } else {})"

abbreviation \<open>Size \<equiv> \<nat>[addrspace_bits]\<close>

lemma \<phi>Nat_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>[b]) \<longleftrightarrow> (p = V_int.mk (b,x)) \<and> x < 2 ^ Big b"
  unfolding \<phi>Type_def Big_def by (simp add: \<phi>Nat_def)

lemma \<phi>Nat_elim[elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> \<nat>[b]) \<Longrightarrow> (x < 2 ^ Big b \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma
  \<open>Inhabited (x \<Ztypecolon> \<nat>[b]) \<longleftrightarrow> x < 2^Big b\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Nat_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<nat>[?b]) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>[b]) (\<tau>Int b)\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns Big_def)

lemma [\<phi>reason on \<open>\<phi>Equal (\<nat>[?b]) ?c ?eq\<close>]:
  "\<phi>Equal (\<nat>[b]) (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (auto simp add: \<phi>expns)

lemma [\<phi>reason on \<open>\<phi>Zero (T_int.mk ?b) (\<nat>[?b]) ?zero\<close>]:
  "\<phi>Zero (T_int.mk b) (\<nat>[b]) 0" unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^Big b
\<Longrightarrow> is_singleton (x \<Ztypecolon> \<nat>[b])\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)

paragraph \<open>Rounded Natural Number\<close>

definition \<phi>NatRound :: "nat \<Rightarrow> ('VAL, nat) \<phi>" ("\<nat>\<^sup>r[_]")
  where "\<nat>\<^sup>r[b] x = { V_int.mk (b, (x mod 2 ^ Big b)) }"

lemma \<phi>NatRound_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>\<^sup>r[b]) \<longleftrightarrow> p = V_int.mk (b, (x mod 2 ^ Big b))"
  unfolding \<phi>Type_def \<phi>NatRound_def by simp

lemma
  \<open>Inhabited (x \<Ztypecolon> \<nat>\<^sup>r[b]) \<longleftrightarrow> True\<close>
  unfolding Inhabited_def by (auto simp add: \<phi>expns)

lemma [\<phi>reason on \<open>\<phi>Zero (T_int.mk ?b) \<nat>\<^sup>r[?b] ?z\<close>]:
  "\<phi>Zero (T_int.mk b) (\<nat>\<^sup>r[b]) 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>NatRound_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<nat>\<^sup>r[?b]) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>\<^sup>r[b]) (\<tau>Int b)\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

subsubsection \<open>Integer in the normal sense\<close>


definition \<phi>Int :: "nat \<Rightarrow> ('VAL, int) \<phi>" ("\<int>[_]")
  where "\<phi>Int b x =(if x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0)
                    then { V_int.mk (b, (if x \<ge> 0 then nat x else nat (2^b + x))) }
                    else {})"

lemma \<phi>Int_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<int>[b]) \<longleftrightarrow> p = V_int.mk (b, (if x \<ge> 0 then nat x else nat (2^b + x)))
                      \<and> x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0)"
  unfolding \<phi>Type_def by (simp add: \<phi>Int_def)

lemma \<phi>Int_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> \<int>[b]) \<Longrightarrow> (x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) 


lemma [simp]: \<open>- (2^(b - 1)) \<le> x \<Longrightarrow> 0 \<le> 2 ^ b + x\<close> for x :: int
  by (smt (verit, best) diff_le_self power_increasing_iff)

lemma [\<phi>reason on \<open>\<phi>Equal \<int>[b] ?c ?eq\<close>]:
    "\<phi>Equal \<int>[b] (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (cases b) (auto simp add: \<phi>expns eq_nat_nat_iff)

lemma [\<phi>reason on \<open>\<phi>Zero (T_int.mk ?b) \<int>[?b] ?x\<close>]:
    "\<phi>Zero (T_int.mk b) \<int>[b] 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Int_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<int>[?b]) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<int>[b]) (\<tau>Int b)\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns Big_def) (smt (verit, ccfv_SIG) diff_le_self power_increasing_iff)


subsubsection \<open>Subtyping\<close>

lemma subty_Z_N[\<phi>overload nat]: 
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < x \<Longrightarrow> x \<Ztypecolon> \<int>[b] \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s nat x \<Ztypecolon> \<nat>[b]"
  unfolding Imply_def Premise_def apply (simp add: \<phi>expns Big_def del: One_nat_def)
  by (smt (verit, del_insts) diff_less less_numeral_extra(1) power_strict_increasing_iff)

lemma subty_N_Z[\<phi>overload int]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^(b - 1) \<Longrightarrow> x \<Ztypecolon> \<nat>[b] \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s int x \<Ztypecolon> \<int>[b]"
  unfolding Imply_def Premise_def apply (simp add: \<phi>expns Big_def del: One_nat_def)
  by (metis less_one linorder_le_cases neg_0_le_iff_le not_exp_less_eq_0_int of_nat_0_le_iff order_trans power_0)


subsubsection \<open>Boolean\<close>

(* lemma [simp]: "(x \<noteq> 1) = (x = 0)" for x :: "1 word" proof -
  have "(UNIV:: 1 word set) = {0,1}" unfolding UNIV_word_eq_word_of_nat
  using less_2_cases apply auto apply force
  by (metis UNIV_I UNIV_word_eq_word_of_nat len_num1 power_one_right)
  then show ?thesis  by auto
qed *)

definition \<phi>Bool :: "('VAL, bool) \<phi>" ("\<bool>")
  where "\<bool> x = { V_int.mk (1, (if x then 1 else 0)) }"

lemma \<phi>Bool_expn[\<phi>expns]:
  " p \<in> (x \<Ztypecolon> \<bool>) \<longleftrightarrow> p = V_int.mk (1, (if x then 1 else 0))"
  unfolding \<phi>Type_def \<phi>Bool_def by simp

lemma \<phi>Bool_inhabited[\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<bool>) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>Bool_eqcmp[\<phi>reason on \<open>\<phi>Equal \<bool> ?c ?eq\<close>]:
  "\<phi>Equal \<bool> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns)

lemma \<phi>Bool_zero[\<phi>reason on \<open>\<phi>Zero (\<tau>Int 1) \<bool> ?z\<close>]:
  "\<phi>Zero (\<tau>Int 1) \<bool> False"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Bool_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<bool>) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<bool>) (\<tau>Int 1)\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns Big_def)

lemma [\<phi>reason]:
  \<open>is_singleton (x \<Ztypecolon> \<bool>)\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)


abbreviation \<open>Predicate_About x \<equiv> (\<bool> <func-over> x)\<close>

end


subsection \<open>Variable\<close>

context \<phi>min begin

abbreviation Var :: \<open>varname \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set\<close>
  where \<open>Var vname T \<equiv> (FIC_var.\<phi> (vname \<^bold>\<rightarrow> \<black_circle> T))\<close>

lemma Var_inhabited[\<phi>reason_elim!,elim!]:
  \<open>Inhabited (x \<Ztypecolon> Var vname T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Var_subty:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> Var vname T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> Var vname T' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma Var_view_shift:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> Var vname T \<longmapsto> x' \<Ztypecolon> Var vname T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Imply_def View_Shift_def by (clarsimp simp add: \<phi>expns, blast)

lemma Var_cast_\<phi>app[\<phi>overload cast]: 
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w FIX x \<Ztypecolon> Var vname T \<longmapsto> x' \<Ztypecolon> Var vname T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Argument_def Fix_def
  using Var_view_shift .

(* lemma Var_ExTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (ExTyp T)) = (\<exists>*a. x a \<Ztypecolon> Var vname (T a))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma Var_SubjTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (x \<Ztypecolon> Var vname T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns) *)

lemma [\<phi>reason 1200 on \<open>EqualAddress (?xa \<Ztypecolon> Var ?va ?Ta) (?xb \<Ztypecolon> Var ?vb ?Tb)\<close>]:
  \<open>EqualAddress (xa \<Ztypecolon> Var var Ta) (xb \<Ztypecolon> Var var Tb)\<close>
  unfolding EqualAddress_def ..

lemma [\<phi>reason 1300 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> x \<Ztypecolon> Var var T \<longmapsto> R\<heavy_comma> \<blangle> x' \<Ztypecolon> Var var T' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding GOAL_CTXT_def FOCUS_TAG_def
  by (simp add: Var_view_shift \<phi>frame_view) 

lemma Var_simp_cong:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Var v T) = (x' \<Ztypecolon> Var v T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup Var_simp_cong ("x \<Ztypecolon> Var v T") = \<open>
  K (NuSimpCong.simproc @{thm Var_simp_cong[folded atomize_eq]})
\<close>



subsubsection \<open>Application Methods for Subtyping\<close>

lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> if no \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Var ?var ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def Fix_def] implies_left_prod
  by (metis Var_subty)


lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?x' \<Ztypecolon> ?T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> if no \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Var ?var ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x' \<Ztypecolon> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def Fix_def] implies_left_prod
  by (metis Var_subty)


subsubsection \<open>Branch Convergence Rules\<close>

lemma [\<phi>reason 1200 on
  \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?R1 \<heavy_comma> ?x \<Ztypecolon> Var ?v ?T) (?N \<heavy_comma> \<blangle> ?R2 \<heavy_comma> ?y \<Ztypecolon> Var ?v' ?U \<brangle>) = ?X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (x \<Ztypecolon> T) (y \<Ztypecolon> U) = (z \<Ztypecolon> Z)
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P R1 (1 \<heavy_comma> \<blangle> N \<heavy_comma> R2 \<brangle>) = R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (R1 \<heavy_comma> x \<Ztypecolon> Var v T) (N \<heavy_comma> \<blangle> R2 \<heavy_comma> y \<Ztypecolon> Var v U \<brangle>) = (R \<heavy_comma> z \<Ztypecolon> Var v Z) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def Merge_def by (cases P; simp add: \<phi>expns mult.assoc)

declare branch_convergence_skip[\<phi>reason 1200
     on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?R1 \<heavy_comma> ?x \<Ztypecolon> Var ?v ?T) (?N \<heavy_comma> \<blangle> ?R2 \<heavy_comma> ?Y \<brangle>) = ?R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  if no \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?R1 \<heavy_comma> ?x \<Ztypecolon> Var ?v ?T) (?N \<heavy_comma> \<blangle> ?R2 \<heavy_comma> ?y \<Ztypecolon> Var ?v' ?U \<brangle>) = ?R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?rG\<close>
]

end


section \<open>Instructions\<close>

context \<phi>min_sem begin

subsection \<open>Arithmetic Operations\<close>

subsubsection \<open>Integer arithmetic\<close>

definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc"
  where "op_const_int bits const = Return (sem_value (V_int.mk (bits,const)))"

definition op_const_size_t :: "nat \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc"
  where "op_const_size_t c = \<phi>M_assume (c < 2 ^ addrspace_bits)
                          \<ggreater> Return (sem_value (V_int.mk (addrspace_bits,c)))"
  \<comment> \<open> `op_const_size_t` checks the overflow during the compilation towards certain decided platform.  \<close>

definition op_add :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'VAL, 'RES_N, 'RES) proc'"
  where "op_add bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (bits, ((val_a + val_b) mod 2^bits))))
  )))"


(* lemma (in \<phi>empty) op_add:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b (\<phi>V_pair vb va) \<lbrace> x \<Ztypecolon> Val va \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vb \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def Premise_def
  by (cases va; cases vb; simp, \<phi>reason) *)


(* lemma (in \<phi>empty)
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c left  \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c right \<lbrace> R2 \<longmapsto> R3\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (left \<ggreater> right \<ggreater> op_add b) \<lbrace> R1 \<longmapsto> R3\<heavy_comma> SYNTHESIS x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  apply (\<phi>reason, assumption) *)

definition op_sub :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'VAL, 'RES_N, 'RES) proc'"
  where "op_sub bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (bits, ((2^bits + val_b - val_a) mod 2^bits))))
  )))"

definition op_umul :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'VAL, 'RES_N, 'RES) proc'"
  where "op_umul bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (bits, ((val_b * val_a) mod 2^bits))))
  )))"

definition op_udiv :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'VAL, 'RES_N, 'RES) proc'"
  where "op_udiv bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (bits, (val_b div val_a))))
  )))"

definition op_lt :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL,'VAL,'RES_N,'RES) proc'"
  where "op_lt bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (1, (if val_b < val_a then 1 else 0))))
  )))"


definition op_le :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL,'VAL,'RES_N,'RES) proc'"
  where "op_le bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Return (sem_value (V_int.mk (1, (if val_b \<le> val_a then 1 else 0))))
  )))"


definition op_not :: "('VAL, 'VAL,'VAL,'RES_N,'RES) proc'"
  where "op_not v =
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) v (\<lambda>v.
    Return (sem_value (V_int.mk (1, 1 - v)))
  )"

definition op_and :: "('VAL \<times> 'VAL, 'VAL,'VAL,'RES_N,'RES) proc'"
  where "op_and =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) va (\<lambda>v.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) vb (\<lambda>u.
    Return (sem_value (V_int.mk (1, v+u-1)))
  )))"

definition op_or :: "('VAL \<times> 'VAL, 'VAL,'VAL,'RES_N,'RES) proc'"
  where "op_or =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) va (\<lambda>v.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) vb (\<lambda>u.
    Return (sem_value (V_int.mk (1, min 1 (v+u))))
  )))"

definition op_equal :: "'TY \<Rightarrow> ('VAL \<times> 'VAL, 'VAL,'VAL,'RES_N,'RES) proc'"
  where "op_equal TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV TY id va (\<lambda>v.
    \<phi>M_getV TY id vb (\<lambda>u.
    (\<lambda>res. \<phi>M_assert (Can_EqCompare res u v) res) \<ggreater>
    Return (sem_value (V_int.mk (1, (if EqCompare u v then 1 else 0))))
)))"




subsection \<open>Variable Operations\<close>

definition \<phi>M_get_var
    :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL \<Rightarrow> ('ret,'VAL,'RES_N,'RES) proc) \<Rightarrow> ('ret,'VAL,'RES_N,'RES) proc"
  where "\<phi>M_get_var vname TY F = R_var.\<phi>R_get_res_entry vname (\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type TY) \<ggreater> F val)"

definition op_get_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc"
  where "op_get_var vname TY = \<phi>M_get_var vname TY (\<lambda>x. Return (sem_value x))"

definition op_set_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL, unit,'VAL,'RES_N,'RES) proc'"
  where "op_set_var vname TY v =
          \<phi>M_getV TY id v (\<lambda>v.
          \<phi>M_get_var vname TY (\<lambda>_.
          R_var.\<phi>R_set_res (\<lambda>f. f(vname := Some v))))"

definition op_free_var :: "varname \<Rightarrow> (unit,'VAL,'RES_N,'RES) proc"
  where "op_free_var vname = R_var.\<phi>R_set_res (\<lambda>f. f(vname := None))"

definition op_var_scope' :: "'TY
                          \<Rightarrow> (varname \<Rightarrow> ('ret,'VAL,'RES_N,'RES) proc)
                          \<Rightarrow> ('VAL,'ret,'VAL,'RES_N,'RES) proc'"
  where "op_var_scope' TY F v =
    \<phi>M_getV TY id v (\<lambda>v.
    R_var.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some v) F
  )"

lemma (in \<phi>min) \<phi>M_get_var[\<phi>reason!]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_var vname TY F \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec \<phi>M_get_var_def
  by (clarsimp simp add: \<phi>expns FIC_var.expand simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_get_res_entry[where v=v]; simp)

lemma (in \<phi>min) \<phi>M_set_var[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c R_var.\<phi>R_set_res (\<lambda>f. f(vname \<mapsto> u)) \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  thm  FIC_var.expand_subj[where x=\<open>1(vname \<mapsto> u)\<close>]
  by (clarsimp simp add: \<phi>expns FIC_var.expand[where x=\<open>1(vname \<mapsto> v)\<close>]
                                FIC_var.expand_subj[where x=\<open>1(vname \<mapsto> u)\<close>]
               simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_set_res[where P=\<open>\<lambda>_. True\<close>]; simp)

lemma (in \<phi>min) op_get_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var vname TY \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> v \<Ztypecolon> Var vname Identity \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding op_get_var_def Premise_def
  by (\<phi>reason, assumption, \<phi>reason)

end


lemma (in \<phi>min) op_set_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_var vname TY rawv \<lbrace> v \<Ztypecolon> Var vname Identity\<heavy_comma> u \<Ztypecolon> Val rawv Identity \<longmapsto> u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding op_set_var_def Premise_def
  by (cases rawv; simp, \<phi>reason, assumption, simp add: \<phi>expns, \<phi>reason)

lemma (in \<phi>min) op_var_scope':
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> (\<And>vname. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F vname \<lbrace> X\<heavy_comma> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope' TY F rawv \<lbrace> X\<heavy_comma> v \<Ztypecolon> Val rawv Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding op_var_scope'_def Premise_def
  apply (cases rawv; simp, \<phi>reason)
  apply (clarsimp simp add: \<phi>expns \<phi>Procedure_\<phi>Res_Spec simp del: set_mult_expn del: subsetI)
  subgoal for r res c
  apply (rule R_var.\<phi>R_allocate_res_entry[where R="(\<I> INTERP (r * c))"])
     apply (clarsimp) using finite_map_freshness infinite_varname apply blast
      apply (clarsimp)

 apply (clarsimp simp del: \<phi>Res_Spec_mult_homo set_mult_expn del: subsetI)
  subgoal premises prems for k res'
    apply (rule prems(2)[THEN spec[where x=r], THEN spec[where x=res'],
                simplified prems, simplified, THEN mp])
    apply (rule exI[where x=\<open>c * FIC_var.mk (1(k \<mapsto> v))\<close>])
    apply (simp add: \<phi>expns prems)
    by (smt (verit, ccfv_threshold) FIC_var.expand FIC_var.sep_disj_fiction Fic_Space_Un Fic_Space_m \<phi>Res_Spec_mult_homo prems(5) prems(6) prems(7) prems(8) prems(9) sep_disj_multD2 sep_disj_multI2 sep_mult_assoc')
  . .


lemma (in \<phi>min) op_free_var:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_var vname \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> 1 \<rbrace>\<close>
  unfolding op_free_var_def \<phi>Procedure_\<phi>Res_Spec
  by (clarsimp simp add: \<phi>expns FIC_var.expand  simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_dispose_res[where any=v and P=\<open>\<lambda>_. True\<close>]; clarsimp simp add: \<phi>Res_Spec_mult_homo)


subsection \<open>Branches & Loops\<close>

context \<phi>min_sem begin

paragraph \<open>Non-Branching Selection\<close>

definition op_sel :: "'TY \<Rightarrow> ('VAL \<times> 'VAL \<times> 'VAL, 'VAL,'VAL,'RES_N,'RES) proc'"
  where "op_sel TY =
    \<phi>M_caseV (\<lambda>vc. \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (\<tau>Int 1) V_int.dest vc (\<lambda>c.
    \<phi>M_getV TY id va (\<lambda>a.
    \<phi>M_getV TY id vb (\<lambda>b.
    Return (sem_value (if snd c = 1 then b else a)))))))"

paragraph \<open>Branch\<close>

definition op_if :: "('ret,'VAL,'RES_N,'RES) proc
                  \<Rightarrow> ('ret,'VAL,'RES_N,'RES) proc
                  \<Rightarrow> ('VAL,'ret,'VAL,'RES_N,'RES) proc'"
  where "op_if brT brF v =
    \<phi>M_getV (\<tau>Int 1) V_int.dest v (\<lambda>c. (if snd c = 1 then brT else brF))"

paragraph \<open>While Loop\<close>

inductive SemDoWhile :: "('VAL,'VAL,'RES_N,'RES) proc \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> (unit,'VAL,'RES_N,'RES) state \<Rightarrow> bool" where
  "Success (sem_value (V_int.mk (1,0))) res \<in> f s \<Longrightarrow> SemDoWhile f s (Success (sem_value ()) res)"
| "Success (sem_value (V_int.mk (1,1))) res \<in> f s \<Longrightarrow> SemDoWhile f res s'' \<Longrightarrow> SemDoWhile f s s''"
| "Exception v e \<in> f s \<Longrightarrow> SemDoWhile f s (Exception v e)"
| "PartialCorrect \<in> f s \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "Invalid \<in> f s \<Longrightarrow> SemDoWhile f s Invalid"

lemma "\<nexists> y. SemDoWhile ((\<lambda>res. Return (sem_value (V_int.mk (1,1))) res)::('VAL,'VAL,'RES_N,'RES) proc) res y"
  apply rule apply (elim exE) subgoal for y
    apply (induct "((\<lambda>res. Return (sem_value (V_int.mk (1,1))) (res::'RES_N \<Rightarrow> 'RES))::('VAL,'VAL,'RES_N,'RES) proc)" res y
           rule: SemDoWhile.induct)
       apply (simp_all add: Return_def det_lift_def) . .

definition op_do_while :: "('VAL,'VAL,'RES_N,'RES) proc \<Rightarrow> (unit,'VAL,'RES_N,'RES) proc" where
  "op_do_while f s = Collect (SemDoWhile f s)"

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

inductive SemRec :: "(('a,'a,'VAL,'RES_N,'RES) proc' \<Rightarrow> ('a,'a,'VAL,'RES_N,'RES) proc')
            \<Rightarrow> 'a sem_value \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('a,'VAL,'RES_N,'RES) state set \<Rightarrow> bool"
where
  SemRec_I0: "(\<And>g. F g x res = y) \<Longrightarrow> SemRec F x res y"
| SemRec_IS: "SemRec (F o F) x res y \<Longrightarrow> SemRec F x res y"

definition op_recursion :: "'TY list \<Rightarrow> 'TY list
                         \<Rightarrow> (('a,'a,'VAL,'RES_N,'RES) proc' \<Rightarrow> ('a,'a,'VAL,'RES_N,'RES) proc')
                         \<Rightarrow> ('a,'a,'VAL,'RES_N,'RES) proc'"
  where "op_recursion _ _ F x s = (if (\<exists>t. SemRec F x s t) then The (SemRec F x s) else {})"


end

end


