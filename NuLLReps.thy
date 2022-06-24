theory NuLLReps
  imports NuSys "HOL-Library.Word"
  abbrevs "<own>" = "\<left_fish_tail>"
    and "<none>" = "\<down_fish_tail>"
    and "<object>" = "\<R_arr_tail>"
begin   

section \<open>\<phi>-Types for Semantic Models\<close>

declare pair_forall[lrep_exps] pair_exists[lrep_exps]
(* declare llty_prod[\<phi>intro] *)

context std begin

subsection \<open>Integer\<close>

\<phi>overloads nat and int

subsubsection \<open>Natural Nmbers\<close>

paragraph \<open>Natural Number\<close>

definition \<phi>Nat :: "nat \<Rightarrow> ('VAL, nat) \<phi>" ("\<nat>[_]")
  where "\<nat>[b] x = (if x < 2^b then { V_int.mk (b,x) } else {})"

abbreviation \<open>Size \<equiv> \<nat>[addrspace_bits]\<close>

lemma \<phi>Nat_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>[b]) \<longleftrightarrow> (p = V_int.mk (b,x)) \<and> x < 2^b"
  unfolding \<phi>Type_def by (simp add: \<phi>Nat_def)

lemma \<phi>Nat_elim[elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> \<nat>[b]) \<Longrightarrow> (x < 2^b \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (auto simp add: \<phi>expns)

lemma \<phi>Nat_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<nat>[?b]) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<nat>[b]) (\<tau>Int b)\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

lemma [\<phi>reason on \<open>\<phi>Equal (\<nat>[?b]) ?c ?eq\<close>]:
  "\<phi>Equal (\<nat>[b]) (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (auto simp add: unsigned_word_eqI \<phi>expns)

lemma [\<phi>reason on \<open>\<phi>Zero (T_int.mk ?b) (\<nat>[?b]) ?zero\<close>]:
  "\<phi>Zero (T_int.mk b) (\<nat>[b]) 0" unfolding \<phi>Zero_def by (simp add: \<phi>expns)

paragraph \<open>Rounded Natural Number\<close>

definition \<phi>NatRound :: "nat \<Rightarrow> ('VAL, nat) \<phi>" ("\<nat>\<^sup>r[_]")
  where "\<nat>\<^sup>r[b] x = { V_int.mk (b, (x mod 2^b)) }"

lemma \<phi>NatRound_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>\<^sup>r[b]) \<longleftrightarrow> p = V_int.mk (b, (x mod 2^b))"
  unfolding \<phi>Type_def \<phi>NatRound_def by simp

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
  by (simp add: \<phi>expns) (smt (verit, ccfv_SIG) diff_le_self power_increasing_iff)


subsubsection \<open>Subtyping\<close>

lemma subty_Z_N[\<phi>overload nat on \<open>?x \<Ztypecolon> \<int>[?b]\<close>]: 
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < x \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> \<int>[b] \<longmapsto> nat x \<Ztypecolon> \<nat>[b]"
  unfolding Subty_def Premise_def apply (simp add: \<phi>expns del: One_nat_def)
  by (smt (verit, del_insts) diff_less less_numeral_extra(1) power_strict_increasing_iff)

lemma subty_N_Z[\<phi>overload int on \<open>?x \<Ztypecolon> \<int>[?b]\<close>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^(b - 1) \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> \<nat>[b] \<longmapsto> int x \<Ztypecolon> \<int>[b]"
  unfolding Subty_def Premise_def apply (simp add: \<phi>expns del: One_nat_def)
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
  by (simp add: \<phi>expns)


subsection \<open>Pointers\<close>

subsubsection \<open>Raw Pointer\<close>

definition RawPointer :: "('VAL, 'TY rawaddr) \<phi>"
  where "RawPointer x = (if valid_rawaddr x then { V_pointer.mk x } else {})"

lemma RawPointer_expn[\<phi>expns]:
  "v \<in> (p \<Ztypecolon> RawPointer) \<longleftrightarrow> v = V_pointer.mk p \<and> valid_rawaddr p"
  by (simp add: \<phi>Type_def RawPointer_def \<phi>expns)

lemma RawPointer_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited (p \<Ztypecolon> RawPointer) \<Longrightarrow> (valid_rawaddr p \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma RawPointer_zero[\<phi>reason on \<open>\<phi>Zero (T_pointer.mk ()) RawPointer ?x\<close>]:
  "\<phi>Zero \<tau>Pointer RawPointer (Null |: 0)"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_prod_def zero_memaddr_def)

lemma RawPointer_eqcmp[\<phi>reason on \<open>\<phi>Equal RawPointer ?c ?eq\<close>]:
  "\<phi>Equal RawPointer (\<lambda>x y. x = 0 |: 0 \<or> y = 0 |: 0 \<or> memaddr.segment x = memaddr.segment y) (=)"
  unfolding \<phi>Equal_def by (simp add: lrep_exps \<phi>expns zero_memaddr_def) blast

lemma RawPointer_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> RawPointer) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> RawPointer) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns)

subsubsection \<open>Pointer\<close>

definition Pointer :: "'TY \<Rightarrow> ('VAL, 'TY logaddr) \<phi>"
  where "Pointer TY x = (if valid_logaddr x \<and> x \<noteq> 0 \<and> logaddr_type x = TY \<and> 0 < MemObj_Size TY
                        then { V_pointer.mk (logaddr_to_raw x) }
                        else {})"

lemma Pointer_expn[\<phi>expns]:
  "v \<in> (addr \<Ztypecolon> Pointer TY) \<longleftrightarrow>
      v = V_pointer.mk (logaddr_to_raw addr) \<and> valid_logaddr addr
    \<and> addr \<noteq> 0 \<and> logaddr_type addr = TY \<and> 0 < MemObj_Size TY"
  unfolding \<phi>Type_def by (simp add: Pointer_def)

lemma Pointer_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited (addr \<Ztypecolon> Pointer TY) \<Longrightarrow>
      (valid_logaddr addr \<and> addr \<noteq> 0 \<and> logaddr_type addr = TY \<and> 0 < MemObj_Size TY \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Pointer_eqcmp[\<phi>reason on \<open>\<phi>Equal (Pointer ?TY) ?c ?eq\<close>]:
    "\<phi>Equal (Pointer TY) (\<lambda>x y. memaddr.segment x = memaddr.segment y) (=)"
  unfolding \<phi>Equal_def
  by (simp add: \<phi>expns) (metis logaddr_to_raw_inj)

lemma Pointer_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> Pointer ?TY) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> Pointer TY) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns valid_logaddr_def)

subsubsection \<open>Slice Pointer\<close>

text \<open>A limitation of the ordinary Pointer is that it cannot point to the end of an array,
  because there is no object at all at the end. To address this, there is a slice pointer which
  can range over a piece of the array including the end.\<close>

definition SlicePtr :: "'TY \<Rightarrow> ('VAL, 'TY logaddr \<times> nat \<times> nat) \<phi>"
  where "SlicePtr TY = (\<lambda>(base,i,len).
    if valid_logaddr base \<and> base \<noteq> 0 \<and> (\<exists>N. logaddr_type base = \<tau>Array N TY \<and> len \<le> N)
        \<and> 0 < MemObj_Size TY \<and> i \<le> len
    then { V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY)) }
    else {})"

lemma SlicePtr_expn[\<phi>expns]:
  \<open>v \<in> ((base, i, len) \<Ztypecolon> SlicePtr TY) \<longleftrightarrow>
      valid_logaddr base \<and> base \<noteq> 0
      \<and> (\<exists>N. logaddr_type base = \<tau>Array N TY \<and> len \<le> N)
      \<and> 0 < MemObj_Size TY \<and> i \<le> len
      \<and> v = V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY))\<close>
  unfolding SlicePtr_def \<phi>Type_def by simp blast

lemma SlicePtr_inhabited[\<phi>reason_elim!,elim!]:
  \<open>Inhabited ((base, i, len) \<Ztypecolon> SlicePtr TY)
\<Longrightarrow> (\<And>N. valid_logaddr base \<Longrightarrow> base \<noteq> 0 \<Longrightarrow> logaddr_type base = \<tau>Array N TY \<Longrightarrow> len \<le> N
          \<Longrightarrow> 0 < MemObj_Size TY \<Longrightarrow> i \<le> len \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def SlicePtr_expn by simp blast

lemma SlicePtr_eqcmp[\<phi>reason on \<open>\<phi>Equal (SlicePtr ?TY) ?c ?eq\<close>]:
    "\<phi>Equal (SlicePtr TY) (\<lambda>x y. fst x = fst y) (\<lambda>(_,i1,_) (_,i2,_). i1 = i2)"
  unfolding \<phi>Equal_def
  apply (clarsimp simp add: \<phi>expns word_of_nat_eq_iff take_bit_nat_def simp del: of_nat_mult)
  subgoal premises for addr i1 n1 i2 N n2 proof -
    note logaddr_storable_in_mem[OF \<open>valid_logaddr addr\<close> \<open>addr \<noteq> 0\<close>,
            unfolded \<open>logaddr_type addr = \<tau>Array N TY\<close>, unfolded memobj_size_arr]
    then have \<open>i1 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
          and \<open>i2 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
      by (meson \<open>i1 \<le> n1\<close> \<open>n1 \<le> N\<close> \<open>i2 \<le> n2\<close> \<open>n2 \<le> N\<close> dual_order.strict_trans2 mult_le_mono1)+
    then show ?thesis
      using \<open>0 < MemObj_Size TY\<close> by fastforce 
  qed
  done

lemma SlicePtr_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> SlicePtr ?TY) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> SlicePtr TY) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (cases x, simp add: \<phi>expns valid_logaddr_def)


subsection \<open>Tuple\<close>

subsubsection \<open>Empty Tuple\<close>

definition EmptyTuple :: \<open>('VAL, unit) \<phi>\<close>
  where \<open>EmptyTuple x = { V_tup.mk [] }\<close>

lemma EmptyTuple_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> EmptyTuple) \<longleftrightarrow> p = V_tup.mk []\<close>
  unfolding EmptyTuple_def \<phi>Type_def by simp

subsubsection \<open>Field\<close>

definition \<phi>Field :: "('VAL, 'a) \<phi> \<Rightarrow> ('VAL, 'a) \<phi>" ("\<clubsuit>")
  where "\<phi>Field T x = { V_tup.mk [v] |v. v \<in> T x }"

lemma \<phi>Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Field T) \<longleftrightarrow> (\<exists>v. p = V_tup.mk [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Field_def \<phi>Type_def by simp

lemma \<phi>Field_inhabited[elim!,\<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<clubsuit> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma EmptyTuple_reduce[simp]:
  \<open>((a,()) \<Ztypecolon> \<clubsuit> T \<^emph> EmptyTuple) = (a \<Ztypecolon> \<clubsuit> T)\<close>
  unfolding set_eq_iff apply (simp add: \<phi>expns V_tup_mult)
  by (metis V_tup_mult append.left_neutral append_Cons)

lemma \<phi>Field_zero  [\<phi>reason on \<open>\<phi>Zero (T_tup.mk [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x \<Longrightarrow> \<phi>Zero (T_tup.mk [ty]) (\<clubsuit> T) x \<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Field_zeros [\<phi>reason on \<open>\<phi>Zero (T_tup.mk [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x
    \<Longrightarrow> \<phi>Zero (T_tup.mk tys) Ts xs
    \<Longrightarrow> \<phi>Zero (T_tup.mk (ty#tys)) (\<clubsuit> T \<^emph> Ts) (x,xs) \<close>
  unfolding \<phi>Zero_def
  by (simp add: \<phi>expns V_tup_mult_cons) blast

lemma \<phi>Field_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<clubsuit> ?T) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> T) TY \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<clubsuit> T) (\<tau>Tuple [TY])\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp simp add: \<phi>expns)

lemma \<phi>Field_semtsy[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<clubsuit> ?T \<^emph> ?Ts) ?ty\<close>]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (xs \<Ztypecolon> Ts) (\<tau>Tuple TYs)
\<Longrightarrow> \<phi>SemType ((x,xs) \<Ztypecolon> (\<clubsuit> T \<^emph> Ts)) (\<tau>Tuple (TY#TYs))\<close>
  unfolding \<phi>SemType_def subset_iff
  apply (clarsimp simp add: \<phi>expns)
  by (metis V_tup_mult append.left_neutral append_Cons list.rel_inject(2))

subsubsection \<open>Helpers\<close>

definition \<open>\<phi>Is_Tuple T x = { V_tup.mk vs |vs. V_tup.mk vs \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>Is_Tuple_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Is_Tuple T) \<longleftrightarrow> (\<exists>vs. p = V_tup.mk vs \<and> V_tup.mk vs \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Is_Tuple_def \<phi>Type_def by simp

lemma \<phi>Is_Tuple_\<phi>Is_Tuple[simp]:
  \<open>\<phi>Is_Tuple (\<phi>Is_Tuple T) = \<phi>Is_Tuple T\<close>
  unfolding \<phi>Is_Tuple_def fun_eq_iff set_eq_iff \<phi>Type_def by simp


lemma (in std) \<phi>Is_Tuple_\<phi>Is_Tuple_more[simp]:
  \<open>\<phi>Is_Tuple (\<clubsuit> A \<^emph> \<phi>Is_Tuple B) = (\<clubsuit> A \<^emph> \<phi>Is_Tuple B)\<close>
  apply (rule \<phi>Type_eqI)
  apply (clarsimp simp add: \<phi>expns, rule; clarify)
  by (metis V_tup_mult)

lemma (in std) \<phi>Is_Tuple_Field[simp]:
  \<open>\<phi>Is_Tuple (\<clubsuit> A) = \<clubsuit> A\<close>
  by (rule \<phi>Type_eqI, clarsimp simp add: \<phi>expns, rule; clarify; blast)

lemma (in std) \<phi>Is_Tuple_EmptyTuple[simp]:
  \<open>\<phi>Is_Tuple EmptyTuple = EmptyTuple\<close>
  by (rule \<phi>Type_eqI, clarsimp simp add: \<phi>expns)



subsection \<open>Array\<close>

definition Array :: "nat \<Rightarrow> ('VAL, 'a) \<phi> \<Rightarrow> ('VAL, 'a list) \<phi>"
  where \<open>Array N T = (\<lambda>l. { V_array.mk (TY,vs) |TY vs.
    length l = N \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)) })\<close>

lemma Array_expns[\<phi>expns]:
  \<open>v \<in> (l \<Ztypecolon> Array N T) \<longleftrightarrow>
    (\<exists> TY vs. length l = N \<and> v = V_array.mk (TY,vs) \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l
        \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)))\<close>
  unfolding Array_def \<phi>Type_def by simp blast

lemma Array_inhabited[\<phi>reason_elim!, elim!]:
  \<open> Inhabited (l \<Ztypecolon> Array N T)
\<Longrightarrow> (length l = N \<Longrightarrow>(\<And>i. i < length l \<Longrightarrow> Inhabited (l!i \<Ztypecolon> T)) \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns list_all2_conv_all_nth) blast

lemma Array_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> Array ?N ?T) ?ty\<close>]:
  \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY) \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> Array N T) (\<tau>Array N TY)\<close>
  apply (clarsimp simp add: \<phi>expns list_all_length list_all2_conv_all_nth \<phi>SemType_def subset_iff
          Inhabited_def)
  using Well_Type_unique by blast
  
lemma Array_zero[\<phi>reason on \<open>\<phi>Zero (\<tau>Array ?N ?TY) (Array ?N ?T) ?x\<close>]:
  \<open>\<phi>Zero TY T zero \<Longrightarrow> \<phi>\<phi>SemType T TY \<Longrightarrow> \<phi>Zero (\<tau>Array N TY) (Array N T) (replicate N zero)\<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns list_all2_conv_all_nth Inhabited_def; blast)


subsection \<open>Index to Fields of Structures\<close>

definition \<phi>Index_getter :: \<open>nat list \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> ('VAL,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_getter idx T U g \<longleftrightarrow> index_value idx \<in> (g \<Ztypecolon> T \<Rrightarrow> U)\<close>

definition \<phi>Index_mapper :: \<open>nat list \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> ('VAL,'b) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_mapper idx T U f \<longleftrightarrow> (\<forall>g g'. g \<in> (g' \<Ztypecolon> U \<Rrightarrow> U) \<longrightarrow> index_mod_value idx g \<in> (f g' \<Ztypecolon> T \<Rrightarrow> T))\<close>


lemma idx_step_value_V_tup_suc:
  \<open>idx_step_value (Suc i) (V_tup.mk (va # vs)) = idx_step_value i (V_tup.mk vs)\<close>
  by (simp add: idx_step_value_tup)

lemma idx_step_mod_value_V_tup_suc:
  \<open>idx_step_mod_value (Suc i) g (V_tup.mk (va # vs)) = V_tup.mk [va] * idx_step_mod_value i g (V_tup.mk vs)\<close>
  by (metis NO_MATCH_I V_tup_mult_cons idx_step_mod_value_tup list_update_code(3) nth_Cons_Suc)
  



lemma (in std) \<phi>Index_getter_tup_suc:
  \<open> \<phi>Index_getter (i # idx) X Y f
\<Longrightarrow> \<phi>Index_getter (Suc i # idx) (\<clubsuit> T \<^emph> \<phi>Is_Tuple X) Y (f o snd)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_V_tup_suc)

lemma (in std) \<phi>Index_getter_tup_0:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (0 # idx) (\<clubsuit> X) Y f\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma (in std) \<phi>Index_getter_tup_0r:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (0 # idx) (\<clubsuit> X \<^emph> \<phi>Is_Tuple R) Y (f o fst)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma (in std) \<phi>Index_getter_arr:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < N
\<Longrightarrow> \<phi>Index_getter (i # idx) (Array N X) Y (\<lambda>l. f (l!i))\<close>
  unfolding \<phi>Index_getter_def Premise_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_arr list_all2_conv_all_nth)



lemma (in std) \<phi>Index_mapper_tup_suc:
  \<open> \<phi>Index_mapper (i # idx) X Y f
\<Longrightarrow> \<phi>Index_mapper (Suc i # idx) (\<clubsuit> T \<^emph> \<phi>Is_Tuple X) Y (apsnd o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_V_tup_suc)
  by (metis idx_step_mod_value_tup)

lemma (in std) \<phi>Index_mapper_tup_0:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>Index_mapper (0 # idx) (\<clubsuit> X) Y f\<close>
  unfolding \<phi>Index_mapper_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)

lemma (in std) \<phi>Index_mapper_tup_0r:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>Index_mapper (0 # idx) (\<clubsuit> X \<^emph> \<phi>Is_Tuple X) Y (apfst o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)
  by (metis V_tup_mult append.left_neutral append_Cons)

lemma (in std) \<phi>Index_mapper_arr:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < N
\<Longrightarrow> \<phi>Index_mapper (i # idx) (Array N X) Y (\<lambda>g l. l[i := f g (l!i)])\<close>
  unfolding \<phi>Index_mapper_def Premise_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_arr list_all2_conv_all_nth)
  by (metis nth_list_update)



subsection \<open>Variable\<close>


definition Var :: \<open>varname \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set\<close>
  where \<open>Var vname T x = {FIC_var.mk (Fine (1(vname \<mapsto> val))) |val. val \<in> (x \<Ztypecolon> T)} \<close>

lemma Var_expn[\<phi>expns]:
  \<open>fic \<in> (x \<Ztypecolon> Var vname T) \<longleftrightarrow> (\<exists>val. fic = FIC_var.mk (Fine (1(vname \<mapsto> val))) \<and> val \<in> (x \<Ztypecolon> T))\<close>
  unfolding Var_def \<phi>Type_def by simp

lemma Var_inhabited[\<phi>reason_elim!,elim!]:
  \<open>Inhabited (x \<Ztypecolon> Var vname T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Var_subty:
  \<open> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> Var vname T \<longmapsto> x' \<Ztypecolon> Var vname T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Subty_def by (simp add: \<phi>expns, blast)

lemma Var_cast_\<phi>app[\<phi>overload cast]: 
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e FIX OBJ x \<Ztypecolon> Var vname T \<longmapsto> OBJ x' \<Ztypecolon> Var vname T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  apply (rule cast_obj_\<phi>app)
  unfolding Argument_def
  using Var_subty .

lemma Var_ExTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (ExTyp T)) = (\<exists>*a. x a \<Ztypecolon> Var vname (T a))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns, blast)

lemma Var_SubjTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (x \<Ztypecolon> Var vname T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns, blast)

lemma [\<phi>reason 110 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> OBJ ?H \<longmapsto> ?R''' * \<medium_left_bracket> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R\<heavy_comma> OBJ x \<Ztypecolon> Var var T \<longmapsto> R\<heavy_comma> \<medium_left_bracket> OBJ x' \<Ztypecolon> Var var T' \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def
  by (simp add: \<phi>expns times_list_def, blast)


subsubsection \<open>Synthesis Rules\<close>

lemma [\<phi>reason on \<open>\<medium_left_bracket> \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S1 \<longmapsto> ?S2\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> Var ?var ?T \<rbrace> \<medium_right_bracket>: ?G\<close>]:
  \<open> SUBGOAL G G'
\<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e S1 \<longmapsto> S2\<heavy_comma> \<medium_left_bracket> OBJ x \<Ztypecolon> Var var T \<medium_right_bracket> \<medium_right_bracket>: G'
\<Longrightarrow> SOLVE_SUBGOAL G'
\<Longrightarrow> \<medium_left_bracket> \<^bold>p\<^bold>r\<^bold>o\<^bold>c SKIP \<lbrace> S1 \<longmapsto> S2\<heavy_comma> SYNTHESIS x \<Ztypecolon> Var var T \<rbrace> \<medium_right_bracket>: G\<close>
  unfolding Subty_Target2_def Subty_Target_def Synthesis_def
  using "\<phi>cast" \<phi>reassemble_proc_0 \<phi>reassemble_proc_final by blast


subsubsection \<open>Application Methods for Subtyping\<close>

lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?x \<Ztypecolon> ?T \<longmapsto> ?Y \<Ztypecolon> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P)
            (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n OBJ ?x \<Ztypecolon> Var ?var ?T) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> x \<Ztypecolon> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n OBJ x \<Ztypecolon> Var var T)
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n OBJ x \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def Fix_def] by metis

lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?x' \<Ztypecolon> ?T' \<longmapsto> ?y \<Ztypecolon> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P)
            (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n OBJ ?x \<Ztypecolon> Var ?var ?T) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x' \<Ztypecolon> T' \<longmapsto> y \<Ztypecolon> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n OBJ x \<Ztypecolon> Var var T)
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n OBJ y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def Fix_def] by metis


lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?x \<Ztypecolon> ?T \<longmapsto> ?y \<Ztypecolon> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P)
          (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> OBJ ?x \<Ztypecolon> Var ?var ?T) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> y \<Ztypecolon> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> OBJ x \<Ztypecolon> Var var T)
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> OBJ y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def Fix_def] \<phi>cast_intro_frame by metis


lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?x' \<Ztypecolon> ?T' \<longmapsto> ?y \<Ztypecolon> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P)
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> OBJ ?x \<Ztypecolon> Var ?var ?T) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x' \<Ztypecolon> T' \<longmapsto> y \<Ztypecolon> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> OBJ x \<Ztypecolon> Var var T)
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> OBJ y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def Fix_def] \<phi>cast_intro_frame by metis



subsection \<open>Memory Object\<close>

definition Ref :: \<open>('VAL,'a) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'TY logaddr \<Zinj> 'a share) \<phi>\<close>
  where \<open>Ref T x' = (case x' of (seg |: idx) \<Zinj> (n \<Znrres> x) \<Rightarrow>
    if 0 < n \<and> valid_index (segidx.layout seg) idx then
    { FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val v)))))
          |v. v \<in> Well_Type (logaddr_type (seg |: idx)) \<and> v \<in> (x \<Ztypecolon> T) }
    else {})\<close>

lemma Ref_expn[\<phi>expns]:
  \<open>fic \<in> ((seg |: idx) \<Zinj> (n \<Znrres> v) \<Ztypecolon> Ref Identity)
    \<longleftrightarrow> 0 < n \<and> valid_index (segidx.layout seg) idx
        \<and> v \<in> Well_Type (logaddr_type (seg |: idx))
        \<and> fic = FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val v)))))\<close>
  unfolding Ref_def \<phi>Type_def by (simp add: Identity_def) blast

(*
definition Slice :: \<open>('VAL,'a) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'TY logaddr \<Zinj> 'a share option list) \<phi>\<close>
  where \<open>Slice T x' = (case x' of (seg |: i#idx) \<Zinj> l \<Rightarrow>
    if valid_index (segidx.layout seg) idx
     \<and> (\<exists>N TY. index_type idx (segidx.layout seg) = \<tau>Array N TY \<and> i + length l \<le> N)
    then let 
    { FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val v)))))
          |v. v \<in> Well_Type (logaddr_type (seg |: idx)) \<and> v \<in> (x \<Ztypecolon> T) }
    else {} | _ \<Rightarrow> {})\<close> *)


end










section \<open>Memory address\<close>

text \<open>The concept of the address space is one of the notions in the LLVM\<close>

(* primrec addr_cap \<comment> \<open>The memory block starting at the address has length `len`\<close>
  where "addr_cap (seg |+ ofs) len \<longleftrightarrow> ofs = 0 \<and> segment_len seg = len" *)

(* definition "malloc h = (@x. \<forall>ofs. h (x |: ofs) = None)"

lemma malloc: "Heap h \<Longrightarrow> h (MemAddress (malloc h |+ ofs)) = None"
  unfolding Heap_def AvailableSegments_def malloc_def
  by (metis (mono_tags, lifting) not_finite_existsD tfl_some) 

lemma malloc2: "Heap h \<Longrightarrow> MemAddress (malloc h |+ ofs) \<notin> dom h"
  using malloc by (simp add: domIff) 


type_synonym raw_memaddr = "size_t word memaddr"
type_synonym logical_memaddr = "nat memaddr"

*)


(* specification (segment_len) segment_len_max: "segment_len seg < (2::nat) ^ addrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg < (2::nat) ^ addrspace_capacity (segment_space seg)" by auto qed *)
(* specification (segment_len) segment_len_max: "segment_len seg * size_of (segment_llty seg) < addrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg * size_of (segment_llty seg) < addrspace_capacity (segment_space seg)" by auto qed *)

(* typedef ('b::len0) size_t = "UNIV :: nat set" ..
instantiation size_t :: (len0) len begin
definition len_of_size_t :: "'a size_t itself \<Rightarrow> nat" where [simp]: "len_of_size_t _ = 1 + addrspace_capacity LENGTH('a)"
  \<comment> \<open>it is plus 1 to enable the representation of `negative` offset of the address exorcising any ambiguity.
    In the complication implementation, it is interpreted as this that the size of a single segment can only be at most to half of the
    actual total capacity of the address space, 2^31 bytes in the 32 bits machine, so that the size_t in this case still equals
    to that in the actual physical machine. \<close>
instance by standard auto
end *)

(* named_theorems fixtyp_\<phi>cast and freetyp_\<phi>cast

lemma [\<phi>intro, fixtyp_\<phi>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e address_llty addr = ty \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> Pointer['spc] \<longmapsto> addr \<tycolon> TypedPtr['spc::len0] ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)

lemma [\<phi>intro, freetyp_\<phi>cast]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> TypedPtr['spc] ty \<longmapsto> addr \<tycolon> Pointer['spc::len0] \<^bold>w\<^bold>i\<^bold>t\<^bold>h address_llty addr = ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)
*)


(* subsubsection \<open>Index\<close>

definition index_tuple :: "('a,'b,'x,'y) index \<Rightarrow> ('a::field_list tuple, 'b::field_list tuple, 'x, 'y) index"
  where "index_tuple idx = (case idx of Index g m \<Rightarrow> Index (g o dest_tuple) (map_tuple o m))"

lemma [\<phi>reason]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<brangle>"
  unfolding \<phi>index_def index_tuple_def tuple_forall by (cases idx) (simp add: \<phi>expns)

lemma [\<phi>reason]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<brangle>"
  unfolding \<phi>index_def index_tuple_def tuple_forall by (cases idx) (simp add: \<phi>expns)
*)
(*section \<open>Function Pointer\<close>

subsubsection \<open>lrep\<close>

instantiation fun_addr ::  lrep begin
definition llty_fun_addr :: " fun_addr itself \<Rightarrow> llty " where [simp, \<phi>reason]: "llty_fun_addr _ = Lty_fun_addr"
definition deepize_fun_addr :: " fun_addr \<Rightarrow> value " where "deepize_fun_addr = DM_fun_addr"
definition shallowize_fun_addr :: " value \<Rightarrow> fun_addr " where "shallowize_fun_addr x = (case x of DM_fun_addr y \<Rightarrow> y)"
instance apply standard using shallowize_fun_addr_def deepize_fun_addr_def by auto
end

subsubsection \<open>zero\<close>

instantiation fun_addr :: zero begin
definition zero_fun_addr :: " fun_addr " where "zero_fun_addr = fun_addr_NULL"
instance by standard
end

subsubsection \<open>ceq\<close>

instantiation fun_addr :: ceq begin
definition ceqable_fun_addr :: " heap \<Rightarrow> fun_addr \<Rightarrow> fun_addr \<Rightarrow> bool " where [simp]: "ceqable_fun_addr _ _ _ = True"
definition ceq_fun_addr :: " fun_addr \<Rightarrow> fun_addr \<Rightarrow> bool " where [simp]: "ceq_fun_addr = (=)"
instance by standard auto
end

subsubsection \<open>miscellaneous\<close>

instantiation fun_addr :: field begin instance by standard end
instantiation fun_addr :: field_list begin instance by standard end

:lsubsubsection \<open>\<phi>-abstractor\<close>

definition op_func_pointer :: "('a \<longmapsto> 'b) \<Rightarrow> ('r :: stack) \<longmapsto> (fun_addr \<times> 'r)"
  where "op_func_pointer f = (\<lambda>(h,r).
    if (\<exists>a. fun_table a = Some f)
    then Success (h, (SOME a. fun_table a = Some f), r)
    else PartialCorrect
)"

definition FunPtr :: "(heap \<times> 'ap::lrep,'ax) \<phi> \<Rightarrow> (heap \<times> 'bp::lrep,'bx) \<phi> \<Rightarrow> (fun_addr, 'ax \<longmapsto> 'bx) \<phi>"
  where "FunPtr A B fx  = {faddr. (\<exists>fp. fun_table faddr = Some fp \<and> (\<forall>a b. \<^bold>p\<^bold>r\<^bold>o\<^bold>c fp \<blangle> a \<tycolon> A \<longmapsto> b \<tycolon> B \<brangle>))}" *)

end