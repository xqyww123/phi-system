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

subsubsection \<open>Natural Nmbers\<close>

paragraph \<open>Natural Number\<close>

definition \<phi>Nat :: "nat \<Rightarrow> ('VAL, nat) \<phi>" ("\<nat>[_]")
  where "\<nat>[b] x = (if x < 2^b then { V_int.mk (b,x) } else {})"

abbreviation \<open>Size \<equiv> \<nat>[addrspace_bits]\<close>

lemma \<phi>Nat_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>[b]) \<longleftrightarrow> (p = V_int.mk (b,x)) \<and> x < 2^b"
  unfolding \<phi>Type_def by (simp add: \<phi>Nat_def)

lemma \<phi>Nat_elim[elim!,\<phi>elim]:
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

\<phi>processor literal_number 9500\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
  \<open>fn ctx => fn meta => Parse.number >> (fn num => fn _ =>
  let open NuBasics
    val num = Syntax.parse_term ctx num
    fun mk term = mk_nuTy (num, term) |> Syntax.check_term ctx |> Thm.cterm_of ctx
    val term = (
        (dest_current_nu meta |> strip_separations |> hd |> dest_RepSet |> #2 |> mk)
      handle TERM _ => mk @{term \<open>\<nat>[32]\<close>}
        | ERROR _ => mk @{term \<open>\<nat>[32]\<close>})
  in (NuSys.auto_construct ctx term meta, ctx)  end)
\<close>

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

lemma \<phi>Int_inhabited[elim,\<phi>elim]:
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

lemma \<phi>Bool_inhabited[\<phi>elim, elim!]:
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

lemma RawPointer_inhabited[elim,\<phi>elim]:
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

lemma Pointer_inhabited[elim,\<phi>elim]:
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

lemma SlicePtr_inhabited[\<phi>elim,elim!]:
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


subsection \<open>Tuple Field\<close>

definition \<phi>Field :: "('VAL, 'a) \<phi> \<Rightarrow> ('VAL, 'a) \<phi>" ("\<clubsuit>")
  where "\<phi>Field T x = { V_tup.mk [v] |v. v \<in> T x }"

lemma \<phi>Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Field T) \<longleftrightarrow> (\<exists>v. p = V_tup.mk [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Field_def \<phi>Type_def by simp

lemma \<phi>Field_inhabited[elim,\<phi>elim]:
  \<open>Inhabited (x \<Ztypecolon> \<clubsuit> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

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


subsection \<open>Array\<close>

definition Array :: "nat \<Rightarrow> ('VAL, 'a) \<phi> \<Rightarrow> ('VAL, 'a list) \<phi>"
  where \<open>Array N T = (\<lambda>l. { V_array.mk (TY,vs) |TY vs.
    length l = N \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)) })\<close>

lemma Array_expns[\<phi>expns]:
  \<open>v \<in> (l \<Ztypecolon> Array N T) \<longleftrightarrow>
    (\<exists> TY vs. length l = N \<and> v = V_array.mk (TY,vs) \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l
        \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)))\<close>
  unfolding Array_def \<phi>Type_def by simp blast

lemma Array_inhabited[\<phi>elim, elim]:
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



subsection \<open>Variable\<close>


definition Var :: \<open>varname \<Rightarrow> 'VAL \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set\<close>
  where \<open>Var vname val = {FIC_var.mk (Fine (1(vname \<mapsto> val)))} \<close>

lemma Var_expn[\<phi>expns]:
  \<open>fic \<in> (val \<Ztypecolon> Var vname) \<longleftrightarrow> fic = FIC_var.mk (Fine (1(vname \<mapsto> val)))\<close>
  unfolding Var_def \<phi>Type_def by simp


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