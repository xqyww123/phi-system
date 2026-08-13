theory Bucket_Hash
  imports Rational_Arith Dynamic_Array_arbi_len Phi_Semantics.PhiSem_Mem_C_MI
          PhiStd.PhiStd_Slice
          "HOL-Data_Structures.AList_Upd_Del"
begin

text \<open>We ignore arithmetic overflow in the length of a dynamic array,
      because otherwise the hash table cannot be specified in the expected way.
      However, we still consider arithmetic overflow in any other cases.\<close>

declare Suc_le_eq[simp]

abbreviation \<open>kv_entry TY \<equiv> \<struct>{k: size_\<t>, v: TY}\<close>

abbreviation \<open>hash (x::nat) n \<equiv> x mod n\<close>

abbreviation \<open>\<h>\<a>\<s>\<h> \<equiv> \<struct> {tabl: \<ptr>, N: size_\<t>} \<close>

term \<open>\<Array>[N] x\<close>

\<phi>type_def Hash
  where \<open>f \<Ztypecolon> Hash addr T \<equiv> 
       (tabl_addr, N) \<Ztypecolon> \<mem>[addr] \<lbrace> tabl: Ptr[\<array>[N] \<ptr>], N: \<nat>(size_\<t>) \<rbrace>\<heavy_comma>
        bucket_ptrs \<Ztypecolon> \<mem>[tabl_addr] \<Array>[N] Ptr\<heavy_comma>
        buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < N} (\<lambda>i. DynArr (bucket_ptrs ! i) \<lbrace>k: \<nat>(size_\<t>), v: T\<rbrace>)
       \<subj> bucket_ptrs buckets tabl_addr N.
           length bucket_ptrs = N \<and>
           (\<forall>i < N. list_all (\<lambda>(k,v). hash k N = i) (buckets i) \<and> distinct (map fst (buckets i))) \<and>
           (\<forall>k x. f k = Some x \<longleftrightarrow> (\<exists>i<N. (k,x) \<in> set (buckets i))) \<and>
           0 < N \<and> address_to_base tabl_addr \<and> address_to_base addr \<and>
           \<typeof> addr = \<struct> {tabl: \<ptr>, N: int(size_\<t>)} \<close>

deriving \<open> Abstract_Domain T P
       \<Longrightarrow> Abstract_Domain (Hash addr T)
            (\<lambda>f. \<typeof> addr = \<struct> {tabl: \<ptr>, N: int(size_\<t>)} \<and> (\<forall>k \<in> dom f. P (the (f k))))\<close>
    notes list_all_length[simp] Let_def[simp] set_eq_iff[simp]

    and \<open>   Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (Hash addr T) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom g. eq (the (f k)) (the (g k))))\<close>

    notes case_prod_beta[simp] list_all2_conv_all_nth[\<phi>sledgehammer_simps] list_all_length[\<phi>sledgehammer_simps]
          image_iff[simp] domIff[simp]
          (tactic: auto simp: Ball_def Bex_def set_eq_iff,
                   subgoal' for f f' xb buckets tabl_addr \<open>rule exI[where x=\<open>\<lambda>i. map (\<lambda>(k,_). (k, the (f' k))) (buckets i)\<close>]\<close> )

  deriving \<open>\<premise> \<typeof> T = \<typeof> U
        \<Longrightarrow> Transformation_Functor (Hash addr) (Hash addr) T U (\<lambda>_. UNIV) (\<lambda>_. UNIV)
                                (\<lambda>r f g. dom f = dom g \<and> (\<forall>k \<in> dom g. r (the (f k)) (the (g k))))\<close>

    notes set_eq_iff [\<phi>sledgehammer_simps] list_all2_conv_all_nth[\<phi>sledgehammer_simps]
          list_all_length[\<phi>sledgehammer_simps] in_set_conv_nth[\<phi>sledgehammer_simps]
    (tactic:  clarsimp,
              subgoal' for x xa xb xc xd xe \<open>rule exI[where x=xe], (rule conjI)+, auto_sledgehammer,
                subgoal_tac \<open>\<exists>g. \<forall>k x. g k = Some x \<longleftrightarrow> (\<exists>i<length xb. (k,x) \<in> set (xe i))\<close>,
                clarify, subgoal' for g \<open>rule exI[where x=g]\<close>,
                auto_sledgehammer,
                subgoal_tac \<open>\<And>k v1 v2.
                      \<exists>i<length xb. (k,v1) \<in> set (xe i)
                  \<Longrightarrow> \<exists>i<length xb. (k,v2) \<in> set (xe i)
                  \<Longrightarrow> v1 = v2\<close>,
                subst choice_iff[symmetric]\<close>)


  deriving \<open> \<premise> \<typeof> T = \<typeof> U
      \<Longrightarrow> Functional_Transformation_Functor (Hash addr) (Hash addr) T U (\<lambda>_. UNIV) (\<lambda>_. UNIV)
              (\<lambda>_ P f. \<forall>k\<in>dom f. P (the (f k))) (\<lambda>h _ f. map_option h o f)\<close>
    and Pointer_Of


declare [[\<phi>trace_reasoning = 1]]

proc calc_hash:
  input  \<open>k \<Ztypecolon> \<val> \<nat>(size_\<t>)\<heavy_comma> N \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
  premises \<open>N \<noteq> 0\<close>
  output \<open>hash k N \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
\<medium_left_bracket>
  k % N
\<medium_right_bracket> .

term \<open>bucket \<Ztypecolon> \<ref> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<close>

declare [[\<phi>trace_reasoning = 1]]

proc insert_bucket:
  input \<open>bucket \<Ztypecolon> \<ref> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<heavy_comma> k \<Ztypecolon> \<val> \<nat>(size_\<t>)\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  premises \<open>distinct (map fst bucket)\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output \<open>bucket' \<Ztypecolon> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>
          \<subj> bucket'. set bucket' = (set bucket - {(k',_). k' = k}) \<union> {(k,v)} \<and>
                        distinct (map fst bucket') \<close>
  is [routine]
\<medium_left_bracket>
  var met \<leftarrow> False \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
              \<open>\<lambda>i. (\<exists>v. (k,v) \<in> set (take i bucket)) \<Ztypecolon> \<var>[met] \<bool>\<heavy_comma>
                   (map (\<lambda>kv. if fst kv = k then (k,v) else kv) (take i bucket) @ drop i bucket)
                        \<Ztypecolon> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    val kv \<leftarrow> get_dynarr(addr, i) \<semicolon>
    if (kv.k = k) \<medium_left_bracket>
      set_dynarr(addr, i, \<lbrace> k: k, v: v \<rbrace>) \<semicolon>
      met \<leftarrow> True
    \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>
  \<medium_right_bracket> certified by (auto simp add: list_eq_iff_nth_eq nth_append list_update_append; auto_sledgehammer) \<semicolon>
  
  if (\<not> met) \<medium_left_bracket>
    push_dynarr (addr, \<lbrace> k: k, v: v \<rbrace>)
  \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> 
\<medium_right_bracket> .

proc update_hash:
  input  \<open>f \<Ztypecolon> \<ref> Hash addr T\<heavy_comma> k \<Ztypecolon> \<val> \<nat>(size_\<t>)\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> Hash addr T\<close> 
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length ;;

  transforms_to \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, base, buckets \<semicolon>
  val tabl_addr \<leftarrow> addr.tabl \<semicolon>
  val N \<leftarrow> addr.N \<semicolon>
  val hash \<leftarrow> calc_hash (k, N) \<semicolon>

  insert_bucket (tabl_addr[hash], k, v) \<semicolon>

  \<makes> \<open>f(k \<mapsto> v) \<Ztypecolon> Hash addr T\<close>
  certified by (auto, auto_sledgehammer, auto_sledgehammer, auto_sledgehammer, auto_sledgehammer,
                rule exI[where x=\<open>\<lambda>i. if i = hash k ?N then bucket' else buckets i\<close>],
                    subgoal_tac \<open>\<And>k' v. \<lbrakk> (k',v) \<in> set bucket' ; k' \<noteq> k \<rbrakk> \<Longrightarrow> (k', v) \<in> set (buckets (hash k ?N))\<close>,
                    subgoal_tac \<open>\<And>k v i.\<lbrakk> (k,v) \<in> set (buckets i) ; i < ?N \<rbrakk> \<Longrightarrow> hash k ?N = i\<close>,
                clarsimp, rule conjI, auto_sledgehammer, rule conjI, auto_sledgehammer,
                rule exI[where x=\<open>\<lambda>i. if i = hash k ?N then bucket' else buckets i\<close>],
                auto_sledgehammer, auto_sledgehammer, auto_sledgehammer)
\<medium_right_bracket> .

proc bucket_has_key:
  input  \<open>bucket \<Ztypecolon> \<ref> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<heavy_comma> k \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
  output \<open>(\<exists>v. (k,v) \<in> set bucket) \<Ztypecolon> \<val> \<bool>\<heavy_comma>
          bucket \<Ztypecolon> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<close>
\<medium_left_bracket>
  var met \<leftarrow> False \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr(addr))
             \<open>\<lambda>i. (\<exists>v. (k,v) \<in> set (take i bucket)) \<Ztypecolon> \<var>[met] \<bool>\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    met \<leftarrow> met \<or> (get_dynarr(addr, i).k = k)
  \<medium_right_bracket> \<semicolon>
  met
\<medium_right_bracket> .

proc hash_has_key:
  input  \<open>f \<Ztypecolon> \<ref> Hash addr T\<heavy_comma> k \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
  output \<open>k \<in> dom f \<Ztypecolon> \<val> \<bool>\<heavy_comma> f \<Ztypecolon> Hash addr T\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length \<semicolon>

  transforms_to \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, base, buckets \<semicolon>
  val tabl_addr \<leftarrow> addr.tabl \<semicolon>
  val N \<leftarrow> addr.N \<semicolon>
  val hash \<leftarrow> k % N \<semicolon>
  val ret \<leftarrow> bucket_has_key (tabl_addr[hash], k) \<semicolon>

  \<makes> \<open>f \<Ztypecolon> Hash addr T\<close> \<semicolon>

  ret
\<medium_right_bracket> .



proc lookup_bucket:
  input \<open>bucket \<Ztypecolon> \<ref> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<heavy_comma> k \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
  premises \<open>\<exists>v. (k,v) \<in> set bucket\<close>
  output \<open>v \<Ztypecolon> \<val> T\<heavy_comma>
          bucket \<Ztypecolon> DynArr addr \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>
          \<subj> v. (k,v) \<in> set bucket\<close>
\<medium_left_bracket>
  var ret \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
              \<open>\<lambda>i. v \<Ztypecolon> \<may> \<inited> \<var>[ret] T
                   \<subj> v v'. (\<exists>v. (k,v) \<in> set (take i bucket)) \<longrightarrow> v = Some v' \<and> (k,v') \<in> set (take i bucket)\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    val entry \<leftarrow> get_dynarr(addr, i) \<semicolon>
    if (entry.k = k) \<medium_left_bracket> 
      ret \<leftarrow> entry.v
    \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> \<semicolon>
  \<medium_right_bracket> \<semicolon>
  ret
\<medium_right_bracket> .


proc hash_lookup:
  input  \<open>f \<Ztypecolon> \<ref> Hash addr T\<heavy_comma> k \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
  premises \<open>k \<in> dom f\<close>
  output \<open>the (f k) \<Ztypecolon> \<val> T\<heavy_comma> f \<Ztypecolon> Hash addr T\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length \<semicolon>

  transforms_to \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, base, buckets \<semicolon>

  val tabl_addr \<leftarrow> addr.tabl \<semicolon>
  val N \<leftarrow> addr.N \<semicolon>
  val hash \<leftarrow> k % N \<semicolon>
  val ret \<leftarrow> lookup_bucket (tabl_addr[hash], k) \<semicolon>

  \<makes> \<open>f \<Ztypecolon> Hash addr T\<close> \<semicolon>

  ret
\<medium_right_bracket> .


proc new_hash:
  input  \<open>N \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
  requires \<open>\<param> T\<close>
  premises \<open>0 < N\<close>
       and \<open>\<typeof> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output \<open>Map.empty \<Ztypecolon> \<ref> Hash addr T \<subj> addr. \<top>\<close>
\<medium_left_bracket>
  val tabl_addr \<leftarrow> calloc (N) Ptr \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(size_\<t>)\<close>, N)
           \<open>\<lambda>M. bucket_ptrs \<Ztypecolon> \<mem>[addr] \<Array>[N] Ptr\<heavy_comma>
                (\<lambda>i. []) \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < M} (\<lambda>i. DynArr (bucket_ptrs ! i) \<lbrace>k: \<nat>(size_\<t>), v: T\<rbrace>)
                \<subj> bucket_ptrs. \<top> \<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    val dynarr \<leftarrow> apply_rule new_dynarr[where T=\<open>\<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<close>] \<semicolon>
    tabl_addr[i] := dynarr \<semicolon>

    define bucket_ptrs' where \<open>bucket_ptrs' \<equiv> list_upd_map i (comb.K addra) bucket_ptrs\<close> \<semicolon>
    fold bucket_ptrs'_def \<semicolon>
    holds_fact [simp]: \<open>addra = bucket_ptrs' ! i\<close>
    have [simp]: \<open>\<big_ast>\<^sup>\<phi> {ia. ia < i} (\<lambda>i. DynArr (bucket_ptrs  ! i) \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>) =
                  \<big_ast>\<^sup>\<phi> {ia. ia < i} (\<lambda>i. DynArr (bucket_ptrs' ! i) \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>)\<close>
      by (rule \<phi>Mul_Quant\<^sub>\<Lambda>_cong, auto_sledgehammer)\<semicolon>

  \<medium_right_bracket> \<semicolon>
  
  val ret \<leftarrow> calloc1 \<open>\<lbrace> tabl: Ptr[\<array>[N] \<ptr>], N: \<nat>(size_\<t>) \<rbrace>\<close> \<semicolon>
  ret.N := N \<semicolon>
  ret.tabl := tabl_addr \<semicolon>
  \<makes> \<open>Map.empty \<Ztypecolon> Hash addra T\<close> \<semicolon>
  ret
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 0]]

proc del_hash:
  input  \<open>f \<Ztypecolon> \<ref> Hash addr T\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  transforms_to \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, tabl, buckets \<semicolon>
  val N \<leftarrow> $addr.N \<semicolon>
  val tabl \<leftarrow> $addr.tabl \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(size_\<t>)\<close>, N)
           \<open>\<lambda>M. buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. M \<le> i \<and> i < ?N} (\<lambda>i. DynArr (bucket_ptrs ! i) \<lbrace>k: \<nat>(size_\<t>), v: T\<rbrace>) \<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    del_dynarr ( tabl[i] )
  \<medium_right_bracket> \<semicolon>
  mfree (tabl) \<semicolon>
  mfree (addr)
\<medium_right_bracket> .


proc entries_of_hash:
  input  \<open>f \<Ztypecolon> \<ref> Hash addr T\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output \<open>addr' \<Ztypecolon> \<val> Ptr\<heavy_comma>
          l \<Ztypecolon> DynArr addr' \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<heavy_comma>
          f \<Ztypecolon> Hash addr T
          \<subj> l addr'. set l = Map.graph f\<close>
\<medium_left_bracket>
  transforms_to \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, tabl, buckets \<semicolon>
  val dynarr \<leftarrow> apply_rule new_dynarr[where T=\<open>\<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>\<close>] \<semicolon>
  val N \<leftarrow> addr.N \<semicolon>
  val tabl \<leftarrow> addr.tabl \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(size_\<t>)\<close>, N)
           \<open>\<lambda>i. l \<Ztypecolon> DynArr addra \<lbrace> k: \<nat>(size_\<t>), v: T \<rbrace>
                \<subj> l. set l = (\<Union>k<i. set (buckets k))\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    concat_dynarr (dynarr, tabl[i]) \<semicolon>
  \<medium_right_bracket> \<semicolon>
  \<makes> \<open>f \<Ztypecolon> Hash addr T\<close> \<semicolon>
  dynarr
\<medium_right_bracket> .


proc rehash:
  input  \<open>f \<Ztypecolon> \<ref> Hash addr  T\<heavy_comma> N \<Ztypecolon> \<val> \<nat>(size_\<t>)\<close>
  premises \<open>0 < N\<close>
       and \<open>\<typeof> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output \<open>f \<Ztypecolon> \<ref> Hash addr' T \<subj> addr'. \<top>\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = Map.graph_def \<semicolon>

  val dynarr \<leftarrow> entries_of_hash (addr) \<semicolon>
  del_hash (addr) \<semicolon>
  val ret \<leftarrow> new_hash (N) T \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (dynarr))
             \<open>\<lambda>i. f \<Ztypecolon> Hash addra T \<subj> f. set (take i l) = Map.graph f\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    val entry \<leftarrow> get_dynarr (dynarr, i) \<semicolon>
    update_hash (ret, entry.k, entry.v)
  \<medium_right_bracket> certified by (clarify, rule exI[where x=\<open>fa(fst (l ! i) \<mapsto> snd (l ! i))\<close>],
                  auto_sledgehammer) \<semicolon>
  del_dynarr (dynarr) \<semicolon>
  ret
\<medium_right_bracket> .


text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm calc_hash_\<phi>app
thm insert_bucket_\<phi>app
thm update_hash_\<phi>app
thm bucket_has_key_\<phi>app
thm hash_has_key_\<phi>app
thm lookup_bucket_\<phi>app
thm hash_lookup_\<phi>app
thm new_hash_\<phi>app
thm del_hash_\<phi>app
thm entries_of_hash_\<phi>app
thm rehash_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm calc_hash_def
thm insert_bucket_def
thm update_hash_def
thm bucket_has_key_def
thm hash_has_key_def
thm lookup_bucket_def
thm hash_lookup_def
thm new_hash_def
thm del_hash_def
thm entries_of_hash_def
thm rehash_def

end