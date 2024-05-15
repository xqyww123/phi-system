theory Bucket_Hash
  imports Rational_Arith Dynamic_Array_arbi_len Phi_Semantics.PhiSem_Mem_C_MI
          PhiStd.PhiStd_Slice
          "HOL-Data_Structures.AList_Upd_Del"
begin

text \<open>We ignore arithmetic overflow in the length of a dynamic array,
      because otherwise the hash table cannot be specified in the expected way.
      However, we still consider arithmetic overflow in any other cases.\<close>

declare Suc_le_eq[simp]

abbreviation \<open>\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY \<equiv> \<s>\<t>\<r>\<u>\<c>\<t>{k: \<s>\<i>\<z>\<e>_\<t>, v: TY}\<close>

abbreviation \<open>hash (x::nat) n \<equiv> x mod n\<close>

abbreviation \<open>\<h>\<a>\<s>\<h> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {tabl: \<p>\<t>\<r>, N: \<s>\<i>\<z>\<e>_\<t>} \<close>


\<phi>type_def Hash :: \<open>address \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, nat \<rightharpoonup> 'x) \<phi>\<close>
  where \<open>f \<Ztypecolon> Hash addr TY T \<equiv> 
       (tabl_addr, N) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> tabl: \<bbbP>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>, N: \<nat>(\<s>\<i>\<z>\<e>_\<t>) \<rbrace>\<heavy_comma>
        bucket_ptrs \<Ztypecolon> \<m>\<e>\<m>[tabl_addr] \<bbbA>\<r>\<r>\<a>\<y>[N] (\<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>)\<heavy_comma>
        buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < N} (\<lambda>i. DynArr (bucket_ptrs ! i) (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace>k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T\<rbrace>)
       \<s>\<u>\<b>\<j> bucket_ptrs buckets tabl_addr N.
           length bucket_ptrs = N \<and>
           (\<forall>i < N. list_all (\<lambda>(k,v). hash k N = i) (buckets i) \<and> distinct (map fst (buckets i))) \<and>
           (\<forall>k x. f k = Some x \<longleftrightarrow> (\<exists>i<N. (k,x) \<in> set (buckets i))) \<and>
           0 < N \<and> address_to_base tabl_addr \<and> address_to_base addr \<close>

deriving \<open> Abstract_Domain T P
       \<Longrightarrow> Abstract_Domain (Hash addr TY T) (\<lambda>f. \<forall>k \<in> dom f. P (the (f k)))\<close>
    notes list_all_length[simp] Let_def[simp] set_eq_iff[simp]

  and \<open>   Object_Equiv T eq
      \<Longrightarrow> Object_Equiv (Hash addr TY T) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom g. eq (the (f k)) (the (g k))))\<close>
    notes case_prod_beta[simp] list_all2_conv_all_nth[\<phi>sledgehammer_simps] list_all_length[\<phi>sledgehammer_simps]
          image_iff[simp] domIff[simp]
    (tactic: auto simp: Ball_def Bex_def set_eq_iff,
             subgoal' for f f' xb buckets tabl_addr \<open>rule exI[where x=\<open>\<lambda>i. map (\<lambda>(k,_). (k, the (f' k))) (buckets i)\<close>]\<close> )

  and \<open>Transformation_Functor (Hash addr TY) (Hash addr TY) T U (\<lambda>_. UNIV) (\<lambda>_. UNIV)
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

  and \<open>Functional_Transformation_Functor (Hash addr TY) (Hash addr TY) T U (\<lambda>_. UNIV) (\<lambda>_. UNIV)
            (\<lambda>_ P f. \<forall>k\<in>dom f. P (the (f k))) (\<lambda>h _ f. map_option h o f)\<close>

declare [[\<phi>trace_reasoning = 1]]

proc calc_hash:
  input  \<open>k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> N \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>
  premises \<open>N \<noteq> 0\<close>
  output \<open>hash k N \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>
\<medium_left_bracket>
  k % N
\<medium_right_bracket> .

context
  fixes T :: \<open>(VAL, 'x) \<phi>\<close>
    and TY :: TY
    and zero :: 'x
  assumes [\<phi>reason add]: \<open>Semantic_Type T TY\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY T zero\<close>
begin

proc insert_bucket:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma>
         bucket \<Ztypecolon> DynArr addr (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<close>
  premises \<open>distinct (map fst bucket)\<close>
  output \<open>bucket' \<Ztypecolon> DynArr addr (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>
          \<s>\<u>\<b>\<j> bucket'. set bucket' = (set bucket - {(k',_). k' = k}) \<union> {(k,v)} \<and>
                        distinct (map fst bucket') \<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  var met \<leftarrow> False \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
              \<open>\<lambda>i. (\<exists>v. (k,v) \<in> set (take i bucket)) \<Ztypecolon> \<v>\<a>\<r>[met] \<bool>\<heavy_comma>
                   (map (\<lambda>kv. if fst kv = k then (k,v) else kv) (take i bucket) @ drop i bucket)
                        \<Ztypecolon> DynArr addr (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<close>
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
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> f \<Ztypecolon> Hash addr TY T\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> Hash addr TY T\<close> 
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length ;;

  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, base, buckets \<semicolon>
  val tabl_addr \<leftarrow> addr.tabl ! \<semicolon>
  val N \<leftarrow> addr.N ! \<semicolon>
  val hash \<leftarrow> calc_hash (k, N) \<semicolon>

  insert_bucket (tabl_addr[hash]!, k, v) \<semicolon>

  \<m>\<a>\<k>\<e>\<s> \<open>f(k \<mapsto> v) \<Ztypecolon> Hash addr TY T\<close>
  certified by (auto, auto_sledgehammer, auto_sledgehammer, auto_sledgehammer,
                rule exI[where x=\<open>\<lambda>i. if i = hash k ?N then bucket' else buckets i\<close>],
                    subgoal_tac \<open>\<And>k' v. \<lbrakk> (k',v) \<in> set bucket' ; k' \<noteq> k \<rbrakk> \<Longrightarrow> (k', v) \<in> set (buckets (hash k ?N))\<close>,
                    subgoal_tac \<open>\<And>k v i.\<lbrakk> (k,v) \<in> set (buckets i) ; i < ?N \<rbrakk> \<Longrightarrow> hash k ?N = i\<close>,
                clarsimp, rule conjI, auto_sledgehammer, rule conjI, auto_sledgehammer,
                rule exI[where x=\<open>\<lambda>i. if i = hash k ?N then bucket' else buckets i\<close>],
                auto_sledgehammer, auto_sledgehammer, auto_sledgehammer)
\<medium_right_bracket> .

proc bucket_has_key:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
          bucket \<Ztypecolon> DynArr addr (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<close>
  output \<open>(\<exists>v. (k,v) \<in> set bucket) \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma>
          bucket \<Ztypecolon> DynArr addr (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<close>
\<medium_left_bracket>
  var met \<leftarrow> False \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr(addr))
              \<open>\<lambda>i. (\<exists>v. (k,v) \<in> set (take i bucket)) \<Ztypecolon> \<v>\<a>\<r>[met] \<bool>\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    met \<leftarrow> met \<or> (get_dynarr(addr, i).k = k)
  \<medium_right_bracket> \<semicolon>
  met
\<medium_right_bracket> .

proc hash_has_key:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> f \<Ztypecolon> Hash addr TY T\<close>
  output \<open>k \<in> dom f \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> f \<Ztypecolon> Hash addr TY T\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length \<semicolon>

  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, base, buckets \<semicolon>
  val tabl_addr \<leftarrow> addr.tabl ! \<semicolon>
  val N \<leftarrow> addr.N ! \<semicolon>
  val hash \<leftarrow> k % N \<semicolon>
  val ret \<leftarrow> bucket_has_key (tabl_addr[hash]!, k) \<semicolon>

  \<m>\<a>\<k>\<e>\<s> \<open>f \<Ztypecolon> Hash addr TY T\<close> \<semicolon>

  ret
\<medium_right_bracket> .



proc lookup_bucket:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
         bucket \<Ztypecolon> DynArr addr (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<close>
  premises \<open>\<exists>v. (k,v) \<in> set bucket\<close>
  output \<open>v \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma>
          bucket \<Ztypecolon> DynArr addr (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>
          \<s>\<u>\<b>\<j> v. (k,v) \<in> set bucket\<close>
\<medium_left_bracket>
  var ret \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
              \<open>\<lambda>i. v \<Ztypecolon> \<m>\<a>\<y> \<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[ret] T
                   \<s>\<u>\<b>\<j> v v'. (\<exists>v. (k,v) \<in> set (take i bucket)) \<longrightarrow> v = Some v' \<and> (k,v') \<in> set (take i bucket)\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    val entry \<leftarrow> get_dynarr(addr, i) \<semicolon>
    if (entry.k = k) \<medium_left_bracket> 
      ret \<leftarrow> entry.v
    \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> \<semicolon>
  \<medium_right_bracket> \<semicolon>
  ret
\<medium_right_bracket> .


proc hash_lookup:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> f \<Ztypecolon> Hash addr TY T\<close>
  premises \<open>k \<in> dom f\<close>
  output \<open>the (f k) \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> f \<Ztypecolon> Hash addr TY T\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length \<semicolon>

  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, base, buckets \<semicolon>
  val tabl_addr \<leftarrow> addr.tabl ! \<semicolon>
  val N \<leftarrow> addr.N ! \<semicolon>
  val hash \<leftarrow> k % N \<semicolon>
  val ret \<leftarrow> lookup_bucket (tabl_addr[hash] !, k) \<semicolon>

  \<m>\<a>\<k>\<e>\<s> \<open>f \<Ztypecolon> Hash addr TY T\<close> \<semicolon>

  ret
\<medium_right_bracket> .


proc new_hash:
  input  \<open>N \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>
  premises \<open>0 < N\<close>
  output \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> Map.empty \<Ztypecolon> Hash addr TY T \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  val tabl_addr \<leftarrow> calloc (N) \<open>\<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close> \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>, N)
           \<open>\<lambda>M. bucket_ptrs \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[N] (\<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>)\<heavy_comma>
                (\<lambda>i. []) \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < M} (\<lambda>i. DynArr (bucket_ptrs ! i) (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace>k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T\<rbrace>)
                \<s>\<u>\<b>\<j> bucket_ptrs. \<top> \<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    val dynarr \<leftarrow> apply_rule new_dynarr[where T=\<open>\<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<close>] \<semicolon>
    tabl_addr[i] := dynarr \<semicolon>

    define bucket_ptrs' where \<open>bucket_ptrs' \<equiv> list_upd_map i (comb.K addra) bucket_ptrs\<close> \<semicolon>
    fold bucket_ptrs'_def \<semicolon>
    holds_fact [simp]: \<open>addra = bucket_ptrs' ! i\<close>
    have [simp]: \<open>\<big_ast>\<^sup>\<phi> {ia. ia < i} (\<lambda>i. DynArr (bucket_ptrs ! i) (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>) =
                  \<big_ast>\<^sup>\<phi> {ia. ia < i} (\<lambda>i. DynArr (bucket_ptrs' ! i) (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>)\<close>
      by (rule \<phi>Mul_Quant\<^sub>\<Lambda>_cong, auto_sledgehammer)\<semicolon>

  \<medium_right_bracket> \<semicolon>
  
  val ret \<leftarrow> calloc1 \<open>\<lbrace> tabl: \<bbbP>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>, N: \<nat>(\<s>\<i>\<z>\<e>_\<t>) \<rbrace>\<close> \<semicolon>
  ret.N := N \<semicolon>
  ret.tabl := tabl_addr \<semicolon>
  \<m>\<a>\<k>\<e>\<s> \<open>Map.empty \<Ztypecolon> Hash addra TY T\<close> \<semicolon>
  ret
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 0]]

proc del_hash:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> f \<Ztypecolon> Hash addr TY T\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, tabl, buckets \<semicolon>
  val N \<leftarrow> $addr.N ! \<semicolon>
  val tabl \<leftarrow> $addr.tabl ! \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>, N)
           \<open>\<lambda>M. buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. M \<le> i \<and> i < ?N} (\<lambda>i. DynArr (bucket_ptrs ! i) (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace>k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T\<rbrace>) \<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    del_dynarr ( tabl[i]! ) 
  \<medium_right_bracket> \<semicolon>
  mfree (tabl) \<semicolon>
  mfree (addr)
\<medium_right_bracket> .


proc entries_of_hash:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> f \<Ztypecolon> Hash addr TY T\<close>
  output \<open>addr' \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma>
          l \<Ztypecolon> DynArr addr' (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<heavy_comma>
          f \<Ztypecolon> Hash addr TY T
          \<s>\<u>\<b>\<j> l addr'. set l = Map.graph f\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<exists>bucket_ptrs, tabl, buckets \<semicolon>
  val dynarr \<leftarrow> apply_rule new_dynarr[where T=\<open>\<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>\<close>] \<semicolon>
  val N \<leftarrow> addr.N ! \<semicolon>
  val tabl \<leftarrow> addr.tabl ! \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>, N)
           \<open>\<lambda>i. l \<Ztypecolon> DynArr addra (\<k>\<v>_\<e>\<n>\<t>\<r>\<y> TY) \<lbrace> k: \<nat>(\<s>\<i>\<z>\<e>_\<t>), v: T \<rbrace>
                \<s>\<u>\<b>\<j> l. set l = (\<Union>k<i. set (buckets k))\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    concat_dynarr (dynarr, tabl[i]!) \<semicolon>
  \<medium_right_bracket> \<semicolon>
  \<m>\<a>\<k>\<e>\<s> \<open>f \<Ztypecolon> Hash addr TY T\<close> \<semicolon>
  dynarr
\<medium_right_bracket> .



proc rehash:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> N \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> f \<Ztypecolon> Hash addr  TY T\<close>
  premises \<open>0 < N\<close>
  output \<open>addr' \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> f \<Ztypecolon> Hash addr' TY T \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = Map.graph_def \<semicolon>

  val dynarr \<leftarrow> entries_of_hash (addr) \<semicolon>
  del_hash (addr) \<semicolon>
  val ret \<leftarrow> new_hash (N) \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (dynarr))
              \<open>\<lambda>i. f \<Ztypecolon> Hash addra TY T \<s>\<u>\<b>\<j> f. set (take i l) = Map.graph f\<close>
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

end