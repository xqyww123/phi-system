theory Bucket_Hash2
  imports PhiEx_Linked_Lst PhiEx_Rational Dyn_Arr_arbi
begin

abbreviation \<open>\<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t>{k: \<a>\<i>\<n>\<t>, v: \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l>}\<close>

abbreviation \<open>hash (x::nat) n \<equiv> x mod n\<close>

abbreviation \<open>\<h>\<a>\<s>\<h> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {tabl: \<p>\<t>\<r>, N: \<a>\<i>\<n>\<t>} \<close>

declare [[ML_print_depth = 1000]]

\<phi>type_def Hash :: \<open>logaddr \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, nat \<rightharpoonup> 'x) \<phi>\<close>
  where \<open>f \<Ztypecolon> Hash addr T \<equiv> 
       buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < N} (\<lambda>i.
                  DynArr (bucket_ptrs ! i) \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace>k: \<nat>, v: T\<rbrace>)\<heavy_comma>
       bucket_ptrs \<Ztypecolon> \<m>\<e>\<m>[tabl_addr] \<Aa>\<r>\<r>\<a>\<y>[N] (\<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>)\<heavy_comma>
       (tabl_addr, N) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> tabl: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>, N: \<nat> \<rbrace>
       \<s>\<u>\<b>\<j> bucket_ptrs buckets tabl_addr N.
          length bucket_ptrs = N \<and>
          (\<forall>i < N. list_all (\<lambda>(k,v). hash k N = i) (buckets i) \<and> distinct (map fst (buckets i))) \<and>
          (\<forall>k x. f k = Some x \<longleftrightarrow> (\<exists>i<N. (k,x) \<in> set (buckets i))) \<and>
          0 < N \<and> address_to_base tabl_addr \<and> address_to_base addr \<close>

deriving \<open> Abstract_Domain T P
         \<Longrightarrow> Abstract_Domain (Hash addr T) (\<lambda>f. \<forall>k \<in> dom f. P (the (f k)))\<close>
    notes list_all_length[simp] Let_def[simp] set_eq_iff[simp]

and \<open>Object_Equiv T eq
    \<Longrightarrow> Object_Equiv (Hash addr T) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom g. eq (the (f k)) (the (g k))))\<close>
    notes case_prod_beta[simp] list_all2_conv_all_nth[\<phi>sledgehammer_simps] list_all_length[\<phi>sledgehammer_simps]
          image_iff[simp] domIff[simp]
    (tactic: auto simp: Ball_def Bex_def set_eq_iff,
             subgoal' for f f' xb buckets tabl_addr \<open>rule exI[where x=\<open>\<lambda>i. map (\<lambda>(k,_). (k, the (f' k))) (buckets i)\<close>]\<close> )

and \<open>Transformation_Functor (Hash addr) (Hash addr) T U (\<lambda>_. UNIV) (\<lambda>_. UNIV) (\<lambda>r f g. dom f = dom g \<and> (\<forall>k \<in> dom g. r (the (f k)) (the (g k))))\<close>
    notes set_eq_iff [\<phi>sledgehammer_simps] list_all2_conv_all_nth[\<phi>sledgehammer_simps]
          list_all_length[\<phi>sledgehammer_simps] in_set_conv_nth[\<phi>sledgehammer_simps]
    (tactic:  clarsimp,
              subgoal' for x xa xb xc xd xe \<open>rule exI[where x=xe], (rule conjI)+, (auto_sledgehammer)[1],
                subgoal_tac \<open>\<exists>g. \<forall>k x. g k = Some x \<longleftrightarrow> (\<exists>i<length xb. (k,x) \<in> set (xe i))\<close>,
                clarify, subgoal' for g \<open>rule exI[where x=g]\<close>,
                auto_sledgehammer,
                subgoal_tac \<open>\<And>k v1 v2.
                      \<exists>i<length xb. (k,v1) \<in> set (xe i)
                  \<Longrightarrow> \<exists>i<length xb. (k,v2) \<in> set (xe i)
                  \<Longrightarrow> v1 = v2\<close>,
                subst choice_iff[symmetric]\<close>) 

and \<open>Functional_Transformation_Functor (Hash addr) (Hash addr) T U (\<lambda>_. UNIV) (\<lambda>_. UNIV)
          (\<lambda>_ P f. \<forall>k\<in>dom f. P (the (f k))) (\<lambda>h _ f. map_option h o f)\<close>



context
  fixes T :: \<open>(VAL, 'x) \<phi>\<close>
    and zero :: 'x
  assumes [\<phi>reason add]: \<open>\<phi>SemType (x \<Ztypecolon> T) \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l>\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l> T zero\<close>
begin

proc insert_bucket:
  input \<open>bucket \<Ztypecolon> DynArr addr \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>distinct (map fst bucket)\<close>
  output \<open>bucket' \<Ztypecolon> DynArr addr \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>
          \<s>\<u>\<b>\<j> bucket'. set bucket' = (set bucket - {(k',_). k' = k}) \<union> {(k,v)} \<and>
                        distinct (map fst bucket') \<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  var met \<leftarrow> False ;;
  replicate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr ($addr))
              \<open>\<lambda>i. (map (\<lambda>kv. if fst kv = k then (k,v) else kv) (take i bucket) @ drop i bucket)
                      \<Ztypecolon> DynArr addr \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
                   (\<exists>v. (k,v) \<in> set (take i bucket)) \<Ztypecolon> \<v>\<a>\<r>[met] \<bool>\<close>
  \<medium_left_bracket> \<rightarrow> val i ;;
    val kv \<leftarrow> get_dynarr($addr, $i) ;;
    if ($kv \<tribullet> k = $k) \<medium_left_bracket>
      set_dynarr($addr, $i, \<lbrace> k: $k, v: $v \<rbrace>) ;;
      $met \<leftarrow> True
    \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>
  \<medium_right_bracket> certified by (auto simp add: list_eq_iff_nth_eq nth_append list_update_append; auto_sledgehammer) ;;
  
  if ($met) \<medium_left_bracket> \<medium_right_bracket> \<medium_left_bracket>
    push_dynarr ($addr, \<lbrace> k: $k, v: $v \<rbrace>)
  \<medium_right_bracket>
\<medium_right_bracket> .



declare Suc_le_eq[simp]

proc update_hash:
  input  \<open>f \<Ztypecolon> Hash addr T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> Hash addr T\<close> 
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length ;;

  to \<open>OPEN _ _\<close> \<exists>c, bucket_ptrs, base, buckets \<semicolon>
  val tabl_addr \<leftarrow> $addr \<tribullet> tabl ! \<semicolon>
  val N \<leftarrow> $addr \<tribullet> N ! \<semicolon>
  val hash \<leftarrow> $k % $N \<semicolon>

  insert_bucket ($tabl_addr \<tribullet> $hash !, $k, $v) ;;

  holds_fact [\<phi>safe_simp]: \<open>{i. i < ?N} - ({i. i < ?N} - {hash k ?N}) = {hash k ?N}\<close> ;;

  \<open>_ \<Ztypecolon> \<big_ast>\<^sup>\<phi> _ _ \<close> \<open>f(k \<mapsto> v) \<Ztypecolon> MAKE _ (Hash addr T)\<close>
      certified by (auto, auto_sledgehammer, auto_sledgehammer, auto_sledgehammer,
                    rule exI[where x=\<open>\<lambda>i. if i = hash k ?N then bucket' else buckets i\<close>],
                    subgoal_tac \<open>\<And>k' v. \<lbrakk> (k',v) \<in> set bucket' ; k' \<noteq> k \<rbrakk> \<Longrightarrow> (k', v) \<in> set (buckets (hash k ?N))\<close>,
                    subgoal_tac \<open>\<And>k v i.\<lbrakk> (k,v) \<in> set (buckets i) ; i < ?N \<rbrakk> \<Longrightarrow> hash k ?N = i\<close>;
                    auto_sledgehammer)
\<medium_right_bracket> .





proc new_hash:
  input  \<open>N \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>0 < N\<close>
  output \<open>Map.empty \<Ztypecolon> Hash addr T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h> \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  val tabl_addr \<leftarrow> calloc_aN ($N) \<open>\<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close> ;;
  replicate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, $N)
              \<open>\<lambda>M. (\<lambda>i. []) \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < M} (\<lambda>i. DynArr (bucket_ptrs ! i) \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace>k: \<nat>, v: T\<rbrace>)\<heavy_comma>
                   bucket_ptrs \<Ztypecolon> \<m>\<e>\<m>[addr] \<Aa>\<r>\<r>\<a>\<y>[N] (\<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>)
                   \<s>\<u>\<b>\<j> bucket_ptrs. \<top> \<close>
  \<medium_left_bracket> \<rightarrow> val i ;;
    val dynarr \<leftarrow> apply_rule new_dynarr[where T=\<open>\<lbrace> k: \<nat>, v: T \<rbrace>\<close>] ;;
    $tabl_addr \<tribullet> $i := $dynarr ;;

    define bucket_ptrs' where \<open>bucket_ptrs' \<equiv> list_upd_map i (comb.K addra) bucket_ptrs\<close> ;;
    fold bucket_ptrs'_def ;;
    holds_fact [simp]: \<open>addra = bucket_ptrs' ! i\<close>
           and [simp]: \<open>\<big_ast>\<^sup>\<phi> {ia. ia < i} (\<lambda>i. DynArr (bucket_ptrs ! i) \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>) =
                        \<big_ast>\<^sup>\<phi> {ia. ia < i} (\<lambda>i. DynArr (bucket_ptrs' ! i) \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>)\<close> ;;
    holds_fact [\<phi>safe_simp]: \<open>{ia. ia < Suc i} - {ia. ia < i} = {i}\<close> ;;

    \<open>_ \<Ztypecolon> \<big_ast>\<^sup>\<phi> _ _ \<close>
  \<medium_right_bracket> ;;
  
  val ret \<leftarrow> calloc_1 \<open>\<lbrace> tabl: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>, N: \<nat> \<rbrace>\<close> ;;
  $ret \<tribullet> N := $N ;;
  $ret \<tribullet> tabl := $tabl_addr ;;
  \<open>Map.empty \<Ztypecolon> MAKE _ (Hash addra T)\<close> ;;
  $ret
\<medium_right_bracket> .


proc del_hash:
  input  \<open>f \<Ztypecolon> Hash addr T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h>\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> \<exists>c, bucket_ptrs, tabl, buckets ;;
  val N \<leftarrow> $addr \<tribullet> N ! ;;
  val tabl \<leftarrow> $addr \<tribullet> tabl ! ;;
  replicate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, $N)
              \<open>\<lambda>M. buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. M \<le> i \<and> i < ?N} (\<lambda>i. DynArr (bucket_ptrs ! i) \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace>k: \<nat>, v: T\<rbrace>) \<close>
  \<medium_left_bracket> \<rightarrow> val i ;;
    del_dynarr ($tabl \<tribullet> $i !)
  \<medium_right_bracket> ;;
  mfree ($tabl) ;;
  mfree ($addr) ;;
\<medium_right_bracket> .


proc entries_of_hash:
  input  \<open>f \<Ztypecolon> Hash addr T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h>\<close>
  output \<open>f \<Ztypecolon> Hash addr T\<heavy_comma>
          l \<Ztypecolon> DynArr addr' \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>
          \<s>\<u>\<b>\<j> l addr'. set l = Map.graph f\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> \<exists>c, bucket_ptrs, tabl, buckets ;;
  val dynarr \<leftarrow> apply_rule new_dynarr[where T=\<open>\<lbrace> k: \<nat>, v: T \<rbrace>\<close>] ;;
  val N \<leftarrow> $addr \<tribullet> N ! ;;
  val tabl \<leftarrow> $addr \<tribullet> tabl ! ;;
  replicate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, $N)
              \<open>\<lambda>i. l \<Ztypecolon> DynArr addra \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>
                   \<s>\<u>\<b>\<j> l. set l = (\<Union>k<i. set (buckets k))\<close>
  \<medium_left_bracket> \<rightarrow> val i ;;
    concat_dynarr ($dynarr, $tabl \<tribullet> $i !) ;;
    \<open>_ \<Ztypecolon> \<big_ast>\<^sup>\<phi> _ _ \<close> ;;
    holds_fact [\<phi>safe_simp]: \<open>{i. i < ?N} - ({i. i < ?N} - {i}) = {i}\<close> ;;
  \<medium_right_bracket> ;;
  \<open>f \<Ztypecolon> MAKE _ (Hash addr T)\<close> ;;
  $dynarr
\<medium_right_bracket> .



proc rehash:
  input  \<open>f \<Ztypecolon> Hash addr T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> N \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>0 < N\<close>
  output \<open>f \<Ztypecolon> Hash addr' T\<heavy_comma> addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h> \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = Map.graph_def;;

  val dynarr \<leftarrow> entries_of_hash ($addr) ;;
  del_hash ($addr) ;;
  val ret \<leftarrow> new_hash ($N) ;;
  replicate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr ($dynarr))
              \<open>\<lambda>i. f \<Ztypecolon> Hash addra T
                   \<s>\<u>\<b>\<j> f. set (take i l) = Map.graph f\<close>
  \<medium_left_bracket> \<rightarrow> val i ;;
    val entry \<leftarrow> get_dynarr ($dynarr, $i) ;;
    update_hash ($ret, $entry \<tribullet> k, $entry \<tribullet> v)
  \<medium_right_bracket> certified by (clarify, rule exI[where x=\<open>fa(fst (l ! i) \<mapsto> snd (l ! i))\<close>],
                  auto_sledgehammer) ;;
  del_dynarr ($dynarr) ;;
  $ret
\<medium_right_bracket> .




end



end