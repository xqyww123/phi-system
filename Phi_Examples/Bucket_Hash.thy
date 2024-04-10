theory Bucket_Hash
  imports PhiEx_Linked_Lst PhiEx_Rational PhiEx_DynArr
begin

abbreviation \<open>\<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t>{k: \<a>\<i>\<n>\<t>, v: \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l>}\<close>

abbreviation \<open>hash (x::nat) n \<equiv> x mod n\<close>

declare [[ML_print_depth = 1000]]



lemma relational_functor_proof_obligation:
  \<open> \<forall>i<length xb. list_all2 (\<lambda>xa xy'. fst xy' = fst xa \<and> x (snd xa) (snd xy')) (xc i) (xd i)
\<Longrightarrow> \<forall>i<length xb. list_all (\<lambda>(k, v). hash k (length xb) = i) (xc i) \<and> distinct (map fst (xc i))
\<Longrightarrow> \<forall>k x. (xa k = Some x) = (\<exists>xa\<in>{..<length xb}. (k, x) \<in> set (xc xa))
\<Longrightarrow> \<exists>uu. (\<forall>i<length xb. list_all (\<lambda>(k, v). hash k (length xb) = i) (uu i) \<and> distinct (map fst (uu i))) \<and>
          (\<exists>uua. (\<forall>k x. (uua k = Some x) = (\<exists>i<length xb. (k, x) \<in> set (uu i))) \<and>
                 dom xa = dom uua \<and>
                 (\<forall>k\<in>dom uua. x (the (xa k)) (the (uua k))) \<and> (\<forall>i<length xb. list_all2 (\<lambda>x y. snd x = snd y \<and> fst x = fst y) (xd i) (uu i))) \<close>
    apply (rule exI[where x=xd], auto simp: list_all2_conv_all_nth list_all_length)
    apply fastforce
    apply (metis (mono_tags, lifting) map_equality_iff)
    subgoal premises prems proof -
      have t1: \<open>\<forall>i<length xb. distinct (map fst (xd i))\<close>
        by (smt (verit) map_equality_iff prems(1) prems(2))
      have t2: \<open>\<exists>i<length xb. (k,v1) \<in> set (xd i)
            \<Longrightarrow> \<exists>i<length xb. (k,v2) \<in> set (xd i)
            \<Longrightarrow> v1 = v2\<close> for k v1 v2
        by (auto, smt (verit, ccfv_SIG) case_prod_beta' eq_key_imp_eq_value fst_conv last_index_less_size_conv local.t1 nth_last_index prems(1) prems(2))  
      have t3: \<open>(\<Union>i<length xb. set (xd i)) `` {k} = {} \<or> (\<exists>v. (\<Union>i<length xb. set (xd i)) `` {k} = {v})\<close> for k
        by (insert t2, auto simp: set_eq_iff, metis lessThan_iff)
      have t4: \<open>\<exists>g. \<forall>k x. g k = Some x \<longleftrightarrow> (\<exists>i<length xb. (k,x) \<in> set (xd i))\<close>
        by (subst choice_iff[symmetric], metis option.sel option.simps(3) t2)

      have t5[simp]: \<open>xa k = Some y \<longleftrightarrow> (\<exists>i<length xb. (k,y) \<in> set (xc i))\<close> for k y
        using prems(3) by auto

      obtain g where g: \<open>\<forall>k x. g k = Some x \<longleftrightarrow> (\<exists>i<length xb. (k,x) \<in> set (xd i))\<close> for k
        using t4 by blast

      show ?thesis
        apply (rule exI[where x=g], auto simp: g)
        apply (metis fst_conv last_index_less_size_conv nth_last_index nth_mem prems(1) surjective_pairing)
        apply (metis fst_conv last_index_less_size_conv nth_last_index nth_mem prems(1) surjective_pairing)
        by (smt (verit, best) fst_conv g in_set_conv_nth option.sel prems(1) prod.collapse t5)
qed .


abbreviation \<open>\<h>\<a>\<s>\<h> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {tabl: \<p>\<t>\<r>, N: \<a>\<i>\<n>\<t>} \<close>


\<phi>type_def Hash :: \<open>logaddr \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, nat \<rightharpoonup> 'x) \<phi>\<close>
  where \<open>f \<Ztypecolon> Hash addr T \<equiv> 
       (tabl_addr, N) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> tabl: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>, N: \<nat> \<rbrace>\<heavy_comma>
       bucket_ptrs \<Ztypecolon> \<m>\<e>\<m>[tabl_addr] \<Aa>\<r>\<r>\<a>\<y>[N] (\<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> \<k>\<v>_\<e>\<n>\<t>\<r>\<y>)\<heavy_comma>
       buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < length bucket_ptrs} (\<lambda>i.
                  Linked_Lst (bucket_ptrs ! i) \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace>k: \<nat>, v: T\<rbrace>)
       \<s>\<u>\<b>\<j> bucket_ptrs buckets tabl_addr N.
          length bucket_ptrs = N \<and>
          (\<forall>i < N. list_all (\<lambda>(k,v). hash k N = i) (buckets i) \<and> distinct (map fst (buckets i))) \<and>
          (\<forall>k x. f k = Some x \<longleftrightarrow> (\<exists>i<N. (k,x) \<in> set (buckets i))) \<and>
          0 < N \<close>

deriving \<open> Abstract_Domain T P
         \<Longrightarrow> Abstract_Domain (Hash addr T) (\<lambda>f. \<forall>k \<in> dom f. P (the (f k)))\<close>
    notes list_all_length[simp] Let_def[simp] set_eq_iff[simp]

and \<open>Object_Equiv T eq
    \<Longrightarrow> Object_Equiv (Hash addr T) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom g. eq (the (f k)) (the (g k))))\<close>
    notes case_prod_beta[simp] list_all2_conv_all_nth[\<phi>sledgehammer_simps] list_all_length[\<phi>sledgehammer_simps]
          image_iff[simp]
    (tactic: auto simp: Ball_def Bex_def set_eq_iff,
        subgoal' for f f' xb buckets tabl_addr \<open>rule exI[where x=\<open>\<lambda>i. map (\<lambda>(k,_). (k, the (f' k))) (buckets i)\<close>]\<close> )

and \<open>Transformation_Functor (Hash addr) (Hash addr) T U ran (\<lambda>_. UNIV) (\<lambda>r f g. dom f = dom g \<and> (\<forall>k \<in> dom g. r (the (f k)) (the (g k))))\<close>
    notes set_eq_iff [\<phi>sledgehammer_simps]
    (tactic: auto, auto_sledgehammer, rule relational_functor_proof_obligation) 

and \<open>Functional_Transformation_Functor (Hash addr) (Hash addr) T U ran (\<lambda>_. UNIV)
          (\<lambda>_ P f. \<forall>k\<in>dom f. P (the (f k))) (\<lambda>h _ f. map_option h o f)\<close>


term \<open>f(a \<mapsto> b)\<close>

declare Suc_le_eq[simp]

term \<open>S \<union> (D::'a set)\<close>
term \<open>r |` S\<close>

proc insert_bucket:
  input \<open>bucket \<Ztypecolon> Linked_Lst addr \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> \<k>\<v>_\<e>\<n>\<t>\<r>\<y>\<heavy_comma> kk \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> vv \<Ztypecolon> \<v>\<a>\<l> T\<close>
  output \<open>bucket' \<Ztypecolon> Linked_Lst addr' \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>
          \<s>\<u>\<b>\<j> bucket' addr'. set bucket' = (set bucket - {(k',_). k' = k}) \<union> {(k,v)}\<close>
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>   
    \<lbrace> k: $kk, v: $vv \<rbrace>
(*    prepend_llist ($addr,  *)




proc update_hash:
  input  \<open>f \<Ztypecolon> Hash addr T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> Hash addr T\<close> 
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> \<exists>c, bucket_ptrs, tabl_addr, buckets \<semicolon>
  val tabl_addr \<leftarrow> $addr \<tribullet> tabl ! \<semicolon>
  val N \<leftarrow> $addr \<tribullet> N ! \<semicolon>
  val hash \<leftarrow> $k % $N \<semicolon>
  $tabl_addr \<tribullet> $hash !


thm mod_\<phi>app



end