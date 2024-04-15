theory Bucket_Hash
  imports PhiEx_Linked_Lst PhiEx_Rational Dyn_Arr_arbi
begin

abbreviation \<open>\<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t>{k: \<a>\<i>\<n>\<t>, v: \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l>}\<close>

abbreviation \<open>hash (x::nat) n \<equiv> x mod n\<close>

declare [[ML_print_depth = 1000]]








(*
lemma
  \<open> \<forall>a. a \<in> ran xa \<longrightarrow> Inhabited (a \<Ztypecolon> T) \<longrightarrow> (\<exists>xa. x a xa \<and> Inhabited (xa \<Ztypecolon> U)) \<Longrightarrow>
     \<forall>i<xd. list_all2 (\<lambda>xa xy'. fst xy' = fst xa \<and> x (snd xa) (snd xy')) (xb i) (xe i) \<Longrightarrow>
     \<forall>i<xd. list_all (\<lambda>(k, v). hash k xd = i) (xb i) \<and> distinct (map fst (xb i)) \<Longrightarrow>
     \<forall>k x. (xa k = Some x) = (\<exists>i<xd. (k, x) \<in> set (xb i)) \<Longrightarrow>
     0 < xd \<Longrightarrow>
     memaddr.blk addr \<noteq> Null \<Longrightarrow>
     \<forall>i<xd. list_all (\<lambda>x. Inhabited (snd x \<Ztypecolon> U)) (xe i) \<Longrightarrow>
     \<exists>uu. (\<forall>i<xd. list_all (\<lambda>(k, v). hash k xd = i) (uu i) \<and> distinct (map fst (uu i))) \<and>
          (\<exists>uua. (\<forall>k x. (uua k = Some x) = (\<exists>i<xd. (k, x) \<in> set (uu i))) \<and>
                 dom xa = dom uua \<and> (\<forall>k\<in>dom uua. x (the (xa k)) (the (uua k))) \<and> (\<forall>i<xd. xe i = uu i)) \<close>
apply (rule exI[where x=xe], auto simp: list_all2_conv_all_nth list_all_length)

lemma relational_functor_proof_obligation:
  \<open> \<forall>i<length xb. list_all2 (\<lambda>xa xy'. fst xy' = fst xa \<and> x (snd xa) (snd xy')) (xc i) (xd i)
\<Longrightarrow> \<forall>i<length xb. list_all (\<lambda>(k, v). hash k (length xb) = i) (xc i) \<and> distinct (map fst (xc i))
\<Longrightarrow> \<forall>k x. (xa k = Some x) = (\<exists>i<length xb. (k, x) \<in> set (xc i))
\<Longrightarrow> \<exists>uu. (\<forall>i<length xb. list_all (\<lambda>(k, v). hash k (length xb) = i) (uu i) \<and> distinct (map fst (uu i))) \<and>
          (\<exists>uua. (\<forall>k x. (uua k = Some x) = (\<exists>i<length xb. (k, x) \<in> set (uu i))) \<and>
                 dom xa = dom uua \<and> (\<forall>k\<in>dom uua. x (the (xa k)) (the (uua k))) \<and> (\<forall>i<length xb. xd i = uu i)) \<close>
    apply (rule exI[where x=xd], auto simp: list_all2_conv_all_nth list_all_length)
    apply auto_sledgehammer
    apply auto_sledgehammer
    subgoal premises prems proof -
      have t1: \<open>\<forall>i<length xb. distinct (map fst (xd i))\<close>
        by auto_sledgehammer
      have t2: \<open>\<exists>i<length xb. (k,v1) \<in> set (xd i)
            \<Longrightarrow> \<exists>i<length xb. (k,v2) \<in> set (xd i)
            \<Longrightarrow> v1 = v2\<close> for k v1 v2
        by auto_sledgehammer  
      have t3: \<open>(\<Union>i<length xb. set (xd i)) `` {k} = {} \<or> (\<exists>v. (\<Union>i<length xb. set (xd i)) `` {k} = {v})\<close> for k
        by (insert t2, auto simp: set_eq_iff, auto_sledgehammer)
      have t4: \<open>\<exists>g. \<forall>k x. g k = Some x \<longleftrightarrow> (\<exists>i<length xb. (k,x) \<in> set (xd i))\<close>
        by (subst choice_iff[symmetric], auto_sledgehammer)

      have t5[simp]: \<open>xa k = Some y \<longleftrightarrow> (\<exists>i<length xb. (k,y) \<in> set (xc i))\<close> for k y
        by auto_sledgehammer

      obtain g where g: \<open>\<forall>k x. g k = Some x \<longleftrightarrow> (\<exists>i<length xb. (k,x) \<in> set (xd i))\<close>
        by auto_sledgehammer

      show ?thesis
        by (rule exI[where x=g], auto simp: g; auto_sledgehammer)
        (*apply (metis fst_conv last_index_less_size_conv nth_last_index nth_mem prems(1) surjective_pairing)
        apply (metis fst_conv last_index_less_size_conv nth_last_index nth_mem prems(1) surjective_pairing)
        by (smt (verit, best) fst_conv g in_set_conv_nth option.sel prems(1) prod.collapse t5) *)
qed .
*)

abbreviation \<open>\<h>\<a>\<s>\<h> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {tabl: \<p>\<t>\<r>, N: \<a>\<i>\<n>\<t>} \<close>



\<phi>type_def Bucket :: \<open>logaddr \<Rightarrow> nat \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x list) \<phi>\<close>
  where \<open>bucket \<Ztypecolon> Bucket base i TY T \<equiv> ptr \<Ztypecolon> \<m>\<e>\<m>[base \<tribullet>\<^sub>a i\<^sup>\<t>\<^sup>\<h>] (\<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma>
                                       bucket \<Ztypecolon> Linked_Lst ptr TY T
                                       \<s>\<u>\<b>\<j> ptr. \<top>\<close>
  deriving \<open> Abstract_Domain T P
         \<Longrightarrow> Abstract_Domain (Bucket base i TY T) (list_all P)\<close>
       and \<open> Object_Equiv T eq
         \<Longrightarrow> Object_Equiv (Bucket base i TY T) (list_all2 eq) \<close>
       and \<open> Transformation_Functor (Bucket base i TY) (Bucket base i TY) T U set (\<lambda>_. UNIV) list_all2 \<close>
       and \<open> Functional_Transformation_Functor
                (Bucket base i TY) (Bucket base i TY) T U set (\<lambda>_. UNIV)
                (\<lambda>f P. list_all P) (\<lambda>f P. map f)\<close>  




\<phi>type_def Hash :: \<open>logaddr \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, nat \<rightharpoonup> 'x) \<phi>\<close>
  where \<open>f \<Ztypecolon> Hash addr T \<equiv> 
       buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < N} (\<lambda>i. Bucket base i \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace>k: \<nat>, v: T\<rbrace>)\<heavy_comma>
       (base, N) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> tabl: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>, N: \<nat> \<rbrace>
       \<s>\<u>\<b>\<j> buckets base N.
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
        subgoal' for f f' buckets tabl_addr \<open>rule exI[where x=\<open>\<lambda>i. map (\<lambda>(k,_). (k, the (f' k))) (buckets i)\<close>]\<close>,
        auto_sledgehammer,
        subgoal' for f f' buckets xx tabl_addr \<open>rule exI[where x=\<open>\<lambda>i. map (\<lambda>(k,_). (k, the (f' k))) (buckets i)\<close>]\<close>)
  

and \<open>Transformation_Functor (Hash addr) (Hash addr) T U ran (\<lambda>_. UNIV) (\<lambda>r f g. dom f = dom g \<and> (\<forall>k \<in> dom g. r (the (f k)) (the (g k))))\<close>
    notes set_eq_iff [\<phi>sledgehammer_simps] list_all2_conv_all_nth[\<phi>sledgehammer_simps]
          list_all_length[\<phi>sledgehammer_simps] in_set_conv_nth[\<phi>sledgehammer_simps]
    (tactic: clarsimp, (rule conjI)+, auto_sledgehammer, clarify,
        subgoal' for x xa xb xc xd xe \<open>rule exI[where x=xe], (rule conjI)+, (auto_sledgehammer)[1],
          subgoal_tac \<open>\<exists>g. \<forall>k x. g k = Some x \<longleftrightarrow> (\<exists>i<xd. (k,x) \<in> set (xe i))\<close>,
          clarify, subgoal' for g \<open>rule exI[where x=g]\<close>,
          auto_sledgehammer,
          subgoal_tac \<open>\<And>k v1 v2.
                \<exists>i<xd. (k,v1) \<in> set (xe i)
            \<Longrightarrow> \<exists>i<xd. (k,v2) \<in> set (xe i)
            \<Longrightarrow> v1 = v2\<close>,
          subst choice_iff[symmetric]\<close>) 

and \<open>Functional_Transformation_Functor (Hash addr) (Hash addr) T U ran (\<lambda>_. UNIV)
          (\<lambda>_ P f. \<forall>k\<in>dom f. P (the (f k))) (\<lambda>h _ f. map_option h o f)\<close>













(*
\<phi>type_def Hash :: \<open>logaddr \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, nat \<rightharpoonup> 'x) \<phi>\<close>
  where \<open>f \<Ztypecolon> Hash addr T \<equiv> 
       buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. i < N} (\<lambda>i.
                  Linked_Lst (bucket_ptrs ! i) \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace>k: \<nat>, v: T\<rbrace>)\<heavy_comma>
       bucket_ptrs \<Ztypecolon> \<m>\<e>\<m>[tabl_addr] \<Aa>\<r>\<r>\<a>\<y>[N] (\<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> \<k>\<v>_\<e>\<n>\<t>\<r>\<y>)\<heavy_comma>
       (tabl_addr, N) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> tabl: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>, N: \<nat> \<rbrace>
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
          image_iff[simp] domIff[simp]
    (tactic: auto simp: Ball_def Bex_def set_eq_iff,
        subgoal' for f f' xb buckets tabl_addr \<open>rule exI[where x=\<open>\<lambda>i. map (\<lambda>(k,_). (k, the (f' k))) (buckets i)\<close>]\<close> )

and \<open>Transformation_Functor (Hash addr) (Hash addr) T U ran (\<lambda>_. UNIV) (\<lambda>r f g. dom f = dom g \<and> (\<forall>k \<in> dom g. r (the (f k)) (the (g k))))\<close>
    notes set_eq_iff [\<phi>sledgehammer_simps]
    (tactic: auto, auto_sledgehammer, rule relational_functor_proof_obligation) 

and \<open>Functional_Transformation_Functor (Hash addr) (Hash addr) T U ran (\<lambda>_. UNIV)
          (\<lambda>_ P f. \<forall>k\<in>dom f. P (the (f k))) (\<lambda>h _ f. map_option h o f)\<close>
*)


context
  fixes T :: \<open>(VAL, 'x) \<phi>\<close>
    and zero :: 'x
  assumes [\<phi>reason add]: \<open>\<phi>SemType (x \<Ztypecolon> T) \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l>\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l> T zero\<close>
begin

proc insert_bucket:
  input \<open>bucket \<Ztypecolon> Linked_Lst addr \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> \<k>\<v>_\<e>\<n>\<t>\<r>\<y>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>distinct (map fst bucket)\<close>
  output \<open>bucket' \<Ztypecolon> Linked_Lst addr' \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> \<k>\<v>_\<e>\<n>\<t>\<r>\<y>
          \<s>\<u>\<b>\<j> bucket' addr'. set bucket' = (set bucket - {(k',_). k' = k}) \<union> {(k,v)} \<and>
                             distinct (map fst bucket') \<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>   
    val ret \<leftarrow> prepend_llist ($addr, \<lbrace> k: $k, v: $v \<rbrace>) ;;
    return ($ret)
  \<medium_right_bracket> \<medium_left_bracket>
    to \<open>OPEN 1 _\<close> ;;
    if ($addr \<tribullet> data \<tribullet> k! = $k) \<medium_left_bracket>
      $addr \<tribullet> data \<tribullet> v := $v ;;
      \<open>MAKE 1 (Linked_Lst addr _ _)\<close> ;;
      return ($addr) (* certified by (simp, rule exI[where x=\<open>(k, v) # tl bucket\<close>], auto_sledgehammer) *)
    \<medium_right_bracket> \<medium_left_bracket>
      val addr' \<leftarrow> insert_bucket ($addr \<tribullet> nxt!, $k, $v) ;;
      $addr \<tribullet> nxt := $addr' ;;
      \<open>MAKE 1 (Linked_Lst addr _ _)\<close> ;;
      return ($addr)
    \<medium_right_bracket>
  \<medium_right_bracket>   
\<medium_right_bracket> .


(*
proc insert_bucket':
  input \<open>bucket \<Ztypecolon> Bucket base i \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
         base \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<t>\<r>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>distinct (map fst bucket)\<close>
  output \<open>bucket' \<Ztypecolon> Bucket base i \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>
          \<s>\<u>\<b>\<j> bucket'. set bucket' = (set bucket - {(k',_). k' = k}) \<union> {(k,v)} \<and>
                       distinct (map fst bucket')\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  $base 
*)


(*

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

*)





(*


proc insert_bucket:
  input \<open>bucket \<Ztypecolon> Linked_Lst addr \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> \<k>\<v>_\<e>\<n>\<t>\<r>\<y>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>distinct (map fst bucket)\<close>
  output \<open>bucket' \<Ztypecolon> Linked_Lst addr' \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> \<k>\<v>_\<e>\<n>\<t>\<r>\<y>
          \<s>\<u>\<b>\<j> bucket' addr'. set bucket' = (set bucket - {(k',_). k' = k}) \<union> {(k,v)} \<and>
                             distinct (map fst bucket') \<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>   
    val ret \<leftarrow> prepend_llist ($addr, \<lbrace> k: $k, v: $v \<rbrace>) ;;
    return ($ret)
  \<medium_right_bracket> \<medium_left_bracket>
    to \<open>OPEN 1 _\<close> ;;
    if ($addr \<tribullet> data \<tribullet> k! = $k) \<medium_left_bracket>
      $addr \<tribullet> data \<tribullet> v := $v ;;
      \<open>MAKE 1 (Linked_Lst addr _ _)\<close> ;;
      return ($addr) (* certified by (simp, rule exI[where x=\<open>(k, v) # tl bucket\<close>], auto_sledgehammer) *)
    \<medium_right_bracket> \<medium_left_bracket>
      val addr' \<leftarrow> insert_bucket ($addr \<tribullet> nxt!, $k, $v) ;;
      $addr \<tribullet> nxt := $addr' ;;
      \<open>MAKE 1 (Linked_Lst addr _ _)\<close> ;;
      return ($addr)
    \<medium_right_bracket>
  \<medium_right_bracket>   
\<medium_right_bracket> .
(*    prepend_llist ($addr,  *)
*)

declare Suc_le_eq[simp]

proc update_hash:
  input  \<open>f \<Ztypecolon> Hash addr T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<h>\<a>\<s>\<h>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> Hash addr T\<close> 
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_all2_conv_all_nth list_all_length ;;

  to \<open>OPEN _ _\<close> \<exists>c, bucket_ptrs, N, buckets \<semicolon>
  val tabl_addr \<leftarrow> $addr \<tribullet> tabl ! \<semicolon>
  val N \<leftarrow> $addr \<tribullet> N ! \<semicolon>
  val hash \<leftarrow> $k % $N \<semicolon>

  \<open>Bucket bucket_ptrs ?hash \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>\<close> to \<open>OPEN _ _\<close> \<semicolon>

  val new_bucket \<leftarrow> insert_bucket ($tabl_addr \<tribullet> $hash !, $k, $v) ;;
  $tabl_addr \<tribullet> $hash := $new_bucket ;;

  \<open>MAKE _ (Bucket bucket_ptrs ?hash \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>)\<close> ;;

  holds_fact [\<phi>safe_simp]: \<open>{i. i < N} - ({i. i < N} - {hash k N}) = {hash k N}\<close> ;;
  \<open>_ \<Ztypecolon> \<big_ast>\<^sup>\<phi> ({i. i < N} - {hash k N}) (\<lambda>i. Bucket bucket_ptrs i \<k>\<v>_\<e>\<n>\<t>\<r>\<y> \<lbrace> k: \<nat>, v: T \<rbrace>) \<close> ;;

  \<open>f(k \<mapsto> v) \<Ztypecolon> MAKE _ (Hash addr T)\<close>
      certified by (auto, auto_sledgehammer,
                    rule exI[where x=\<open>\<lambda>i. if i = hash k N then bucket' else buckets i\<close>],
                    subgoal_tac \<open>\<And>k' v. \<lbrakk> (k',v) \<in> set bucket' ; k' \<noteq> k \<rbrakk> \<Longrightarrow> (k', v) \<in> set (buckets (hash k N))\<close>,
                    subgoal_tac \<open>\<And>k v i.\<lbrakk> (k,v) \<in> set (buckets i) ; i < N \<rbrakk> \<Longrightarrow> hash k N = i\<close>;
                    auto_sledgehammer)
\<medium_right_bracket> .




proc new_hash:
  input  \<open>N \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>Map.empty \<Ztypecolon> Hash addr T \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  val tabl_addr \<leftarrow> calloc_aN ($N) \<open>\<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close> ;;




end