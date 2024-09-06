theory PhiSem_Aggregate_Array
  imports PhiSem_Aggregate_Base
  abbrevs "<Array>" = "\<bbbA>\<r>\<r>\<a>\<y>"
      and "<array>" = "\<a>\<r>\<r>\<a>\<y>"
begin

section \<open>Semantics\<close>

debt_axiomatization mk_array_T :: \<open>nat \<Rightarrow> TY \<Rightarrow> TY\<close> ("\<a>\<r>\<r>\<a>\<y>[_] _" [20, 910] 910)
                and sem_mk_array   :: \<open>VAL list \<Rightarrow> VAL\<close>
                and sem_dest_array :: \<open>VAL \<Rightarrow> VAL list\<close>
  where sem_mk_dest_array[simp]: \<open>sem_dest_array (sem_mk_array vs) = vs\<close>
  and   semty_array_eq_poison[simp]: \<open>\<a>\<r>\<r>\<a>\<y>[N] T = \<p>\<o>\<i>\<s>\<o>\<n> \<longleftrightarrow> (T = \<p>\<o>\<i>\<s>\<o>\<n> \<and> N \<noteq> 0)\<close>
  and   WT_arr[simp]:   \<open>Well_Type (\<a>\<r>\<r>\<a>\<y>[n] t) = { sem_mk_array vs |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs }\<close>
  and   semty_arr_uniq: \<open>sem_mk_array vs \<in> Well_Type TY \<Longrightarrow> \<exists>T. TY = mk_array_T (length vs) T\<close>
  and   zero_arr[simp]: \<open>\<a>\<r>\<r>\<a>\<y>[N] T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<Longrightarrow> Zero (\<a>\<r>\<r>\<a>\<y>[N] T)  = map_option (\<lambda>z. sem_mk_array (replicate N z)) (Zero T)\<close>
  and   idx_step_type_arr [eval_aggregate_path] : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> N \<noteq> 0 \<Longrightarrow> idx_step_type (AgIdx_N i) (\<a>\<r>\<r>\<a>\<y>[N] T) = T\<close>
  and   valid_idx_step_arr[eval_aggregate_path] : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<Longrightarrow> valid_idx_step (\<a>\<r>\<r>\<a>\<y>[N] T) j \<longleftrightarrow> j \<in> {AgIdx_N i | i. i < N}\<close>
  and   idx_step_value_arr[eval_aggregate_path] : \<open>idx_step_value (AgIdx_N i) (sem_mk_array vs) = vs!i\<close>
  and   idx_step_mod_value_arr : \<open>idx_step_mod_value (AgIdx_N i) f (sem_mk_array vs) = sem_mk_array (vs[i := f (vs!i)])\<close>
  and   type_measure_arr : \<open>type_measure (\<a>\<r>\<r>\<a>\<y>[N] T) = (if T = \<p>\<o>\<i>\<s>\<o>\<n> \<or> N = 0 then 0 else Suc (type_measure T))\<close>
  and   V_arr_sep_disj[simp]:
            \<open>sem_mk_array vs1 ## sem_mk_array vs2 \<longleftrightarrow> list_all2 (##) vs1 vs2\<close>
  and   V_arr_mult[simp]:
            \<open>sem_mk_array vs1 * sem_mk_array vs2 = sem_mk_array (map2 (*) vs1 vs2)\<close>
  and   V_arr_sep_disj_R:
            \<open>sem_mk_array vs1 ## vs2' \<Longrightarrow> (\<exists>vs. vs2' = sem_mk_array vs)\<close>
  and   V_named_tup_sep_disj_L:
            \<open>vs1' ## sem_mk_array vs2 \<Longrightarrow> (\<exists>vs. vs1' = sem_mk_array vs)\<close>

lemma sem_mk_array_inj[simp]:
  \<open>sem_mk_array vs1 = sem_mk_array vs2 \<equiv> vs1 = vs2\<close>
  by (smt (verit, best) sem_mk_dest_array)

lemma list_all_replicate[simp]:
  \<open>list_all P (replicate n x) \<longleftrightarrow> n = 0 \<or> P x\<close>
  by (induct n; simp; blast)

lemma \<a>\<r>\<r>\<a>\<y>_0_eq_any:
  \<open>\<a>\<r>\<r>\<a>\<y>[0] A = \<a>\<r>\<r>\<a>\<y>[0] B\<close>
  by (simp add: Well_Type_unique)

lemma [simp]:
  \<open>N \<noteq> 0 \<Longrightarrow> \<a>\<r>\<r>\<a>\<y>[N] \<p>\<o>\<i>\<s>\<o>\<n> = \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  using semty_array_eq_poison
  by blast

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal T
\<Longrightarrow> Is_Literal N
\<Longrightarrow> Is_Type_Literal (\<a>\<r>\<r>\<a>\<y>[N] T) \<close>
  unfolding Is_Type_Literal_def ..



section \<open>\<phi>Type\<close>


\<phi>type_def Array :: "nat \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a list) \<phi>"
                    ("\<bbbA>\<r>\<r>\<a>\<y>[_] _" [20, 910] 910)
  where \<open>l \<Ztypecolon> Array N T \<equiv> sem_mk_array vs \<Ztypecolon> Itself \<s>\<u>\<b>\<j> vs. length l = N \<and> list_all2 (\<lambda>v x. v \<Turnstile> (x \<Ztypecolon> T)) vs l\<close>
  deriving \<open>Abstract_Domain\<^sub>L T P
        \<Longrightarrow> Abstract_Domain\<^sub>L (Array N T) (\<lambda>x. length x = N \<and> list_all P x) \<close>
          (tactic: clarsimp ; subgoal' for x \<open>induct x arbitrary: N\<close>)
       and Abstract_Domain
       and \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (Array N T) (list_all2 eq)\<close>
       and Transformation_Functor
           (tactic: clarsimp ; subgoal' for g x xb \<open>induct x arbitrary: xb xa N Na; auto simp add: list_all2_Cons2\<close>)
       and Functional_Transformation_Functor
       and \<open>Is_Aggregate (Array N T)\<close>
    (* and \<open>Semantic_Type T TY \<Longrightarrow> Semantic_Type (Array N T) (\<a>\<r>\<r>\<a>\<y>[N] TY)\<close>
           notes list_all2_conv_all_nth[simp] list_all_length[simp]
       and \<open>Semantic_Zero_Val TY T zero \<Longrightarrow> Semantic_Zero_Val (\<a>\<r>\<r>\<a>\<y>[N] TY) (Array N T) (replicate N zero)\<close>
           notes list_all2_conv_all_nth[simp] list_all_length[simp] *)
       and Inhabited
       and \<open>Functionality T D \<Longrightarrow> Functionality (\<bbbA>\<r>\<r>\<a>\<y>[N] T) (list_all D)\<close>
           notes list_all2_conv_all_nth[simp] list_all_length[simp]


lemma semty_Array [simp, \<phi>type_property Array Semantic_Type]:
  \<open>\<t>\<y>\<p>\<e>\<o>\<f> (Array N T) = \<a>\<r>\<r>\<a>\<y>[N] (\<t>\<y>\<p>\<e>\<o>\<f> T)\<close>
  unfolding SType_Of_def Inhabited_def Satisfiable_def Semantic_Type_def
  apply (cases N)
  apply auto
  apply (smt (verit, best) WT_arr Well_Type_unique exE_some less_nat_zero_code list.pred_inject(1) list.size(3) list_all2_conv_all_nth mem_Collect_eq)
  using WT_arr list.pred_inject(1) apply blast
  apply (smt (verit, del_insts) \<a>\<r>\<r>\<a>\<y>_0_eq_any length_0_conv list.ctr_transfer(1) semty_arr_uniq someI)
  using WT_arr list.pred_inject(1) apply blast
  apply (smt (verit) \<a>\<r>\<r>\<a>\<y>_0_eq_any exE_some list.size(3) list_all2_Nil2 semty_arr_uniq)
  using WT_arr list.pred_inject(1) apply blast

  subgoal for nat x TY p xa TYa xb
  apply (cases xa; cases xb; auto)
   subgoal premises prems for xx list u lista proof -
      let ?aa = \<open>\<lambda>x v. (\<exists>xa. v = sem_mk_array xa \<and> length x = Suc nat \<and> list_all2 (\<lambda>v x. v \<Turnstile> (x \<Ztypecolon> T)) xa x) \<close>
      let ?xx = \<open>\<lambda>x v TY. ?aa x v \<longrightarrow> v \<in> Well_Type TY\<close>
      have t1: \<open>\<exists>TY. \<forall>x v. ?xx x v TY\<close>
        using prems(4) prems(7) by blast
      have t2: \<open>?aa (replicate N xx) (sem_mk_array (replicate N u))\<close>
        using list_all2_conv_all_nth prems(1) prems(7) prems(8) by fastforce
      note t3 = someI_ex[OF t1, THEN spec[where x=\<open>replicate N xx\<close>], THEN spec[where x=\<open>sem_mk_array (replicate N u)\<close>],
                         THEN mp, OF t2]
      from semty_arr_uniq[OF t3]
        obtain TT where t4: \<open>(SOME TY. \<forall>x v. ?xx x v TY) = \<a>\<r>\<r>\<a>\<y>[length (replicate N u)] TT\<close>
          by blast
      have t5: \<open>sem_mk_array (replicate N u) \<in> Well_Type (\<a>\<r>\<r>\<a>\<y>[length (replicate N u)] TT)\<close>
        using t3 t4 by force
      have t6: \<open>u \<in> Well_Type TT\<close>
        using prems(1) t5 by auto
      
      have t7: \<open>\<exists>TY.  \<forall>x v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> v \<in> Well_Type TY\<close>
        using prems(2) by blast
      from someI_ex[OF t7, THEN spec, THEN spec, THEN mp, OF \<open>u \<Turnstile> (xx \<Ztypecolon> T)\<close>]
        have t8: \<open>u \<in> Well_Type (SOME x. \<forall>xa v. v \<Turnstile> (xa \<Ztypecolon> T) \<longrightarrow> v \<in> Well_Type x)\<close> .
      show ?thesis
        by (smt (verit, del_insts) Eps_cong Well_Type_unique length_replicate prems(1) t2 t4 t6 t8)
      qed .
    
  subgoal premises prems for nat x TY p
    by (insert prems(1-3) prems(4)[THEN spec[where x=\<open>replicate N x\<close>]],
        metis (no_types, lifting) length_replicate list_all2_conv_all_nth nth_replicate)
  
  subgoal premises prems for nat x TY p
    by (insert prems(1-3) prems(4)[THEN spec[where x=\<open>\<a>\<r>\<r>\<a>\<y>[N] TY\<close>]],
        auto simp: list_all2_conv_all_nth,
        metis (mono_tags, lifting) list_all_length)
  
    apply (metis (no_types, lifting) length_0_conv list.rel_cases old.nat.distinct(1))
  
  subgoal for nat x TY xa
    apply (cases x; cases xa; auto)
    subgoal premises prems for xx list vv lista
    apply (insert prems(3)[THEN spec[where x=\<open>replicate N xx\<close>], THEN spec[where x=\<open>sem_mk_array (replicate N vv)\<close>]], auto)
      using prems(1) apply blast
      apply (simp add: list_all2_conv_all_nth prems(7))
    subgoal premises premx
      apply (insert semty_arr_uniq[OF premx], clarsimp)
    subgoal for TY'
      apply (insert prems(2)[THEN spec[where x=TY']], clarsimp)
    subgoal for x' v'
      apply (insert prems(3)[THEN spec[where x=\<open>replicate N x'\<close>], THEN spec[where x=\<open>sem_mk_array (replicate N v')\<close>]],
          auto)
      using prems(1) apply blast
      by (simp add: list_all2_conv_all_nth) . . . .
  .


let_\<phi>type Array
  deriving \<open>Semantic_Zero_Val TY T zero \<Longrightarrow> Semantic_Zero_Val (\<a>\<r>\<r>\<a>\<y>[N] TY) (Array N T) (replicate N zero)\<close>
           notes list_all2_conv_all_nth[simp] list_all_length[simp]

(*
lemma Separation_Homo\<^sub>I_Array[\<phi>reason add]:
  \<open>Separation_Homo\<^sub>I (Array n) (Array n) (Array n) T U {(x,y). length x = length y} (\<lambda>(x,y). zip x y)\<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def
  by (auto simp: list_all2_conv_all_nth; blast)

lemma Separation_Homo\<^sub>E_Array[\<phi>reason add]:
  \<open>Separation_Homo\<^sub>E (Array n) (Array n) (Array n) T U list.unzip \<close>
  unfolding Separation_Homo\<^sub>E_def Transformation_def
  apply (auto simp: list_all2_conv_all_nth choice_iff
                    ex_simps(6)[where P=\<open>i < j\<close> for i j, symmetric]
              simp del: ex_simps)
  subgoal for z vs f1 f2
    by (rule exI[where x=\<open>sem_mk_array (map f1 [0..<length z])\<close>],
        rule exI[where x=\<open>sem_mk_array (map f2 [0..<length z])\<close>],
        auto simp add: nth_equalityI list_all2_conv_all_nth) .
*)


section \<open>Reasoning\<close>

text \<open>All the reasoning rules below are for semantic properties.
      All reasoning rules for transformations and SL are derived automatically by the above \<open>\<phi>type_def\<close> command\<close>

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N \<and> TY \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N i) (\<a>\<r>\<r>\<a>\<y>[N] TY) TY \<close>
  unfolding is_valid_step_idx_of_def Premise_def
  by (simp add: valid_idx_step_arr idx_step_type_arr)

subsection \<open>Index to Fields of Structures\<close>

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter idx X Y f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i # idx) (Array N X) Y (\<lambda>l. f (l!i))\<close>
  unfolding \<phi>Aggregate_Getter_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp simp add: idx_step_value_arr list_all2_conv_all_nth)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper idx X X Y Y' f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i # idx) (Array N X) (Array N X) Y Y' (\<lambda>g l. l[i := f g (l!i)])\<close>
  unfolding \<phi>Aggregate_Mapper_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp simp add: idx_step_mod_value_arr list_all2_conv_all_nth nth_list_update)





term list_all2

lemma
  \<open> Equiv_Class T r
\<Longrightarrow> Equiv_Class (Array N T) (list_all2 r) \<close>
  unfolding Equiv_Class_alt_def
  by (auto, metis list_all2_conv_all_nth)








end