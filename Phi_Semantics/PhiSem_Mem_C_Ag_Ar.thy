theory PhiSem_Mem_C_Ag_Ar
  imports PhiSem_Mem_C PhiSem_Aggregate_Array
begin

section \<open>Array in Memory\<close>

subsection \<open>Semantics\<close>

debt_axiomatization
      Map_of_Val_arr: \<open>Map_of_Val (V_array.mk vs) =
        (\<lambda>path. case path of AgIdx_N i # path' \<Rightarrow>
                                  if i < length vs then Map_of_Val (vs ! i) path' else 1
                           | _ \<Rightarrow> 1)\<close>
  and idx_step_offset_arr: \<open> idx_step_offset (\<a>\<r>\<r>\<a>\<y>[N] ty) (AgIdx_N j) = j * MemObj_Size ty\<close>
  and MemObj_Size_arr: \<open>MemObj_Size (\<a>\<r>\<r>\<a>\<y>[N] ty) = N * MemObj_Size ty\<close>



subsection \<open>Syntax\<close>

term \<open>\<m>\<e>\<m>[addr] \<Aa>\<r>\<r>\<a>\<y>[n] T\<close>

setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 110 (
    fn ((ctxt,i), f, Const(\<^const_syntax>\<open>Array\<close>, _) $ n $ T) =>
        SOME (Const(\<^const_name>\<open>\<phi>Mul_Quant_Tree\<close>, dummyT)
                $ \<^Const>\<open>AgIdx_N \<^Type>\<open>VAL\<close>\<close>
                $ (\<^Const>\<open>Len_Intvl \<^Type>\<open>nat\<close>\<close> $ HOLogic.zero $ n)
                $ f (ctxt,0) T)
     | X => NONE)
)\<close>

term \<open>\<m>\<e>\<m>[addr] \<Aa>\<r>\<r>\<a>\<y>[n] T\<close>

subsection \<open>Reasoning\<close>

subsubsection \<open>Mem Coerce\<close>

text \<open>The following lemma cannot be automated because it is tightly related to the semantics\<close>

lemma split_mem_coerce_array':
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> length l = Suc n
\<Longrightarrow> (l \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<Aa>\<r>\<r>\<a>\<y>[Suc n] T) = (take n l \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<Aa>\<r>\<r>\<a>\<y>[n] T) * (last l \<Ztypecolon> AG_IDX(n\<^sup>\<t>\<^sup>\<h>) \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)\<close>
  unfolding BI_eq_iff Premise_def
  apply (clarsimp; rule; clarsimp)

  subgoal for vs
    apply (rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val (V_array.mk (take n vs))\<close>])
    apply (rule exI[where x=\<open>[AG_IDX(n\<^sup>\<t>\<^sup>\<h>)] \<tribullet>\<^sub>m (to_share \<circ> map_option discrete \<circ> Map_of_Val (last vs))\<close>])
    apply (auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq sep_disj_fun_def
                      list_all2_lengthD
                split: list.split aggregate_index'.split)
    apply (metis (mono_tags, lifting) comp_apply diff_add_inverse last_conv_nth length_0_conv less_antisym list_all2_lengthD nat.simps(3) plus_1_eq_Suc push_map_cons push_map_mult_nil)

    apply (rule exI[where x=\<open>V_array.mk (take n vs)\<close>],
        auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq list_all2_lengthD
             split: list.split aggregate_index'.split)
    apply (rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val (last vs)\<close>],
        auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq list_all2_lengthD
             split: list.split aggregate_index'.split,
        rule exI[where x=\<open>last vs\<close>], clarsimp)
    by (metis diff_add_inverse last_conv_nth lessI list.size(3) list_all2_conv_all_nth nat.simps(3) plus_1_eq_Suc)

  subgoal for v_h v_t
    apply (rule exI[where x=\<open>V_array.mk (v_h @ [v_t])\<close>])
    apply (auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq sep_disj_fun_def
                      list_all2_lengthD nth_append
                split: list.split aggregate_index'.split)
    using less_antisym apply fastforce
    by (smt (verit, ccfv_SIG) append_eq_conv_conj length_Suc_conv_rev less_antisym list_all2_conv_all_nth nth_append nth_append_length snoc_eq_iff_butlast)
  .


lemma split_mem_coerce_array:
  \<open> (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<Aa>\<r>\<r>\<a>\<y>[n] T) = \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) \<close>
  apply (induct n,
      (rule \<phi>Type_eqI_BI; unfold BI_eq_iff; clarsimp; rule;
       clarsimp simp: Map_of_Val_arr fun_eq_iff atLeast0_lessThan_Suc list_all2_Cons2
                split: list.split aggregate_index'.split),
       rule \<phi>Type_eqI_Tr)

  \<medium_left_bracket> for n, l premises Tr
    split_mem_coerce_array'
    unfold Tr  
  \<medium_right_bracket> certified by auto_sledgehammer 
  \<medium_left_bracket> premises Tr 
    apply_rule split_mem_coerce_array'[symmetric, where n=n and l=x and T=T, unfolded Tr]
    certified by auto_sledgehammer
  \<medium_right_bracket>.

subsubsection \<open>ToA Mapper\<close>

lemma [\<phi>reason %mapToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %mapToA_mem_coerce]:
  \<open> \<m>\<a>\<p> g : \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] U)  \<^emph>[C\<^sub>R] R
          \<mapsto> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] U') \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] U) \<^emph>[C\<^sub>R] R
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] U') \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .

lemma [\<phi>reason %mapToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %mapToA_mem_coerce]:
  \<open> \<m>\<a>\<p> g : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<^emph>[C\<^sub>W] W
          \<mapsto> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T') \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] T) \<^emph>[C\<^sub>W] W
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] T') \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .


subsubsection \<open>Transformation\<close>

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] T) \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] T) \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<Aa>\<r>\<r>\<a>\<y>[n] T) \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .


hide_fact split_mem_coerce_array'


subsubsection \<open>Address Offset\<close>

term logaddr_type

lemma [\<phi>reason add]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (\<a>\<r>\<r>\<a>\<y>[N] TY) : logaddr_type addr
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] i+n < N
\<Longrightarrow> abstract_address_offset (addr \<tribullet>\<^sub>a i\<^sup>\<t>\<^sup>\<h>) TY TY n (addr \<tribullet>\<^sub>a (i+n)\<^sup>\<t>\<^sup>\<h>) \<close>
  unfolding abstract_address_offset_def Simplify_rev_def Premise_def
            logaddr_to_raw_def addr_gep_def 
  by (cases addr; clarsimp, rule,
      simp add: valid_logaddr_def valid_idx_step_arr,
      simp add: idx_step_offset_arr,
      metis add.commute distrib_right idx_step_type_arr mult.commute)

lemma [\<phi>reason add]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (\<a>\<r>\<r>\<a>\<y>[N] \<a>\<r>\<r>\<a>\<y>[M] TY) : logaddr_type addr
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] i*M+j+n < M * N
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (i', j') : (i + (j + n) div M, (j + n) mod M)
\<Longrightarrow> abstract_address_offset (addr \<tribullet>\<^sub>a i\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>) TY TY n (addr \<tribullet>\<^sub>a i'\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a j'\<^sup>\<t>\<^sup>\<h>) \<close>
  unfolding abstract_address_offset_def Simplify_rev_def Premise_def
            logaddr_to_raw_def addr_gep_def 
  apply (cases addr; clarsimp, rule;
        clarsimp simp: valid_logaddr_def valid_idx_step_arr idx_step_type_arr
                       valid_index_tail[where idx=\<open>idx@[j]\<close> for idx j, simplified]
                       idx_step_offset_arr index_offset_tail[where idx=\<open>idx@[j]\<close> for idx j, simplified])
  subgoal premises for blk idx proof -
    have [simp]: \<open>i + (j + n) div M < N\<close>
      by (metis \<open>i * M + j + n < M * N\<close> add.assoc add.commute add_lessD1 div_mult_self1 less_mult_imp_div_less mult.commute mult_0_right verit_comp_simplify1(1))
    show ?thesis
      by (simp add: idx_step_type_arr valid_idx_step_arr, insert \<open>j < M\<close>, fastforce)
  qed
  subgoal premises prems for blk idx proof -
    have [simp]: \<open>i + (j + n) div M < N\<close>
      by (metis \<open>i * M + j + n < M * N\<close> add.assoc add.commute add_lessD1 div_mult_self1 less_mult_imp_div_less mult.commute mult_0_right verit_comp_simplify1(1))
    have t1: \<open>(i + n div M) * M = i * M + (n div M * M)\<close>
      using add_mult_distrib by presburger

    show ?thesis
    proof (simp add: idx_step_offset_arr idx_step_type_arr MemObj_Size_arr
                     Abs_fnat_homs
                del: of_nat_mult of_nat_add)
      have "\<forall>n na nb. (na::nat) + (n + nb) = n + (nb + na)"
        by force
      then show \<open>to_size_t (MemObj_Size TY * n + (i * (M * MemObj_Size TY) + j * MemObj_Size TY)) =
                to_size_t ((i + (j + n) div M) * (M * MemObj_Size TY) + (j + n) mod M * MemObj_Size TY) \<and>
                idx_step_type AG_IDX(((j + n) mod M)\<^sup>\<t>\<^sup>\<h>) (\<a>\<r>\<r>\<a>\<y>[M] TY) = TY\<close>
        by (smt (verit, ccfv_threshold) Euclidean_Rings.div_eq_0_iff add.commute add_mult_distrib idx_step_type_arr less_nat_zero_code mod_div_mult_eq mod_div_trivial mult.assoc mult.commute prems(10))
    qed
  qed .


end