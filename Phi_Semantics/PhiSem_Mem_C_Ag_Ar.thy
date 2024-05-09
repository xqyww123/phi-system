theory PhiSem_Mem_C_Ag_Ar
  imports PhiSem_Mem_C PhiSem_Aggregate_Array
  abbrevs "<SPtr>" = "\<bbbS>\<p>\<t>\<r>"
begin

section \<open>Semantics\<close>

debt_axiomatization
      Map_of_Val_arr: \<open>Map_of_Val (V_array.mk vs) =
        (\<lambda>path. case path of AgIdx_N i # path' \<Rightarrow>
                                  if i < length vs then Map_of_Val (vs ! i) path' else 1
                           | _ \<Rightarrow> 1)\<close>
  and idx_step_offset_arr: \<open> idx_step_offset (\<a>\<r>\<r>\<a>\<y>[N] ty) (AgIdx_N j) = j * MemObj_Size ty\<close>
  and MemObj_Size_arr: \<open>MemObj_Size (\<a>\<r>\<r>\<a>\<y>[N] ty) = N * MemObj_Size ty\<close>

  and array_TY_neq_void: \<open>void \<noteq> \<a>\<r>\<r>\<a>\<y>[N] TY\<close>

lemma address_to_raw_array_GEP:
  \<open> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY
\<Longrightarrow> address_to_raw (addr \<tribullet> (i)\<^sup>\<t>\<^sup>\<h>) = address_to_raw addr ||+ of_nat (i * MemObj_Size TY) \<close>
  unfolding address_to_raw_def addr_gep_def
  by (cases addr; clarsimp simp: idx_step_offset_arr)

lemma address_to_raw_inj_array:
  \<open> valid_address addr
\<Longrightarrow> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY
\<Longrightarrow> i \<le> N \<and> j \<le> N
\<Longrightarrow> \<not> phantom_mem_semantic_type TY
\<Longrightarrow> address_to_raw (addr \<tribullet> (i)\<^sup>\<t>\<^sup>\<h>) = address_to_raw (addr \<tribullet> (j)\<^sup>\<t>\<^sup>\<h>) \<longleftrightarrow> i = j \<close>
  unfolding address_to_raw_array_GEP valid_address_def Valid_MemBlk_def
  apply (clarsimp; cases addr; clarsimp)
  subgoal for blk idx
    apply (cases \<open>blk\<close>; clarsimp simp: array_TY_neq_void)
    subgoal premises prems for _ BTY proof -
      have \<open>type_storable_in_mem (\<a>\<r>\<r>\<a>\<y>[N] TY)\<close>
        using index_type_type_storable_in_mem prems(1) prems(3) prems(6) by fastforce
      then have t1: \<open>N * MemObj_Size TY < 2^addrspace_bits\<close>
        using MemObj_Size_arr by force
      show ?thesis
        by (metis Abs_fnat_hom_mult dual_order.strict_trans2 mult_cancel2 mult_le_cancel2 phantom_mem_semantic_type_def prems(2) prems(4) prems(5) t1 unat_to_size_t)
    qed . .


lemma address_to_raw_array_0th:
  \<open> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY
\<Longrightarrow> address_to_raw (addr \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>) = address_to_raw addr \<close>
  unfolding address_to_raw_def addr_gep_def
  by (auto simp: idx_step_offset_arr split: memaddr.split)

lemma address_to_raw_array_ith:
  \<open> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY
\<Longrightarrow> phantom_mem_semantic_type TY
\<Longrightarrow> address_to_raw (addr \<tribullet> (i)\<^sup>\<t>\<^sup>\<h>) = address_to_raw addr \<close>
  unfolding address_to_raw_def addr_gep_def
  by (auto simp: idx_step_offset_arr phantom_mem_semantic_type_def split: memaddr.split)


lemma address_to_raw_inj_arr:
    \<open>valid_address addr1 \<Longrightarrow>
     valid_address addr2 \<Longrightarrow>
     address_type addr1 = \<a>\<r>\<r>\<a>\<y>[N] TY \<Longrightarrow>
     address_type addr2 = \<a>\<r>\<r>\<a>\<y>[M] TY \<Longrightarrow>
     \<not> phantom_mem_semantic_type TY \<Longrightarrow>
     0 < N \<Longrightarrow> 0 < M \<Longrightarrow>
     address_to_raw addr1 = address_to_raw addr2 \<Longrightarrow>
     addr1 = addr2 \<close>
  subgoal premises prems proof -
    have t1: \<open>address_to_raw (addr1 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>) = address_to_raw (addr2 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>)\<close>
      by (simp add: address_to_raw_array_0th prems(3) prems(4) prems(8))
    have t2: \<open>valid_address (addr1 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>) \<close>
      using prems(1) prems(3) prems(6) valid_idx_step_arr by fastforce
    have t3: \<open>valid_address (addr2 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>) \<close>
      by (simp add: prems(2) prems(4) prems(7) valid_idx_step_arr)
    have t4: \<open>address_type (addr1 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>) = address_type (addr2 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>)\<close>
      by (simp add: idx_step_type_arr prems(3) prems(4) prems(6) prems(7))
    have t5: \<open>addr1 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h> = addr2 \<tribullet> (0)\<^sup>\<t>\<^sup>\<h>\<close>
      using idx_step_type_arr address_to_raw_inj address_type_gep prems(4) prems(5) prems(7) t1 t2 t3 t4 by presburger
    show ?thesis
      using t5 by blast
  qed .

definition \<open>rawaddr_to_log_arr T raddr = (@laddr. address_to_raw laddr = raddr \<and> (\<exists>N. 0 < N \<and> address_type laddr = \<a>\<r>\<r>\<a>\<y>[N] T) \<and> valid_address laddr)\<close>



lemma rawaddr_arr_to_log[simp]:
  \<open> valid_address addr
\<Longrightarrow> \<not> phantom_mem_semantic_type (address_type addr)
\<Longrightarrow> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY
\<Longrightarrow> rawaddr_to_log_arr TY (address_to_raw addr) = addr\<close>
  unfolding rawaddr_to_log_arr_def
  by (rule some_equality, auto simp: MemObj_Size_arr phantom_mem_semantic_type_def address_to_raw_inj_arr)


lemma address_to_raw_arr[iff]:
  \<open> (\<exists>laddr. address_to_raw laddr = addr \<and> (\<exists>N. 0 < N \<and> address_type laddr = \<a>\<r>\<r>\<a>\<y>[N] TY) \<and> valid_address laddr)
\<Longrightarrow> address_to_raw (rawaddr_to_log_arr TY addr) = addr \<and>
    (\<exists>N. 0 < N \<and> address_type (rawaddr_to_log_arr TY addr) = \<a>\<r>\<r>\<a>\<y>[N] TY) \<and>
    valid_address (rawaddr_to_log_arr TY addr)\<close>
  unfolding rawaddr_to_log_arr_def
  by (elim exE; rule someI; blast)


lemma address_to_raw_phantom_mem_type_gep_N__arr:
  \<open> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY
\<Longrightarrow> phantom_mem_semantic_type TY
\<Longrightarrow> valid_index TY path
\<Longrightarrow> address_to_raw (addr_geps addr (AgIdx_N i # path)) = address_to_raw addr\<close>
  by (auto simp: address_to_raw_array_ith idx_step_type_arr address_to_raw_phantom_mem_type_gep_N)



proc op_get_element_pointer_arr[\<phi>overload \<tribullet> 100]:
  requires \<open>parse_eleidx_input (\<a>\<r>\<r>\<a>\<y>[any] TY) input_index sem_idx (AgIdx_N si # spec_idx) reject\<close>
       and [unfolded is_valid_index_of_def, useful]: \<open>is_valid_index_of spec_idx TY TY'\<close>
       and \<open>report_unprocessed_element_index reject\<close>
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr (\<a>\<r>\<r>\<a>\<y>[any] TY)\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>addr_geps addr (AgIdx_N si # spec_idx) \<Ztypecolon> \<v>\<a>\<l> Ptr TY'\<close>
\<medium_left_bracket>
  $addr semantic_local_value pointer ;;
  have t1: \<open>0 < any\<close>
    by (insert \<open>address_type addr = \<a>\<r>\<r>\<a>\<y>[any] TY\<close>
               \<open>valid_address addr\<close> parse_eleidx_input_def that(1) valid_idx_step_arr,
        cases addr, auto) ;;
  holds_fact t2: \<open>0 < N \<Longrightarrow> phantom_mem_semantic_type (\<a>\<r>\<r>\<a>\<y>[N] TY) \<longleftrightarrow> phantom_mem_semantic_type TY\<close> for N ;;
  semantic_return \<open>
    V_pointer.mk (address_to_raw (addr_geps (rawaddr_to_log_arr TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1))) sem_idx))
      \<Turnstile> (addr_geps addr (AgIdx_N si # spec_idx) \<Ztypecolon> Ptr TY')\<close>
\<medium_right_bracket> .


thm "\<tribullet>_\<phi>app"




section \<open>Slice Pointers\<close>

subsection \<open>Slice Pointer\<close>
  \<comment> \<open>points to the beginning address of a component or the end of an allocation block.
      has GEP and shift arithmetic.
      only points to elements in an array.\<close>

(*
definition \<open>valid_address_range TY addr N \<longleftrightarrow>
    valid_address addr \<and> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY\<close>

lemma valid_address_range_sub:
  \<open> base \<le> base' \<and> base'+len' \<le> base+len
\<Longrightarrow> valid_address_range TY addr base  len
\<Longrightarrow> valid_address_range TY addr base' len'\<close>
  unfolding valid_address_range_def
  by (clarsimp, smt (verit, ccfv_threshold) add.assoc add_lessD1 le_eq_less_or_eq le_iff_add nat_add_left_cancel_less)
*)

\<phi>type_def SlicePtr :: \<open>address \<Rightarrow> nat \<Rightarrow> TY \<Rightarrow> (VAL, nat) \<phi>\<close>
  where \<open>i \<Ztypecolon> SlicePtr addr N TY \<equiv> address_to_raw (addr \<tribullet> i\<^sup>\<t>\<^sup>\<h>) \<Ztypecolon> RawPointer
                \<s>\<u>\<b>\<j> i \<le> N \<and> valid_address addr \<and> address_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY\<close>
  deriving Basic
       and \<open>Object_Equiv (SlicePtr addr N TY) (=)\<close>
       and Functionality
       and \<open>\<phi>SemType (x \<Ztypecolon> SlicePtr addr N TY) pointer\<close>



notation SlicePtr ("\<bbbS>\<p>\<t>\<r>[_:_] _" [20,20,900] 899)


lemma Ptr_eqcmp[\<phi>reason 1000]:
  \<open>\<phi>Equal (\<bbbS>\<p>\<t>\<r>[addr:N] TY) (\<lambda>_ _. \<not> phantom_mem_semantic_type TY) (=)\<close>
  unfolding \<phi>Equal_def
  by (clarsimp simp: address_to_raw_inj_array)

\<phi>reasoner_group slice_ptr_ToA = (%ToA_cut, [%ToA_cut, %ToA_cut+30]) in ToA_cut \<open>\<close>

lemma [\<phi>reason %slice_ptr_ToA]: \<comment> \<open>TODO: automatically generate this rule!\<close>
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> addr' = addr \<and> len' = len \<and> TY' = TY
\<Longrightarrow> x \<Ztypecolon> \<bbbS>\<p>\<t>\<r>[addr:len] TY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<bbbS>\<p>\<t>\<r>[addr':len'] TY' \<close>
  unfolding Premise_def
  by simp

lemma [\<phi>reason %slice_ptr_ToA]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < len
\<Longrightarrow> i \<Ztypecolon> \<bbbS>\<p>\<t>\<r>[addr:len] TY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> addr \<tribullet> i\<^sup>\<t>\<^sup>\<h> \<Ztypecolon> \<bbbP>\<t>\<r> TY' \<close>
  \<medium_left_bracket>
    to \<open>OPEN _ _\<close>
    to \<open>\<bbbP>\<t>\<r> TY'\<close> certified by (insert \<phi>, auto simp add: valid_idx_step_arr, auto_sledgehammer)
  \<medium_right_bracket> .

lemma [\<phi>reason %slice_ptr_ToA+10 for \<open>_ \<tribullet> (_)\<^sup>\<t>\<^sup>\<h> \<Ztypecolon> \<bbbP>\<t>\<r> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<bbbS>\<p>\<t>\<r>[_:_] _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P> \<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> address_type addr = \<a>\<r>\<r>\<a>\<y>[len] TY
\<Longrightarrow> addr \<tribullet> i\<^sup>\<t>\<^sup>\<h> \<Ztypecolon> \<bbbP>\<t>\<r> TY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> i \<Ztypecolon> \<bbbS>\<p>\<t>\<r>[addr:len] TY' @tag \<T>\<P> \<close>
  \<medium_left_bracket>
    to RawPointer
    note idx_step_type_arr[simp] ;;
    \<open>i \<Ztypecolon> MAKE _ (\<bbbS>\<p>\<t>\<r>[addr:len] TY')\<close> certified by auto_sledgehammer
  \<medium_right_bracket> .

lemma [\<phi>reason %slice_ptr_ToA for \<open>_ \<Ztypecolon> \<bbbP>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<bbbS>\<p>\<t>\<r>[_:_] _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P> \<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> addr \<noteq> 0
\<Longrightarrow> addr \<Ztypecolon> \<bbbP>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[LEN] TY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 \<Ztypecolon> \<bbbS>\<p>\<t>\<r>[addr:LEN] TY @tag \<T>\<P> \<close>
  \<medium_left_bracket>
    to RawPointer ;;
    \<open>0 \<Ztypecolon> MAKE _ (\<bbbS>\<p>\<t>\<r>[addr:LEN] TY)\<close> certified by auto_sledgehammer
  \<medium_right_bracket> .



section \<open>Array in Memory\<close>

subsection \<open>Syntax\<close>

term \<open>\<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[n] T\<close>

setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 110 (
    fn ((ctxt,i), f, Const(\<^const_syntax>\<open>Array\<close>, _) $ n $ T) =>
        SOME (Const(\<^const_name>\<open>\<phi>Mul_Quant_Tree\<close>, dummyT)
                $ \<^Const>\<open>AgIdx_N \<^Type>\<open>VAL\<close>\<close>
                $ (\<^Const>\<open>Len_Intvl \<^Type>\<open>nat\<close>\<close> $ HOLogic.zero $ n)
                $ f (ctxt,0) T)
     | X => NONE)
)\<close>

term \<open>\<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[n] (T::(VAL,'x) \<phi>)\<close>

subsection \<open>Reasoning\<close>

subsubsection \<open>Mem Coerce\<close>

text \<open>The following lemma cannot be automated because it is tightly related to the semantics\<close>

lemma split_mem_coerce_array':
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> length l = Suc n
\<Longrightarrow> (l \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<bbbA>\<r>\<r>\<a>\<y>[Suc n] T) = (last l \<Ztypecolon> AG_IDX(n\<^sup>\<t>\<^sup>\<h>) \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) * (take n l \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<bbbA>\<r>\<r>\<a>\<y>[n] T)\<close>
  unfolding BI_eq_iff Premise_def
  apply (clarsimp; rule; clarsimp)

  subgoal for vs
    apply (rule exI[where x=\<open>[AG_IDX(n\<^sup>\<t>\<^sup>\<h>)] \<tribullet>\<^sub>m (to_share \<circ> map_option discrete \<circ> Map_of_Val (last vs))\<close>])
    apply (rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val (V_array.mk (take n vs))\<close>])
    
    apply (auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq sep_disj_fun_def
                      list_all2_lengthD
                split: list.split aggregate_index'.split)
    apply (metis (mono_tags, lifting) comp_apply diff_add_inverse last_conv_nth length_0_conv less_antisym list_all2_lengthD nat.simps(3) plus_1_eq_Suc push_map_cons push_map_mult_nil)

    apply (rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val (last vs)\<close>],
        auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq list_all2_lengthD
             split: list.split aggregate_index'.split,
        rule exI[where x=\<open>last vs\<close>],
        metis add_diff_cancel_left' last_conv_nth length_0_conv lessI list_all2_conv_all_nth nat.simps(3) plus_1_eq_Suc)
    apply (rule exI[where x=\<open>V_array.mk (take n vs)\<close>])
    by (auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq list_all2_lengthD
             split: list.split aggregate_index'.split)

  subgoal for v_t v_h
    apply (rule exI[where x=\<open>V_array.mk (v_h @ [v_t])\<close>])
    apply (auto simp: fun_eq_iff times_fun Map_of_Val_arr push_map_cons_neq sep_disj_fun_def
                      list_all2_lengthD nth_append
                split: list.split aggregate_index'.split)
    using less_antisym apply fastforce
    by (smt (verit, ccfv_SIG) append_eq_conv_conj length_Suc_conv_rev less_antisym list_all2_conv_all_nth nth_append nth_append_length snoc_eq_iff_butlast)
  .


lemma split_mem_coerce_array:
  \<open> (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<bbbA>\<r>\<r>\<a>\<y>[n] T) = \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) \<close>
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

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] U) \<^emph>[C\<^sub>R] R
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] U') \<^emph>[C\<^sub>R] R'
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
    \<o>\<v>\<e>\<r> f : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] T) \<^emph>[C\<^sub>W] W
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] T') \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .


subsubsection \<open>Transformation\<close>

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] T) \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] T) \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[0,n] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[sty] T) \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<a>\<r>\<r>\<a>\<y>[n] sty] (\<bbbA>\<r>\<r>\<a>\<y>[n] T) \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def split_mem_coerce_array .


hide_fact split_mem_coerce_array'


subsubsection \<open>Address Offset\<close>

term address_type

lemma [\<phi>reason add]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (\<a>\<r>\<r>\<a>\<y>[N] TY) : address_type addr
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] i+n < N
\<Longrightarrow> abstract_address_offset (addr \<tribullet> i\<^sup>\<t>\<^sup>\<h>) TY TY n (addr \<tribullet> (i+n)\<^sup>\<t>\<^sup>\<h>) \<close>
  unfolding abstract_address_offset_def Simplify_rev_def Premise_def
            address_to_raw_def addr_gep_def 
  by (cases addr; clarsimp, rule,
      simp add: valid_address_def valid_idx_step_arr,
      simp add: idx_step_offset_arr,
      metis add.commute distrib_right idx_step_type_arr mult.commute)

lemma [\<phi>reason add]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (\<a>\<r>\<r>\<a>\<y>[N] \<a>\<r>\<r>\<a>\<y>[M] TY) : address_type addr
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] i*M+j+n < M * N
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (i', j') : (i + (j + n) div M, (j + n) mod M)
\<Longrightarrow> abstract_address_offset (addr \<tribullet> i\<^sup>\<t>\<^sup>\<h> \<tribullet> j\<^sup>\<t>\<^sup>\<h>) TY TY n (addr \<tribullet> i'\<^sup>\<t>\<^sup>\<h> \<tribullet> j'\<^sup>\<t>\<^sup>\<h>) \<close>
  unfolding abstract_address_offset_def Simplify_rev_def Premise_def
            address_to_raw_def addr_gep_def 
  apply (cases addr; clarsimp, rule;
        clarsimp simp: valid_address_def valid_idx_step_arr idx_step_type_arr
                       valid_index_tail[where idx=\<open>idx@[j]\<close> for idx j, simplified]
                       idx_step_offset_arr index_offset_tail[where idx=\<open>idx@[j]\<close> for idx j, simplified])
  subgoal premises for blk idx proof -
    have [simp]: \<open>i + (j + n) div M < N\<close>
      by (metis \<open>i * M + j + n < M * N\<close> add.assoc add.commute add_lessD1 div_mult_self1 less_mult_imp_div_less mult.commute mult_0_right verit_comp_simplify1(1))
    show ?thesis
      using \<open>i + (j + n) div M < N\<close> by blast
  qed
  subgoal premises prems for blk idx proof -
    have [simp]: \<open>i + (j + n) div M < N\<close>
      by (metis \<open>i * M + j + n < M * N\<close> add.assoc add.commute add_lessD1 div_mult_self1 less_mult_imp_div_less mult.commute mult_0_right verit_comp_simplify1(1))
    have t1: \<open>(i + n div M) * M = i * M + (n div M * M)\<close>
      using add_mult_distrib by presburger

    show ?thesis
      by (simp add: idx_step_offset_arr idx_step_type_arr MemObj_Size_arr
                    Abs_fnat_homs
               del: of_nat_mult of_nat_add,
          smt (verit) add.commute left_add_mult_distrib mod_div_mult_eq mult.assoc mult.commute)

  qed .


end