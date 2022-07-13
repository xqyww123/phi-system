theory NuInstructions
  imports NuPrime NuLLReps
begin

section \<open>A Set of Predefined Minimal Instructions\<close>

context std_sem begin

subsection \<open>Manipulation of the Op-Stack\<close>

definition op_drop :: "('VAL,'RES_N,'RES) proc" where
  "op_drop = \<phi>M_get_Val (\<lambda>_. Success)"


subsection \<open>Arithmetic Operations\<close>

subsubsection \<open>Integer arithmetic\<close>

definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_int bits const = \<phi>M_put_Val (V_int.mk (bits,const))"

definition op_const_size_t :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_size_t c = \<phi>M_assume (c < 2 ^ addrspace_bits)
                          \<ggreater> \<phi>M_put_Val (V_int.mk (addrspace_bits,c))"
  \<comment> \<open> `op_const_size_t` checks the overflow during the compilation towards certain decided platform.  \<close>

definition op_add :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_add bits =
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_b.
      \<phi>M_put_Val (V_int.mk (bits, ((val_a + val_b) mod 2^bits)))
  ))"

(* lemma (in std)
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c left  \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c right \<lbrace> R2 \<longmapsto> R3\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (left \<ggreater> right \<ggreater> op_add b) \<lbrace> R1 \<longmapsto> R3\<heavy_comma> SYNTHESIS x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  apply (\<phi>reason, assumption) *)

definition op_sub :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_sub bits =
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_b.
      \<phi>M_put_Val (V_int.mk (bits, ((2^bits + val_b - val_a) mod 2^bits)))
  ))"

definition op_udiv :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_udiv bits =
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_b.
      \<phi>M_put_Val (V_int.mk (bits, (val_b div val_a)))
  ))"

definition op_lt :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_lt bits =
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_b.
      \<phi>M_put_Val (V_int.mk (1, (if val_b < val_a then 1 else 0)))
  ))"


definition op_le :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_le bits =
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_b.
      \<phi>M_put_Val (V_int.mk (1, (if val_b \<le> val_a then 1 else 0)))
  ))"


definition op_not :: "('VAL,'RES_N,'RES) proc"
  where "op_not =
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) (\<lambda>v.
    \<phi>M_put_Val (V_int.mk (1, 1 - v))
  )"

definition op_and :: "('VAL,'RES_N,'RES) proc"
  where "op_and =
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) (\<lambda>v.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) (\<lambda>u.
    \<phi>M_put_Val (V_int.mk (1, v+u-1))
  ))"

definition op_or :: "('VAL,'RES_N,'RES) proc"
  where "op_or =
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) (\<lambda>v.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) (\<lambda>u.
    \<phi>M_put_Val (V_int.mk (1, min 1 (v+u)))
  ))"

definition op_equal :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_equal TY =
    \<phi>M_get_Val (\<lambda>u.
    \<phi>M_get_Val (\<lambda>v. 
    \<phi>M_assert (u \<in> Well_Type TY) \<ggreater>
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater>
    (\<lambda>(vs,res). \<phi>M_assert (Can_EqCompare res v u) (vs,res)) \<ggreater>
    \<phi>M_put_Val (V_int.mk (1, (if EqCompare v u then 1 else 0)))
))"


subsubsection \<open>Address / Pointer\<close>

definition \<phi>M_get_logptr :: \<open>'TY \<Rightarrow> ('TY logaddr \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_logptr TY F = \<phi>M_getV \<tau>Pointer V_pointer.dest (\<lambda>p. F (rawaddr_to_log TY p))\<close>

lemma (in std) \<phi>M_get_logptr:
  \<open>(valid_logaddr addr \<Longrightarrow>
    addr \<noteq> 0 \<Longrightarrow>
    logaddr_type addr = TY \<Longrightarrow>
    0 < MemObj_Size TY \<Longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c F addr \<lbrace> X \<longmapsto> Y \<rbrace>) \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_logptr TY F \<lbrace> X\<heavy_comma> addr \<Ztypecolon> Pointer TY \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>M_get_logptr_def
  by (rule \<phi>M_getV, simp add: \<phi>expns valid_logaddr_def,
        auto simp add: \<phi>expns)


subsection \<open>Access the Resource\<close>

definition \<phi>M_get_res :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'a ?) \<Rightarrow> ('a \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res R F = (\<lambda>(vs,res). F (the_fine (R res)) (vs,res))\<close>

definition \<phi>M_get_res_entry :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('k \<rightharpoonup> 'a) ?) \<Rightarrow> 'k \<Rightarrow> ('a \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res_entry R k F = \<phi>M_get_res R (\<lambda>res.
    case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. Fail))\<close>

definition \<phi>M_set_res_entry :: \<open>
    ((('k \<rightharpoonup> 'v) ? \<Rightarrow> ('k \<rightharpoonup> 'v) ?) \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'RES_N \<Rightarrow> 'RES)
      \<Rightarrow> (('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v)) \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_set_res_entry Updt F = (\<lambda>(vs,res).
    Success (vs, Updt (map_fine F) res))\<close>


subsubsection \<open>Memory Operations\<close>

definition \<phi>M_get_mem
    :: "'TY segidx \<Rightarrow> nat list \<Rightarrow> ('VAL \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "\<phi>M_get_mem seg idx F =
            \<phi>M_get_res_entry R_mem.get seg (\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type (segidx.layout seg)) \<ggreater> F (index_value idx val))"

definition op_load_mem :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_load_mem TY =
    \<phi>M_get_logptr TY (\<lambda>ptr.
    \<phi>M_get_mem (memaddr.segment ptr) (memaddr.index ptr) \<phi>M_put_Val)"

definition op_store_mem :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_store_mem TY =
    \<phi>M_get_logptr TY (\<lambda>ptr. case ptr of (seg |: idx) \<Rightarrow>
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater>
    \<phi>M_get_mem seg idx (\<lambda>_.
    \<phi>M_set_res_entry R_mem.updt (\<lambda>f. f(seg := map_option (index_mod_value idx (\<lambda>_. v)) (f seg))))))"

definition op_free_mem :: "('VAL,'RES_N,'RES) proc"
  where "op_free_mem =
    \<phi>M_getV \<tau>Pointer V_pointer.dest (\<lambda>ptr. case ptr of (seg |: ofst) \<Rightarrow>
    \<phi>M_assert (ofst = 0) \<ggreater>
    \<phi>M_set_res_entry R_mem.updt (\<lambda>f. f(seg := None)))"

definition op_alloc_mem :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_alloc_mem TY' =
    \<phi>M_getV (\<tau>Int addrspace_bits) V_int.dest (\<lambda>(_, n).
    \<phi>M_set_res_entry R_mem.updt (\<lambda>f.
    let TY = \<tau>Array n TY'
      ; addr = (@addr. f addr = None \<and> segidx.layout addr = TY)
     in f(addr := Some (Zero TY))))"

declare (in std) fiction_mem_\<I>[simp]

lemma (in std) \<phi>M_get_mem:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> (seg |: idx) \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity \<longmapsto> Y \<rbrace>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_mem seg idx F \<lbrace> (seg |: idx) \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def
  apply clarify
  apply (subgoal_tac \<open>\<phi>M_get_mem seg idx F (a, b) = F v (a, b)\<close>)
  apply simp
  unfolding \<phi>M_get_mem_def \<phi>M_get_res_entry_def \<phi>M_get_res_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                R_mem.mult_in_dom Valid_Mem_def times_fun
                mult_strip_fine_011 times_list_def)
  subgoal premises prems for vals R fic res mem mem'
  proof -
    note [simp] = mult_strip_fine_011
    from \<open>mem' ## mem\<close> have t1: \<open>mem' seg ## mem seg\<close> by (simp add: sep_disj_fun) 
    show ?thesis
      using \<open>\<forall>_. \<exists>_. _ = Fine _ \<and> _ \<in> _\<close>[THEN spec[where x=seg]] t1 \<open>valid_index (segidx.layout seg) idx\<close>
        apply (auto simp add: \<open>0 < n\<close>)
      apply (rule \<phi>M_assert')
      using \<open>\<forall>_ \<in> dom _. _\<close>[unfolded Ball_def, THEN spec[where x=seg]]
       apply (auto simp add: times_fun)[1]

      subgoal premises prems2 for sh' v' proof -
        have [simp]: \<open>valid_index (segidx.layout seg) idx\<close>
          by (simp add: \<open>valid_index (segidx.layout seg) idx\<close> \<open>v' \<in> Well_Type (segidx.layout seg)\<close>)
        note t2[simp] = this[THEN Mapof_Val_pull]

        have t3[simp]: \<open>pull_map idx sh' ## share n (to_share \<circ> Mapof_Val v)\<close>
          using \<open>sh' ## push_map idx _\<close> by (metis pull_map_sep_disj pull_push_map)
        have t5: \<open>index_value idx v' \<in> Well_Type (index_type idx (segidx.layout seg))\<close>
          using index_value_welltyp \<open>valid_index (segidx.layout seg) idx\<close>
                  \<open>v' \<in> Well_Type (segidx.layout seg)\<close> by blast

        let \<open>?lhs = ?rhs\<close> = \<open>to_share \<circ> Mapof_Val v' = sh' * push_map idx (share n (to_share \<circ> Mapof_Val v))\<close>
        from \<open>?lhs = ?rhs\<close> have \<open>pull_map idx ?lhs = pull_map idx ?rhs\<close> by fastforce
        note this[simplified pull_map_to_share pull_map_homo_mult pull_push_map t2]
        then have \<open>Mapof_Val (index_value idx v') = (strip_share \<circ> pull_map idx sh') ++ (Mapof_Val v)\<close>
          by (metis prems(5) prems2(6) strip_share_fun_mult strip_share_fun_share strip_share_share_funcomp(2) t2 t3)
        then have txx: \<open>index_value idx v' = v\<close>
          using Valof_Map_append Valof_Map t5
          by (metis prems(7))
        
        show ?thesis by (subst txx) standard
      qed
      done
  qed
  done

lemma (in std) op_load_mem:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load_mem TY
          \<lbrace> ptr \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> ptr \<Ztypecolon> Pointer TY \<longmapsto> ptr \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> v \<Ztypecolon> Identity\<rbrace>\<close>
  unfolding Premise_def op_load_mem_def
  by (rule \<phi>M_get_logptr, cases ptr, simp, rule \<phi>M_get_mem, rule \<phi>M_put_Val, simp add: \<phi>expns)

lemma (in std) op_store_mem:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store_mem TY
          \<lbrace> ptr \<Zinj> 1 \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> u \<Ztypecolon> Identity\<heavy_comma> ptr \<Ztypecolon> Pointer TY
        \<longmapsto> ptr \<Zinj> 1 \<Znrres> u \<Ztypecolon> Ref Identity\<rbrace>\<close>
  unfolding Premise_def op_store_mem_def
  apply (rule \<phi>M_get_logptr, cases ptr, simp, rule \<phi>M_get_Val, simp add: \<phi>expns, rule \<phi>M_get_mem)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                        R_mem.mult_in_dom times_list_def)
  subgoal premises prems for seg idx vals R fic res mem mem_remain'
  proof -
    show ?thesis
      using \<open>\<forall>_. \<exists>_. _ \<and> mem _ \<in> _\<close>[THEN spec[where x=seg]] \<open>mem_remain' * Fine mem \<in> Valid_Mem\<close>
      apply (auto simp add: mult_strip_fine_011 prems Valid_Mem_def times_fun
                            sep_disj_partial_map_some_none times_fine times_list_def)
      subgoal premises prems2 for fic_mR mem_R val
      proof -
        have [simp]: \<open>seg \<in> dom mem\<close> using \<open>mem seg = Some val\<close> by blast
        have [simp]: \<open>\<And>any. mem_R ## mem(seg := any)\<close> using \<open>mem_R ## _\<close> \<open>mem seg = Some val\<close>
          by (smt (verit, best) fun_upd_apply sep_disj_commuteI sep_disj_fun_def sep_disj_option(3) sep_disj_partial_map_some_none)
      have t1: \<open>dom (push_map idx (to_share \<circ> Mapof_Val u)) = dom (push_map idx (to_share \<circ> Mapof_Val v))\<close>
        by simp (meson Mapof_Val_same_dom \<open>u \<in> Well_Type _\<close> \<open>v \<in> Well_Type _\<close>)
      have t2: \<open>fic_mR ## push_map idx (to_share \<circ> Mapof_Val u)\<close>
        using total_Mapof_disjoint dom1_disjoint_sep_disj dom1_dom t1
        by (metis \<open>fic_mR ## _\<close> \<open>to_share \<circ> Mapof_Val val = _\<close>)
        
        show ?thesis
          apply (rule exI[where x=\<open>fic * FIC_mem.mk (1(seg := Fine (push_map idx (to_share \<circ> Mapof_Val u))))\<close>])
          apply (auto simp add: prems prems2 inj_image_mem_iff index_mod_value_welltyp
                                FIC_mem.interp_split' R_mem.times_fun_upd sep_disj_partial_map_upd
                                times_set_def times_fine'[symmetric] R_mem.mk_homo_mult)
          apply (fold \<open>mem_remain' = Fine mem_R\<close>,
                 fold \<open>res R_mem.name = R_mem.inject mem_remain'\<close>,
                 fold mult.assoc,
                 fold R_mem.split)
          apply (rule exI[where x=\<open>res\<close>])
          apply (rule exI[where x=\<open>R_mem.mk (Fine (mem(seg \<mapsto> index_mod_value idx (\<lambda>_. u) val)))\<close>])
          apply (simp add: prems share_mem_def )
          apply (auto simp add: mult_strip_fine_011 times_fun inj_image_mem_iff prems2 times_fine t2)
          apply (rule exI[where x =\<open>fic_mR * push_map idx (to_share \<circ> Mapof_Val u)\<close>],
              simp add: Mapof_Val_modify_fiction[of \<open>segidx.layout seg\<close> idx val v u fic_mR]
                        prems2 prems index_mod_value_welltyp)
          subgoal for x
            using \<open>\<forall>_. \<exists>y. _\<close>[THEN spec[where x=x]] apply clarsimp apply (case_tac \<open>y=1\<close>; simp)
          subgoal for y by (rule exI[where x=y], simp)
          done
        done
    qed
    done
  qed
  done

declare (in std) fiction_mem_\<I>[simp del]


lemma (in std) fiction_mem_\<I>':
  \<open> Rmem \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> (\<exists>mem. Rmem = R_mem.mk (Fine mem) \<and> mem \<in> \<I> I fic)\<close>
  unfolding fiction_mem_\<I> by clarsimp blast

lemma (in std) fiction_mem_\<I>'':
  \<open> Rmem R_mem.name = R_mem.inject (Fine mem)
\<Longrightarrow> Rmem \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> Rmem = R_mem.mk (Fine mem) \<and> mem \<in> \<I> I fic\<close>
  unfolding fiction_mem_\<I>' by auto

lemma (in std) fiction_mem_\<I>_simp:
  \<open> R_mem.mk (Fine mem) \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> mem \<in> \<I> I fic\<close>
  unfolding fiction_mem_\<I>' by simp



lemma (in std) share_mem_in_dom:
  \<open> mem \<in> \<I> share_mem' fic
\<Longrightarrow> seg \<in> dom1 fic
\<Longrightarrow> seg \<in> dom mem\<close>
  unfolding share_mem'_def
  by (simp add: domIff dom1_def one_fine_def)
     (smt (verit, ccfv_SIG) mem_Collect_eq option.distinct(1))


lemma (in std) share_mem'_mono:
  \<open> x \<in> \<I> share_mem' fx
\<Longrightarrow> y \<in> \<I> share_mem' fy
\<Longrightarrow> dom1 fx \<inter> dom1 fy = {}
\<Longrightarrow> x * y \<in> \<I> share_mem' (fx * fy)\<close>
  unfolding share_mem'_def set_eq_iff
  apply clarsimp
  subgoal premises prems for k
    using prems[THEN spec[where x=k]]
  apply (clarsimp simp add: times_fun dom1_def one_fine_def)
    subgoal for fx' fy'
      apply (cases \<open>fx' = 1\<close>; cases \<open>fy' = 1\<close>; clarsimp simp add: times_fine)
      using Mapof_not_1 to_share_funcomp_eq_1_iff by blast+
    done
  done



lemma (in std) share_mem'_drop_seg:
  \<open> v \<in> Well_Type (segidx.layout seg)
\<Longrightarrow> mem \<in> \<I> share_mem' (fic * 1(seg := Fine (to_share \<circ> Mapof_Val v)))
\<Longrightarrow> seg \<in> dom mem \<and> mem(seg := None) \<in> \<I> share_mem' fic\<close>
  unfolding share_mem'_def
  apply (auto simp add: times_fun)
  subgoal premises prems proof -
    show ?thesis
      using prems(2)[THEN spec[where x=seg]]
      by (clarsimp simp add: mult_strip_fine_011)
  qed
  subgoal premises prems proof -
    show ?thesis
      using prems(2)[THEN spec[where x=seg]]
      apply (clarsimp simp add: mult_strip_fine_011)  
      subgoal premises prems2 for r u proof -
        have \<open>dom r \<inter> dom (to_share o Mapof_Val v) = {}\<close>
          using total_Mapof_disjoint[where idx=\<open>[]\<close>, simplified]
                \<open>r ## (to_share \<circ> Mapof_Val v)\<close> \<open>to_share \<circ> Mapof_Val u = r * (to_share \<circ> Mapof_Val v)\<close>
          by fastforce
        moreover have \<open>dom (to_share \<circ> Mapof_Val u) = dom (to_share \<circ> Mapof_Val v)\<close>
          using Mapof_Val_same_dom
          by (metis \<open>u \<in> Well_Type (segidx.layout seg)\<close> dom_map_option_comp prems(1)) 
        moreover have \<open>dom (to_share \<circ> Mapof_Val u) = dom r \<union> dom (to_share \<circ> Mapof_Val v)\<close>
          using dom_mult by (metis prems2) 
        ultimately have \<open>dom r = {}\<close> by (metis inf_sup_absorb)
        then show ?thesis unfolding one_partial_map by blast
      qed
      done
  qed
  subgoal premises prems for x proof -
    thm prems
    show ?thesis using \<open>\<forall>_. _\<close>[THEN spec[where x=x]] \<open>x\<noteq>seg\<close> apply clarsimp
      subgoal for m by (rule exI[where x=m], simp, cases \<open>m = 1\<close>; simp)
      done
  qed
  done


lemma (in std) op_alloc_mem:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc_mem TY \<lbrace> n \<Ztypecolon> Size \<longmapsto> (seg |: []) \<Zinj> 1 \<Znrres> (Zero (\<tau>Array n TY)) \<Ztypecolon> Ref Identity \<^bold>s\<^bold>u\<^bold>b\<^bold>j seg. True\<rbrace>\<close>
  unfolding op_alloc_mem_def
  apply (rule \<phi>M_tail_left, rule \<phi>M_getV; simp add: \<phi>expns)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' times_fun dom_mult
                        R_mem.mult_in_dom Valid_Mem_def mult_strip_fine_011 mult_strip_fine_001
                        fiction_mem_\<I>'' share_mem_def' times_list_def)
  subgoal premises prems for vals R fic res mem' mem
  proof -
    note [simp] = times_fun dom_mult
    have t0: \<open>finite (dom (mem' * mem))\<close> using prems by simp
    note t1 = Mem_freshness[OF t0, of \<open>\<tau>Array n TY\<close>, THEN someI_ex, simplified]
    let ?seg = \<open>(SOME x. mem' x = None \<and> mem x = None \<and> segidx.layout x = \<tau>Array n TY)\<close>
    have t2'[simp]: \<open>mem' ?seg = None \<and> mem ?seg = None\<close> using t1 by blast
    have t2'': \<open>?seg \<notin> dom mem\<close> by force
    have t6: \<open>\<And>any. R_mem.clean res * R_mem.mk (Fine ((mem' * mem)(?seg := any)))
                  = res * (R_mem.mk (Fine (mem * 1(?seg := any))))\<close>
      unfolding fun_upd_def fun_eq_iff
      apply (simp add: prems R_mem.inj_homo_mult[symmetric] times_fine fun_eq_iff sep_disj_fun_def)
      by (simp add: \<open>mem' ## mem\<close> sep_disj_fun)

    show ?thesis
      apply (rule exI[where x = \<open>fic * FIC_mem.mk
                  (1(?seg := Fine (to_share \<circ> Mapof_Val (V_array.mk (TY, replicate n (Zero TY))))))\<close>])
      apply (auto simp add: prems inj_image_mem_iff t1 list_all_length zero_well_typ
                            FIC_mem.interp_split' R_mem.times_fun_upd sep_disj_partial_map_upd
                            times_set_def times_fine'[symmetric] R_mem.mk_homo_mult)
       apply (rule exI[where x=\<open>?seg\<close>], rule exI[where x=fic], simp add: prems t1 list_all_length zero_well_typ)
      apply (unfold t6)
      apply (rule exI[where x=\<open>res\<close>])
      apply (rule exI[where x=\<open>R_mem.mk (Fine (mem * 1(?seg \<mapsto> V_array.mk (TY, replicate n (Zero TY)))))\<close>])
      using \<open>res \<in> \<I> INTERP (FIC_mem.clean fic)\<close>
      apply (clarsimp simp add: prems share_mem_def' fiction_mem_\<I>_simp)
      apply (rule share_mem'_mono, simp add: prems)
      apply (clarsimp simp add: share_mem'_def t1 list_all_length zero_well_typ one_fine_def)
      apply (simp add: set_eq_iff)
      using share_mem_in_dom[OF \<open>mem \<in> \<I> share_mem' (FIC_mem.get fic)\<close>]  t2'' by blast
  qed
  done


lemma (in std) op_free_mem:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_mem \<lbrace> (seg |: []) \<Zinj> 1 \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> (seg |: 0) \<Ztypecolon> RawPointer \<longmapsto> 1\<rbrace>\<close>
  unfolding op_free_mem_def
  apply (rule \<phi>M_getV; simp add: \<phi>expns)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' times_fun dom_mult
                        R_mem.mult_in_dom Valid_Mem_def mult_strip_fine_011 mult_strip_fine_001
                        fiction_mem_\<I>'' share_mem_def' times_list_def)
  subgoal premises prems for vals R fic res memR mem
  proof -
    have t2: \<open>seg \<in> dom mem\<close>
      using share_mem'_drop_seg prems by blast 
    have t3: \<open>seg \<notin> dom memR\<close>
      by (meson domD domIff prems sep_disj_partial_map_some_none t2)
    have t1: \<open>(res * R_mem.mk (Fine mem))(R_mem.name := R_mem.inject (Fine ((memR * mem)(seg := None))))
            = res * R_mem.mk (Fine (mem(seg := None)))\<close>
      unfolding fun_eq_iff times_fun
      apply (simp add: prems R_mem.inj_homo_mult[symmetric] times_fine sep_disj_partial_map_del)
      apply (simp add: fun_upd_def fun_eq_iff times_fun)
      using domIff t3 by fastforce
    show ?thesis
      apply (rule exI[where x=fic], simp add: prems FIC_mem.interp_split' sep_disj_partial_map_del t1)
      apply (rule times_set_I, simp add: prems)
      using share_mem'_drop_seg prems
      by (metis fiction_mem_\<I>' share_mem_def')
  qed
  done


subsubsection \<open>Variable Operations\<close>

definition \<phi>M_get_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "\<phi>M_get_var vname TY F = \<phi>M_get_res_entry (R_var.get) vname (\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type TY) \<ggreater> F val)"

definition op_get_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_var vname TY = \<phi>M_get_var vname TY \<phi>M_put_Val"

definition op_set_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_var vname TY = \<phi>M_get_Val (\<lambda>v. \<phi>M_get_var vname TY (\<lambda>_.
            \<phi>M_assert (v \<in> Well_Type TY) \<ggreater> \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname := Some v))))"

definition op_free_var :: "varname \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_free_var vname = \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname := None))"

definition op_var_scope' :: "'TY \<Rightarrow> (varname \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_var_scope' TY F =
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_get_res R_var.get (\<lambda>f.
    let vname = (@vname. f vname = None) in
    \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname := Some v)) \<ggreater>
    F vname))"

definition op_var_scope :: "'TY \<Rightarrow> (varname \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_var_scope TY F =
    op_var_scope' TY (\<lambda>vname. F vname \<ggreater> op_free_var vname)"

lemma (in std) \<phi>M_get_var:
  \<open>v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_var vname TY F \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_get_var_def \<phi>M_get_res_entry_def \<phi>M_get_res_def
  apply (simp add: \<phi>expns R_var.prj.homo_mult times_list_def)
  apply (subst R_var_valid_split)
  apply (auto simp add: \<phi>expns FIC_var_split times_set_def R_var.mult_in_dom mult_strip_fine_011 times_fine times_list_def)
  subgoal premises prems for vals R fic res vars
  proof -
    note [simp] = \<open>vars ## 1(vname \<mapsto> v)\<close> [THEN sep_disj_fun[where x=vname], simplified]
    note F = \<open>\<forall>_ _ _. _ \<longrightarrow> F v _ \<in> _\<close>[THEN spec[where x=vals],
                                       THEN spec[where x=\<open>res * R_var.mk (Fine (1(vname \<mapsto> v)))\<close>],
                                       THEN spec[where x=R], THEN mp]
    show ?thesis
      apply (simp add: times_fun)
      apply (rule \<phi>M_assert', rule \<open>v \<in> Well_Type TY\<close>, rule F,
             rule exI[where x=\<open>fic * FIC_var.mk (Fine (1(vname \<mapsto> v)))\<close>])
      using prems apply (auto simp add: FIC_var_split times_set_def)
      apply (subst R_var_valid_split)
      apply (auto simp add: R_var.inj_homo_mult[symmetric] times_fine)
      done
  qed
  done

lemma (in std) \<phi>M_set_var:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname \<mapsto> u)) \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011 times_list_def)
  subgoal premises prems for vals R fic res vars
  proof -
    note [simp] = \<open>vars ## 1(vname \<mapsto> v)\<close> [THEN sep_disj_fun[where x=vname], simplified]
    have [simp]: \<open>(vars * 1(vname \<mapsto> v))(vname \<mapsto> u) = vars * 1(vname \<mapsto> u)\<close>
      unfolding times_fun_def fun_eq_iff fun_upd_def by simp
    from \<open>vars ## 1(vname \<mapsto> v)\<close> have [simp]: \<open>vars ## 1(vname \<mapsto> u)\<close>
      unfolding sep_disj_fun_def by simp
    show ?thesis
      apply (rule exI[where x=\<open>fic * FIC_var.mk (Fine (1(vname \<mapsto> u))) \<close>])
      apply (auto simp add: R_var_valid_split' FIC_var_split times_set_def prems)
      apply (rule exI[where x = res])
      by (auto simp add: fun_eq_iff times_fun prems R_var.inj_homo_mult[symmetric] times_fine)
  qed
  done


lemma (in std) op_get_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var vname TY \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> v \<Ztypecolon> Var vname Identity \<heavy_comma> v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding op_get_var_def Premise_def
  by (rule \<phi>M_get_var, assumption, rule \<phi>M_put_Val, simp add: \<phi>expns)
end

lemma (in std) op_set_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_var vname TY \<lbrace> v \<Ztypecolon> Var vname Identity\<heavy_comma> u \<Ztypecolon> Identity \<longmapsto> u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding op_set_var_def Premise_def
  by (rule \<phi>M_get_Val, rule \<phi>M_get_var, assumption,
      rule \<phi>SEQ, rule \<phi>M_assert, simp_all add: \<phi>expns, rule \<phi>M_set_var)


lemma (in std) op_var_scope':
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> (\<And>vname. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F vname \<lbrace> X\<heavy_comma> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace> )
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope' TY F \<lbrace> X\<heavy_comma> v \<Ztypecolon> Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding op_var_scope'_def Premise_def
  apply (rule \<phi>M_get_Val)
  unfolding \<phi>Procedure_def
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def \<phi>M_get_res_def Let_def instr_comp_def bind_def
  apply (simp add: \<phi>expns)
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011 times_list_def)
  subgoal premises prems for res R valR ficR valX ficX vars
  proof -
    note t1 = finite_map_freshness[OF \<open>finite (dom vars)\<close>, OF infinite_varname]
    have t2[simp]: \<open>vars ## 1(SOME fic. vars fic = None \<mapsto> v)\<close>
      unfolding sep_disj_fun_def by simp (meson someI t1)
    have t3[simp]: \<open>vars (SOME vname. vars vname = None) = None\<close>
      by (meson someI t1)
    show ?thesis
      apply (rule \<open>\<forall>a. _\<close>[of \<open>(SOME vname. vars vname = None)\<close>,
        THEN spec,
        THEN spec,
        THEN spec,
        THEN mp])
      apply (rule exI[where x=\<open>ficR * ficX * FIC_var.mk (Fine (1((@x. vars x = None) \<mapsto> v))) \<close>])
      apply (auto simp add: \<phi>expns R_var_valid_split' FIC_var_split times_set_def prems)
      using \<open>(valR, ficR) \<in> R\<close> \<open>(valX, ficX) \<in> X\<close> apply (smt (verit) fun_mult_norm) 
      apply (rule exI[where x = res])
      by (simp add: fun_eq_iff times_fun prems R_var.inj_homo_mult[symmetric] times_fine)
  qed
  done

lemma (in std) op_free_var:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_var vname \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> 1 \<rbrace>\<close>
  unfolding op_free_var_def \<phi>Procedure_def \<phi>M_set_res_entry_def
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011 times_list_def)
  subgoal premises prems for vals R fic res vars
  proof -
    note [simp] = \<open>vars ## 1(vname \<mapsto> v)\<close> [THEN sep_disj_fun[where x=vname], simplified]
    have [simp]: \<open>(vars * 1(vname \<mapsto> v))(vname := None) = vars\<close>
      unfolding fun_upd_def fun_eq_iff times_fun by simp
    have [simp]: \<open>(res * R_var.mk (Fine (1(vname \<mapsto> v))))(R_var.name := R_var.inject (Fine vars)) = res\<close>
      by (simp add: times_fun_def fun_upd_def fun_eq_iff prems)
    show ?thesis
      apply (rule exI[where x=fic])
      by (auto simp add: prems)
  qed
  done

lemma (in std) op_var_scope''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> (\<And>vname. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F vname \<lbrace> X\<heavy_comma> v \<Ztypecolon> Var vname Identity \<longmapsto> Y\<heavy_comma> u \<Ztypecolon> Var vname Identity \<^bold>s\<^bold>u\<^bold>b\<^bold>j u. True \<rbrace> )
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TY F \<lbrace> X\<heavy_comma> v \<Ztypecolon> Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding Premise_def op_var_scope_def
  apply (rule op_var_scope', simp add: Premise_def,
      rule \<phi>SEQ, assumption)
  \<medium_left_bracket> ;; \<exists>u op_free_var \<medium_right_bracket> .. .





context std begin










subsection \<open>Branches & Loops\<close>

paragraph \<open>Non-Branching Selection\<close>

definition op_sel :: "('VAL,'RES_N,'RES) proc"
  where "op_sel =
    \<phi>M_getV (\<tau>Int 1) V_int.dest (\<lambda>c.
    \<phi>M_get_Val (\<lambda>b.
    \<phi>M_get_Val (\<lambda>a.
    \<phi>M_put_Val (if snd c = 1 then a else b))))"

paragraph \<open>Branch\<close>

definition op_if :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_if brT brF =
    \<phi>M_getV (\<tau>Int 1) V_int.dest (\<lambda>c.
    if snd c = 1 then brT else brF)"

paragraph \<open>While Loop\<close>

inductive SemDoWhile :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) comp \<Rightarrow> ('VAL,'RES_N,'RES) state \<Rightarrow> bool" where
  "f s = Success (V_int.mk (1,0) # vs, res) \<Longrightarrow> SemDoWhile f s (Success (vs,res))"
| "f s = PartialCorrect \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "f s = Fail \<Longrightarrow> SemDoWhile f s Fail"
| "f s = Success (V_int.mk (1,1) # vs, res) \<Longrightarrow> SemDoWhile f (vs,res) s'' \<Longrightarrow> SemDoWhile f s s''"

lemma "\<nexists> y. SemDoWhile (\<lambda>(vs,res). Success (V_int.mk (1,1) # vs, res)) (vs,res) y"
  apply rule apply (elim exE) subgoal for y 
    thm SemDoWhile.induct
    apply (induct "(\<lambda>(vs,res). Success (V_int.mk (1,1) # vs, (res::'RES_N \<Rightarrow> 'RES)))" "(vs, res)" y
           rule: SemDoWhile.induct)
       apply simp_all
    done done

definition op_do_while :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc" where
  "op_do_while f s = (if (\<exists>y. SemDoWhile f s y) then The (SemDoWhile f s) else PartialCorrect)"

lemma SemDoWhile_deterministic:
  assumes "SemDoWhile c s s1"
      and "SemDoWhile c s s2"
    shows "s1 = s2"
proof -
  have "SemDoWhile c s s1 \<Longrightarrow> (\<forall>s2. SemDoWhile c s s2 \<longrightarrow> s1 = s2)"
    by (induct rule: SemDoWhile.induct) (subst SemDoWhile.simps, simp)+
  thus ?thesis
    using assms by simp
qed

lemma SemDoWhile_deterministic2: " SemDoWhile body s x \<Longrightarrow> The ( SemDoWhile body s) = x"
  using SemDoWhile_deterministic by blast


paragraph \<open>Recursion\<close>

inductive SemRec :: "(('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) comp \<Rightarrow> ('VAL,'RES_N,'RES) state \<Rightarrow> bool" where
  SemRec_I0: "(\<And>g. F g x = y) \<Longrightarrow> SemRec F x y"
| SemRec_IS: "SemRec (F o F) x y \<Longrightarrow> SemRec F x y"

definition op_recursion :: "'TY list \<Rightarrow> 'TY list \<Rightarrow> (('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_recursion _ _ F s = (if (\<exists>t. SemRec F s t) then The (SemRec F s) else PartialCorrect)"

ML \<open>Syntax.parse_term \<^context> "_"\<close>

subsection \<open>Tuple Operations\<close>



subsubsection \<open>Construct Tuple\<close>

definition cons_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "cons_tup tys = (\<lambda>(vs,res).
    let N = length tys in
    if N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (rev (take N vs)) tys
    then Success (V_tup.mk (rev (take N vs)) # drop N vs, res)
    else Fail)"

lemma cons_tup_nil:
  \<open>cons_tup [] = \<phi>M_put_Val (V_tup.mk [])\<close>
  unfolding cons_tup_def \<phi>M_put_Val_def
  by simp

lemma cons_tup_cons:
  \<open>cons_tup (TY#TYs) =
    cons_tup TYs \<ggreater>
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (V_tup.mk [v] * tup)
    ))\<close>
  apply (auto split: list.split
    simp add: cons_tup_def fun_eq_iff pair_forall instr_comp_def bind_def
    \<phi>M_get_Val_def \<phi>M_assert_def \<phi>M_put_Val_def Let_def V_tup_mult)
  apply (metis Suc_le_eq list.sel(1) take_hd_drop)
  apply (metis Cons_nth_drop_Suc Suc_le_eq list.sel(3))
  apply (metis Suc_le_eq drop_all leI list.simps(3))
  apply (metis (no_types, lifting) drop_all leI list.ctr_transfer(1) list.sel(1) list.simps(3) list_all2_Cons2 list_all2_appendI list_all2_rev1 rev.simps(2) take_hd_drop)
  apply (smt (verit, del_insts) Suc_le_eq append1_eq_conv list.sel(1) list_all2_Cons2 rev_eq_Cons_iff take_hd_drop)
  by (simp add: take_Suc_conv_app_nth)

lemma (in std) op_cons_tup_nil:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup [] \<lbrace> Void \<longmapsto> () \<Ztypecolon> EmptyTuple \<rbrace>\<close>
  unfolding cons_tup_nil by \<phi>reason

lemma (in std) op_cons_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup TYs \<lbrace> X \<longmapsto> VAL y \<Ztypecolon> Y \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup (TY#TYs) \<lbrace> VAL a \<Ztypecolon> A\<heavy_comma> X \<longmapsto> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> Y) \<rbrace>\<close>
  unfolding cons_tup_cons
  apply \<phi>reason apply (rule \<phi>frame, assumption)
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  apply \<phi>reason apply (simp add: \<phi>expns) by blast


subsubsection \<open>Destruct Tuple\<close>


definition op_dest_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_dest_tup tys =
    \<phi>M_getV (\<tau>Tuple tys) V_tup.dest (\<lambda>tup.
    \<lambda>(vs, res). Success (rev tup@vs, res))"

lemma op_dest_tup_nil_expn:
  \<open>op_dest_tup [] = \<phi>M_getV (\<tau>Tuple []) V_tup.dest (\<lambda>_. SKIP)\<close>
  by (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)

lemma op_dest_tup_cons_expn:
  \<open>op_dest_tup (TY#TYs) =
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_assert (\<exists>h tup'. tup = V_tup.mk (h#tup') \<and> h \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (hd (V_tup.dest tup)) \<ggreater>
    \<phi>M_put_Val (V_tup.mk (tl (V_tup.dest tup))) \<ggreater>
    op_dest_tup TYs)\<close>
  apply (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)
  by (metis list.discI list.exhaust_sel list.rel_sel list.sel(1))

lemma (in std) op_dest_tup_nil:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup [] \<lbrace> () \<Ztypecolon> EmptyTuple \<longmapsto> Void \<rbrace> \<close>
  unfolding op_dest_tup_nil_expn by \<phi>reason

lemma (in std) op_dest_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup TYs \<lbrace> VAL y \<Ztypecolon> Y \<longmapsto> X \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup (TY#TYs) \<lbrace> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> \<phi>Is_Tuple Y) \<longmapsto> VAL a \<Ztypecolon> A\<heavy_comma> X \<rbrace>\<close>
  unfolding op_dest_tup_cons_expn
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  by (rule \<phi>frame, assumption)



subsubsection \<open>Accessing Elements\<close>


definition op_get_element :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_element idx TY =
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx) \<ggreater>
    \<phi>M_put_Val (index_value idx v))"

definition op_set_element :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_element idx TY =
    \<phi>M_get_Val (\<lambda>u.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx \<and> u \<in> Well_Type (index_type idx TY)) \<ggreater>
    \<phi>M_put_Val (index_mod_value idx (\<lambda>_. u) v)
  ))"

lemma (in std) op_get_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_element idx TY \<lbrace> VAL x \<Ztypecolon> X \<longmapsto> VAL f x \<Ztypecolon> Y \<rbrace> \<close>
  unfolding op_get_element_def \<phi>Index_getter_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason

lemma (in std) op_set_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> Y) (index_type idx TY)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_element idx TY \<lbrace> VAL x \<Ztypecolon> X\<heavy_comma> VAL y \<Ztypecolon> Y \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> X \<rbrace>\<close>
  unfolding op_set_element_def \<phi>Index_mapper_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
   apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason






end

end
