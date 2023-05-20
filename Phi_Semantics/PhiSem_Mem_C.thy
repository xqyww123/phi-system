theory PhiSem_Mem_C
  imports PhiSem_Mem_Pointer
  abbrevs "<mem>" = "\<m>\<e>\<m>"
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

(* For technical reasons, the memory resource is installed in \<^file>\<open>PhiSem_Mem_Pointer.thy\<close> *)

(*
definition Valid_Mem :: "('TY,'VAL) R_mem set"
  where "Valid_Mem = { Fine h |h. finite (dom h)
                                \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` Well_Type (segidx.layout seg))}"

lemma Valid_Mem_1[simp]: \<open>1 \<in> Valid_Mem\<close>
  unfolding Valid_Mem_def one_fun_def one_fine_def by simp
*)


subsection \<open>Fiction\<close>

fiction_space aggregate_mem =
  aggregate_mem :: \<open>RES.aggregate_mem.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>blk. \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (memblk.layout blk)))\<close>
     (perm_aggregate_mem_fiction RES.aggregate_mem memblk.layout)
  by (standard, of_tac \<open>\<lambda>_. UNIV\<close>; simp add: pointwise_set_UNIV)

(*

fiction_space (in agmem_sem) agmem_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> = \<phi>min_fic +
  FIC_mem :: share_mem


locale agmem = agmem_fic
  where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                    \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                    \<times> ('RES_N \<Rightarrow> 'RES::{comm_monoid_mult,no_inverse}))\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::{no_inverse,comm_monoid_mult})\<close> 
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>
begin

lemma R_mem_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    R_mem.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_mem.name = R_mem.inject m \<and> m \<in> Valid_Mem)\<close>
  by (subst R_mem.split, simp add: Valid_Resource_def times_fun_def res_valid_mem image_iff, blast)
     

lemma R_mem_valid_split': \<open>NO_MATCH (R_mem.clean res') res \<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow>
    R_mem.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_mem.name = R_mem.inject m \<and> m \<in> Valid_Mem)\<close>
  using R_mem_valid_split .

end
*)

section \<open>\<phi>Type for Semantic Models\<close>

subsection \<open>Pointers\<close>




(* subsubsection \<open>Slice Pointer\<close>

text \<open>A limitation of TypPtr is that it cannot point to the end of an array,
  because there is no object exists at the end. To address this, we provide slice pointer which
  can range over a piece of the array including the end.\<close>

definition SlicePtr :: "TY \<Rightarrow> (VAL, logaddr \<times> nat \<times> nat) \<phi>"
  where "SlicePtr TY = (\<lambda>(base,i,len).
    if valid_logaddr base \<and> base \<noteq> 0 \<and> (\<exists>N. logaddr_type base = array N TY \<and> len \<le> N)
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

lemma SlicePtr_inhabited[\<phi>reason_elim!,elim!]:
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

*)

subsection \<open>Memory Object\<close>

abbreviation Mem :: \<open>logaddr \<Rightarrow> (aggregate_path \<Rightarrow> VAL nosep share option,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<m>\<e>\<m>[_]")
  where \<open>Mem addr T \<equiv> FIC.aggregate_mem.\<phi> (memaddr.blk addr \<^bold>\<rightarrow> memaddr.index addr \<^bold>\<rightarrow>\<^sub>@ T)\<close>

(*
definition Ref :: \<open>('VAL,'a) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'TY logaddr \<Zinj> 'a share) \<phi>\<close>
  where \<open>Ref T x' = (case x' of (seg |: idx) \<Zinj> (n \<Znrres> x) \<Rightarrow>
    if 0 < n \<and> valid_index (segidx.layout seg) idx then
    { FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Map_of_Val v)))))
          |v. v \<in> Well_Type (logaddr_type (seg |: idx)) \<and> v \<in> (x \<Ztypecolon> T) }
    else {})\<close>

lemma (in agmem) Ref_expn[\<phi>expns]:
  \<open>fic \<in> ((seg |: idx) \<Zinj> (n \<Znrres> v) \<Ztypecolon> Ref Identity)
    \<longleftrightarrow> 0 < n \<and> valid_index (segidx.layout seg) idx
        \<and> v \<in> Well_Type (logaddr_type (seg |: idx))
        \<and> fic = FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Map_of_Val v)))))\<close>
  unfolding Ref_def \<phi>Type_def by (simp add: Identity_def) blast

definition Slice :: \<open>('VAL,'a) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'TY logaddr \<Zinj> 'a share option list) \<phi>\<close>
  where \<open>Slice T x' = (case x' of (seg |: i#idx) \<Zinj> l \<Rightarrow>
    if valid_index (segidx.layout seg) idx
     \<and> (\<exists>N TY. index_type idx (segidx.layout seg) = \<tau>Array N TY \<and> i + length l \<le> N)
    then let 
    { FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Map_of_Val v)))))
          |v. v \<in> Well_Type (logaddr_type (seg |: idx)) \<and> v \<in> (x \<Ztypecolon> T) }
    else {} | _ \<Rightarrow> {})\<close> *)

section \<open>Instructions & Their Specifications\<close>

lemma
  \<open>(1(memaddr.blk addr := to_share \<circ> memaddr.index addr \<tribullet>\<^sub>m (map_option nosep \<circ> Map_of_Val v)) \<Ztypecolon> FIC.aggregate_mem.\<phi> Identity)
    = (v \<Ztypecolon> \<m>\<e>\<m>[addr] ([] \<^bold>\<rightarrow> to_share.\<phi> (\<black_circle> Nosep Identity)))\<close>
  unfolding set_eq_iff
  apply (clarsimp simp add: \<phi>expns to_share.perm_ins_homo_axioms)

thm to_share.perm_ins_homo_axioms
















term Map_of_Val_ins.\<phi>
thm Map_of_Val_ins.\<phi>insertion

proc op_load_mem:
  input  \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<coercion> T)\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<close>
  output \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<coercion> T)\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  to Identity \<exists>v
thm \<phi>
  thm FIC.aggregate_mem.getter_rule











subsubsection \<open>Address / Pointer\<close>

(*
definition \<phi>M_get_logptr :: \<open>'TY \<Rightarrow> 'VAL sem_value \<Rightarrow> ('TY logaddr \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_logptr TY v F = \<phi>M_getV \<tau>Pointer V_pointer.dest v (\<lambda>p. F (rawaddr_to_log TY p))\<close>

lemma (in agmem) \<phi>M_get_logptr[\<phi>reason!]:
  \<open>(valid_logaddr addr \<Longrightarrow>
    addr \<noteq> 0 \<Longrightarrow>
    logaddr_type addr = TY \<Longrightarrow>
    0 < MemObj_Size TY \<Longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c F addr \<lbrace> X \<longmapsto> Y \<rbrace>) \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_logptr TY v F \<lbrace> X\<heavy_comma> addr \<Ztypecolon> Val v (Pointer TY) \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>M_get_logptr_def
  by (cases v, simp, rule \<phi>M_getV, simp add: \<phi>expns valid_logaddr_def, auto simp add: \<phi>expns)
*)

subsection \<open>Access the Resource\<close>

subsubsection \<open>Memory Operations\<close>

definition \<phi>M_get_mem
    :: "'TY segidx \<Rightarrow> nat list \<Rightarrow> ('VAL \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc"
  where "\<phi>M_get_mem seg idx F =
            \<phi>M_get_res_entry R_mem.get seg (\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type (segidx.layout seg)) \<ggreater> F (index_value idx val))"

definition op_load_mem :: "'TY \<Rightarrow> ('VAL, 'VAL,'RES_N,'RES) proc'"
  where "op_load_mem TY v =
    \<phi>M_get_logptr TY v (\<lambda>ptr.
    \<phi>M_get_mem (memaddr.segment ptr) (memaddr.index ptr) (\<lambda>x. Return (sem_value x)))"

definition op_store_mem :: "'TY \<Rightarrow> ('VAL \<times> 'VAL, unit,'RES_N,'RES) proc'"
  where "op_store_mem TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_get_logptr TY va (\<lambda>ptr. case ptr of (seg |: idx) \<Rightarrow>
    \<phi>M_getV TY id vb (\<lambda>v.
    \<phi>M_get_mem seg idx (\<lambda>_.
    \<phi>M_set_res R_mem.updt (\<lambda>f. f(seg := map_option (index_mod_value idx (\<lambda>_. v)) (f seg)))))))"

definition op_free_mem :: "('VAL, unit,'RES_N,'RES) proc'"
  where "op_free_mem v =
    \<phi>M_getV \<tau>Pointer V_pointer.dest v (\<lambda>ptr. case ptr of (seg |: ofst) \<Rightarrow>
    \<phi>M_assert (ofst = 0) \<ggreater>
    \<phi>M_set_res R_mem.updt (\<lambda>f. f(seg := None)))"

definition op_alloc_mem :: "'TY \<Rightarrow> ('VAL, unit,'RES_N,'RES) proc'"
  where "op_alloc_mem TY' v =
    \<phi>M_getV (\<tau>Int addrspace_bits) V_int.dest v (\<lambda>(_, n).
    \<phi>M_set_res R_mem.updt (\<lambda>f.
    let TY = \<tau>Array n TY'
      ; addr = (@addr. f addr = None \<and> segidx.layout addr = TY)
     in f(addr := Some (Zero TY))))"

declare (in agmem) fiction_mem_\<I>[simp]

lemma (in agmem) \<phi>M_get_mem[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> (seg |: idx) \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity \<longmapsto> Y \<rbrace>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_mem seg idx F \<lbrace> (seg |: idx) \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def
  apply clarify
  apply (subgoal_tac \<open>\<phi>M_get_mem seg idx F comp = F v comp\<close>)
  apply simp
  unfolding \<phi>M_get_mem_def \<phi>M_get_res_entry_def \<phi>M_get_res_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                R_mem.mult_in_dom Valid_Mem_def times_fun
                mult_strip_fine_011 times_list_def del: subsetI)
  subgoal premises prems for R fic res mem mem'
  proof -
    note [simp] = mult_strip_fine_011
    from \<open>mem' ## mem\<close> have t1: \<open>mem' seg ## mem seg\<close> by (simp add: sep_disj_fun) 
    show ?thesis
      using \<open>\<forall>_. \<exists>_. _ = Fine _ \<and> _ \<in> _\<close>[THEN spec[where x=seg]] t1 \<open>valid_index (segidx.layout seg) idx\<close>
        apply (auto simp add: \<open>0 < n\<close>)
      using \<open>\<forall>_ \<in> dom _. _\<close>[unfolded Ball_def, THEN spec[where x=seg]]
       apply (auto simp add: times_fun)[1]

      subgoal premises prems2 for sh' v' proof -
        have [simp]: \<open>valid_index (segidx.layout seg) idx\<close>
          by (simp add: \<open>valid_index (segidx.layout seg) idx\<close> \<open>v' \<in> Well_Type (segidx.layout seg)\<close>)
        note t2[simp] = this[THEN Map_of_Val_pull]

        have t3[simp]: \<open>pull_map idx sh' ## share n (to_share \<circ> Map_of_Val v)\<close>
          using \<open>sh' ## push_map idx _\<close> by (metis pull_map_sep_disj pull_push_map)
        have t5: \<open>index_value idx v' \<in> Well_Type (index_type idx (segidx.layout seg))\<close>
          using index_value_welltyp \<open>valid_index (segidx.layout seg) idx\<close>
                  \<open>v' \<in> Well_Type (segidx.layout seg)\<close> by blast

        let \<open>?lhs = ?rhs\<close> = \<open>to_share \<circ> Map_of_Val v' = sh' * push_map idx (share n (to_share \<circ> Map_of_Val v))\<close>
        from \<open>?lhs = ?rhs\<close> have \<open>pull_map idx ?lhs = pull_map idx ?rhs\<close> by fastforce
        note this[simplified pull_map_to_share pull_map_homo_mult pull_push_map t2]
        then have \<open>Map_of_Val (index_value idx v') = (strip_share \<circ> pull_map idx sh') ++ (Map_of_Val v)\<close>
          by (metis prems(5) prems2(6) strip_share_fun_mult strip_share_fun_share strip_share_share_funcomp(2) t2 t3)
        then have txx: \<open>index_value idx v' = v\<close>
          using Val_of_Map_append Val_of_Map t5
          by (metis prems(7))
        
        show ?thesis by (subst txx) standard
      qed
      done
  qed
  done

lemma (in agmem) op_load_mem:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load_mem TY raw
          \<lbrace> ptr \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> ptr \<Ztypecolon> Val raw (Pointer TY) \<longmapsto> ptr \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding Premise_def op_load_mem_def
  apply (cases ptr; simp)
  apply \<phi>reason
  apply simp
  by \<phi>reason

lemma (in agmem) op_store_mem:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store_mem TY (\<phi>V_pair raw_ptr raw_u)
          \<lbrace> ptr \<Zinj> 1 \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> u \<Ztypecolon> Val raw_u Identity\<heavy_comma> ptr \<Ztypecolon> Val raw_ptr (Pointer TY)
        \<longmapsto> ptr \<Zinj> 1 \<Znrres> u \<Ztypecolon> Ref Identity\<rbrace>\<close>
  unfolding Premise_def op_store_mem_def
  apply (rule \<phi>M_caseV, rule \<phi>M_get_logptr)
  apply (cases ptr; cases raw_u; simp, \<phi>reason)
  unfolding \<phi>M_set_res_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                        R_mem.mult_in_dom times_list_def)
  subgoal premises prems for seg idx R fic res mem mem_remain'
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
      have t1: \<open>dom (push_map idx (to_share \<circ> Map_of_Val u)) = dom (push_map idx (to_share \<circ> Map_of_Val v))\<close>
        by simp (meson Map_of_Val_same_dom \<open>u \<in> Well_Type _\<close> \<open>v \<in> Well_Type _\<close>)
      have t2: \<open>fic_mR ## push_map idx (to_share \<circ> Map_of_Val u)\<close>
        using total_Mapof_disjoint dom1_disjoint_sep_disj dom1_dom t1
        by (metis \<open>fic_mR ## _\<close> \<open>to_share \<circ> Map_of_Val val = _\<close>)
        
        show ?thesis
          apply (rule exI[where x=\<open>fic * FIC_mem.mk (1(seg := Fine (push_map idx (to_share \<circ> Map_of_Val u))))\<close>])
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
          apply (rule exI[where x =\<open>fic_mR * push_map idx (to_share \<circ> Map_of_Val u)\<close>],
              simp add: Map_of_Val_modify_fiction[of \<open>segidx.layout seg\<close> idx val v u fic_mR]
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


declare (in agmem) fiction_mem_\<I>[simp del]


lemma (in agmem) fiction_mem_\<I>':
  \<open> Rmem \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> (\<exists>mem. Rmem = R_mem.mk (Fine mem) \<and> mem \<in> \<I> I fic)\<close>
  unfolding fiction_mem_\<I> by clarsimp blast

lemma (in agmem) fiction_mem_\<I>'':
  \<open> Rmem R_mem.name = R_mem.inject (Fine mem)
\<Longrightarrow> Rmem \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> Rmem = R_mem.mk (Fine mem) \<and> mem \<in> \<I> I fic\<close>
  unfolding fiction_mem_\<I>' by auto

lemma (in agmem) fiction_mem_\<I>_simp:
  \<open> R_mem.mk (Fine mem) \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> mem \<in> \<I> I fic\<close>
  unfolding fiction_mem_\<I>' by simp



lemma (in agmem) share_mem_in_dom:
  \<open> mem \<in> \<I> share_mem' fic
\<Longrightarrow> seg \<in> dom1 fic
\<Longrightarrow> seg \<in> dom mem\<close>
  unfolding share_mem'_def
  by (simp add: domIff dom1_def one_fine_def)
     (smt (verit, ccfv_SIG) mem_Collect_eq option.distinct(1))


lemma (in agmem) share_mem'_mono:
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



lemma (in agmem) share_mem'_drop_seg:
  \<open> v \<in> Well_Type (segidx.layout seg)
\<Longrightarrow> mem \<in> \<I> share_mem' (fic * 1(seg := Fine (to_share \<circ> Map_of_Val v)))
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
        have \<open>dom r \<inter> dom (to_share o Map_of_Val v) = {}\<close>
          using total_Mapof_disjoint[where idx=\<open>[]\<close>, simplified]
                \<open>r ## (to_share \<circ> Map_of_Val v)\<close> \<open>to_share \<circ> Map_of_Val u = r * (to_share \<circ> Map_of_Val v)\<close>
          by fastforce
        moreover have \<open>dom (to_share \<circ> Map_of_Val u) = dom (to_share \<circ> Map_of_Val v)\<close>
          using Map_of_Val_same_dom
          by (metis \<open>u \<in> Well_Type (segidx.layout seg)\<close> dom_map_option_comp prems(1)) 
        moreover have \<open>dom (to_share \<circ> Map_of_Val u) = dom r \<union> dom (to_share \<circ> Map_of_Val v)\<close>
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


lemma (in agmem) op_alloc_mem:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc_mem TY raw_n \<lbrace> n \<Ztypecolon> Val raw_n Size \<longmapsto> ((seg |: []) \<Zinj> 1 \<Znrres> (Zero (\<tau>Array n TY)) \<Ztypecolon> Ref Identity \<^bold>s\<^bold>u\<^bold>b\<^bold>j seg. True) \<rbrace>\<close>
  unfolding op_alloc_mem_def
  apply (cases raw_n; simp, rule \<phi>M_tail_left, rule \<phi>M_getV; simp add: \<phi>expns)
  unfolding \<phi>M_set_res_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' times_fun dom_mult
                        R_mem.mult_in_dom Valid_Mem_def mult_strip_fine_011 mult_strip_fine_001
                        fiction_mem_\<I>'' share_mem_def' times_list_def)
  subgoal premises prems for R fic res mem' mem
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
                  (1(?seg := Fine (to_share \<circ> Map_of_Val (V_array.mk (TY, replicate n (Zero TY))))))\<close>])
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


lemma (in agmem) op_free_mem:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_mem vptr \<lbrace> (seg |: []) \<Zinj> 1 \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> (seg |: 0) \<Ztypecolon> Val vptr RawPointer \<longmapsto> 1\<rbrace>\<close>
  unfolding op_free_mem_def
  apply (cases vptr; simp, rule \<phi>M_getV; simp add: \<phi>expns)
  unfolding \<phi>M_set_res_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' times_fun dom_mult
                        R_mem.mult_in_dom Valid_Mem_def mult_strip_fine_011 mult_strip_fine_001
                        fiction_mem_\<I>'' share_mem_def' times_list_def)
  subgoal premises prems for R fic res memR mem
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



end






end