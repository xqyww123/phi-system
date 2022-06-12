theory NuInstructions
  imports NuPrime NuLLReps
begin

subsection \<open>Basic sequential instructions\<close>


context std_sem begin

definition op_drop :: "('VAL,'RES_N,'RES) proc" where
  "op_drop = (\<lambda>(v#vs,res). Success (vs,res))"

definition op_dup :: "('VAL,'RES_N,'RES) proc"
  where "op_dup = (\<lambda>(v#vs,res). Success (v#v#vs,res))"

definition op_set_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_var name' T = (\<lambda>(v#vs, res).
    if v \<in> Well_Type T \<and> pred_option1 (\<lambda>v. v \<in> Well_Type T) (!! (R_var.get res) name')
    then Success (vs, R_var.updt (map_fine (\<lambda>vars. vars(name' \<mapsto> v))) res)
    else Fail)"



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



definition \<phi>M_get_mem
    :: "'TY segidx \<Rightarrow> nat list \<Rightarrow> ('VAL \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "\<phi>M_get_mem seg idx F =
            \<phi>M_get_res_entry R_mem.get seg (\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type (segidx.layout seg)) \<ggreater> F (index_value idx val))"

term \<open>\<phi>M_getV \<tau>Pointer V_pointer.dest\<close>

definition \<phi>M_get_logptr :: \<open>'TY \<Rightarrow> ('TY logaddr \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_logptr TY F = \<phi>M_getV \<tau>Pointer V_pointer.dest (\<lambda>p. F (rawaddr_to_log TY p))\<close>

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
                mult_strip_fine_011)
  subgoal premises prems for vals R fic res mem mem'
  proof -
    note [simp] = mult_strip_fine_011
    from \<open>mem' ## mem\<close> have t1: \<open>mem' seg ## mem seg\<close> by (simp add: sep_disj_fun) 
    show ?thesis
      using \<open>\<forall>_. \<exists>_. _ = Fine _ \<and> _ \<in> _\<close>[THEN spec[where x=seg]] t1 \<open>valid_index (segidx.layout seg) idx\<close>
        apply (auto simp add: \<open>n \<noteq> 0\<close>)
      apply (rule \<phi>M_assert')
      using \<open>\<forall>_ \<in> dom _. _\<close>[unfolded Ball_def, THEN spec[where x=seg]]
       apply (auto simp add: times_fun)[1]

      subgoal premises prems2 for sh' v' proof -
        have [simp]: \<open>valid_index (Typeof v') idx\<close>
          by (simp add: \<open>valid_index (segidx.layout seg) idx\<close> \<open>Typeof v' = segidx.layout seg\<close>)
        note t2[simp] = this[THEN Mapof_Val_pull]

        have t3[simp]: \<open>pull_map idx sh' ## share n (to_share \<circ> Mapof_Val v)\<close>
          using \<open>sh' ## push_map idx _\<close> by (metis pull_map_sep_disj pull_push_map)
        have t5: \<open>Typeof (index_value idx v') = Typeof v\<close>
          using \<open>v \<in> Well_Type (index_type idx (segidx.layout seg))\<close>
              index_value_type
          by (metis WT_Typeof \<open>valid_index (Typeof v') idx\<close> \<open>Typeof v' = segidx.layout seg\<close>)

        let \<open>?lhs = ?rhs\<close> = \<open>to_share \<circ> Mapof_Val v' = sh' * push_map idx (share n (to_share \<circ> Mapof_Val v))\<close>
        from \<open>?lhs = ?rhs\<close> have \<open>pull_map idx ?lhs = pull_map idx ?rhs\<close> by fastforce
        note this[simplified pull_map_to_share pull_map_homo_mult pull_push_map t2]
        then have \<open>Mapof_Val (index_value idx v') = (strip_share \<circ> pull_map idx sh') ++ (Mapof_Val v)\<close>
          by (metis strip_share_fun_mult strip_share_share_funcomp(2) t3 strip_share_fun_share \<open>n \<noteq> 0\<close> strip_share_share_funcomp)
        then have txx: \<open>index_value idx v' = v\<close>
          using Valof_Map_append Valof_Map t5
          by (metis Valof_Map_append Valof_Map)

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
  apply (rule \<phi>M_get_logptr, cases ptr, simp, rule \<phi>M_get_Val, simp add: \<phi>expns,
         rule \<phi>SEQ, rule \<phi>M_assert, standard, rule \<phi>M_get_mem)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                        R_mem.mult_in_dom)
  subgoal premises prems for seg idx vals R fic res mem mem_remain'
  proof -
    show ?thesis
      using \<open>\<forall>_. \<exists>_. _ \<and> mem _ \<in> _\<close>[THEN spec[where x=seg]] \<open>mem_remain' * Fine mem \<in> Valid_Mem\<close>
      apply (auto simp add: mult_strip_fine_011 prems Valid_Mem_def times_fun
                            sep_disj_partial_map_some_none)
      subgoal premises prems2 for fic_mR mem_R val
      proof -
        show ?thesis
          apply (rule exI[where x=\<open>fic * FIC_mem.mk (1(seg := Fine (push_map idx (to_share \<circ> Mapof_Val u))))\<close>])
          apply (auto simp add: prems inj_image_mem_iff index_mod_value_welltyp)
          apply (rule index_mod_value_welltyp, simp add: prems)
          using index_mod_value_welltyp
          apply (rule exI[where x=fic], simp add: prems)
  
          thm Mapof_Val_modify_fiction
          thm prems
          thm prems2



        from \<open>to_share \<circ> Mapof_Val val = _\<close>
        have \<open>to_share \<circ> Mapof_Val (index_value idx val) = pull_map idx fic_mR * (to_share \<circ> Mapof_Val v)\<close>
          by (metis Mapof_Val_pull \<open>valid_index (segidx.layout seg) idx\<close>
                    \<open>Typeof val = segidx.layout seg\<close> pull_map_homo_mult pull_map_to_share pull_push_map)
        then have \<open>Mapof_Val (index_value idx val) = (strip_share \<circ> pull_map idx fic_mR) ++ (Mapof_Val v)\<close>
          by (metis prems2(5) pull_map_sep_disj pull_push_map strip_share_fun_mult strip_share_share_funcomp(2))
        then have \<open>val = v\<close>
      thm prems2(5)

  thm  Valid_Mem_def
  thm FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                R_mem.mult_in_dom Valid_Mem_def times_fun
                mult_strip_fine_011




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

definition op_new_var :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_new_var TY =
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_set_res_entry R_var.updt (\<lambda>f.
    let vname = (@vname. f vname = None)
     in f(vname := Some v)))"


lemma (in std) \<phi>M_get_var:
  \<open>v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> v \<Ztypecolon> Var vname \<longmapsto> Y \<rbrace>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_var vname TY F \<lbrace> v \<Ztypecolon> Var vname \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_get_var_def \<phi>M_get_res_entry_def \<phi>M_get_res_def
  apply (simp add: \<phi>expns R_var.prj.homo_mult )
  apply (subst R_var_valid_split)
  apply (auto simp add: \<phi>expns FIC_var_split times_set_def R_var.mult_in_dom mult_strip_fine_011)
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
      apply (auto simp add: R_var.inj_homo_mult[symmetric])
      done
  qed
  done

lemma (in std) \<phi>M_set_var:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname \<mapsto> u)) \<lbrace> v \<Ztypecolon> Var vname \<longmapsto> u \<Ztypecolon> Var vname \<rbrace>\<close>
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011)
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
      by (auto simp add: fun_eq_iff times_fun prems R_var.inj_homo_mult[symmetric])
  qed
  done


lemma (in std) op_get_var:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var vname TY \<lbrace> v \<Ztypecolon> Var vname \<longmapsto> v \<Ztypecolon> Var vname \<heavy_comma> v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding op_get_var_def Premise_def
  by (rule \<phi>M_get_var, assumption, rule \<phi>M_put_Val, simp add: \<phi>expns)

lemma (in std) op_set_var:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_var vname TY \<lbrace> v \<Ztypecolon> Var vname\<heavy_comma> u \<Ztypecolon> Identity \<longmapsto> u \<Ztypecolon> Var vname \<rbrace>\<close>
  unfolding op_set_var_def Premise_def
  by (rule \<phi>M_get_Val, rule \<phi>M_get_var, assumption,
      rule \<phi>SEQ, rule \<phi>M_assert, simp_all add: \<phi>expns, rule \<phi>M_set_var)

lemma (in std) op_new_var:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_new_var TY \<lbrace> v \<Ztypecolon> Identity \<longmapsto> v \<Ztypecolon> Var vname \<^bold>s\<^bold>u\<^bold>b\<^bold>j vname. True \<rbrace>\<close>
  unfolding op_new_var_def Premise_def
  apply (rule \<phi>M_tail_left, rule \<phi>M_get_Val)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011)
  subgoal premises prems for vals res R fic vars
  proof -
    note t1 = finite_map_freshness[OF \<open>finite (dom vars)\<close>, OF infinite_UNIV_nat]
    have t2[simp]: \<open>vars ## 1(SOME fic. vars fic = None \<mapsto> v)\<close>
      unfolding sep_disj_fun_def by simp (meson someI t1)
    have t3[simp]: \<open>vars (SOME vname. vars vname = None) = None\<close>
      by (meson someI t1)
    show ?thesis
      apply (rule exI[where x=\<open>fic * FIC_var.mk (Fine (1((@x. vars x = None) \<mapsto> v))) \<close>])
      apply (auto simp add: R_var_valid_split' FIC_var_split times_set_def prems)
      using \<open>(vals, fic) \<in> R\<close> apply blast
      apply (rule exI[where x = res])
      by (simp add: fun_eq_iff times_fun prems R_var.inj_homo_mult[symmetric])
  qed
  done


lemma (in std) op_free_var:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_var vname \<lbrace> v \<Ztypecolon> Var vname \<longmapsto> 1 \<rbrace>\<close>
  unfolding op_free_var_def \<phi>Procedure_def \<phi>M_set_res_entry_def
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011)
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



thm \<phi>SEQ
  thm \<phi>M_assert

lemma (in std) \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var vname TY \<lbrace> v \<Ztypecolon> Var vname \<longmapsto> v \<Ztypecolon> Var vname\<heavy_comma> v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding \<phi>Procedure_def op_get_var_def \<phi>M_get_res_entry_def \<phi>M_get_res_def Premise_def
  apply (simp add: \<phi>expns R_var.prj.homo_mult )
  apply (subst R_var_valid_split)
  apply (auto simp add: \<phi>expns FIC_var_split times_set_def R_var.mult_in_dom mult_strip_fine_011)
  subgoal premises prems for vals R fic res vars
  proof -
    note [simp] = \<open>vars ## 1(vname \<mapsto> v)\<close> [THEN sep_disj_fun[where x=vname], simplified]
    show ?thesis
      apply (simp add: times_fun)
      apply (rule \<phi>M_assert', rule \<open>v \<in> Well_Type TY\<close>)
      apply (simp add: \<phi>M_put_Val_def \<phi>expns)
      apply (rule exI[where x = \<open>fic * FIC_var.mk (Fine (1(vname \<mapsto> v)))\<close>])
      using prems apply (auto simp add: FIC_var_split times_set_def)
      apply (subst R_var_valid_split)
      apply (auto simp add: R_var.inj_homo_mult[symmetric])
      done
  qed
  done



  thm sep_disj_fun_def
  apply (subst FIC_var_split)
  thm R_var.proj_inj
  thm FIC_var_split




subsection \<open>Branches & Loops\<close>

definition op_sel :: "('VAL,'RES_N,'RES) proc"
  where "op_sel = (\<lambda>(c#b#a#vs,res).
    Success ((if snd (V_int.dest c) = 1 then a else b) # vs, res))"

definition op_if :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_if brT brF = (\<lambda>(c#vs,res).
    if snd (V_int.dest c) = 1 then brT (vs,res) else brF (vs,res))"

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

inductive SemRec :: "(('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) comp \<Rightarrow> ('VAL,'RES_N,'RES) state \<Rightarrow> bool" where
  SemRec_I0: "(\<And>g. F g x = y) \<Longrightarrow> SemRec F x y"
| SemRec_IS: "SemRec (F o F) x y \<Longrightarrow> SemRec F x y"

definition op_recursion :: "'TY \<Rightarrow> 'TY \<Rightarrow> (('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_recursion _ _ F s = (if (\<exists>t. SemRec F s t) then The (SemRec F s) else PartialCorrect)"

section \<open>Arithmetic instructions\<close>

subsection \<open>Integer arithmetic\<close>

definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_int bits const = \<phi>M_put_Val (V_int.mk (bits,const))"

definition op_const_size_t :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_size_t c = \<phi>M_assume (c < 2 ^ addrspace_bits)
                          \<ggreater> \<phi>M_put_Val (V_int.mk (addrspace_bits,c))"
  \<comment> \<open> `op_const_size_t` checks overflow during the compilation towards certain decided platform.  \<close>

definition op_add :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_add bits =
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_b.
      \<phi>M_put_Val (V_int.mk (bits, ((val_a + val_b) mod 2^bits)))
  ))"

definition op_sub :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_sub bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (bits, (2^bits + val_b - val_a mod 2^bits)) # vs, res)
      else Fail)"

definition op_udiv :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_udiv bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (bits, (val_b div val_a)) # vs, res)
      else Fail)"

definition op_lt :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_lt bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (1, (if val_b < val_a then 1 else 0)) # vs, res)
      else Fail)"

definition op_le :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_le bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (1, (if val_b \<le> val_a then 1 else 0)) # vs, res)
      else Fail)"

definition op_not :: "('VAL,'RES_N,'RES) proc"
  where "op_not = (\<lambda>(v#vs, res).
    case V_int.dest v of (bits, v') \<Rightarrow>
      if v \<in> Well_Type (\<tau>Int 1)
      then Success (V_int.mk (1, (1 - v')) # vs, res)
      else Fail)"

definition op_and :: "('VAL,'RES_N,'RES) proc"
  where "op_and = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (bit_a, val_a) \<Rightarrow>
    case V_int.dest vb of (bit_b, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int 1) \<and> vb \<in> Well_Type (\<tau>Int 1)
      then Success (V_int.mk (1, (val_a + val_b - 1)) # vs, res)
      else Fail)"

definition op_or :: "('VAL,'RES_N,'RES) proc"
  where "op_or = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (bit_a, val_a) \<Rightarrow>
    case V_int.dest vb of (bit_b, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int 1) \<and> vb \<in> Well_Type (\<tau>Int 1)
      then Success (V_int.mk (1, (val_a + val_b)) # vs, res)
      else Fail)"

definition op_equal :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_equal T = (\<lambda>(va#vb#vs, res).
    if va \<in> Well_Type T \<and> vb \<in> Well_Type T \<and> Can_EqCompare res va vb
    then Success (V_int.mk (1, (if EqCompare va vb then 1 else 0)) # vs, res)
    else Fail)"


section \<open>Tuple Operations\<close>

definition cons_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "cons_tup tys = (\<lambda>(vs,res).
    let N = length tys in
    if N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (take N vs) tys
    then Success (V_tup.mk (take N vs) # drop N vs, res)
    else Fail)"

definition op_dest_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_dest_tup tys = (\<lambda>(v#vs,res).
    let tup = V_tup.dest v in
    if list_all2 (\<lambda>v t. v \<in> Well_Type t) tup tys
    then Success (tup @ vs, res)
    else Fail)"

definition op_get_tuple :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_tuple idx T = (\<lambda>(v#vs,res).
    if valid_index T idx \<and> v \<in> Well_Type T
    then Success (index_value idx v # vs, res)
    else Fail)"

definition op_set_tuple :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_tuple idx T = (\<lambda>(v#tup#vs,res).
    if valid_index T idx \<and> tup \<in> Well_Type T \<and> v \<in> Well_Type (index_type idx T)
    then Success (index_mod_value idx (\<lambda>_. v) tup # vs, res)
    else Fail)"


section \<open>Memory & Pointer Operations\<close>

definition op_get_element_pointer :: "'TY \<Rightarrow> nat list \<Rightarrow>('VAL,'RES_N,'RES) proc"
  where \<open>op_get_element_pointer T idx = (\<lambda>(raddr#vs, res).
    case V_pointer.dest raddr of seg |: ofst \<Rightarrow>
      Success (V_pointer.mk (seg |: ofst + to_size_t (index_offset T idx)) # vs, res))\<close>

definition op_add_pointer :: "('VAL,'RES_N,'RES) proc"
  where "op_add_pointer = (\<lambda>(raddr1#raddr2#vs, res) \<Rightarrow>
    case V_pointer.dest raddr1 of seg1 |: ofst1 \<Rightarrow>
    case V_pointer.dest raddr2 of seg2 |: ofst2 \<Rightarrow>
    if (seg1 = Null \<or> seg2 = Null)
    then let seg = if seg1 = Null then seg2 else seg1
          in Success (V_pointer.mk (seg |: ofst1 + ofst2) # vs, res)
    else Fail)"


definition op_load :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_load TY = (\<lambda>(raddr'#vs, res) \<Rightarrow>
    let raddr = V_pointer.dest raddr'
      ; laddr = rawaddr_to_log TY raddr
      ; mem = the_fine (R_mem.get res)
     in if (\<exists>laddr'. valid_logaddr laddr' \<and> logaddr_type laddr' = TY \<and> logaddr_to_raw laddr' = raddr)
           \<and> 0 < MemObj_Size TY
           \<and> memaddr.segment laddr \<in> dom mem
        then Success (sem_read_mem laddr res # vs,res)
        else Fail)"

(* definition "heap_assignN n v seg heap = (\<lambda>key. case key of MemAddress (seg' |+ ofs') \<Rightarrow>
      if seg' = seg \<and> ofs' < n then v else
      if seg' = seg \<and> ofs' = n then Some DM_void else heap key | _ \<Rightarrow> heap key)"

definition op_alloc :: "('x::{zero,field}) itself \<Rightarrow> size_t word \<times> ('r::stack) \<longmapsto> memptr \<times>'r"
  where "op_alloc _ s = (case s of (heap,n,r) \<Rightarrow>  let seg = malloc heap in
  if segment_len seg = unat n \<and> segment_llty seg = LLTY('x) then
    Success (heap_assignN (unat n) (Some (deepize (0 :: 'x))) seg heap, memptr (seg |+ 0), r)
  else PartialCorrect)"

definition op_store :: " 'x itself \<Rightarrow> 'a itself \<Rightarrow> ('a::lrep,'a,'x,'x) index \<Rightarrow> 'x::field \<times> memptr \<times> ('r::stack) \<longmapsto> 'r "
  where "op_store _ _ idx s = (case s of (heap, x, memptr addr, r) \<Rightarrow>
    (let key = MemAddress (logical_addr_of addr) in
    case heap key of Some data \<Rightarrow>
      Success (heap(key \<mapsto> map_deepmodel (map_idx idx (\<lambda>_. x)) data), r) | _ \<Rightarrow> Fail))"

definition op_free :: " memptr \<times> ('r::stack) \<longmapsto> 'r "
  where "op_free s = (case s of (h,memptr (base |+ ofs),r) \<Rightarrow>
    (if ofs = 0 then Success (h |` (-{MemAddress (base |+ ofs) | ofs. True}), r) else Fail))"

*)

end

end
