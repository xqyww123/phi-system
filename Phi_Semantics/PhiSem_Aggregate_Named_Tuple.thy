theory PhiSem_Aggregate_Named_Tuple
  imports PhiSem_Aggregate_Base
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype named_tuple_ty =
  named_tup     :: \<open>(symbol, 'self) fmap\<close>

debt_axiomatization T_named_tup :: \<open>(symbol, TY) fmap type_entry\<close>
  where named_tuple_ty_ax: \<open>named_tuple_ty TY_CONS_OF T_named_tup\<close>

interpretation named_tuple_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_named_tup
  using named_tuple_ty_ax .

(*TODO: intergrate automatic hidding into the automation command*)
hide_fact named_tuple_ty_ax


subsubsection \<open>Value\<close>

virtual_datatype named_tuple_val =
  V_named_tup   :: \<open>(symbol, 'self) fmap\<close>

debt_axiomatization V_named_tup :: \<open>(symbol, VAL) fmap value_entry\<close>
  where named_tuple_val_ax: \<open>named_tuple_val VAL_CONS_OF V_named_tup\<close>

interpretation named_tuple_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_named_tup
  using named_tuple_val_ax .

hide_fact named_tuple_val_ax

(* abbreviation \<open>struct \<equiv> named_tup.mk\<close> *)

(*TODO: syntax*)
(* term \<open>struct {name: asd, nam2: TT}\<close> *)


subsection \<open>Semantics\<close>

debt_axiomatization
        WT_named_tup[simp]:
            \<open>Well_Type (named_tup.mk Ts)  = { V_named_tup.mk vs |vs. fmrel (\<lambda> t v. v \<in> Well_Type t) Ts vs }\<close>
  and   zero_named_tup[simp]:
            \<open>Zero (named_tup.mk Ts) = (if fmpred (\<lambda>_ t. Zero t \<noteq> None) Ts
                                       then Some (V_named_tup.mk (fmmap (the o Zero) Ts))
                                       else None)\<close>
  and   V_named_tup_sep_disj_R:
            \<open>V_named_tup.mk f1 ## vf2 \<Longrightarrow> (\<exists>f2. vf2 = V_named_tup.mk f2)\<close>
  and   V_named_tup_sep_disj_L:
            \<open>vf1 ## V_named_tup.mk f2 \<Longrightarrow> (\<exists>f1. vf1 = V_named_tup.mk f1)\<close>
  and   V_named_tup_sep_disj:
            \<open>V_named_tup.mk f1 ## V_named_tup.mk f2 \<longleftrightarrow> (fmdom f1 |\<inter>| fmdom f2 = {||})\<close>
  and   V_named_tup_mult:
            \<open>V_named_tup.mk f1 * V_named_tup.mk f2 = V_named_tup.mk (f1 ++\<^sub>f f2)\<close>
  and   idx_step_type_tup [eval_semantic_index]:
            \<open>s |\<in>| fmdom Ts \<Longrightarrow> idx_step_type (AgIdx_S s) (named_tup.mk Ts) = the (fmlookup Ts s)\<close>
  and   valid_idx_step_tup[eval_semantic_index]:
            \<open>valid_idx_step (named_tup.mk Ts) j \<longleftrightarrow> j \<in> {AgIdx_S s | s. s |\<in>| fmdom Ts }\<close>
  and   idx_step_value_named_tup[eval_semantic_index]:
            \<open>idx_step_value (AgIdx_S s) (V_named_tup.mk vs) = the (fmlookup vs s)\<close>
  and   idx_step_mod_value_named_tup:
            \<open>idx_step_mod_value (AgIdx_S s) f (V_named_tup.mk vs) = V_named_tup.mk (fmupd s (f (the (fmlookup vs s))) vs)\<close>

lemma V_named_tup_mult_cons:
  \<open> V_named_tup.mk y * V_named_tup.mk (fmupd s x fmempty) = V_named_tup.mk (fmupd s x y)\<close>
  by (simp add: V_named_tup_mult)

lemma idx_step_mod_value_named_tupl_cons:
  \<open> s \<noteq> s'
\<Longrightarrow> idx_step_mod_value (AgIdx_S s') f (V_named_tup.mk (fmupd s v vs))
      = idx_step_mod_value (AgIdx_S s') f (V_named_tup.mk vs) * V_named_tup.mk (fmupd s v fmempty)\<close>
  unfolding idx_step_mod_value_named_tup
  by (simp add: V_named_tup_mult_cons fmupd_reorder_neq)

lemma idx_step_mod_value_named_tupl_cons':
  \<open> NO_MATCH fmempty vs
\<Longrightarrow> idx_step_mod_value (AgIdx_S s) f (V_named_tup.mk (fmupd s v vs))
      = V_named_tup.mk vs * idx_step_mod_value (AgIdx_S s) f (V_named_tup.mk (fmupd s v fmempty)) \<close>
  unfolding idx_step_mod_value_named_tup
  by (simp add: V_named_tup_mult_cons fmupd_reorder_neq)


section \<open>\<phi>Type\<close>

subsection \<open>Empty Tuple\<close>

definition Empty_Named_Tuple :: \<open>(VAL, unit) \<phi>\<close>
  where \<open>Empty_Named_Tuple x = { V_named_tup.mk fmempty }\<close>

\<phi>adhoc_overloading \<phi>_Empty_Tuple_sugar Empty_Named_Tuple

lemma Empty_Named_Tuple_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Empty_Named_Tuple) \<longleftrightarrow> p = V_named_tup.mk fmempty \<close>
  unfolding Empty_Named_Tuple_def \<phi>Type_def by simp


subsection \<open>Field\<close>

definition Named_Tuple_Field :: "symbol \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>"
  where "Named_Tuple_Field s T x = { V_named_tup.mk (fmupd s v fmempty) |v. v \<in> T x }"

syntax "\<phi>_named_tuple_" :: \<open>\<phi>_symbol_ \<Rightarrow> logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_: _")

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_named_tuple_ s X))" => "\<phi>_named_tuple_ s X"

parse_translation \<open>[
  (\<^syntax_const>\<open>\<phi>_named_tuple_\<close>, fn ctxt => fn [sym,T] =>
      Const(\<^const_name>\<open>Named_Tuple_Field\<close>, dummyT)
          $ (case sym of (Const(\<^syntax_const>\<open>_LOG_EXPR_SYMBOL_\<close>, _) $ x) => x
                       | _ => Const(\<^const_name>\<open>mk_symbol\<close>, dummyT) $ sym)
          $ T)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>Named_Tuple_Field\<close>, fn ctxt => fn [sym,T] =>
      Const (\<^syntax_const>\<open>_\<phi>Tuple\<close>, dummyT) $
        (Const (\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $
           (Const (\<^syntax_const>\<open>\<phi>_named_tuple_\<close>, dummyT)
              $ (case sym of Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ id => Phi_Tool_Symbol.print id
                           | _ => sym)
              $ T)))
]\<close>

lemma Named_Tuple_Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<lbrace> LOGIC(s): T \<rbrace>) \<longleftrightarrow> (\<exists>v. p = V_named_tup.mk (fmupd s v fmempty) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding Named_Tuple_Field_def \<phi>Type_def by simp

lemma Named_Tuple_Field_inhabited[elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> \<lbrace> LOGIC(s): T \<rbrace>) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Empty_Tuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> Empty_Named_Tuple \<^emph> \<lbrace> LOGIC(s): T \<rbrace>) = (a \<Ztypecolon> \<lbrace> LOGIC(s): T \<rbrace>)\<close>
  \<open>((a,()) \<Ztypecolon> \<lbrace> LOGIC(s): T \<rbrace> \<^emph> Empty_Named_Tuple) = (a \<Ztypecolon> \<lbrace> LOGIC(s): T \<rbrace>)\<close>
  unfolding set_eq_iff
  by ((clarsimp; rule; clarsimp simp add: \<phi>expns V_named_tup_mult V_named_tup_sep_disj),
      blast,
      metis V_named_tup_mult V_named_tup_sep_disj fmadd_empty(2) fmdom'_restrict_fset_precise fmdom_empty fmrestrict_fset_null,
      (clarsimp; rule; clarsimp simp add: \<phi>expns V_named_tup_mult V_named_tup_sep_disj),
      blast,
      metis V_named_tup_mult V_named_tup_sep_disj fmadd_empty(1) fmdom'_restrict_fset_precise fmdom_empty fmrestrict_fset_empty)


lemma Named_Tuple_Field_zero  [\<phi>reason 1000]:
  \<open>\<phi>Zero ty T x \<Longrightarrow> \<phi>Zero (named_tup.mk (fmupd s ty fmempty)) \<lbrace> LOGIC(s): T \<rbrace> x \<close>
  unfolding \<phi>Zero_def
  by (clarsimp simp add: \<phi>expns,
      metis (mono_tags, lifting) Named_Tuple_Field_expn comp_apply fmmap_empty fmmap_fmupd fmpred_empty fmpred_upd image_eqI option.sel)

lemma Tuple_Field_zeros [\<phi>reason 1000]:
  \<open> s |\<notin>| fmdom tys
\<Longrightarrow> \<phi>Zero ty T x
\<Longrightarrow> \<phi>Zero (named_tup.mk tys) Ts xs
\<Longrightarrow> \<phi>Zero (named_tup.mk (fmupd s ty tys)) (\<lbrace> LOGIC(s): T \<rbrace> \<^emph> Ts) (x,xs) \<close>
  unfolding \<phi>Zero_def
  apply (clarsimp simp add: \<phi>expns; cases \<open>fmpred (\<lambda>_ t. \<exists>y. Zero t = Some y) tys\<close>;
     auto simp add: inj_image_mem_iff \<phi>expns fmmap_fmupd
     V_named_tup_mult_cons[where s=s and y=\<open>fmmap (the \<circ> Zero) tys\<close>, symmetric])
  subgoal for x'
    by (rule exI[where x=\<open>V_named_tup.mk (fmmap (the \<circ> Zero) tys)\<close>],
        rule exI[where x=\<open>V_named_tup.mk (fmupd s x' fmempty)\<close>],
        auto simp add: V_named_tup_sep_disj) .

lemma Tuple_Field_semty[\<phi>reason 1000]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<lbrace> LOGIC(s): T \<rbrace>) (named_tup.mk (fmupd s TY fmempty))\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp simp add: \<phi>expns; blast)

lemma Tuple_Field_semtys[\<phi>reason 1000]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (xs \<Ztypecolon> Ts) (named_tup.mk TYs)
\<Longrightarrow> \<phi>SemType ((x,xs) \<Ztypecolon> (\<lbrace> LOGIC(s): T \<rbrace> \<^emph> Ts)) (named_tup.mk (fmupd s TY TYs))\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp simp add: \<phi>expns; metis V_named_tup_mult fmadd_empty(2) fmadd_fmupd fmrel_upd)

subsection \<open>Index\<close>

lemma [\<phi>reason 1200]:
  \<open> \<g>\<u>\<a>\<r>\<d> s' \<noteq> s
\<Longrightarrow> \<phi>Index_getter (AgIdx_S s' # idx) X Y f
\<Longrightarrow> \<phi>Index_getter (AgIdx_S s' # idx) (\<lbrace> LOGIC(s): T \<rbrace> \<^emph> X) Y (f o snd)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns,
      metis V_named_tup_mult V_named_tup_sep_disj_L fmadd_empty(2) fmadd_fmupd fmupd_lookup idx_step_value_named_tup)

lemma [\<phi>reason 1201]:
  \<open> \<g>\<u>\<a>\<r>\<d> s' = s
\<Longrightarrow> \<phi>Index_getter idx T Y f
\<Longrightarrow> \<phi>Index_getter (AgIdx_S s' # idx) (\<lbrace> LOGIC(s): T \<rbrace> \<^emph> X) Y (f o fst)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns,
      metis V_named_tup_mult V_named_tup_sep_disj_L fmadd_fmupd fmupd_lookup idx_step_value_named_tup option.sel)

lemma [\<phi>reason 1201]:
  \<open> \<g>\<u>\<a>\<r>\<d> s' = s
\<Longrightarrow> \<phi>Index_getter idx T Y f
\<Longrightarrow> \<phi>Index_getter (AgIdx_S s' # idx) \<lbrace> LOGIC(s): T \<rbrace> Y f\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns, metis fmupd_lookup idx_step_value_named_tup option.sel)

lemma [\<phi>reason 1200]:
  \<open> \<g>\<u>\<a>\<r>\<d> s' \<noteq> s
\<Longrightarrow> \<phi>Index_mapper (AgIdx_S s' # idx) X X' Y Y' f
\<Longrightarrow> \<phi>Index_mapper (AgIdx_S s' # idx) (\<lbrace> LOGIC(s): T \<rbrace> \<^emph> X) (\<lbrace> LOGIC(s): T \<rbrace> \<^emph> X') Y Y' (apsnd o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns )
  subgoal premises prems for g g' a b c' v' proof -
    obtain c'f where c'f: \<open>c' = V_named_tup.mk c'f\<close> using V_named_tup_sep_disj_L[OF \<open>c' ## _\<close>] by blast
    show ?thesis
      by (insert prems, simp add: c'f V_named_tup_mult_cons idx_step_mod_value_named_tupl_cons,
          rule exI[where x=\<open>idx_step_mod_value (AgIdx_S s') (index_mod_value idx g) (V_named_tup.mk c'f)\<close>],
          rule exI[where x=\<open>V_named_tup.mk (fmupd s v' fmempty)\<close>],
          simp add: V_named_tup_sep_disj, rule,
          blast,
          simp add: idx_step_mod_value_named_tup V_named_tup_sep_disj)
  qed .

lemma [\<phi>reason 1201]:
  \<open> \<g>\<u>\<a>\<r>\<d> s' = s
\<Longrightarrow> \<phi>Index_mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Index_mapper (AgIdx_S s' # idx) (\<lbrace> LOGIC(s): X \<rbrace> \<^emph> R) (\<lbrace> LOGIC(s): X' \<rbrace> \<^emph> R) Y Y' (apfst o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns )
  subgoal premises prems for g g' a b c' v' proof -
    obtain c'f where c'f: \<open>c' = V_named_tup.mk c'f\<close> using V_named_tup_sep_disj_L[OF \<open>c' ## _\<close>] by blast
    show ?thesis
      by (insert prems, simp add: c'f V_named_tup_mult_cons idx_step_mod_value_named_tupl_cons',
          metis V_named_tup_sep_disj fmdom_fmupd fmupd_idem fmupd_lookup idx_step_mod_value_named_tup option.sel)
  qed .

lemma [\<phi>reason 1201]:
  \<open> \<g>\<u>\<a>\<r>\<d> s' = s
\<Longrightarrow> \<phi>Index_mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Index_mapper (AgIdx_S s' # idx) \<lbrace> LOGIC(s): X \<rbrace> \<lbrace> LOGIC(s): X' \<rbrace> Y Y' f\<close>
  unfolding \<phi>Index_mapper_def
  by (clarsimp simp add: \<phi>expns, metis fmupd_idem fmupd_lookup idx_step_mod_value_named_tup option.sel)


end