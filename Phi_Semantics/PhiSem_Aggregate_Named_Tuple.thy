theory PhiSem_Aggregate_Named_Tuple
  imports PhiSem_Aggregate_Base
  abbrevs "<struct>" = "\<s>\<t>\<r>\<u>\<c>\<t>"
begin

section \<open>Semantics\<close>

debt_axiomatization semty_ntup    :: \<open>(symbol, TY) fmap \<Rightarrow> TY\<close>
                and sem_mk_ntup   :: \<open>(symbol, VAL) fmap \<Rightarrow> VAL\<close>
                and sem_dest_ntup :: \<open>VAL \<Rightarrow> (symbol, VAL) fmap\<close>
  where sem_mk_dest_ntup[simp]: \<open>sem_dest_ntup (sem_mk_ntup vs) = vs\<close>
  and   semty_ntup_eq_poison: \<open>semty_ntup Ts = \<p>\<o>\<i>\<s>\<o>\<n> \<longleftrightarrow> \<p>\<o>\<i>\<s>\<o>\<n> |\<in>| fmran Ts\<close>
  (*and   semty_ntup_inj: \<open> semty_ntup Ts1 = semty_ntup Ts2 \<longleftrightarrow> Ts1 = Ts2 \<close>*)
  and   WT_named_tup[simp]:
            \<open>Well_Type (semty_ntup Ts)  = { sem_mk_ntup vs |vs. fmrel (\<lambda> t v. v \<in> Well_Type t) Ts vs }\<close>
  and   semty_ntup_uniq:
            \<open>sem_mk_ntup vs \<in> Well_Type TY \<Longrightarrow> \<exists>Ts. TY = semty_ntup Ts\<close>
  and   zero_named_tup[simp]:
            \<open>Zero (semty_ntup Ts) = (if fmpred (\<lambda>_ t. Zero t \<noteq> None) Ts
                                     then Some (sem_mk_ntup (fmmap (the o Zero) Ts))
                                     else None)\<close>
  and   V_named_tup_sep_disj_R:
            \<open>sem_mk_ntup f1 ## vf2 \<Longrightarrow> (\<exists>f2. vf2 = sem_mk_ntup f2)\<close>
  and   V_named_tup_sep_disj_L:
            \<open>vf1 ## sem_mk_ntup f2 \<Longrightarrow> (\<exists>f1. vf1 = sem_mk_ntup f1)\<close>
  and   V_named_tup_sep_disj[simp]:
            \<open>sem_mk_ntup f1 ## sem_mk_ntup f2 \<longleftrightarrow> f1 ## f2 \<close>
  and   V_named_tup_mult[simp]:
            \<open>sem_mk_ntup f1 * sem_mk_ntup f2 = sem_mk_ntup (f1 * f2)\<close>
  and   idx_step_type_tup [eval_aggregate_path]:
            \<open>s |\<in>| fmdom Ts \<Longrightarrow> idx_step_type (AgIdx_S s) (semty_ntup Ts) = the (fmlookup Ts s)\<close>
  and   valid_idx_step_named_tup[eval_aggregate_path]:
            \<open>valid_idx_step (semty_ntup Ts) j \<longleftrightarrow> j \<in> {AgIdx_S s | s. s |\<in>| fmdom Ts }\<close>
  and   idx_step_value_named_tup[eval_aggregate_path]:
            \<open>idx_step_value (AgIdx_S s) (sem_mk_ntup vs) = the (fmlookup vs s)\<close>
  and   idx_step_mod_value_named_tup:
            \<open>idx_step_mod_value (AgIdx_S s) f (sem_mk_ntup vs) = sem_mk_ntup (fmupd s (f (the (fmlookup vs s))) vs)\<close>

lemma semty_ntup_uniq':
  \<open> sem_mk_ntup vs \<in> Well_Type TY
\<Longrightarrow> \<exists>Ts. TY = semty_ntup Ts \<and> fmrel (\<lambda> t v. v \<in> Well_Type t) Ts vs \<close>
  by (smt (verit, del_insts) WT_named_tup mem_Collect_eq sem_mk_dest_ntup semty_ntup_uniq)

lemma semty_ntup_uniq'2:
  \<open> sem_mk_ntup (fmupd s v vs) \<in> Well_Type TY
\<Longrightarrow> s |\<notin>| fmdom vs
\<Longrightarrow> \<exists>t Ts. TY = semty_ntup (fmupd s t Ts) \<and> fmrel (\<lambda> t v. v \<in> Well_Type t) Ts vs \<and> v \<in> Well_Type t \<close>
  apply (drule semty_ntup_uniq', auto simp: fmrel_iff)
  subgoal for Ts
    by (rule exI[where x=\<open>the (fmlookup Ts s)\<close>], rule exI[where x=\<open>fmfilter (\<lambda>k. k \<noteq> s) Ts\<close>], auto,
        smt (verit, ccfv_SIG) fmap_ext fmlookup_filter fmupd_lookup option.collapse option.rel_sel option.simps(3),
        presburger,
        smt (verit, best) option.sel option_rel_Some2) .

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal (semty_ntup fmempty) \<close>
  unfolding Is_Type_Literal_def ..

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal v
\<Longrightarrow> Is_Type_Literal (semty_ntup fm)
\<Longrightarrow> Is_Type_Literal (semty_ntup (fmupd k v fm)) \<close>
  unfolding Is_Type_Literal_def ..


subsubsection \<open>Syntax\<close>

abbreviation "semty_ntup_empty" ("\<s>\<t>\<r>\<u>\<c>\<t> {}")
  where \<open>semty_ntup_empty \<equiv> semty_ntup fmempty\<close>

notation semty_ntup_empty ("struct{}")
     and semty_ntup_empty ("S{}")
     and semty_ntup_empty ("\<s>\<t>\<r>\<u>\<c>\<t> { }")

nonterminal semty_ntup_args and semty_ntup_arg

syntax "semty_ntup_arg" :: \<open>\<phi>_symbol_ \<Rightarrow> logic \<Rightarrow> semty_ntup_arg\<close> ("_: _")
       "semty_ntup_arg0" :: \<open>semty_ntup_arg \<Rightarrow> semty_ntup_args\<close> ("_")
       "semty_ntup_args" :: \<open>semty_ntup_arg \<Rightarrow> semty_ntup_args \<Rightarrow> semty_ntup_args\<close> ("_, _")

       "_semty_ntup" :: \<open>semty_ntup_args \<Rightarrow> logic\<close> ("struct{_}" [50] 999)
       "_semty_ntup" :: \<open>semty_ntup_args \<Rightarrow> logic\<close> ("S{_}" [50] 999)
       "_semty_ntup" :: \<open>semty_ntup_args \<Rightarrow> logic\<close> ("\<s>\<t>\<r>\<u>\<c>\<t> {_}" [50] 999)

parse_translation \<open>[
  (\<^syntax_const>\<open>_semty_ntup\<close>, fn ctxt => fn [args] =>
    let fun strip_args (Const(\<^syntax_const>\<open>semty_ntup_args\<close>, _) $ x $ L)
              = x :: strip_args L
          | strip_args (Const(\<^syntax_const>\<open>semty_ntup_arg0\<close>, _) $ x) = [x]
          | strip_args _ = error "Bad Syntax"
     in \<^Const>\<open>semty_ntup\<close> $
        fold_rev (fn (Const(\<^syntax_const>\<open>semty_ntup_arg\<close>, _) $ s $ T) => (fn X =>
                        \<^Const>\<open>fmupd \<^Type>\<open>symbol\<close> \<^Type>\<open>TY\<close>\<close> $ s $ T $ X)
                   | X => error "Bad Syntax")
                 (strip_args args) \<^Const>\<open>fmempty \<^Type>\<open>symbol\<close> \<^Type>\<open>TY\<close>\<close>
    end)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>semty_ntup\<close>, fn ctxt => fn [args] =>
  let fun strip_fmupd (Const(\<^const_syntax>\<open>fmupd\<close>, _) $ s $ v $ L)
            = (s,v) :: strip_fmupd L
        | strip_fmupd (Const(\<^const_syntax>\<open>fmempty\<close>, _)) = []
      fun pass_sym (Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ X) = Phi_Tool_Symbol.print X
        | pass_sym X = X
      fun assemble [(s,v)] =
            Const(\<^syntax_const>\<open>semty_ntup_arg0\<close>, dummyT) $ (Const(\<^syntax_const>\<open>semty_ntup_arg\<close>, dummyT) $ pass_sym s $ v)
        | assemble ((s,v)::L) =
            Const(\<^syntax_const>\<open>semty_ntup_args\<close>, dummyT)
              $ (Const(\<^syntax_const>\<open>semty_ntup_arg\<close>, dummyT) $ pass_sym s $ v)
              $ (assemble L)
      fun assemble' [] = Const(\<^const_syntax>\<open>semty_ntup_empty\<close>, dummyT)
        | assemble' L = Const(\<^syntax_const>\<open>_semty_ntup\<close>, dummyT) $ assemble L
   in assemble' (strip_fmupd args)
  end)
]\<close>

subsubsection \<open>Basic Properties\<close>
  
lemma sem_mk_ntup_inj[simp]:
  \<open> sem_mk_ntup f1 = sem_mk_ntup f2 \<longleftrightarrow> f1 = f2 \<close>
  by (smt (verit) sem_mk_dest_ntup)

lemma V_named_tup_mult_cons[simp]:
  \<open> NO_MATCH fmempty y
\<Longrightarrow> s |\<notin>| fmdom y
\<Longrightarrow> sem_mk_ntup y * sem_mk_ntup (fmupd s x fmempty) = sem_mk_ntup (fmupd s x y)\<close>
  by simp

lemma idx_step_mod_value_named_tupl_cons:
  \<open> s \<noteq> s'
\<Longrightarrow> s |\<notin>| fmdom vs
\<Longrightarrow> idx_step_mod_value (AgIdx_S s') f (sem_mk_ntup (fmupd s v vs))
      = idx_step_mod_value (AgIdx_S s') f (sem_mk_ntup vs) * sem_mk_ntup (fmupd s v fmempty)\<close>
  unfolding idx_step_mod_value_named_tup
  by (simp add: fmupd_reorder_neq)

lemma idx_step_mod_value_named_tupl_cons':
  \<open> NO_MATCH fmempty vs
\<Longrightarrow> s |\<notin>| fmdom vs
\<Longrightarrow> idx_step_mod_value (AgIdx_S s) f (sem_mk_ntup (fmupd s v vs))
      = sem_mk_ntup vs * idx_step_mod_value (AgIdx_S s) f (sem_mk_ntup (fmupd s v fmempty)) \<close>
  unfolding idx_step_mod_value_named_tup
  by (simp add: fmupd_reorder_neq)

primrec semantic_named_tuple_constructor
  where \<open>semantic_named_tuple_constructor syms [] = sem_mk_ntup fmempty\<close>
      | \<open>semantic_named_tuple_constructor syms (v#R) =
            sem_mk_ntup (fmupd (hd syms) v
                (sem_dest_ntup (semantic_named_tuple_constructor (tl syms) R)))\<close>

subsubsection \<open>Homomorphic Properties\<close>

lemma homo_sep_mult_V_named_tup[simp]:
  \<open>homo_sep_mult (\<lambda>v. sem_mk_ntup (fmupd s v fmempty))\<close>
  including fmap.lifting
  unfolding homo_sep_mult_def
  by (auto, transfer, auto simp: fun_eq_iff times_fun_def map_upd_def)

lemma homo_sep_disj_V_named_tup[simp]:
  \<open>homo_sep_disj (\<lambda>v. sem_mk_ntup (fmupd s v fmempty))\<close>
  including fmap.lifting
  unfolding homo_sep_disj_def
  by (clarsimp, transfer, clarsimp simp: map_upd_def)

lemma closed_homo_sep_disj_V_named_tup[simp]:
  \<open>closed_homo_sep_disj (\<lambda>v. sem_mk_ntup (fmupd s v fmempty))\<close>
  including fmap.lifting
  unfolding closed_homo_sep_disj_def
  by (clarsimp, transfer, clarsimp simp: map_upd_def)

lemma homo_sep_V_named_tup[simp]:
  \<open>homo_sep (\<lambda>v. sem_mk_ntup (fmupd s v fmempty))\<close>
  unfolding homo_sep_def
  by simp

lemma closed_homo_sep_V_named_tup[simp]:
  \<open>closed_homo_sep (\<lambda>v. sem_mk_ntup (fmupd s v fmempty))\<close>
  unfolding closed_homo_sep_def
  by simp

subsubsection \<open>Reduction to poison\<close>

ML_file \<open>library/Ag_Named_Tuple.ML\<close>

local_setup \<open>setup_semty_ntup_to_poison\<close>


lemma semty_ntup_neq_poison[simp]:
  \<open> k |\<notin>| fmdom Ts
\<Longrightarrow> semty_ntup (fmupd k TY Ts) = \<p>\<o>\<i>\<s>\<o>\<n> \<longleftrightarrow> TY = \<p>\<o>\<i>\<s>\<o>\<n> \<or> semty_ntup Ts = \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  unfolding semty_ntup_eq_poison atomize_eq
  by (metis domIff fmdom.rep_eq fmdom_fmupd fmlookup_ran_iff fmupd_lookup option.simps(1))

lemma semty_ntup_neq_poison0[simp]:
  \<open> \<s>\<t>\<r>\<u>\<c>\<t> { } \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  unfolding semty_ntup_eq_poison
  by clarsimp

lemma
  \<open>\<s>\<t>\<r>\<u>\<c>\<t>{a: T, b: U, c: \<p>\<o>\<i>\<s>\<o>\<n>} = \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  by simp

lemma
  \<open>P (\<s>\<t>\<r>\<u>\<c>\<t>{a: T, b: U, c: \<p>\<o>\<i>\<s>\<o>\<n>}) = P \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  by simp

lemma
  \<open>\<s>\<t>\<r>\<u>\<c>\<t>{a: \<b>\<o>\<o>\<l>, b: \<b>\<o>\<o>\<l>, c: \<b>\<o>\<o>\<l>} \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  by simp



section \<open>\<phi>Type\<close>

subsection \<open>Empty Tuple\<close>

\<phi>type_def Empty_Named_Tuple :: \<open>(VAL, unit) \<phi>\<close>
  where \<open>x \<Ztypecolon> Empty_Named_Tuple \<equiv> sem_mk_ntup fmempty \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality
       (*and \<open>Semantic_Type Empty_Named_Tuple (semty_ntup fmempty)\<close> *)
       and \<open>Semantic_Zero_Val (semty_ntup fmempty) Empty_Named_Tuple ()\<close>
       and \<open>Is_Aggregate Empty_Named_Tuple\<close>
       and Inhabited
       and \<open>\<t>\<y>\<p>\<e>\<o>\<f> Empty_Named_Tuple = \<s>\<t>\<r>\<u>\<c>\<t> { }\<close>

\<phi>adhoc_overloading \<phi>_Empty_Tuple_sugar Empty_Named_Tuple


subsection \<open>Field\<close>

\<phi>type_def Named_Tuple_Field :: "symbol \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>"
  where \<open>Named_Tuple_Field s T \<equiv> (\<lambda>v. sem_mk_ntup (fmupd s v fmempty)) \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Functionality
       and \<open>Is_Aggregate (Named_Tuple_Field s T)\<close>
       and Separation_Homo
       and Inhabited

subsubsection \<open>Syntax\<close>

syntax "\<phi>_named_tuple_" :: \<open>\<phi>_symbol_ \<Rightarrow> logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_: _")

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_named_tuple_ s X))" => "\<phi>_named_tuple_ s X"

parse_translation \<open>[
  (\<^syntax_const>\<open>\<phi>_named_tuple_\<close>, fn ctxt => fn [sym,T] =>
      Const(\<^const_name>\<open>Named_Tuple_Field\<close>, dummyT)
          $ sym
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

subsubsection \<open>Properties\<close>

lemma \<t>\<y>\<p>\<e>\<o>\<f>_ntup_1 [simp, \<phi>type_property Named_Tuple_Field Semantic_Type]:
  \<open> \<t>\<y>\<p>\<e>\<o>\<f> \<lbrace> SYMBOL_VAR(s): T \<rbrace> = \<s>\<t>\<r>\<u>\<c>\<t> {SYMBOL_VAR(s): \<t>\<y>\<p>\<e>\<o>\<f> T} \<close> 
  unfolding SType_Of_def Named_Tuple_Field.unfold Inhabited_def Satisfiable_def
  apply auto
  apply (smt (z3) WT_named_tup Well_Type_unique exE_some fmempty_transfer fmrel_upd mem_Collect_eq)
  apply (metis (mono_tags, lifting) WT_named_tup fmempty_transfer fmrel_upd mem_Collect_eq)
   apply blast
  subgoal premises prems for x TY v
  proof -
    have t1: \<open>sem_mk_ntup (fmupd s v fmempty) \<in> Well_Type TY\<close>
      using prems(2) prems(3) by blast
    obtain TY' where t2: \<open>TY = semty_ntup (fmupd s TY' fmempty)\<close>
      apply (insert semty_ntup_uniq[OF t1]
                    prems(2)[THEN spec[where x=x], THEN spec[where x=\<open>sem_mk_ntup (fmupd s v fmempty)\<close>]],
             auto simp: fmrel_iff)
      using prems(3) apply blast
      by (smt (verit) fmap_exhaust fmdom_notD fmempty_lookup fmupd_lookup option.distinct(1) option_rel_Some2 rel_option_None2)
    from prems(1)[THEN spec[where x=\<open>TY'\<close>]] prems(2) have False
      by (auto simp: fmrel_iff t2,
          smt (verit, best) fmupd_lookup option.distinct(1) option.rel_sel option.sel sem_mk_dest_ntup)
    then show ?thesis
      by blast
  qed .

definition Named_Tuple_Types :: \<open>(VAL, 'x) \<phi> \<Rightarrow> (symbol, TY) fmap \<Rightarrow> bool\<close>
  where \<open>Named_Tuple_Types T Tys = (
    (\<p>\<o>\<i>\<s>\<o>\<n> |\<notin>| fmran Tys \<longleftrightarrow> Inhabited T \<and> (\<exists>TY. \<forall>x v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> v \<in> Well_Type TY)) \<and>
    (\<p>\<o>\<i>\<s>\<o>\<n> |\<notin>| fmran Tys \<longrightarrow>
        (\<forall>x c. c \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>vf. c = sem_mk_ntup vf \<and> fmrel (\<lambda>t v. v \<in> Well_Type t) Tys vf)))
)\<close>

lemma \<t>\<y>\<p>\<e>\<o>\<f>_ntup:
  \<open> Named_Tuple_Types T Tys
\<Longrightarrow> \<t>\<y>\<p>\<e>\<o>\<f> T \<equiv> semty_ntup Tys \<close>
  unfolding Named_Tuple_Types_def SType_Of_def atomize_eq
  by (auto simp: semty_ntup_eq_poison,
      metis semty_ntup_eq_poison,
      metis semty_ntup_eq_poison,
      metis semty_ntup_eq_poison,
      metis semty_ntup_eq_poison,
      smt (verit) Inhabited_def Satisfiable_def WT_named_tup Well_Type_unique mem_Collect_eq someI,
      blast,
      metis semty_ntup_eq_poison,
      metis semty_ntup_eq_poison,
      metis semty_ntup_eq_poison,
      metis semty_ntup_eq_poison)

lemma Named_Tuple_Types_0:
  \<open> Named_Tuple_Types Empty_Named_Tuple fmempty \<close>
  unfolding Named_Tuple_Types_def
  by (auto simp add: Empty_Named_Tuple.Inhabited, insert WT_named_tup, blast)


lemma Named_Tuple_Types_1:
  \<open> Named_Tuple_Types \<lbrace> SYMBOL_VAR(s): T \<rbrace> (fmupd s (\<t>\<y>\<p>\<e>\<o>\<f> T) fmempty) \<close>
  unfolding Named_Tuple_Types_def
  apply auto
  using SType_Of_not_poison semty_ntup_eq_poison apply fastforce
  apply (metis Named_Tuple_Field.expansion \<t>\<y>\<p>\<e>\<o>\<f>_ntup_1 SType_Of_not_poison semty_ntup_eq_poison)
  apply (metis Named_Tuple_Field.expansion SType_Of_not_poison \<t>\<y>\<p>\<e>\<o>\<f>_ntup_1 semty_ntup_eq_poison)
  by (metis SType_Of_not_poison fmempty_transfer fmlookup_ran_iff fmrel_upd fmupd_lookup)


lemma Named_Tuple_Types_N:
  \<open> Named_Tuple_Types U Tys
\<Longrightarrow> s |\<notin>| fmdom Tys
\<Longrightarrow> Named_Tuple_Types (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> U) (fmupd s (\<t>\<y>\<p>\<e>\<o>\<f> T) Tys) \<close>
  unfolding Named_Tuple_Types_def Inhabited_def Satisfiable_def
apply auto
  using semty_ntup_eq_poison semty_ntup_neq_poison apply force
  using semty_ntup_eq_poison semty_ntup_neq_poison apply force
  using semty_ntup_eq_poison semty_ntup_neq_poison apply force
  apply (drule V_named_tup_sep_disj_R, auto simp: )[1]
  apply (metis (mono_tags, opaque_lifting) finsert_iff fmdom_fmupd fmupd_lookup idx_step_type_tup option.sel semty_ntup_eq_poison semty_ntup_neq_poison semty_ntup_neq_poison0)
  using semty_ntup_eq_poison semty_ntup_neq_poison apply force
  apply (metis Inhabited_def SType_Of_not_poison Satisfiable_def V_named_tup_sep_disj empty_iff fmap_sepdisj_fmempty(2) fmdom_empty fmrel_fmdom_eq fset_simps(1) semty_ntup_eq_poison semty_ntup_neq_poison sep_disj_fmupd_left)
         apply (smt (verit, del_insts) SType_Of_not_poison V_named_tup_mult WT_named_tup fmap_times_fempty(2) fmrel_fmdom_eq fmrel_upd fmupd_times_right mem_Collect_eq semty_ntup_eq_poison semty_ntup_neq_poison)
  subgoal premises prems for x TY p a TYa b cb xa
  proof -
    thm prems
    obtain vf where t1: \<open>cb = sem_mk_ntup vf \<and> fmrel (\<lambda>t v. v \<in> Well_Type t) Tys vf\<close>
      using prems(2) prems(7) by blast
    have t2: \<open>sem_mk_ntup (fmupd s xa vf) \<in> Well_Type TYa\<close>
      by (metis V_named_tup_mult fmap_times_fempty(2) fmrel_fmdom_eq fmupd_times_right prems(1) prems(6) prems(7) prems(8) prems(9) t1)
    have t3: \<open>s |\<notin>| fmdom vf\<close>
      using fmrel_fmdom_eq prems(1) t1 by blast
    obtain t' Ts' where t4: \<open>TYa = semty_ntup (fmupd s t' Ts') \<and> fmrel (\<lambda>t v. v \<in> Well_Type t) Ts' vf \<and> xa \<in> Well_Type t'\<close>
      using semty_ntup_uniq'2 t2 t3 by presburger
    have t5: \<open>\<t>\<y>\<p>\<e>\<o>\<f> T = \<p>\<o>\<i>\<s>\<o>\<n>\<close>
      using prems(1) prems(10) prems(3) semty_ntup_eq_poison semty_ntup_neq_poison by force
    have t6: \<open>\<not> Inhabited T \<or> (\<forall>TY. \<exists>x v. v \<Turnstile> (x \<Ztypecolon> T) \<and> v \<notin> Well_Type TY)\<close>
      by (metis SType_Of_not_poison t5)
    then show ?thesis
    proof (rule, meson Inhabited_def Satisfiable_I prems(9))
      assume t7: \<open>\<forall>TY. \<exists>x v. v \<Turnstile> (x \<Ztypecolon> T) \<and> v \<notin> Well_Type TY\<close>
      then obtain x' v' where \<open>v' \<Turnstile> (x' \<Ztypecolon> T) \<and> v' \<notin> Well_Type t'\<close>
        by blast
      have t2: \<open>sem_mk_ntup (fmupd s v' vf) \<in> Well_Type TYa\<close>
        by (metis (no_types, lifting) V_named_tup_mult V_named_tup_sep_disj \<open>v' \<Turnstile> (x' \<Ztypecolon> T) \<and> v' \<notin> Well_Type t'\<close> all_not_fin_conv fmap_sepdisj_fmempty(2) fmap_times_fempty(2) fmdom_empty fmupd_times_right prems(6) prems(7) sep_disj_fmupd_left t1 t3)
      then show False
        using semty_ntup_uniq'2
        by (metis \<open>v' \<Turnstile> (x' \<Ztypecolon> T) \<and> v' \<notin> Well_Type t'\<close> finsert_iff fmdom_fmupd fmupd_lookup idx_step_type_tup option.sel t3 t4)
    qed
  qed
  apply (metis (no_types, lifting) SType_Of_not_poison V_named_tup_mult fmap_times_fempty(2) fmrel_fmdom_eq fmrel_upd fmupd_times_right semty_ntup_eq_poison semty_ntup_neq_poison)
  using semty_ntup_eq_poison semty_ntup_neq_poison apply force  
  using semty_ntup_eq_poison semty_ntup_neq_poison apply fastforce
  using semty_ntup_eq_poison semty_ntup_neq_poison apply force
  apply (metis (mono_tags, lifting) WT_named_tup mem_Collect_eq)
  using semty_ntup_eq_poison semty_ntup_neq_poison by force


simproc_setup \<t>\<y>\<p>\<e>\<o>\<f>_ntup (\<open>\<t>\<y>\<p>\<e>\<o>\<f> (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> U)\<close>) = \<open>
  fn _ => fn ctxt => fn ctm =>
    Drule.infer_instantiate ctxt [(("T",0), Thm.dest_arg ctm)] @{thm' \<t>\<y>\<p>\<e>\<o>\<f>_ntup}
      |> REPEAT_DETERM (resolve_tac ctxt @{thms' Named_Tuple_Types_N Named_Tuple_Types_1} 1)
      |> Seq.pull
      |> Option.map fst
\<close>

ML_file \<open>library/Ag_Named_Tuple2.ML\<close>


let_\<phi>type Named_Tuple_Field
  deriving \<open> Semantic_Zero_Val ty T x
         \<Longrightarrow> Semantic_Zero_Val (semty_ntup (fmupd s ty fmempty)) \<lbrace> SYMBOL_VAR(s): T \<rbrace> x \<close>

text \<open>All the reasoning rules below are for semantic properties.
      All reasoning rules for transformations and SL are derived automatically by the above \<open>\<phi>type_def\<close> command\<close>

lemma Empty_Tuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> Empty_Named_Tuple \<^emph> \<lbrace> SYMBOL_VAR(s): T \<rbrace>) = (a \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>)\<close>
  \<open>((a,()) \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> Empty_Named_Tuple) = (a \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>)\<close>
  unfolding BI_eq_iff
  by ((clarsimp; rule; clarsimp), blast, force)+

lemma Tuple_Field_zeros [\<phi>reason %semantic_zero_val_cut]:
  \<open> Semantic_Zero_Val ty T x
\<Longrightarrow> Semantic_Zero_Val (semty_ntup tys) Ts xs
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| fmdom tys
\<Longrightarrow> Semantic_Zero_Val (semty_ntup (fmupd s ty tys)) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> Ts) (x,xs) \<close>
  unfolding Semantic_Zero_Val_def Premise_def
  apply (clarsimp; cases \<open>fmpred (\<lambda>_ t. \<exists>y. Zero t = Some y) tys\<close>)
  apply (auto simp add: inj_image_mem_iff fmmap_fmupd)
  subgoal for x'
    by (rule exI[where x=\<open>sem_mk_ntup (fmupd s x' fmempty)\<close>],
        rule exI[where x=\<open>sem_mk_ntup (fmmap (the \<circ> Zero) tys)\<close>],
        auto simp add: fmlookup_dom_iff sep_disj_fmap.rep_eq,
        metis (no_types, lifting) fmap_times_fempty(2) fmempty_lookup fmlookup_dom_iff fmlookup_map fmmap_empty fmupd_times_right option.distinct(1)) .

section \<open>Reasoning\<close>

text \<open>All the reasoning rules below are for semantic properties.
      All reasoning rules for transformations and SL are derived automatically by the above \<open>\<phi>type_def\<close> command\<close>

subsubsection \<open>Is_Named_Tuple\<close>

definition Is_Named_Tuple :: \<open>(VAL, 'x) \<phi> \<Rightarrow> symbol fset \<Rightarrow> bool\<close>
  where \<open>Is_Named_Tuple T Fields = (\<forall>x c. c \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>vf. c = sem_mk_ntup vf \<and> fmdom vf = Fields))\<close>

\<phi>reasoner_group Is_Named_Tuple = (1000, [1000,1200]) for \<open>Is_Named_Tuple T Fields\<close>
  \<open>chekcs whether \<open>T\<close> is a named tuple\<close>

declare [[
  \<phi>reason_default_pattern \<open>Is_Named_Tuple ?T _\<close> \<Rightarrow> \<open>Is_Named_Tuple ?T _\<close> (100),
  \<phi>default_reasoner_group \<open>Is_Named_Tuple _ _\<close> : %Is_Named_Tuple (100)
]]

lemma Is_Named_Tuple_sing[\<phi>reason add]:
  \<open>Is_Named_Tuple \<lbrace> SYMBOL_VAR(s): T \<rbrace> {|s|}\<close>
  unfolding Is_Named_Tuple_def
  by clarsimp


lemma Is_Named_Tuple_comp[\<phi>reason add]:
  \<open> Is_Named_Tuple U S
\<Longrightarrow> Is_Named_Tuple (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> U) (finsert s S) \<close>
  unfolding Is_Named_Tuple_def Premise_def
  by (clarsimp, drule V_named_tup_sep_disj_R, auto, fastforce+)


subsection \<open>Semantics Related\<close>

lemma [\<phi>reason %chk_sem_ele_idx+20]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s = s'
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s') (semty_ntup (fmupd s TY Tys)) TY \<close>
  unfolding \<r>Guard_def Premise_def is_valid_step_idx_of_def
  by (clarsimp simp add: valid_idx_step_named_tup idx_step_type_tup)

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s \<noteq> s'
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s') (semty_ntup Tys) RET
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s') (semty_ntup (fmupd s TY Tys)) RET \<close>
  unfolding \<r>Guard_def Premise_def is_valid_step_idx_of_def
  by (clarsimp simp add: valid_idx_step_named_tup idx_step_type_tup)

lemma [\<phi>reason %chk_sem_ele_idx+20]:
  \<open> FAIL TEXT(s \<open>is not a field of the named tuple\<close>)
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s) (semty_ntup fmempty) RET \<close>
  unfolding \<r>Guard_def Premise_def FAIL_def
  by blast


lemma [\<phi>reason %inhabited+10]:
  \<open> Inhabited T
\<Longrightarrow> Is_Named_Tuple Ts fields
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s |\<notin>| fields
\<Longrightarrow> Inhabited Ts
\<Longrightarrow> Inhabited (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> Ts) \<close>
  unfolding subset_iff Premise_def Inhabited_def Satisfiable_def Semantic_Type_def Is_Named_Tuple_def
  apply (clarsimp)
  subgoal premises prems for x y p q
    by (insert prems(1)[THEN spec, THEN spec, THEN mp, OF prems(4)],
        clarify,
        rule exI[where x=x], rule exI[where x=y],
        rule exI[where x=\<open>sem_mk_ntup (fmupd s p fmempty)\<close>],
        rule exI[where x=q], insert prems(2-4), clarsimp, blast) .



subsection \<open>General\<close>

lemma [\<phi>reason 2000]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s \<noteq> s'
\<Longrightarrow> s |\<notin>| fmdom R
\<Longrightarrow> s |\<notin>| fmdom (fmupd s' v R) \<close>
  for s :: symbol
  unfolding Premise_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> s |\<notin>| fmdom fmempty \<close>
  by simp

subsection \<open>Index\<close>

lemma [\<phi>reason %aggregate_access]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' \<noteq> s
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X) Y (f o snd)\<close>
  unfolding \<phi>Aggregate_Getter_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def
            Is_Named_Tuple_def Ant_Seq_def
  by (clarsimp, drule V_named_tup_sep_disj_R, clarsimp simp: idx_step_value_named_tup, metis idx_step_value_named_tup)

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> Is_Named_Tuple X fields
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s |\<notin>| fields
\<Longrightarrow> \<phi>Aggregate_Getter idx T Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X) Y (f o fst)\<close>
  unfolding \<phi>Aggregate_Getter_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def Is_Named_Tuple_def
  by (clarsimp, drule V_named_tup_sep_disj_R, clarsimp simp: idx_step_value_named_tup, fastforce)

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> \<phi>Aggregate_Getter idx T Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) \<lbrace> SYMBOL_VAR(s): T \<rbrace> Y f\<close>
  unfolding \<phi>Aggregate_Getter_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp, metis fmupd_lookup idx_step_value_named_tup option.sel)



lemma [\<phi>reason %aggregate_access]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' \<noteq> s
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X') Y Y' (apsnd o f)\<close>
  unfolding \<phi>Aggregate_Mapper_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def
  apply clarsimp
  subgoal premises prems for g g' a b c' v' proof -
    obtain c'f where c'f: \<open>c' = sem_mk_ntup c'f\<close>
      using V_named_tup_sep_disj_R prems(5) by blast
    show ?thesis
      by (insert prems, simp add: c'f V_named_tup_mult_cons idx_step_mod_value_named_tupl_cons,
          rule exI[where x=\<open>sem_mk_ntup (fmupd s v' fmempty)\<close>],
          rule exI[where x=\<open>idx_step_mod_value (AgIdx_S s') (index_mod_value idx g) (sem_mk_ntup c'f)\<close>],
          simp add: V_named_tup_sep_disj idx_step_mod_value_named_tup fmupd_times_left,
          smt (verit, del_insts) fmap_sepdisj_fmempty(2) fmupd_lookup idx_step_mod_value_named_tup sep_disj_fmap.rep_eq)
  qed .

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> Is_Named_Tuple R fields
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s |\<notin>| fields
\<Longrightarrow> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): X \<rbrace> \<^emph> R) (\<lbrace> SYMBOL_VAR(s): X' \<rbrace> \<^emph> R) Y Y' (apfst o f)\<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def Is_Named_Tuple_def
  apply clarsimp
  subgoal premises prems for g g' a b c' v' proof -
    obtain c'f where c'f: \<open>c' = sem_mk_ntup c'f\<close>
      using V_named_tup_sep_disj_R prems(7) by blast
    show ?thesis
      by (insert prems,
          rule exI[where x=\<open>sem_mk_ntup (fmupd s (index_mod_value idx g v') fmempty)\<close>],
          rule exI[where x=c'],
          auto simp: c'f V_named_tup_mult_cons idx_step_mod_value_named_tupl_cons' \<r>Guard_def
                     Premise_def idx_step_mod_value_named_tup fmupd_times_right,
          metis fmupd_idem fmupd_lookup fmupd_times_right option.sel sem_mk_dest_ntup times_fmlookup,
          fastforce)
  qed .

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) \<lbrace> SYMBOL_VAR(s): X \<rbrace> \<lbrace> SYMBOL_VAR(s): X' \<rbrace> Y Y' f\<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: \<r>Guard_def Premise_def, metis fmupd_idem fmupd_lookup idx_step_mod_value_named_tup option.sel)

lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Constructor_Synth (semantic_named_tuple_constructor []) (() \<Ztypecolon> \<circle>) (semty_ntup fmempty) (() \<Ztypecolon> \<lbrace> \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def semantic_named_tuple_constructor_def \<phi>Type_Mapping_def
  by clarsimp

lemma [\<phi>reason %aggregate_access+20]:
  \<open> Semantic_Type' (x \<Ztypecolon> T) TY @tag \<A>ctr_arg (Inl s)
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth (semantic_named_tuple_constructor [s])
          (x \<Ztypecolon> List_Item T)
          (semty_ntup (fmupd s TY fmempty)) (x \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def semantic_named_tuple_constructor_def
            Action_Tag_def Semantic_Type'_def
  by (clarsimp, metis Satisfaction_def fmempty_transfer fmrel_upd)

lemma [\<phi>reason %aggregate_access]:
  \<open> Semantic_Type' (x \<Ztypecolon> T) TY @tag \<A>ctr_arg (Inl s)
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth (semantic_named_tuple_constructor sR) (xs \<Ztypecolon> L) (semty_ntup TyR) (r \<Ztypecolon> R)
\<Longrightarrow> s |\<notin>| fmdom TyR
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth (semantic_named_tuple_constructor (s # sR))
          ((x,xs) \<Ztypecolon> List_Item T \<^emph> L)
          (semty_ntup (fmupd s TY TyR)) ((x, r) \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> R)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def Semantic_Type'_def Action_Tag_def
  apply (clarsimp simp: V_named_tup_mult_cons[symmetric] times_list_def; rule)
  subgoal premises prems for vs v
    by (insert prems(1,3-) 
               prems(2)[THEN spec[where x=vs], THEN mp, OF \<open>vs \<Turnstile> (xs \<Ztypecolon> L)\<close>]
               V_named_tup_mult,
        
        rule exI[where x=\<open>sem_mk_ntup (fmupd s v fmempty)\<close>],
        rule exI[where x=\<open>semantic_named_tuple_constructor sR vs\<close>],
        auto simp: V_named_tup_sep_disj fmrel_fmdom_eq,
        metis fmap_times_fempty(2) fmupd_times_right)
  subgoal premises prems for vs v
    by (insert prems(1,3-) 
               prems(2)[THEN spec[where x=vs], THEN mp, OF \<open>vs \<Turnstile> (xs \<Ztypecolon> L)\<close>]
               V_named_tup_mult,
        metis fmrel_upd sem_mk_dest_ntup) .


lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Constructor (semantic_named_tuple_constructor []) [] (semty_ntup fmempty) (() \<Ztypecolon> \<lbrace> \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_named_tuple_constructor_def \<phi>Type_Mapping_def
  by clarsimp

lemma [\<phi>reason %aggregate_access+20]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T) @tag \<A>ctr_arg (Inl s)
\<Longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_named_tuple_constructor [s]) [v]
          (semty_ntup (fmupd s TY fmempty)) (x \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_named_tuple_constructor_def
            Action_Tag_def Semantic_Type'_def
  by (clarsimp, metis Satisfaction_def fmempty_transfer fmrel_upd)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T) @tag \<A>ctr_arg (Inl s)
\<Longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_named_tuple_constructor sR) vR (semty_ntup TyR) (r \<Ztypecolon> R)
\<Longrightarrow> s |\<notin>| fmdom TyR
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_named_tuple_constructor (s # sR)) (v # vR)
          (semty_ntup (fmupd s TY TyR)) ((x, r) \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> R)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_named_tuple_constructor_def
            Action_Tag_def Semantic_Type'_def
  apply (clarsimp simp: V_named_tup_mult_cons[symmetric]; rule)
  subgoal for vs
    by (rule exI[where x=\<open>sem_mk_ntup (fmupd s (\<phi>arg.dest v) fmempty)\<close>],
        rule exI[where x=\<open>sem_mk_ntup vs\<close>],
        simp add: V_named_tup_sep_disj,
        metis (no_types, lifting) fmap_sepdisj_fmempty(2) fmap_times_fempty(2) fmdom_notI fmempty_lookup fmrel_fmdom_eq fmupd_times_right sep_disj_fmupd_left)
  using V_named_tup_mult by auto


setup \<open>Context.theory_map (
  Generic_Element_Access.Agg_Constructors.add 0 (fn (kind, args, (ctxt,sequent)) =>
    if kind = "" andalso forall (fn ((SOME _, _),[_]) => true | _ => false) args
    then let val args' = map (fn (_,[rule]) => Phi_Local_Value.get_raw_val_in_rule rule) args
             val symbols = map (fn ((SOME s, _),_) => Phi_Tool_Symbol.mk_symbol s) args
                        |> HOLogic.mk_list \<^typ>\<open>symbol\<close>
             val ctor = Thm.cterm_of ctxt \<^Const>\<open>semantic_named_tuple_constructor for symbols\<close>
          in SOME (ctxt, ctor, args')
         end
    else NONE
))\<close>


subsection \<open>Synthesis\<close>

\<phi>reasoner_group \<phi>synthesis_ag_NT = (%\<phi>synthesis_ag, [%\<phi>synthesis_ag, %\<phi>synthesis_ag]) in \<phi>synthesis_ag
  \<open>for named tuple\<close>

declare synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> U\<close> for s T U,
         \<phi>reason %\<phi>synthesis_ag_NT
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. ?x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> SYMBOL_VAR(?s): ?T \<rbrace> \<^emph> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @tag synthesis\<close>]

        synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> \<rbrace>\<close>,
         \<phi>reason %\<phi>synthesis_ag_NT
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. ?x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] Empty_Named_Tuple \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @tag synthesis\<close>]

        synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> SYMBOL_VAR(s): T \<rbrace>\<close> for s T,
         \<phi>reason %\<phi>synthesis_ag_NT
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. ?x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> SYMBOL_VAR(?s): ?T \<rbrace> \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @tag synthesis\<close>]


end