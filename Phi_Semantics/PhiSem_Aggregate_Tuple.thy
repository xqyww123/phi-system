theory PhiSem_Aggregate_Tuple
  imports PhiSem_Aggregate_Base
  abbrevs "<tup>" = "\<t>\<u>\<p>"
begin

section \<open>Semantics\<close>

debt_axiomatization sem_tup_T    :: \<open>TY list \<Rightarrow> TY\<close>
                and sem_mk_tup   :: \<open>VAL list \<Rightarrow> VAL\<close>
                and sem_dest_tup :: \<open>VAL \<Rightarrow> VAL list\<close>
                where sem_dest_mk_tup[simp]: \<open>sem_dest_tup (sem_mk_tup vs) = vs\<close>
  and   WT_tup[simp]: \<open>Well_Type (sem_tup_T ts)  = { sem_mk_tup vs |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
  and   semty_tup_eq_poison[simp]: \<open>sem_tup_T Ts = \<p>\<o>\<i>\<s>\<o>\<n> \<longleftrightarrow> \<p>\<o>\<i>\<s>\<o>\<n> \<in> set Ts\<close>
  and   semty_tup_uniq:
            \<open>sem_mk_tup vs \<in> Well_Type TY \<Longrightarrow> \<exists>Ts. TY = sem_tup_T Ts\<close>

  and   zero_tup[simp]: \<open>sem_tup_T Ts \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<Longrightarrow> Zero (sem_tup_T Ts) = map_option sem_mk_tup (those (map Zero Ts))\<close>
  and   V_tup_sep_disj_R[simp]: \<open>sem_mk_tup l1 ## vl2 \<longleftrightarrow> (\<exists>l2. vl2 = sem_mk_tup l2)\<close>
  and   V_tup_sep_disj_L[simp]: \<open>vl1 ## sem_mk_tup l2 \<longleftrightarrow> (\<exists>l1. vl1 = sem_mk_tup l1)\<close>
  and   V_tup_mult    : \<open>sem_mk_tup l1 * sem_mk_tup l2 = sem_mk_tup (l1 @ l2)\<close>
  and   idx_step_type_tup [eval_aggregate_path] : \<open> sem_tup_T tys \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> i < length tys
                                                \<Longrightarrow> idx_step_type (AgIdx_N i) (sem_tup_T tys) = tys!i \<close>
  and   valid_idx_step_tup[eval_aggregate_path] : \<open> sem_tup_T tys \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>
                                                \<Longrightarrow> valid_idx_step (sem_tup_T tys) j \<longleftrightarrow> j \<in> {AgIdx_N i | i. i < length tys} \<close>
  and   idx_step_value_tup[eval_aggregate_path] : \<open>idx_step_value (AgIdx_N i) (sem_mk_tup vs) = vs!i\<close>
  and   idx_step_mod_value_tup : \<open>idx_step_mod_value (AgIdx_N i) f (sem_mk_tup vs) = sem_mk_tup (vs[i := f (vs!i)])\<close>

lemma sem_mk_tup_inj[simp]:
  \<open>sem_mk_tup vs1 = sem_mk_tup vs2 \<longleftrightarrow> vs1 = vs2\<close>
  by (metis sem_dest_mk_tup)


subsubsection \<open>Syntax\<close>

abbreviation semty_tup_empty ("\<t>\<u>\<p> {}")
  where \<open>semty_tup_empty \<equiv> sem_tup_T []\<close>

notation semty_tup_empty ("tup{}")
     and semty_tup_empty ("T{}")
     and semty_tup_empty ("\<t>\<u>\<p> { }")

syntax "\<phi>_tuple_" :: \<open>logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_")

       "_semty_tup" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("tup{_}" [50] 999)
       "_semty_tup" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("T{_}" [50] 999)
       "_semty_tup" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("\<t>\<u>\<p> {_}" [50] 999)

parse_translation \<open>[
  (\<^syntax_const>\<open>_semty_tup\<close>, fn ctxt => fn [args] =>
    \<^Const>\<open>sem_tup_T\<close> $
    fold_rev (fn (Const(\<^syntax_const>\<open>\<phi>_tuple_\<close>, _) $ T) => (fn X => \<^Const>\<open>list.Cons \<^Type>\<open>TY\<close>\<close> $ T $ X)
               | _ => error "Bad Syntax")
             (strip_phi_tuple_args args) \<^Const>\<open>list.Nil \<^Type>\<open>TY\<close>\<close>)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>sem_tup_T\<close>, fn ctxt => fn [args] =>
  let fun strip_list (Const(\<^const_syntax>\<open>list.Cons\<close>, _) $ T $ L)
            = T :: strip_list L
        | strip_list (Const(\<^const_syntax>\<open>list.Nil\<close>, _)) = []
      fun assemble [T] =
            Const(\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $ (Const(\<^syntax_const>\<open>\<phi>_tuple_\<close>, dummyT) $ T)
        | assemble (T::L) =
            Const(\<^syntax_const>\<open>_\<phi>tuple_args\<close>, dummyT)
              $ (Const(\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $ (Const(\<^syntax_const>\<open>\<phi>_tuple_\<close>, dummyT) $ T))
              $ (assemble L)
      fun assemble' [] = Const(\<^const_syntax>\<open>semty_tup_empty\<close>, dummyT)
        | assemble' L = Const(\<^syntax_const>\<open>_semty_tup\<close>, dummyT) $ assemble L
   in assemble' (strip_list args)
  end)
]\<close>

(*
  "_semty_tup_arg0 (_semty_tup_arg s x)" <= "CONST list.Cons (_MK_SYMBOL_ s) x CONST fmempty"
  "_semty_tup_arg0 (_semty_tup_arg s x)" == "CONST list.Cons s x CONST fmempty"
  "_semty_tup_args (_semty_tup_arg s x) r" <= "CONST fmupd (_MK_SYMBOL_ s) x r"
  "_semty_tup_args (_semty_tup_arg s x) r" == "CONST fmupd s x r"
*)


subsubsection \<open>Basic Properties\<close>

lemma V_tup_mult_cons:
  \<open>NO_MATCH vs ([]::VAL list) \<Longrightarrow> sem_mk_tup (v#vs) = sem_mk_tup [v] * sem_mk_tup vs\<close>
  using V_tup_mult by simp

lemma list_all_replicate:
  \<open>list_all P (replicate n x) \<longleftrightarrow> n = 0 \<or> P x\<close>
  by (induct n; simp; blast)

primrec semantic_tuple_constructor
  where \<open>semantic_tuple_constructor (n::nat) [] = sem_mk_tup []\<close>
      | \<open>semantic_tuple_constructor n (v#R) =
            sem_mk_tup (v # sem_dest_tup (semantic_tuple_constructor 0 R))\<close>

lemma semantic_tuple_constructor_N_no_use:
  \<open> NO_MATCH 0 N
\<Longrightarrow> semantic_tuple_constructor N L = semantic_tuple_constructor 0 L \<close>
  by (induct L; auto)

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal (\<t>\<u>\<p> {}) \<close> ..

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal H
\<Longrightarrow> Is_Type_Literal (sem_tup_T L)
\<Longrightarrow> Is_Type_Literal (sem_tup_T (H#L)) \<close>
  ..

(* lemma Valid_Type_\<tau>Tuple[simp]:
  \<open>Valid_Type (sem_tup_T Ts) \<longleftrightarrow> list_all Valid_Type Ts\<close>
  unfolding Satisfiable_def
  by (simp; induct Ts; simp add: list_all2_Cons1) *)

subsubsection \<open>Reduction to poison\<close>

ML_file \<open>library/Ag_Tuple.ML\<close>

local_setup \<open>setup_semty_tup_to_poison\<close>

lemma
  \<open>P (\<t>\<u>\<p> {\<p>\<o>\<i>\<s>\<o>\<n>}) = P \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  by simp

lemma
  \<open>P (\<t>\<u>\<p> {A, B, \<p>\<o>\<i>\<s>\<o>\<n>, C}) = P \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  by simp


section \<open>\<phi>Type\<close>

subsection \<open>Empty Tuple\<close>

\<phi>type_def Empty_Tuple :: \<open>(VAL, unit) \<phi>\<close>
  where \<open>x \<Ztypecolon> Empty_Tuple \<equiv> sem_mk_tup [] \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality
       and \<open>\<t>\<y>\<p>\<e>\<o>\<f> Empty_Tuple = \<t>\<u>\<p> {}\<close>
       and \<open>Semantic_Zero_Val (sem_tup_T []) Empty_Tuple ()\<close>
       and \<open>Is_Aggregate Empty_Tuple\<close>
       and Inhabited

\<phi>adhoc_overloading \<phi>_Empty_Tuple_sugar Empty_Tuple

subsection \<open>Field\<close>

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def Tuple_Field :: "(VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>"
  where \<open>Tuple_Field T \<equiv> (\<lambda>v. sem_mk_tup [v]) \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Functionality
       and \<open>Is_Aggregate (Tuple_Field T)\<close>

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_tuple_ X))" \<rightleftharpoons> "CONST Tuple_Field X"

definition Tuple_Type_Helper :: \<open>(VAL, 'x) \<phi> \<Rightarrow> TY list \<Rightarrow> bool\<close>
  where \<open>Tuple_Type_Helper T Tys = (
    (\<p>\<o>\<i>\<s>\<o>\<n> \<notin> set Tys \<longleftrightarrow> Inhabited T \<and> (\<exists>TY. \<forall>x v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> v \<in> Well_Type TY)) \<and>
    (\<forall>x c. c \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>vf. c = sem_mk_tup vf \<and> (\<p>\<o>\<i>\<s>\<o>\<n> \<notin> set Tys \<longrightarrow> list_all2 (\<lambda>t v. v \<in> Well_Type t) Tys vf)))
)\<close>

subsubsection \<open>\<open>\<t>\<y>\<p>\<e>\<o>\<f>\<close>\<close>

lemma semty_tup_eq_poison_rev[simp]: \<open>\<p>\<o>\<i>\<s>\<o>\<n> = sem_tup_T Ts \<longleftrightarrow> \<p>\<o>\<i>\<s>\<o>\<n> \<in> set Ts\<close>
  by (metis semty_tup_eq_poison)
  

lemma \<t>\<y>\<p>\<e>\<o>\<f>_tup:
  \<open> Tuple_Type_Helper U Tys
\<Longrightarrow> \<t>\<y>\<p>\<e>\<o>\<f> U \<equiv> sem_tup_T Tys  \<close>
  unfolding Tuple_Type_Helper_def SType_Of_def atomize_eq Semantic_Type_def
  apply auto
  apply (smt (verit) SType_Of_not_poison WT_tup mem_Collect_eq someI_ex)
  by (smt (verit) Eps_cong SType_Of_def SType_Of_not_poison WT_tup mem_Collect_eq)

lemma Tuple_Type_Helper_0:
  \<open> Tuple_Type_Helper \<lbrace> T \<rbrace> [\<t>\<y>\<p>\<e>\<o>\<f> T] \<close>
  unfolding Tuple_Type_Helper_def Inhabited_def
  apply auto
  apply (metis (no_types) SType_Of_not_poison Tuple_Field.expansion typing_inhabited)
  unfolding SType_Of_def Inhabited_def Satisfiable_def Semantic_Type_def
    apply (auto simp: split_ifs)
  subgoal for x P TY by (rule exI[where x=\<open>\<t>\<u>\<p> {TY}\<close>], auto)
  subgoal premises prems for x TY v
    apply (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>sem_mk_tup [v]\<close>]] prems(2),
            auto )
    subgoal premises prems2
      apply (insert prems2(1)[THEN semty_tup_uniq], clarsimp)
      subgoal for TTT
        by (rule exI[where x=\<open>hd TTT\<close>], insert prems, auto,
            metis list.sel(1) list_all2_Cons2 sem_mk_tup_inj) . .
  apply (smt (verit, best) SType_Of'_not_poison Satisfiable_I \<open>\<And>x v TY. \<lbrakk>\<forall>x v. (\<exists>xa. v = sem_mk_tup [xa] \<and> xa \<Turnstile> (x \<Ztypecolon> T)) \<longrightarrow> v \<in> Well_Type TY; v \<Turnstile> (x \<Ztypecolon> T)\<rbrakk> \<Longrightarrow> \<exists>TY. \<forall>x v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> v \<in> Well_Type TY\<close> some_eq_imp)
  by (smt (z3) someI2_ex)



lemma Tuple_Type_Helper_S:
  \<open> Tuple_Type_Helper Ts TYs
\<Longrightarrow> Tuple_Type_Helper (\<lbrace> T \<rbrace> \<^emph> Ts) (\<t>\<y>\<p>\<e>\<o>\<f> T # TYs)  \<close>
  unfolding Tuple_Type_Helper_def SType_Of_def Inhabited_def Satisfiable_def Semantic_Type_def
  
  apply (auto)
  apply (metis V_tup_sep_disj_L)
  subgoal premises prems for x TY p xa TYa pa xb TYb pb proof -
    obtain TXX where t1: \<open>TY = sem_tup_T TXX\<close>
      using prems(1) prems(3) prems(9) semty_tup_uniq by blast
    show ?thesis apply (rule exI[where x=\<open>sem_tup_T (TYa # TXX)\<close>]; auto)
      by (smt (verit, best) NO_MATCH_def V_tup_mult_cons WT_tup list_all2_Cons mem_Collect_eq prems(3) prems(5) t1)
  qed
  apply (smt (verit) Well_Type_poison someI zero_set_def zero_set_iff)
         apply (smt (verit, ccfv_threshold) NO_MATCH_def V_tup_mult_cons list.rel_inject(2) someI)

  subgoal premises prems for x TY p TYa a b xa l2 proof -
    obtain TH TXX where t1: \<open>TYa = sem_tup_T (TH # TXX)\<close>
      by (smt (z3) NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L WT_tup list_all2_Cons2 mem_Collect_eq prems(1) prems(4) prems(6) prems(8) sem_mk_tup_inj semty_tup_uniq)
    obtain xx vv where t2: \<open>vv \<Turnstile> (xx \<Ztypecolon> T) \<and> vv \<notin> Well_Type TH\<close>
      using prems(5) by blast
    show ?thesis
      apply (insert \<open>\<forall>a b v.  _\<close>[THEN spec[where x=xx], THEN spec[where x=b], THEN spec[where x=\<open>sem_mk_tup (vv # l2)\<close>]],
          auto)
      apply (metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L prems(7) t2)
      by (simp add: t1 t2)
  qed

  using V_tup_mult apply force
  apply (smt (verit, del_insts) Well_Type_poison ex_in_conv someI_ex)

  subgoal premises prems for x TY p a TYa b cb xa proof -
    obtain cb' where t1: \<open>cb = sem_mk_tup cb'\<close>
      using prems(1) prems(7) by presburger
    have t2: \<open>\<exists>ca cb. sem_mk_tup (xa # cb') = ca * cb \<and> cb \<Turnstile> (b \<Ztypecolon> Ts) \<and> (\<exists>x. ca = sem_mk_tup [x] \<and> x \<Turnstile> (a \<Ztypecolon> T)) \<and> ca ## cb\<close>
      by (metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L prems(7) prems(8) t1)
    from \<open>\<forall>a b v. _\<close>[THEN spec[where x=a], THEN spec[where x=b], THEN spec[where x=\<open>sem_mk_tup (xa # cb')\<close>], THEN mp, OF t2]
    have t3: \<open>sem_mk_tup (xa # cb') \<in> Well_Type TYa\<close> .
    from semty_tup_uniq[OF this]
    obtain TH TXX where t1: \<open>TYa = sem_tup_T (TH # TXX)\<close>
      by (smt (verit, del_insts) WT_tup list_all2_Cons2 mem_Collect_eq sem_dest_mk_tup t3)

    show ?thesis apply (rule exI[where x=\<open>sem_tup_T TXX\<close>]; auto)
      by (smt (z3) NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L WT_tup list_all2_Cons mem_Collect_eq prems(1) prems(6) prems(8) sem_dest_mk_tup t1)
  qed
  apply (metis V_tup_mult)

  subgoal premises prems for TY a b cb x proof -
    obtain cb' where t1: \<open>cb = sem_mk_tup cb'\<close>
      using prems(1) prems(6) by presburger
    obtain TTT where t2: \<open>TY = sem_tup_T TTT\<close>
      by (metis V_tup_mult V_tup_sep_disj_L prems(5) prems(6) prems(7) semty_tup_uniq t1)

    obtain x1 v1 where t3: \<open>v1 \<Turnstile> (x1 \<Ztypecolon> T ) \<and> v1 \<notin> Well_Type (hd TTT)\<close>
      using prems(4) by blast
    obtain x2 v2 where t4: \<open>sem_mk_tup v2 \<Turnstile> (x2 \<Ztypecolon> Ts) \<and> sem_mk_tup v2 \<notin> Well_Type (sem_tup_T (tl TTT))\<close>
      using prems(1) prems(3) by blast

    show ?thesis
      apply (insert \<open>\<forall>a b v. _\<close>[THEN spec[where x=a], THEN spec[where x=b], THEN spec[where x=\<open>sem_mk_tup (v1 # v2)\<close>]]; auto)
      apply (smt (z3) NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_R WT_tup \<open>\<And>thesis. (\<And>x2 v2. sem_mk_tup v2 \<Turnstile> (x2 \<Ztypecolon> Ts) \<and> sem_mk_tup v2 \<notin> Well_Type (sem_tup_T (tl TTT)) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> list.sel(3) list_all2_Cons2 mem_Collect_eq prems(5) prems(7) sem_mk_tup_inj t2)
      by (smt (verit, best) WT_tup list.sel(3) list_all2_Cons2 mem_Collect_eq sem_dest_mk_tup t2 t4)
  qed
  using V_tup_mult by blast 

simproc_setup \<t>\<y>\<p>\<e>\<o>\<f>_tup (\<open>\<t>\<y>\<p>\<e>\<o>\<f> (\<lbrace> T \<rbrace> \<^emph> U)\<close> | \<open>\<t>\<y>\<p>\<e>\<o>\<f> (\<lbrace> T \<rbrace>)\<close>) = \<open>
  fn _ => fn ctxt => fn ctm =>
    Drule.infer_instantiate ctxt [(("U",0), Thm.dest_arg ctm)] @{thm' \<t>\<y>\<p>\<e>\<o>\<f>_tup}
      |> REPEAT_DETERM (resolve_tac ctxt @{thms' Tuple_Type_Helper_0 Tuple_Type_Helper_S} 1)
      |> Seq.pull
      |> Option.map fst
\<close>

lemma
  \<open> P (\<t>\<y>\<p>\<e>\<o>\<f> \<lbrace> A \<rbrace>) = P (\<t>\<u>\<p> {\<t>\<y>\<p>\<e>\<o>\<f> A}) \<close>
  by simp

lemma 
  \<open> P (\<t>\<y>\<p>\<e>\<o>\<f> \<lbrace> A, B \<rbrace>) = P (\<t>\<u>\<p> {\<t>\<y>\<p>\<e>\<o>\<f> A, \<t>\<y>\<p>\<e>\<o>\<f> B}) \<close>
  by simp

lemma 
  \<open> P (\<t>\<y>\<p>\<e>\<o>\<f> \<lbrace> A, B, C \<rbrace>) = P (\<t>\<u>\<p> {\<t>\<y>\<p>\<e>\<o>\<f> A, \<t>\<y>\<p>\<e>\<o>\<f> B, \<t>\<y>\<p>\<e>\<o>\<f> C}) \<close>
  by simp

lemma 
  \<open> \<t>\<y>\<p>\<e>\<o>\<f> B = \<p>\<o>\<i>\<s>\<o>\<n>
\<Longrightarrow> P (\<t>\<y>\<p>\<e>\<o>\<f> \<lbrace> A, B, C \<rbrace>) = P \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by simp


subsubsection \<open>Reductions\<close>


lemma Empty_Tuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> Empty_Tuple \<^emph> \<lbrace> T \<rbrace>) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  \<open>((a,()) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> Empty_Tuple) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding BI_eq_iff
  by ((clarsimp; rule; clarsimp simp add: V_tup_mult),
      metis Cons_eq_append_conv V_tup_mult,
      (clarsimp; rule; clarsimp simp add: V_tup_mult),
      metis NO_MATCH_def V_tup_mult_cons)

lemma Tuple_Field_zeros [\<phi>reason %semantic_zero_val_cut]:
  \<open> Semantic_Zero_Val ty T x
\<Longrightarrow> Semantic_Zero_Val (sem_tup_T tys) Ts xs
\<Longrightarrow> Semantic_Zero_Val (sem_tup_T (ty#tys)) (\<lbrace> T \<rbrace> \<^emph> Ts) (x,xs) \<close>
  unfolding Semantic_Zero_Val_def
  by (clarsimp simp add: V_tup_mult_cons image_iff, insert V_tup_sep_disj_L, blast)

declare [[\<phi>trace_reasoning = 1]]

lemma Tuple_Field_semtys[\<phi>reason add]:
  \<open> Semantic_Type T TY
\<Longrightarrow> Semantic_Type Ts (sem_tup_T TYs)
\<Longrightarrow> Semantic_Type (\<lbrace> T \<rbrace> \<^emph> Ts) (sem_tup_T (TY#TYs))\<close>
  unfolding Semantic_Type_def subset_iff
  by (clarsimp, insert V_tup_mult, fastforce)

lemma [\<phi>reason %inhabited]:
  \<open> Inhabited T
\<Longrightarrow> Semantic_Type Ts (sem_tup_T TYs)
\<Longrightarrow> Inhabited Ts
\<Longrightarrow> Inhabited (\<lbrace> T \<rbrace> \<^emph> Ts) \<close>
  unfolding subset_iff Inhabited_def Satisfiable_def Semantic_Type_def
  apply clarsimp
  subgoal for x y p q
    by (rule exI[where x=x], rule exI[where x=y], rule exI[where x=\<open>sem_mk_tup [p]\<close>], rule exI[where x=q], clarsimp, blast) .


section \<open>Reasoning\<close>

text \<open>All the reasoning rules below are for semantic properties.
      All reasoning rules for transformations and SL are derived automatically\<close>

subsection \<open>Show validity of an index for a type\<close>

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> sem_tup_T (Ty # Tys) \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N 0) (sem_tup_T (Ty # Tys)) Ty \<close>
  unfolding is_valid_step_idx_of_def Premise_def
  by (simp add: valid_idx_step_tup idx_step_type_tup)

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> sem_tup_T (Ty # Tys) \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N i) (sem_tup_T Tys) RET
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N (Suc i)) (sem_tup_T (Ty # Tys)) RET \<close>
  unfolding is_valid_step_idx_of_def Premise_def
  by (simp add: valid_idx_step_tup idx_step_type_tup)

lemma [\<phi>reason %chk_sem_ele_idx - 5 except \<open>is_valid_step_idx_of (AgIdx_N 0) (sem_tup_T _) _\<close>
                                           \<open>is_valid_step_idx_of (AgIdx_N (Suc _)) (sem_tup_T _) _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<r>nat_to_suc_nat n n'
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N n') (sem_tup_T Tys) Ty
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N n) (sem_tup_T Tys) Ty \<close>
  unfolding \<r>nat_to_suc_nat_def \<r>Guard_def
  by simp


lemma [\<phi>reason %chk_sem_ele_idx - 10 except \<open>is_valid_step_idx_of (AgIdx_N 0) (sem_tup_T _) _\<close>
                                            \<open>is_valid_step_idx_of (AgIdx_N (Suc _)) (sem_tup_T _) _\<close>]:
  \<open> FAIL TEXT(\<open>Element index of tuple must be literal numbers but given\<close> n)
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N n) (sem_tup_T Tys) Ty \<close>
  unfolding FAIL_def
  by blast


subsection \<open>Aggregate Access\<close>

lemma idx_step_value_V_tup_suc:
  \<open>idx_step_value (AgIdx_N (Suc i)) (sem_mk_tup (va # vs)) = idx_step_value (AgIdx_N i) (sem_mk_tup vs)\<close>
  by (simp add: idx_step_value_tup)

lemma idx_step_mod_value_V_tup_suc:
  \<open>idx_step_mod_value (AgIdx_N (Suc i)) g (sem_mk_tup (va # vs)) = sem_mk_tup [va] * idx_step_mod_value (AgIdx_N i) g (sem_mk_tup vs)\<close>
  by (metis NO_MATCH_I V_tup_mult_cons idx_step_mod_value_tup list_update_code(3) nth_Cons_Suc)

lemma [\<phi>reason %aggregate_access-5 except \<open>\<phi>Aggregate_Getter (AgIdx_N 0 # _) _ _ _\<close>
                                          \<open>\<phi>Aggregate_Getter (AgIdx_N (Suc _) # _) _ _ _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<r>nat_to_suc_nat i i'
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i' # idx) \<lbrace> T \<rbrace> Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i # idx) \<lbrace> T \<rbrace> Y f\<close>
  unfolding \<r>nat_to_suc_nat_def \<r>Guard_def
  by simp

lemma [\<phi>reason %aggregate_access-5 except \<open>\<phi>Aggregate_Getter (AgIdx_N 0 # _) _ _ _\<close>
                                          \<open>\<phi>Aggregate_Getter (AgIdx_N (Suc _) # _) _ _ _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<r>nat_to_suc_nat i i'
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i' # idx) (\<lbrace> T \<rbrace> \<^emph> X) Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i # idx) (\<lbrace> T \<rbrace> \<^emph> X) Y f\<close>
  unfolding \<r>nat_to_suc_nat_def \<r>Guard_def
  by simp

lemma [\<phi>reason %aggregate_access-10 except \<open>\<phi>Aggregate_Getter (AgIdx_N 0 # _) _ _ _\<close>
                                           \<open>\<phi>Aggregate_Getter (AgIdx_N (Suc _) # _) _ _ _\<close>]:
  \<open> FAIL TEXT(\<open>Element index of tuple must be literal numbers but given\<close> i)
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i # idx) \<lbrace> T \<rbrace> Y f\<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason %aggregate_access-10 except \<open>\<phi>Aggregate_Getter (AgIdx_N 0 # _) _ _ _\<close>
                                           \<open>\<phi>Aggregate_Getter (AgIdx_N (Suc _) # _) _ _ _\<close>]:
  \<open> FAIL TEXT(\<open>Element index of tuple must be literal numbers but given\<close> i)
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i # idx) (\<lbrace> T \<rbrace> \<^emph> X) Y f\<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason %aggregate_access-5 except \<open>\<phi>Aggregate_Mapper (AgIdx_N 0 # _) _ _ _ _ _\<close>
                                          \<open>\<phi>Aggregate_Mapper (AgIdx_N (Suc _) # _) _ _ _ _ _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<r>nat_to_suc_nat i i'
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i' # idx) (\<lbrace> T \<rbrace> \<^emph> X) X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i  # idx) (\<lbrace> T \<rbrace> \<^emph> X) X' Y Y' f \<close>
  unfolding \<r>nat_to_suc_nat_def \<r>Guard_def
  by simp

lemma [\<phi>reason %aggregate_access-5 except \<open>\<phi>Aggregate_Mapper (AgIdx_N 0 # _) _ _ _ _ _\<close>
                                          \<open>\<phi>Aggregate_Mapper (AgIdx_N (Suc _) # _) _ _ _ _ _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<r>nat_to_suc_nat i i'
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i' # idx) \<lbrace> T \<rbrace> X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i  # idx) \<lbrace> T \<rbrace> X' Y Y' f \<close>
  unfolding \<r>nat_to_suc_nat_def \<r>Guard_def
  by simp

lemma [\<phi>reason %aggregate_access-10 except \<open>\<phi>Aggregate_Mapper (AgIdx_N 0 # _) _ _ _ _ _\<close>
                                           \<open>\<phi>Aggregate_Mapper (AgIdx_N (Suc _) # _) _ _ _ _ _\<close>]:
  \<open> FAIL TEXT(\<open>Element index of tuple must be literal numbers but given\<close> i)
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i # idx) \<lbrace> T \<rbrace> X' Y Y' f\<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason %aggregate_access-10 except \<open>\<phi>Aggregate_Mapper (AgIdx_N 0 # _) _ _ _ _ _\<close>
                                           \<open>\<phi>Aggregate_Mapper (AgIdx_N (Suc _) # _) _ _ _ _ _\<close>]:
  \<open> FAIL TEXT(\<open>Element index of tuple must be literal numbers but given\<close> i)
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i # idx) (\<lbrace> T \<rbrace> \<^emph> X) X' Y Y' f\<close>
  unfolding FAIL_def
  by blast




lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter (AgIdx_N i # idx) X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N (Suc i) # idx) (\<lbrace> T \<rbrace> \<^emph> X) Y (f o snd)\<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_value_V_tup_suc)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter idx X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N 0 # idx) \<lbrace> X \<rbrace> Y f \<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter idx X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N 0 # idx) (\<lbrace> X \<rbrace> \<^emph> R) Y (f o fst) \<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper (AgIdx_N i # idx) X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N (Suc i) # idx) (\<lbrace> T \<rbrace> \<^emph> X) (\<lbrace> T \<rbrace> \<^emph> X') Y Y' (apsnd o f) \<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_mod_value_V_tup_suc,
      metis V_tup_sep_disj_R idx_step_mod_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N 0 # idx) \<lbrace> X \<rbrace> \<lbrace> X' \<rbrace> Y Y' f \<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_mod_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N 0 # idx) (\<lbrace> X \<rbrace> \<^emph> R) (\<lbrace> X' \<rbrace> \<^emph> R) Y Y' (apfst o f) \<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_mod_value_tup,
      metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L)


lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Constructor_Synth (semantic_tuple_constructor N) (() \<Ztypecolon> \<circle>) (sem_tup_T []) (() \<Ztypecolon> \<lbrace> \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def
  by clarsimp

lemma [\<phi>reason %aggregate_access+20]:
  \<open> Semantic_Type' (x \<Ztypecolon> T) TY @tag \<A>ctr_arg (Inr N)
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth (semantic_tuple_constructor N) (x \<Ztypecolon> List_Item T) (sem_tup_T [TY]) (x \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def Semantic_Type'_def Action_Tag_def
  by (clarsimp; blast)

lemma [\<phi>reason %aggregate_access]:
  \<open> Semantic_Type' (x \<Ztypecolon> T) TY @tag \<A>ctr_arg (Inr N)
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth (semantic_tuple_constructor (Suc N))
        (xs \<Ztypecolon> Ts) (sem_tup_T Tys) (r \<Ztypecolon> Tr)
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth (semantic_tuple_constructor N)
        ((x,xs) \<Ztypecolon> List_Item T \<^emph> Ts) (sem_tup_T (TY # Tys)) ((x, r) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> Tr)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def Semantic_Type'_def Action_Tag_def
  by (clarsimp simp: V_tup_mult_cons times_list_def semantic_tuple_constructor_N_no_use)
     (metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L list.rel_intros(2) sem_dest_mk_tup)
      

lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Constructor (semantic_tuple_constructor N) [] (sem_tup_T []) (() \<Ztypecolon> \<lbrace> \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_tuple_constructor_def
  by clarsimp

lemma [\<phi>reason %aggregate_access+20]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T) @tag \<A>ctr_arg (Inr N)
\<Longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_tuple_constructor N) [v] (sem_tup_T [TY]) (x \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_tuple_constructor_def Action_Tag_def
            Semantic_Type'_def
  by (cases v; clarsimp; blast)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T) @tag \<A>ctr_arg (Inr N)
\<Longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_tuple_constructor (Suc N)) vR (sem_tup_T Tys) (r \<Ztypecolon> Tr)
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_tuple_constructor N) (v # vR) (sem_tup_T (TY # Tys)) ((x, r) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> Tr)\<close>
  unfolding \<phi>Aggregate_Constructor_def Semantic_Type'_def Action_Tag_def
  by (cases v; clarsimp simp: semantic_tuple_constructor_N_no_use;
      metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L)

setup \<open>Context.theory_map (
  Generic_Element_Access.Agg_Constructors.add 0 (fn (kind, args, (ctxt,sequent)) =>
    if kind = "" andalso forall (fn ((NONE,_),[_]) => true | _ => false) args
    then let val args' = map (fn (_,[rule]) => Phi_Local_Value.get_raw_val_in_rule rule) args
          in SOME (ctxt, \<^cterm>\<open>semantic_tuple_constructor 0\<close>, args')
         end
    else NONE
))\<close>

subsection \<open>Synthesis\<close>

\<phi>reasoner_group \<phi>synthesis_ag_T = (%\<phi>synthesis_ag, [%\<phi>synthesis_ag, %\<phi>synthesis_ag]) in \<phi>synthesis_ag
  \<open>for tuple\<close>

declare synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> T \<rbrace> \<^emph> U\<close> for T U,
         \<phi>reason %\<phi>synthesis_ag_T
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. ?x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> ?T \<rbrace> \<^emph> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @tag synthesis\<close>]

        synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> T \<rbrace>\<close> for T,
         \<phi>reason %\<phi>synthesis_ag_T
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. ?x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> ?T \<rbrace> \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @tag synthesis\<close>]

        synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> \<rbrace>\<close>,
         \<phi>reason %\<phi>synthesis_ag_T
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. () \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> \<rbrace> \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @tag synthesis\<close>]


hide_fact semantic_tuple_constructor_N_no_use

subsection \<open>Aux\<close>

lemma semty_tup_eq_poison_compute[simp]:
  \<open> \<t>\<u>\<p> {} \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  \<open> sem_tup_T (H#L) = \<p>\<o>\<i>\<s>\<o>\<n> \<longleftrightarrow> H = \<p>\<o>\<i>\<s>\<o>\<n> \<or> sem_tup_T L = \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by simp_all blast

declare semty_tup_eq_poison[simp del]

end