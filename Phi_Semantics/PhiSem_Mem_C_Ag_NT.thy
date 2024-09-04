theory PhiSem_Mem_C_Ag_NT \<comment> \<open>Named Tuple\<close>
  imports PhiSem_Mem_C PhiSem_Aggregate_Named_Tuple
begin

section \<open>Named Tuple in Memory\<close>

subsection \<open>Semantics\<close>

debt_axiomatization
    Map_of_Val_ntup: \<open>Map_of_Val (sem_mk_ntup vs) =
      (\<lambda>path. case path of AgIdx_S s # path' \<Rightarrow>
                                if s |\<in>| fmdom vs then Map_of_Val (the (fmlookup vs s)) path'
                                                  else 1
                         | _ \<Rightarrow> 1)\<close>


subsection \<open>Syntax\<close>

syntax "\<phi>_shared_named_tuple_" :: \<open>logic \<Rightarrow> \<phi>_symbol_ \<Rightarrow> logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_ \<odiv> _: _")

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_shared_named_tuple_ n s X))" => "\<phi>_shared_named_tuple_ n s X"

setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 110 (
    fn ((ctxt,_), f, Const(\<^const_name>\<open>Named_Tuple_Field\<close>, _) $ s $ T) =>
        SOME (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, dummyT)
                $ (Const(\<^const_name>\<open>Cons\<close>, dummyT) $ (Const(\<^const_name>\<open>AgIdx_S\<close>, dummyT) $ s) $ Const(\<^const_name>\<open>Nil\<close>, dummyT))
                $ f (ctxt,0) T)
     | ((ctxt,_), f, Const(\<^syntax_const>\<open>\<phi>_shared_named_tuple_\<close>, _) $ sh $ s $ T) =>
        SOME (Const(\<^const_name>\<open>\<phi>Share\<close>, dummyT)
          $ sh
          $ (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, dummyT)
                $ (Const(\<^const_name>\<open>Cons\<close>, dummyT) $ (Const(\<^const_name>\<open>AgIdx_S\<close>, dummyT) $ s) $ Const(\<^const_name>\<open>Nil\<close>, dummyT))
                $ f (ctxt,0) T))
     | _ => NONE)

#>Phi_Mem_Printer.add 110 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>Phi_Types.\<phi>MapAt_L1\<close>, _)
          $ (Const(\<^const_syntax>\<open>AgIdx_S\<close>, _) $ s)
          $ T) =>
        SOME (Const(\<^const_syntax>\<open>Named_Tuple_Field\<close>, dummyT) $ s $ f ctxt T)
     | (ctxt, f, Const(\<^const_syntax>\<open>\<phi>Share\<close>, _) $ sh
        $ (Const(\<^const_syntax>\<open>Phi_Types.\<phi>MapAt_L1\<close>, _)
            $ (Const(\<^const_syntax>\<open>AgIdx_S\<close>, _) $ sym)
            $ T)) =>
          SOME (Const (\<^syntax_const>\<open>_\<phi>Tuple\<close>, dummyT) $
                  (Const (\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $ (
            Const(\<^syntax_const>\<open>\<phi>_shared_named_tuple_\<close>, dummyT) $ sh
                  $ (case sym of Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ id => Phi_Tool_Symbol.print id
                           | _ => sym)
                  $ f ctxt T)))
     | X_ => NONE
)
)\<close>

(* example
term \<open>a \<odiv> b\<close>
    
term \<open>\<m>\<e>\<m>[addr] \<lbrace> c \<odiv> a: T, dd \<odiv> b: \<lbrace> e: U \<rbrace>\<rbrace>\<close>
term \<open>\<m>\<e>\<m>[addr] \<lbrace> a: T, b: (U \<^emph> D)\<rbrace>\<close>
*)

subsection \<open>Reasoning\<close>

subsubsection \<open>Mem Coerce\<close>

text \<open>The following lemma cannot be automated because it is tightly related to the semantics\<close>

lemma Mem_Coerce_NTup:
  \<open> (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> SYMBOL_VAR(s): T \<rbrace>) = (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) \<close>
  apply (rule \<phi>Type_eqI_BI; unfold BI_eq_iff; clarsimp; rule; clarsimp)
  subgoal for x v
    by (rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val v\<close>],
        auto simp add: Map_of_Val_ntup fun_eq_iff push_map_cons_neq
             split: aggregate_index'.split list.split)
  subgoal for x v
    by (rule exI[where x=\<open>sem_mk_ntup (fmupd s v fmempty)\<close>],
        auto simp add: Map_of_Val_ntup fun_eq_iff push_map_cons_neq
             split: aggregate_index'.split list.split) .

lemma Mem_Coerce_NTup_Comb:
  \<open> Fx |\<inter>| Fy = {||}
\<Longrightarrow> Is_Named_Tuple T Fx
\<Longrightarrow> Is_Named_Tuple U Fy
\<Longrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (T \<^emph> U) = \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U \<close>
  apply (rule \<phi>Type_eqI_BI, unfold BI_eq_iff Is_Named_Tuple_def Premise_def;
      clarsimp; rule; clarsimp)

  subgoal premises prems for x y a b
    by (insert prems(2)[THEN spec, THEN spec, THEN mp, OF prems(5)]
               prems(3)[THEN spec, THEN spec, THEN mp, OF prems(4)],
        clarsimp simp: V_named_tup_mult Map_of_Val_ntup,
        rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val a\<close>],
        rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val b\<close>],
        insert prems(1,4-), auto simp: Map_of_Val_ntup
          fun_eq_iff times_fun sep_disj_fun_def split: list.split aggregate_index'.split,
        rule exI[where x=b], (auto simp: Map_of_Val_ntup)[1],
        rule exI[where x=a], (auto simp: Map_of_Val_ntup)[1])
  
  subgoal premises prems for x y a b
    apply (insert prems(2)[THEN spec, THEN spec, THEN mp, OF prems(6)]
                  prems(3)[THEN spec, THEN spec, THEN mp, OF prems(5)])
    apply (rule exI[where x=\<open>b * a\<close>])
    apply (insert prems(1,4-), auto simp: V_named_tup_mult Map_of_Val_ntup fmdom_notD
        fun_eq_iff times_fun sep_disj_fun_def split: list.split aggregate_index'.split)
    by (metis (no_types, lifting) V_named_tup_mult V_named_tup_sep_disj disjoint_iff_fnot_equal fmdom_notD one_option_def sep_disj_fmap.rep_eq sep_magma_1_left sep_magma_1_right) .


subsubsection \<open>ToA Mapper\<close>

lemma [\<phi>reason %mapToA_mem_coerce+10]:
  \<open> \<m>\<a>\<p> g : (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] U) \<OTast> R \<mapsto> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty fmempty)] \<lbrace> SYMBOL_VAR(s): U \<rbrace> \<OTast> R
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> SYMBOL_VAR(s): U' \<rbrace> \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>
  unfolding Mem_Coerce_NTup Guided_Mem_Coercion_def .


lemma [\<phi>reason %mapToA_mem_coerce]:
  \<open> \<m>\<a>\<p> g : (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] U\<^sub>1 \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup tys] U\<^sub>2) \<OTast> R
          \<mapsto> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U\<^sub>1' \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U\<^sub>2') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> Is_Named_Tuple U\<^sub>2  field\<^sub>2
\<Longrightarrow> Is_Named_Tuple U\<^sub>2' field\<^sub>2
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| field\<^sub>2

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty tys)] (\<lbrace> SYMBOL_VAR(s): U\<^sub>1 \<rbrace> \<^emph> U\<^sub>2) \<OTast> R
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (\<lbrace> SYMBOL_VAR(s): U\<^sub>1' \<rbrace> \<^emph> U\<^sub>2') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>

  unfolding Guided_Mem_Coercion_def Transformation_def Premise_def
  subgoal premises prems proof -
    have t1: \<open>{|s|} |\<inter>| field\<^sub>2 = {||}\<close>
      using prems(4) by blast
    show ?thesis
      by (unfold Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): U\<^sub>1 \<rbrace>\<close> and U=\<open>U\<^sub>2\<close>, OF t1 Is_Named_Tuple_sing prems(2)]
                 Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): U\<^sub>1' \<rbrace>\<close> and U=\<open>U\<^sub>2'\<close>, OF t1 Is_Named_Tuple_sing prems(3)]
                 Mem_Coerce_NTup,
          insert prems(1), this)
  qed .


lemma [\<phi>reason %mapToA_mem_coerce+10]:
  \<open> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) \<OTast> W
          \<mapsto> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> SYMBOL_VAR(s): T \<rbrace> \<OTast> W
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> SYMBOL_VAR(s): T' \<rbrace> \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>
  unfolding Mem_Coerce_NTup Guided_Mem_Coercion_def .

lemma [\<phi>reason %mapToA_mem_coerce+10]:
  \<open> \<m>\<a>\<p> g : (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U) \<OTast> R \<mapsto> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> SYMBOL_VAR(s): U \<rbrace> \<OTast> R \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> SYMBOL_VAR(s): U' \<rbrace> \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>
  unfolding Mem_Coerce_NTup Guided_Mem_Coercion_def .


lemma [\<phi>reason %mapToA_mem_coerce]:
  \<open> Is_Named_Tuple T\<^sub>2  field\<^sub>2
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| field\<^sub>2

\<Longrightarrow> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T\<^sub>1 \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T\<^sub>2) \<OTast> W
          \<mapsto> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T\<^sub>1' \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T\<^sub>2') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> \<d>\<o> Is_Named_Tuple T\<^sub>2' field\<^sub>2

\<Longrightarrow> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace> \<^emph> T\<^sub>2) \<OTast> W
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (\<lbrace> SYMBOL_VAR(s): T\<^sub>1' \<rbrace> \<^emph> T\<^sub>2') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>

  unfolding Guided_Mem_Coercion_def Transformation_def Premise_def Do_def
  subgoal premises prems proof -
    have t1: \<open>{|s|} |\<inter>| field\<^sub>2 = {||}\<close>
      using prems(2) by blast
    show ?thesis
      by (unfold Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace>\<close> and U=\<open>T\<^sub>2\<close>, OF t1 Is_Named_Tuple_sing prems(1)]
                 Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): T\<^sub>1' \<rbrace>\<close> and U=\<open>T\<^sub>2'\<close>, OF t1 Is_Named_Tuple_sing prems(4)]
                 Mem_Coerce_NTup,
          insert prems(3), this)
  qed .


lemma [\<phi>reason %mapToA_mem_coerce]:
  \<open> \<m>\<a>\<p> g : (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U\<^sub>1 \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U\<^sub>2) \<OTast> R
          \<mapsto> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U\<^sub>1' \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U\<^sub>2') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> Is_Named_Tuple U\<^sub>2  field\<^sub>2
\<Longrightarrow> Is_Named_Tuple U\<^sub>2' field\<^sub>2
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| field\<^sub>2

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (\<lbrace> SYMBOL_VAR(s): U\<^sub>1 \<rbrace> \<^emph> U\<^sub>2) \<OTast> R
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (\<lbrace> SYMBOL_VAR(s): U\<^sub>1' \<rbrace> \<^emph> U\<^sub>2') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W
          \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>

  unfolding Guided_Mem_Coercion_def Transformation_def Premise_def
  subgoal premises prems proof -
    have t1: \<open>{|s|} |\<inter>| field\<^sub>2 = {||}\<close>
      using prems(4) by blast
    show ?thesis
      by (unfold Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): U\<^sub>1 \<rbrace>\<close> and U=\<open>U\<^sub>2\<close>, OF t1 Is_Named_Tuple_sing prems(2)]
                 Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): U\<^sub>1' \<rbrace>\<close> and U=\<open>U\<^sub>2'\<close>, OF t1 Is_Named_Tuple_sing prems(3)]
                 Mem_Coerce_NTup,
          insert prems(1), this)
  qed .


subsubsection \<open>Transformation\<close>


lemma [\<phi>reason %ToA_mem_coerce+10,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce+10]:
  \<open> x \<Ztypecolon> AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty fmempty)] (\<lbrace> SYMBOL_VAR(s): T \<rbrace>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Mem_Coerce_NTup Guided_Mem_Coercion_def .


lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> Is_Named_Tuple T\<^sub>2 field\<^sub>2
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| field\<^sub>2
\<Longrightarrow> x \<Ztypecolon> AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T\<^sub>1 \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup tys] T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty tys)] (\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace> \<^emph> T\<^sub>2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def
  subgoal premises prems proof -
    have t1: \<open>{|s|} |\<inter>| field\<^sub>2 = {||}\<close>
      using Premise_D prems(2) by blast

    show ?thesis
      by (unfold Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace>\<close> and U=\<open>T\<^sub>2\<close>, OF t1 Is_Named_Tuple_sing prems(1)]
                 Mem_Coerce_NTup,
          insert prems(3), blast)
  qed .


lemma [\<phi>reason %ToA_mem_coerce+10,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce+10]:
  \<open> x \<Ztypecolon> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty fmempty)] (\<lbrace> SYMBOL_VAR(s): T \<rbrace>) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Mem_Coerce_NTup Guided_Mem_Coercion_def .


lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> Is_Named_Tuple T\<^sub>2 field\<^sub>2
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| field\<^sub>2
\<Longrightarrow> x \<Ztypecolon> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T\<^sub>1 \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup tys] T\<^sub>2) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty tys)] (\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace> \<^emph> T\<^sub>2) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def
  subgoal premises prems proof -
    have t1: \<open>{|s|} |\<inter>| field\<^sub>2 = {||}\<close>
      using Premise_D prems(2) by blast

    show ?thesis
      by (unfold Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace>\<close> and U=\<open>T\<^sub>2\<close>, OF t1 Is_Named_Tuple_sing prems(1)]
                 Mem_Coerce_NTup,
          insert prems(3), blast)
  qed .

lemma [\<phi>reason %ToA_mem_coerce+10,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce+10]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty fmempty)] (\<lbrace> SYMBOL_VAR(s): T \<rbrace>) \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def Mem_Coerce_NTup .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T\<^sub>1 \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup tys] T\<^sub>2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> Is_Named_Tuple T\<^sub>2 field\<^sub>2
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| field\<^sub>2
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty tys)] (\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace> \<^emph> T\<^sub>2) \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def
  subgoal premises prems proof -
    have t1: \<open>{|s|} |\<inter>| field\<^sub>2 = {||}\<close>
      using Premise_D prems(3) by blast

    show ?thesis
      by (unfold Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace>\<close> and U=\<open>T\<^sub>2\<close>, OF t1 Is_Named_Tuple_sing prems(2)]
                 Mem_Coerce_NTup,
          insert prems(1), blast)
  qed .

lemma [\<phi>reason %ToA_mem_coerce+10,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce+10]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T) \<OTast> W \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty fmempty)] (\<lbrace> SYMBOL_VAR(s): T \<rbrace>) \<OTast> W \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def Mem_Coerce_NTup .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (AgIdx_S s \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T\<^sub>1 \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup tys] T\<^sub>2) \<OTast> W \<w>\<i>\<t>\<h> P
\<Longrightarrow> Is_Named_Tuple T\<^sub>2 field\<^sub>2
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] s |\<notin>| field\<^sub>2
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[semty_ntup (fmupd s ty tys)] (\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace> \<^emph> T\<^sub>2) \<OTast> W \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def
  subgoal premises prems proof -
    have t1: \<open>{|s|} |\<inter>| field\<^sub>2 = {||}\<close>
      using Premise_D prems(3) by blast

    show ?thesis
      by (unfold Mem_Coerce_NTup_Comb[where T=\<open>\<lbrace> SYMBOL_VAR(s): T\<^sub>1 \<rbrace>\<close> and U=\<open>T\<^sub>2\<close>, OF t1 Is_Named_Tuple_sing prems(2)]
                 Mem_Coerce_NTup,
          insert prems(1), blast)
  qed .


subsubsection \<open>Generalized_Semantic_Type\<close>

lemma [\<phi>reason %\<A>sem_typ_mod_cut]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] f : (f\<^sub>2 ++\<^sub>f f\<^sub>1)
\<Longrightarrow> \<A>sem_typ_mod2 (\<^emph>) (semty_ntup f\<^sub>1) (semty_ntup f\<^sub>2) (semty_ntup f) \<close>
  unfolding \<A>sem_typ_mod2_def ..

(*
lemma [\<phi>reason %generalized_sematic_type_cut]:
  \<open> Generalized_Semantic_Type T TY
\<Longrightarrow> Generalized_Semantic_Type (AgIdx_S k \<^bold>\<rightarrow> T) (semty_ntup (fmupd k TY fmempty)) \<close>
  unfolding Generalized_Semantic_Type_def ..

lemma [\<phi>reason %generalized_sematic_type_cut+10]:
  \<open> Generalized_Semantic_Type T TY
\<Longrightarrow> Generalized_Semantic_Type (AgIdx_S k \<^bold>\<rightarrow>\<^sub># T) (semty_ntup (fmupd k TY fmempty)) \<close>
  unfolding Generalized_Semantic_Type_def ..

lemma [\<phi>reason %generalized_sematic_type_cut]:
  \<open> Generalized_Semantic_Type (L \<^bold>\<rightarrow>\<^sub>@ T) TY
\<Longrightarrow> Generalized_Semantic_Type ((AgIdx_S k # L) \<^bold>\<rightarrow>\<^sub>@ T) (semty_ntup (fmupd k TY fmempty)) \<close>
  unfolding Generalized_Semantic_Type_def ..

lemma [\<phi>reason %generalized_sematic_type_cut]:
  \<open> Generalized_Semantic_Type T TY
\<Longrightarrow> Generalized_Semantic_Type ([] \<^bold>\<rightarrow>\<^sub>@ T) TY \<close>
  unfolding Generalized_Semantic_Type_def ..

(* term \<open>\<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> a: A, b: B \<rbrace>)\<close> *)
*)

end