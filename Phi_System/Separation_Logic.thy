theory Separation_Logic
  imports BI "Phi-Semantics-Framework.Phi_Semantics_Framework"
begin

section \<open>Specification Framework\<close>

type_synonym ('RES_N,'RES) assn = "('RES_N \<Rightarrow> 'RES) set" \<comment> \<open>assertion\<close>

subsection \<open>Specification for Returning States\<close>

context \<phi>resource_sem begin

definition StrictStateTy :: "('ret sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ex  sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ret,'ex,'RES_N,'RES) state set" ("!\<S>")
  where "!\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val | Exception val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"

definition LooseStateTy  :: "('ret sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ex  sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ret,'ex,'RES_N,'RES) state set" ("\<S>")
  where  "\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val | Exception val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma StrictStateTy_expn[iff]:
        "Success vs x \<in> !\<S> T E \<equiv> x \<in> T vs" "Exception v x \<in> !\<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> !\<S> T E)"  "\<not> (PartialCorrect \<in> !\<S> T E)"
  and LooseStateTy_expn[iff]:
        "Success vs x \<in> \<S> T E \<equiv> x \<in> T vs" "Exception v x \<in> \<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> \<S> T E)"  "(PartialCorrect \<in> \<S> T E)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)

lemma LooseStateTy_expn' :
    "x \<in> \<S> T E \<longleftrightarrow> x = PartialCorrect \<or> (\<exists>x' v. x = Success v x' \<and> x' \<in> T v) \<or> (\<exists>x' v. x = Exception v x' \<and> x' \<in> E v)"
  by (cases x) simp_all

lemma StrictStateTy_elim[elim]:
    "s \<in> !\<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Exception v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> C" by (cases s) auto

lemma StrictStateTy_intro[intro]:
    " x \<in> T v \<Longrightarrow> Success v x \<in> !\<S> T E"
    " x \<in> E v \<Longrightarrow> Exception v x \<in> !\<S> T E"
  by simp_all

lemma LooseStateTy_E[elim]:
    "s \<in> \<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Exception v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C)
\<Longrightarrow> C"
  by (cases s) auto

lemma LooseStateTy_I[intro]:
  "x \<in> T v \<Longrightarrow> Success v x \<in> \<S> T E"
  "x \<in> E v \<Longrightarrow> Exception v x \<in> \<S> T E"
  "PartialCorrect \<in> \<S> T E"
  by simp_all

lemma LooseStateTy_upgrade:
  "s \<in> \<S> T E \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E"
  by (cases s) auto

lemma StrictStateTy_degrade: "s \<in> !\<S> T E \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto

lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E) \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto

lemma StrictStateTy_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> !\<S> A E \<subseteq> !\<S> A' E'\<close>
  unfolding subset_iff StrictStateTy_def by simp
lemma StrictStateTy_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> !\<S> A E \<Longrightarrow> s \<in> !\<S> A' E'\<close>
  unfolding StrictStateTy_def by (cases s; simp)

lemma LooseStateTy_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> \<S> A E \<subseteq> \<S> A' E'\<close>
  unfolding subset_iff LooseStateTy_def by simp
lemma LooseStateTy_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> \<S> A E \<Longrightarrow> s \<in> \<S> A' E'\<close>
  unfolding LooseStateTy_def by (cases s; simp)


lemma LooseStateTy_plus[iff]:
(*  \<open>\<S> (A + B) E   = \<S> A E + \<S> B E\<close> *)
  \<open>\<S> X (\<lambda>v. EA v + EB v) = \<S> X EA + \<S> X EB\<close>
  unfolding set_eq_iff LooseStateTy_def by simp_all
lemma StrictStateTy_plus[iff]:
(*  \<open>!\<S> (A + B) E   = !\<S> A E  + !\<S> B E\<close> *)
  \<open>!\<S> X (\<lambda>v. EA v + EB v) = !\<S> X EA + !\<S> X EB\<close>
  unfolding set_eq_iff StrictStateTy_def by simp_all

end

abbreviation (in \<phi>fiction) \<open>Void \<equiv> (1::('FIC_N,'FIC) assn)\<close>


subsection \<open>Assertion\<close>

context \<phi>fiction begin
(* definition Fiction_Spec :: \<open>('FIC_N, 'FIC) assn \<Rightarrow> ('ret,'RES_N,'RES) proc \<Rightarrow> ('ret sem_value \<Rightarrow> ('FIC_N,'FIC) assn) \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> bool\<close>
  where \<open>Fiction_Spec P C Q E \<longleftrightarrow>
    (\<forall>com. com \<in> INTERP_SPEC P \<longrightarrow> C com \<in> \<S> (\<lambda>v. INTERP_SPEC (Q v)) (INTERP_SPEC E))\<close> *)

definition \<phi>Procedure :: "('ret,'ex,'RES_N,'RES) proc
                        \<Rightarrow> ('FIC_N,'FIC) assn
                        \<Rightarrow> ('ret sem_value \<Rightarrow> ('FIC_N,'FIC) assn)
                        \<Rightarrow> ('ex  sem_value \<Rightarrow> ('FIC_N,'FIC) assn)
                        \<Rightarrow> bool"
    ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _ \<rbrace>))" [101,2,2,2] 100)
  where "\<phi>Procedure f T U E \<longleftrightarrow>
    (\<forall>comp R. comp \<in> INTERP_SPEC (R * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_SPEC (R * U v)) (\<lambda>v. INTERP_SPEC (R * E v)))"

abbreviation \<phi>Procedure_no_exception ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<rbrace>))" [101,2,2] 100)
  where \<open>\<phi>Procedure_no_exception f T U \<equiv> \<phi>Procedure f T U 0\<close>

lemma \<phi>Procedure_alt:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<longmapsto> U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<longleftrightarrow> (\<forall>comp r. comp \<in> INTERP_SPEC ({r} * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_SPEC ({r} * U v)) (\<lambda>v. INTERP_SPEC ({r} * E v)))\<close>
  apply rule
   apply ((unfold \<phi>Procedure_def)[1], blast)
  unfolding \<phi>Procedure_def INTERP_SPEC subset_iff
  apply (clarsimp simp add: times_set_def)
  subgoal for comp R s r p
    apply (cases \<open>s\<close>; simp add: INTERP_SPEC_def)
    apply fastforce
    subgoal premises prems for e
      apply (insert prems(1)[THEN spec[where x=comp], THEN spec[where x=r], simplified prems, simplified])
      using prems(2) prems(3) prems(4) prems(5) prems(6) by blast
    subgoal premises prems
      apply (insert prems(1)[THEN spec[where x=comp], THEN spec[where x=r], simplified prems, simplified])
      using prems(2) prems(4) prems(5) prems(6) by blast . .

lemmas \<phi>Procedure_I = \<phi>Procedure_alt[THEN iffD2]


subsection \<open>View Shift\<close>

definition View_Shift
    :: "('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> bool \<Rightarrow> bool" ("(2\<^bold>v\<^bold>i\<^bold>e\<^bold>w _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
  where "View_Shift T U P \<longleftrightarrow> (\<forall>x R. x \<in> INTERP_SPEC (R * T) \<longrightarrow> x \<in> INTERP_SPEC (R * U) \<and> P)"

abbreviation Simple_View_Shift
    :: "('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> bool" ("(2\<^bold>v\<^bold>i\<^bold>e\<^bold>w _/ \<longmapsto> _)"  [13,13] 12)
  where \<open>Simple_View_Shift T U \<equiv> View_Shift T U True\<close>


lemma View_Shift_imply_P:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> (P1 \<longrightarrow> P2)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2\<close>
  unfolding View_Shift_def
  by blast


subsection \<open>Essential Hoare Rules\<close>

lemma \<phi>SKIP[simp,intro!]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c det_lift (Success v) \<lbrace> T v \<longmapsto> T \<rbrace>"
  unfolding \<phi>Procedure_def det_lift_def by clarsimp

lemma \<phi>SEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> (\<And>vs. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g vs \<lbrace> B vs \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<bind> g) \<lbrace> A \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding \<phi>Procedure_def bind_def apply (clarsimp simp add: subset_iff)
  subgoal for comp R x s
    apply (cases s; clarsimp; cases x; clarsimp; blast) . .

lemma \<phi>frame:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>ex. R * E ex \<rbrace>"
  unfolding \<phi>Procedure_def subset_iff
  apply clarify subgoal premises prems for comp R' s
    using prems(1)[THEN spec[where x=comp], THEN spec[where x=\<open>R' * R\<close>],
          simplified mult.assoc, THEN mp, OF prems(2)] prems(3) by blast .

lemma \<phi>frame0:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<rbrace>"
  using \<phi>frame[where E=0, simplified, folded zero_fun_def] .

lemma \<phi>frame_view:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R * A \<longmapsto> R * B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc)

lemma \<phi>frame_view_right:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A * R \<longmapsto> B * R \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc mult.commute)

lemma \<phi>view_refl:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X \<close>
  unfolding View_Shift_def by blast

lemma \<phi>view_trans:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2\<close>
  unfolding View_Shift_def by blast

lemma \<phi>view_shift_by_implication:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def Imply_def
  by (metis INTERP_SPEC set_mult_expn)

lemma \<phi>CONSEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A  \<longmapsto> B  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<rbrace>
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A' \<longmapsto> A \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1
\<Longrightarrow> (\<And>ret. \<^bold>v\<^bold>i\<^bold>e\<^bold>w B ret \<longmapsto> B' ret \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2)
\<Longrightarrow> (\<And>ex.  \<^bold>v\<^bold>i\<^bold>e\<^bold>w E ex  \<longmapsto> E' ex  \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any3)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A' \<longmapsto> B' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>"
  unfolding \<phi>Procedure_def View_Shift_def subset_iff
  apply clarsimp
  by (smt (verit, del_insts) LooseStateTy_expn')
  
end

parse_translation \<open> let
  val typ_tag = Const (\<^type_syntax>\<open>proc\<close>, dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
        $ Free ("'VAL", dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
  fun do_tag_E E = Const (\<^syntax_const>\<open>_constrain\<close>, dummyT) $ E $ typ_tag
  fun tag_E (E as Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free _ $ _) = do_tag_E E
    | tag_E (E as Const (\<^syntax_const>\<open>_constrain\<close>, _) $ _ $ _) = E
    | tag_E E = do_tag_E E
in [
  ("\<^const>local.\<phi>Procedure", (fn ctxt => fn [f,T,U,E] =>
    (Const("\<^const>local.\<phi>Procedure", dummyT) $ tag_E f $ T $ U $ E))),
  ("\<^const>local.\<phi>Procedure_no_exception", (fn ctxt => fn [f,T,U] =>
    (Const("\<^const>local.\<phi>Procedure_no_exception", dummyT) $ tag_E f $ T $ U)))
] end\<close>



end