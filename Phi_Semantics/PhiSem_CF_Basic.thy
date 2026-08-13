chapter \<open>Basic Control Flow\<close>

theory PhiSem_CF_Basic
  imports PhiSem_Generic_Boolean "HOL-Library.While_Combinator"
begin

section \<open>Instructions\<close>

subsection \<open>Non-Branching Selection\<close>

definition op_sel :: "TY \<Rightarrow> (VAL \<times> VAL \<times> VAL, VAL) proc'"
  where "op_sel TY =
    \<phi>M_caseV (\<lambda>vc. \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV \<bool'> sem_dest_bool vc (\<lambda>c.
    \<phi>M_getV TY id va (\<lambda>a.
    \<phi>M_getV TY id vb (\<lambda>b.
    Return (\<phi>arg (if c then a else b)))))))"

subsection \<open>Branch\<close>

definition op_if :: "'ret proc
                  \<Rightarrow> 'ret proc
                  \<Rightarrow> (VAL,'ret) proc'"
  where "op_if brT brF v =
    \<phi>M_getV \<bool'> sem_dest_bool v (\<lambda>c. (if c then brT else brF))"

subsection \<open>While Loop\<close>

inductive SemDoWhile :: "VAL proc \<Rightarrow> resource \<Rightarrow> unit comp \<Rightarrow> bool" where
  "Success (\<phi>arg (sem_mk_bool False)) res \<in> f s \<Longrightarrow> SemDoWhile f s (Success (\<phi>arg ()) res)"
| "Success (\<phi>arg (sem_mk_bool True)) res \<in> f s \<Longrightarrow> SemDoWhile f res s'' \<Longrightarrow> SemDoWhile f s s''"
| "Abnormal v e \<in> f s \<Longrightarrow> SemDoWhile f s (Abnormal v e)"
| "NonTerm \<in> f s \<Longrightarrow> SemDoWhile f s NonTerm"
| "AssumptionBroken \<in> f s \<Longrightarrow> SemDoWhile f s AssumptionBroken"
| "Invalid \<in> f s \<Longrightarrow> SemDoWhile f s Invalid"

lemma "\<nexists> y. SemDoWhile ((\<lambda>res. Return (\<phi>arg (sem_mk_bool True)) res) :: VAL proc) res y"
  apply rule apply (elim exE) subgoal for y
    apply (induct "((\<lambda>res. Return (\<phi>arg (sem_mk_bool True)) (res::resource)) :: VAL proc)" res y
           rule: SemDoWhile.induct)
       apply (simp_all add: Return_def det_lift_def) . .

definition op_do_while :: " VAL proc \<Rightarrow> unit proc"
  where "op_do_while f s = Collect (SemDoWhile f s)"


subsection \<open>Recursion\<close>

inductive SemRec :: "(('a,'b) proc' \<Rightarrow> ('a,'b) proc')
            \<Rightarrow> 'a \<phi>arg \<Rightarrow> resource \<Rightarrow> 'b comp set \<Rightarrow> bool"
where
  SemRec_I0: "(\<And>g. F g x res = y) \<Longrightarrow> SemRec F x res y"
| SemRec_IS: "SemRec (F o F) x res y \<Longrightarrow> SemRec F x res y"

definition op_fix_point :: "(('a,'b) proc' \<Rightarrow> ('a,'b) proc')
                         \<Rightarrow> ('a,'b) proc'"
  where "op_fix_point F x s = (if (\<exists>t. SemRec F x s t) then The (SemRec F x s) else {})"

ML \<open>Synchronized.change Phi_Syntax.semantic_oprs (Symtab.update (\<^const_name>\<open>op_fix_point\<close>, 0))\<close>


subsubsection \<open>Simple Properties\<close>

lemma SemRec_IR: "SemRec F x r y \<Longrightarrow> SemRec (F o F) x r y"
  by (induct rule: SemRec.induct, rule SemRec_I0, simp)

lemma SemRec_deterministic:
  assumes "SemRec c s r s1" and "SemRec c s r s2" shows "s1 = s2"
proof -
  have "SemRec c s r s1 \<Longrightarrow> (\<forall>s2. SemRec c s r s2 \<longrightarrow> s1 = s2)"
    apply (induct rule: SemRec.induct)
     apply clarify
    subgoal for F a b y s2 apply (rotate_tac 1)
      apply (induct rule: SemRec.induct) by auto
    apply clarify apply (blast intro: SemRec_IR) done
  thus ?thesis using assms by simp
qed

lemma SemRec_deterministic2: " SemRec body s r x \<Longrightarrow> The (SemRec body s r) = x"
  using SemRec_deterministic by (metis theI_unique)



section \<open>Abstraction of Procedures\<close>

subsubsection \<open>Syntax for Annotations\<close>

consts Invariant :: \<open>bool \<Rightarrow> bool\<close> ("Inv: _" [100] 36)
consts Guard :: \<open>bool \<Rightarrow> bool\<close> ("Guard: _" [100] 36)
consts End   :: \<open>bool \<Rightarrow> bool\<close> ("End: _" [100] 36)
consts Transition :: \<open>'a \<Rightarrow> bool\<close> ("Transition: _" [100] 36)

subsection \<open>Branch-like\<close>

lemma sel_\<phi>app:
  \<open> Semantic_Type' (a \<Ztypecolon> A) TY
\<Longrightarrow> Semantic_Type' (b \<Ztypecolon> B) TY
\<Longrightarrow> \<proc> op_sel TY (\<phi>V_pair rawc (\<phi>V_pair rawa rawb)) \<lbrace>
        c \<Ztypecolon> \<val>[rawc] \<bool>\<heavy_comma> a \<Ztypecolon> \<val>[rawa] A\<heavy_comma> b \<Ztypecolon> \<val>[rawb] B
    \<longmapsto> (if c then a else b) \<Ztypecolon> \<val> (if c then A else B)
    \<rbrace>\<close>
  unfolding op_sel_def
  by ((cases rawc; cases rawb; cases rawa; cases c; simp add: Semantic_Type'_def subset_iff),
      rule, rule, rule, simp add: \<phi>expns WT_bool, blast, rule, simp add: \<phi>expns WT_bool, rule,
      simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns WT_bool, rule, rule, rule,
      simp add: \<phi>expns WT_bool, blast, rule, simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns WT_bool,
      rule, simp add: \<phi>expns WT_bool)

lemma branch_\<phi>app:
  \<open> (\<premise>   C \<longrightarrow> \<proc> br\<^sub>T \<lbrace> X \<longmapsto> Y\<^sub>T \<rbrace> \<throws> E\<^sub>T )
\<Longrightarrow> (\<premise> \<not> C \<longrightarrow> \<proc> br\<^sub>F \<lbrace> X \<longmapsto> Y\<^sub>F \<rbrace> \<throws> E\<^sub>F )
\<Longrightarrow> (\<And>v. If C (Y\<^sub>T v) (Y\<^sub>F v) \<transforms> Y v @tag invoke_br_join)
\<Longrightarrow> \<proc> op_if br\<^sub>T br\<^sub>F rawc \<lbrace> C \<Ztypecolon> \<val>[rawc] \<bool>\<heavy_comma> X \<longmapsto> Y \<rbrace> \<throws> (\<lambda>e. (E\<^sub>T e \<subj> C) + (E\<^sub>F e \<subj> \<not> C)) \<close>
  unfolding op_if_def Premise_def Action_Tag_def
  by (cases rawc; cases C; simp; rule; simp add: \<phi>expns WT_bool;
      insert \<phi>CONSEQ view_shift_by_implication view_shift_refl; blast)

proc "if":
  requires C: \<open>\<proc> cond \<lbrace> X \<longmapsto> \<val> C \<Ztypecolon> \<bool>\<heavy_comma> X1 \<rbrace> \<throws> E \<close>
      and brT: \<open>\<premise>   C \<longrightarrow> \<proc> brT \<lbrace> X1 \<longmapsto> Y\<^sub>T \<rbrace> \<throws> E\<^sub>T \<close>
      and brF: \<open>\<premise> \<not> C \<longrightarrow> \<proc> brF \<lbrace> X1 \<longmapsto> Y\<^sub>F \<rbrace> \<throws> E\<^sub>F \<close>
      and BC: \<open>(\<And>v. If C (Y\<^sub>T v) (Y\<^sub>F v) \<transforms> Y v @tag invoke_br_join)\<close>
  input  \<open>X\<close>
  output \<open>Y\<close>
  throws \<open>E + E\<^sub>T + E\<^sub>F\<close>
  \<medium_left_bracket> C branch brT brF BC \<medium_right_bracket> .

ML \<open>Synchronized.change Phi_Syntax.semantic_oprs (Symtab.update (\<^const_name>\<open>if\<close>, 3))\<close>



subsection \<open>Loops\<close>
 
lemma "__DoWhile__rule_\<phi>app":
  " \<proc> body \<lbrace> X x \<subj> x. P x \<longmapsto> (\<exists>*x'. \<val> P x' \<Ztypecolon> \<bool>\<heavy_comma> X x') \<rbrace> \<throws> E
\<Longrightarrow> \<proc> op_do_while body \<lbrace> X x \<subj> x. P x \<longmapsto> X x' \<subj> x'. \<not> P x' \<rbrace> \<throws> E "
  unfolding op_do_while_def \<phi>Procedure_def
  apply (simp add: less_eq_BI_iff LooseState_expn')
  apply (rule allI impI conjI)+
  subgoal for comp R s
  apply (rotate_tac 2)
    apply (induct body comp s rule: SemDoWhile.induct;
           clarsimp simp add: times_list_def INTERP_SPEC)
    apply fastforce
    subgoal premises prems for res f s s'' c u v proof -
      have t1: \<open>\<exists>uu. (\<exists>x. (\<exists>u v. uu = u * v \<and> u \<Turnstile> X x \<and> v \<Turnstile> R \<and> u ## v) \<and> P x) \<and> s \<Turnstile> INTERP_RES uu\<close>
        using prems(5) prems(6) prems(7) prems(8) prems(9) by blast
      show ?thesis
        by (insert \<open>\<forall>_ _. (\<exists>_. _) \<longrightarrow> _\<close>[THEN spec[where x=s], THEN spec[where x=R], THEN mp, OF t1]
                   prems(1) prems(3), fastforce)
    qed
    apply fastforce
    by blast .
  
proc (nodef) do_while:
  requires \<open>\<param> ( X' x \<subj> x. Inv: invariant x \<and> Guard: cond x)\<close>
       and V: \<open>\<r>CALL X \<transforms> ( X' x \<subj> x. invariant x \<and> cond x) \<with> Any\<close>
       and B: \<open>\<forall>x. \<premise> cond x \<longrightarrow> \<premise> invariant x
      \<longrightarrow> \<proc> body \<lbrace> X' x \<longmapsto> (\<val> cond x' \<Ztypecolon> \<bool>\<heavy_comma> X' x' \<subj> x'. invariant x') \<rbrace> \<throws> E \<close>
  input  \<open>X\<close>
  output \<open>X' x' \<subj> x'. invariant x' \<and> \<not> cond x'\<close>
  throws E
  \<medium_left_bracket>
    apply_rule V[unfolded Action_Tag_def]
    apply_rule "__DoWhile__rule_\<phi>app"[where P=cond and X=\<open>\<lambda>x'. X' x' \<subj> invariant x'\<close>, simplified]
    \<medium_left_bracket> B \<medium_right_bracket> !!
  \<medium_right_bracket> .

ML \<open>Synchronized.change Phi_Syntax.semantic_oprs (Symtab.update (\<^const_name>\<open>op_do_while\<close>, 2))\<close>

(*
We fail to infer the abstraction of the loop guard automatically but
require users to give by an annotation.
The main difficulty is about the nondeterminancy in higher-order unification.
In \<^term>\<open>cond x' \<Ztypecolon> \<bool>\<close> in the above rule, both \<open>cond\<close> and \<open>x'\<close> are schematic variables,
which means we cannot determine either of them via unification.
Even though the abstract state \<open>x'\<close> may be determined possibly in the unification of \<open>X x'\<close>,
to infer \<open>cond x'\<close> it is still a problem especially when \<open>x'\<close> is not a variable but a compounded
term and its expression may be shattered in and mixed up with the expression of \<open>cond\<close> after
simplifications like beta reduction,
causing it is very difficult to recover the actual abstract guard
\<open>cond\<close> from the reduced composition \<open>cond x'\<close>.
*)

proc while:
  requires \<open>\<param> ( X x \<subj> x. Inv: invariant x \<and> Guard: cond x)\<close>
    and V: "X' \<transforms> ((X x \<remains> R) \<subj> x. invariant x) \<with> Any"
    and C: "\<forall>x. \<premise> invariant x \<longrightarrow> \<proc> Cond \<lbrace> X x\<heavy_comma> R \<longmapsto> \<val> cond x' \<Ztypecolon> \<bool>\<heavy_comma> X x'\<heavy_comma> R \<subj> x'. invariant x' \<rbrace> \<throws> E1"
    and B: "\<forall>x. \<premise> invariant x \<longrightarrow> \<premise> cond x \<longrightarrow> \<proc> Body \<lbrace> X x\<heavy_comma> R \<longmapsto> X x'\<heavy_comma> R \<subj> x'. invariant x' \<rbrace> \<throws> E2"
  input  \<open>X'\<close>
  output \<open>X x\<heavy_comma> R \<subj> x. invariant x \<and> \<not> cond x\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> V C
    branch \<medium_left_bracket>
      do_while \<open>X vars\<heavy_comma> R \<subj> vars. Inv: invariant vars \<and> Guard: cond vars\<close>
      \<medium_left_bracket> B C \<medium_right_bracket>
    \<medium_right_bracket>
    \<medium_left_bracket> \<medium_right_bracket> for \<open>R\<heavy_comma> X vars \<subj> vars. invariant vars \<and> \<not> cond vars\<close> ;;
  \<medium_right_bracket> .

ML \<open>Synchronized.change Phi_Syntax.semantic_oprs (Symtab.update (\<^const_name>\<open>while\<close>, 3))\<close>

proc (nodef) refine_while
  [unfolded \<phi>Type_def[where T=\<open>X::'a \<Rightarrow> (FIC_N \<Rightarrow> FIC) BI\<close>]]:
  requires \<open>\<param> (X x \<subj> x. Inv: invariant x \<and> Guard: cond x \<and> Transition: f x)\<close>
    and V: "X' \<transforms> (X x \<remains> R) \<subj> invariant x \<with> Any"
    and C: "\<forall>x. \<premise> invariant x \<longrightarrow> \<proc> Cond \<lbrace> R\<heavy_comma> X x \<longmapsto> R\<heavy_comma> X x\<heavy_comma> \<val> cond x \<Ztypecolon> \<bool> \<rbrace> \<throws> E1"
    and B: "\<forall>x. \<premise> invariant x \<longrightarrow> \<premise> cond x \<longrightarrow> \<proc> Body \<lbrace> R\<heavy_comma> X x \<longmapsto> R\<heavy_comma> X x' \<subj> x'. x' = f x \<and> invariant x' \<rbrace> \<throws> E2"
  input \<open>X'\<close>
  output \<open>R\<heavy_comma> X x' \<subj> x'. x' = While_Combinator.while cond f x \<and> invariant x'\<close>
  throws \<open>E1 + E2\<close>
  apply (represent_BI_pred_in_\<phi>Type X)
  \<medium_left_bracket> V
    while \<open>x' \<Ztypecolon> X \<subj> x' i.
        Inv: (x' = (f ^^ i) x \<and> (\<forall>k < i. cond ((f ^^ k) x)) \<and> (\<forall>k \<le> i. invariant ((f ^^ k) x)) ) \<and>
        Guard: cond x'\<close>
    \<medium_left_bracket> C \<medium_right_bracket>
    \<medium_left_bracket> B \<medium_right_bracket> certified by (clarsimp, rule exI[where x=\<open>i+1\<close>],
                        auto simp add: less_Suc_eq_le \<phi>,
                        (insert le_eq_less_or_eq the_\<phi>(5) the_\<phi>(7), fastforce)[1],
                        metis funpow.simps(2) le_SucE o_apply the_\<phi>(6) the_\<phi>lemmata(3) the_\<phi>lemmata(4)) \<semicolon>

    have [\<phi>reason add]:
        \<open>\<And>y. \<premise> (f ^^ y) x = While_Combinator.while cond f x
      \<Longrightarrow> X ((f ^^ y) x) \<transforms> X (While_Combinator.while cond f x)\<close>
      by (simp add: Premise_def)

  \<medium_right_bracket> certified
    by (auto simp add: While_Combinator.while_def while_option_def \<phi>; auto_sledgehammer) .


subsection \<open>Recursion\<close>

lemma "__op_recursion_simp__":
  "(\<And>g x' v'. (\<And>x'' v''. \<proc> g v''  \<lbrace> X x'' v'' \<longmapsto> \<lambda>ret. Y x'' ret \<rbrace> \<throws> E x'')
                      \<Longrightarrow> \<proc> F g v' \<lbrace> X x' v'   \<longmapsto> \<lambda>ret. Y x'  ret \<rbrace> \<throws> E x' )
\<Longrightarrow> \<forall>x v. \<proc> op_fix_point F v \<lbrace> X x v \<longmapsto> \<lambda>ret. Y x ret \<rbrace> \<throws> E x"
  unfolding op_fix_point_def \<phi>Procedure_def atomize_all
  apply (clarsimp simp add: SemRec_deterministic2 less_eq_BI_iff del: subsetI)

  subgoal for x v comp a R w
    apply (rotate_tac 1) apply (induct rule: SemRec.induct)

    subgoal premises prems for F v res y
      using prems(4)[of \<open>\<lambda>_ _. {AssumptionBroken}\<close> x v, simplified, THEN spec[where x=res],
                     THEN spec[where x=R], THEN mp, OF prems(2), unfolded prems(1)] prems(3) by blast
    by (smt (z3) comp_apply) .

text \<open>Instead, we use a variant of the above rule which in addition annotates the names
  of the values.\<close>

lemma "__op_recursion__":
  "(\<And>g x' (v':: 'a \<phi>arg <named> 'names).
          P x'
      \<Longrightarrow> PROP Labelled label (Technical
          (\<And>x'' (v''::'a \<phi>arg <named> 'names).
              P x'' \<Longrightarrow>
              \<proc> g (case_named id v'') \<lbrace> case_named (X x'') v'' \<longmapsto> \<lambda>ret. Y x'' ret \<rbrace> \<throws> E x''))
      \<Longrightarrow> \<proc> F g (case_named id v') \<lbrace> case_named (X x') v'   \<longmapsto> \<lambda>ret. Y x'  ret \<rbrace> \<throws> E x' )
\<Longrightarrow> PROP Pure.prop (
      P x \<Longrightarrow>
      \<proc> op_fix_point F v \<lbrace> X x v \<longmapsto> \<lambda>ret. Y x ret \<rbrace> \<throws> E x
)"
  unfolding op_fix_point_def \<phi>Procedure_def atomize_all \<phi>arg_forall \<phi>arg_All Technical_def
            Pure.prop_def
  apply (clarsimp simp add: SemRec_deterministic2 less_eq_BI_iff del: subsetI)

  subgoal for comp a R w
    apply (rotate_tac 2) apply (induct rule: SemRec.induct)

    subgoal premises prems for F v res y
      using prems(4)[OF prems(5),
                     of \<open>\<lambda>_ _. {AssumptionBroken}\<close> v, simplified, THEN spec[where x=res],
                     THEN spec[where x=R], THEN mp, OF prems(2), unfolded prems(1)]
            prems(3) by blast
    by (smt (z3) comp_apply) .

ML_file \<open>library/basic_recursion.ML\<close>

attribute_setup recursive = \<open>Scan.repeat (Scan.lift Parse.term) >> (fn vars =>
    Phi_Modifier.wrap_to_attribute (fn (ctxt,sequent) =>
      case Phi_Toplevel.name_of_the_building_procedure ctxt
        of NONE => error "Name binding of the recursive procedure is mandatory."
         | SOME b => (
            let
             in if Binding.is_empty b
                then error "A recursive procedure cannot be anonymous."
                else if null vars then tracing "You may want to use syntax \<open>recursive vars\<close> to indicate \
                     \variables varying throught recursive calls." else ();
             PhiSem_Control_Flow.basic_recursive_mod Syntax.read_terms b vars (ctxt,sequent)
            end
           )
  ))\<close>


subsection \<open>Syntax\<close>

syntax "_while_" :: \<open>do_binds \<Rightarrow> do_binds \<Rightarrow> do_binds\<close>
                 ("((2\<while> {//(_))//(2} {//(_))//})" [11,11] 20)
       "_if_" :: \<open>do_binds \<Rightarrow> do_binds \<Rightarrow> do_binds \<Rightarrow> do_binds\<close>
                 ("((2\<if> {//(_))//(2} \<then'> {//(_))//(2} \<else> {//(_))//})" [11,11,11] 20)
       "_fix_point_" :: \<open>idt \<Rightarrow> idt \<Rightarrow> do_binds \<Rightarrow> do_bind\<close> ("((2\<fix> _ '(_') {//)(_)//})" [100,100,10] 20)

optional_translations (do_notation)

  "_while_ C B" <= "CONST PhiSem_CF_Basic.while C B"
  "_while_ C B" <= "_while_ (_do_block C) B"
  "_while_ C B" <= "_while_ C (_do_block B)"

  "_if_ C A B" <= "CONST PhiSem_CF_Basic.if TY C A B"
  "_if_ C A B" <= "_if_ (_do_block C) A B"
  "_if_ C A B" <= "_if_ C (_do_block A) B"
  "_if_ C A B" <= "_if_ C A (_do_block B)"

  "_fix_point_ f arg B" <= "CONST op_fix_point (\<lambda>f arg. B)"

end