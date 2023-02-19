chapter \<open>Basic Control Flow\<close>

theory PhiSem_CF_Basic
  imports PhiSem_Generic_Boolean
begin

section \<open>Instructions\<close>

subsection \<open>Non-Branching Selection\<close>

definition op_sel :: "TY \<Rightarrow> (VAL \<times> VAL \<times> VAL, VAL) proc'"
  where "op_sel TY =
    \<phi>M_caseV (\<lambda>vc. \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV bool V_bool.dest vc (\<lambda>c.
    \<phi>M_getV TY id va (\<lambda>a.
    \<phi>M_getV TY id vb (\<lambda>b.
    Return (\<phi>arg (if c then b else a)))))))"

subsection \<open>Branch\<close>

definition op_if :: "'ret proc
                  \<Rightarrow> 'ret proc
                  \<Rightarrow> (VAL,'ret::VALs) proc'"
  where "op_if brT brF v =
    \<phi>M_getV bool V_bool.dest v (\<lambda>c. (if c then brT else brF))"

subsection \<open>While Loop\<close>

inductive SemDoWhile :: "VAL proc \<Rightarrow> resource \<Rightarrow> unit state \<Rightarrow> bool" where
  "Success (\<phi>arg (V_bool.mk False)) res \<in> f s \<Longrightarrow> SemDoWhile f s (Success (\<phi>arg ()) res)"
| "Success (\<phi>arg (V_bool.mk True)) res \<in> f s \<Longrightarrow> SemDoWhile f res s'' \<Longrightarrow> SemDoWhile f s s''"
| "Abnormality v e \<in> f s \<Longrightarrow> SemDoWhile f s (Abnormality v e)"
| "NonTerm \<in> f s \<Longrightarrow> SemDoWhile f s NonTerm"
| "AssumptionBroken \<in> f s \<Longrightarrow> SemDoWhile f s AssumptionBroken"
| "Invalid \<in> f s \<Longrightarrow> SemDoWhile f s Invalid"

lemma "\<nexists> y. SemDoWhile ((\<lambda>res. Return (\<phi>arg (V_bool.mk True)) res) :: VAL proc) res y"
  apply rule apply (elim exE) subgoal for y
    apply (induct "((\<lambda>res. Return (\<phi>arg (V_bool.mk True)) (res::resource)) :: VAL proc)" res y
           rule: SemDoWhile.induct)
       apply (simp_all add: Return_def det_lift_def) . .

definition op_do_while :: " VAL proc \<Rightarrow> unit proc"
  where "op_do_while f s = Collect (SemDoWhile f s)"

(* lemma SemDoWhile_deterministic:
  assumes "SemDoWhile c s s1"
      and "SemDoWhile c s s2"
    shows "s1 = s2"
proof -
  have "SemDoWhile c s s1 \<Longrightarrow> (\<forall>s2. SemDoWhile c s s2 \<longrightarrow> s1 = s2)"
    apply (induct rule: SemDoWhile.induct)
    by (subst SemDoWhile.simps, simp)+
  thus ?thesis
    using assms by simp
qed

lemma SemDoWhile_deterministic2:
    "SemDoWhile body s x \<Longrightarrow> The ( SemDoWhile body s) = x"
  using SemDoWhile_deterministic by blast *)


subsection \<open>Recursion\<close>

inductive SemRec :: "(('a,'a) proc' \<Rightarrow> ('a,'a) proc')
            \<Rightarrow> 'a \<phi>arg \<Rightarrow> resource \<Rightarrow> 'a state set \<Rightarrow> bool"
where
  SemRec_I0: "(\<And>g. F g x res = y) \<Longrightarrow> SemRec F x res y"
| SemRec_IS: "SemRec (F o F) x res y \<Longrightarrow> SemRec F x res y"

definition op_fix_point :: "(('a,'a) proc' \<Rightarrow> ('a,'a) proc')
                         \<Rightarrow> ('a,'a) proc'"
  where "op_fix_point F x s = (if (\<exists>t. SemRec F x s t) then The (SemRec F x s) else {})"



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

subsection \<open>Branch-like\<close>

lemma op_sel_\<phi>app:
  \<open> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> B) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sel TY (\<phi>V_pair rawc (\<phi>V_pair rawb rawa)) \<lbrace>
        a \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawa] A\<heavy_comma> b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawb] B\<heavy_comma> c \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawc] \<bool>
    \<longmapsto> (if c then a else b) \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l (if c then A else B)
    \<rbrace>\<close>
  unfolding op_sel_def
  by (cases rawc; cases rawb; cases rawa; cases c; simp add: \<phi>SemType_def subset_iff,
      rule, rule, rule, simp add: \<phi>expns WT_bool, blast, rule, simp add: \<phi>expns WT_bool, rule,
      simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns WT_bool)

lemma branch_\<phi>app:
  \<open> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>T \<lbrace> X \<longmapsto> Y\<^sub>T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T )
\<Longrightarrow> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>F \<lbrace> X \<longmapsto> Y\<^sub>F \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F )
\<Longrightarrow> (\<And>v. If C (Y\<^sub>T v) (Y\<^sub>F v) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y v @action branch_convergence)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if br\<^sub>T br\<^sub>F rawc \<lbrace> X\<heavy_comma> C \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawc] \<bool> \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>e. (E\<^sub>T e \<^bold>s\<^bold>u\<^bold>b\<^bold>j C) + (E\<^sub>F e \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> C)) \<close>
  unfolding op_if_def Premise_def Action_Tag_def
  apply (cases rawc; cases C; simp; rule; simp add: \<phi>expns WT_bool)
  using \<phi>CONSEQ view_shift_by_implication view_shift_refl by blast+

proc "if":
  assumes C: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c cond \<lbrace> X \<longmapsto> X1\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l C \<Ztypecolon> \<bool> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
      and brT: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brT \<lbrace> X1 \<longmapsto> Y\<^sub>T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<close>
      and brF: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brF \<lbrace> X1 \<longmapsto> Y\<^sub>F \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<close>
      and BC: \<open>(\<And>v. If C (Y\<^sub>T v) (Y\<^sub>F v) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y v @action branch_convergence)\<close>
  input  \<open>X\<close>
  output \<open>Y\<close>
  throws \<open>E + E\<^sub>T + E\<^sub>F\<close>
  \<medium_left_bracket> C branch brT brF BC \<medium_right_bracket>. .


subsection \<open>Loops\<close>

lemma "__DoWhile__rule_\<phi>app":
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> (\<exists>*x'. X x' \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l P x' \<Ztypecolon> \<bool>) \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. \<not> P x' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E "
  unfolding op_do_while_def \<phi>Procedure_def
  apply (simp add: subset_iff LooseStateSpec_expn')
  apply (rule allI impI conjI)+
  subgoal for comp R s
  apply (rotate_tac 2)
    apply (induct body comp s rule: SemDoWhile.induct; clarsimp simp add: \<phi>expns times_list_def)
    apply fastforce
    subgoal premises prems for res f s s'' c u v proof -
      have t1: \<open>\<exists>c. (\<exists>fic. (\<exists>u v. fic = u * v \<and> u \<in> R \<and> v \<in> X c \<and> u ## v) \<and> s \<in> INTERP_RES fic) \<and> P c\<close>
        using prems(5) prems(6) prems(7) prems(8) prems(9) by blast
      show ?thesis
        apply (insert \<open>\<forall>_ _. (\<exists>_. _) \<longrightarrow> _\<close>[THEN spec[where x=s], THEN spec[where x=R], THEN mp, OF t1])
        using prems(1) prems(3) by fastforce
    qed
    apply fastforce
    by blast .

proc (nodef) do_while:
assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x)\<close>
    and V: \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> cond x) \<^bold>a\<^bold>n\<^bold>d Any @action ToSA\<close>
assumes B: \<open>\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X' x \<longmapsto> (X' x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x') \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
input  \<open>X\<close>
output \<open>X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> \<not> cond x'\<close>
throws E
  \<medium_left_bracket>
    V[unfolded Action_Tag_def]
    "__DoWhile__rule_\<phi>app"[where P=cond and X=\<open>\<lambda>x'. X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j invariant x'\<close>, simplified]
  \<medium_left_bracket> B \<medium_right_bracket>.
  \<medium_right_bracket> by simp .

proc while:
  assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x)\<close>
  assumes V[unfolded Action_Tag_def]:
           "X' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x) \<^bold>a\<^bold>n\<^bold>d Any @action ToSA"
    and C: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<lbrace> X x \<longmapsto> X x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1"
    and B: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<lbrace> X x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2"
  input  \<open>X'\<close>
  output \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> \<not> cond x\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> V C
    branch \<medium_left_bracket>
      do_while \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. Inv: invariant vars \<and> Guard: cond vars\<close>
      \<medium_left_bracket> B C \<medium_right_bracket>.
      \<medium_right_bracket>.
    \<medium_left_bracket> \<medium_right_bracket> for \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. invariant vars \<and> \<not> cond vars\<close> ..
  \<medium_right_bracket> .. .

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


subsection \<open>Recursion\<close>

lemma "__op_recursion_simp__":
  "(\<And>g x' v'. (\<And>x'' v''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g v''  \<lbrace> X x'' v'' \<longmapsto> \<lambda>ret. Y x'' ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x'')
                      \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g v' \<lbrace> X x' v'   \<longmapsto> \<lambda>ret. Y x'  ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x' )
\<Longrightarrow> \<forall>x v. \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_fix_point F v \<lbrace> X x v \<longmapsto> \<lambda>ret. Y x ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x"
  unfolding op_fix_point_def \<phi>Procedure_def atomize_all
  apply (clarsimp simp add: SemRec_deterministic2 del: subsetI)
  
  subgoal for x v comp a R
    apply (rotate_tac 1) apply (induct rule: SemRec.induct) 
    
    subgoal premises prems for F v res y
      using prems(3)[of \<open>\<lambda>_ _. {AssumptionBroken}\<close> x v, simplified, THEN spec[where x=res],
                     THEN spec[where x=R], THEN mp, OF prems(2), unfolded prems(1)] .
    by simp .

text \<open>Instead, we use a variant of the above rule which in addition annotates the names
  of the values.\<close>

lemma "__op_recursion__":
  "(\<And>g x' (v':: 'a::VALs \<phi>arg <named> 'names).
          P x'
      \<Longrightarrow> PROP Labelled label (HIDDEN_PREM
          (\<And>x'' (v''::'a \<phi>arg <named> 'names).
              P x'' \<Longrightarrow>
              \<^bold>p\<^bold>r\<^bold>o\<^bold>c g (case_named id v'') \<lbrace> case_named (X x'') v'' \<longmapsto> \<lambda>ret. Y x'' ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x''))
      \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g (case_named id v') \<lbrace> case_named (X x') v'   \<longmapsto> \<lambda>ret. Y x'  ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x' )
\<Longrightarrow> PROP Pure.prop (
      P x \<Longrightarrow>
      \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_fix_point F v \<lbrace> X x v \<longmapsto> \<lambda>ret. Y x ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x
)"
  unfolding op_fix_point_def \<phi>Procedure_def atomize_all \<phi>arg_forall \<phi>arg_All HIDDEN_PREM_def
            Pure.prop_def
  apply (clarsimp simp add: SemRec_deterministic2 del: subsetI)

  subgoal for comp a R
    apply (rotate_tac 2) apply (induct rule: SemRec.induct) 

    subgoal premises prems for F v res y
      using prems(3)[OF prems(4),
                     of \<open>\<lambda>_ _. {AssumptionBroken}\<close> v, simplified, THEN spec[where x=res],
                     THEN spec[where x=R], THEN mp, OF prems(2), unfolded prems(1)] .
    by simp .


ML_file \<open>library/basic_recursion.ML\<close>

attribute_setup recursive = \<open>Scan.repeat (Scan.lift Parse.term) >> (fn vars =>
    Phi_Modifier.wrap_to_attribute (fn (ctxt,sequent) =>
      case Phi_Toplevel.name_of_the_building_procedure ctxt
        of NONE => error "Name binding of the recursive procedure is mandatory."
         | SOME b => (
            if Binding.is_empty b
            then error "Name binding of the recursive procedure is mandatory."
            else if null vars then tracing "You may want to use syntax \<open>recursive vars\<close> to indicate \
                 \which variables are varied between the recursive callings." else ();
            PhiSem_Control_Flow.basic_recursive_mod Syntax.read_terms b vars (ctxt,sequent)
           )
  ))\<close>

end