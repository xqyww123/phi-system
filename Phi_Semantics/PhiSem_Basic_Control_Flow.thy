chapter \<open>Basic Control Flow\<close>

theory PhiSem_Basic_Control_Flow
  imports PhiSem_Generic_Boolean
begin

section \<open>Instructions\<close>

paragraph \<open>Non-Branching Selection\<close>

definition op_sel :: "TY \<Rightarrow> (VAL \<times> VAL \<times> VAL, VAL) proc'"
  where "op_sel TY =
    \<phi>M_caseV (\<lambda>vc. \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV bool V_bool.dest vc (\<lambda>c.
    \<phi>M_getV TY id va (\<lambda>a.
    \<phi>M_getV TY id vb (\<lambda>b.
    Return (sem_value (if c then b else a)))))))"

paragraph \<open>Branch\<close>

definition op_if :: "'ret proc
                  \<Rightarrow> 'ret proc
                  \<Rightarrow> (VAL,'ret) proc'"
  where "op_if brT brF v =
    \<phi>M_getV bool V_bool.dest v (\<lambda>c. (if c then brT else brF))"

paragraph \<open>While Loop\<close>

inductive SemDoWhile :: "VAL proc \<Rightarrow> resource \<Rightarrow> unit state \<Rightarrow> bool" where
  "Success (sem_value (V_bool.mk False)) res \<in> f s \<Longrightarrow> SemDoWhile f s (Success (sem_value ()) res)"
| "Success (sem_value (V_bool.mk True)) res \<in> f s \<Longrightarrow> SemDoWhile f res s'' \<Longrightarrow> SemDoWhile f s s''"
| "Exception v e \<in> f s \<Longrightarrow> SemDoWhile f s (Exception v e)"
| "PartialCorrect \<in> f s \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "Invalid \<in> f s \<Longrightarrow> SemDoWhile f s Invalid"

lemma "\<nexists> y. SemDoWhile ((\<lambda>res. Return (sem_value (V_bool.mk True)) res) :: VAL proc) res y"
  apply rule apply (elim exE) subgoal for y
    apply (induct "((\<lambda>res. Return (sem_value (V_bool.mk True)) (res::resource)) :: VAL proc)" res y
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


paragraph \<open>Recursion\<close>

inductive SemRec :: "(('a,'a) proc' \<Rightarrow> ('a,'a) proc')
            \<Rightarrow> 'a sem_value \<Rightarrow> resource \<Rightarrow> 'a state set \<Rightarrow> bool"
where
  SemRec_I0: "(\<And>g. F g x res = y) \<Longrightarrow> SemRec F x res y"
| SemRec_IS: "SemRec (F o F) x res y \<Longrightarrow> SemRec F x res y"

definition op_recursion :: "TY list \<Rightarrow> TY list
                         \<Rightarrow> (('a,'a) proc' \<Rightarrow> ('a,'a) proc')
                         \<Rightarrow> ('a,'a) proc'"
  where "op_recursion _ _ F x s = (if (\<exists>t. SemRec F x s t) then The (SemRec F x s) else {})"

section \<open>Abstraction of Procedures\<close>

subsubsection \<open>Syntax for Annotations\<close>

consts Invariant :: \<open>bool \<Rightarrow> bool\<close> ("Inv: _" [37] 36)
consts Guard :: \<open>bool \<Rightarrow> bool\<close> ("Guard: _" [37] 36)

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
  \<open> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>T \<lbrace> X \<longmapsto> Y\<^sub>T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>)
\<Longrightarrow> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>F \<lbrace> X \<longmapsto> Y\<^sub>F \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>)
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T v) (Y\<^sub>F v) \<longmapsto> Y v \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if br\<^sub>T br\<^sub>F rawc \<lbrace> X\<heavy_comma> C \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawc] \<bool> \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. (E\<^sub>T e \<^bold>s\<^bold>u\<^bold>b\<^bold>j C) + (E\<^sub>F e \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> C) \<rbrace>\<close>
  unfolding op_if_def Premise_def Action_Tag_def
  apply (cases rawc; cases C; simp; rule; simp add: \<phi>expns WT_bool)
  using \<phi>CONSEQ view_shift_id by blast+

proc "if":
  assumes C: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c cond \<lbrace> X \<longmapsto> X1\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l C \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
      and brT: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brT \<lbrace> X1 \<longmapsto> Y\<^sub>T (ret::'a sem_value) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>\<close>
      and brF: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brF \<lbrace> X1 \<longmapsto> Y\<^sub>F (ret::'a sem_value) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>\<close>
      and [\<phi>reason 9999 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T ?v) (Y\<^sub>F ?v) \<longmapsto> ?Y \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
              \<open>(\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T v) (Y\<^sub>F v) \<longmapsto> Y v \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)\<close>
  argument \<open>X\<close>
  return \<open>Y (ret::'a sem_value)\<close>
  throws \<open>\<lambda>e. E e + (E\<^sub>T e \<^bold>s\<^bold>u\<^bold>b\<^bold>j C) + (E\<^sub>F e \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> C)\<close>
  \<medium_left_bracket> C branch brT brF \<medium_right_bracket>. .

subsection \<open>Loops\<close>

lemma "__DoWhile__rule_\<phi>app":
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> (\<exists>*x'. X x' \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l P x' \<Ztypecolon> \<bool>) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding op_do_while_def \<phi>Procedure_def
  apply (simp add: subset_iff LooseStateTy_expn')
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

lemma
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l P x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x'\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<and> \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<rbrace>"
  using "__DoWhile__rule_\<phi>app"[where X=\<open>\<lambda>x. X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j I x\<close> and P=P,
            simplified Subjection_times, simplified] .

proc (nodef) do_while:
assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x)\<close>
    and V: \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> cond x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA\<close>
assumes B: \<open>\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X' x \<longmapsto> (X' x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x') \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
argument \<open>X\<close>
return   \<open>X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> \<not> cond x'\<close>
throws E
  \<medium_left_bracket>
  V[unfolded Action_Tag_def]
  "__DoWhile__rule_\<phi>app"[where P=cond and X=\<open>\<lambda>x'. X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j invariant x'\<close>, simplified]
  \<medium_left_bracket> B \<medium_right_bracket>.
  \<medium_right_bracket> by simp .

proc while:
  assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x)\<close>
  assumes V[unfolded Action_Tag_def]:
           "\<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA"
    and C: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<lbrace> X x \<longmapsto> X x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace>"
    and B: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<lbrace> X x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace>"
  argument \<open>X'\<close>
  return \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> \<not> cond x\<close>
  \<medium_left_bracket> V C
    branch \<medium_left_bracket>
      do_while \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. Inv: invariant vars \<and> Guard: cond vars\<close>
      \<medium_left_bracket> B C \<medium_right_bracket>.
      \<medium_right_bracket>.
    \<medium_left_bracket> \<medium_right_bracket> for \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. invariant vars \<and> \<not> cond vars\<close> ..
  \<medium_right_bracket>. .

(*
We fail to infer the abstract loop guard automatically but require users to give.
The main problem is about nondeterminancy in higher-order unification.
In the below rule, in \<^term>\<open>cond x' \<Ztypecolon> \<bool>\<close>, both \<open>cond\<close> and \<open>x'\<close> are schematic variables,
which means we cannot determine either of them via unification.
Even though the abstract state \<open>x'\<close> may be determined possibly in the unification of \<open>X x'\<close>,
to infer \<open>cond x'\<close> it is still a problem especially when \<open>x'\<close> is not a variable but a composite
term and its composite expression may be shattered in the expression of \<open>cond\<close> after
rewrites and simplifications, causing it is very difficult to recover the actual abstract guard
\<open>cond\<close> from simplified composition \<open>cond x'\<close>.
*)

end