chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

text \<open>The part includes some reasoning processes that can already be defined
  after the IDE-CP is ready.\<close>

theory IDE_CP_Reasoning2
  imports IDE_CP_Applications1
begin

section \<open>Small Reasoning Processes\<close>

text \<open>The section includes several processes handling values used in different scenarios.\<close>

subsection \<open>Removing Values\<close>

text \<open>Given an assertion X, antecedent \<^term>\<open>Remove_Values X X'\<close>
  returns X' where all free value assertions \<^term>\<open>x \<Ztypecolon> Val raw T\<close> filtered out, where \<^term>\<open>raw\<close>
  contains at least one free variable of \<^typ>\<open>'a \<phi>arg\<close>.

  It is typically used in exception. When a computation triggers an exception at state X,
    the state recorded in the exception is exactly X' where value assertions are filtered out.\<close>

declare [[\<phi>reason_default_pattern \<open>Remove_Values ?X _\<close> \<Rightarrow> \<open>Remove_Values ?X _\<close> (100)]]

(* lemma [\<phi>reason for \<open>Remove_Values ?ex ?var_X ?Z\<close>]:
  \<open>Remove_Values ex X X\<close>
  unfolding Remove_Values_def using implies_refl . *)

lemma [\<phi>reason 1200]:
  \<open>(\<And>c. Remove_Values (T c) (T' c))
\<Longrightarrow> Remove_Values (ExSet T) (ExSet T')\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200]:
  \<open> Remove_Values T T'
\<Longrightarrow> Remove_Values (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> Remove_Values (A * B) (A' * B')
\<Longrightarrow> Remove_Values (A * \<blangle> B \<brangle>) (A' * \<blangle> B' \<brangle>)\<close>
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values \<blangle> A \<brangle> \<blangle> A' \<brangle>\<close>
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values R R'
\<Longrightarrow> Remove_Values (R * (x \<Ztypecolon> Val raw T)) R'\<close>
  unfolding Remove_Values_def Imply_def by (simp add: Val_expn Subjection_expn)

lemma [\<phi>reason 1200]:
  \<open>Remove_Values (x \<Ztypecolon> Val raw T) 1\<close>
  unfolding Remove_Values_def Imply_def by (simp add: Val_expn Subjection_expn)

lemma [\<phi>reason 1100]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values (A * B) (A' * B)\<close>
  unfolding Remove_Values_def Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1000]:
  \<open> Remove_Values A A\<close>
  unfolding Remove_Values_def
  by simp 

subsection \<open>Extract Elimination Rule\<close>

definition Extract_Elimination_Rule :: \<open>prop \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> prop\<close>
  where \<open>Extract_Elimination_Rule IN OUT_L OUT_R \<equiv> (PROP IN \<Longrightarrow> OUT_L \<Longrightarrow> OUT_R)\<close>

declare [[\<phi>reason_default_pattern \<open>PROP Extract_Elimination_Rule ?I ?L ?R\<close>
                                \<Rightarrow> \<open>PROP Extract_Elimination_Rule ?I ?L ?R\<close> (100) ]]

lemma Do_Extract_Elimination_Rule:
  \<open> PROP IN
\<Longrightarrow> PROP Extract_Elimination_Rule IN OUT_L OUT_R
\<Longrightarrow> OUT_L \<Longrightarrow> (OUT_R \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Extract_Elimination_Rule_def
proof -
  assume IN: \<open>PROP IN\<close>
    and  RL: \<open>PROP IN \<Longrightarrow> OUT_L \<Longrightarrow> OUT_R\<close>
    and  OL: \<open>OUT_L\<close>
    and  OR: \<open>OUT_R \<Longrightarrow> C\<close>
  from OR[OF RL[OF IN OL]] show \<open>C\<close> .
qed

lemma [\<phi>reason 1100]:
  \<open>PROP Extract_Elimination_Rule (Trueprop (X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y)) (Inhabited X) (Inhabited Y) \<close>
  unfolding Extract_Elimination_Rule_def Imply_def Inhabited_def by blast

lemma [\<phi>reason 1000]:
  \<open>PROP Extract_Elimination_Rule (Trueprop (X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P)) (Inhabited X) (Inhabited Y \<and> P) \<close>
  unfolding Extract_Elimination_Rule_def Imply_def Inhabited_def by blast


subsection \<open>Rewrite into \<phi>-Type\<close>

definition Rewrite_into_\<phi>Type :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where \<open>Rewrite_into_\<phi>Type IN OUT \<longleftrightarrow> IN = OUT\<close>

declare [[\<phi>reason_default_pattern \<open>Rewrite_into_\<phi>Type ?X _\<close> \<Rightarrow> \<open>Rewrite_into_\<phi>Type ?X _\<close> (100)]]

lemma [\<phi>reason 3000]:
  \<open>Rewrite_into_\<phi>Type (x \<Ztypecolon> T) (x \<Ztypecolon> T)\<close>
  unfolding Rewrite_into_\<phi>Type_def ..


(*
subsection \<open>Extract a Value\<close>

definition \<open>Extract_a_Value (S_in::assn) S_out val_out \<longleftrightarrow> (S_in \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S_out \<^bold>a\<^bold>n\<^bold>d val_out)\<close>

text \<open>\<^prop>\<open>Extract_a_Value S_in S_out val_out\<close> removes the first (right-most) value from the
  input assertion \<open>S_in\<close> and gives the specification theorem of the removed value in \<open>val_out\<close>.

  The process is used during assigning a local value to a binding which
    enables user to access the value later.
  The specification theorem of the value is in form \<^prop>\<open>\<phi>arg.dest raw_val \<in> (x \<Ztypecolon> T)\<close>.
  The binding is bound with this theorem which is used when later loading this value back
    to the state sequent when user is accessing the value.
\<close>

lemma [\<phi>reason 1200 for \<open>Extract_a_Value (?R \<heavy_comma> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?T) ?R ?V\<close>]:
  \<open>Extract_a_Value (R \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T) R (\<phi>arg.dest v \<in> (x \<Ztypecolon> T))\<close>
  unfolding Extract_a_Value_def Imply_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> Extract_a_Value R R' V
\<Longrightarrow> Extract_a_Value (R\<heavy_comma> X) (R'\<heavy_comma> X) V\<close>
  unfolding Extract_a_Value_def
  by (rule implies_right_prod)

lemma [\<phi>reason 1000]:
  \<open> ERROR TEXT(\<open>The assertion has no value.\<close>)
\<Longrightarrow> Extract_a_Value R R' V\<close>
  by blast

lemma apply_extract_a_value:
  \<open> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S
\<Longrightarrow> Extract_a_Value S S' V
\<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S') \<and> V\<close>
  unfolding Extract_a_Value_def
  using \<phi>apply_implication . *)

end