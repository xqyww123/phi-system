chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

text \<open>The part includes some reasoning processes that can already be defined
  after the IDE-CP is ready.\<close>

theory IDE_CP_Reasoning2
  imports IDE_CP
begin

section \<open>Extracts Values\<close>

text \<open>The section includes several processes handling values used in different scenarios.\<close>

subsection \<open>Removing Values\<close>

text \<open>Given an assertion X, antecedent \<^term>\<open>Remove_Values X X'\<close>
  returns X' where all free value assertions \<^term>\<open>x \<Ztypecolon> Val raw T\<close> filtered out, where \<^term>\<open>raw\<close>
  contains at least one free variable of \<^typ>\<open>'a sem_value\<close>.

  It is typically used in exception. When a computation triggers an exception at state X,
    the state recorded in the exception is exactly X' where value assertions are filtered out.\<close>

definition \<open>Remove_Values' (remain::assn) (keep::assn) (check::assn) (ret::assn)
              \<longleftrightarrow> (keep = check \<longrightarrow> (remain * keep \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ret))\<close>

(* lemma [\<phi>reason for \<open>Remove_Values ?ex ?var_X ?Z\<close>]:
  \<open>Remove_Values ex X X\<close>
  unfolding Remove_Values_def using implies_refl . *)

lemma [\<phi>reason 1200 for \<open>Remove_Values (ExSet ?T) ?T'\<close>]:
  \<open>(\<And>c. Remove_Values (T c) (T' c))
\<Longrightarrow> Remove_Values (ExSet T) (ExSet T')\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200 for \<open>Remove_Values (?T \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P) ?T'\<close>]:
  \<open> Remove_Values T T'
\<Longrightarrow> Remove_Values (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Remove_Values (?R * ?X) ?Z\<close>]:
  \<open> Remove_Values R R'
\<Longrightarrow> Remove_Values'  R' X X Z
\<Longrightarrow> Remove_Values (R * X) Z\<close>
  unfolding Remove_Values_def Imply_def Remove_Values'_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1100 for \<open>Remove_Values ?R ?Z\<close>]:
  \<open> Remove_Values'  1 R R Z
\<Longrightarrow> Remove_Values R Z\<close>
  unfolding Remove_Values_def Remove_Values'_def Imply_def
  by simp

lemma [\<phi>reason 1200 for \<open>Remove_Values' ?R ?Y (SYNTHESIS ?X) ?Z\<close>]:
  \<open> Remove_Values' R Y X Z
\<Longrightarrow> Remove_Values' R Y (SYNTHESIS X) Z\<close>
  unfolding Remove_Values'_def Synthesis_def .

(* lemma [\<phi>reason 1200 for \<open>Remove_Values' ?R ?Y (FIX ?X) ?Z\<close>]:
  \<open> Remove_Values' R Y X Z
\<Longrightarrow> Remove_Values' R Y (FIX X) Z\<close>
  unfolding Remove_Values'_def Fix_def . *)

lemma [\<phi>reason 1100 for \<open>Remove_Values' 1 ?Y ?X ?Z\<close>]:
  \<open>Remove_Values' 1 Y X Y\<close>
  unfolding Remove_Values'_def Imply_def by simp

lemma Remove_Values'_accept_1[\<phi>reason 1110 for \<open>Remove_Values' 1 ?Y ?X ?Z\<close>]:
  \<open>Remove_Values' 1 Y X Y\<close>
  unfolding Remove_Values'_def Imply_def by simp

lemma Remove_Values'_accept[\<phi>reason 1100 for \<open>Remove_Values' ?R ?Y ?X ?Z\<close>]:
  \<open>Remove_Values' R Y X (R * Y)\<close>
  unfolding Remove_Values'_def Imply_def by simp

lemma Remove_Values'_reject_val:
  \<open>Remove_Values' R Y (x \<Ztypecolon> Val raw T) R\<close>
  unfolding Remove_Values'_def Imply_def by (simp add: \<phi>expns)

\<phi>reasoner_ML Remove_Values'_reject_val 1200
  (\<open>Remove_Values' ?R ?Y (?x \<Ztypecolon> Val ?raw ?T) ?Z\<close>) = \<open>
fn (ctxt, sequent) =>
  let
    val Const (\<^const_name>\<open>Remove_Values'\<close>, _) $ R $ _
          $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ raw $ _))
          $ _ = Thm.major_prem_of sequent
    fun has_free_val (Free (_, Type (\<^type_name>\<open>sem_value\<close>, [_]))) = true
      | has_free_val (A $ B) = has_free_val A orelse has_free_val B
      | has_free_val (Abs (_,_,X)) = has_free_val X
      | has_free_val _ = false
    val rule =
      if has_free_val raw
      then @{thm Remove_Values'_reject_val}
      else (case R of Const (\<^const_name>\<open>one_class.one\<close>, _) => @{thm Remove_Values'_accept_1}
                    | _ => @{thm Remove_Values'_accept})
  in
    Seq.single (ctxt, rule RS sequent)
  end
\<close>


subsection \<open>Extract a Value\<close>

definition \<open>Extract_a_Value (S_in::assn) S_out val_out \<longleftrightarrow> (S_in \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S_out \<^bold>a\<^bold>n\<^bold>d val_out)\<close>

text \<open>\<^prop>\<open>Extract_a_Value S_in S_out val_out\<close> removes the first (right-most) value from the
  input assertion \<open>S_in\<close> and gives the specification theorem of the removed value in \<open>val_out\<close>.

  The process is used during assigning a local value to a binding which
    enables user to access the value later.
  The specification theorem of the value is in form \<^prop>\<open>sem_value.dest raw_val \<in> (x \<Ztypecolon> T)\<close>.
  The binding is bound with this theorem which is used when later loading this value back
    to the state sequent when user is accessing the value.
\<close>

lemma [\<phi>reason 1200 for \<open>Extract_a_Value (?R \<heavy_comma> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?T) ?R ?V\<close>]:
  \<open>Extract_a_Value (R \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T) R (sem_value.dest v \<in> (x \<Ztypecolon> T))\<close>
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
  using \<phi>cast_P .

end