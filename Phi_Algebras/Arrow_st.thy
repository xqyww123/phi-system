theory Arrow_st
  imports Algebras
begin


datatype 'a arrow_st = Arrow_st (s: 'a) (t: 'a) (infix "\<BRarrow>" 60)

lemma split_arrow_All:
  \<open> All P \<longleftrightarrow> (\<forall>a b. P (a \<BRarrow> b)) \<close>
  by (metis arrow_st.collapse)

lemma split_arrow_Ex:
  \<open> Ex P \<longleftrightarrow> (\<exists>a b. P (a \<BRarrow> b)) \<close>
  by (metis arrow_st.collapse)

lemma split_arrow_all:
  \<open> Pure.all P \<equiv> (\<And>a b. PROP P (a \<BRarrow> b)) \<close>
proof
  fix a b :: 'a
  assume \<open>\<And>x. PROP P x\<close>
  then show \<open>PROP P (a \<BRarrow> b)\<close> .
next
  fix x :: \<open>'a arrow_st\<close>
  assume \<open>\<And>a b. PROP P (a \<BRarrow> b)\<close>
  from \<open>PROP P (s x \<BRarrow> t x)\<close> show \<open>PROP P x\<close> by simp
qed

instantiation arrow_st :: (type) partial_add_cancel begin

definition plus_arrow_st :: \<open>'a arrow_st \<Rightarrow> 'a arrow_st \<Rightarrow> 'a arrow_st\<close>
  where \<open>plus_arrow_st a b = (s a \<BRarrow> t b)\<close>

definition dom_of_add_arrow_st :: \<open>'a arrow_st \<Rightarrow> 'a arrow_st \<Rightarrow> bool\<close>
  where \<open>dom_of_add_arrow_st a b \<longleftrightarrow> t a = s b\<close>

lemma plus_arrow[iff]:
  \<open> (ss \<BRarrow> tt) + (tt \<BRarrow> uu) = (ss \<BRarrow> uu) \<close>
  unfolding plus_arrow_st_def
  by simp

lemma dom_of_add_arrow_st[iff]:
  \<open> (ss \<BRarrow> tt) ##\<^sub>+ (uu \<BRarrow> vv) \<longleftrightarrow> tt = uu \<close>
  unfolding dom_of_add_arrow_st_def
  by simp

instance by (standard, clarsimp simp: split_arrow_all)

end

instance arrow_st :: (type) partial_cancel_semigroup_add
  by (standard; clarsimp simp add: split_arrow_all)



hide_const (open) s t

end