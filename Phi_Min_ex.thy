theory Phi_Min_ex
  imports Phi_Min "HOL-Library.Word"
begin

section \<open>Additional Stuffs\<close>

subsection \<open>Representations about Word\<close>

subsubsection \<open>Word is not Separable\<close>

instantiation word :: (len) nonsepable_semigroup begin
definition sep_disj_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> bool\<close>
  where [simp]: \<open>sep_disj_word _ _ = False\<close>
instance by (standard; simp)
end

subsubsection \<open>Natural Number Abstraction\<close>

paragraph \<open>Natural Number\<close>

definition \<phi>Nat_for_Word :: "('len::len word, nat) \<phi>" ("\<nat>\<^sup>w")
  where "\<nat>\<^sup>w = (\<lambda>x. {v. unat v = x})"

lemma \<phi>Nat_for_Word_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>\<^sup>w) \<longleftrightarrow> unat p = x" for p :: \<open>'len::len word\<close>
  unfolding \<phi>Type_def \<phi>Nat_for_Word_def by simp

lemma \<phi>Nat_for_Word_expn_elim[elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> \<nat>\<^sup>w :: 'len::len word set) \<Longrightarrow> (x < 2^(Big LENGTH('len)) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Big_def Inhabited_def by (clarsimp simp add: \<phi>expns)

lemma
  \<open>Inhabited (x \<Ztypecolon> \<nat>\<^sup>w :: 'len::len word set) \<longleftrightarrow> x < 2^LENGTH('len)\<close>
  unfolding Inhabited_def apply (clarsimp simp add: \<phi>expns)
  using of_nat_inverse unsigned_less by blast

subsubsection \<open>Conversions\<close>

lemma [
  \<phi>reason 1200 on \<open>?x \<Ztypecolon> \<nat>\<^sup>w \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> to_Identity\<close>,
  unfolded Action_Tag_def,
  \<phi>reason on \<open>?x \<Ztypecolon> \<nat>\<^sup>w \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> Identity \<^bold>a\<^bold>n\<^bold>d ?P\<close>
]:
  \<open>x \<Ztypecolon> \<nat>\<^sup>w \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s of_nat x \<Ztypecolon> Identity \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> to_Identity\<close>
  unfolding Action_Tag_def Imply_def by (simp add: \<phi>expns; fastforce)


lemma [simp]:
  \<open>m < 2 ^ (Big LENGTH('a::len)) \<Longrightarrow> (word_of_nat m :: 'a word) \<in> (m \<Ztypecolon> \<nat>\<^sup>w)\<close>
  unfolding Big_def apply (simp add: \<phi>expns)
  using of_nat_inverse by blast

lemma unat_word_of_nat[simp]:
  \<open>m < 2 ^ (Big LENGTH('a)) \<Longrightarrow> unat (word_of_nat m :: 'a::len word) = m\<close>
  unfolding Big_def using of_nat_inverse by blast

lemma unat_lt_2_exp_Big[simp]:
  \<open>unat (x::'a::len word) < 2 ^ Big (LENGTH('a))\<close>
  unfolding Big_def
  by simp 

subsubsection \<open>Conversion between Deep representation and Word\<close>

context \<phi>min_sem begin

definition V_int_to_word :: \<open>'VAL \<Rightarrow> 'len::len word\<close>
  where \<open>V_int_to_word v = of_nat (snd (V_int.dest v))\<close>

definition word_to_V_int :: \<open>'len::len word \<Rightarrow> 'VAL\<close>
  where \<open>word_to_V_int v = V_int.mk (LENGTH('len), unat v)\<close>

lemma word_to_V_int[simp]:
  \<open>word_to_V_int x = V_int.mk (LENGTH('len), unat x)\<close>
  for x :: \<open>'len::len word\<close>
  unfolding word_to_V_int_def ..

lemma V_int_to_word[simp]:
  \<open> LENGTH('len::len) = n
\<Longrightarrow> V_int_to_word (V_int.mk (n,x)) = of_nat x\<close>
  unfolding V_int_to_word_def by simp 

lemma word_to_V_int_V_int_to_word[simp]:
  \<open> v \<in> Well_Type (\<tau>Int LENGTH('len))
\<Longrightarrow> word_to_V_int (V_int_to_word v :: 'len::len word) = v\<close>
  unfolding word_to_V_int_def V_int_to_word_def by clarsimp

lemma V_int_to_word_word_to_V_int[simp]:
  \<open>V_int_to_word (word_to_V_int v) = v\<close>
  unfolding word_to_V_int_def V_int_to_word_def by clarsimp  

end

end