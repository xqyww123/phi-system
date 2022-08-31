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
  where "\<nat>\<^sup>w x = (if x < 2^LENGTH('len) then { of_nat x } else {})"

lemma \<phi>Nat_for_Word_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>\<^sup>w) \<longleftrightarrow> (p = of_nat x) \<and> x < 2^LENGTH('len)" for p :: \<open>'len::len word\<close>
  unfolding \<phi>Type_def \<phi>Nat_for_Word_def by simp

lemma \<phi>Nat_for_Word_expn_elim[elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> \<nat>\<^sup>w :: 'len::len word set) \<Longrightarrow> (x < 2^LENGTH('len) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns)

lemma
  \<open>Inhabited (x \<Ztypecolon> \<nat>\<^sup>w :: 'len::len word set) \<longleftrightarrow> x < 2^LENGTH('len)\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns)


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
  unfolding word_to_V_int_def V_int_to_word_def apply clarsimp
  using of_nat_inverse by blast

lemma V_int_to_word_word_to_V_int[simp]:
  \<open>V_int_to_word (word_to_V_int v) = v\<close>
  unfolding word_to_V_int_def V_int_to_word_def by clarsimp  

end

end