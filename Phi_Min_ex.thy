theory Phi_Min_ex
  imports Phi_Min "HOL-Library.Word"
begin

section \<open>Additional Stuffs\<close>

subsection \<open>Convert between Deep Model and Word Type\<close>

term unat

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