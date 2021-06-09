theory NuLLReps
  imports NuPrim  "HOL-Library.Word"
begin

instantiation unit :: register_collection begin
definition layout_unit :: "unit itself \<Rightarrow> layout" where
  layout_unit_def[simp]: "layout_unit _ = la_z"
instance by standard
end

instantiation register :: (llty) register_collection begin
definition register_unit :: "'a register itself \<Rightarrow> layout" where
  register_unit_def[simp]: "register_unit _ = la_z"
instance by standard
end

instantiation prod :: (llty,llty) llty begin
definition layout_prod :: "('a \<times> 'b) itself \<Rightarrow> layout" where
  layout_prod_def[simp]: "layout_prod _ = la_C (layout TYPE('a)) (layout TYPE('b))"
instance by standard
end

instantiation prod :: (register_collection,register_collection) register_collection
  begin instance by standard end

  \<comment> \<open> StateOn stack registers
    where stack :: llty and registers :: register_collection \<close>

instantiation state :: (llty) llty begin
definition layout_state :: "'a state itself \<Rightarrow> layout" where
  layout_state_def[simp]: "layout_state _ = la_z"
instance by standard
end

instantiation with_registers :: (llty,register_collection) llty begin
definition layout_with_registers :: "('a with 'r) itself \<Rightarrow> layout" where
  layout_with_registers_def[simp]: "layout_with_registers _ = layout (TYPE ('a))"
instance by standard
end

instantiation word :: (len) masharable_llty
begin
definition layout_word :: "'a word itself \<Rightarrow> layout" where
  layout_word_def[simp]: "layout_word _ = la_i LENGTH('a)"
definition share_word :: "'a word \<Rightarrow> zint \<Rightarrow> 'a word" where
  share_word_def: "share_word x z = x"
definition sharable_word :: "'a word \<Rightarrow> bool" where
  sharable_word_def: "sharable_word x = True"
definition revert_word :: "'a word \<times> 'a word \<Rightarrow> bool" where
  revert_word_def: "revert_word xy = True"
definition dpriv_word :: "'a word \<Rightarrow> 'a word" where
  depriv_word_def: "dpriv_word x = x"
instance by standard (auto simp add: share_word_def simp add: sharable_word_def
      simp add: revert_word_def simp add: depriv_word_def)
end

instantiation word :: (len) zero_llty
begin
definition lty_zero_word[simp]: "lty_zero_word = (0 :: 'a word)"
instance by standard
end

instantiation word :: (len) ceq_llty
begin
definition ceqable_word :: "'a word \<times> 'a word \<Rightarrow> bool" where
  ceqable_word_def[simp]: "ceqable_word x = True"
definition ceq_word :: "'a word \<times> 'a word \<Rightarrow> bool" where
  ceq_word_def: "ceq_word = (\<lambda>(x,y). (x = y))"
lemma ceq_word[simp]: "ceq (x,y) = (x = y)" for x :: "'a word"
   by (simp add: ceq_word_def)
instance by standard (auto+)
end

instantiation prod :: (zero_llty, zero_llty) zero_llty begin
definition lty_zero_prod :: "'a \<times> 'b" where
  lty_zero_prod_def[simp]: "lty_zero_prod = (lty_zero,lty_zero)"
instance by standard
end

(* declare [[show_hyps = true, show_types = true, show_sorts = true]] *)
instantiation prod :: (sharable_llty, sharable_llty) sharable_llty begin
fun revert_prod :: "('a \<times> 'b) \<times> ('a \<times> 'b) \<Rightarrow> bool" where
  "revert_prod (v1,v2) \<longleftrightarrow> (case v1 of (a1,b1) \<Rightarrow> case v2 of (a2,b2) \<Rightarrow> revert (a1,a2) \<and> revert (b1,b2))"
fun sharable_prod :: "'a \<times> 'b \<Rightarrow> bool" where
  "sharable_prod (a,b) \<longleftrightarrow> sharable a \<and> sharable b"
definition share_prod :: "'a \<times> 'b \<Rightarrow> zint \<Rightarrow> 'a \<times> 'b" where
  share_prod_def[simp]: "share_prod x z = (case x of (a,b) \<Rightarrow> (share a z, share b z))"
definition dpriv_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  dpriv_prod_def[simp]: "dpriv_prod x = (case x of (a,b) \<Rightarrow> (dpriv a, dpriv b))"
instance by standard (auto, (metis revert_sym revert_trans) +)
end

definition NuNat :: "('a::len) itself \<Rightarrow> ('a word, nat) nu" where
  NuNat_def: "NuNat _ = Nu (\<lambda>px. case px of (p,x) \<Rightarrow> (p = Word.of_nat x))"

lemma NuNat_abst_ex[abst_expn]: "p \<nuLinkL> NuNat b \<nuLinkR> x \<equiv> (p = Word.of_nat x)"
  by (auto simp add: NuNat_def simp add: abstraction_def)

end