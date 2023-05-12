theory Resource_Space_Inst_Tools
  imports Resource_Space
begin


quotient_type (overloaded) ('a,'b) sum1 (infixr "+\<^sub>1" 10) =
  \<open>('a::one) + ('b::one)\<close> / \<open>(\<lambda>x y. ((x = Inl 1 \<or> x = Inr 1) \<and> (y = Inl 1 \<or> y = Inr 1))\<or> x = y)\<close>
  by (rule equivpI; simp add: reflp_def symp_def transp_def split_sum_all)

instantiation sum1 :: (one, one) one begin
lift_definition one_sum1 :: "'a +\<^sub>1 'b" is "Inl 1" .
instance ..
end


instantiation sum1 :: (mult_1, mult_1) mult_1
begin

lift_definition times_sum1 :: "'a +\<^sub>1 'b \<Rightarrow> 'a +\<^sub>1 'b \<Rightarrow> 'a +\<^sub>1 'b"
  is "\<lambda>x y. case x of Inl x1 \<Rightarrow> (case y of Inl y1 \<Rightarrow> Inl (x1 * y1)
                                         | Inr y2 \<Rightarrow> (if y2 = 1 then Inl x1 else if x1 = 1 then Inr y2 else undefined))
                    | Inr x2 \<Rightarrow> (case y of Inl y1 \<Rightarrow> (if y1 = 1 then Inr x2 else if x2 = 1 then Inl y1 else undefined)
                                         | Inr y2 \<Rightarrow> Inr (x2 * y2))"
  by (clarsimp simp add: atomize_all atomize_imp split_sum_all)

instance by (standard; transfer; case_tac x; simp)
end

instantiation sum1 :: (sep_magma_1, sep_magma_1) sep_magma_1 begin

lift_definition sep_disj_sum1 :: "'a +\<^sub>1 'b \<Rightarrow> 'a +\<^sub>1 'b \<Rightarrow> bool"
  is "\<lambda>x y. case x of Inl x1 \<Rightarrow> (case y of Inl y1 \<Rightarrow> x1 ## y1
                                         | Inr y2 \<Rightarrow> (y2 = 1 \<or> x1 = 1))
                    | Inr x2 \<Rightarrow> (case y of Inl y1 \<Rightarrow> (y1 = 1 \<or> x2 = 1)
                                         | Inr y2 \<Rightarrow> x2 ## y2)"
  by (clarsimp simp add: atomize_all atomize_imp split_sum_all)

instance by (standard; transfer; case_tac x; simp)
end

instantiation sum1 :: (sep_monoid, sep_monoid) sep_monoid begin

instance apply standard
       apply (unfold join_sub_def; transfer; case_tac x; case_tac y; clarsimp simp add: split_sum_ex)
       apply (smt (z3) Inl_Inr_False join_positivity join_sub_def sum.inject(1))
  apply (case_tac \<open>b = 1\<close>; simp)
  apply (metis Inl_not_Inr old.sum.inject(1) sep_no_inverse)
         apply fastforce
  apply (case_tac \<open>b = 1\<close>; simp)
  apply (metis Inl_not_Inr old.sum.inject(1) sep_no_inverse)
        apply fastforce
  apply (case_tac \<open>ba = 1\<close>; simp)
  apply force
  apply (metis Inl_Inr_False join_positivity join_sub_def sum.inject(2))

  apply (transfer; case_tac x; case_tac y; case_tac z; clarsimp simp add: sep_mult_assoc; fastforce)

  apply (transfer; case_tac x; case_tac y; case_tac z; clarsimp simp add: sep_mult_assoc)
  using sep_disj_multD1 apply blast
  apply fastforce
  apply fastforce
  using sep_disj_multD1 apply blast
  apply (transfer; case_tac x; case_tac y; case_tac z; clarsimp simp add: sep_mult_assoc)
  using sep_disj_multI1 apply blast
  using sum.sel(2) apply fastforce
  apply (smt (verit, best) old.sum.simps(5) old.sum.simps(6) sep_magma_1_left)
  apply (smt (verit, best) old.sum.simps(5) old.sum.simps(6) sep_magma_1_left)
  using sum.sel(1) apply fastforce
  using sep_disj_multI1 apply blast

  apply (transfer; case_tac x; case_tac y; case_tac z; clarsimp simp add: sep_mult_assoc)
  using sep_disj_multD2 apply blast
  apply (smt (verit, best) old.sum.simps(6) sep_magma_1_right)
  apply (smt (verit, best) old.sum.simps(5) sep_magma_1_right)
  using sep_disj_multD2 apply blast

  apply (transfer; case_tac x; case_tac y; case_tac z; clarsimp simp add: sep_mult_assoc)
  using sep_disj_multI2 apply blast
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  using sep_disj_multI2 by blast
end

instantiation sum1 :: (sep_algebra, sep_algebra) sep_algebra begin
instance apply (standard; transfer; case_tac x; case_tac y; simp)
  using sep_disj_commuteI apply blast
  apply fastforce
  apply fastforce
  using sep_disj_commuteI apply blast
  using sep_mult_commute apply blast
  using sep_mult_commute by blast
end

setup \<open>Sign.mandatory_path "sum1"\<close>

lift_definition Inl :: "'a \<Rightarrow> 'a::one +\<^sub>1 'b::one" is \<open>Sum_Type.Inl\<close> .
lift_definition Inr :: "'b \<Rightarrow> 'a::one +\<^sub>1 'b::one" is \<open>Sum_Type.Inr\<close> .

lift_definition projl :: "'a::one +\<^sub>1 'b::one \<Rightarrow> 'a"
  is \<open>\<lambda>x. case x of Inl x1 \<Rightarrow> x1 | Inr x2 \<Rightarrow> 1\<close>
  by (case_tac sum1; case_tac sum2; simp; fastforce)

lift_definition projr :: "'a::one +\<^sub>1 'b::one \<Rightarrow> 'b"
  is \<open>\<lambda>x. case x of Inl x1 \<Rightarrow> 1 | Inr x2 \<Rightarrow> x2\<close>
  by (case_tac sum1; case_tac sum2; simp; fastforce)

lemma proj1[simp]:
  \<open>sum1.projl 1 = 1\<close>
  \<open>sum1.projr 1 = 1\<close>
  by (transfer; simp)+

lemma proj_In[simp]:
  \<open>sum1.projl (sum1.Inl x) = x\<close>
  \<open>sum1.projr (sum1.Inr x) = x\<close>
  by (transfer; simp)+

lemma In_1[simp]:
  \<open>sum1.Inl 1 = 1\<close>
  \<open>sum1.Inr 1 = 1\<close>
  by (transfer; simp)+

interpretation left: sep_inj_proj sum1.Inl sum1.projl
  apply (standard; transfer)
  apply (simp)
  apply (simp)
  apply (case_tac x; case_tac y; simp; meson)
    apply (case_tac a; case_tac b; simp; meson; simp)
    apply simp
apply simp
apply (case_tac a; case_tac b; simp; meson; simp)
  by blast

interpretation right: sep_inj_proj sum1.Inr sum1.projr
  apply (standard; transfer)
  apply (simp)
  apply (simp)
  apply (case_tac x; case_tac y; simp; meson)
    apply (case_tac a; case_tac b; simp; meson; simp)
    apply simp
apply simp
apply (case_tac a; case_tac b; simp; meson; simp)
  by blast

setup \<open>Sign.parent_path\<close>


end