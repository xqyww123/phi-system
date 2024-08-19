theory Phi_Fictions
  imports Phi_Types
begin



subsection \<open>Instances\<close>

subsubsection \<open>Itself\<close>

lemma Itself_refinement_projection:
  \<open> S \<le> S'
\<Longrightarrow> refinement_projection Itself S \<le> S' * top\<close>
  unfolding refinement_projection_def
  by (clarsimp simp add: less_eq_BI_iff) blast

lemma Itself_refinement:
  \<open>((u,v) \<Ztypecolon> Itself) * BI_Id_on top \<r>\<e>\<f>\<i>\<n>\<e>\<s> (u,v) \<Ztypecolon> Itself \<w>.\<r>.\<t> Itself \<i>\<n> (u \<Ztypecolon> Itself)\<close>
  for u :: \<open>'a::{sep_cancel,sep_semigroup}\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff,
      metis sep_cancel sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)


subsubsection \<open>Composition\<close>


lemma sep_refinement_stepwise:
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> Ia \<i>\<n> D
\<Longrightarrow> S2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> Ib \<i>\<n> D'
\<Longrightarrow> refinement_projection Ib D' \<le> D
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (Ia \<Zcomp> Ib) \<i>\<n> D'\<close>
  for Ia :: \<open>('a::sep_magma_1, 'b::sep_magma_1) \<phi>\<close>
  unfolding Fictional_Forward_Simulation_def refinement_projection_def
  apply (auto simp add: subset_iff Image_def Bex_def less_eq_BI_iff set_mult_expn split_option_all)
  subgoal premises prems for x r R t u v xb
  proof -
    thm prems
    thm prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>]]
    have \<open>\<exists>w'. (w', t) \<Turnstile> S1 \<and> (\<exists>u v. w' = u * v \<and> u \<Turnstile> Ia (xb * 1) \<and> v \<Turnstile> R \<and> u ## v) \<and> xb ## 1 \<and> xb \<Turnstile> D\<close>
      using prems(10) prems(3) prems(4) prems(5) prems(6) prems(7) prems(8) prems(9) by fastforce
    note prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y u'' v''
      proof -
        have \<open>\<exists>w'. (w', y) \<Turnstile> S2 \<and> (\<exists>u v. w' = u * v \<and> u \<Turnstile> Ib (x * r) \<and> v \<Turnstile> Itself 1 \<and> u ## v) \<and> x ## r \<and> x \<Turnstile> D'\<close>
          by (simp, rule exI[where x=xb], simp add: prems2 prems)
        note prems(2)[THEN spec[where x=x],THEN spec[where x=r],THEN spec[where x=\<open>Itself 1\<close>], THEN spec[where x=y],
                THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(3) prems2(4) prems2(5) by auto
      qed .
  qed .

lemma sep_refinement_stepwise':
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> Ia \<i>\<n> D
\<Longrightarrow> S2' \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> Ib \<i>\<n> D'
\<Longrightarrow> refinement_projection Ib D' \<le> D
\<Longrightarrow> S2 \<le> S2'
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (Ia \<Zcomp> Ib) \<i>\<n> D'\<close>
  for Ia :: \<open>'b::sep_magma_1 \<Rightarrow> 'a::sep_magma_1 BI\<close>
  using refinement_sub_fun sep_refinement_stepwise
  by metis

lemma refinement_projections_stepwise:
  \<open>refinement_projection (Ia \<Zcomp> Ib) D \<le> refinement_projection Ia (refinement_projection Ib D)\<close>
  for Ia :: \<open>('c::sep_magma_1, 'a::sep_monoid) \<phi>\<close>
  unfolding refinement_projection_def
  apply (clarsimp simp add: Bex_def less_eq_BI_iff set_mult_expn)
  subgoal for x x' u v
    by (metis mult_1_class.mult_1_right sep_magma_1_left) .

lemma refinement_projections_stepwise_UNIV_paired:
  \<open> refinement_projection Ia Da \<le> Dc * top
\<Longrightarrow> refinement_projection Ib Db \<le> Da * top
\<Longrightarrow> refinement_projection (Ia \<Zcomp> Ib) Db \<le> Dc * top \<close>
  for Ia :: \<open>('c::sep_magma_1, 'a::sep_monoid) \<phi>\<close>
  using refinement_projections_stepwise
  by (metis (no_types, opaque_lifting) order.trans refinement_projection_UNIV_times_D refinement_projection_mono)


subsubsection \<open>Function, pointwise\<close>

definition [simp]: "\<F>_finite_product I f = prod (\<lambda>x. I x (f x)) (dom1 f)"

lemma \<F>_finite_product_split:
  " finite (dom1 f)
\<Longrightarrow> (\<And>k. homo_one (I k))
\<Longrightarrow> \<F>_finite_product I f = I k (f k) * \<F>_finite_product I (f(k:=1))
   \<and> \<F>_finite_product I (f(k:=1)) ## I k (f k)"
  for I :: \<open>'a \<Rightarrow> 'b::sep_algebra \<Rightarrow> 'c::sep_algebra BI\<close>
  by (simp add: homo_one_def,
      smt (verit, best) dom1_upd fun_upd_triv mult.comm_neutral mult.commute prod.insert_remove)



(*
definition "\<F>_fun I = \<F>_fun' (\<lambda>_. I)"

lemma \<F>_fun_\<I>[simp]: "\<I> (\<F>_fun I) = (\<lambda>f. prod (\<I> I o f) (dom1 f))"
  unfolding \<F>_fun_def by simp

lemma \<F>_fun_split:
  " finite (dom1 f)
\<Longrightarrow> \<I> (\<F>_fun I) f = \<I> (\<F>_fun I) (f(k:=1)) * \<I> I (f k)
  \<and> \<I> (\<F>_fun I) (f(k:=1)) ## \<I> I (f k)"
  for f :: "'a \<Rightarrow> 'b::sep_algebra"
  unfolding \<F>_fun_def using \<F>_fun'_split .

lemma \<F>_interp_fun_\<I>_1_fupdt[simp]: "\<I> (\<F>_fun I) (1(k:=v)) = \<I> I v" by simp
*)
(*
definition "\<F>_pointwise I = Interp (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"

lemma \<F>_pointwise_\<I>[simp]:
  "\<I> (\<F>_pointwise I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"
  unfolding \<F>_pointwise_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fun_def fun_eq_iff)

lemma \<F>_pointwise_Itself:
  \<open>\<F>_pointwise Itself = Itself\<close>
  by (rule interp_eq_I; simp add: fun_eq_iff set_eq_iff) *)

definition [simp]: "\<F>_pointwise I f = BI {g. \<forall>x. g x \<Turnstile> (I x) (f x)}"

lemma \<F>_pointwise_homo_one[simp, locale_intro]:
  \<open> (\<And>k. homo_one (I k))
\<Longrightarrow> homo_one (\<F>_pointwise I)\<close>
  unfolding homo_one_def by (simp add: BI_eq_iff) fastforce

lemma \<F>_pointwise_Itself:
  \<open>\<F>_pointwise (\<lambda>_. Itself) = Itself\<close>
  by (simp add: fun_eq_iff BI_eq_iff)

lemma \<F>_pointwise_projection:
  \<open> refinement_projection (I k) D' \<le> D * top
\<Longrightarrow> refinement_projection (\<F>_pointwise I) (fun_upd 1 k `\<^sub>I D') \<le> fun_upd 1 k `\<^sub>I D * top\<close>
  for D :: \<open>'b::sep_monoid BI\<close>
  apply (clarsimp simp add: less_eq_BI_iff Bex_def image_iff set_mult_expn times_fun
            refinement_projection_def)
  subgoal premises prems for t u xb
  proof -
    have t1: \<open>xb ## u k\<close>
      by (metis fun_upd_same prems(3) sep_disj_fun)
    have \<open>\<exists>m. (\<exists>w'. m = I k w' \<and> (\<exists>u v. w' = u * v \<and> u \<Turnstile> D' \<and> u ## v)) \<and> t k \<Turnstile> m\<close>
      by (metis prems(2) prems(4) t1)
    note prems(1)[THEN spec[where x=\<open>t k\<close>], THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for u' v'
        by (rule exI[where x=\<open>1(k := u')\<close>], rule exI[where x=\<open>t(k := v')\<close>],
            simp add: fun_eq_iff prems2 sep_disj_fun_def times_fun) .
  qed .

lemma \<F>_pointwise_refinement:
  \<open> A * BI_Id_on top \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I k \<i>\<n> D
\<Longrightarrow> pairself (fun_upd 1 k) `\<^sub>I A * BI_Id_on top \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) `\<^sub>I B
    \<w>.\<r>.\<t> \<F>_pointwise I \<i>\<n> fun_upd 1 k `\<^sub>I D\<close>
  for I :: \<open>'c \<Rightarrow> 'b::sep_magma_1 \<Rightarrow> 'a::sep_magma_1 BI\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn image_iff Image_def less_eq_BI_iff Bex_def times_fun Id_on_iff)
  subgoal premises prems for r R xc u v xb a b
  proof -
    have t1[simp]: \<open>a ## xc k\<close>
      by (metis fun_upd_same prems(8) sep_disj_fun)
    have t2[simp]: \<open>b ## xc k\<close>
      by (metis fun_upd_same prems(9) sep_disj_fun)
    have \<open>\<exists>w'. (\<exists>a ba aa. w' = a * aa \<and> b * xc k = ba * aa \<and> (a, ba) \<Turnstile> A \<and> a ## aa \<and> ba ## aa) \<and>
      (\<exists>u va. w' = u * va \<and> u \<Turnstile> I k (xb * r k) \<and> va \<Turnstile> Itself (v k) \<and> u ## va) \<and> xb ## r k \<and> xb \<Turnstile> D\<close>
      by (auto simp add: prems,
          smt (verit, ccfv_threshold) fun_upd_same prems(10) prems(2) prems(3) prems(5) prems(7) sep_disj_fun_def t1 t2 times_fun_def)
    note prems(1)[THEN spec[where x=xb], THEN spec[where x=\<open>r k\<close>], THEN spec[where x=\<open>Itself (v k)\<close>, THEN spec[where x=\<open>b * xc k\<close>]],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y v'
      proof -
        have t4: \<open>u(k := v') ## v\<close>
          by (clarsimp simp add: sep_disj_fun_def prems2 prems(7)) (simp add: prems(7))
        have t3: \<open>1(k := b) * xc = u(k := v') * v\<close>
          by (clarsimp simp add: fun_eq_iff times_fun prems2,
              metis (mono_tags, opaque_lifting) fun_upd_apply mult_1_class.mult_1_left prems(3) times_fun_def)
        show ?thesis
          by (rule exI[where x=\<open>1(k := y)\<close>]; simp add: prems prems2; rule,
              smt (verit, ccfv_threshold) fun_split_1 fun_upd_other fun_upd_same prems(5) prems(6) prems2(4) t3 t4 times_fun_def,
              metis fun_sep_disj_1_fupdt(2) fun_upd_triv prems2(1) prems2(2))
              
      qed .
  qed .

(* subsubsection \<open>Pairwise\<close>

definition "\<F>_pair I1 I2 = (\<lambda>(x,y). I1 x * I2 y) "

lemma \<F>_pair[simp]: "\<F>_pair I1 I2 (x,y) = I1 x * I2 y"
  for I1 :: "('a::one,'b::sep_monoid) interp"
  unfolding \<F>_pair_def by (simp add: one_prod_def)

notation \<F>_pair (infixl "\<bullet>\<^sub>\<F>" 50)


subsubsection \<open>Option\<close>

definition "\<F>_option I = Interp (case_option 1 I)"

lemma \<F>_option_\<I>[simp]: "\<I> (\<F>_option I) = (case_option 1 I)"
  unfolding \<F>_option_def
  by (rule Interp_inverse) (simp add: Interpretation_def)


definition "\<F>_optionwise I = Interp (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"

lemma \<F>_optionwise_\<I>[simp]:
  "\<I> (\<F>_optionwise I) = (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"
  unfolding \<F>_optionwise_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def)
*)

(* subsubsection \<open>Partiality\<close>

definition "fine I = Interp (case_fine (\<I> I) {})"
lemma fine_\<I>[simp]: "\<I> (fine I) = case_fine (\<I> I) {}"
  unfolding fine_def by (rule Interp_inverse) (simp add: Interpretation_def one_fine_def)

definition "defined I = Interp (\<lambda>x. Fine ` \<I> I x)"
lemma defined_\<I>[simp]: "\<I> (defined I) = (\<lambda>x. Fine ` \<I> I x)"
  unfolding defined_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fine_def)

definition "partialwise I = \<F>_fine (defined I)"
lemma partialwise_\<I>[simp]: "\<I> (partialwise I) (Fine x) = { Fine y |y. y \<in> \<I> I x }"
  unfolding partialwise_def by auto
*)

subsubsection \<open>Functional Fiction\<close>

definition [simp]: \<open>\<F>_functional \<psi> D x = BI {y. x = \<psi> y \<and> y \<in> D }\<close>

(* lemma (in kernel_is_1) \<F>_functional_\<I>[simp]:
  \<open>\<I> (\<F>_functional \<psi>) = (\<lambda>x. {y. x = \<psi> y})\<close>
  unfolding \<F>_functional_def
  by (rule Interp_inverse, simp add: Interpretation_def one_set_def set_eq_iff inj_at_1) *)

lemma \<F>_functional_homo_one[simp, locale_intro]:
  \<open> simple_homo_mul \<psi> D
\<Longrightarrow> homo_one (\<F>_functional \<psi> D)\<close>
  unfolding homo_one_def \<F>_functional_def simple_homo_mul_def
  by (clarsimp simp add: BI_eq_iff Ball_def; blast)

(*TODO: move this or remove this*)
lemma map_option_inj_at_1[simp]:
  \<open>simple_homo_mul (map_option f) top\<close>
  unfolding one_option_def simple_homo_mul_def
  by (simp add: split_option_all)

lemma (in sep_orthogonal_monoid) \<F>_functional_projection:
  \<open> S \<le> D
\<Longrightarrow> refinement_projection (\<F>_functional \<psi> D) (\<psi> `\<^sub>I S) \<le> S * top\<close>
  unfolding refinement_projection_def
  by (clarsimp simp add: subset_iff set_mult_expn eq_commute[where a=\<open>\<psi> _\<close>] sep_orthogonal; blast)

lemma \<F>_functional_pointwise:
  \<open>\<F>_functional ((\<circ>) \<psi>) (pointwise_set D) = \<F>_pointwise (\<lambda>_. \<F>_functional \<psi> D)\<close>
  by (auto simp add: fun_eq_iff set_eq_iff; simp add: pointwise_set_def)

lemma \<F>_functional_comp:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> \<F>_functional (f o g) Dg = \<F>_functional g Dg \<Zcomp>\<^sub>\<I> \<F>_functional f Df\<close>
  by (auto simp add: fun_eq_iff set_eq_iff; blast)
  

(* definition "\<F>_share s = (case s of Share w v \<Rightarrow> if w = 1 then {v} else {})"

lemma \<F>_share_\<I>[simp]: "\<F>_share (Share w v) = (if w = 1 then {v} else {})"
  unfolding \<F>_share_def by simp *)

(* lemma In_ficion_fine [simp]:
  \<open>x \<in> (case some_fine of Fine y \<Rightarrow> f y | Undef \<Rightarrow> {})
        \<longleftrightarrow> (\<exists>y. some_fine = Fine y \<and> x \<in> f y)\<close>
  by (cases some_fine; simp)
*)

subsubsection \<open>Agreement\<close>

(* TODO: check this!!!!
definition \<open>\<F>_agree = (\<lambda>x. case x of agree x' \<Rightarrow> {x'})\<close> *)


subsection \<open>Refinement of Algebraic Structures\<close>

subsubsection \<open>Cancellative Separation Insertion Homomorphism\<close>

(*
lemma refinement_projection:
  \<open> kernel_is_1 \<psi>
\<Longrightarrow> Id_on UNIV * {(a, b)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` {(a,b)} \<w>.\<r>.\<t> \<F>_functional \<psi> \<i>\<n> \<psi> ` {a}\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn Subjection_expn_set)
subgoal for r R u v w *)

definition \<F>_functional_condition
  where \<open>\<F>_functional_condition D \<longleftrightarrow> (\<forall>r x y. x ## r \<and> y ## r \<and> r \<Turnstile> D \<and> x \<Turnstile> D \<and> x * r \<Turnstile> D \<and> y \<Turnstile> D \<longrightarrow> y * r \<Turnstile> D)\<close>

lemma \<F>_functional_condition_UNIV[simp]:
  \<open>\<F>_functional_condition top\<close>
  unfolding \<F>_functional_condition_def by simp

definition frame_preserving_relation \<comment> \<open>TODO: REALLY UGLY!\<close>
  where \<open>frame_preserving_relation R
    \<longleftrightarrow> (\<forall>a b c d r w. (a,b) \<Turnstile> R \<and> (c,d) \<Turnstile> R \<and> a * r = c * w \<and> a ## r \<and> b ## r \<and> c ## w
            \<longrightarrow> b * r = d * w \<and> d ## w)\<close>

context cancl_sep_orthogonal_monoid begin

lemma \<F>_functional_refinement_complex:
  \<open> (\<forall>a b. (a,b) \<in> R \<longrightarrow> a \<in> D \<and> b \<in> D)
\<Longrightarrow> frame_preserving_relation R
\<Longrightarrow> Sep_Closed D
\<Longrightarrow> R * Id_on UNIV \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` R \<w>.\<r>.\<t> \<F>_functional \<psi> D \<i>\<n> \<psi> ` (Domain R) \<close>
  unfolding Fictional_Forward_Simulation_def
  apply (auto simp add: set_mult_expn Subjection_expn_set sep_orthogonal Sep_Closed_def image_iff Bex_def)
  by (smt (z3) frame_preserving_relation_def homo_mult sep_disj_homo_semi sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)

lemma \<F>_functional_refinement:
  \<open> a \<in> D \<and> b \<in> D
\<Longrightarrow> \<F>_functional_condition D
\<Longrightarrow> {(a, b)} * Id_on UNIV \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` {(a,b)} \<w>.\<r>.\<t> \<F>_functional \<psi> D \<i>\<n> \<psi> ` {a} \<close>
  unfolding Fictional_Forward_Simulation_def \<F>_functional_condition_def
  apply (auto simp add: set_mult_expn Subjection_expn_set sep_orthogonal)
  apply (metis (no_types, lifting) homo_mult sep_cancel sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)
  by (metis sep_cancel sep_disj_homo_semi sep_disj_multD1 sep_disj_multD2 sep_disj_multI2 sep_mult_assoc)

end

subsubsection \<open>Cancellative Permission Insertion Homomorphism\<close>


context cancl_share_orthogonal_homo begin

lemma refinement_projection_half_perm:
  \<open>S \<subseteq> D \<Longrightarrow> 0 < n \<Longrightarrow> refinement_projection (\<F>_functional \<psi> D) ((share n o \<psi>) ` S) \<subseteq> S * UNIV\<close>
  unfolding refinement_projection_def
  by (auto simp add: set_mult_expn sep_orthogonal share_orthogonal';
      cases \<open>n \<le> 1\<close>,
      ((insert share_orthogonal_homo.share_orthogonal' share_orthogonal_homo_axioms, blast)[1],
       metis in_mono leI sep_orthogonal share_bounded share_right_one))


end



end