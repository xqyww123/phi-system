theory Semimodule
  imports HOL.Modules
begin

locale semi_additive =
  fixes f :: "'a::comm_monoid_add \<Rightarrow> 'b::comm_monoid_add"
  assumes add: "f (x + y) = f x + f y"
    and  zero: \<open>f 0 = 0\<close>
begin

lemma sum: "f (sum g A) = (\<Sum>x\<in>A. f (g x))"
  by (induct A rule: infinite_finite_induct) (simp_all add: zero add)

end

locale semi_additive_cancel =
  fixes f :: "'a::cancel_comm_monoid_add \<Rightarrow> 'b::cancel_comm_monoid_add"
  assumes add: "f (x + y) = f x + f y"
begin

lemma zero: "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "\<dots> = f 0 + f 0" by (rule add)
  finally show "f 0 = 0" by simp
qed

sublocale semi_additive apply standard using add zero .

end


locale semimodule =
  fixes scale :: "'a::comm_semiring_1 \<Rightarrow> 'b::comm_monoid_add \<Rightarrow> 'b" (infixr "*s" 75)
  assumes scale_right_distrib [algebra_simps, algebra_split_simps]:
      "a *s (x + y) = a *s x + a *s y"
    and scale_left_distrib [algebra_simps, algebra_split_simps]:
      "(a + b) *s x = a *s x + b *s x"
    and scale_scale [simp]: "a *s (b *s x) = (a * b) *s x"
    and scale_one [simp]: "1 *s x = x"
    and scale_zero [simp]: \<open>0 *s x = 0\<close> \<open>a *s 0 = 0\<close>
begin

lemma scale_left_commute: "a *s (b *s x) = b *s (a *s x)"
  by (simp add: mult.commute)

lemma scale_sum_left: "(sum f A) *s x = (\<Sum>a\<in>A. (f a) *s x)"
proof -
  interpret s: semi_additive "\<lambda>a. a *s x"
    by standard (rule scale_left_distrib, simp)
  show "(sum f A) *s x = (\<Sum>a\<in>A. (f a) *s x)" by (rule s.sum)
qed

lemma scale_sum_right: "a *s (sum f A) = (\<Sum>x\<in>A. a *s (f x))"
proof -
  interpret s: semi_additive "\<lambda>x. a *s x"
    by standard (rule scale_right_distrib, simp)
  show "a *s (sum f A) = (\<Sum>x\<in>A. a *s (f x))" by (rule s.sum)
qed

lemma sum_constant_scale: "(\<Sum>x\<in>A. y) = scale (of_nat (card A)) y"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

end

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>divide\<close>, SOME \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>)\<close>

context semimodule
begin

lemma [field_simps, field_split_simps]:
  shows scale_left_distrib_NO_MATCH: "NO_MATCH (x div y) c \<Longrightarrow> (a + b) *s x = a *s x + b *s x"
    and scale_right_distrib_NO_MATCH: "NO_MATCH (x div y) a \<Longrightarrow> a *s (x + y) = a *s x + a *s y"
  by (rule scale_left_distrib scale_right_distrib)+

end

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>divide\<close>, SOME \<^typ>\<open>'a::divide \<Rightarrow> 'a \<Rightarrow> 'a\<close>)\<close>


section \<open>Subspace\<close>

context semimodule
begin

definition subspace :: "'b set \<Rightarrow> bool"
  where "subspace S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>x\<in>S. \<forall>y\<in>S. x + y \<in> S) \<and> (\<forall>c. \<forall>x\<in>S. c *s x \<in> S)"

lemma subspaceI:
  "0 \<in> S \<Longrightarrow> (\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x + y \<in> S) \<Longrightarrow> (\<And>c x. x \<in> S \<Longrightarrow> c *s x \<in> S) \<Longrightarrow> subspace S"
  by (auto simp: subspace_def)

lemma subspace_UNIV[simp]: "subspace UNIV"
  by (simp add: subspace_def)

lemma subspace_single_0[simp]: "subspace {0}"
  by (simp add: subspace_def)

lemma subspace_0: "subspace S \<Longrightarrow> 0 \<in> S"
  by (metis subspace_def)

lemma subspace_add: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x + y \<in> S"
  by (metis subspace_def)

lemma subspace_scale: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> c *s x \<in> S"
  by (metis subspace_def)

lemma subspace_sum: "subspace A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<in> A) \<Longrightarrow> sum f B \<in> A"
  by (induct B rule: infinite_finite_induct) (auto simp add: subspace_add subspace_0)

lemma subspace_Int: "(\<And>i. i \<in> I \<Longrightarrow> subspace (s i)) \<Longrightarrow> subspace (\<Inter>i\<in>I. s i)"
  by (auto simp: subspace_def)

lemma subspace_Inter: "\<forall>s \<in> f. subspace s \<Longrightarrow> subspace (\<Inter>f)"
  unfolding subspace_def by auto

lemma subspace_inter: "subspace A \<Longrightarrow> subspace B \<Longrightarrow> subspace (A \<inter> B)"
  by (simp add: subspace_def)


section \<open>Span: subspace generated by a set\<close>

definition span :: "'b set \<Rightarrow> 'b set"
  where span_explicit: "span b = {(\<Sum>a\<in>t. r a *s  a) | t r. finite t \<and> t \<subseteq> b}"

lemma span_explicit':
  "span b = {(\<Sum>v | f v \<noteq> 0. f v *s v) | f. finite {v. f v \<noteq> 0} \<and> (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> b)}"
  unfolding span_explicit
proof safe
  fix t r assume "finite t" "t \<subseteq> b"
  then show "\<exists>f. (\<Sum>a\<in>t. r a *s a) = (\<Sum>v | f v \<noteq> 0. f v *s v) \<and> finite {v. f v \<noteq> 0} \<and> (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> b)"
    by (intro exI[of _ "\<lambda>v. if v \<in> t then r v else 0"]) (auto intro!: sum.mono_neutral_cong_right)
next
  fix f :: "'b \<Rightarrow> 'a" assume "finite {v. f v \<noteq> 0}" "(\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> b)"
  then show "\<exists>t r. (\<Sum>v | f v \<noteq> 0. f v *s v) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> b"
    by (intro exI[of _ "{v. f v \<noteq> 0}"] exI[of _ f]) auto
qed

lemma span_alt:
  "span B = {(\<Sum>x | f x \<noteq> 0. f x *s x) | f. {x. f x \<noteq> 0} \<subseteq> B \<and> finite {x. f x \<noteq> 0}}"
  unfolding span_explicit' by auto

lemma span_finite:
  assumes fS: "finite S"
  shows "span S = range (\<lambda>u. \<Sum>v\<in>S. u v *s v)"
  unfolding span_explicit
proof safe
  fix t r assume "t \<subseteq> S" then show "(\<Sum>a\<in>t. r a *s a) \<in> range (\<lambda>u. \<Sum>v\<in>S. u v *s v)"
    by (intro image_eqI[of _ _ "\<lambda>a. if a \<in> t then r a else 0"])
       (auto simp: if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases fS Int_absorb1)
next
  show "\<exists>t r. (\<Sum>v\<in>S. u v *s v) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> S" for u
    by (intro exI[of _ u] exI[of _ S]) (auto intro: fS)
qed

lemma span_induct_alt [consumes 1, case_names base step, induct set: span]:
  assumes x: "x \<in> span S"
  assumes h0: "h 0" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *s x + y)"
  shows "h x"
  using x unfolding span_explicit
proof safe
  fix t r assume "finite t" "t \<subseteq> S" then show "h (\<Sum>a\<in>t. r a *s a)"
    by (induction t) (auto intro!: hS h0)
qed

lemma span_mono: "A \<subseteq> B \<Longrightarrow> span A \<subseteq> span B"
  by (auto simp: span_explicit)

lemma span_base: "a \<in> S \<Longrightarrow> a \<in> span S"
  by (auto simp: span_explicit intro!: exI[of _ "{a}"] exI[of _ "\<lambda>_. 1"])

lemma span_superset: "S \<subseteq> span S"
  by (auto simp: span_base)

lemma span_zero: "0 \<in> span S"
  by (auto simp: span_explicit intro!: exI[of _ "{}"])

lemma span_UNIV[simp]: "span UNIV = UNIV"
  by (auto intro: span_base)

lemma span_add: "x \<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x + y \<in> span S"
  unfolding span_explicit
proof safe
  fix tx ty rx ry assume *: "finite tx" "finite ty" "tx \<subseteq> S" "ty \<subseteq> S"
  have [simp]: "(tx \<union> ty) \<inter> tx = tx" "(tx \<union> ty) \<inter> ty = ty"
    by auto
  show "\<exists>t r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> S"
    apply (intro exI[of _ "tx \<union> ty"])
    apply (intro exI[of _ "\<lambda>a. (if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)"])
    apply (auto simp: * scale_left_distrib sum.distrib if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases)
    done
qed

lemma span_scale: "x \<in> span S \<Longrightarrow> c *s x \<in> span S"
  unfolding span_explicit
proof safe
  fix t r assume *: "finite t" "t \<subseteq> S"
  show "\<exists>t' r'. c *s (\<Sum>a\<in>t. r a *s a) = (\<Sum>a\<in>t'. r' a *s a) \<and> finite t' \<and> t' \<subseteq> S"
    by (intro exI[of _ t] exI[of _ "\<lambda>a. c * r a"]) (auto simp: * scale_sum_right)
qed

lemma subspace_span [iff]: "subspace (span S)"
  by (auto simp: subspace_def span_zero span_add span_scale)

lemma span_sum: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> span S) \<Longrightarrow> sum f A \<in> span S"
  by (rule subspace_sum, rule subspace_span)

lemma span_minimal: "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> span S \<subseteq> T"
  by (auto simp: span_explicit intro!: subspace_sum subspace_scale)

lemma span_def: "span S = subspace hull S" 
  by (intro hull_unique[symmetric] span_superset subspace_span span_minimal)

lemma span_unique:
  "S \<subseteq> T \<Longrightarrow> subspace T \<Longrightarrow> (\<And>T'. S \<subseteq> T' \<Longrightarrow> subspace T' \<Longrightarrow> T \<subseteq> T') \<Longrightarrow> span S = T"
  unfolding span_def by (rule hull_unique)

lemma span_subspace_induct[consumes 2]:
  assumes x: "x \<in> span S"
    and P: "subspace P"
    and SP: "\<And>x. x \<in> S \<Longrightarrow> x \<in> P"
  shows "x \<in> P"
proof -
  from SP have SP': "S \<subseteq> P"
    by (simp add: subset_eq)
  from x hull_minimal[where S=subspace, OF SP' P, unfolded span_def[symmetric]]
  show "x \<in> P"
    by (metis subset_eq)
qed

lemma (in semimodule) span_induct[consumes 1, case_names base step, induct set: span]:
  assumes x: "x \<in> span S"
    and P: "subspace (Collect P)"
    and SP: "\<And>x. x \<in> S \<Longrightarrow> P x"
  shows "P x"
  using P SP span_subspace_induct x by fastforce

lemma span_empty[simp]: "span {} = {0}"
  by (rule span_unique) (auto simp add: subspace_def)

lemma span_subspace: "A \<subseteq> B \<Longrightarrow> B \<subseteq> span A \<Longrightarrow> subspace B \<Longrightarrow> span A = B"
  by (metis order_antisym span_def hull_minimal)

lemma span_span: "span (span A) = span A"
  unfolding span_def hull_hull ..

lemma span_singleton: "span {x} = range (\<lambda>k. k *s x)"
  by (auto simp: span_finite)

lemma span_Un: "span (S \<union> T) = {x + y | x y. x \<in> span S \<and> y \<in> span T}"
proof safe
  fix x assume "x \<in> span (S \<union> T)"
  then obtain t r where t: "finite t" "t \<subseteq> S \<union> T" and x: "x = (\<Sum>a\<in>t. r a *s a)"
    by (auto simp: span_explicit)
  moreover have "t \<inter> S \<union> (t - S) = t" by auto
  ultimately show "\<exists>xa y. x = xa + y \<and> xa \<in> span S \<and> y \<in> span T"
    unfolding x
    apply (rule_tac exI[of _ "\<Sum>a\<in>t \<inter> S. r a *s a"])
    apply (rule_tac exI[of _ "\<Sum>a\<in>t - S. r a *s a"])
    apply (subst sum.union_inter_neutral[symmetric])
    apply (auto intro!: span_sum span_scale intro: span_base)
    done
next
  fix x y assume"x \<in> span S" "y \<in> span T" then show "x + y \<in> span (S \<union> T)"
    using span_mono[of S "S \<union> T"] span_mono[of T "S \<union> T"]
    by (auto intro!: span_add)
qed

lemma span_insert: "span (insert a S) = {x + k *s a | x k. x \<in> span S}"
proof -
  have "span ({a} \<union> S) = {x + k *s a |x k. x \<in> span S}"
    unfolding span_Un span_singleton
    apply (auto simp add: set_eq_iff)
    subgoal for y k using add.commute by blast 
    subgoal for y k using add.commute by blast 
    done
  then show ?thesis by simp
qed

lemma span_breakdown:
  assumes bS: "b \<in> S"
    and aS: "a \<in> span S"
  shows "\<exists>k a'. a = a' + k *s b \<and> a' \<in> span (S - {b})"
  using assms span_insert [of b "S - {b}"]
  using insert_Diff by fastforce

lemma span_breakdown_eq: "x \<in> span (insert a S) \<longleftrightarrow> (\<exists>k x'. x = x' + k *s a \<and> x' \<in> span S)"
  using span_insert by auto

lemmas span_clauses = span_base span_zero span_add span_scale

lemma span_eq_iff[simp]: "span s = s \<longleftrightarrow> subspace s"
  unfolding span_def by (rule hull_eq) (rule subspace_Inter)

lemma span_eq: "span S = span T \<longleftrightarrow> S \<subseteq> span T \<and> T \<subseteq> span S"
  by (metis span_minimal span_subspace span_superset subspace_span)

(* lemma eq_span_insert_eq:
  assumes "(x - y) \<in> span S"
    shows "span(insert x S) = span(insert y S)"
proof -
  have *: "span(insert x S) \<subseteq> span(insert y S)" if "(x - y) \<in> span S" for x y
  proof -
    have 1: "(r *s x - r *s y) \<in> span S" for r
      by (metis scale_right_diff_distrib span_scale that)
    have 2: "(z - k *s y) - k *s (x - y) = z - k *s x" for  z k
      by (simp add: scale_right_diff_distrib)
  show ?thesis
    apply (clarsimp simp add: span_breakdown_eq)
    by (metis 1 2 diff_add_cancel scale_right_diff_distrib span_add_eq)
  qed
  show ?thesis
    apply (intro subset_antisym * assms)
    using assms subspace_neg subspace_span minus_diff_eq by force
qed
*)


end