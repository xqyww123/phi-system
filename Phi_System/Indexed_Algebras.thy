theory Indexed_Algebras
  imports Phi_BI
begin

section \<open>Definitions\<close>

locale simple_homo_mul =
  fixes \<psi> :: \<open> 'a::one \<Rightarrow> 'b::one \<close>
    and D :: \<open> 'a BI \<close> \<comment> \<open>The domain is still required. For example, consider the homomorphism
                            from mult-element algebra to single element algebra,
                            the homomorphism cannot be simple unless the domain of the homomorphism
                            is limited to {1}.\<close>
  assumes kernel_is_1[iff]: \<open>x \<Turnstile> D \<Longrightarrow> \<psi> x = 1 \<longleftrightarrow> x = 1\<close>
      and simple_homo_mul_dom[simp]: \<open>1 \<Turnstile> D\<close>
begin

sublocale homo_one by (standard, insert simple_homo_mul_dom, blast)

end


lemma simple_homo_mul_sub_dom:
  \<open> D' \<le> D \<and> 1 \<Turnstile> D'
\<Longrightarrow> simple_homo_mul \<psi> D
\<Longrightarrow> simple_homo_mul \<psi> D' \<close>
  unfolding simple_homo_mul_def less_eq_BI_iff
  by clarsimp

locale sep_orthogonal = homo_sep \<psi>
  for \<psi> :: \<open>'a::sep_magma \<Rightarrow> 'b::sep_magma\<close>
  and D :: \<open>'a set\<close> \<comment> \<open>carrier set of the source algebra,
            Previously we implicitly extend the carrier set to be the universe of the type.
            It can be done because for any element \<open>d\<close> not belonging to the carrier set,
            only if \<open>d\<close> has no defined operation with any element including itself,
            the introduction of \<open>d\<close> doesn't affect anything.
            However here, if \<open>a = \<psi> d\<close> accidentally belongs to the target algebra, \<open>d\<close> matters,
            so we must give the carrier set explicitly to exclude such \<open>d\<close>.\<close>
        \<comment> \<open>It is a bad idea to reuse \<open>mul_carrier\<close> to replace \<open>D\<close> here. \<open>sep_orthogonal\<close> is mainly
            used in fictional SL where the actual domain can be various and even for example dependent
            on the key of the map (e.g., later in the memory model of C, the domain of each block
            depends on the type of the block which is acquired from the key of the map modelling
            the memory). \<open>mul_carrier\<close> is fixed to its logic type can never be so flexible.
            \<open>mul_carrier\<close> is designed for simplifying the specification of separation semimodules.
            Properties of separation semimodules are bound to the type, by means of type classes,
            so it is okay to again use a type class to bind the carrier set to the types.\<close>
+ assumes sep_orthogonal: \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> \<psi> b * a = \<psi> c \<longleftrightarrow> (\<exists>a'. a = \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
begin


lemma sep_orthogonal'[no_atp]:
  \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> \<psi> c = \<psi> b * a \<longleftrightarrow> (\<exists>a'. a = \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
  by (metis sep_orthogonal)

sublocale homo_join_sub \<psi>
  apply standard
  unfolding join_sub_def
  by (metis homo_mult sep_disj_homo_semi sep_orthogonal)

text \<open>The weak homomorphism of \<open>\<preceq>\<^sub>S\<^sub>L\<close>, \<open>x \<preceq>\<^sub>S\<^sub>L z \<longrightarrow> \<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> z\<close> is trivially true but the reversed
so-called closed homo \<open>\<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> z \<longrightarrow> x \<preceq>\<^sub>S\<^sub>L z\<close> is not seen even in closed separation homo.

\<open>\<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> z \<longrightarrow> x \<preceq>\<^sub>S\<^sub>L z  \<Longleftrightarrow>  \<forall>y'. \<psi> z = y' * \<psi> x \<longrightarrow> \<exists>y. z = y * x\<close>
can be unfolded to a form really similar (but weaker) to the orthogonal homo
(the only difference is it doesn't require \<open>y' = \<psi> y\<close>). So orthogonal homo entails the closed homo
of join_sub, but not reversely.\<close>

end

locale sep_orthogonal_1 = sep_orthogonal \<psi> D
  for \<psi> :: \<open>'a::sep_magma_1 \<Rightarrow> 'b::sep_magma_1\<close> and D
+ assumes one_in_D: \<open>1 \<in> D\<close>
begin

sublocale homo_one \<psi>
  by (standard, metis mult_1_class.mult_1_left mult_1_class.mult_1_right one_in_D sep_magma_1_left sep_orthogonal)

end



locale sep_orthogonal_monoid = sep_orthogonal_1 \<psi> D
  for \<psi> :: \<open>'a::sep_monoid \<Rightarrow> 'b::sep_monoid\<close> and D
begin

lemma simple_homo_mul[simp]:
  \<open>simple_homo_mul \<psi> D\<close>
  unfolding simple_homo_mul_def
  by (metis homo_join_sub homo_one join_sub.bot.extremum join_sub.bot.extremum_uniqueI one_in_D)

end

locale cancl_sep_orthogonal_monoid = sep_orthogonal_monoid \<psi> D
  for \<psi> :: \<open>'a::{sep_cancel, sep_monoid} \<Rightarrow> 'b::sep_monoid\<close> and D

locale share_orthogonal_homo = sep_orthogonal_monoid \<psi> D
  for \<psi> :: \<open>'a::sep_algebra \<Rightarrow> 'b::share_semimodule\<close> and D
+ assumes share_orthogonal: \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
                           share n (\<psi> b) * a = \<psi> c \<longleftrightarrow> (\<exists>a'. a = share (1-n) (\<psi> b) * \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
    and   share_bounded: \<open>\<lbrakk> b \<in> D \<and> c \<in> D ; \<psi> b ## a ; n > 1 ; \<psi> b \<noteq> 1 \<rbrakk> \<Longrightarrow> share n (\<psi> b) * a \<noteq> \<psi> c\<close>
    and   \<psi>_mul_carrier: \<open>x \<in> D \<Longrightarrow> mul_carrier (\<psi> x) \<close>
begin

lemma share_orthogonal'[no_atp]:
  \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
      \<psi> c = share n (\<psi> b) * a \<longleftrightarrow> (\<exists>a'. a = share (1-n) (\<psi> b) * \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
  by (metis share_orthogonal)

lemma
  join_sub_share_join_sub_whole: \<open>0 < n \<and> n \<le> 1 \<Longrightarrow> x \<in> D \<and> y \<in> D \<Longrightarrow> share n (\<psi> x) \<preceq>\<^sub>S\<^sub>L \<psi> y \<longleftrightarrow> x \<preceq>\<^sub>S\<^sub>L y\<close>
  unfolding join_sub_def
  by ((rule; clarsimp simp add: homo_mult),
      metis share_orthogonal,
      meson \<psi>_mul_carrier join_sub_def join_sub_ext_right less_eq_rat_def sep_disj_homo_semi share_sep_disj_left share_sub)
  
end

locale cancl_share_orthogonal_homo = share_orthogonal_homo \<psi> D
  for \<psi> :: \<open>'a::{sep_cancel, sep_algebra} \<Rightarrow> 'b::share_semimodule\<close> and D
begin

sublocale cancl_sep_orthogonal_monoid ..

end

subsubsection \<open>With Discrete Algebra\<close>

lemma closed_homo_sep_disj_discrete_1[simp]:
  \<open> simple_homo_mul \<psi> UNIV
\<Longrightarrow> closed_homo_sep_disj \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_monoid \<Rightarrow> 'b::discrete_monoid\<close>
  unfolding closed_homo_sep_disj_def simple_homo_mul_def
  by simp



section \<open>Instances\<close>

subsection \<open>Lambda Identity\<close>

lemma simple_homo_mul_id[simp]:
  \<open>1 \<in> D \<Longrightarrow> simple_homo_mul (\<lambda>x. x) D\<close>
  unfolding simple_homo_mul_def
  by simp

subsection \<open>Functional Composition\<close>

lemma simple_homo_mul_comp[simp]:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> simple_homo_mul f Df
\<Longrightarrow> simple_homo_mul g Dg
\<Longrightarrow> simple_homo_mul (f o g) Dg\<close>
  unfolding simple_homo_mul_def
  by (simp add: image_subset_iff)

lemma sep_orthogonal_comp:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> sep_orthogonal f Df \<Longrightarrow> sep_orthogonal g Dg \<Longrightarrow> sep_orthogonal (f o g) Dg\<close>
  unfolding sep_orthogonal_def sep_orthogonal_axioms_def
  by (clarsimp simp add: homo_sep_comp subset_iff image_iff Bex_def,
      smt (verit, ccfv_threshold) homo_sep.axioms(2) homo_sep_disj.sep_disj_homo_semi)

lemma sep_orthogonal_1_comp:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> sep_orthogonal_1 f Df \<Longrightarrow> sep_orthogonal_1 g Dg \<Longrightarrow> sep_orthogonal_1 (f o g) Dg\<close>
  unfolding sep_orthogonal_1_def
  by (clarsimp simp add: homo_sep_comp subset_iff image_iff Bex_def,
      metis image_subsetI sep_orthogonal_comp)

lemma sep_orthogonal_monoid_comp[locale_intro]:
  \<open> g ` Dg \<subseteq> Df \<Longrightarrow> sep_orthogonal_monoid f Df \<Longrightarrow> sep_orthogonal_monoid g Dg \<Longrightarrow> sep_orthogonal_monoid (f o g) Dg\<close>
  unfolding sep_orthogonal_monoid_def using sep_orthogonal_1_comp .

lemma share_orthogonal_homo_composition[locale_intro]:
  assumes dom_trans: \<open>g ` Dg \<subseteq> Df\<close>
      and f: \<open>share_orthogonal_homo f Df\<close>
      and g: \<open>sep_orthogonal_monoid g Dg\<close>
    shows \<open>share_orthogonal_homo (f o g) Dg\<close>
proof -
  interpret f: share_orthogonal_homo f Df using f .
  interpret g: sep_orthogonal_monoid g Dg using g .
  have f': \<open>sep_orthogonal_monoid f Df\<close> by (simp add: f.sep_orthogonal_monoid_axioms)
  have g': \<open>sep_orthogonal_monoid g Dg\<close> by (simp add: g.sep_orthogonal_monoid_axioms)
  have t[simp]: \<open>x \<in> Dg \<Longrightarrow> g x \<in> Df\<close> for x using dom_trans by blast 

  show ?thesis
    unfolding share_orthogonal_homo_def share_orthogonal_homo_axioms_def
    apply (auto simp add: f.share_orthogonal)
    apply (meson dom_trans f' g' sep_orthogonal_monoid_comp)
    using g.sep_orthogonal apply auto[1]
    using g.homo_mult apply auto[1]
    using f.share_bounded t apply blast
    using f.\<psi>_mul_carrier t by blast 

qed

subsection \<open>Option\<close>

lemma simple_homo_mul_map_option[simp]:
  \<open>simple_homo_mul (map_option f) UNIV\<close>
  unfolding simple_homo_mul_def
  by simp

subsection \<open>Pointwise\<close>

lemma simple_homo_mul_funcomp[simp]:
  \<open> simple_homo_mul f D
\<Longrightarrow> simple_homo_mul ((o) f) (pointwise_set D)\<close>
  unfolding simple_homo_mul_def pointwise_set_def
  by (clarsimp simp add: Ball_def fun_eq_iff)


subsection \<open>Partial Map\<close>

lemma sep_orthogonal_monoid_pointwise[locale_intro]:
  assumes D':   \<open>D' = pointwise_set D\<close>
      and prem: \<open>sep_orthogonal_monoid \<psi> D\<close>
  shows \<open>sep_orthogonal_monoid ((\<circ>) \<psi>) D'\<close>
  unfolding comp_def
proof
  interpret xx: sep_orthogonal_monoid \<psi> D using prem .
  fix x y a b c :: \<open>'a \<Rightarrow> 'b\<close>
  fix a' :: \<open>'a \<Rightarrow> 'c\<close>
  show \<open>x ## y \<Longrightarrow> (\<lambda>xa. \<psi> ((x * y) xa)) = (\<lambda>xa. \<psi> (x xa)) * (\<lambda>x. \<psi> (y x))\<close>
    by (simp add: fun_eq_iff times_fun sep_disj_fun_def xx.homo_mult)
  show \<open>a ## b \<longrightarrow> (\<lambda>x. \<psi> (a x)) ## (\<lambda>x. \<psi> (b x))\<close>
    by (simp add: fun_eq_iff times_fun sep_disj_fun_def D' pointwise_set_def)
  show \<open>b \<in> D' \<and> c \<in> D' \<Longrightarrow> (\<lambda>x. \<psi> (b x)) ## a' \<Longrightarrow>
     ((\<lambda>x. \<psi> (b x)) * a' = (\<lambda>x. \<psi> (c x))) = (\<exists>a. a' = (\<lambda>x. \<psi> (a x)) \<and> b * a = c \<and> b ## a \<and> a \<in> D')\<close>
    by (auto simp add: D' fun_eq_iff times_fun sep_disj_fun_def xx.sep_orthogonal pointwise_set_def; metis)
  show \<open>1 \<in> D'\<close>
    by (simp add: D' pointwise_set_def xx.one_in_D)
qed

lemma share_orthogonal_homo_pointwise[locale_intro]:
  assumes D':   \<open>D' = pointwise_set D\<close>
      and prem: \<open>share_orthogonal_homo \<psi> D\<close>
    shows \<open>share_orthogonal_homo ((\<circ>) \<psi>) D'\<close>
proof (rule share_orthogonal_homo.intro, rule sep_orthogonal_monoid_pointwise,
       rule D', rule share_orthogonal_homo.axioms(1)[OF prem], standard)
  interpret xx: share_orthogonal_homo \<psi> D using prem .

  fix x y z a b c :: \<open>'a \<Rightarrow> 'b\<close>
  fix a' :: \<open>'a \<Rightarrow> 'c\<close>
  fix n :: rat

  show \<open>x \<in> D' \<Longrightarrow> mul_carrier (\<psi> \<circ> x)\<close>
    by (simp add: D' sep_disj_fun_def xx.\<psi>_mul_carrier pointwise_set_def)
  
  show \<open>b \<in> D' \<and> c \<in> D' \<Longrightarrow> (\<psi> \<circ> b) ## a' \<Longrightarrow>
       0 < n \<and> n \<le> 1 \<Longrightarrow> (n \<odivr> (\<psi> \<circ> b) * a' = (\<psi> \<circ> c))
                        = (\<exists>a''. a' = (1 - n) \<odivr> (\<psi> \<circ> b) * (\<psi> \<circ> a'') \<and> b * a'' = c \<and> b ## a'' \<and> a'' \<in> D')\<close>
    by (auto simp add: join_sub_def fun_eq_iff times_fun sep_disj_fun_def xx.share_orthogonal
            share_fun_def pointwise_set_def D'; metis)

  show \<open>b \<in> D' \<and> c \<in> D' \<Longrightarrow> (\<psi> \<circ> b) ## a' \<Longrightarrow> 1 < n \<Longrightarrow> \<psi> \<circ> b \<noteq> 1 \<Longrightarrow> n \<odivr> (\<psi> \<circ> b) * a' \<noteq> \<psi> \<circ> c\<close>
    by (clarsimp simp add: fun_eq_iff sep_disj_fun_def times_fun_def share_fun_def,
        metis D' mem_Collect_eq pointwise_set_def xx.share_bounded)

qed

lemma sep_orthogonal_monoid_pointwise_eq:
  \<open>sep_orthogonal_monoid ((\<circ>) \<psi>) (pointwise_set D) \<longleftrightarrow> sep_orthogonal_monoid \<psi> D\<close>
  for \<psi> :: \<open>'b::sep_monoid \<Rightarrow> 'c::sep_monoid\<close>
proof
  assume prem: \<open>sep_orthogonal_monoid ((\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) (pointwise_set D)\<close>
  show \<open>sep_orthogonal_monoid \<psi> D\<close>
  proof
    interpret xx: sep_orthogonal_monoid \<open>(\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close> \<open>(pointwise_set D)\<close> using prem .
    fix x y a b c :: \<open>'b\<close> and a2 :: 'c
    show \<open>x ## y \<Longrightarrow> \<psi> (x * y) = \<psi> x * \<psi> y\<close>
      using xx.homo_mult[unfolded sep_disj_fun_def times_fun one_fun_def fun_eq_iff, simplified]
      by meson
    show \<open>a ## b \<longrightarrow> \<psi> a ## \<psi> b\<close>
      using xx.sep_disj_homo_semi[unfolded sep_disj_fun_def times_fun one_fun_def fun_eq_iff, simplified]
      by meson
    show \<open>1 \<in> D\<close>
      using xx.one_in_D by (auto simp add: pointwise_set_def)
    show \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a2 \<Longrightarrow>
            (\<psi> b * a2 = \<psi> c) = (\<exists>a'. a2 = \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
      using xx.sep_orthogonal[unfolded sep_disj_fun_def times_fun one_fun_def fun_eq_iff,
          where a=\<open>\<lambda>_. a2\<close> and b=\<open>\<lambda>_. b\<close> and c=\<open>\<lambda>_. c\<close>, simplified pointwise_set_def, simplified]
      by auto
  qed
next
  show \<open>sep_orthogonal_monoid \<psi> D \<Longrightarrow> sep_orthogonal_monoid ((\<circ>) \<psi>) (pointwise_set D)\<close>
    using sep_orthogonal_monoid_pointwise by blast 
qed

lemma share_orthogonal_homo_pointwise_eq:
  \<open>share_orthogonal_homo ((\<circ>) \<psi>) (pointwise_set D) \<longleftrightarrow> share_orthogonal_homo \<psi> D\<close>
  for \<psi> :: \<open>'b::sep_algebra \<Rightarrow> 'c::share_semimodule\<close>
proof
  assume prem: \<open>share_orthogonal_homo ((\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) (pointwise_set D)\<close>
  show \<open>share_orthogonal_homo \<psi> D\<close>
  proof (rule share_orthogonal_homo.intro[OF share_orthogonal_homo.axioms(1)[OF prem, unfolded sep_orthogonal_monoid_pointwise_eq]],
         standard)
    interpret xx: share_orthogonal_homo \<open>((\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c)\<close> \<open>(pointwise_set D)\<close> using prem .
    fix x y a b c :: \<open>'b\<close> and a2 :: 'c and n :: rat

    show \<open> x \<in> D \<Longrightarrow> mul_carrier (\<psi> x) \<close>
      using xx.\<psi>_mul_carrier[of \<open>\<lambda>_. x\<close>, simplified pointwise_set_def, simplified]
      by (auto simp add: sep_disj_fun_def)

    show \<open> b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a2 \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
            (n \<odivr> \<psi> b * a2 = \<psi> c) = (\<exists>a'. a2 = (1 - n) \<odivr> \<psi> b * \<psi> a'\<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
      by (insert xx.share_orthogonal[where a=\<open>\<lambda>_. a2\<close> and b=\<open>\<lambda>_. b\<close> and c=\<open>\<lambda>_. c\<close>];
          clarsimp simp add: sep_disj_fun_def share_fun_def fun_eq_iff times_fun pointwise_set_def; rule; auto)

    show \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a2 \<Longrightarrow> 1 < n \<Longrightarrow> \<psi> b \<noteq> 1 \<Longrightarrow> n \<odivr> \<psi> b * a2 \<noteq> \<psi> c\<close>
      by (insert xx.share_bounded[where a=\<open>\<lambda>_. a2\<close> and b=\<open>\<lambda>_. b\<close> and c=\<open>\<lambda>_. c\<close>];
          clarsimp simp add: sep_disj_fun_def share_fun_def fun_eq_iff times_fun pointwise_set_def)

  qed
next
  show \<open>share_orthogonal_homo \<psi> D \<Longrightarrow> share_orthogonal_homo ((\<circ>) \<psi>) (pointwise_set D)\<close>
    using share_orthogonal_homo_pointwise by blast 
qed


subsection \<open>Permission\<close>

lemma share_orthogonal_homo_to_share[locale_witness]:
  \<open>share_orthogonal_homo (to_share::'a::{sep_carrier, discrete_semigroup} option \<Rightarrow> 'a share option) (Collect mul_carrier)\<close>
proof
  fix x y z a b c :: \<open>'a option\<close>
  fix xx yy aa bb cc :: \<open>'a\<close>
  fix a' a2 :: \<open>'a share option\<close>
  fix n :: rat
  show \<open>x ## y \<Longrightarrow> to_share (x * y) = to_share x * to_share y\<close> by (cases x; cases y; simp)
  show \<open>a ## b \<longrightarrow> to_share a ## to_share b\<close> by simp
  show \<open>b \<in> Collect mul_carrier \<and> c \<in> Collect mul_carrier \<Longrightarrow>
        to_share b ## a' \<Longrightarrow>
       (to_share b * a' = to_share c) = (\<exists>a. a' = to_share a \<and> b * a = c \<and> b ## a \<and> a \<in> Collect mul_carrier)\<close>
    apply (cases a'; cases b; cases c; simp add: split_option_ex)
    subgoal for a'' by (cases a''; simp) .
  show \<open>(1::'a option) \<in> Collect mul_carrier\<close> by simp
  (* show \<open>inj to_share\<close>
    by (rule, simp, metis option.inj_map_strong share.inject) *)
  show \<open>x \<in> Collect mul_carrier \<Longrightarrow> mul_carrier (to_share x)\<close> by (cases x; simp)
  show \<open>b \<in> Collect mul_carrier \<and> c \<in> Collect mul_carrier \<Longrightarrow>
        to_share b ## a2 \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
        (n \<odivr> to_share b * a2 = to_share c) = (\<exists>a'. a2 = (1 - n) \<odivr> to_share b * to_share a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> Collect mul_carrier)\<close>
    apply (cases a2; cases b; cases c; simp add: share_option_def)
    apply (cases \<open>n < 1\<close>; simp)
    apply (smt (verit, ccfv_SIG) diff_add_cancel diff_gt_0_iff_gt sep_cancel sep_disj_commuteI sep_disj_multD2 sep_disj_multI2 sep_disj_share sep_mult_commute times_share)
    by (metis join_strict_positivity sep_disj_distrib_left sep_disj_share zero_less_one)

  show \<open>b \<in> Collect mul_carrier \<and> c \<in> Collect mul_carrier \<Longrightarrow> to_share b ## a2 \<Longrightarrow> 1 < n \<Longrightarrow> to_share b \<noteq> 1 \<Longrightarrow>
        n \<odivr> to_share b * a2 \<noteq> to_share c\<close>
    by (cases a2; cases b; cases c; simp; case_tac a; simp)
  
qed


lemma to_share_kernel_is_1[locale_witness]:
  \<open> 1 \<in> D
\<Longrightarrow> simple_homo_mul to_share D\<close>
  by (simp add: simple_homo_mul_def)



end