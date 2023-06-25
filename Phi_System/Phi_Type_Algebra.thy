theory Phi_Type_Algebra
  imports IDE_CP_Core Phi_Algebras.Map_of_Tree
  keywords "\<phi>type_def" :: thy_defn
begin

section \<open>The Algebra of \<open>\<phi>\<close>-Refinement\<close>

subsection \<open>Definitions\<close>

(*
subsubsection \<open>Unit\<close>

definition \<open>Unit_Homo T \<longleftrightarrow> (1 \<Ztypecolon> T) = 1\<close>
definition \<open>Semi_Unit_Homo T \<longleftrightarrow> ((1 \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1)\<close>
definition \<open>Semi_Unit_Functor F \<longleftrightarrow> (\<forall>x T. (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1) \<longrightarrow> (x \<Ztypecolon> F T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1))\<close> *)

(*
definition \<open>Unit_Functor F \<longleftrightarrow> (\<forall>x T. (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1) \<longrightarrow> (x \<Ztypecolon> F T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1)) \<and>
                               (\<forall>x T. (1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T) \<longrightarrow> (1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> F T))\<close> *)


subsubsection \<open>Transformation\<close>

definition \<open>Transformation_Functor F1 F2 D mapper \<longleftrightarrow>
  (\<forall>T U x g. (\<forall>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b) \<longrightarrow>
               (x \<Ztypecolon> F1 T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y))\<close>
  \<comment> \<open>f1 and d1 make the domain set.

  The definition is given in reasoning-friendly form and should entail, (TODO: verify!)

  definition \<open>Transformation_Functor F1 F2 mapper \<longleftrightarrow>
    (\<forall>T U r x. (\<forall>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. (x,y) \<in> r) \<longrightarrow>
               (x \<Ztypecolon> F1 T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. (x,y) \<in> mapper r))\<close>,
  when D is UNIV

  The nondeterminancy from relation \<open>r\<close> can be achieved by embedding ExTyp.

  We strengthen this original definition by allowing the domain of the element transformation to be
  depended on the source object of the functor transformation so that the reasoning can have more
  information about the domain of the element transformation.
\<close>

lemma Transformation_Functor_sub_dom:
  \<open> (\<And>x. Da x \<subseteq> Db x)
\<Longrightarrow> Transformation_Functor F1 F2 Da mapper
\<Longrightarrow> Transformation_Functor F1 F2 Db mapper\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: subset_iff; blast)

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb D mapper
\<Longrightarrow> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<Longrightarrow> a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<close>
  unfolding Transformation_Functor_def Premise_def
  by simp


subsubsection \<open>Inhabitance\<close>

(*depreciated!*)
definition \<open>Inhabitance_Functor F f \<longleftrightarrow> (\<forall>T x. Inhabited(x \<Ztypecolon> F T) \<longrightarrow> Inhabited(f x \<Ztypecolon> T))\<close>
(* definition \<open>Inhabitance_Functor2 F f g \<longleftrightarrow> (\<forall>T U x. Inhabited(x \<Ztypecolon> F T U) \<longrightarrow> Inhabited(f x \<Ztypecolon> T) \<and> Inhabited(g x \<Ztypecolon> U))\<close> *)

subsubsection \<open>Additive Disjunction\<close>

locale Union_Functor = (*is this necessary?*)
  fixes Fa :: \<open>('e, 'a \<Rightarrow> 'd) \<phi> \<Rightarrow> ('c, 'a \<Rightarrow> 'b) \<phi>\<close>
    and Fb :: \<open>('e,'d) \<phi> \<Rightarrow> ('c, 'b) \<phi>\<close>
  assumes union_functor[simp]: \<open>Fa (ExTyp T) = ExTyp (\<lambda>c. Fb (T c))\<close>


subsubsection \<open>Separation\<close>


definition Separation_Homo :: \<open>('b::sep_magma, 'a::sep_magma) \<phi> \<Rightarrow> bool\<close>
  where \<open>Separation_Homo T \<longleftrightarrow> (\<forall>x y. (x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x * y \<Ztypecolon> T \<a>\<n>\<d> x ## y )\<close>

definition \<open>Separation_Homo_unzip T \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> ( (x * y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) ))\<close>

definition \<open>Sep_Type_Functor_zip Ft Fu F3 z \<longleftrightarrow>
              (\<forall>T U x y. (x,y) \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> z (x,y) \<Ztypecolon> F3 (T \<^emph> U))\<close>

definition \<open>Sep_Type_Functor_unzip Ft Fu F3 un \<longleftrightarrow>
              (\<forall>T U z. z \<Ztypecolon> F3 (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> un z \<Ztypecolon> Ft T \<^emph> Fu U)\<close>

definition Scala_Semimodule_Functor :: \<open>('s \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 's::semigroup_mult set \<Rightarrow> bool\<close>
  where \<open>Scala_Semimodule_Functor F T D \<longleftrightarrow> (\<forall>s \<in> D. \<forall>t \<in> D. F s (F t T) = F (t * s) T)\<close>

definition Near_Semimodule_Functor_zip :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Near_Semimodule_Functor_zip F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F s T \<^emph> F t T \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s x \<Ztypecolon> F (t + s) T ))\<close>

definition Near_Semimodule_Functor_zip_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Near_Semimodule_Functor_zip_rev F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F t T \<^emph> F s T \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s x \<Ztypecolon> F (t + s) T ))\<close>

definition Near_Semimodule_Functor_unzip :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a) \<Rightarrow> bool\<close>
  where \<open>Near_Semimodule_Functor_unzip F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F (t + s) T \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T ))\<close>

subsubsection \<open>Intro/Outro Itself\<close>

(*
definition \<open>Intro_Itself_Functor F f1 f2 \<longleftrightarrow>
                (\<forall>T U x y Q. (f1 x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Itself \<a>\<n>\<d> Q) \<longrightarrow> (x \<Ztypecolon> F1 T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> F2 U \<a>\<n>\<d> Q))\<close>

*)


subsection \<open>Configurations\<close>

declare (in homo_one) homo_one_axioms[\<phi>reason 1100]

lemma (in homo_sep_mult) [\<phi>reason 1100]:
  \<open>homo_sep_mult \<psi>\<close>
  by (simp add: homo_sep_mult_axioms)

lemma (in homo_sep_disj_total) [\<phi>reason 1100]:
  \<open>homo_sep_disj_total \<psi>\<close>
  by (simp add: homo_sep_disj_total_axioms)


declare [[
  \<phi>reason_default_pattern_ML
      \<open>Transformation_Functor ?F1 ?F2 _ _\<close> \<Rightarrow> \<open>fn generic => fn term =>
          let val ctxt = Context.proof_of generic
              val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
              val Trueprop $ (_ (*Transformation_Functor*) $ F1 $ F2 $ D $ mapper) = term'
              val ind = Int.max (maxidx_of_term F1, maxidx_of_term F2) + 1
              fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
              val H = Const(\<^const_name>\<open>Transformation_Functor\<close>, TVar(("'TF",ind),[]))
           in [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "D" "'D" $ var "M" "'M"),
               Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "D" "'D" $ var "Ma" "'M")]
          end\<close> (100)
]]

(*The default patterns of the rules are more general here by varifying types.
  This is designed specially.
  In \<^const>\<open>Reverse_Transformation\<close>, as the reverse transformation can have different type,
    and in the algebraic general rule \<open>_Structural_Extract_general_rule'_\<close> the functors are
    represented by variables, it means we have no simple way to varify the type of the functors.
    We use ML (who?) to capture the functor constant and varify the type variables as much as it can
    (we have no way to know the appropriate extend to which it varifies).
    Under such varified types, we set the default pattern of the algebraic properties to be also
    similarly very varified, to hope the rules can still capture the very varified
    reasoning subgoals.
  We only need to over-varify Transformation_Functor and Separation_Functor in such way, because
  only them two are used in the reverse transformation.*)


declare [[
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Transformation_Functor _ _ _ _\<close>,
  \<phi>reason_default_pattern
      \<open>Inhabitance_Functor ?F _\<close> \<Rightarrow> \<open>Inhabitance_Functor ?F _\<close> (100),
  (*\<phi>reason_default_pattern
      \<open>Inhabitance_Functor2 ?F _ _\<close> \<Rightarrow> \<open>Inhabitance_Functor2 ?F _ _\<close> (100),*)
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Inhabitance_Functor _ _\<close>,
  (*\<phi>premise_attribute? [\<phi>reason add] for \<open>Inhabitance_Functor2 _ _ _\<close>,*)

  \<phi>reason_default_pattern_ML \<open>Sep_Type_Functor_zip ?Ft ?Fu _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Functor*) $ F1 $ F2 $ F3 $ f) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Sep_Type_Functor_zip\<close>, TVar(("'SF",ind),[]))
       in [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "z" "'z"),
           Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "z" "'z"),
           Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>reason_default_pattern_ML \<open>Sep_Type_Functor_unzip ?Ft ?Fu _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Functor*) $ F1 $ F2 $ F3 $ f) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Sep_Type_Functor_unzip\<close>, TVar(("'SF",ind),[]))
       in [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "z" "'z"),
           Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "z" "'z"),
           Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>premise_attribute? [\<phi>reason add] for \<open>Sep_Type_Functor_zip _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Sep_Type_Functor_unzip _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Near_Semimodule_Functor_zip _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Near_Semimodule_Functor_zip_rev _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Near_Semimodule_Functor_unzip _ _ _ _\<close>,
  \<phi>reason_default_pattern
      \<open>Near_Semimodule_Functor_zip ?F _ _ _\<close> \<Rightarrow> \<open>Near_Semimodule_Functor_zip ?F _ _ _\<close> (100)
  and \<open>Near_Semimodule_Functor_unzip ?F _ _ _\<close> \<Rightarrow> \<open>Near_Semimodule_Functor_unzip ?F _ _ _\<close> (100)
  and \<open>Near_Semimodule_Functor_zip_rev ?F _ _ _\<close> \<Rightarrow> \<open>Near_Semimodule_Functor_zip_rev ?F _ _ _\<close> (100)
]]


subsection \<open>Applications\<close>

subsubsection \<open>Separation Homo / Functor\<close>


lemma apply_sep_homo:
  \<open> Separation_Homo T
\<Longrightarrow> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x * y \<Ztypecolon> T \<a>\<n>\<d> x ## y\<close>
  unfolding Separation_Homo_def by simp

lemma apply_sep_homo_unzip:
  \<open> Separation_Homo_unzip T
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x ## y
\<Longrightarrow> (x * y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T)\<close>
  unfolding Separation_Homo_unzip_def Premise_def by blast

lemma apply_Separation_Functor_zip:
  \<open> Sep_Type_Functor_zip Ft Fu Fc z
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> z x \<Ztypecolon> Fc(T \<^emph> U)\<close>
  unfolding Sep_Type_Functor_zip_def
  by (cases x; simp)

lemma apply_Separation_Functor_unzip:
  \<open> Sep_Type_Functor_unzip Ft Fu Fc un
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> un x \<Ztypecolon> Ft(T) \<^emph> Fu(U)\<close>
  unfolding Sep_Type_Functor_unzip_def \<phi>Prod_expn'[symmetric]
  by simp

lemma apply_Near_Semimodule_Functor_zip:
  \<open> Near_Semimodule_Functor_zip F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F s T \<^emph> F t T \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s x \<Ztypecolon> F (t + s) T \<close>
  unfolding Near_Semimodule_Functor_zip_def Premise_def
  by blast

lemma apply_Near_Semimodule_Functor_zip_rev:
  \<open> Near_Semimodule_Functor_zip_rev F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F t T \<^emph> F s T \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s x \<Ztypecolon> F (t + s) T \<close>
  unfolding Near_Semimodule_Functor_zip_rev_def Premise_def
  by blast

lemma apply_Near_Semimodule_Functor_unzip:
  \<open> Near_Semimodule_Functor_unzip F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F (t + s) T \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T \<close>
  unfolding Near_Semimodule_Functor_unzip_def Premise_def
  by blast


subsubsection \<open>Transformation Functor\<close>

(*
lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t fa x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> fb y \<Ztypecolon> U \<a>\<n>\<d> Q
\<Longrightarrow> (x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<a>\<n>\<d> Q)\<close>
  unfolding Transformation_Functor_def Argument_def
  by blast

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb mapper
\<Longrightarrow> (fa x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> fb y \<Ztypecolon> U \<a>\<n>\<d> Q)
\<Longrightarrow> (x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<a>\<n>\<d> Q)\<close>
  unfolding Transformation_Functor_def
  by blas
*)

subsection \<open>Reasoning\<close>

subsubsection \<open>Framework\<close>

definition Type_Variant_of_the_Same_Functor :: \<open> 'a \<Rightarrow> 'b \<Rightarrow> bool \<close>
  where \<open> Type_Variant_of_the_Same_Functor Fa Fb \<longleftrightarrow> True \<close>
  \<comment> \<open>Fa and Fb are the same functor but of different type instantiation\<close>

definition Parameter_Variant_of_the_Same_Functor :: \<open> 'a \<Rightarrow> 'b \<Rightarrow> bool \<close>
  where \<open> Parameter_Variant_of_the_Same_Functor Fa Fb \<longleftrightarrow> True \<close>

declare [[
  \<phi>reason_default_pattern
      \<open>Type_Variant_of_the_Same_Functor ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Functor ?Fa _\<close> (100)
  and \<open>Parameter_Variant_of_the_Same_Functor ?Fa _\<close> \<Rightarrow> \<open>Parameter_Variant_of_the_Same_Functor ?Fa _\<close> (100),
  
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Type_Variant_of_the_Same_Functor _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Parameter_Variant_of_the_Same_Functor _ _\<close>
]]

lemma Parameter_Variant_of_the_Same_Functor_I [\<phi>reason 1]:
  \<open>Parameter_Variant_of_the_Same_Functor Fa Fb\<close>
  unfolding Parameter_Variant_of_the_Same_Functor_def ..

lemma Type_Variant_of_the_Same_Functor_I [\<phi>reason 1]:
  \<open>Type_Variant_of_the_Same_Functor Fa Fb\<close>
  unfolding Type_Variant_of_the_Same_Functor_def ..


lemma \<phi>Type_conv_eq_1:
  \<open>T = U \<Longrightarrow> (x \<Ztypecolon> T) = U x\<close>
  unfolding \<phi>Type_def by simp

lemma \<phi>Type_conv_eq_2:
  \<open>T = U \<Longrightarrow> (x \<Ztypecolon> T) = (x \<Ztypecolon> U)\<close>
  unfolding \<phi>Type_def by simp

lemma \<phi>inductive_destruction_rule_from_direct_definition:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> P \<longrightarrow> (R * U \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q)
\<Longrightarrow> P \<longrightarrow> (R * (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q) \<close>
  by simp

lemma \<phi>inductive_destruction_rule_from_direct_definition':
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> P \<longrightarrow> (U \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q)
\<Longrightarrow> P \<longrightarrow> (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q) \<close>
  by simp

lemma \<phi>intro_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T \<a>\<n>\<d> P \<close>
  by simp


ML_file \<open>library/tools/functor_detect.ML\<close>
(* ML_file \<open>library/tools/type_algebra_guess_mapper.ML\<close> *)

(*
datatype yyy = YLeaf nat | YNode nat yyy
datatype ('a,'b) xxx = Leaf 'a | Node nat \<open>('a,'b) xxx\<close>

term xxx.rel_xxx

datatype 'a zzz = AA

ML \<open>val x = the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>xxx\<close>)
val a = BNF_Def.lives_of_bnf x
val s = BNF_Def.sets_of_bnf x
val z = BNF_Def.mk_sets_of_bnf [[],[]] [[\<^typ>\<open>nat\<close>, \<^typ>\<open>int\<close>], [\<^typ>\<open>bool\<close>, \<^typ>\<open>int\<close>]] x\<close>

typ \<open>'a llist\<close>
ML \<open>BNF_Def.bnf_of \<^context> \<^type_name>\<open>yyy\<close>\<close>

ML \<open>val bnf = the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>list\<close>)
val x = BNF_Def.deads_of_bnf bnf
val z = BNF_Def.mk_sets_of_bnf [[]] [[\<^typ>\<open>nat\<close>]] bnf\<close>
ML \<open>BNF_Def.bnf_of \<^context> \<^type_name>\<open>option\<close>\<close>
*)
(* hide_fact \<phi>inductive_destruction_rule_from_direct_definition
          \<phi>inductive_destruction_rule_from_direct_definition'
          \<phi>Type_conv_eq_1 \<phi>Type_conv_eq_2 \<phi>intro_transformation *)

declare conj_imp_eq_imp_imp[simp_for_rule_generation]
        Premise_I[simp_for_rule_generation]


setup \<open>
let fun attach_var F =
      let val i = maxidx_of_term F + 1
       in case fastype_of F of \<^Type>\<open>fun T _\<close> => F $ Var(("uu",i),T)
                             | _ => error "Impossible #8da16473-84ef-4bd8-9a96-331bcff88011"
      end
in Phi_Type_Algebra.Detection_Rewr.setup_attribute \<^binding>\<open>\<phi>functor_of\<close>
  "set the pattern rewrite to parse the functor part and the argument part from a term\
  \ matching the patter"
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Transformation_Functor\<close>
      (fn (_ $ F $ _ $ _ $ _) => F)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Sep_Type_Functor_zip\<close>
      (fn (_ $ F $ _ $ _ $ _ ) => F)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Sep_Type_Functor_unzip\<close>
      (fn (_ $ F $ _ $ _ $ _ ) => F)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Scala_Semimodule_Functor\<close>
      (fn (_ $ F $ _ $ _ ) => attach_var F)
(* #> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Unit_Functor\<close> (fn (_ $ F) => F) *)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Near_Semimodule_Functor_zip\<close>
      (fn (_ $ F $ _ $ _ $ _) => attach_var F)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Near_Semimodule_Functor_zip_rev\<close>
      (fn (_ $ F $ _ $ _ $ _) => attach_var F)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Near_Semimodule_Functor_unzip\<close>
      (fn (_ $ F $ _ $ _ $ _) => attach_var F)
end
\<close>


(* subsubsection \<open>Void Homo / Functor\<close>

lemma [\<phi>reason 30]:
  \<open> Unit_Homo F
\<Longrightarrow> Semi_Unit_Homo F\<close>
  unfolding Semi_Unit_Homo_def Unit_Homo_def
  by simp

lemma [\<phi>reason 30]:
  \<open> Unit_Functor F
\<Longrightarrow> Semi_Unit_Functor F\<close>
  unfolding Semi_Unit_Functor_def Unit_Functor_def
  by blast

lemma Semi_Unit_Homo_by_functor:
  \<open> Semi_Unit_Homo T
\<Longrightarrow> Semi_Unit_Functor F
\<Longrightarrow> Semi_Unit_Homo (F T)\<close>
  unfolding Semi_Unit_Homo_def Semi_Unit_Functor_def
  by (clarsimp; metis set_eq_iff set_in_1)

lemma Unit_Homo_by_functor:
  \<open> Unit_Homo T
\<Longrightarrow> Unit_Functor F
\<Longrightarrow> Unit_Homo (F T)\<close>
  unfolding Unit_Homo_def Unit_Functor_def Imply_def
  by (clarsimp; metis set_eq_iff set_in_1)

\<phi>reasoner_ML Unit_Homo_by_functor 50 (\<open>Unit_Homo _\<close>) = \<open>
fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (_ (*Unit_Homo*) $ T) = Thm.major_prem_of sequent
   in case Phi_Type_Algebra.detect_type_operator 1 ctxt T
        of SOME [Ft,Tt] => let
            val rule = Drule.infer_instantiate ctxt
                          [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                          @{thm "Unit_Homo_by_functor"}
             in SOME ((ctxt, rule RS sequent), Seq.empty) end
         | _ => NONE
  end)
\<close>
*)

subsubsection \<open>Separation Homo / Functor\<close>


(*Separation_Homo is necessary at least for composition \<phi>-type
Separation_Homo B \<longleftrightarrow> Sep_Type_Functor_zip ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x)
*)
lemma Separation_Homo_functor:
  \<open> (\<And>x y z. \<p>\<r>\<e>\<m>\<i>\<s>\<e> (m (\<lambda>(a, b) c. c = b * a \<and> b ## a \<and> (a, b) \<in> D (x, y)) (x, y) z
                        \<longrightarrow> z = y * x \<and> y ## x))
\<Longrightarrow> Sep_Type_Functor_zip F F F' (\<lambda>x. x)
\<Longrightarrow> Transformation_Functor F' F D m
\<Longrightarrow> Separation_Homo T
\<Longrightarrow> Separation_Homo (F T)\<close>
  unfolding Separation_Homo_def Transformation_Functor_def Sep_Type_Functor_zip_def Premise_def
  apply (clarsimp simp add: \<phi>Prod_split[symmetric])
  subgoal premises prems for x y
  proof -
    thm prems
    thm prems(3)[THEN spec[where x=\<open>T \<^emph> T\<close>], THEN spec[where x=T],
                 THEN spec[where x=x], THEN spec[where x=y]]
    have t1: \<open>\<forall>a\<in>D (y, x). a \<Ztypecolon> T \<^emph> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> T \<s>\<u>\<b>\<j> b. (case a of (b, a) \<Rightarrow> \<lambda>c. c = a * b \<and> a ## b \<and> (b, a) \<in> D (y, x)) b\<close>
      by (clarsimp, insert prems(4), blast)
    from prems(3)[THEN spec[where x=\<open>T \<^emph> T\<close>], THEN spec[where x=T],
                 THEN spec[where x=y], THEN spec[where x=x],
                 THEN spec[where x=\<open>\<lambda>(b,a) c. c = a * b \<and> a ## b \<and> (b,a) \<in> D (y,x)\<close>],
                 THEN mp, OF t1]
         prems(1)[of y x]
         prems(2)
    show ?thesis
      by (clarsimp simp add: Imply_def ExSet_expn Subjection_expn; blast)
  qed .


(* \<p>\<r>\<e>\<m>\<i>\<s>\<e> mapper {(a * b, (a, b)) |a b. a ## b} = {(a * b, (a, b)) |a b. a ## b}
\<Longrightarrow>  *)

(* (*Is this really needed?*)
lemma Separation_Homo_eq_functor:
  \<open> (\<And>x y z. \<p>\<r>\<e>\<m>\<i>\<s>\<e> (m (\<lambda>(a, b) c. c = a * b \<and> a ## b \<and> (a, b) \<in> D (x, y)) (x, y) z
                        \<longrightarrow> z = x * y \<and> x ## y))
\<Longrightarrow> Sep_Type_Functor F F F' T T
\<Longrightarrow> Transformation_Functor F F' pred mapper
\<Longrightarrow> Separation_Homo_eq T
\<Longrightarrow> Separation_Homo_eq (F T)\<close>
  unfolding Separation_Homo_eq_def Transformation_Functor_def Sep_Type_Functor_def
            Separation_Homo_def
  apply (clarsimp simp add: \<phi>Prod_split[symmetric])
  subgoal premises prems for x y
  proof -
    thm prems(2)[THEN spec[where x=T], THEN spec[where x=\<open>T \<^emph> T\<close>],
                 THEN spec[where x=\<open>{x*y}\<close>],
                 THEN spec[where x=\<open>{(x * y, (x, y))}\<close>]]
thm prems

  by (simp; metis \<phi>Prod_split) *)

(*
\<phi>reasoner_ML Separation_Homo_functor 50 (\<open>Separation_Homo _\<close>) = \<open>
fn (ctxt, sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (Const(\<^const_name>\<open>Separation_Homo\<close>, _) $ T)
        = Thm.major_prem_of sequent
   in case Phi_Functor_Detect.detect 1 ctxt T
        of SOME [Ft,Tt] => let
            val rule = Drule.infer_instantiate ctxt
                        [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                        @{thm "Separation_Homo_functor"}
            in SOME ((ctxt, rule RS sequent), Seq.empty) end
            handle THM _ => NONE
         | _ => NONE
  end)
\<close>
*)

(*
\<phi>reasoner_ML Separation_Homo_eq_functor 50 (\<open>Separation_Homo_eq _\<close>) = \<open>
fn (ctxt, sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (Const(\<^const_name>\<open>Separation_Homo_eq\<close>, _) $ T)
        = Thm.major_prem_of sequent
   in case Phi_Functor_Detect.detect 1 ctxt T
        of SOME [Ft,Tt] => let
              val rule = Drule.infer_instantiate ctxt
                            [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                            @{thm "Separation_Homo_eq_functor"}
              in SOME ((ctxt, rule RS sequent), Seq.empty) end
              handle THM _ => NONE
         | _ => NONE
  end)
\<close>
*)


subsection \<open>Programming Methods\<close>

subsubsection \<open>Equiv Object\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>x y. \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y \<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> T) M D R F
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (\<phi>Equiv_Obj eq T)) M D R F\<close>
  unfolding \<phi>Programming_Method_def \<phi>Equiv_Obj_def Premise_def
  by clarsimp

subsubsection \<open>Transformation Functor\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>T U x g.
            \<forall>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b
        \<Longrightarrow> x \<Ztypecolon> F1 T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Transformation_Functor F1 F2 D mapper)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Transformation_Functor_def Premise_def
  by clarsimp

subsubsection \<open>Near Semimodule Functor\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F t T) * (x \<Ztypecolon> F s T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s (x,y) \<Ztypecolon> F (t + s) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Near_Semimodule_Functor_zip F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Near_Semimodule_Functor_zip_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s (x,y) \<Ztypecolon> F (t + s) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Near_Semimodule_Functor_zip_rev F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Near_Semimodule_Functor_zip_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T x
          \<Longrightarrow> x \<Ztypecolon> F (t + s) T \<i>\<m>\<p>\<l>\<i>\<e>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Near_Semimodule_Functor_unzip F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Near_Semimodule_Functor_unzip_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')


subsection \<open>Locales for Automation\<close>
 
locale \<phi>Type_Functor =
  fixes F :: \<open>('c,'a) \<phi> \<Rightarrow> ('c1,'a1) \<phi>\<close>
begin
 
declare [[\<phi>functor_of \<open>F ?T\<close> \<Rightarrow> \<open>F\<close> \<open>?T\<close> (31)]]

declaration \<open>fn m => fn ctxt =>
  let val ctxt' = Context.proof_of ctxt
      fun incr_typ_idx protect d tm =
            Term.map_types (Term.map_atyps (
                    fn T as TVar ((N,i),S) =>
                          if member (op =) protect (N,i) then T else TVar ((N,i+d),S)
                     | T => T)) (Thm.term_of tm)
              |> Thm.cterm_of ctxt'
      fun mk_rules tm =
        let val d = Term.maxidx_of_term (Thm.term_of tm) + 1
            val tm' = Thm.incr_indexes_cterm d tm
            val protect_tvars = fold (fn (_,T) => fn L =>
                                          fold (fn (N,_) => fn L' => insert (op =) N L')
                                               (Term.add_tvarsT T []) L)
                                     (Term.add_vars (Thm.term_of tm) []) []
            val tm'T = incr_typ_idx protect_tvars d tm
            val rule = Thm.instantiate (TVars.make [((("'a",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm ),
                                                    ((("'b",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm')],
                                         Vars.make [((("Fa",0), Thm.typ_of_cterm tm ), tm ),
                                                    ((("Fb",0), Thm.typ_of_cterm tm'), tm')])
                                       @{thm Parameter_Variant_of_the_Same_Functor_I}
            val rule'= Thm.instantiate (TVars.make [((("'a",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm ),
                                                    ((("'b",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm'T)],
                                         Vars.make [((("Fa",0), Thm.typ_of_cterm tm ), tm ),
                                                    ((("Fb",0), Thm.typ_of_cterm tm'T), tm'T)])
                                       @{thm Type_Variant_of_the_Same_Functor_I}
         in [rule,rule']
        end
      fun collect_rules ret ctm =
            case Thm.term_of ctm
              of _ $ _ => collect_rules (mk_rules ctm @ ret) (Thm.dest_fun ctm)
               | _ => mk_rules ctm @ ret
      val ctm = Morphism.cterm m \<^cterm>\<open>F\<close>
      val rules = collect_rules [] ctm
      val _ = Phi_Reasoner.info_pretty_generic ctxt 0 (fn () => let open Pretty in
                  chunks (str "Generated reasoning rules: " ::
                          map (fn rule => item [Syntax.pretty_term ctxt' (Thm.prop_of rule)]) rules)
                end)
   in Phi_Reasoner.add_intro_rules (
        map (fn rule => ([rule], \<^here>, Phi_Reasoner.LOCAL_CUT, 1000, [], [], NONE)) rules
        ) ctxt
  end
\<close>

lemma [\<phi>reason add!]:
  \<open>Type_Variant_of_the_Same_Functor F F\<close>
  unfolding Type_Variant_of_the_Same_Functor_def ..

(*priority of the 2-arity functor: 32
  priority of the n-arity functor: 3n
*)

end

(*
context Union_Functor begin
sublocale \<phi>Type_Functor Fb .
end

subsubsection \<open>Unital\<close>


locale Semi_Unit_Homo_L =
  fixes Prem :: bool and T :: \<open>('b::one, 'a::one) \<phi>\<close>
  assumes Semi_Unit_Homo[\<phi>reason 1100]:
    \<open>Prem \<Longrightarrow> Semi_Unit_Homo T\<close>

locale Unit_Homo_L =
  fixes Prem :: bool and T :: \<open>('b::one, 'a::one) \<phi>\<close>
  assumes Unit_Homo[\<phi>reason 1100]: \<open>Prem \<Longrightarrow> Unit_Homo T\<close>
begin

sublocale Semi_Unit_Homo_L
  by (standard; simp add: Unit_Homo[unfolded Unit_Homo_def] Semi_Unit_Homo_def)

end

locale Semi_Unit_Functor_L = \<phi>Type_Functor F
  for Prem :: bool and F :: \<open>('b::one,'a) \<phi> \<Rightarrow> ('c::one,'a) \<phi>\<close>
+ assumes Semi_Unit_Functor[\<phi>reason 1100]: \<open>Prem \<Longrightarrow> Semi_Unit_Functor F\<close>

locale Unit_Functor_L = \<phi>Type_Functor F
  for Prem :: bool and F :: \<open>('b::one,'a) \<phi> \<Rightarrow> ('c::one,'a) \<phi>\<close>
+ assumes Unit_Functor[\<phi>reason 1100]: \<open>Prem \<Longrightarrow> Unit_Functor F\<close>
begin

sublocale Semi_Unit_Functor_L _ F
  by (standard; simp add: Semi_Unit_Functor_def Unit_Functor[unfolded Unit_Functor_def])

end
 *)

subsubsection \<open>Transformation\<close>

lemma Transformation_Functor_L_simp_cong:
  \<open> Transformation_Functor Fa Fa (\<lambda>x. {x}) (\<lambda>x. x)
\<Longrightarrow> (x \<Ztypecolon> T) \<equiv> (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Fa T) \<equiv> (x' \<Ztypecolon> Fa T')\<close>
  unfolding Transformation_Functor_def Imply_def atomize_eq
  apply (auto simp add: \<phi>expns set_eq_iff)
  subgoal premises prems for xa
    using prems(1)[THEN spec[where x=T], THEN spec[where x=T'], THEN spec[where x=x],
            THEN spec[where x=\<open>\<lambda>_ c. c = x'\<close>], simplified]
    using prems(2) prems(3) by blast
  subgoal premises prems for xa
    using prems(1)[THEN spec[where x=T'], THEN spec[where x=T], THEN spec[where x=x'],
            THEN spec[where x=\<open>\<lambda>_ c. c = x\<close>], simplified]
    using prems(2) prems(3) by blast
  .
  

locale Transformation_Functor_L = \<phi>Type_Functor Fa
  for Fa :: \<open>('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>\<close>
+ fixes Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
    and D  :: \<open>'c \<Rightarrow> 'a set\<close>
    and mapper :: \<open>('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool\<close>
    and Prem :: bool
  assumes Transformation_Functor[\<phi>reason 1100]:
    \<open>Prem \<Longrightarrow> Transformation_Functor Fa Fb D mapper\<close>
begin

lemma transformation[\<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> Fb _ \<s>\<u>\<b>\<j> y. _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>
  unfolding meta_Ball_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def]
  by blast

declaration \<open>fn m => fn ctxt =>
  let val rule = Morphism.thm m @{thm Transformation_Functor}
      val thy = Context.theory_of ctxt
   in if Pattern.matches thy (\<^pattern>\<open>True \<Longrightarrow> Transformation_Functor _ _ (\<lambda>x. {x}) (\<lambda>x. x)\<close>, Thm.prop_of rule)
      then let
        val rule' = (@{thm TrueI} RS rule) RS @{thm Transformation_Functor_L_simp_cong}
        val (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ LHS $ _) = Thm.concl_of rule'
         in Simplifier.map_ss (fn ctxt =>
              ctxt addsimprocs [Simplifier.cert_simproc thy "Transformation_Functor_L.\<phi>simp_cong" {
                lhss = [LHS],
                proc = K (Phi_SimpCong.simproc rule')
              }]
            ) ctxt
        end
      else ctxt
  end\<close>

end



locale Functional_Transformation_Functor_L =
  Transformation_Functor_L Fa Fb D mapper Prem
  for Fa :: \<open>('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>\<close>
  and Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
  and D  :: \<open>'c \<Rightarrow> 'a set\<close>
  and mapper :: \<open>('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool\<close> \<comment> \<open>relational mapper\<close>
  and Prem :: bool
+ fixes pred_mapper :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> bool\<close>
    and func_mapper :: \<open>('a \<Rightarrow> 'e) \<Rightarrow> 'c \<Rightarrow> 'f\<close>
  assumes functional_mapper:
      \<open>mapper (\<lambda>a b. b = f a \<and> P a) = (\<lambda>a' b'. b' = func_mapper f a' \<and> pred_mapper P a')\<close>
  and pred_mapper_constant:
      \<open>pred_mapper (\<lambda>x. Q \<and> P x) x \<longleftrightarrow> Q \<and> pred_mapper P x\<close>

setup \<open>Phi_Type_Algebra.add_property_kind "Phi_Type_Algebra.Functional_Transformation_Functor_L"
            (fn (_ $ F $ _ $ _ $ _ $ _ $ _ $ _) => F)\<close>

context Functional_Transformation_Functor_L
begin
 
lemma [\<phi>reason add]:
  \<open>Functional_Transformation_Functor_L Fa Fb D mapper Prem pred_mapper func_mapper\<close>
  by (simp add: Functional_Transformation_Functor_L_axioms)

lemma [\<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> Fb _ \<a>\<n>\<d> _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f a \<Ztypecolon> U \<a>\<n>\<d> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. f a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> func_mapper f x \<Ztypecolon> Fb U \<a>\<n>\<d> pred_mapper P x\<close>
  unfolding meta_Ball_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], unfolded functional_mapper,
          simplified]
  by blast

lemma functional_transformation:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f a \<Ztypecolon> U \<a>\<n>\<d> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. f a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> func_mapper f x \<Ztypecolon> Fb U \<a>\<n>\<d> pred_mapper P x\<close>
  unfolding meta_Ball_def Argument_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], unfolded functional_mapper,
          simplified]
  by blast

end

hide_fact Transformation_Functor_L_simp_cong


subsubsection \<open>Type-Functor for Separation\<close>

locale Sep_Homo_Type_Functor_L =
  fixes Ft :: \<open>('b::sep_magma,'a) \<phi> \<Rightarrow> ('d::sep_magma,'c) \<phi>\<close>
    and Fu :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
    and Fc :: \<open>('b,'a \<times> 'e) \<phi> \<Rightarrow> ('d,'c \<times> 'f) \<phi>\<close>
    and Prem :: bool
  assumes sep_homo_type: \<open>Prem \<Longrightarrow> Ft(T) \<^emph> Fu(U) = Fc (T \<^emph> U)\<close>
begin

lemma [\<phi>reason add]:
  \<open>Prem \<Longrightarrow> Sep_Type_Functor_zip Ft Fu Fc (\<lambda>x. x)\<close>
  unfolding Sep_Type_Functor_zip_def sep_homo_type by simp

lemma [\<phi>reason add]:
  \<open>Prem \<Longrightarrow> Sep_Type_Functor_unzip Ft Fu Fc (\<lambda>x. x)\<close>
  unfolding Sep_Type_Functor_unzip_def sep_homo_type by simp

end


subsubsection \<open>Fun upd\<close>

declare homo_sep_disj_total_comp[\<phi>reason 50]
        homo_sep_comp[\<phi>reason 50]
        homo_sep_mult_comp[\<phi>reason 50]

lemma [\<phi>reason 50]:
  \<open> homo_sep_disj_total \<psi>
\<Longrightarrow> homo_sep_disj_semi \<psi>\<close>
  unfolding homo_sep_disj_semi_def homo_sep_disj_total_def
  by blast

lemma homo_sep_disj_total_fun_upd [\<phi>reason 1100]:
  \<open>homo_sep_disj_total (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k)\<close>
  unfolding homo_sep_disj_total_def
  by (simp add: sep_disj_fun_def)

lemma homo_sep_disj_total_fun_upd' [\<phi>reason 1050]:
  \<open> homo_sep_disj_total f
\<Longrightarrow> homo_sep_disj_total (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x))\<close>
  unfolding homo_sep_disj_total_def
  by (simp add: sep_disj_fun_def)

lemma homo_sep_mult_fun_upd[\<phi>reason 1100]:
  \<open>homo_sep_mult (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k)\<close>
  unfolding homo_sep_mult_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_sep_mult_fun_upd'[\<phi>reason 1050]:
  \<open> homo_sep_mult f
\<Longrightarrow> homo_sep_mult (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x))\<close>
  unfolding homo_sep_mult_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_one_fun_upd[\<phi>reason 1100]:
  \<open>homo_one (fun_upd 1 k)\<close>
  unfolding homo_one_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_one_fun_upd'[\<phi>reason 1050]:
  \<open> homo_one f
\<Longrightarrow> homo_one (\<lambda>x. fun_upd 1 k (f x))\<close>
  unfolding homo_one_def
  by (simp add: fun_eq_iff times_fun_def)


subsubsection \<open>Push map\<close>

declare homo_sep_disj_total_push_map [\<phi>reason 1100]
        homo_sep_mult_push_map [\<phi>reason 1100]
        homo_one_push_map [\<phi>reason 1100]


subsection \<open>Auto Generation of Properties\<close>

subsubsection \<open>General Rules\<close>

lemma mk_ToA_rule:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<a>\<n>\<d> Q
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> Q \<and> P\<close>
  using implies_trans by blast

lemma mk_ToA_rule':
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> A \<brangle> \<a>\<n>\<d> Q
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> B \<brangle> \<a>\<n>\<d> Q \<and> P\<close>
  unfolding FOCUS_TAG_def
  using implies_left_prod mk_ToA_rule by blast

lemma conv_intro_premise:
  \<open>P \<Longrightarrow> X \<equiv> (P \<longrightarrow> X)\<close>
  by simp

lemma [fundef_cong]:
  \<open>T x = T' x' \<Longrightarrow> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')\<close>
  unfolding \<phi>Type_def by simp


subsubsection \<open>Is_Stateless\<close>

lemma
  \<open>\<close>

subsubsection \<open>\<phi>Equiv_Obj\<close>

lemma \<phi>Equiv_Obj_rule:
  \<open> (\<And>x. Ant \<longrightarrow> (\<forall>y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> T)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> \<phi>Equiv_Obj eq T \<close>
  unfolding \<phi>Equiv_Obj_def Premise_def
  by blast

lemma \<phi>Equiv_Obj_rule_move_all:
  \<open>(\<And>x. P x \<and> Q) \<Longrightarrow> (\<forall>x. P x) \<and> Q\<close>
  by blast

lemma \<phi>Equiv_Obj_rule_move_all2:
  \<open>(P \<longrightarrow> (\<forall>x. Q x)) \<and> R \<Longrightarrow> (\<forall>x. P \<longrightarrow> Q x) \<and> R\<close>
  by blast

lemma \<phi>Equiv_Obj_rule_move_set_eq:
  \<open>RR \<Longrightarrow> (R \<and> P \<and> R2 \<longrightarrow> P) \<and> RR\<close>
  by blast

lemma \<phi>Equiv_Obj_rule_move_set_eq_end:
  \<open>(P \<and> R \<longrightarrow> P)\<close>
  by blast

thm imp_conjR[folded atomize_eq, symmetric]
thm simp_thms(17)[folded atomize_eq]
thm simp_thms(15)[folded atomize_eq]

ML_file \<open>library/automation/type_algebra.ML\<close>

thm Action_Tag_D[where A = \<open>ToSA\<close>]

hide_fact \<phi>Equiv_Obj_rule_move_all \<phi>Equiv_Obj_rule_move_set_eq \<phi>Equiv_Obj_rule_move_set_eq_end
          \<phi>Equiv_Obj_rule_move_all2

lemmas [\<phi>constraint_expansion] = HOL.simp_thms ex_simps[symmetric]
          list_all2_Cons1 list_all2_Nil
lemmas [\<phi>type_algebra_normalize_ToA_ss] = HOL.simp_thms implies_refl

subsubsection \<open>Transformation Functor\<close>

lemma
  \<open>(\<And>T U x g a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<Longrightarrow> a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> Transformation_Functor F1 F2 D mapper\<close>

thm Transformation_Functor_def
thm atomize_imp

(* ML_file \<open>library/system/phi_type_definition.ML\<close> *)


end
