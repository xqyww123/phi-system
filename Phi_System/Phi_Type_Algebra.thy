theory Phi_Type_Algebra
  imports IDE_CP_Applications1
  keywords "\<phi>type_def" "\<phi>property_deriver" :: thy_defn
       and "deriving" :: quasi_command
begin

section \<open>The Algebra of \<open>\<phi>\<close>-Refinement\<close>

subsection \<open>Definitions\<close>



(*
subsubsection \<open>Unit\<close>

definition \<open>Unit_Homo T \<longleftrightarrow> (1 \<Ztypecolon> T) = 1\<close>
definition \<open>Semi_Unit_Homo T \<longleftrightarrow> ((1 \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1)\<close>
definition \<open>Semi_Unit_Functor F \<longleftrightarrow> (\<forall>x T. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1) \<longrightarrow> (x \<Ztypecolon> F T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1))\<close> *)

(*
definition \<open>Unit_Functor F \<longleftrightarrow> (\<forall>x T. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1) \<longrightarrow> (x \<Ztypecolon> F T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1)) \<and>
                               (\<forall>x T. (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T) \<longrightarrow> (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F T))\<close> *)


subsubsection \<open>Transformation\<close>

definition \<open>Transformation_Functor F1 F2 D mapper \<longleftrightarrow>
  (\<forall>T U x g. (\<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b) \<longrightarrow>
               (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y))\<close>
  \<comment> \<open>f1 and d1 make the domain set.

  The definition is given in reasoning-friendly form and should entail, (TODO: verify!)

  definition \<open>Transformation_Functor F1 F2 mapper \<longleftrightarrow>
    (\<forall>T U r x. (\<forall>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. (x,y) \<in> r) \<longrightarrow>
               (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. (x,y) \<in> mapper r))\<close>,
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

lemma Transformation_Functor_sub_mapper:
  \<open> ma \<le> mb
\<Longrightarrow> Transformation_Functor F1 F2 D ma
\<Longrightarrow> Transformation_Functor F1 F2 D mb\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: le_fun_def Transformation_def Ball_def ExSet_expn Subjection_expn, blast)

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb D mapper
\<Longrightarrow> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<close>
  unfolding Transformation_Functor_def Premise_def
  by simp



subsubsection \<open>Inhabitance\<close>

(*depreciated!*)
definition \<open>Inhabitance_Functor F f \<longleftrightarrow> (\<forall>T x. Inhabited(x \<Ztypecolon> F T) \<longrightarrow> Inhabited(f x \<Ztypecolon> T))\<close>
(* definition \<open>Inhabitance_Functor2 F f g \<longleftrightarrow> (\<forall>T U x. Inhabited(x \<Ztypecolon> F T U) \<longrightarrow> Inhabited(f x \<Ztypecolon> T) \<and> Inhabited(g x \<Ztypecolon> U))\<close> *)

(* subsubsection \<open>Additive Disjunction\<close>

Is still useful, may need a specific automation, not implied from TF

locale Union_Functor = (*is this necessary?*)
  fixes Fa :: \<open>('e, 'a \<Rightarrow> 'd) \<phi> \<Rightarrow> ('c, 'a \<Rightarrow> 'b) \<phi>\<close>
    and Fb :: \<open>('e,'d) \<phi> \<Rightarrow> ('c, 'b) \<phi>\<close>
  assumes union_functor[simp]: \<open>Fa (ExTyp T) = ExTyp (\<lambda>c. Fb (T c))\<close> *)


subsubsection \<open>Separation\<close>


definition Separation_Homo_Obj :: \<open>('b::sep_magma, 'a::sep_magma) \<phi> \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool\<close>
  where \<open>Separation_Homo_Obj T D \<longleftrightarrow> (\<forall>x y. (y,x) \<in> D \<longrightarrow> ((x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> T \<w>\<i>\<t>\<h> x ## y ))\<close>

definition \<open>Separation_Homo_unzip T \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> ( (x * y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) ))\<close>

definition \<open>Separation_Homo\<^sub>I Ft Fu F3 D z \<longleftrightarrow>
              (\<forall>T U x y. (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (T \<^emph> U)))\<close>

definition \<open>Separation_Homo\<^sub>E Ft Fu F3 un \<longleftrightarrow>
              (\<forall>T U z. z \<Ztypecolon> F3 (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph> Fu U)\<close>

definition Scala_Semimodule_Functor :: \<open>('s \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 's::semigroup_mult set \<Rightarrow> bool\<close>
  where \<open>Scala_Semimodule_Functor F T D \<longleftrightarrow> (\<forall>s \<in> D. \<forall>t \<in> D. F s (F t T) = F (t * s) T)\<close>

definition Near_Semimodule_Functor_zip :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Near_Semimodule_Functor_zip F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F s T \<^emph> F t T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T ))\<close>

definition Near_Semimodule_Functor_zip_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Near_Semimodule_Functor_zip_rev F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T ))\<close>

definition Near_Semimodule_Functor_unzip :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a) \<Rightarrow> bool\<close>
  where \<open>Near_Semimodule_Functor_unzip F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F (t + s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T ))\<close>

subsubsection \<open>Intro/Outro Itself\<close>

(*
definition \<open>Intro_Itself_Functor F f1 f2 \<longleftrightarrow>
                (\<forall>T U x y Q. (f1 x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<w>\<i>\<t>\<h> Q) \<longrightarrow> (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<w>\<i>\<t>\<h> Q))\<close>

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
           in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "D" "'D" $ var "M" "'M"),
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
      \<open>Inhabitance_Functor ?F _\<close> \<Rightarrow> \<open>Inhabitance_Functor ?F _\<close> (100)
  and \<open>Separation_Homo_Obj ?T _\<close> \<Rightarrow> \<open>Separation_Homo_Obj ?T _\<close> (100),
  (*\<phi>reason_default_pattern
      \<open>Inhabitance_Functor2 ?F _ _\<close> \<Rightarrow> \<open>Inhabitance_Functor2 ?F _ _\<close> (100),*)
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Inhabitance_Functor _ _\<close>,
  (*\<phi>premise_attribute? [\<phi>reason add] for \<open>Inhabitance_Functor2 _ _ _\<close>,*)

  \<phi>reason_default_pattern_ML \<open>Separation_Homo\<^sub>I ?Ft ?Fu _ _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Functor*) $ F1 $ F2 $ F3 $ D $ f) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, TVar(("'SF",ind),[]))
       in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "D" "'d" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "D" "'d" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "D" "'d" $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>reason_default_pattern_ML \<open>Separation_Homo\<^sub>E ?Ft ?Fu _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Functor*) $ F1 $ F2 $ F3 $ f) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, TVar(("'SF",ind),[]))
       in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>I _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>E _ _ _ _\<close>,
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
  \<open> Separation_Homo_Obj T D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (y,x) \<in> D
\<Longrightarrow> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> T \<w>\<i>\<t>\<h> x ## y\<close>
  unfolding Separation_Homo_Obj_def Premise_def by simp

lemma apply_sep_homo_unzip:
  \<open> Separation_Homo_unzip T
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x ## y
\<Longrightarrow> (x * y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T)\<close>
  unfolding Separation_Homo_unzip_def Premise_def by blast

lemma apply_Separation_Functor_zip:
  \<open> Separation_Homo\<^sub>I Ft Fu Fc D z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z x \<Ztypecolon> Fc(T \<^emph> U)\<close>
  unfolding Separation_Homo\<^sub>I_def Premise_def
  by (cases x; simp)

lemma apply_Separation_Functor_unzip:
  \<open> Separation_Homo\<^sub>E Ft Fu Fc un
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph> Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'[symmetric]
  by simp

lemma apply_Near_Semimodule_Functor_zip:
  \<open> Near_Semimodule_Functor_zip F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F s T \<^emph> F t T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T \<close>
  unfolding Near_Semimodule_Functor_zip_def Premise_def
  by blast

lemma apply_Near_Semimodule_Functor_zip_rev:
  \<open> Near_Semimodule_Functor_zip_rev F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T \<close>
  unfolding Near_Semimodule_Functor_zip_rev_def Premise_def
  by blast

lemma apply_Near_Semimodule_Functor_unzip:
  \<open> Near_Semimodule_Functor_unzip F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F (t + s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T \<close>
  unfolding Near_Semimodule_Functor_unzip_def Premise_def
  by blast


subsubsection \<open>Transformation Functor\<close>

(*
lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t fa x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fb y \<Ztypecolon> U \<w>\<i>\<t>\<h> Q
\<Longrightarrow> (x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> Q)\<close>
  unfolding Transformation_Functor_def Argument_def
  by blast

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb mapper
\<Longrightarrow> (fa x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fb y \<Ztypecolon> U \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> (x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> Q)\<close>
  unfolding Transformation_Functor_def
  by blas
*)

subsection \<open>Reasoning\<close>

subsubsection \<open>Convention\<close>

text \<open>
Priority:
\<^item> 30: inductively introduction ToA

\<close>

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
\<Longrightarrow> P \<longrightarrow> (R * U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> P \<longrightarrow> (R * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q) \<close>
  by simp

lemma \<phi>inductive_destruction_rule_from_direct_definition':
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> P \<longrightarrow> (U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> P \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q) \<close>
  by simp

lemma \<phi>intro_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma \<phi>intro'_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * U \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * (x \<Ztypecolon> T) \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma \<phi>gen_expansion:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> p \<Turnstile> (x \<Ztypecolon> T) \<equiv> p \<Turnstile> U \<close>
  by simp






ML_file \<open>library/tools/functor_detect.ML\<close>
(* ML_file \<open>library/tools/type_algebra_guess_mapper.ML\<close> *)


datatype yyy = YLeaf nat | YNode nat yyy
datatype ('a,'b) xxx = Leaf 'a | LeafB 'b | Node nat \<open>('a,'b) xxx\<close>

term xxx.rel_xxx
thm xxx.set




datatype 'a zzz = AA

ML \<open>val x = the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>xxx\<close>)
val a = BNF_Def.lives_of_bnf x
val s = BNF_Def.sets_of_bnf x
val z = BNF_Def.mk_sets_of_bnf [[],[]] [[\<^typ>\<open>nat\<close>, \<^typ>\<open>int\<close>], [\<^typ>\<open>bool\<close>, \<^typ>\<open>int\<close>]] x
val d = BNF_Def.set_transfer_of_bnf x\<close>

ML \<open>#fp_res (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>xxx\<close>))
|> #ctor_injects\<close>

declare [[ML_print_depth = 1000]]

ML \<open>#fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>xxx\<close>))
|> #ctr_sugar
\<close>

ML \<open>BNF_Def.map_def_of_bnf (the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>list\<close>))\<close>

ML \<open>#fp_bnf_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))\<close>

ML \<open>local val bnf = (the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>list\<close>))
in 
val xx = BNF_Def.pred_mono_of_bnf bnf
end\<close>

thm list.rel_eq

ML \<open>(the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))\<close>

ML \<open>
val ths = #fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))
|> #ctr_sugar
|> #disc_thmss
|> flat
val ((_,ths2),_) = Variable.import true ths \<^context>
val xxx = ths2
|> map (Simplifier.asm_simplify (Simplifier.clear_simpset \<^context> addsimps @{thms HOL.simp_thms ex_simps[symmetric]}))
|> filter (fn th => (case Thm.concl_of th of \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> => false | _ => true))
|> distinct (Thm.equiv_thm \<^theory>)
\<close>

ML \<open>    
    val equal_binding = \<^binding>\<open>=\<close>;

fun is_disc_binding_valid b =
      not (Binding.is_empty b orelse Binding.eq_name (b, equal_binding));
\<close>

thm list.collapse


ML \<open>#fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))\<close>

ML \<open>BNF_Def.bnf_of \<^context> \<^type_name>\<open>yyy\<close>\<close>

ML \<open>local val bnf = the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>list\<close>) in
val x = BNF_Def.deads_of_bnf bnf
val z = BNF_Def.mk_sets_of_bnf [[]] [[\<^typ>\<open>nat\<close>]] bnf
end\<close>
ML \<open>BNF_Def.bnf_of \<^context> \<^type_name>\<open>option\<close>\<close>

(* hide_fact \<phi>inductive_destruction_rule_from_direct_definition
          \<phi>inductive_destruction_rule_from_direct_definition'
          \<phi>Type_conv_eq_1 \<phi>Type_conv_eq_2 \<phi>intro_transformation *)

declare conj_imp_eq_imp_imp[simp_for_\<phi>TA_rule_generation]
        Premise_I[simp_for_\<phi>TA_rule_generation]


setup \<open>
let fun attach_var F =
      let val i = maxidx_of_term F + 1
       in case fastype_of F of \<^Type>\<open>fun T _\<close> => F $ Var(("uu",i),T)
                             | _ => error "Impossible #8da16473-84ef-4bd8-9a96-331bcff88011"
      end
in (*Phi_Type_Algebra.Detection_Rewr.setup_attribute \<^binding>\<open>\<phi>functor_of\<close>
  "set the pattern rewrite to parse the functor part and the argument part from a term\
  \ matching the patter"
#>*) Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Transformation_Functor\<close>
      (fn (_ $ F $ _ $ _ $ _) => F)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Separation_Homo\<^sub>I\<close>
      (fn (_ $ F $ _ $ _ $ _ $ _ ) => F)
#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Separation_Homo\<^sub>E\<close>
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
  unfolding Unit_Homo_def Unit_Functor_def Transformation_def
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

lemma Separation_Homo_Obj_subdom[\<phi>reason default 1]:
  \<open> Separation_Homo_Obj T Da
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Db \<subseteq> Da
\<Longrightarrow> Separation_Homo_Obj T Db\<close>
  unfolding Separation_Homo_Obj_def Premise_def subset_iff
  by blast

(*Separation_Homo_Obj is necessary at least for composition \<phi>-type
Separation_Homo_Obj B \<longleftrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x)
*)

lemma Separation_Homo_functor[\<phi>reason_template 50]:
  \<open> Separation_Homo\<^sub>I F F F' Ds (\<lambda>x. x) \<comment> \<open>TODO: isn't this \<open>(\<lambda>x. x)\<close> too strong?\<close>
\<Longrightarrow> Transformation_Functor F' F D m
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x y z. m (\<lambda>(a, b) c. c = b * a \<and> b ## a \<and> (a, b) \<in> D (x, y)) (x, y) z
                        \<longrightarrow> z = y * x \<and> y ## x)
\<Longrightarrow> Separation_Homo_Obj T (Set.bind Ds D)
\<Longrightarrow> Separation_Homo_Obj (F T) Ds\<close>
  unfolding Separation_Homo_Obj_def Transformation_Functor_def Separation_Homo\<^sub>I_def Premise_def
  apply (clarsimp simp add: \<phi>Prod_expn'[symmetric])
  subgoal premises prems for x y
  proof -
    have t1: \<open>\<forall>a\<in>D (y, x). a \<Ztypecolon> T \<^emph> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> T \<s>\<u>\<b>\<j> b. (case a of (b, a) \<Rightarrow> \<lambda>c. c = a * b \<and> a ## b \<and> (b, a) \<in> D (y, x)) b\<close>
      by (clarsimp, insert prems(4,5), blast)
    from prems(2)[THEN spec[where x=\<open>T \<^emph> T\<close>], THEN spec[where x=T],
                 THEN spec[where x=y], THEN spec[where x=x],
                 THEN spec[where x=\<open>\<lambda>(b,a) c. c = a * b \<and> a ## b \<and> (b,a) \<in> D (y,x)\<close>],
                 THEN mp, OF t1]
         prems(3)[THEN spec[where x=y], THEN spec[where x=x]]
         prems(1)
         prems(5)
    show ?thesis
      by (clarsimp simp add: Transformation_def, blast)
  qed .


(* \<p>\<r>\<e>\<m>\<i>\<s>\<e> mapper {(a * b, (a, b)) |a b. a ## b} = {(a * b, (a, b)) |a b. a ## b}
\<Longrightarrow>  *)

(* (*Is this really needed?*)
lemma Separation_Homo_eq_functor:
  \<open> (\<And>x y z. \<p>\<r>\<e>\<m>\<i>\<s>\<e> (m (\<lambda>(a, b) c. c = a * b \<and> a ## b \<and> (a, b) \<in> D (x, y)) (x, y) z
                        \<longrightarrow> z = x * y \<and> x ## y))
\<Longrightarrow> Sep_Homo_Ty F F F' T T
\<Longrightarrow> Transformation_Functor F F' pred mapper
\<Longrightarrow> Separation_Homo_eq T
\<Longrightarrow> Separation_Homo_eq (F T)\<close>
  unfolding Separation_Homo_eq_def Transformation_Functor_def Sep_Homo_Ty_def
            Separation_Homo_Obj_def
  apply (clarsimp simp add: \<phi>Prod_split[symmetric])
  subgoal premises prems for x y
  proof -
    thm prems(2)[THEN spec[where x=T], THEN spec[where x=\<open>T \<^emph> T\<close>],
                 THEN spec[where x=\<open>{x*y}\<close>],
                 THEN spec[where x=\<open>{(x * y, (x, y))}\<close>]]
thm prems

  by (simp; metis \<phi>Prod_split) *)

(*
\<phi>reasoner_ML Separation_Homo_functor 50 (\<open>Separation_Homo_Obj _\<close>) = \<open>
fn (ctxt, sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (Const(\<^const_name>\<open>Separation_Homo_Obj\<close>, _) $ T)
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
  \<open> PROP \<phi>Programming_Method (\<And>x y. \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T) M D R F
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Object_Equiv T eq)) M D R F\<close>
  unfolding \<phi>Programming_Method_def Object_Equiv_def Premise_def
  by clarsimp

subsubsection \<open>Transformation Functor\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>T U x g.
            \<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b
        \<Longrightarrow> x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Transformation_Functor F1 F2 D mapper)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Transformation_Functor_def Premise_def
  by clarsimp

subsubsection \<open>Near Semimodule Functor\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F t T) * (x \<Ztypecolon> F s T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s (x,y) \<Ztypecolon> F (t + s) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Near_Semimodule_Functor_zip F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Near_Semimodule_Functor_zip_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s (x,y) \<Ztypecolon> F (t + s) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Near_Semimodule_Functor_zip_rev F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Near_Semimodule_Functor_zip_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T x
          \<Longrightarrow> x \<Ztypecolon> F (t + s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Near_Semimodule_Functor_unzip F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Near_Semimodule_Functor_unzip_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')


subsection \<open>Locales for Automation\<close>
 
locale \<phi>Type_Functor =
  fixes F :: \<open>('c,'a) \<phi> \<Rightarrow> ('c1,'a1) \<phi>\<close>
begin
 
(* declare [[\<phi>functor_of \<open>F ?T\<close> \<Rightarrow> \<open>F\<close> \<open>?T\<close> (31)]] *)

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
    (* val _ = Phi_Reasoner.info_pretty_generic ctxt 0 (fn () => let open Pretty in
                  chunks (str "Generated reasoning rules: " ::
                          map (fn rule => item [Syntax.pretty_term ctxt' (Thm.prop_of rule)]) rules)
                end) *)
   in Phi_Reasoner.add_intro_rules (
        map (fn rule => ([rule], \<^here>, Phi_Reasoner.LOCAL_CUT, 1000, [], [], NONE)) rules
        ) ctxt
  end
\<close>

(*
lemma [\<phi>reason add!]:
  \<open>Type_Variant_of_the_Same_Functor F F\<close>
  unfolding Type_Variant_of_the_Same_Functor_def ..*)

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
  unfolding Transformation_Functor_def Transformation_def atomize_eq
  apply (auto simp add: BI_eq_iff)
  subgoal premises prems for xa
    using prems(1)[THEN spec[where x=T], THEN spec[where x=T'], THEN spec[where x=x],
            THEN spec[where x=\<open>\<lambda>_ c. c = x'\<close>], simplified]
    using prems(2) prems(3) by blast
  subgoal premises prems for xa
    using prems(1)[THEN spec[where x=T'], THEN spec[where x=T], THEN spec[where x=x'],
            THEN spec[where x=\<open>\<lambda>_ c. c = x\<close>], simplified]
    using prems(2) prems(3) by blast
  .

attribute_setup \<phi>TA_internal_simplify_special_cases = \<open>Scan.succeed (
  let fun rule_attribute f (x, th) =
            if Thm.is_free_dummy th
            then (NONE, NONE)
            else (SOME x, SOME (f x th))
   in rule_attribute (fn generic => fn rule =>
        let val ctxt = Context.proof_of generic
            val sctxt = Simplifier.clear_simpset ctxt addsimps @{thms meta_Ball_simp}
            val rule' = Simplifier.full_simplify sctxt rule
                      |> Phi_Help.instantiate_higher_order_schematic_var ~2 ctxt
         in rule'
        end)
  end
)\<close>

 
locale Transformation_Functor_L = \<phi>Type_Functor Fa
  for Fa :: \<open>('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>\<close>
+ fixes Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
    and D  :: \<open>'c \<Rightarrow> 'a set\<close>
    and mapper :: \<open>('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool\<close>
    and Prem :: bool
  assumes Transformation_Functor[\<phi>reason 1100]:
    \<open>Prem \<Longrightarrow> Transformation_Functor Fa Fb D mapper\<close>
begin

lemma transformation[\<phi>TA_internal_simplify_special_cases,
                     \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Fb _ \<s>\<u>\<b>\<j> y. _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>
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
                proc = K (Phi_SimpProc.cong rule')
              }]
            ) ctxt
        end
      else ctxt
  end\<close>

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<s>\<u>\<b>\<j> y. _ @action \<A>_structural _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>_structural Act)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using transformation .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<s>\<u>\<b>\<j> y. _ @action as _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action as Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action as Z \<close>
  unfolding Action_Tag_def
  using transformation .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fb Z) \<close>
  unfolding Action_Tag_def
  using transformation .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 36]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to Z \<close>
  unfolding Action_Tag_def
  using transformation .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 41]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (Z' \<f>\<o>\<r> Z))
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fa Z' \<f>\<o>\<r> Fb Z) \<close>
  unfolding Action_Tag_def
  using transformation .

end
  
lemma [\<phi>reason_template default 53 requires Separation_Homo\<^sub>E]:
  \<open> Transformation_Functor Fa Fb D mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (\<s>\<p>\<l>\<i>\<t> Z))
\<Longrightarrow> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action \<A>\<T>split_step
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action to (\<s>\<p>\<l>\<i>\<t> (Fa Z)) \<close>
  unfolding Action_Tag_def meta_Ball_def Premise_def Transformation_Functor_def Ball_def
  by (rule implies_trans[where P=True and Q=True and B=\<open>y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>, simplified], blast)

lemma [\<phi>reason_template default 50 requires Separation_Homo\<^sub>E]:
  \<open> Transformation_Functor Fa Fb D mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (\<s>\<p>\<l>\<i>\<t> Z))
\<Longrightarrow> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action \<A>\<T>split_step
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action to (\<s>\<p>\<l>\<i>\<t> Z) \<close>
  unfolding Action_Tag_def meta_Ball_def Premise_def Transformation_Functor_def Ball_def
  by (rule implies_trans[where P=True and Q=True and B=\<open>y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>, simplified], blast)

lemma [\<phi>reason_template default 50]:
  \<open> Separation_Homo\<^sub>E Fa\<^sub>L Fa\<^sub>R Fb un
\<Longrightarrow> y \<Ztypecolon> Fb (U\<^sub>L \<^emph> U\<^sub>R) \<s>\<u>\<b>\<j> y. r y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Fa\<^sub>L U\<^sub>L \<^emph> Fa\<^sub>R U\<^sub>R \<s>\<u>\<b>\<j> z. (\<exists>z'. z = un z' \<and> r z') @action \<A>\<T>split_step\<close> (*TODO: this syntactic priority*)
  unfolding Separation_Homo\<^sub>E_def Action_Tag_def
  by (clarsimp simp add: Subjection_transformation_expn Ex_transformation_expn
                  intro!: ExSet_imp_I Subjection_imp_I,
      rule implies_weaken[where P=True], blast, blast)

lemma [\<phi>reason default 1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>\<T>split_step\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action \<A>\<T>split_step \<close>
  unfolding Action_Tag_def by simp


locale Functional_Transformation_Functor =
  Transformation_Functor_L Fa Fb D mapper Prem
  for Fa :: \<open>('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>\<close>
  and Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
  and D  :: \<open>'c \<Rightarrow> 'a set\<close>
  and mapper :: \<open>('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool\<close> \<comment> \<open>relational mapper\<close>
  and Prem :: bool
+ fixes pred_mapper :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> bool\<close>
    and func_mapper :: \<open>('a \<Rightarrow> 'e) \<Rightarrow> 'c \<Rightarrow> 'f\<close>
  assumes functional_mapper:
      \<open>Prem \<Longrightarrow> mapper (\<lambda>a b. b = f a \<and> P a) = (\<lambda>a' b'. b' = func_mapper f a' \<and> pred_mapper P a')\<close>

setup \<open>Phi_Type_Algebra.add_property_kind "Phi_Type_Algebra.Functional_Transformation_Functor"
            (fn (_ $ F $ _ $ _ $ _ $ _ $ _ $ _) => F)\<close>

context Functional_Transformation_Functor
begin

lemma [\<phi>reason add]:
  \<open>Functional_Transformation_Functor Fa Fb D mapper Prem pred_mapper func_mapper\<close>
  by (simp add: Functional_Transformation_Functor_axioms)

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Fb _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x\<close>
  unfolding meta_Ball_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], simplified functional_mapper,
          simplified]
  by blast

lemma functional_transformation:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x\<close>
  unfolding meta_Ball_def Argument_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], simplified functional_mapper,
          simplified]
  by blast

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action \<A>_structural _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action \<A>_structural Act)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action as _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action as Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action as Z \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .


(*
lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action to _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action to Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action to (Fb Z) \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 31 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action to _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action to Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action to Z \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .
*)

end

hide_fact Transformation_Functor_L_simp_cong


subsubsection \<open>Type-Functor for Separation\<close>

locale Sep_Homo_Type_zip_L =
  fixes Fa :: \<open>('b::sep_magma,'a) \<phi> \<Rightarrow> ('d::sep_magma,'c) \<phi>\<close>
    and Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
    and Fc :: \<open>('b,'a \<times> 'e) \<phi> \<Rightarrow> ('d,'g) \<phi>\<close>
    and D  :: \<open>('c \<times> 'f) set\<close>
    and z  :: \<open>'c \<times> 'f \<Rightarrow> 'g\<close>
    and Prem :: bool
  assumes Separation_Homo\<^sub>I: \<open>Prem \<Longrightarrow> Separation_Homo\<^sub>I Fa Fb Fc D z\<close>
begin



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

subsubsection \<open>Extension of BNF-FP\<close>

ML_file \<open>library/tools/BNF_fp_sugar_more.ML\<close>


lemma zip_eq_Cons_ex:
  \<open>zip a b = (h#l) \<longleftrightarrow> (\<exists>ah al bh bl. a = ah # al \<and> b = bh # bl \<and> (ah,bh) = h \<and> zip al bl = l)\<close>
  by (induct b; cases a; simp)

lemma zip_eq_Nil_eq_len:
  \<open>length a = length b \<Longrightarrow> (zip a b = []) \<longleftrightarrow> a = [] \<and> b = []\<close>
  by (induct b; cases a; simp)

lemma zip_eq_Nil_with_rel:
  \<open>list_all2 P a b \<and> zip a b = [] \<longleftrightarrow> a = [] \<and> b = []\<close>
  by (induct b; cases a; simp)


setup \<open>Context.theory_map(
  BNF_FP_Sugar_More.add_fp_more (\<^type_name>\<open>list\<close>, {
      deads = [],
      lives = [\<^typ>\<open>'a\<close>],
      lives'= [\<^typ>\<open>'b\<close>],
      zip = \<^term>\<open>case_prod zip\<close>,
      unzip = \<^term>\<open>(\<lambda>l. (map fst l, map snd l))\<close>,
      zip_simps = @{thms zip_eq_Cons_ex},
      unzip_simps = [] (*what I need to give?*)
  })
)\<close>

(* ML \<open>\<^pattern>\<open>case_prod zip\<close>\<close>
ML \<open>\<^pattern>\<open>(\<lambda>l. (map fst l, map snd l))\<close>\<close> *)


subsubsection \<open>Deriver Framework\<close>


consts \<phi>TA_ind_target :: \<open>action \<Rightarrow> action\<close>
       \<phi>TA_IH_ToA :: action

lemma mk_ToA_rule:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> Q
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> Q \<and> P\<close>
  using implies_trans by blast

lemma mk_ToA_rule':
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> A \<brangle> \<w>\<i>\<t>\<h> Q
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> B \<brangle> \<w>\<i>\<t>\<h> Q \<and> P\<close>
  unfolding FOCUS_TAG_def
  using implies_left_prod mk_ToA_rule by blast

lemma conv_intro_premise:
  \<open>P \<Longrightarrow> X \<equiv> (P \<longrightarrow> X)\<close>
  by simp

lemma [fundef_cong]:
  \<open>T x = T' x' \<Longrightarrow> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')\<close>
  unfolding \<phi>Type_def by simp

ML_file \<open>library/automation/type_algebra.ML\<close>

subsubsection \<open>Warn if the Def contains Sat\<close>

\<phi>property_deriver Warn_if_contains_Sat 10 = \<open>fn [] => fn phi => fn thy => (
  if Phi_Type_Algebra.is_Type_Opr (Term.fastype_of (#term phi)) andalso
     Phi_Type_Algebra.def_contains_satisfaction phi
  then warning ("The \<phi>-type definition contains satisfaction operator (\<Turnstile>).\n\
                \When a \<phi>-type is specified by satisfaction in a boolean assertion, it looses the ability to guide the reasoning.\n\
                \The deriving may fail. It is recommended to use composition operator (\<Zcomp>) to replace the (\<Turnstile>) if possible.")
  else () ;
  thy
)\<close>

subsubsection \<open>Implication\<close>

lemma \<phi>TA_Inh_rule:
  \<open> (\<And>x. Ant \<longrightarrow> Inhabited (x \<Ztypecolon> T) \<longrightarrow> P x @action \<phi>TA_ind_target \<A>EIF)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> \<forall>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P x\<close>
  unfolding Action_Tag_def
  by simp

lemma \<phi>TA_Inh_rewr:
  \<open>Trueprop (Ant \<longrightarrow> XX @action \<phi>TA_ind_target A)
 \<equiv> (Ant \<Longrightarrow> XX @action A)\<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_Inh_step:
  \<open> Inh \<longrightarrow> Any @action \<A>EIF
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Any \<longrightarrow> P)
\<Longrightarrow> Inh \<longrightarrow> P @action \<A>EIF\<close>
  unfolding Action_Tag_def Premise_def
  by blast

lemma \<phi>TA_Inh_inst_P:
  \<open> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Ant \<longrightarrow> others
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Ant \<longrightarrow> ((Any \<longrightarrow> Ant \<and> Any) \<and> others)\<close>
  unfolding Premise_def
  by blast

lemma \<phi>TA_Inh_extract_prem:
  \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<Longrightarrow> (\<exists>v. v \<Turnstile> (x \<Ztypecolon> T)) \<longrightarrow> P\<close>
  unfolding Action_Tag_def Inhabited_def .

ML_file \<open>library/phi_type_algebra/implication.ML\<close>

hide_fact \<phi>TA_Inh_rule \<phi>TA_Inh_rewr \<phi>TA_Inh_step \<phi>TA_Inh_inst_P

\<phi>property_deriver Implication 90 for (\<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.inhabitance
\<close>


subsubsection \<open>Identity Element Intro \& Elim\<close>

lemma \<phi>TA_1L_rule:
  \<open> (Ant \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) Any @action \<phi>TA_ind_target undefined)
\<Longrightarrow> (Ant \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Any \<longrightarrow> P))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P\<close>
  unfolding Action_Tag_def Identity_Element\<^sub>I_def Premise_def
  using implies_weaken by blast

lemma \<phi>TA_1L_rule':
  \<open> (Ant \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P\<close>
  unfolding Action_Tag_def Identity_Element\<^sub>I_def Premise_def
  using implies_weaken by blast

lemma \<phi>TA_1R_rule:
  \<open> (Ant \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T)\<close>
  unfolding Action_Tag_def .

lemma \<phi>TA_Ident_I_extract_prem:
  \<open>Identity_Element\<^sub>I S P \<Longrightarrow> (\<forall>v. v \<Turnstile> S \<longrightarrow> v = 1 \<and> P)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by blast

lemma \<phi>TA_Ident_E_extract_prem:
  \<open>Identity_Element\<^sub>E S \<Longrightarrow> (1 \<Turnstile> S)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by blast

ML_file \<open>library/phi_type_algebra/identity_element.ML\<close>

hide_fact \<phi>TA_1L_rule \<phi>TA_1R_rule

\<phi>property_deriver Identity_Element\<^sub>I 100 for (\<open>Identity_Element\<^sub>I _ _\<close>)
    requires Warn_if_contains_Sat
  = \<open>Phi_Type_Algebra_Derivers.identity_element_I\<close>

\<phi>property_deriver Identity_Element\<^sub>E 101 for (\<open>Identity_Element\<^sub>E _\<close>)
    requires Warn_if_contains_Sat
  = \<open>Phi_Type_Algebra_Derivers.identity_element_E\<close>

\<phi>property_deriver Identity_Element 102 requires Identity_Element\<^sub>I and Identity_Element\<^sub>E


subsubsection \<open>Object_Equiv\<close>

lemma Object_Equiv_rule:
  \<open> (\<And>x. Ant \<longrightarrow> (\<forall>y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T)) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Object_Equiv T eq \<close>
  unfolding Object_Equiv_def Premise_def Action_Tag_def
  by blast

lemma \<phi>TA_EO_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>y. P y \<longrightarrow> Q y) @action \<phi>TA_ind_target undefined)
\<equiv> (\<And>y. Ant \<Longrightarrow> P y \<Longrightarrow> Q y @action \<phi>TA_IH_ToA)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)

lemma \<phi>TA_EO_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target undefined)
\<equiv> (Ant \<Longrightarrow> P)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)

lemma Object_Equiv_rule_move_all:
  \<open>(\<And>x. P x \<and> Q) \<Longrightarrow> (\<forall>x. P x) \<and> Q\<close>
  by blast

lemma Object_Equiv_rule_move_all2:
  \<open>(P \<longrightarrow> (\<forall>x. Q x)) \<and> R \<Longrightarrow> (\<forall>x. P \<longrightarrow> Q x) \<and> R\<close>
  by blast

lemma Object_Equiv_rule_move_set_eq:
  \<open>RR \<Longrightarrow> (R \<and> P \<and> R2 \<longrightarrow> P) \<and> RR\<close>
  by blast

lemma Object_Equiv_rule_move_set_eq_end:
  \<open>(P \<and> R \<longrightarrow> P)\<close>
  by blast

lemma \<phi>TA_OE_extract_prem:
  \<open>Object_Equiv T eq \<Longrightarrow> (\<forall>x y v. eq x y \<longrightarrow> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> v \<Turnstile> (y \<Ztypecolon> T))\<close>
  unfolding Object_Equiv_def Transformation_def
  by blast


ML_file \<open>library/phi_type_algebra/object_equiv.ML\<close>
(*
hide_fact Object_Equiv_rule \<phi>TA_EO_rewr_IH \<phi>TA_EO_rewr_C Object_Equiv_rule_move_all
          Object_Equiv_rule_move_all2 Object_Equiv_rule_move_set_eq
          Object_Equiv_rule_move_set_eq_end *)

\<phi>property_deriver Object_Equiv 105 for (\<open>Object_Equiv _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.object_equiv
\<close>

\<phi>property_deriver Basic 109 requires Object_Equiv and Implication


subsubsection \<open>Transformation Functor\<close>

lemma \<phi>TA_TF_rule:
  \<open>(\<And>T U g x. Ant \<longrightarrow>
               (\<forall>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<longrightarrow> (a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)) \<longrightarrow> \<comment> \<open>split D\<close>
               (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) @action \<phi>TA_ind_target (to (U \<f>\<o>\<r> T)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Transformation_Functor F1 F2 D mapper\<close>
  unfolding Transformation_Functor_def Action_Tag_def Ball_def Premise_def
  by simp

lemma \<phi>TA_TF_rewr:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x. P x \<longrightarrow> A2 x) \<longrightarrow> C @action \<phi>TA_ind_target A)
\<equiv> (Ant \<Longrightarrow> (\<And>x. P x \<Longrightarrow> A2 x @action A) \<Longrightarrow> C @action A)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

lemma \<phi>TA_TF_pattern_IH:
  \<open> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> PROP Pure.term (\<And>a \<in> S. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Any a \<w>\<i>\<t>\<h> Any' a @action A)\<close> .

lemma \<phi>TA_TF_rule_step:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' \<w>\<i>\<t>\<h> Any @action \<A>_every_item A
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action ToSA
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action A\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def)

lemma \<phi>TA_TF_extract_prem:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. r b @action to what_ever
\<Longrightarrow> (\<forall>v. v \<Turnstile> X \<longrightarrow> (\<exists>b. v \<Turnstile> (b \<Ztypecolon> U) \<and> r b))\<close>
  unfolding Transformation_def Action_Tag_def
  by blast

subsubsection \<open>Functional Transformation Functor\<close>

lemma \<phi>TA_FTF_rule:
  \<open> (Ant \<Longrightarrow> Prem \<Longrightarrow> Transformation_Functor F1 F2 D mapper)
\<Longrightarrow> (Ant \<Longrightarrow> Prem \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>f P. mapper (\<lambda>a b. b = f a \<and> P a) = (\<lambda>a' b'. b' = fm f a' \<and> pm P a')))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Functional_Transformation_Functor F1 F2 D mapper Prem pm fm\<close>
  unfolding Functional_Transformation_Functor_def Premise_def fun_eq_iff
            Functional_Transformation_Functor_axioms_def Transformation_Functor_L_def
  by blast

ML_file \<open>library/phi_type_algebra/transformation_functor.ML\<close>

\<phi>property_deriver Transformation_Functor 110 for (\<open>Transformation_Functor _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.transformation_functor
\<close>

\<phi>property_deriver Functional_Transformation_Functor 111
  for (\<open>Functional_Transformation_Functor _ _ _ _ _ _ _\<close>)
  requires Transformation_Functor
    = \<open>Phi_Type_Algebra_Derivers.functional_transformation_functor\<close>

hide_fact \<phi>TA_TF_rule \<phi>TA_TF_rewr \<phi>TA_TF_pattern_IH \<phi>TA_FTF_rule


subsubsection \<open>Sep\<close>

lemma \<phi>TA_SHz_rule:
  \<open> (\<And>T U z. Ant \<longrightarrow>
        (\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z
            \<longrightarrow> ((y \<Ztypecolon> Fb U) * (x \<Ztypecolon> Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Fc (T \<^emph> U))) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Separation_Homo\<^sub>I Fa Fb Fc D w \<close>
  unfolding Separation_Homo\<^sub>I_def \<phi>Prod_expn' Action_Tag_def
  by simp

lemma \<phi>TA_SHu_rule:
  \<open> (\<And>T U z. Ant \<longrightarrow> (z \<Ztypecolon> Fc (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz z \<Ztypecolon> Ft T \<^emph> Fu U) @action \<phi>TA_ind_target (to (\<s>\<p>\<l>\<i>\<t> (T \<^emph> U))))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc uz \<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn' Action_Tag_def
  by simp

lemma \<phi>TA_SHz_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x y. P x y \<longrightarrow> Q x y) @action \<phi>TA_ind_target undefined)
\<equiv> (\<And>x y. Ant \<Longrightarrow> P x y \<Longrightarrow> Q x y @action \<phi>TA_IH_ToA)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

lemma \<phi>TA_SHz_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target A)
\<equiv> (Ant \<Longrightarrow> P)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

lemma \<phi>TA_SHu_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (z \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz \<Ztypecolon> U) @action \<phi>TA_ind_target A)
\<equiv> (Ant \<Longrightarrow> z \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z' \<Ztypecolon> U \<s>\<u>\<b>\<j> z'. z' = uz @action A)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by simp

lemma \<phi>TA_SHu_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target A)
\<equiv> (Ant \<Longrightarrow> P @action A)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

lemmas \<phi>TA_SHu_rule_step = \<phi>TA_TF_rule_step

ML_file \<open>library/phi_type_algebra/separation_homo.ML\<close>

hide_fact \<phi>TA_SHz_rule \<phi>TA_SHu_rule \<phi>TA_SHz_rewr_IH \<phi>TA_SHz_rewr_C
          \<phi>TA_SHu_rewr_IH \<phi>TA_SHu_rewr_C \<phi>TA_SHu_rule_step

\<phi>property_deriver Separation_Homo\<^sub>I 120 for (\<open>Separation_Homo\<^sub>I _ _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.separation_homo_I
\<close>

\<phi>property_deriver Separation_Homo\<^sub>E 121 for (\<open>Separation_Homo\<^sub>E _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.separation_homo_E
\<close>

\<phi>property_deriver Separation_Homo 122
  requires Separation_Homo\<^sub>I and Separation_Homo\<^sub>E = \<open>K (K I)\<close>



subsubsection \<open>Transform to Raw Abstraction (the Itself \<phi>-type)\<close>

lemma \<phi>TA_TrRA_rule:
  \<open> (\<And>x. Ant \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_ind_target (to Itself))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> \<forall>x. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to Itself) \<close>
  unfolding Action_Tag_def
  by simp

lemma \<phi>TA_TrRA_rewr:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_ind_target A) \<equiv> (Ant \<Longrightarrow> X @action A) \<close>
  unfolding Action_Tag_def atomize_imp .


ML_file \<open>library/phi_type_algebra/trans_to_raw_abst.ML\<close>

\<phi>property_deriver Trans_to_Raw_Abst 100 for (\<open>\<forall>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself\<close>) = \<open>
  Phi_Type_Algebra_Derivers.trans_to_raw_abst
\<close>

(* lemma \<phi>TA_ind_target_proctector_cong:
  \<open> P @action \<phi>TA_ind_target A \<equiv> P @action \<phi>TA_ind_target A\<close> . *)



subsubsection \<open>System\<close>

lemma list_all2_reduct_rel[simp]:
  \<open>list_all2 (\<lambda>a b. b = f a \<and> P a) = (\<lambda>a' b'. b' = map f a' \<and> list_all P a')\<close>
  apply (clarsimp simp add: fun_eq_iff)
  subgoal for x y by (induct x arbitrary: y; simp; case_tac y; simp; blast) .

(*
lemma
  \<open>list_all (\<lambda>x. Q \<and> P x) x = (Q \<and> list_all P x)\<close>
  apply (induct x; simp) *)




term case_prod

ML \<open>Sign.arity_sorts \<^theory> \<^type_name>\<open>prod\<close> \<^sort>\<open>times\<close>\<close>

(* hide_fact Object_Equiv_rule_move_all Object_Equiv_rule_move_set_eq Object_Equiv_rule_move_set_eq_end
          Object_Equiv_rule_move_all2

          \<phi>TA_TF_rule \<phi>TA_TF_rewr \<phi>TA_TF_pattern_IH (*\<phi>TA_TF_rule_step*) *)

lemmas [\<phi>constraint_expansion] =
          HOL.simp_thms ex_simps[symmetric] mem_Collect_eq imp_ex
          prod.case prod.sel fst_apfst snd_apfst fst_apsnd snd_apsnd apfst_id apsnd_id apfst_conv apsnd_conv
          ExSet_simps
          \<phi>Prod_expn' \<phi>Prod_expn''
          FSet.ball_simps(5-7) Set.ball_simps(5-7,9) Set.ball_Un
          Fun.bind_image Set.empty_bind Set.bind_singleton_conv_image Set.nonempty_bind_const Finite_Set.finite_bind
          list_all2_Cons1 list_all2_Nil zip_eq_Cons_ex zip_eq_Nil_eq_len list_all2_lengthD
              map_ident

thm prod.map_ident
thm zip_eq_Nil_eq_len zip_eq_Cons_ex



lemma Set_bind_insert[simp, \<phi>constraint_expansion]:
  \<open>Set.bind (insert x S) f = f x \<union> Set.bind S f\<close>
  unfolding Set.bind_def
  by auto

ML \<open>Conjunction.conjunctionI\<close>

lemma list_all2__const_True[simp]:
  \<open>list_all2 (\<lambda>x y. True) = (\<lambda>x y. length x = length y)\<close>
  apply (clarsimp simp add: fun_eq_iff)
  subgoal for x y
  by (induct x arbitrary: y; simp; case_tac y; simp) .


thm Set.ball_Un
thm set_simps
thm list.set


ML \<open>\<^simproc>\<open>defined_Ex\<close>\<close>
ML \<open>Quantifier1.rearrange_Ex\<close>
thm ExSet_simps
thm ex_simps



(*
lemma
  \<open> (\<And>T U z. Ant \<longrightarrow> (\<forall>x y. z = w(x,y) \<longrightarrow> (z \<Ztypecolon> Fc (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph> Fu U)))
\<Longrightarrow> Ant
\<Longrightarrow> Separation_Homo\<^sub>E Fa Fb Fc w \<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'
  by simp

lemma
  \<open> Scala_Semimodule_Functor F  \<close> *)


end
                                                          