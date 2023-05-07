theory Phi_Refinement_Algebra
  imports Phi_BI
begin

section \<open>The Algebra of \<open>\<phi>\<close>-Refinement\<close>

subsection \<open>Definitions\<close>

subsubsection \<open>Unit\<close>

definition \<open>Unit_Homo T \<longleftrightarrow> (1 \<Ztypecolon> T) = 1\<close>
definition \<open>Semi_Unit_Homo T \<longleftrightarrow> ((1 \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1)\<close>
definition \<open>Unit_Functor F \<longleftrightarrow> (\<forall>x T. (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1) \<longrightarrow> (x \<Ztypecolon> F T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1)) \<and>
                               (\<forall>x T. (1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T) \<longrightarrow> (1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> F T))\<close>
definition \<open>Semi_Unit_Functor F \<longleftrightarrow> (\<forall>x T. (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1) \<longrightarrow> (x \<Ztypecolon> F T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1))\<close>

subsubsection \<open>Transformation\<close>

definition \<open>Transformation_Functor F1 F2 f1 f2 \<longleftrightarrow>
  (\<forall>T U x y Q. (f1 x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f2 y \<Ztypecolon> U \<a>\<n>\<d> Q) \<longrightarrow> (x \<Ztypecolon> F1 T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> F2 U \<a>\<n>\<d> Q))\<close>

subsubsection \<open>Inhabitance\<close>

definition \<open>Inhabitance_Functor F f \<longleftrightarrow> (\<forall>T x. Inhabited(x \<Ztypecolon> F T) \<longrightarrow> Inhabited(f x \<Ztypecolon> T))\<close>
definition \<open>Inhabitance_Functor2 F f g \<longleftrightarrow> (\<forall>T U x. Inhabited(x \<Ztypecolon> F T U) \<longrightarrow> Inhabited(f x \<Ztypecolon> T) \<and> Inhabited(g x \<Ztypecolon> U))\<close>

subsubsection \<open>Separation\<close>

definition \<open>Separation_Homo T \<longleftrightarrow> (\<forall>x y. (x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x * y \<Ztypecolon> T \<a>\<n>\<d> x ## y )\<close>
definition \<open>Separation_Homo_eq T \<longleftrightarrow> Separation_Homo T \<and>
                          (\<forall>x y. x ## y \<longrightarrow> ( (x * y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) ))\<close>
definition \<open>Separation_Functor Ft Fu F3 T U \<longleftrightarrow> Ft(T) \<^emph> Fu(U) = F3 (T \<^emph> U)\<close>

definition Left_Seminearring_Functor :: \<open>('s \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 's::monoid_mult set \<Rightarrow> bool\<close>
  where \<open>Left_Seminearring_Functor F T D \<longleftrightarrow> (\<forall>s \<in> D. \<forall>t \<in> D. F s (F t T) = F (t * s) T)\<close>

subsection \<open>Configurations\<close>

lemma (in homo_one) [\<phi>reason 1100]:
  \<open>homo_one \<phi>\<close>
  by (simp add: homo_one_axioms)

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
              val Trueprop $ (_ (*Transformation_Functor*) $ F1 $ F2 $ f1 $ f2) = term'
              val ind = Int.max (maxidx_of_term F1, maxidx_of_term F2) + 1
              fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
              val H = Const(\<^const_name>\<open>Transformation_Functor\<close>, TVar(("'TF",ind),[]))
           in @{print} [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "f1" "'f1" $ var "f2" "'f2"),
               Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "f1" "'f1" $ var "f2" "'f2")]
          end\<close> (100)
]]

(*The default patterns of the rules are more general here by varifying types.
  This is designed specially.
  In \<^const>\<open>Automatic_Morphism\<close>, as the reverse transformation can have different type,
    and in the algebraic general rule \<open>_Structural_Extract_general_rule'_\<close> the functors are
    represented by variables, it means we have no simple way to varify the type of the functors.
    We use ML to capture the functor constant and varify the type variables as much as it can
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
  \<phi>reason_default_pattern
      \<open>Inhabitance_Functor2 ?F _ _\<close> \<Rightarrow> \<open>Inhabitance_Functor2 ?F _ _\<close> (100),
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Inhabitance_Functor _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Inhabitance_Functor2 _ _ _\<close>,

  \<phi>reason_default_pattern_ML \<open>Separation_Functor ?Ft ?Fu ?F3 _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Functor*) $ F1 $ F2 $ F3 $ T $ U) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Separation_Functor\<close>, TVar(("'SF",ind),[]))
       in [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3"
                         $ var "T" "'T" $ var "U" "U'"),
           Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3"
                         $ var "T" "'T" $ var "U" "U'"),
           Trueprop $ (H $ var "F1" "'F1" $ var "F3" "'F3" $ F3
                         $ var "T" "'T" $ var "U" "U'")]
      end
    \<close> (100),

  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Functor _ _ _ _ _\<close>
]]

subsection \<open>Applications\<close>

subsubsection \<open>Separation Homo / Functor\<close>

lemma \<phi>sep_homo:
  \<open> Separation_Homo T
\<Longrightarrow> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x * y \<Ztypecolon> T \<a>\<n>\<d> x ## y\<close>
  unfolding Separation_Homo_def by simp

lemma \<phi>sep_homo_inv:
  \<open> Separation_Homo_eq T
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x ## y
\<Longrightarrow> (x * y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T)\<close>
  unfolding Separation_Homo_eq_def Premise_def by blast

lemma apply_Separation_Functor_go:
  \<open> Separation_Functor Ft Fu Fc T U
\<Longrightarrow> (y \<Ztypecolon> Fu(U)) * (x \<Ztypecolon> Ft(T)) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x,y) \<Ztypecolon> Fc(T \<^emph> U)\<close>
  unfolding Separation_Functor_def \<phi>Prod_expn'[symmetric]
  by simp

lemma apply_Separation_Functor_back:
  \<open> Separation_Functor Ft Fu Fc T U
\<Longrightarrow> (x,y) \<Ztypecolon> Fc(T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> Fu(U)) * (x \<Ztypecolon> Ft(T))\<close>
  unfolding Separation_Functor_def \<phi>Prod_expn'[symmetric]
  by simp

subsubsection \<open>Transformation Functor\<close>

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> (fa x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> fb y \<Ztypecolon> U \<a>\<n>\<d> Q)
\<Longrightarrow> (x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<a>\<n>\<d> Q)\<close>
  unfolding Transformation_Functor_def
  by blast

subsection \<open>Reasoning\<close>

ML_file \<open>library/tools/functor_detect.ML\<close>

setup \<open>Phi_Functor_Detect.Rewr.setup_attribute \<^binding>\<open>\<phi>functor_of\<close>
  "set the pattern rewrite to parse the functor part and the argument part from a term\
  \ matching the patter"\<close>

subsubsection \<open>Void Homo / Functor\<close>

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
  let val _ (*Trueprop*) $ (_ (*\<r>Clean*) $ ( _ (*\<phi>Type*) $ _ $ T)) = Thm.major_prem_of sequent
   in case Phi_Functor_Detect.detect 1 ctxt T
        of SOME [Ft,Tt] => let
            val rule = Drule.infer_instantiate ctxt
                          [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                          @{thm "Unit_Homo_by_functor"}
             in SOME ((ctxt, rule RS sequent), Seq.empty) end
         | _ => NONE
  end)
\<close>

subsubsection \<open>Separation Homo / Functor\<close>

lemma [\<phi>reason add]:
  \<open> Separation_Homo_eq T
\<Longrightarrow> Separation_Homo T\<close>
  unfolding Separation_Homo_eq_def by blast

lemma Separation_Homo_functor:
  \<open> Separation_Functor F F F' T T
\<Longrightarrow> Transformation_Functor F' F id id
\<Longrightarrow> Separation_Homo T
\<Longrightarrow> Separation_Homo (F T)\<close>
  unfolding Separation_Homo_def Transformation_Functor_def Separation_Functor_def
  by (simp; metis \<phi>Prod_split)

lemma Separation_Homo_eq_functor:
  \<open> Separation_Functor F F F' T T
\<Longrightarrow> Transformation_Functor F F' id id
\<Longrightarrow> Separation_Homo (F T)
\<Longrightarrow> Separation_Homo_eq T
\<Longrightarrow> Separation_Homo_eq (F T)\<close>
  unfolding Separation_Homo_eq_def
  apply simp
  unfolding Transformation_Functor_def Separation_Functor_def
  by (simp; metis \<phi>Prod_split)

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
         | _ => NONE
  end)
\<close>

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
         | _ => NONE
  end)
\<close>


subsubsection \<open>Inhabitance Functor\<close>

lemma Inhabitance_Functor_from_Transformation_Functor[\<phi>reason 50]:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> Inhabitance_Functor Fa fa\<close>
  unfolding Inhabitance_Functor_def Transformation_Functor_def Inhabited_def Imply_def
  by clarsimp meson




end