theory Phi_Type_Algebra
  imports IDE_CP_Core Phi_Algebras.Map_of_Tree
  keywords "\<phi>type_def" :: thy_defn
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

(*f1 f2: do not use constants (e.g. id), use lambda expressions (e.g. \<lambda>x. x)
  so that pattern match has no impediment *)

subsubsection \<open>Inhabitance\<close>

definition \<open>Inhabitance_Functor F f \<longleftrightarrow> (\<forall>T x. Inhabited(x \<Ztypecolon> F T) \<longrightarrow> Inhabited(f x \<Ztypecolon> T))\<close>
definition \<open>Inhabitance_Functor2 F f g \<longleftrightarrow> (\<forall>T U x. Inhabited(x \<Ztypecolon> F T U) \<longrightarrow> Inhabited(f x \<Ztypecolon> T) \<and> Inhabited(g x \<Ztypecolon> U))\<close>

subsubsection \<open>Additive Disjunction\<close>

locale Union_Functor =
  fixes Fa :: \<open>('e, 'a \<Rightarrow> 'd) \<phi> \<Rightarrow> ('c, 'a \<Rightarrow> 'b) \<phi>\<close>
    and Fb :: \<open>('e,'d) \<phi> \<Rightarrow> ('c, 'b) \<phi>\<close>
  assumes union_functor[simp]: \<open>Fa (ExTyp T) = ExTyp (\<lambda>c. Fb (T c))\<close>


subsubsection \<open>Separation\<close>

definition \<open>Separation_Homo T \<longleftrightarrow> (\<forall>x y. (x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x * y \<Ztypecolon> T \<a>\<n>\<d> x ## y )\<close>
definition \<open>Separation_Homo_eq T \<longleftrightarrow> Separation_Homo T \<and>
                          (\<forall>x y. x ## y \<longrightarrow> ( (x * y \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) ))\<close>
definition \<open>Separation_Functor Ft Fu F3 T U \<longleftrightarrow> Ft(T) \<^emph> Fu(U) = F3 (T \<^emph> U)\<close>

definition Scala_Semimodule_Functor :: \<open>('s \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 's::monoid_mult set \<Rightarrow> bool\<close>
  where \<open>Scala_Semimodule_Functor F T D \<longleftrightarrow> (\<forall>s \<in> D. \<forall>t \<in> D. F s (F t T) = F (t * s) T)\<close>


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
              val Trueprop $ (_ (*Transformation_Functor*) $ F1 $ F2 $ f1 $ f2) = term'
              val ind = Int.max (maxidx_of_term F1, maxidx_of_term F2) + 1
              fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
              val H = Const(\<^const_name>\<open>Transformation_Functor\<close>, TVar(("'TF",ind),[]))
           in [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "f1" "'f1" $ var "f2" "'f2"),
               Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "f1" "'f1" $ var "f2" "'f2")]
          end\<close> (100)
]]

(*The default patterns of the rules are more general here by varifying types.
  This is designed specially.
  In \<^const>\<open>Reverse_Transformation\<close>, as the reverse transformation can have different type,
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
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t fa x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> fb y \<Ztypecolon> U \<a>\<n>\<d> Q
\<Longrightarrow> (x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<a>\<n>\<d> Q)\<close>
  unfolding Transformation_Functor_def Argument_def
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
  let val _ (*Trueprop*) $ (_ (*Unit_Homo*) $ T) = Thm.major_prem_of sequent
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
\<Longrightarrow> Transformation_Functor F' F (\<lambda>x. x) (\<lambda>x. x)
\<Longrightarrow> Separation_Homo T
\<Longrightarrow> Separation_Homo (F T)\<close>
  unfolding Separation_Homo_def Transformation_Functor_def Separation_Functor_def
  by (simp; metis \<phi>Prod_split)

lemma Separation_Homo_eq_functor:
  \<open> Separation_Functor F F F' T T
\<Longrightarrow> Transformation_Functor F F' (\<lambda>x. x) (\<lambda>x. x)
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
            handle THM _ => NONE
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
              handle THM _ => NONE
         | _ => NONE
  end)
\<close>


subsubsection \<open>Inhabitance Functor\<close>

lemma Inhabitance_Functor_from_Transformation_Functor[\<phi>reason 50]:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> Inhabitance_Functor Fa fa\<close>
  unfolding Inhabitance_Functor_def Transformation_Functor_def Inhabited_def Imply_def
  by clarsimp meson


subsection \<open>Automation\<close>
 
locale \<phi>Type_Functor =
  fixes F :: \<open>('c,'a) \<phi> \<Rightarrow> ('c1,'a1) \<phi>\<close>
begin
 
declare [[\<phi>functor_of \<open>F ?T\<close> \<Rightarrow> \<open>F\<close> \<open>?T\<close> (31)]]
(*priority of the 2-arity functor: 32*)

end

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


subsubsection \<open>Transformation\<close>

lemma simp_cong[\<phi>simp_cong]:
  \<open> Transformation_Functor Fa Fa fa fa
\<Longrightarrow> (fa x \<Ztypecolon> T) \<equiv> (fa x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Fa T) \<equiv> (x' \<Ztypecolon> Fa T')\<close>
  unfolding Transformation_Functor_def Imply_def atomize_eq
  by blast

locale Transformation_Functor_L = \<phi>Type_Functor Fa
  for Fa :: \<open>('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>\<close>
+ fixes Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
    and fa :: \<open>'c \<Rightarrow> 'a\<close>
    and fb :: \<open>'f \<Rightarrow> 'e\<close>
    and Prem :: bool
  assumes Transformation_Functor[\<phi>reason 1100]:
    \<open>Prem \<Longrightarrow> Transformation_Functor Fa Fb fa fb\<close>
begin

lemma transformation[\<phi>reason default 40]:
  \<open> Prem
\<Longrightarrow> fa x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> fb y \<Ztypecolon> U \<a>\<n>\<d> Q
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<a>\<n>\<d> Q\<close>
  using Transformation_Functor[unfolded Transformation_Functor_def]
  by blast
(*
simproc_setup simp_cong ("(x \<Ztypecolon> Fa T)") = \<open>
fn morph =>
let val redex_residue = Morphism.cterm morph \<^schematic_cterm>\<open>((?x \<Ztypecolon> Fa ?T), Fa)\<close>
    val redex = Thm.dest_arg1 redex_residue
    val residue = @{print} (Thm.dest_arg redex_residue)
in fn ctxt => fn cterm =>
  let val s = Thm.first_order_match (redex, cterm)
      val Fa = Thm.instantiate_cterm s residue
      val rule = (ctxt, Drule.infer_instantiate ctxt [(("Fa",0),Fa)] @{thm simp_cong})
               |> Phi_Reasoner.reason (SOME 1)
               |> Option.map snd
   in Option.mapPartial (fn rule => Phi_SimpCong.simproc rule ctxt cterm) rule
  end
end
\<close>
*)
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


subsection \<open>\<phi>-Type definition tools\<close>

ML_file \<open>library/system/phi_type_definition.ML\<close>


end