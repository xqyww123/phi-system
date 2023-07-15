chapter \<open>Pre-built \<phi>-Types\<close>

theory Phi_Types
  imports IDE_CP_Reasoning2
begin

section \<open>Basics\<close>

subsection \<open>Preliminary Sugars\<close>

consts \<phi>coercion :: \<open>('c1,'a) \<phi> \<Rightarrow> ('c2,'a) \<phi>\<close> ("\<coercion> _" [61] 60)
  \<comment> \<open>merely a syntax sugar to be overloaded.\<close>

(*reconsider this! may depreciate it!*)
text \<open>A semantic type is not always required to be annotated if it is known syntactically.
  We use syntax translation to achieve a sugar to do this.

This is a planning feature has not been implemented\<close>

syntax TY_of_\<phi> :: \<open>('a,'b) \<phi> \<Rightarrow> TY\<close> ("TY'_of'_\<phi>")



subsection \<open>Func\<close>

declare [[\<phi>trace_reasoning = 0]]
                 
\<phi>type_def \<phi>Fun :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('c,'a) \<phi>\<close>
  where [\<phi>defs]: \<open>\<phi>Fun f x = (f x \<Ztypecolon> Itself)\<close>
  deriving \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = 1 \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> \<phi>Fun f) True\<close>
       and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = 1 \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> \<phi>Fun f)\<close>
       and Basic
       and Is_Functional
       and Trans_to_Raw_Abst


subsubsection \<open>Algebraic Properties\<close>

lemma [\<phi>reason add]:
  \<open> homo_sep_disj_total f
\<Longrightarrow> homo_sep_mult f
\<Longrightarrow> Separation_Homo_Obj (\<phi>Fun f) UNIV \<close>
  unfolding Separation_Homo_Obj_def Transformation_def
  by (clarsimp simp add: set_mult_expn homo_sep_disj_total.sep_disj_homo
                         homo_sep_mult.homo_mult)

lemma [\<phi>reason add]:
  \<open> homo_sep_disj_total f
\<Longrightarrow> homo_sep_mult f
\<Longrightarrow> Separation_Homo_unzip (\<phi>Fun f)\<close>
  unfolding Separation_Homo_unzip_def Transformation_def
  by (clarsimp simp add: set_mult_expn homo_sep_disj_total.sep_disj_homo
                         homo_sep_mult.homo_mult)

(*
interpretation \<phi>Fun: Unit_Homo_L \<open>homo_one f\<close> \<open>\<phi>Fun f\<close>
  apply standard
  unfolding Unit_Homo_def homo_one_def Transformation_def
  by (simp add: \<phi>Fun_expn set_eq_iff)

lemma \<phi>Fun_unit_homo[\<phi>reason add]:
  \<open> homo_one f
\<Longrightarrow> Unit_Homo (\<phi>Fun f) \<close>
  unfolding Unit_Homo_def homo_one_def Transformation_def
  by (simp add: \<phi>Fun_expn set_eq_iff) *)


subsection \<open>\<phi>-Type Embedding of \<open>\<top>\<close>\<close>
   
\<phi>type_def \<phi>Any :: \<open>('x, unit) \<phi>\<close>
  where [embed_into_\<phi>type]: \<open>\<phi>Any = (\<lambda>_. UNIV)\<close>
  deriving Basic

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> \<phi>Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v \<Ztypecolon> Itself \<s>\<u>\<b>\<j> v. True @action to Itself\<close>
  \<medium_left_bracket> to Itself \<medium_right_bracket>.

declare [[\<phi>trace_reasoning = 3]]

 
 
subsection \<open>Embedding Subjection into Type\<close>
                                                                        
\<phi>type_def SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<s>\<u>\<b>\<j>" 25)
  where [embed_into_\<phi>type]: \<open> (T \<phi>\<s>\<u>\<b>\<j> P) = (\<lambda>x. x \<Ztypecolon> T \<s>\<u>\<b>\<j> P) \<close>
  deriving Basic
       (*and \<open>(\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> Is_Functional (x \<Ztypecolon> T)) \<Longrightarrow> Is_Functional (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P) \<close>
       and \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<Longrightarrow> x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> Q \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> Q \<close>
       and \<open>(\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to Itself) \<Longrightarrow>
             x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y \<and> P @action to Itself \<close>
       and Functional_Transformation_Functor*)
       and Separation_Homo


translations "TY_of_\<phi> (T \<phi>\<s>\<u>\<b>\<j> P)" \<rightharpoonup> "TY_of_\<phi> T"

declare SubjectionTY.unfold[\<phi>programming_simps]


subsubsection \<open>Algebraic Properties\<close>

(* declare [[\<phi>functor_of \<open>?T \<phi>\<s>\<u>\<b>\<j> ?P\<close> \<Rightarrow> \<open>\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P\<close> \<open>?T\<close> (100) ]] *)

(* lemma SubjectionTY_unit_functor[\<phi>reason add]:
  \<open> Semi_Unit_Functor (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P) \<close>
  unfolding Semi_Unit_Functor_def Transformation_def
  by (clarsimp simp add: SubjectionTY_expn Subjection_expn set_eq_iff) *)
 
interpretation SubjectionTY: Functional_Transformation_Functor
    \<open>\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P\<close> \<open>\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P\<close> \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> \<open>True\<close> \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard, clarsimp simp add: Transformation_Functor_def Transformation_def SubjectionTY_expn
          Subjection_expn, blast)

lemma SubjectionTY_inhabitance_functor[\<phi>reason add]:
  \<open> Inhabitance_Functor (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P) id \<close>
  unfolding Inhabitance_Functor_def Inhabited_def
  by (clarsimp simp add: SubjectionTY_expn)

interpretation SubjectionTY: Sep_Homo_Type_Functor_L
      \<open>\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P\<close> \<open>\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P\<close> \<open>\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P\<close> True
  by (standard, rule \<phi>Type_eqI, clarsimp simp add:
      set_eq_iff SubjectionTY_expn Subjection_expn set_mult_expn \<phi>Prod_expn; blast)

lemma \<phi>\<s>\<u>\<b>\<j>_simp:
  \<open> Transformation_Functor Fa Fa D mapper
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ((\<forall>x y. mapper (\<lambda>a b. a = b \<and> P) x y \<longrightarrow> x = y \<and> P))
\<Longrightarrow> (Fa (T \<phi>\<s>\<u>\<b>\<j> P)) \<equiv> (Fa T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Transformation_Functor_def Transformation_def atomize_eq Premise_def
  by (rule \<phi>Type_eqI; clarsimp simp add: SubjectionTY_expn Subjection_expn ExSet_expn subset_iff,
      smt (z3) SubjectionTY_expn Subjection_expn \<phi>Type_eqI

simproc_setup (in Transformation_Functor_L) \<phi>\<s>\<u>\<b>\<j>_simp (\<open>Fa (T \<phi>\<s>\<u>\<b>\<j> P)\<close>) = \<open>
fn morph => 
let val redex_residue = Morphism.cterm morph \<^schematic_cterm>\<open>(Fa (?T \<phi>\<s>\<u>\<b>\<j> ?k), Fa)\<close>
    val redex = Thm.dest_arg1 redex_residue
    val residue = Thm.dest_arg redex_residue
in fn ctxt => fn cterm =>
  let val s = Thm.first_order_match (redex, cterm)
      val Fa = Thm.instantiate_cterm s residue
<<<<<<< HEAD
   in (Drule.infer_instantiate ctxt [(("Fa",0),Fa)] @{thm \<phi>\<s>\<u>\<b>\<j>_simp})
         |> Phi_Reasoner.reason (SOME 1) ctxt
=======
   in (ctxt, Drule.infer_instantiate ctxt [(("Fa",0),Fa)] @{thm \<phi>\<s>\<u>\<b>\<j>_simp})
         |> Phi_Reasoner.reason (SOME 2)
         |> Option.map snd
>>>>>>> dce1a7d (WIP)
  end
end
\<close>



subsection \<open>Embedding Existential Quantification\<close>

syntax
  "_SetcomprPhiTy" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<phi>\<s>\<u>\<b>\<j>/ _./ _ " [2,0,2] 2)
  "_SetcomprPhiTy'" :: "logic \<Rightarrow> idts \<Rightarrow> logic \<Rightarrow> logic"

parse_ast_translation \<open>
  let open Ast
    fun idts_to_abs x (Appl [Constant "_idts", a, b]) = Appl [Constant "_abs", a, idts_to_abs x b]
      | idts_to_abs x c = Appl [Constant "_abs", c, x]
    fun parse_SetcomprPhiTy ctxt [Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, x, T],idts,P] =
          Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>,
                idts_to_abs x idts,
                Appl [Constant "\<^const>Phi_BI.ExTyp_binder", idts,
                      (case P of (Appl [Constant "_constrain", Variable "True", _]) => T
                               | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, T, P])]]
      | parse_SetcomprPhiTy ctxt [X,idts,P] =
          Appl [Constant "\<^const>Phi_BI.ExTyp_binder", idts,
                (case P of (Appl [Constant "_constrain", Variable "True", _]) => X
                         | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, X, P])]
  in [(\<^syntax_const>\<open>_SetcomprPhiTy\<close>, parse_SetcomprPhiTy)] end
\<close>
(*
lemma Action_to_Itself[\<phi>reason 25]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (v \<Ztypecolon> Itself \<s>\<u>\<b>\<j> v. v \<in> X) @action to Itself\<close>
  unfolding Action_Tag_def Transformation_def by (simp add: \<phi>expns)*)


lemma [\<phi>reason 1000]:
  \<open> (\<And>x. Object_Equiv (T x) (R x))
\<Longrightarrow> Object_Equiv (ExTyp T) (\<lambda>f g. \<forall>x. R x (f x) (g x)) \<close>
  unfolding Object_Equiv_def ExTyp_expn Transformation_def
  by (clarsimp simp add: ExSet_expn; blast)




(*
lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v \<Ztypecolon> Itself \<s>\<u>\<b>\<j> v. True @action to Itself\<close>
  for x :: \<open>nat\<close>
  \<medium_left_bracket> case_analysis *)

subsection \<open>Stepwise Abstraction\<close>

declare [[\<phi>trace_reasoning = 3]]
                                                                         
\<phi>type_def \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 30)
  where [\<phi>defs]: \<open>\<phi>Composition T U x = (y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<Turnstile> (x \<Ztypecolon> U))\<close>

ML \<open>Embed_into_Phi_Type.print \<^context> false\<close>

thm \<phi>Composition

lemma [\<phi>reason 1200]:
  \<open>x \<Ztypecolon> T \<Zcomp> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<Turnstile> (x \<Ztypecolon> U) @action to RAW\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket> .

lemma [\<phi>reason 1200]:
  \<open> y \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> y \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<Zcomp> U \<w>\<i>\<t>\<h> P\<close>
  \<medium_left_bracket> premises Y[unfolded Transformation_def Itself_expn, simplified, useful]
    construct\<phi> \<open>x \<Ztypecolon> T \<Zcomp> U\<close> \<medium_right_bracket> .

lemma [\<phi>reason 1200]:
  \<open> Is_Functional (x \<Ztypecolon> U)
\<Longrightarrow> y \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> T \<Zcomp> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<w>\<i>\<t>\<h> P\<close>
  \<medium_left_bracket> premises [unfolded Is_Functional_def, useful] and [unfolded satisfication_encoding, useful]
    destruct \<medium_right_bracket> .

lemma \<phi>Composition_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (x \<Ztypecolon> T \<Zcomp> U) \<longleftrightarrow> (\<exists>y. p \<Turnstile> (y \<Ztypecolon> T) \<and> y \<Turnstile> (x \<Ztypecolon> U))\<close>
  unfolding \<phi>Composition_def \<phi>Type_def by simp

lemma [\<phi>inhabitance_rule 1000]:
  \<open> x \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> A
\<Longrightarrow> (\<And>y. y \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> B y)
\<Longrightarrow> x \<Ztypecolon> T \<Zcomp> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<and> Ex B \<close>
  unfolding Inhabited_def Action_Tag_def
  by blast

lemma \<phi>Composition_transformation[\<phi>reason 1200 for \<open>(_ \<Ztypecolon> _ \<Zcomp> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<Ztypecolon> _ \<Zcomp> _) \<w>\<i>\<t>\<h> _\<close>]:
  \<open> x1 \<Ztypecolon> U1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x2 \<Ztypecolon> U2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x1 \<Ztypecolon> T \<Zcomp> U1) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x2 \<Ztypecolon> T \<Zcomp> U2) \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by blast

subsubsection \<open>Algebraic Properties\<close>

declare [[\<phi>trace_reasoning = 1]]

interpretation \<phi>Composition: Functional_Transformation_Functor
      \<open>(\<Zcomp>) B\<close> \<open>(\<Zcomp>) B'\<close> \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B'\<close> \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard,
      ( unfold Transformation_Functor_def Premise_def,
        clarsimp simp add: \<phi>Composition_expn Transformation_def ExSet_expn Subjection_expn ,
        blast),
      blast)

lemma \<phi>Composition_separatio_functor_zip[\<phi>reason add]:
  \<open> Separation_Homo_Obj B UNIV
\<Longrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) UNIV (\<lambda>x. x)\<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Separation_Homo_Obj_def
  by (clarsimp simp add: \<phi>Prod_expn \<phi>Composition_expn, insert times_set_I, blast)

lemma (*The above rule is reversible. requiring the sep homo domain being the univ is already the weakest.*)
  \<open> S \<noteq> {} \<Longrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) S (\<lambda>x. x) \<Longrightarrow> Separation_Homo_Obj B UNIV \<close>
  unfolding Separation_Homo\<^sub>I_def Separation_Homo_Obj_def Transformation_def
  apply (clarsimp simp add: \<phi>Prod_expn \<phi>Composition_expn set_mult_expn)
  apply (simp add: \<phi>Type_def)
  subgoal premises prems for x y u v
    by (insert prems(2)[THEN spec[where x=\<open>\<lambda>_. {y}\<close>], THEN spec[where x=\<open>\<lambda>_. {x}\<close>], simplified]
               prems(1,3-5), auto) .


lemma \<phi>Composition_separatio_functor_unzip[\<phi>reason add]:
  \<open> Separation_Homo_unzip B
\<Longrightarrow> Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x)\<close>
  for B :: \<open>('d::sep_magma,'e::sep_magma) \<phi>\<close>
  unfolding Separation_Homo\<^sub>E_def Transformation_def Separation_Homo_unzip_def
  by (clarsimp simp add: \<phi>Prod_expn \<phi>Composition_expn set_mult_expn; blast)

lemma (*The above rule is reversible*)
  \<open> Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x) \<Longrightarrow> Separation_Homo_unzip B \<close>
  unfolding Separation_Homo\<^sub>E_def Separation_Homo_unzip_def Transformation_def
  apply (clarsimp simp add: \<phi>Prod_expn \<phi>Composition_expn set_mult_expn)
  apply (simp add: \<phi>Type_def)
  subgoal premises prems for x y v
    by (insert prems(1)[THEN spec[where x=\<open>\<lambda>_. {y}\<close>], THEN spec[where x=\<open>\<lambda>_. {x}\<close>], simplified]
               prems(2-3), blast) .

(*
interpretation Unit_Functor_L \<open>Unit_Homo B\<close> \<open>((\<Zcomp>) B)\<close>
  unfolding Unit_Functor_L_def Unit_Functor_def Transformation_def Unit_Homo_def
  by (auto simp add: \<phi>Composition_expn) *)

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>I (1 \<Ztypecolon> B) P
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) Q
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> B \<Zcomp> T) (P \<and> Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>E (1 \<Ztypecolon> B)
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T)
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> B \<Zcomp> T)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by blast

(*
lemma \<phi>Composition_unit_functor[\<phi>reason add]:
  \<open> Unit_Homo B
\<Longrightarrow> Unit_Functor ((\<Zcomp>) B)\<close>
  unfolding Unit_Functor_def Unit_Homo_def
  by (auto simp add: \<phi>Composition_expn) *)

(*
lemma \<phi>Composition_union_functor[\<phi>reason add]:
  \<open>Union_Functor ((\<Zcomp>) B) ((\<Zcomp>) B)\<close>
  unfolding Union_Functor_def
  by (clarify, rule \<phi>Type_eqI, simp add: \<phi>expns \<phi>Composition_expn; blast)
*)

section \<open>Logical Connectives\<close>




subsection \<open>Embedding Universal Quantification\<close>

definition \<phi>Type_univ_quant :: \<open>('c \<Rightarrow> ('a, 'b) \<phi>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b)\<phi>\<close> ("\<forall>\<^sub>\<phi> _" [10] 10)
  where \<open>\<phi>Type_univ_quant T = (\<lambda>x. {p. (\<forall>c. p \<in> (x c \<Ztypecolon> T c))})\<close>

lemma \<phi>Type_univ_quant_expn[\<phi>expns]:
  \<open>p \<in> (f \<Ztypecolon> (\<forall>\<^sub>\<phi> T)) \<longleftrightarrow> (\<forall>x. p \<in> (f x \<Ztypecolon> T x))\<close>
  unfolding \<phi>Type_univ_quant_def \<phi>Type_def by clarsimp


subsection \<open>Embedding Additive Conjunction\<close>

definition \<phi>Inter :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<inter>\<^sub>\<phi>" 70)
  where \<open>(T \<inter>\<^sub>\<phi> U) = (\<lambda>(x,y). (x \<Ztypecolon> T) \<inter> (y \<Ztypecolon> U))\<close>

lemma \<phi>Inter_expn[\<phi>expns]:
  \<open>((x,y) \<Ztypecolon> (T \<inter>\<^sub>\<phi> U)) = (x \<Ztypecolon> T) \<inter> (y \<Ztypecolon> U)\<close>
  unfolding set_eq_iff \<phi>Type_def \<phi>Inter_def by simp

lemma \<phi>Inter_inhabited[\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> A @action \<A>EIF
\<Longrightarrow> Inhabited (y \<Ztypecolon> U) \<longrightarrow> B @action \<A>EIF
\<Longrightarrow> Inhabited ((x,y) \<Ztypecolon> (T \<inter>\<^sub>\<phi> U)) \<longrightarrow> A \<and> B @action \<A>EIF \<close>
  unfolding Inhabited_def Action_Tag_def
  by (clarsimp simp add: \<phi>Inter_expn; blast)




section \<open>Structural Connectives\<close>

subsection \<open>None\<close>





subsubsection \<open>Actions\<close>




subsubsection \<open>Rules\<close>





(*
lemma [\<phi>reason 1500
    for \<open>(() \<Ztypecolon> \<phi>None) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P @action (?Act::?'a::simplification action)\<close>
    except \<open>(() \<Ztypecolon> \<phi>None) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x \<Ztypecolon> ?T \<w>\<i>\<t>\<h> ?P @action (?Act::?'a::simplification action)\<close>
]:
  \<open>(() \<Ztypecolon> \<phi>None) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def by (simp add: implies_refl)
*)

subsection \<open>Prod\<close>

(* lemma \<phi>Prod_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<longleftrightarrow> Inhabited (x1 \<Ztypecolon> T1) \<and> Inhabited (x2 \<Ztypecolon> T2)\<close>
  unfolding Inhabited_def apply (simp add: \<phi>expns) *)




(*lemma (in \<phi>empty) SepNu_to_SepSet: "(OBJ (a,b) \<Ztypecolon> A \<^emph> B) = (OBJ a \<Ztypecolon> A) * (OBJ b \<Ztypecolon> B)"
  by (simp add: \<phi>expns set_eq_iff times_list_def) *)

subsubsection \<open>Reasoning Rules\<close>

(* paragraph \<open>View Shift\<close>

lemma [\<phi>reason for \<open>(?x,?y) \<Ztypecolon> ?N \<^emph> ?M \<s>\<h>\<i>\<f>\<t>\<s> (?x',?y') \<Ztypecolon> ?N' \<^emph> ?M' \<w>\<i>\<t>\<h> ?P\<close>]:
  " x \<Ztypecolon> N \<s>\<h>\<i>\<f>\<t>\<s> x' \<Ztypecolon> N' \<w>\<i>\<t>\<h> P1
\<Longrightarrow> y \<Ztypecolon> M \<s>\<h>\<i>\<f>\<t>\<s> y' \<Ztypecolon> M' \<w>\<i>\<t>\<h> P2
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<s>\<h>\<i>\<f>\<t>\<s> (x',y') \<Ztypecolon> N' \<^emph> M' \<w>\<i>\<t>\<h> P1 \<and> P2"
  unfolding View_Shift_def \<phi>Prod_expn'
  by (smt (verit, best) mult.commute mult.left_commute)  *)

(*do not add it to \<phi>-LPR because we have stronger reasoning mechanisms*)





subsubsection \<open>Action\<close>

lemma [\<phi>reason 1200]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action \<A>_structural act
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action \<A>_structural act
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action \<A>_structural act\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)








lemma [\<phi>reason 1000]:
  \<open> P @action as ((x \<Ztypecolon> T) * (y \<Ztypecolon> U))
\<Longrightarrow> P @action as ((x,y) \<Ztypecolon> (T \<^emph> U)) \<close>
  unfolding Action_Tag_def .

lemma prod_transform_as1:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action as M
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action as N
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action as (M * N)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma prod_transform_as2:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action to N
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action to M
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action to (M * N)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

declare [[\<phi>reason 1200 prod_transform_as1 prod_transform_as2
      for \<open>?A * ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (?M * ?N)\<close>]]

hide_fact prod_transform_as1 prod_transform_as2

lemma [\<phi>reason 1100]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action as T
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action as T
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action as T\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma Prod_transform_as1:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P @action as A
\<Longrightarrow> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<w>\<i>\<t>\<h> Q @action as B
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<w>\<i>\<t>\<h> P \<and> Q @action as (A * B)\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .

lemma Prod_transform_as2:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P @action as B
\<Longrightarrow> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<w>\<i>\<t>\<h> Q @action as A
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<w>\<i>\<t>\<h> P \<and> Q @action as (A * B)\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .

declare [[\<phi>reason 1200 Prod_transform_as1 Prod_transform_as2
      for \<open>(?x,?y) \<Ztypecolon> (?T \<^emph> ?U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action as (?A * ?B)\<close>]]

hide_fact Prod_transform_as1 Prod_transform_as2

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P @action as Target
\<Longrightarrow> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<w>\<i>\<t>\<h> Q @action as Target
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<w>\<i>\<t>\<h> P \<and> Q @action as Target\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .


paragraph \<open>Simplification\<close>

(*lemma \<phi>Prod_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (y \<Ztypecolon> U) = (y' \<Ztypecolon> U')
\<Longrightarrow> ((x,y) \<Ztypecolon> T \<^emph> U) = ((x',y') \<Ztypecolon> T' \<^emph> U')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Prod_simp_cong ("(x,y) \<Ztypecolon> (T \<^emph> U)") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>Prod_simp_cong} ctxt)
\<close>*)

lemma [simp]:
  \<open>((x,y) \<Ztypecolon> ExTyp T \<^emph> U) = ((\<lambda>c. (x c, y)) \<Ztypecolon> (\<exists>\<phi> c. T c \<^emph> U))\<close>
  by (clarsimp simp add: set_eq_iff \<phi>expns; blast)

lemma [simp]:
  \<open> NO_MATCH (ExTyp Any) T
\<Longrightarrow> ((x,y) \<Ztypecolon> T \<^emph> ExTyp U) = ((\<lambda>c. (x, y c)) \<Ztypecolon> (\<exists>\<phi> c. T \<^emph> U c))\<close>
  by (clarsimp simp add: set_eq_iff \<phi>expns; blast)


(*lemma [simp]: "A \<inter> S \<perpendicular> A \<inter> -S"
  unfolding disjoint_def by auto
lemma heap_split_id: "P h1' h2' \<Longrightarrow> \<exists>h1 h2. h1' ++ h2' = h1 ++ h2 \<and> P h1 h2" by auto
lemma heap_split_by_set: "P (h |` S) (h |` (- S)) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  by (rule exI[of _ "h |` S"], rule exI[of _ "h |` (- S)"])
    (auto simp add: map_add_def option.case_eq_if restrict_map_def disjoint_def disjoint_iff domIff)
lemma heap_split_by_addr_set: "P (h |` (MemAddress ` S)) (h |` (- (MemAddress ` S))) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  using heap_split_by_set .*)


subsection \<open>List Item \& Empty List\<close>

subsubsection \<open>List Item\<close>

definition List_Item :: \<open>('v, 'a) \<phi> \<Rightarrow> ('v list, 'a) \<phi>\<close>
  where \<open>List_Item T = (\<lambda>x. { [v] |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma List_Item_expn[\<phi>expns]:
 \<open>p \<in> (x \<Ztypecolon> List_Item T) \<longleftrightarrow> (\<exists>v. p = [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding List_Item_def \<phi>Type_def by simp

lemma List_Item_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> List_Item T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> Inhabited (x \<Ztypecolon> List_Item T) \<longrightarrow> C @action \<A>EIF \<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp add: \<phi>expns)

lemma \<comment> \<open>A example for how to represent list of multi-elements\<close>
  \<open> v1 \<in> (x1 \<Ztypecolon> T1)
\<Longrightarrow> v2 \<in> (x2 \<Ztypecolon> T2)
\<Longrightarrow> [v1,v2] \<in> ((x1, x2) \<Ztypecolon> (List_Item T1 \<^emph> List_Item T2))\<close>
  by (simp add: \<phi>expns times_list_def, rule exI[where x=\<open>[v2]\<close>], rule exI[where x=\<open>[v1]\<close>], simp)

subsubsection \<open>Empty List\<close>

definition Empty_List :: \<open>('v list, unit) \<phi>\<close>
  where \<open>Empty_List = (\<lambda>x. { [] })\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Empty_List) \<longleftrightarrow> p = []\<close>
  unfolding Empty_List_def \<phi>Type_def by simp

lemma Empty_List_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> Empty_List) \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsection \<open>Optional\<close>

definition \<phi>Optional :: \<open>('c,'x) \<phi> \<Rightarrow> bool \<Rightarrow> ('c::one,'x) \<phi>\<close> (infix "?\<^sub>\<phi>" 55)
  where \<open>(T ?\<^sub>\<phi> C) = (\<lambda>x. if C then (x \<Ztypecolon> T) else 1)\<close>

lemma \<phi>Optional_expn[\<phi>expns]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> C) = (if C then x \<Ztypecolon> T else 1)\<close>
  unfolding \<phi>Type_def \<phi>Optional_def by simp

lemma \<phi>Optional_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> T ?\<^sub>\<phi> C) \<Longrightarrow> ((C \<Longrightarrow> Inhabited (x \<Ztypecolon> T)) \<Longrightarrow> Z) \<Longrightarrow> Z\<close>
  unfolding Inhabited_def by (cases C; clarsimp simp add: \<phi>Optional_expn)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> (C \<Longrightarrow> Inhabited (x \<Ztypecolon> T) \<longrightarrow> A @action \<A>EIF)
\<Longrightarrow> Inhabited (x \<Ztypecolon> T ?\<^sub>\<phi> C) \<longrightarrow> (C \<longrightarrow> A) @action \<A>EIF \<close>
  unfolding Inhabited_def Action_Tag_def
  by (cases C; clarsimp simp add: \<phi>Optional_expn)


subsubsection \<open>Conversion\<close>

lemma [simp]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> True) = (x \<Ztypecolon> T)\<close>
  unfolding set_eq_iff by (simp add: \<phi>Optional_expn)

lemma [simp]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> False) = 1\<close>
  unfolding set_eq_iff by (simp add: \<phi>Optional_expn)

subsubsection \<open>Rules\<close>

lemma [\<phi>reason 3000 for \<open>Identity_Element\<^sub>I (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C) _\<close>]:
  \<open> Identity_Element\<^sub>I (x \<Ztypecolon> T ?\<^sub>\<phi> False) True\<close>
  unfolding Identity_Element\<^sub>I_def by simp



subsection \<open>Mapping\<close>

definition \<phi>Mapping :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> ('av \<Rightarrow> 'bv, 'a \<Rightarrow> 'b) \<phi>\<close> (infixr "\<Rrightarrow>" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow> U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U) })\<close>

lemma \<phi>Mapping_expn[\<phi>expns]:
  \<open>g \<in> (f \<Ztypecolon> T \<Rrightarrow> U) \<longleftrightarrow> (\<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U))\<close>
  unfolding \<phi>Mapping_def \<phi>Type_def by simp

lemma \<phi>Mapping_inhabited[elim!]:
  \<open>Inhabited (f \<Ztypecolon> T \<Rrightarrow> U) \<Longrightarrow> ((\<And>x. Inhabited (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (f x \<Ztypecolon> U)) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>Mapping_expn, blast)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> ((\<exists>x. Inhabited (x \<Ztypecolon> T)) \<and> P = True) \<or> P = False
\<Longrightarrow> (\<And>x. Inhabited (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (f x \<Ztypecolon> U) \<longrightarrow> C x @action \<A>EIF)
\<Longrightarrow> Inhabited (f \<Ztypecolon> T \<Rrightarrow> U) \<longrightarrow> (P \<longrightarrow> Ex C) @action \<A>EIF\<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp add: \<phi>Mapping_expn, blast)

(*
lemma
  \<open>(\<exists>c ca w cb cc wa.
             \<forall>T U g x Ta xa l.
                True \<longrightarrow>
                True \<longrightarrow>
                (\<forall>xb xaa.
                    True \<longrightarrow>
                    list_all2 g l xb \<longrightarrow>
                    g xa xaa \<longrightarrow> (True \<and> True) \<and> True \<longrightarrow> g xa (id (c T U g x Ta xa l xb xaa)) \<and> list_all2 g l (id (ca T U g x Ta xa l xb xaa))) \<and>
                (\<forall>xb xaa. True \<longrightarrow> list_all2 g l xb \<longrightarrow> g xa xaa \<longrightarrow> True \<and> True \<longrightarrow> xaa = id (c T U g x Ta xa l xb xaa)) \<and>
                (\<forall>xb xaa. True \<longrightarrow> list_all2 g l xb \<longrightarrow> g xa xaa \<longrightarrow> fst (xb, w T U g x Ta xa l xb xaa) = id (ca T U g x Ta xa l xb xaa)) \<and>
                (True \<longrightarrow> xa \<in> set (xa # l)) \<and> (\<forall>a. True \<longrightarrow> a \<in> set l \<longrightarrow> a \<in> set (xa # l)) \<and> True \<or>
                (\<forall>xb xaa.
                    True \<longrightarrow>
                    list_all2 g l xb \<longrightarrow>
                    g xa xaa \<longrightarrow> (True \<and> True) \<and> True \<longrightarrow> g xa (id (cb T U g x Ta xa l xb xaa)) \<and> list_all2 g l (id (cc T U g x Ta xa l xb xaa))) \<and>
                (\<forall>xb xaa. True \<longrightarrow> list_all2 g l xb \<longrightarrow> g xa xaa \<longrightarrow> True \<and> True \<longrightarrow> xaa = id (cb T U g x Ta xa l xb xaa)) \<and>
                (\<forall>xb xaa. True \<longrightarrow> list_all2 g l xb \<longrightarrow> g xa xaa \<longrightarrow> list_all2 (=) (fst (xb, wa T U g x Ta xa l xb xaa)) (id (cc T U g x Ta xa l xb xaa))) \<and>
                (True \<longrightarrow> xa \<in> set (xa # l)) \<and> (\<forall>a. True \<longrightarrow> a \<in> set l \<longrightarrow> a \<in> set (xa # l)) \<and> True) \<and>
         (\<forall>T U g x Ta. True \<longrightarrow> True \<longrightarrow> True) \<and> True \<close>
  apply (((rule conjI)+ ; ((rule exI)+)?), auto) *)



subsection \<open>Point on a Mapping\<close>

subsubsection \<open>By Key\<close>

ML \<open>Phi_Cache_DB.invalidate_cache \<^theory>\<close>

declare [[ML_print_depth = 1000, \<phi>trace_reasoning = 0]]
                                                                                                                                                                                             
\<phi>type_def List :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List T) = (x \<Ztypecolon> T\<heavy_comma> l \<Ztypecolon> List T)\<close>
  deriving Basic
       and Identity_Element
       and Functional_Transformation_Functor
       and Separation_Homo


\<phi>type_def List3 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List3 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List3 T) = (x \<Ztypecolon> List T\<heavy_comma> l \<Ztypecolon> List3 T)\<close>
  deriving Basic
       and Identity_Element
       and Transformation_Functor



thm List3.obj_eq

(* BOSS:
\<phi>type_def List2 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List2 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List2 T) = (prod (\<lambda>x. x \<Ztypecolon> T) (set x)\<heavy_comma> l \<Ztypecolon> List2 T)\<close>
*)
consts Nat :: \<open>(nat,nat) \<phi>\<close>
 
declare [[\<phi>trace_reasoning = 0]]
      
\<phi>type_def rounded_Nat :: \<open>nat \<Rightarrow> (nat,nat) \<phi>\<close>
  where \<open>(x \<Ztypecolon> rounded_Nat m) = (x mod m \<Ztypecolon> Nat)\<close>
  deriving Basic

thm List.Implication
thm List.unfold

print_\<phi>reasoners \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ? ?
  

(*
lemma [\<phi>reason 10000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P\<close>
  sorry  *)
 declare [[\<phi>trace_reasoning = 3]]



\<phi>type_def \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::sep_algebra, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 75)
  where [\<phi>defs, \<phi>expns]: \<open>\<phi>MapAt k T = (\<phi>Fun (fun_upd 1 k) \<Zcomp> T)\<close>
  deriving Basic and Identity_Element
       and Functional_Transformation_Functor
       and Separation_Homo
       and Trans_to_Raw_Abst



lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> k = k'
\<Longrightarrow> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> 1(k := v) \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> k' \<^bold>\<rightarrow> T \<w>\<i>\<t>\<h> P\<close>
  by (clarsimp simp add: \<phi>expns Transformation_def, blast)

lemma [\<phi>reason 1200]:
  \<open> Is_Functional (x \<Ztypecolon> T)
\<Longrightarrow> Is_Functional (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  by (clarsimp simp add: \<phi>expns Is_Functional_def, blast)  



(*
TESTING
definition \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 60)
  where \<open>\<phi>MapAt key T x = { 1(key := v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>MapAt_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> key \<^bold>\<rightarrow> T) \<longleftrightarrow> (\<exists>v. p = 1(key := v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>MapAt_def \<phi>Type_def by simp

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> field \<^bold>\<rightarrow> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Conversions\<close>

lemma \<phi>MapAt_\<phi>Prod:
  \<open>k \<^bold>\<rightarrow> (T \<^emph> U) = (k \<^bold>\<rightarrow> T) \<^emph> (k \<^bold>\<rightarrow> U)\<close>
  for T :: \<open>('a::sep_magma_1,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1))
  by (metis fun_1upd_homo_right1)

lemma \<phi>MapAt_\<phi>None:
  \<open>k \<^bold>\<rightarrow> \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

(*
lemma \<phi>MapAt_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> k \<^bold>\<rightarrow> T) = (x' \<Ztypecolon> k \<^bold>\<rightarrow> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>MapAt_simp_cong ("(x \<Ztypecolon> k \<^bold>\<rightarrow> T)") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>MapAt_simp_cong} ctxt)
\<close> *)

paragraph \<open>Implication \& Action rules\<close>

lemma \<phi>MapAt_cast:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma (*[\<phi>reason 1000]: TESTING*)
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P\<close>
  using \<phi>MapAt_cast by (simp add: Premise_def)

(*lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .*)

(* TESTING
lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action to (k' \<^bold>\<rightarrow> Z) \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action to Z \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .*)

(*lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> k' \<^bold>\<rightarrow> Z) \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action as Z \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow> (T \<phi>\<s>\<u>\<b>\<j> P)) = (k \<^bold>\<rightarrow> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)
*)

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> k = k'
\<Longrightarrow> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> 1(k := v) \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> k' \<^bold>\<rightarrow> T \<w>\<i>\<t>\<h> P\<close>
  by (clarsimp simp add: \<phi>expns Transformation_def, blast)

lemma [\<phi>reason 1200]:
  \<open> Is_Functional (x \<Ztypecolon> T)
\<Longrightarrow> Is_Functional (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  by (clarsimp simp add: \<phi>expns Is_Functional_def, blast)

paragraph \<open>Algebraic Properties\<close>

lemma \<phi>MapAt_transformation_functor(*[\<phi>reason 1100]*):
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'
\<Longrightarrow> Transformation_Functor ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k') (\<lambda>x. x) (\<lambda>x. x)\<close>
  unfolding Transformation_Functor_def Premise_def
  by (simp add: \<phi>MapAt_cast)

interpretation \<phi>MapAt: Transformation_Functor_L \<open>(\<^bold>\<rightarrow>) k\<close> \<open>(\<^bold>\<rightarrow>) k'\<close> \<open>(\<lambda>x. x)\<close> \<open>(\<lambda>x. x)\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'\<close>
  by (standard, rule \<phi>MapAt_transformation_functor)

lemma \<phi>MapAt_separation_functor[\<phi>reason 1100]:
  \<open>Separation_Functor ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) T U\<close>
  for T :: \<open>('a::sep_magma_1,'b) \<phi>\<close>
  unfolding Separation_Functor_def \<phi>MapAt_\<phi>Prod ..

lemma \<phi>MapAt_void_functor[\<phi>reason add]:
  \<open>Unit_Functor ((\<^bold>\<rightarrow>) k)\<close>
  unfolding Unit_Functor_def Transformation_def
  by (clarsimp simp add: \<phi>expns; metis fun_1upd1)

interpretation Union_Functor \<open>(\<^bold>\<rightarrow>) k\<close> \<open>(\<^bold>\<rightarrow>) k\<close>
  by (standard; rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

*)

subsubsection \<open>By List of Keys\<close>

(*
definition \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 60)
  where [\<phi>defs, \<phi>expns]: \<open>\<phi>MapAt_L k T = (\<phi>Fun (push_map k) \<Zcomp> T)\<close>

interpretation \<phi>MapAt_L: Transformation_Functor_L \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close> \<open>(\<^bold>\<rightarrow>\<^sub>@) k'\<close> \<open>(\<lambda>x. x)\<close> \<open>(\<lambda>x. x)\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'\<close>
  by (standard, unfold \<phi>MapAt_L_def, \<phi>reason)

lemma \<phi>MapAt_L_separation_functor[\<phi>reason add]:
  \<open>Separation_Functor ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) T U\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_magma_1,'b) \<phi>\<close>
  unfolding \<phi>MapAt_L_def by \<phi>reason

lemma \<phi>MapAt_L_void_functor[\<phi>reason 1100]:
  \<open>Unit_Functor ((\<^bold>\<rightarrow>\<^sub>@) k)\<close>
  unfolding \<phi>MapAt_L_def
  by \<phi>reason *)


definition \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 75)
  where \<open>\<phi>MapAt_L key T x = { push_map key v |v. v \<in> (x \<Ztypecolon> T) }\<close>

abbreviation \<phi>MapAt_L1 :: \<open>'key \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>#" 75)
  where \<open>\<phi>MapAt_L1 key \<equiv> \<phi>MapAt_L [key]\<close>

abbreviation \<phi>MapAt_Lnil :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>[\<^sub>]" 75)
  where \<open>\<phi>MapAt_Lnil key T \<equiv> \<phi>MapAt_L [key] (\<phi>MapAt [] T)\<close>

lemma \<phi>MapAt_L_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) \<longleftrightarrow> (\<exists>v. p = push_map k v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>MapAt_L_def by simp

lemma \<phi>MapAt_L_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> Inhabited (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) \<longrightarrow> C @action \<A>EIF \<close>
  unfolding Inhabited_def
  by (simp add: \<phi>expns)

paragraph \<open>Conversion\<close>

lemma \<phi>MapAt_L_\<phi>MapAt:
  \<open>k1 \<^bold>\<rightarrow>\<^sub>@ k2 \<^bold>\<rightarrow> T = (k1 @ k2) \<^bold>\<rightarrow> T\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns \<phi>MapAt_def; force)

lemma \<phi>MapAt_L_\<phi>MapAt_L:
  \<open>k1 \<^bold>\<rightarrow>\<^sub>@ k2 \<^bold>\<rightarrow>\<^sub>@ T = (k1 @ k2) \<^bold>\<rightarrow>\<^sub>@ T\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; metis push_map_push_map)

lemma \<phi>MapAt_L_\<phi>None:
  \<open>k \<^bold>\<rightarrow>\<^sub>@ \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

(*
lemma [\<phi>reason for \<open>?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub># \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P @action (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub># \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> () \<Ztypecolon> \<circle> @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def by (simp add: implies_refl \<phi>MapAt_L_\<phi>None) *)

(*
lemma \<phi>MapAt_L_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) = (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>MapAt_L_simp_cong ("x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>MapAt_L_simp_cong} ctxt)
\<close>*)

lemma \<phi>MapAt_L_At:
  \<open>(ks \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) = (ks \<^bold>\<rightarrow> T)\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; metis append_self_conv push_map_unit)


paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>MapAt_L_cast:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: \<phi>expns; blast)

(* TESTING
lemma [\<phi>reason 1020]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P\<close>
  using \<phi>MapAt_L_cast by (simp add: Premise_def)*)

lemma [\<phi>reason 1017]:
  \<open> \<g>\<u>\<a>\<r>\<d>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> length k < length k'
&&& \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k @ kd = k'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def \<r>Guard_def conjunction_imp
  apply (clarsimp simp add: \<phi>expns)
  using push_map_push_map by blast

lemma [\<phi>reason 1013]:
  \<open> \<g>\<u>\<a>\<r>\<d>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> length k' < length k
&&& \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k @ kd = k'
\<Longrightarrow> x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def \<r>Guard_def conjunction_imp
  by (clarsimp simp add: \<phi>expns)

(* TESTING
lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def using \<phi>MapAt_L_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow>\<^sub>@ (T \<phi>\<s>\<u>\<b>\<j> P)) = (k \<^bold>\<rightarrow>\<^sub>@ T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)
*)

paragraph \<open>Algebraic Properties\<close>
 
interpretation \<phi>MapAt_L: Functional_Transformation_Functor
    \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close> \<open>(\<^bold>\<rightarrow>\<^sub>@) k'\<close> \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'\<close> \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard, clarsimp simp add: Transformation_Functor_def Transformation_def ExSet_expn Premise_def
      Subjection_expn \<phi>MapAt_L_expns; blast)

interpretation \<phi>MapAt_L: Sep_Homo_Type_Functor_L
    \<open>(\<^bold>\<rightarrow>\<^sub>@) k :: (_ \<Rightarrow> 'a::sep_magma_1,'b) \<phi> \<Rightarrow> _\<close> \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close> \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close> True
  by (standard, (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns),
      smt (verit, ccfv_threshold) push_map_distrib_sep_mult push_map_sep_disj)

lemma \<phi>MapAt_L_left_seminearring_functor[\<phi>reason 1100]:
  \<open>Scala_Semimodule_Functor (\<^bold>\<rightarrow>\<^sub>@) T UNIV\<close>
  unfolding Scala_Semimodule_Functor_def
  by (clarsimp simp add: \<phi>MapAt_L_\<phi>MapAt_L times_list_def)

(*
lemma \<phi>MapAt_L_void_functor[\<phi>reason add]:
  \<open>Unit_Functor ((\<^bold>\<rightarrow>\<^sub>@) k)\<close>
  unfolding Unit_Functor_def Transformation_def
  by (clarsimp simp add: \<phi>expns; metis fun_1upd1)

interpretation \<phi>MapAt_L: Union_Functor \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close> \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close>
  by (standard; rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1000]:
  \<open>Type_Variant_of_the_Same_Functor ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k)\<close>
  unfolding Type_Variant_of_the_Same_Functor_def ..
*)


(* subsection \<open>Down Lifting\<close> (*depreciated*)

definition DownLift :: "('a, 'b) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<phi>" (infixl "<down-lift>" 80)
  where "DownLift N g x = (g x \<Ztypecolon> N)"

lemma DownLift_expn[simp]: " p \<in> (x \<Ztypecolon> N <down-lift> g) \<longleftrightarrow> p \<in> (g x \<Ztypecolon> N) "
  unfolding DownLift_def \<phi>Type_def by simp

lemma [elim!,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> N <down-lift> g) \<Longrightarrow> (Inhabited (g x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

(* lemma [\<phi>cast_overload E]: " x \<Ztypecolon> N <down-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g x \<Ztypecolon> N" unfolding Transformation_def by simp *)
lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> g x = x' \<Longrightarrow> x \<Ztypecolon> N <down-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> N" unfolding Transformation_def by (simp add: \<phi>expns)

(* lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> (g y = x) \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <down-lift> g"
  unfolding Intro_def Transformation_def by (simp add: \<phi>expns) blast
lemma [\<phi>reason, \<phi>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <down-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g y \<Ztypecolon> M"
  unfolding Dest_def Transformation_def by (simp add: \<phi>expns) *)

lemma [\<phi>reason]: " x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y1 \<Ztypecolon> M \<w>\<i>\<t>\<h> P \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y1 = g y  \<Longrightarrow> x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <down-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns)
lemma "\<down>lift_\<phi>app": "\<p>\<a>\<r>\<a>\<m> g \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> g y = x \<Longrightarrow> x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> N <down-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns)



subsection \<open>Up Lifting\<close> (*depreciated*)

definition UpLift :: "('a, 'c) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<phi>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> p \<in> (y \<Ztypecolon> N))}"

lemma UpLift_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <up-lift> f) \<longleftrightarrow> (\<exists>y. (f y = x) \<and> p \<in> (y \<Ztypecolon> N))"
  unfolding UpLift_def \<phi>Type_def by auto

lemma UpLift_inhabited[elim,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> N <up-lift> f) \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> Inhabited (y \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma "\<up>lift_\<phi>app":
  "\<p>\<a>\<r>\<a>\<m> g \<Longrightarrow> \<p>\<a>\<r>\<a>\<m> y \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <up-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns) blast
(* lemma [\<phi>overload D]: "x \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists> \<Ztypecolon> M) "
  unfolding Transformation_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x \<Longrightarrow> \<i>\<n>\<^bold>t\<^bold>r\<^bold>o x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <up-lift> g"
  unfolding Intro_def Transformation_def by (simp add: \<phi>expns) blast *)

lemma [\<phi>reason 130]:
  "x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> M' \<w>\<i>\<t>\<h> P \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x' \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M' <up-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 20]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> N \<w>\<i>\<t>\<h> P x)
\<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> N \<w>\<i>\<t>\<h> (\<exists>x. y = g x \<and> P x)"
  unfolding Transformation_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 150]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' x \<Ztypecolon> M' x \<w>\<i>\<t>\<h> P x)
    \<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>*x. y' x \<Ztypecolon> M' x) \<w>\<i>\<t>\<h> (\<exists>x. y = g x \<and> P x)"
  unfolding Transformation_def by (simp add: \<phi>expns) blast

(* lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. (x \<Ztypecolon> M) \<and>\<^sup>s g x = y)"
  unfolding Dest_def Transformation_def by (simp add: \<phi>expns) blast *)

lemma "x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> N <up-lift> f" unfolding Transformation_def by (simp add: \<phi>expns) blast
lemma "x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> N <up-lift> f" unfolding Transformation_def by (simp add: \<phi>expns) blast

(* lemma "\<phi>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<phi>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<phi>Equal_def by (auto 0 6) *)
*)

section \<open>Semantics Related\<close>

subsection \<open>Value\<close>

subsubsection \<open>Syntax to fetch the latest n-th Val\<close>

(*
setup \<open>let open Ast Phi_Syntax
  fun strip_constrain (Const ("_constrain", _) $ x $ _) = strip_constrain x
    | strip_constrain (Const ("_type_constraint_", _) $ x) = strip_constrain x
    | strip_constrain x = x

  fun name_of_Val (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ v $ _ ))
        = SOME v
    | name_of_Val _ = NONE

  fun get_val ctxt ind =
    let
      val values = Thm.prop_of (Phi_Envir.the_construction ctxt)
                  |> dest_CurrentConstruction |> #4
                  |> strip_separations |> rev
                  |> map_filter name_of_Val
    in if ind < length values
       then List.nth (values, ind)
       else error ("Referring a value that does not exists.")
    end

  fun has_get_val (Const (\<^const_name>\<open>\<phi>__get_val\<close>, _)) = true
    | has_get_val (A $ B) = has_get_val A orelse has_get_val B
    | has_get_val (Abs (_,_,X)) = has_get_val X
    | has_get_val _ = false
  fun map_get_val ctxt (Const (\<^const_name>\<open>\<phi>__get_val\<close>, _) $ X)
        = get_val ctxt (Value.parse_nat (Term.term_name (strip_constrain X)))
    | map_get_val ctxt (A $ B) = map_get_val ctxt A $ map_get_val ctxt B
    | map_get_val ctxt (Abs (name,ty,X)) = Abs (name,ty, map_get_val ctxt X)
    | map_get_val ctxt x = x
 in Context.theory_map (Syntax_Phases.term_check ~10 "\<phi>valiable" (fn ctxt =>
      map (fn x => if has_get_val x then map_get_val ctxt x else x)))
end\<close> *)


subsection \<open>Semantic Type Annotation\<close>

paragraph \<open>Annotation for Single One\<close>

definition Of_Type :: \<open>(VAL,'a) \<phi> \<Rightarrow> TY \<Rightarrow> (VAL,'a) \<phi>\<close> (infix "<of-type>" 23)
  where \<open>(T <of-type> TY) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> Well_Type TY)\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-type> TY) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> p \<in> Well_Type TY\<close>
  unfolding Of_Type_def \<phi>Type_def by (simp add: \<phi>expns)

lemma [elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-type> TY) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> T <of-type> TY) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> T <of-type> TY) TY\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U <of-type> TY \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def \<phi>SemType_def by (simp add: \<phi>expns) blast


paragraph \<open>Annotation for a List\<close>

definition Of_Types :: \<open>(VAL list,'a) \<phi> \<Rightarrow> TY list \<Rightarrow> (VAL list,'a) \<phi>\<close> (infix "<of-types>" 23)
  where \<open>(T <of-types> TYs) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> {p. list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs})\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-types> TYs) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs\<close>
  unfolding Of_Types_def \<phi>Type_def by (simp add: \<phi>expns)

lemma [elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-types> TYs) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> T <of-types> TYs) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast


section \<open>Permission \& Share\<close>

subsection \<open>Share \& Option\<close>

subsubsection \<open>Definition of Properties\<close>

definition \<phi>Sep_Disj :: \<open>('a::sep_disj,'b1) \<phi> \<Rightarrow> ('a::sep_disj,'b2) \<phi> \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj T U \<longleftrightarrow> (\<forall>x y u v. u \<in> (x \<Ztypecolon> T) \<and> v \<in> (y \<Ztypecolon> U) \<longrightarrow> u ## v)\<close>

definition \<phi>Sep_Disj_Inj :: \<open>'a::share_semimodule_sep set \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj_Inj S \<longleftrightarrow> (\<forall>u v. u \<in> S \<and> v \<in> S \<and> u ## v \<longrightarrow> u = v) \<and> (\<forall>u. u \<in> S \<longrightarrow> u ## u)\<close>


subsubsection \<open>Insertion Functor\<close>

declare perm_ins_homo_pointwise[\<phi>reason 1200]
        perm_ins_homo_to_share[\<phi>reason 1200]

definition \<phi>insertion :: \<open>('a::sep_monoid \<Rightarrow> 'b::sep_monoid) \<Rightarrow> 'a set \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi>insertion \<psi> D T = (\<lambda>x. { \<psi> v |v. v \<in> (x \<Ztypecolon> T) \<and> sep_insertion_monoid \<psi> D})\<close>

abbreviation (in sep_insertion_monoid) \<open>\<phi> \<equiv> \<phi>insertion \<psi> D\<close>

lemma \<phi>insertion_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>insertion \<psi> D T)
    \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<in> (x \<Ztypecolon> T) \<and> sep_insertion_monoid \<psi> D)\<close>
  unfolding \<phi>insertion_def \<phi>Type_def by (simp add: \<phi>expns)

lemma (in sep_insertion_monoid) [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>insertion_def \<phi>Type_def by (simp add: \<phi>expns sep_insertion_monoid_axioms)

lemma \<phi>insertion_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>insertion \<psi> D T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> \<phi>insertion \<psi> D T) \<longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

paragraph \<open>Implication\<close>

lemma \<phi>insertion_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp simp add: \<phi>expns; blast)

paragraph \<open>Action\<close>

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>insertion_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (\<phi>insertion \<psi> D Z) \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<w>\<i>\<t>\<h> P @action as Z \<close>
  unfolding Action_Tag_def using \<phi>insertion_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> \<phi>insertion \<psi> D Z) \<close>
  unfolding Action_Tag_def using \<phi>insertion_cast .



paragraph \<open>Simplification\<close>

lemma [simp]:
  \<open>(\<phi>insertion \<psi> D (ExTyp T)) = (\<exists>\<phi> c. \<phi>insertion \<psi> D (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi>insertion \<psi> D (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<phi>insertion \<psi> D T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

(*
lemma \<phi>insertion_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi>insertion \<psi> T) = (x' \<Ztypecolon> \<phi>insertion \<psi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>insertion_simp_cong ("x \<Ztypecolon> \<phi>insertion \<psi> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>insertion_simp_cong} ctxt)
\<close>
*)


lemma \<phi>insertion_\<phi>None:
  assumes prem: \<open>sep_insertion_monoid \<psi> D\<close>
  shows \<open>\<phi>insertion \<psi> D \<circle> = \<circle>\<close>
proof -
  interpret sep_insertion_monoid \<psi> using prem .
  show \<open>\<phi> \<circle> = \<circle>\<close>
    by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns sep_insertion_monoid_axioms)
qed

(* lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> \<phi>insertion ?\<psi> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P @action (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> \<phi>insertion \<psi> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Transformation_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  using inj_at_1_def perm_ins_homo'.axioms(5) by blast *)

lemma \<phi>insertion_MapAt:
  \<open>\<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow> T) = (k \<^bold>\<rightarrow> \<phi>insertion f D T)\<close>
proof (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>MapAt_def
            sep_insertion_monoid_pointwise_eq; rule; clarsimp)
  fix x :: 'a and va :: 'd
  assume \<open>sep_insertion_monoid f D\<close>
  then interpret sep_insertion_monoid f .
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> 1(k := va) = 1(k := v) \<and> (\<exists>va. v = f va \<and> va \<in> (x \<Ztypecolon> T))\<close> by fastforce
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. 1(k := f va) = f \<circ> v \<and> (\<exists>va. v = 1(k := va) \<and> va \<in> (x \<Ztypecolon> T))\<close>
    by (metis \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> 1(k := va) = 1(k := v) \<and> (\<exists>va. v = f va \<and> va \<in> (x \<Ztypecolon> T))\<close> comp_def fun_upd_same)
qed

lemma \<phi>insertion_MapAt_L:
  \<open>\<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow>\<^sub>@ T) = (k \<^bold>\<rightarrow>\<^sub>@ \<phi>insertion ((o) f) (pointwise_set D) T)\<close>
proof (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns
            sep_insertion_monoid_pointwise_eq; rule; clarsimp)
  fix x :: 'a and va :: \<open>'b list \<Rightarrow> 'd\<close>
  assume \<open>sep_insertion_monoid f D\<close>
  then interpret sep_insertion_monoid f .
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> k \<tribullet>\<^sub>m va = k \<tribullet>\<^sub>m v \<and> (\<exists>va. v = f \<circ> va \<and> va \<in> (x \<Ztypecolon> T))\<close>
    using homo_one_axioms push_map_homo by blast
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. k \<tribullet>\<^sub>m (f \<circ> va) = f \<circ> v \<and> (\<exists>va. v = k \<tribullet>\<^sub>m va \<and> va \<in> (x \<Ztypecolon> T))\<close>
    by (metis homo_one_axioms push_map_homo)
qed    


lemma \<phi>insertion_Prod_imply:
  \<open>x \<Ztypecolon> \<phi>insertion f D (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<phi>insertion f D T) \<^emph> (\<phi>insertion f D U)\<close>
  unfolding Transformation_def
  apply (cases x; clarsimp simp add: \<phi>expns \<phi>Sep_Disj_def)
  by (metis homo_sep_def homo_sep_disj_semi_def homo_sep_mult_def sep_insertion.axioms(1) sep_insertion_1.axioms sep_insertion_monoid.axioms perm_ins_homo.axioms(1))

lemma \<phi>insertion_Prod:
  \<open> \<phi>Sep_Disj U T
\<Longrightarrow> \<phi>insertion f D (T \<^emph> U) = (\<phi>insertion f D T) \<^emph> (\<phi>insertion f D U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>Sep_Disj_def; rule; clarsimp)
  apply (metis homo_sep_def homo_sep_disj_semi_def homo_sep_mult_def sep_insertion_1_def sep_insertion_def sep_insertion_monoid_def)
  by (metis homo_sep_def homo_sep_mult.homo_mult sep_insertion_1.axioms(1) sep_insertion_def sep_insertion_monoid.axioms)

thm perm_ins_homo.axioms(1)

subsubsection \<open>Permission Annotation\<close>

definition \<phi>Share :: \<open>rat \<Rightarrow> ('v::share,'x) \<phi> \<Rightarrow> ('v, 'x) \<phi>\<close> (infixr "\<odiv>" 75)
  where \<open>\<phi>Share n T = (\<lambda>x. { share n v |v. v \<in> (x \<Ztypecolon> T) \<and> 0 < n }) \<close>

lemma \<phi>Share_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> n \<odiv> T) \<longleftrightarrow> (\<exists>v. p = share n v \<and> v \<in> (x \<Ztypecolon> T) \<and> 0 < n )\<close>
  unfolding \<phi>Share_def \<phi>Type_def by simp

lemma \<phi>Share_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> n \<odiv> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> 0 < n \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>Share_expn)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> Inhabited (x \<Ztypecolon> n \<odiv> T) \<longrightarrow> 0 < n \<and> C @action \<A>EIF\<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp add: \<phi>Share_expn)


subparagraph \<open>Auxiliary Tag\<close>

(*TODO: depreciate this, or automate this*)

definition half :: \<open>rat \<Rightarrow> rat\<close> where [iff]: \<open>half x = x\<close>

text \<open>Many read-only applicable rules require only non-zero permissions.
  It is reflected as arbitrary schematic variable in the rule, like
    \<^schematic_prop>\<open> x \<Ztypecolon> ?n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z\<close>.
  As arbitrary schematic variable, the reasoner may by mistake instantiate it to be the total
  permission. It is not the optimal, and it is better to only assign a half of the permission
    and to leave the remain half to be used potentially later.
  For example, if a rule requires twice the same resource,
    \<^schematic_prop>\<open> (x \<Ztypecolon> ?n \<odiv> T) * (x \<Ztypecolon> ?m \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z\<close>.
  The best solution is to assign ?n by a half of the current permission and then assign ?m
    the half of the remaining half.

  Unfortunately, the reasoner can hardly be configured to apply this conservative policy, because
  schematic variables have a semantics of accepting any instantiation and there are many short-cut
  reasoning rule trying to solve greedily a local problem by unification.

  An approach is, if a rule may request a same object by twice, add the tag \<^term>\<open>half\<close> on its
    permission to tell explicitly the reasoner to only assign it a half of the permission.
    \<^schematic_prop>\<open> (x \<Ztypecolon> half ?n \<odiv> T) * (x \<Ztypecolon> half ?m \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z\<close>.
\<close>

paragraph \<open>Structural Conversions\<close>

lemma \<phi>Share_1[simp]:
  \<open> 1 \<odiv> T = T \<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

lemma \<phi>Share_\<phi>Share[simp]:
  \<open> 0 < n \<and> 0 < m
\<Longrightarrow> n \<odiv> m \<odiv> T = (m * n) \<odiv> T \<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)
  by (metis mult.commute share_share_not0)
  

lemma \<phi>Share_share:
  \<open> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) * (x \<Ztypecolon> m \<odiv> T) = (x \<Ztypecolon> (n + m) \<odiv> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns set_eq_iff; rule; clarsimp)
  using share_sep_left_distrib_0 apply blast
  subgoal for v
  apply (rule exI[where x=\<open>share n v\<close>], rule exI[where x=\<open>share m v\<close>], simp)
    by (metis share_sep_left_distrib_0) .

lemma \<phi>Share_\<phi>MapAt:
  \<open>n \<odiv> k \<^bold>\<rightarrow> T = k \<^bold>\<rightarrow> n \<odiv> T\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply blast
  by (metis share_fun_updt share_right_one)

lemma \<phi>Share_\<phi>MapAt_L:
  \<open>n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T = k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule)
  apply (clarsimp simp add: share_push_map) apply blast
  apply (clarsimp simp add: share_push_map[symmetric]) by blast

lemma \<phi>Share_\<phi>Prod:
  \<open>n \<odiv> (T \<^emph> U) = (n \<odiv> T) \<^emph> (n \<odiv> U)\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis share_sep_disj_left share_sep_disj_right share_sep_right_distrib_0)
  using share_sep_right_distrib_0 by blast

lemma \<phi>Share_\<phi>None:
  \<open>0 < n \<Longrightarrow> n \<odiv> \<circle> = (\<circle> :: ('a::share_one,unit) \<phi>)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

(*
lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> ?n \<Znrres> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action (?Act::?'b::simplification action)\<close>]:
  \<open>x \<Ztypecolon> n \<Znrres> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>) @action Act\<close>
  for Act :: \<open>'b::simplification action\<close>
  unfolding Transformation_def Action_Tag_def
  by (simp add: \<phi>expns) *)


paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>Share_transformation:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> n \<odiv> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1010]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n = n'
\<Longrightarrow> x \<Ztypecolon> n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> n' \<odiv> U \<w>\<i>\<t>\<h> P\<close>
  using \<phi>Share_transformation by (simp add: Premise_def)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> (m * n) \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> x \<Ztypecolon> n \<odiv> m \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (m * n) \<odiv> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> m \<odiv> T \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow> n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> k \<^bold>\<rightarrow> n \<odiv> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow> T \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> T) \<^emph> (n \<odiv> U) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> (T \<^emph> U) \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> (n \<odiv> T) \<^emph> (n \<odiv> U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> (T \<^emph> U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .


paragraph \<open>Action Rules\<close>

lemma [\<phi>reason 1200]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<odiv> U) \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

(* TESTING
lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<Znrres> U) \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n' = n
\<Longrightarrow> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<Znrres> U) \<w>\<i>\<t>\<h> P @action to (n' \<Znrres> Z)\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<Znrres> U) \<w>\<i>\<t>\<h> P @action as Z\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n' = n
\<Longrightarrow> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<Znrres> U) \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> n' \<Znrres> Z)\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation . *)


paragraph \<open>Simplifications\<close>

lemma [simp]:
  \<open>(n \<odiv> ExTyp T) = (\<exists>\<phi> c. n \<odiv> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(n \<odiv> (T \<phi>\<s>\<u>\<b>\<j> P)) = (n \<odiv> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

(*
lemma \<phi>Share_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) = (x' \<Ztypecolon> n \<Znrres> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Share_simp_cong ("x \<Ztypecolon> n \<Znrres> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>Share_simp_cong} ctxt)
\<close>*)


subparagraph \<open>Permission\<close>

lemma share_split_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> (x \<Ztypecolon> (n+m) \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> n \<odiv> T) * (x \<Ztypecolon> m \<odiv> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share Premise_def)

lemma share_merge_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) * (x \<Ztypecolon> m \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> (n+m) \<odiv> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share Premise_def)

paragraph \<open>Algebraic Properties\<close>

lemma \<phi>Share_left_seminearring_functor[\<phi>reason add]:
  \<open>Scala_Semimodule_Functor (\<odiv>) T {0<..1}\<close>
  unfolding Scala_Semimodule_Functor_def
  by clarsimp

(*
lemma \<phi>Share_void_functor[\<phi>reason add]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n
\<Longrightarrow> Unit_Functor ((\<Znrres>) n :: ('a::share_one, 'b) \<phi> \<Rightarrow> ('a, 'b) \<phi>)\<close>
  unfolding Unit_Functor_def Transformation_def Premise_def
  by (clarsimp simp add: \<phi>Share_expn, insert share_right_one, blast)*)
 
interpretation \<phi>Share: Functional_Transformation_Functor
    \<open>(\<odiv>) n\<close> \<open>(\<odiv>) n'\<close> \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> n = n'\<close> \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard, clarsimp simp add: Transformation_Functor_def Transformation_def ExSet_expn Premise_def
      Subjection_expn \<phi>Share_expn; blast)

interpretation \<phi>Share: Sep_Homo_Type_Functor_L
    \<open>(\<odiv>) n :: ('a::share_semimodule_sep, 'b) \<phi> \<Rightarrow> _\<close> \<open>(\<odiv>) n\<close> \<open>(\<odiv>) n\<close> True
  by ((standard; rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp),
      (insert share_sep_right_distrib_0, blast)[1],
      metis share_sep_disj_left share_sep_disj_right share_sep_right_distrib_0)

lemma [\<phi>reason add]:
  \<open> Near_Semimodule_Functor_zip ((\<odiv>) :: _ \<Rightarrow> ('a::share_semimodule_sep,'b) \<phi> \<Rightarrow> _)
        {n. 0 < n}
        (\<lambda>T x. \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> T) \<and> Object_Equiv T eq \<and> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd x) (fst x)))
        (\<lambda>_ _. fst) \<close>
  unfolding Near_Semimodule_Functor_zip_def \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: Transformation_def \<phi>Prod_expn Object_Equiv_def \<phi>Share_expn Premise_def;
      metis share_sep_left_distrib_0)

lemma [\<phi>reason add]:
  \<open> Near_Semimodule_Functor_zip_rev ((\<odiv>) :: _ \<Rightarrow> ('a::share_semimodule_sep,'b) \<phi> \<Rightarrow> _)
        {n. 0 < n}
        (\<lambda>T x. \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> T) \<and> Object_Equiv T eq \<and> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd x) (fst x)))
        (\<lambda>_ _. fst) \<close>
  unfolding Near_Semimodule_Functor_zip_rev_def \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: Transformation_def \<phi>Prod_expn Object_Equiv_def \<phi>Share_expn Premise_def;
      metis add.commute share_sep_left_distrib_0)

lemma [\<phi>reason add]:
  \<open> Near_Semimodule_Functor_unzip ((\<odiv>) :: _ \<Rightarrow> ('a::share_semimodule_sep,'b) \<phi> \<Rightarrow> _)
        {n. 0 < n}
        (\<lambda>T x. \<phi>Sep_Disj_Inj (x \<Ztypecolon> T))
        (\<lambda>_ _ x. (x,x)) \<close>
  unfolding Near_Semimodule_Functor_unzip_def \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: Transformation_def \<phi>Prod_expn Object_Equiv_def \<phi>Share_expn;
      metis share_sep_disj_left share_sep_disj_right share_sep_left_distrib_0)



subsubsection \<open>\<phi>-Some\<close>

definition \<phi>Some :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<black_circle> _" [91] 90)
  where \<open>\<phi>Some T = (\<lambda>x. { Some v |v. v \<in> (x \<Ztypecolon> T) })\<close>

abbreviation \<phi>Share_Some ("\<fish_eye> _" [91] 90)
  where \<open>\<phi>Share_Some T \<equiv> \<phi>insertion to_share UNIV (\<phi>Some T)\<close>

abbreviation \<phi>Share_Some_L ("\<fish_eye>\<^sub>L _" [91] 90)
  where \<open>\<phi>Share_Some_L T \<equiv> [] \<^bold>\<rightarrow> \<phi>insertion to_share UNIV (\<phi>Some T)\<close>

\<phi>adhoc_overloading \<phi>coercion \<phi>Some \<phi>Share_Some \<phi>Share_Some_L

lemma \<phi>Some_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Some T) \<longleftrightarrow> (\<exists>v. p = Some v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>Some_def by simp

lemma \<phi>Some_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Some T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> \<phi>Some T) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>Some_expn)


paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>Some_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 1070]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (\<black_circle> Z) \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

(* TODO:: fix me!!!
lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P @action to Itself
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Some x' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P @action to Itself \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns) *)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z) \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> \<black_circle> Z) \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .


lemma [simp]:
  \<open>(\<black_circle> ExTyp T) = (\<exists>\<phi> c. \<black_circle> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<black_circle> (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<black_circle> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

(*lemma \<phi>Some_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<black_circle> T) = (x' \<Ztypecolon> \<black_circle> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Some_simp_cong ("x \<Ztypecolon> \<black_circle> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>Some_simp_cong} ctxt)
\<close>*)

lemma [\<phi>reason 1200]:
  \<open> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> Some v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> \<black_circle> T \<w>\<i>\<t>\<h> P\<close>
  by (clarsimp simp add: \<phi>expns Transformation_def)

lemma [\<phi>reason 1200]:
  \<open> Is_Functional (x \<Ztypecolon> T)
\<Longrightarrow> Is_Functional (x \<Ztypecolon> \<black_circle> T)\<close>
  by (clarsimp simp add: \<phi>expns Is_Functional_def)

paragraph \<open>Algebraic Properties\<close>

interpretation \<phi>Some: Functional_Transformation_Functor \<phi>Some \<phi>Some
      \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> True \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard, clarsimp simp add: Transformation_Functor_def Transformation_def ExSet_expn
      Subjection_expn \<phi>Some_expn; blast)

interpretation \<phi>Some: Sep_Homo_Type_Functor_L \<phi>Some \<phi>Some \<phi>Some True
  by (standard, rule \<phi>Type_eqI, clarsimp simp add: \<phi>Prod_expn \<phi>Some_expn, force)


subsubsection \<open>\<phi>Sep_Disj\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj X Y
\<Longrightarrow> \<phi>Sep_Disj X (m \<odiv> Y)\<close>
  for X :: \<open>('a::share_sep_disj,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj Y X
\<Longrightarrow> \<phi>Sep_Disj (m \<odiv> Y) X\<close>
  for X :: \<open>('a::share_sep_disj,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj X \<phi>None\<close>
  for X :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj \<phi>None X\<close>
  for X :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k1 \<noteq> k2
||| \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>Sep_Disj (k1 \<^bold>\<rightarrow> T) (k2 \<^bold>\<rightarrow> U)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def atomize_Branch
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)+

lemma [\<phi>reason 1200]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k1 \<noteq> k2
||| \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>Sep_Disj (k1 \<^bold>\<rightarrow>\<^sub># T) (k2 \<^bold>\<rightarrow>\<^sub># U)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def atomize_Branch
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def push_map_def)+


lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj X A
\<Longrightarrow> \<phi>Sep_Disj X B
\<Longrightarrow> \<phi>Sep_Disj X (A \<^emph> B) \<close>
  for X :: \<open>('a::sep_disj_intuitive, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)

lemma [\<phi>reason 1300]:
  \<open> \<phi>Sep_Disj X Z
\<Longrightarrow> \<phi>Sep_Disj Y Z
\<Longrightarrow> \<phi>Sep_Disj (X \<^emph> Y) Z \<close>
  for X :: \<open>('a::sep_disj_intuitive, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)


subsubsection \<open>\<phi>Sep_Disj_Inj\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> n \<odiv> T)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Inj_\<phi>MapAt[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Inj_\<phi>MapAt_L[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns)
  using push_map_sep_disj by blast

lemma \<phi>Sep_Disj_Inj_Prod[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (y \<Ztypecolon> U)
\<Longrightarrow> \<phi>Sep_Disj_Inj ((x,y) \<Ztypecolon> T \<^emph> U)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis self_disj_I sep_disj_commute sep_disj_multD2 sep_mult_commute)

lemma [\<phi>reason 1190]:
  \<open> \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (snd x \<Ztypecolon> U)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T \<^emph> U)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (cases x; clarsimp simp add: \<phi>expns; metis self_disj_I sep_disj_multD1 sep_disj_multD2)


lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion f D T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow> T)) \<close>
  by (subst \<phi>insertion_MapAt; rule \<phi>Sep_Disj_Inj_\<phi>MapAt)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion ((o) f) (pointwise_set D) T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow>\<^sub>@ T)) \<close>
  by (subst \<phi>insertion_MapAt_L; rule \<phi>Sep_Disj_Inj_\<phi>MapAt_L)

lemma [\<phi>reason 1190]:
  \<open> \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> \<phi>insertion f D T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (snd x \<Ztypecolon> \<phi>insertion f D U)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion f D (T \<^emph> U)) \<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (cases x; simp; smt (verit) Transformation_def \<phi>Sep_Disj_Inj_Prod \<phi>Sep_Disj_Inj_def \<phi>insertion_Prod_imply)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion f D T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (y \<Ztypecolon> \<phi>insertion f D U)
\<Longrightarrow> \<phi>Sep_Disj_Inj ((x,y) \<Ztypecolon> \<phi>insertion f D (T \<^emph> U)) \<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (smt (verit) Transformation_def \<phi>Sep_Disj_Inj_Prod \<phi>Sep_Disj_Inj_def \<phi>insertion_Prod_imply)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion to_share D (\<phi>Some T))\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion to_share D \<phi>None)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>None :: 'a::share_module_sep set) \<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: \<phi>expns)


subsection \<open>Agreement\<close>

definition Agreement :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T agree option, 'x) \<phi>\<close>
  where \<open>Agreement T x = { Some (agree v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma Agreement_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Agreement T) \<longleftrightarrow> (\<exists>v. p = Some (agree v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Agreement_def by simp

lemma Agreement_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> Agreement T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> Agreement T) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: Agreement_expns)

lemma Agreement_times:
  \<open>(w \<Ztypecolon> Agreement W) * (x \<Ztypecolon> Agreement T) = ((w,x) \<Ztypecolon> Agreement (W \<inter>\<^sub>\<phi> T))\<close>
  unfolding set_eq_iff
  apply (clarsimp simp add: \<phi>expns; rule; clarsimp)
  subgoal for v
    by (rule exI[where x=\<open>Some (agree v)\<close>]; rule exI[where x=\<open>Some (agree v)\<close>]; simp) .

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>Agreement (T \<phi>\<s>\<u>\<b>\<j> P) = (Agreement T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>Agreement (ExTyp T) = (\<exists>\<phi>c. Agreement (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

paragraph \<open>Rule\<close>

lemma Agreement_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma Agreement_dup[
  \<phi>reason 1200 for \<open>?x \<Ztypecolon> Agreement ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?U \<w>\<i>\<t>\<h> ?P @action action_dup\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>?x \<Ztypecolon> Agreement ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<w>\<i>\<t>\<h> ?P\<close>
]:
  \<open> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) @action action_dup\<close>
  unfolding Transformation_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for v by (rule exI[where x=\<open>Some (agree v)\<close>]; rule exI[where x=\<open>Some (agree v)\<close>]; simp) .

lemma Agreement_shrink[
  \<phi>reason 1200 for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?U \<w>\<i>\<t>\<h> ?P @action action_shrink\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x \<Ztypecolon> Agreement ?T \<w>\<i>\<t>\<h> ?P\<close>
]:
  \<open> (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Agreement T @action action_shrink \<close>
  unfolding Transformation_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)


lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (Agreement Z)\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action as Z\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Agreement Z)\<close>
  unfolding Action_Tag_def using Agreement_cast .


subsection \<open>Nosep\<close>

definition Nosep :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T nosep, 'x) \<phi>\<close>
  where \<open>Nosep T x = nosep ` (x \<Ztypecolon> T)\<close>

term \<open>\<lambda>T. \<fish_eye> Nosep T\<close>

\<phi>adhoc_overloading \<phi>coercion \<open>\<lambda>T. \<black_circle> Nosep T\<close> \<open>\<lambda>T. \<fish_eye> Nosep T\<close> (* \<open>\<lambda>T. \<fish_eye>\<^sub>L Nosep T\<close> *)

(*TODO: give a configure flag to control this sugar*)
translations
  "\<coercion> T" <= "\<fish_eye> CONST Nosep T"

lemma Nosep_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Nosep T) \<longleftrightarrow> (\<exists>v. p = nosep v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Nosep_def by blast

lemma Nosep_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> Nosep T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> Inhabited (x \<Ztypecolon> Nosep T) \<longrightarrow> C @action \<A>EIF\<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp add: Nosep_expns)


paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>Nosep (T \<phi>\<s>\<u>\<b>\<j> P) = (Nosep T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>Nosep (ExTyp T) = (\<exists>\<phi>c. Nosep (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)


paragraph \<open>Rule\<close>

lemma Nosep_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (Nosep Z)\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P @action as Z\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Nosep Z)\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Nosep _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Itself \<w>\<i>\<t>\<h> _\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> nosep y \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def 
  by (clarsimp simp add: Nosep_expns Itself_expn)


section \<open>Specifc Structures\<close>

subsection \<open>Potentially Uninitialized Structure\<close>

datatype 'V uninit = initialized 'V | uninitialized

instantiation uninit :: (nonsepable_semigroup) nonsepable_semigroup begin
definition \<open>sep_disj_uninit (x::'a uninit) (y::'a uninit) \<longleftrightarrow> False\<close>
instance apply standard unfolding sep_disj_uninit_def by simp_all
end

paragraph \<open>Definition\<close>

text \<open>\<phi>MayInit T relates a value with T if the value is initialized; or if not, it relates the zero
  value of that type with T.\<close>

definition \<phi>MayInit :: \<open>TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (VAL uninit, 'x) \<phi>\<close>
  where \<open>\<phi>MayInit TY T x = ({uninitialized} \<s>\<u>\<b>\<j> (\<exists>z. Zero TY = Some z \<and> z \<in> (x \<Ztypecolon> T))) + initialized ` (x \<Ztypecolon> T <of-type> TY)\<close>

(* abbreviation \<phi>Share_Some_Init ("\<fish_eye>\<lbrakk>_\<rbrakk> _" [0, 91] 90)
  where \<open>\<phi>Share_Some_Init TY T \<equiv> \<fish_eye> \<phi>MayInit TY T\<close> *)

lemma \<phi>MayInit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>MayInit TY T) \<longleftrightarrow> (p = uninitialized \<and> (\<exists>z. Zero TY = Some z \<and> z \<in> (x \<Ztypecolon> T)) \<or> (\<exists>v. p = initialized v \<and> v \<in> (x \<Ztypecolon> T <of-type> TY)))\<close>
  unfolding \<phi>Type_def \<phi>MayInit_def by (simp add: \<phi>expns, blast)

(*
lemma \<phi>MayInit_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>MayInit TY T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast) *)

paragraph \<open>Conversions\<close>

lemma [simp]:
  \<open>\<phi>MayInit TY (T \<phi>\<s>\<u>\<b>\<j> P) = (\<phi>MayInit TY T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>\<phi>MayInit TY (ExTyp T) = (\<exists>\<phi> c. \<phi>MayInit TY (T c))\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

paragraph \<open>Rules\<close>

(*TODO: improve this*)
lemma \<phi>MayInit_cast[\<phi>reason for \<open>?x \<Ztypecolon> \<phi>MayInit ?TY ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<phi>MayInit ?TY' ?U \<w>\<i>\<t>\<h> ?P\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>MayInit_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)


definition \<phi>Uninit :: \<open>('v uninit, unit) \<phi>\<close>
  where \<open>\<phi>Uninit x = {uninitialized}\<close>

lemma \<phi>Uninit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Uninit) \<longleftrightarrow> p = uninitialized\<close>
  unfolding \<phi>Type_def \<phi>Uninit_def by simp

(* TODO
lemma \<phi>Uninit_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Uninit) \<Longrightarrow> C \<Longrightarrow> C\<close> . *)


section \<open>Misc.\<close>

subsection \<open>Forward Simulation\<close>

definition \<phi>F_simulation
    :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> (('av \<times> 'bv) set, ('a \<times> 'b) set) \<phi>\<close> (infixr "\<Rrightarrow>\<^sub>r" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow>\<^sub>r U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>u y. (v,u) \<in> g \<and> (x,y) \<in> f \<and> u \<in> (y \<Ztypecolon> U)) })\<close>

end
