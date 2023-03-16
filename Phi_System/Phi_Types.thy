chapter \<open>Pre-built \<phi>-Types\<close>

theory Phi_Types
  imports IDE_CP_Reasoning2
begin

section \<open>Basics\<close>

subsection \<open>Syntax Sugars\<close>

text \<open>Sometimes, we do not want to verbosely write a semantic type if it is known syntactically.
  We use syntax translation to achieve a sugar to do this.

This is a planning feature has not been implemented\<close>

syntax TY_of_\<phi> :: \<open>('a,'b) \<phi> \<Rightarrow> TY\<close> ("TY'_of'_\<phi>")

consts \<phi>coercion :: \<open>('c1,'a) \<phi> \<Rightarrow> ('c2,'a) \<phi>\<close> ("\<coercion> _" [61] 60)
  \<comment> \<open>A syntax sugar to be overloaded!\<close>

subsection \<open>Identity\<close>

definition Identity :: " ('a,'a) \<phi> " where "Identity x = {x}"

lemma Identity_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> Identity) \<longleftrightarrow> p = x"
  unfolding \<phi>Type_def Identity_def by auto

lemma Identity_inhabited[elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> Identity) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma Identity_functional[\<phi>reason 1000]:
  \<open>is_singleton (x \<Ztypecolon> Identity)\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)

lemma Identity_E[\<phi>reason 10]:
  \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> (x \<Ztypecolon> T) \<Longrightarrow> v \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T\<close>
  unfolding Imply_def Premise_def by (simp add: \<phi>expns)

(*lemma [simp]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> SemTyp_Of (v \<Ztypecolon> Identity) = TY\<close>
  unfolding \<phi>Type_def Identity_def
  by (simp add: \<phi>SemType_def)*)

lemma [\<phi>reason 1200]:
  \<open>is_functional (v \<Ztypecolon> Identity)\<close>
  by (clarsimp simp add: Identity_expn)

lemma satisfication_encoding:
  \<open> (x \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> T \<a>\<n>\<d> P) \<longleftrightarrow> x \<in> (y \<Ztypecolon> T) \<and> P\<close>
  unfolding Imply_def Identity_expn by blast

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v = v'
\<Longrightarrow> v \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> {v'}\<close>
  unfolding Imply_def Identity_expn Premise_def by simp

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v = v'
\<Longrightarrow> {v'} \<i>\<m>\<p>\<l>\<i>\<e>\<s> v \<Ztypecolon> Identity\<close>
  unfolding Imply_def Identity_expn Premise_def by simp


subsection \<open>Func\<close>

definition \<phi>Fun :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('c,'a) \<phi>\<close>
  where [\<phi>defs]: \<open>\<phi>Fun f x = { f x }\<close>

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v = f x
\<Longrightarrow> v \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<phi>Fun f\<close>
  \<medium_left_bracket> construct\<phi> \<open>x \<Ztypecolon> \<phi>Fun f\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = y
\<Longrightarrow> x \<Ztypecolon> \<phi>Fun f \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Identity\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = y
\<Longrightarrow> x \<Ztypecolon> \<phi>Fun f \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Identity @action to Identity\<close> \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open>is_functional (x \<Ztypecolon> \<phi>Fun f)\<close>
  \<medium_left_bracket> to Identity \<medium_right_bracket>. .


subsection \<open>Any\<close>

definition \<phi>Any :: \<open>('x, unit) \<phi>\<close>
  where \<open>\<phi>Any = (\<lambda>_. UNIV)\<close>

lemma \<phi>Any_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Any)\<close>
  unfolding \<phi>Any_def \<phi>Type_def by simp

lemma \<phi>Any_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Any) \<Longrightarrow> C \<Longrightarrow> C\<close>
  .

lemma \<phi>Any_cast [\<phi>reason 1200]:
  \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<phi>Any\<close>
  unfolding Imply_def by (simp add: \<phi>expns)



subsection \<open>Black Hole\<close>

text \<open>The system is a Classical Separation Logic.
  For some situation like garbage collection, Intuitionistic Separation Logic can be more convenient.
  Therefore, we employ a `Black Hole' which can contain arbitrary resources to simulate the
    Intuitionistic Separation Logic\<close>

abbreviation Black_Hole :: \<open>(FIC_N \<Rightarrow> FIC) set\<close>
  where \<open>Black_Hole \<equiv> UNIV\<close>

lemma UNIV_subty [\<phi>reason 1000]:
  \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> UNIV\<close>
  unfolding Imply_def by simp


subsection \<open>Stepwise Abstraction\<close>

definition \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 30)
  where [\<phi>defs]: \<open>\<phi>Composition T U x = (y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<in> (x \<Ztypecolon> U))\<close>

lemma [\<phi>reason 1200]:
  \<open>x \<Ztypecolon> T \<Zcomp> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<in> (x \<Ztypecolon> U) @action to RAW\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> y \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> y \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T \<Zcomp> U \<a>\<n>\<d> P\<close>
  \<medium_left_bracket> premises Y[unfolded Imply_def Identity_expn, simplified, useful]
    construct\<phi> \<open>x \<Ztypecolon> T \<Zcomp> U\<close> \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> is_functional (x \<Ztypecolon> U)
\<Longrightarrow> y \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> T \<Zcomp> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> T \<a>\<n>\<d> P\<close>
  \<medium_left_bracket> premises [unfolded is_functional_def, useful] and [unfolded satisfication_encoding, useful]
    D \<medium_right_bracket>. .

lemma \<phi>Composition_expn:
  \<open>p \<in> (x \<Ztypecolon> T \<Zcomp> U) \<longleftrightarrow> (\<exists>y. p \<in> (y \<Ztypecolon> T) \<and> y \<in> (x \<Ztypecolon> U))\<close>
  unfolding \<phi>Composition_def \<phi>Type_def by (simp add: \<phi>expns)

lemma \<phi>Composition_inhabited[elim,\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> T \<Zcomp> U) \<Longrightarrow> (\<And>y. Inhabited (x \<Ztypecolon> U) \<Longrightarrow> Inhabited (y \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns \<phi>Composition_expn) blast

lemma [\<phi>reason 1200 for \<open>(_ \<Ztypecolon> _ \<Zcomp> _) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (_ \<Ztypecolon> _ \<Zcomp> _) \<a>\<n>\<d> _\<close>]:
  \<open> x1 \<Ztypecolon> U1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> x2 \<Ztypecolon> U2 \<a>\<n>\<d> P
\<Longrightarrow> (x1 \<Ztypecolon> T \<Zcomp> U1) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x2 \<Ztypecolon> T \<Zcomp> U2) \<a>\<n>\<d> P\<close>
  unfolding \<phi>Composition_expn Imply_def by blast


section \<open>Logical Connectives\<close>

subsection \<open>Subjection as a Type\<close>

definition SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<s>\<u>\<b>\<j>" 25)
  where \<open> (T \<phi>\<s>\<u>\<b>\<j> P) = (\<lambda>x. x \<Ztypecolon> T \<s>\<u>\<b>\<j> P) \<close>

translations "TY_of_\<phi> (T \<phi>\<s>\<u>\<b>\<j> P)" \<rightharpoonup> "TY_of_\<phi> T"

lemma SubjectionTY_expn[\<phi>programming_simps, \<phi>expns]:
  \<open>(x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P) = (x \<Ztypecolon> T \<s>\<u>\<b>\<j> P)\<close>
  unfolding set_eq_iff SubjectionTY_def \<phi>Type_def by simp

lemma SubjectionTY_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P) \<Longrightarrow> (P \<Longrightarrow> Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding SubjectionTY_expn using Subjection_inhabited .

lemma [\<phi>reason 1000]:
  \<open> Rewrite_into_\<phi>Type S (x \<Ztypecolon> T)
\<Longrightarrow> Rewrite_into_\<phi>Type (S \<s>\<u>\<b>\<j> P) (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Rewrite_into_\<phi>Type_def by (simp add: SubjectionTY_expn)

lemma [\<phi>reason 1200]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> is_functional (x \<Ztypecolon> T))
\<Longrightarrow> is_functional (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  \<medium_left_bracket> premises [\<phi>reason add] ;; \<medium_right_bracket>. .

subsection \<open>Existential Quantification as a Type\<close>

definition ExTyp :: \<open>('c \<Rightarrow> ('a, 'b) \<phi>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b)\<phi>\<close> (binder "\<exists>\<phi>" 10)
  where \<open>ExTyp T = (\<lambda>x. (\<exists>*c. x c \<Ztypecolon> T c))\<close>

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
                Appl [Constant "\<^const>Phi_Types.ExTyp_binder", idts,
                      (case P of (Appl [Constant "_constrain", Variable "True", _]) => T
                               | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, T, P])]]
      | parse_SetcomprPhiTy ctxt [X,idts,P] =
          Appl [Constant "\<^const>Phi_Types.ExTyp_binder", idts,
                (case P of (Appl [Constant "_constrain", Variable "True", _]) => X
                         | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, X, P])]
  in [(\<^syntax_const>\<open>_SetcomprPhiTy\<close>, parse_SetcomprPhiTy)] end
\<close>

(* TODO
term \<open>x \<Ztypecolon> (X a) \<phi>\<s>\<u>\<b>\<j> a b c. P a\<close>

translations
  " _SetcomprPhiTy' x idts X" <= "x \<Ztypecolon> (\<exists>\<phi> idts. X)"

print_ast_translation \<open>
  [(\<^syntax_const>\<open>_SetcomprPhiTy'\<close>, (fn _ => fn x => hd (@{print} x)))]
\<close>

term \<open>x \<Ztypecolon> (X a) \<phi>\<s>\<u>\<b>\<j> a b c. P a\<close>

*)

lemma ExTyp_expn[\<phi>expns,\<phi>programming_simps]:
  \<open>(x \<Ztypecolon> ExTyp T) = (\<exists>*a. x a \<Ztypecolon> T a)\<close>
  unfolding set_eq_iff ExTyp_def \<phi>Type_def by (simp add: \<phi>expns)

lemma ExTyp_inhabited[elim!, \<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> ExTyp T) \<Longrightarrow> (Inhabited (\<exists>*a. x a \<Ztypecolon> T a) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding ExTyp_expn .

(* lemma [\<phi>reason 1000]:
  \<open> P @action \<A>nap (\<A>_structural (to Identity))
\<Longrightarrow> P @action \<A>nap (to Identity)\<close>
  unfolding Action_Tag_def . *)

lemma Action_to_Identity[\<phi>reason 30]:
  \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (v \<Ztypecolon> Identity \<phi>\<s>\<u>\<b>\<j> v. v \<in> X) @action to Identity\<close>
  unfolding Action_Tag_def Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  \<open> (\<And>a. Rewrite_into_\<phi>Type (S a) (x a \<Ztypecolon> T a))
\<Longrightarrow> Rewrite_into_\<phi>Type (ExSet S) (x \<Ztypecolon> ExTyp T)\<close>
  unfolding Rewrite_into_\<phi>Type_def by (simp add: ExTyp_expn, metis)


subsection \<open>Inter\<close>

definition \<phi>Inter :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<inter>\<^sub>\<phi>" 70)
  where \<open>(T \<inter>\<^sub>\<phi> U) = (\<lambda>(x,y). (x \<Ztypecolon> T) \<inter> (y \<Ztypecolon> U))\<close>

lemma \<phi>Inter_expn[\<phi>expns]:
  \<open>((x,y) \<Ztypecolon> (T \<inter>\<^sub>\<phi> U)) = (x \<Ztypecolon> T) \<inter> (y \<Ztypecolon> U)\<close>
  unfolding set_eq_iff \<phi>Type_def \<phi>Inter_def by simp

lemma \<phi>Inter_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited ((x,y) \<Ztypecolon> (T \<inter>\<^sub>\<phi> U)) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (y \<Ztypecolon> U) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns; blast)


section \<open>Structural Connectives\<close>

subsection \<open>None\<close>

definition \<phi>None :: \<open>('v::one, unit) \<phi>\<close> ("\<circle>")
  where \<open>\<phi>None = (\<lambda>x. { 1 }) \<close>

lemma \<phi>None_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>None) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>None_def \<phi>Type_def by simp

lemma \<phi>None_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>None) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>None_itself_is_one[simp]:
  \<open>(() \<Ztypecolon> \<phi>None) = 1\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open>() \<Ztypecolon> \<phi>None \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 \<Ztypecolon> Identity\<close>
  unfolding Imply_def \<phi>None_expn Identity_expn by simp

subsubsection \<open>Actions\<close>

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<circle> @action to Target \<close>
  unfolding Action_Tag_def using implies_refl .

lemma [\<phi>reason 1200]:
  \<open>() \<Ztypecolon> \<phi>None \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 \<Ztypecolon> Identity @action to Identity\<close> \<medium_left_bracket> \<medium_right_bracket>. .

subsubsection \<open>Rules\<close>

lemma [\<phi>reason 3000]:
  \<open>\<r>Clean (() \<Ztypecolon> \<phi>None)\<close>
  unfolding \<r>Clean_def by simp

lemma [\<phi>reason 1200]:
  \<open>is_functional (() \<Ztypecolon> \<phi>None)\<close>
  \<medium_left_bracket> to Identity \<medium_right_bracket>. .

(*
lemma [\<phi>reason 1500
    for \<open>(() \<Ztypecolon> \<phi>None) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X \<a>\<n>\<d> ?P @action (?Act::?'a::simplification action)\<close>
    except \<open>(() \<Ztypecolon> \<phi>None) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?x \<Ztypecolon> ?T \<a>\<n>\<d> ?P @action (?Act::?'a::simplification action)\<close>
]:
  \<open>(() \<Ztypecolon> \<phi>None) \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def by (simp add: implies_refl)
*)

subsection \<open>Prod\<close>

definition \<phi>Prod :: " ('concrete::sep_magma, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 55)
  where "A \<^emph> B = (\<lambda>(a,b). B b * A a)"

lemma \<phi>Prod_expn[\<phi>expns]:
  "concrete \<in> ((a,b) \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>cb ca. concrete = cb * ca \<and> cb \<in> (b \<Ztypecolon> B) \<and> ca \<in> (a \<Ztypecolon> A) \<and> cb ## ca)"
  unfolding \<phi>Prod_def \<phi>Type_def times_set_def by simp

lemma \<phi>Prod_expn'[assertion_simps]:
  \<open>((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma \<phi>Prod_inhabited[elim!,\<phi>inhabitance_rule]:
  "Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<Longrightarrow> (Inhabited (x1 \<Ztypecolon> T1) \<Longrightarrow> Inhabited (x2 \<Ztypecolon> T2) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

(* lemma \<phi>Prod_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<longleftrightarrow> Inhabited (x1 \<Ztypecolon> T1) \<and> Inhabited (x2 \<Ztypecolon> T2)\<close>
  unfolding Inhabited_def apply (simp add: \<phi>expns) *)

lemma \<phi>Prod_split: "((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)"
  by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Prod_\<phi>None:
  \<open>((x',y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'a::sep_magma_1 set)\<close>
  \<open>((x,y') \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'b::sep_magma_1 set)\<close>
  unfolding set_eq_iff
  by (simp_all add: \<phi>expns)

(*lemma (in \<phi>empty) SepNu_to_SepSet: "(OBJ (a,b) \<Ztypecolon> A \<^emph> B) = (OBJ a \<Ztypecolon> A) * (OBJ b \<Ztypecolon> B)"
  by (simp add: \<phi>expns set_eq_iff times_list_def) *)

subsubsection \<open>Reasoning Rules\<close>

(* paragraph \<open>View Shift\<close>

lemma [\<phi>reason for \<open>(?x,?y) \<Ztypecolon> ?N \<^emph> ?M \<s>\<h>\<i>\<f>\<t>\<s> (?x',?y') \<Ztypecolon> ?N' \<^emph> ?M' \<a>\<n>\<d> ?P\<close>]:
  " x \<Ztypecolon> N \<s>\<h>\<i>\<f>\<t>\<s> x' \<Ztypecolon> N' \<a>\<n>\<d> P1
\<Longrightarrow> y \<Ztypecolon> M \<s>\<h>\<i>\<f>\<t>\<s> y' \<Ztypecolon> M' \<a>\<n>\<d> P2
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<s>\<h>\<i>\<f>\<t>\<s> (x',y') \<Ztypecolon> N' \<^emph> M' \<a>\<n>\<d> P1 \<and> P2"
  unfolding View_Shift_def \<phi>Prod_expn'
  by (smt (verit, best) mult.commute mult.left_commute)  *)

(*do not add it to \<phi>-LPR because we have stronger reasoning mechanisms*)
lemma \<phi>Prod_transformation:
  " x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> N' \<a>\<n>\<d> P1
\<Longrightarrow> y \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' \<Ztypecolon> M' \<a>\<n>\<d> P2
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x',y') \<Ztypecolon> N' \<^emph> M' \<a>\<n>\<d> P1 \<and> P2"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (y \<Ztypecolon> U)
\<Longrightarrow> \<r>Clean ((x,y) \<Ztypecolon> T \<^emph> U)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<r>Clean_def \<phi>Prod_expn' Imply_def
  apply (simp add: \<phi>expns)
  using mult_1_class.mult_1_left by blast

lemma [\<phi>reason 1200]:
  \<open> is_functional (x \<Ztypecolon> T)
\<Longrightarrow> is_functional (y \<Ztypecolon> U)
\<Longrightarrow> is_functional ((x,y) \<Ztypecolon> T \<^emph> U)\<close>
  unfolding is_functional_def set_eq_iff
  by (simp add: \<phi>expns, blast)


subsubsection \<open>Action\<close>

lemma [\<phi>reason 1200]:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action \<A>_structural act
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action \<A>_structural act
\<Longrightarrow> A * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * Y \<a>\<n>\<d> P \<and> Q @action \<A>_structural act\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma prod_transform_to1:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action to T
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action to U
\<Longrightarrow> A * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * Y \<a>\<n>\<d> P \<and> Q @action to (T \<^emph> U)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma prod_transform_to2:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action to U
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action to T
\<Longrightarrow> A * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * Y \<a>\<n>\<d> P \<and> Q @action to (T \<^emph> U)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

declare [[\<phi>reason 1200 prod_transform_to1 prod_transform_to2
      for \<open>?A * ?B \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (?T \<^emph> ?U)\<close>]]

hide_fact prod_transform_to1 prod_transform_to2

lemma [\<phi>reason 1100]:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action to T
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action to T
\<Longrightarrow> A * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * Y \<a>\<n>\<d> P \<and> Q @action to T\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma Prod_transform_to1:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P @action to A
\<Longrightarrow> y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' \<Ztypecolon> U' \<a>\<n>\<d> Q @action to B
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<a>\<n>\<d> P \<and> Q @action to (A \<^emph> B)\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .

lemma Prod_transform_to2:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P @action to B
\<Longrightarrow> y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' \<Ztypecolon> U' \<a>\<n>\<d> Q @action to A
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<a>\<n>\<d> P \<and> Q @action to (A \<^emph> B)\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .

declare [[\<phi>reason 1200 Prod_transform_to1 Prod_transform_to2
      for \<open>(?x,?y) \<Ztypecolon> (?T \<^emph> ?U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (?A \<^emph> ?B)\<close>]]

hide_fact Prod_transform_to1 Prod_transform_to2

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P @action to Target
\<Longrightarrow> y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' \<Ztypecolon> U' \<a>\<n>\<d> Q @action to Target
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<a>\<n>\<d> P \<and> Q @action to Target\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .


lemma [\<phi>reason 1000]:
  \<open> P @action as ((x \<Ztypecolon> T) * (y \<Ztypecolon> U))
\<Longrightarrow> P @action as ((x,y) \<Ztypecolon> (T \<^emph> U)) \<close>
  unfolding Action_Tag_def .

lemma prod_transform_as1:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action as M
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action as N
\<Longrightarrow> A * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * Y \<a>\<n>\<d> P \<and> Q @action as (M * N)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma prod_transform_as2:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action to N
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action to M
\<Longrightarrow> A * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * Y \<a>\<n>\<d> P \<and> Q @action to (M * N)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

declare [[\<phi>reason 1200 prod_transform_as1 prod_transform_as2
      for \<open>?A * ?B \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to (?M * ?N)\<close>]]

hide_fact prod_transform_as1 prod_transform_as2

lemma [\<phi>reason 1100]:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action as T
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action as T
\<Longrightarrow> A * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * Y \<a>\<n>\<d> P \<and> Q @action as T\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma Prod_transform_as1:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P @action as A
\<Longrightarrow> y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' \<Ztypecolon> U' \<a>\<n>\<d> Q @action as B
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<a>\<n>\<d> P \<and> Q @action as (A * B)\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .

lemma Prod_transform_as2:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P @action as B
\<Longrightarrow> y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' \<Ztypecolon> U' \<a>\<n>\<d> Q @action as A
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<a>\<n>\<d> P \<and> Q @action as (A * B)\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .

declare [[\<phi>reason 1200 Prod_transform_as1 Prod_transform_as2
      for \<open>(?x,?y) \<Ztypecolon> (?T \<^emph> ?U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action as (?A * ?B)\<close>]]

hide_fact Prod_transform_as1 Prod_transform_as2

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P @action as Target
\<Longrightarrow> y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' \<Ztypecolon> U' \<a>\<n>\<d> Q @action as Target
\<Longrightarrow> (x,y) \<Ztypecolon> (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x',y') \<Ztypecolon> (T' \<^emph> U') \<a>\<n>\<d> P \<and> Q @action as Target\<close>
  unfolding Action_Tag_def
  using \<phi>Prod_transformation .


paragraph \<open>Simplification\<close>

lemma \<phi>Prod_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (y \<Ztypecolon> U) = (y' \<Ztypecolon> U')
\<Longrightarrow> ((x,y) \<Ztypecolon> T \<^emph> U) = ((x',y') \<Ztypecolon> T' \<^emph> U')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Prod_simp_cong ("(x,y) \<Ztypecolon> (T \<^emph> U)") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>Prod_simp_cong} ctxt)
\<close>

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

lemma List_Item_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> List_Item T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<comment> \<open>A example for how to represent multi-elements list\<close>
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

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Empty_List) \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsection \<open>Optional\<close>

definition \<phi>Optional :: \<open>('c,'x) \<phi> \<Rightarrow> bool \<Rightarrow> ('c::one,'x) \<phi>\<close> (infix "?\<^sub>\<phi>" 55)
  where \<open>(T ?\<^sub>\<phi> C) = (\<lambda>x. if C then (x \<Ztypecolon> T) else 1)\<close>

lemma \<phi>Optional_expn[\<phi>expns]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> C) = (if C then x \<Ztypecolon> T else 1)\<close>
  unfolding \<phi>Type_def \<phi>Optional_def by simp

lemma \<phi>Optional_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T ?\<^sub>\<phi> C) \<Longrightarrow> ((C \<Longrightarrow> Inhabited (x \<Ztypecolon> T)) \<Longrightarrow> Z) \<Longrightarrow> Z\<close>
  unfolding Inhabited_def by (cases C; clarsimp simp add: \<phi>expns)

subsubsection \<open>Conversion\<close>

lemma [simp]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> True) = (x \<Ztypecolon> T)\<close>
  unfolding set_eq_iff by (simp add: \<phi>Optional_expn)

lemma [simp]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> False) = 1\<close>
  unfolding set_eq_iff by (simp add: \<phi>Optional_expn)

subsubsection \<open>Rules\<close>

lemma [\<phi>reason 3000 for \<open>\<r>Clean (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C)\<close>]:
  \<open> \<r>Clean (x \<Ztypecolon> T ?\<^sub>\<phi> False) \<close>
  unfolding \<r>Clean_def by simp



subsection \<open>Mapping\<close>

definition \<phi>Mapping :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> ('av \<Rightarrow> 'bv, 'a \<Rightarrow> 'b) \<phi>\<close> (infixr "\<Rrightarrow>" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow> U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U) })\<close>

lemma \<phi>Mapping_expn[\<phi>expns]:
  \<open>g \<in> (f \<Ztypecolon> T \<Rrightarrow> U) \<longleftrightarrow> (\<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U))\<close>
  unfolding \<phi>Mapping_def \<phi>Type_def by simp

lemma \<phi>Mapping_inhabited[\<phi>expns]:
  \<open>Inhabited (f \<Ztypecolon> T \<Rrightarrow> U) \<Longrightarrow> ((\<And>x. Inhabited (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (f x \<Ztypecolon> U)) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)


subsection \<open>Point on a Mapping\<close>

subsubsection \<open>By Key\<close>

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
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1))
  by (metis fun_1upd_homo_right1)

lemma \<phi>MapAt_\<phi>None:
  \<open>k \<^bold>\<rightarrow> \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

(*
lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> ?k \<^bold>\<rightarrow> \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y @action (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> k \<^bold>\<rightarrow> \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> () \<Ztypecolon> \<circle> @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def
  by (simp add: implies_refl \<phi>MapAt_\<phi>None) *)

lemma \<phi>MapAt_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> k \<^bold>\<rightarrow> T) = (x' \<Ztypecolon> k \<^bold>\<rightarrow> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>MapAt_simp_cong ("(x \<Ztypecolon> k \<^bold>\<rightarrow> T)") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>MapAt_simp_cong} ctxt)
\<close>

paragraph \<open>Implication \& Action rules\<close>

lemma \<phi>MapAt_cast:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<a>\<n>\<d> P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1000]:
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> k = k'
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow> U \<a>\<n>\<d> P\<close>
  using \<phi>MapAt_cast by (simp add: Premise_def)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<a>\<n>\<d> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<a>\<n>\<d> P @action to (k' \<^bold>\<rightarrow> Z) \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<a>\<n>\<d> P @action to Z \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> k' \<^bold>\<rightarrow> Z) \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<a>\<n>\<d> P @action as Z \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow> ExTyp T) = (\<exists>\<phi> c. k \<^bold>\<rightarrow> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow> (T \<phi>\<s>\<u>\<b>\<j> P)) = (k \<^bold>\<rightarrow> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  unfolding \<r>Clean_def Imply_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis fun_1upd1)

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> k = k'
\<Longrightarrow> v \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> v' \<Ztypecolon> T \<a>\<n>\<d> P
\<Longrightarrow> 1(k := v) \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> v' \<Ztypecolon> k' \<^bold>\<rightarrow> T \<a>\<n>\<d> P\<close>
  by (clarsimp simp add: \<phi>expns Imply_def, blast)

lemma [\<phi>reason 1200]:
  \<open> is_functional (x \<Ztypecolon> T)
\<Longrightarrow> is_functional (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  by (clarsimp simp add: \<phi>expns is_functional_def, blast)


subsubsection \<open>By List of Keys\<close>

definition \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 60)
  where \<open>\<phi>MapAt_L key T x = { push_map key v |v. v \<in> (x \<Ztypecolon> T) }\<close>

abbreviation \<phi>MapAt_L1 :: \<open>'key \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>#" 60)
  where \<open>\<phi>MapAt_L1 key \<equiv> \<phi>MapAt_L [key]\<close>

abbreviation \<phi>MapAt_Lnil :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>[\<^sub>]" 60)
  where \<open>\<phi>MapAt_Lnil key T \<equiv> \<phi>MapAt_L [key] (\<phi>MapAt [] T)\<close>

lemma \<phi>MapAt_L_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) \<longleftrightarrow> (\<exists>v. p = push_map k v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>MapAt_L_def by simp

lemma \<phi>MapAt_L_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Conversion\<close>

lemma \<phi>MapAt_L_\<phi>Prod:
  \<open>k \<^bold>\<rightarrow>\<^sub>@ (T \<^emph> U) = (k \<^bold>\<rightarrow>\<^sub>@ T) \<^emph> (k \<^bold>\<rightarrow>\<^sub>@ U)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule)
  apply (clarsimp simp add: push_map_distrib_sep_mult[symmetric])
  using push_map_sep_disj apply blast
  apply (clarsimp simp add: push_map_distrib_sep_mult)
  by blast

lemma \<phi>MapAt_L_\<phi>MapAt:
  \<open>k1 \<^bold>\<rightarrow>\<^sub>@ k2 \<^bold>\<rightarrow> T = k1 @ k2 \<^bold>\<rightarrow> T\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; force)

lemma \<phi>MapAt_L_\<phi>MapAt_L:
  \<open>k1 \<^bold>\<rightarrow>\<^sub>@ k2 \<^bold>\<rightarrow>\<^sub>@ T = k1 @ k2 \<^bold>\<rightarrow>\<^sub>@ T\<close>
  apply (rule \<phi>Type_eqI; simp add: \<phi>expns)
  by (metis push_map_push_map)

lemma \<phi>MapAt_L_\<phi>None:
  \<open>k \<^bold>\<rightarrow>\<^sub>@ \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

(*
lemma [\<phi>reason for \<open>?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub># \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X \<a>\<n>\<d> ?P @action (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub># \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> () \<Ztypecolon> \<circle> @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def by (simp add: implies_refl \<phi>MapAt_L_\<phi>None) *)

lemma \<phi>MapAt_L_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) = (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>MapAt_L_simp_cong ("x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>MapAt_L_simp_cong} ctxt)
\<close>

lemma \<phi>MapAt_L_At:
  \<open>(ks \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) = (ks \<^bold>\<rightarrow> T)\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; metis append_self_conv push_map_unit)

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T)\<close>
  unfolding \<r>Clean_def Imply_def
  apply (simp add: \<phi>expns)
  using push_map_1 by blast



paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>MapAt_L_cast:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U \<a>\<n>\<d> P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1020]:
  \<open> \<r>REQUIRE \<s>\<i>\<m>\<p>\<r>\<e>\<m> k' = k
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<a>\<n>\<d> P\<close>
  using \<phi>MapAt_L_cast by (simp add: Premise_def)

lemma [\<phi>reason 1017]:
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> length k < length k'
&&& \<s>\<i>\<m>\<p>\<r>\<e>\<m> k @ kd = k'
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<a>\<n>\<d> P\<close>
  unfolding Imply_def \<r>Require_def conjunction_imp
  apply (clarsimp simp add: \<phi>expns)
  using push_map_push_map by blast

lemma [\<phi>reason 1013]:
  \<open> \<r>REQUIRE
    \<s>\<i>\<m>\<p>\<r>\<e>\<m> length k' < length k
&&& \<s>\<i>\<m>\<p>\<r>\<e>\<m> k @ kd = k'
\<Longrightarrow> x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<a>\<n>\<d> P\<close>
  unfolding Imply_def \<r>Require_def conjunction_imp
  by (clarsimp simp add: \<phi>expns)


lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U \<a>\<n>\<d> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def using \<phi>MapAt_L_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow>\<^sub>@ ExTyp T) = (\<exists>\<phi> c. k \<^bold>\<rightarrow>\<^sub>@ T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow>\<^sub>@ (T \<phi>\<s>\<u>\<b>\<j> P)) = (k \<^bold>\<rightarrow>\<^sub>@ T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

(* subsection \<open>Down Lifting\<close> (*depreciated*)

definition DownLift :: "('a, 'b) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<phi>" (infixl "<down-lift>" 80)
  where "DownLift N g x = (g x \<Ztypecolon> N)"

lemma DownLift_expn[simp]: " p \<in> (x \<Ztypecolon> N <down-lift> g) \<longleftrightarrow> p \<in> (g x \<Ztypecolon> N) "
  unfolding DownLift_def \<phi>Type_def by simp

lemma [elim!,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> N <down-lift> g) \<Longrightarrow> (Inhabited (g x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

(* lemma [\<phi>cast_overload E]: " x \<Ztypecolon> N <down-lift> g \<i>\<m>\<p>\<l>\<i>\<e>\<s> g x \<Ztypecolon> N" unfolding Imply_def by simp *)
lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> g x = x' \<Longrightarrow> x \<Ztypecolon> N <down-lift> g \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> N" unfolding Imply_def by (simp add: \<phi>expns)

(* lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> (g y = x) \<Longrightarrow> x \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> M <down-lift> g"
  unfolding Intro_def Imply_def by (simp add: \<phi>expns) blast
lemma [\<phi>reason, \<phi>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <down-lift> g \<i>\<m>\<p>\<l>\<i>\<e>\<s> g y \<Ztypecolon> M"
  unfolding Dest_def Imply_def by (simp add: \<phi>expns) *)

lemma [\<phi>reason]: " x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> y1 \<Ztypecolon> M \<a>\<n>\<d> P \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y1 = g y  \<Longrightarrow> x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> M <down-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns)
lemma "\<down>lift_\<phi>app": "\<p>\<a>\<r>\<a>\<m> g \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> g y = x \<Longrightarrow> x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> N <down-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns)



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
  "\<p>\<a>\<r>\<a>\<m> g \<Longrightarrow> \<p>\<a>\<r>\<a>\<m> y \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x \<Longrightarrow> x \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> M <up-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns) blast
(* lemma [\<phi>overload D]: "x \<Ztypecolon> M <up-lift> g \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<exists> \<Ztypecolon> M) "
  unfolding Imply_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x \<Longrightarrow> \<i>\<n>\<^bold>t\<^bold>r\<^bold>o x \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> M <up-lift> g"
  unfolding Intro_def Imply_def by (simp add: \<phi>expns) blast *)

lemma [\<phi>reason 130]:
  "x \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> M' \<a>\<n>\<d> P \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x' \<Longrightarrow> x \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> M' <up-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 20]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> N \<a>\<n>\<d> P x)
\<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<i>\<m>\<p>\<l>\<i>\<e>\<s> N \<a>\<n>\<d> (\<exists>x. y = g x \<and> P x)"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 150]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<i>\<m>\<p>\<l>\<i>\<e>\<s> y' x \<Ztypecolon> M' x \<a>\<n>\<d> P x)
    \<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<exists>*x. y' x \<Ztypecolon> M' x) \<a>\<n>\<d> (\<exists>x. y = g x \<and> P x)"
  unfolding Imply_def by (simp add: \<phi>expns) blast

(* lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <up-lift> g \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<exists>* x. (x \<Ztypecolon> M) \<and>\<^sup>s g x = y)"
  unfolding Dest_def Imply_def by (simp add: \<phi>expns) blast *)

lemma "x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> f x \<Ztypecolon> N <up-lift> f" unfolding Imply_def by (simp add: \<phi>expns) blast
lemma "x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> f x \<Ztypecolon> N <up-lift> f" unfolding Imply_def by (simp add: \<phi>expns) blast

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

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-type> TY) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> T <of-type> TY) TY\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U <of-type> TY \<a>\<n>\<d> P\<close>
  unfolding Imply_def \<phi>SemType_def by (simp add: \<phi>expns) blast


paragraph \<open>Annotation for a List\<close>

definition Of_Types :: \<open>(VAL list,'a) \<phi> \<Rightarrow> TY list \<Rightarrow> (VAL list,'a) \<phi>\<close> (infix "<of-types>" 23)
  where \<open>(T <of-types> TYs) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> {p. list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs})\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-types> TYs) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs\<close>
  unfolding Of_Types_def \<phi>Type_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-types> TYs) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast


section \<open>Permission \& Share\<close>

subsection \<open>Share \& Option\<close>

subsubsection \<open>Definition of Properties\<close>

definition \<phi>Sep_Disj :: \<open>('a::sep_disj,'b1) \<phi> \<Rightarrow> ('a::sep_disj,'b2) \<phi> \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj T U \<longleftrightarrow> (\<forall>x y u v. u \<in> (x \<Ztypecolon> T) \<and> v \<in> (y \<Ztypecolon> U) \<longrightarrow> u ## v)\<close>

definition \<phi>Sep_Disj_Identical :: \<open>('a::share_semimodule_sep, 'b) \<phi> \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj_Identical T
    \<longleftrightarrow> (\<forall>x u v. u \<in> (x \<Ztypecolon> T) \<and> v \<in> (x \<Ztypecolon> T) \<and> u ## v \<longrightarrow> u = v)
      \<and> (\<forall>x u. u \<in> (x \<Ztypecolon> T) \<longrightarrow> u ## u)\<close>


subsubsection \<open>Permission Functor\<close>

definition \<phi>perm_ins_homo :: \<open>('a::sep_algebra \<Rightarrow> 'b::share_module_sep) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi>perm_ins_homo \<psi> T = (\<lambda>x. { \<psi> v |v. v \<in> (x \<Ztypecolon> T) \<and> perm_ins_homo' \<psi>})\<close>

abbreviation (in perm_ins_homo) \<open>\<phi> \<equiv> \<phi>perm_ins_homo \<psi>\<close>

lemma \<phi>perm_ins_homo_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T)
    \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<in> (x \<Ztypecolon> T) \<and> perm_ins_homo' \<psi>)\<close>
  unfolding \<phi>perm_ins_homo_def \<phi>Type_def by (simp add: \<phi>expns)

lemma (in perm_ins_homo) [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>perm_ins_homo_def \<phi>Type_def by (simp add: \<phi>expns)

lemma \<phi>perm_ins_homo_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

paragraph \<open>Implication\<close>

lemma \<phi>perm_ins_homo_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns; blast)

paragraph \<open>Action\<close>

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U \<a>\<n>\<d> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>perm_ins_homo_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U \<a>\<n>\<d> P @action to Z \<close>
  unfolding Action_Tag_def using \<phi>perm_ins_homo_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U \<a>\<n>\<d> P @action to (\<phi>perm_ins_homo \<psi> Z) \<close>
  unfolding Action_Tag_def using \<phi>perm_ins_homo_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as Z
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U \<a>\<n>\<d> P @action as Z \<close>
  unfolding Action_Tag_def using \<phi>perm_ins_homo_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>perm_ins_homo \<psi> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> \<phi>perm_ins_homo \<psi> Z) \<close>
  unfolding Action_Tag_def using \<phi>perm_ins_homo_cast .



paragraph \<open>Simplification\<close>

lemma [simp]:
  \<open>(\<phi>perm_ins_homo \<psi> (ExTyp T)) = (\<exists>\<phi> c. \<phi>perm_ins_homo \<psi> (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi>perm_ins_homo \<psi> (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<phi>perm_ins_homo \<psi> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>perm_ins_homo_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T) = (x' \<Ztypecolon> \<phi>perm_ins_homo \<psi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>perm_ins_homo_simp_cong ("x \<Ztypecolon> \<phi>perm_ins_homo \<psi> T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>perm_ins_homo_simp_cong} ctxt)
\<close>


lemma \<phi>perm_ins_homo_\<phi>None:
  \<open> perm_ins_homo' \<psi>
\<Longrightarrow> \<phi>perm_ins_homo \<psi> \<circle> = \<circle>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)
  by (metis inj_at_1_def perm_ins_homo'.axioms(5))

(* lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> \<phi>perm_ins_homo ?\<psi> \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X \<a>\<n>\<d> ?P @action (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> \<phi>perm_ins_homo \<psi> \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<circle> @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Imply_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  using inj_at_1_def perm_ins_homo'.axioms(5) by blast *)

lemma \<phi>perm_ins_homo_MapAt:
  \<open>\<phi>perm_ins_homo ((o) f) (k \<^bold>\<rightarrow> T) = (k \<^bold>\<rightarrow> \<phi>perm_ins_homo f T)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>perm_ins_homo_expns
            perm_ins_homo_pointwise_eq; rule; clarsimp)
  using inj_at_1.inj_at_1 perm_ins_homo'.axioms(5) apply fastforce
  by (metis fun_upd_comp inj_at_1.inj_at_1 perm_ins_homo'.axioms(5) perm_ins_homo_pointwise)


lemma \<phi>perm_ins_homo_MapAt_L:
  \<open>\<phi>perm_ins_homo ((o) f) (k \<^bold>\<rightarrow>\<^sub>@ T) = (k \<^bold>\<rightarrow>\<^sub>@ \<phi>perm_ins_homo ((o) f) T)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>perm_ins_homo_expns
            perm_ins_homo_pointwise_eq; rule; clarsimp)
  using homo_one.push_map_homo homo_sep_mult_def perm_ins_homo'.axioms(1) apply blast
  by (metis homo_one.push_map_homo homo_sep_mult_def perm_ins_homo'.axioms(1) push_map_sep_disj)


lemma \<phi>perm_ins_homo_Prod_imply:
  \<open>x \<Ztypecolon> \<phi>perm_ins_homo f (T \<^emph> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> (\<phi>perm_ins_homo f T) \<^emph> (\<phi>perm_ins_homo f U)\<close>
  unfolding Imply_def
  apply (cases x; clarsimp simp add: \<phi>expns \<phi>Sep_Disj_def)
  using homo_sep_disj_semi_def homo_sep_mult.homo_mult perm_ins_homo'_def by blast

lemma \<phi>perm_ins_homo_Prod:
  \<open> \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>perm_ins_homo f (T \<^emph> U) = (\<phi>perm_ins_homo f T) \<^emph> (\<phi>perm_ins_homo f U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>Sep_Disj_def; rule; clarsimp)
  using homo_sep_disj_semi_def homo_sep_mult.homo_mult perm_ins_homo'_def apply blast
  by (metis homo_sep_mult.homo_mult perm_ins_homo'_def sep_disj_commute)


subsubsection \<open>Permission Annotation\<close>

definition \<phi>Share :: \<open>rat \<Rightarrow> ('v::share,'x) \<phi> \<Rightarrow> ('v, 'x) \<phi>\<close> (infixr "\<Znrres>" 60)
  where \<open>\<phi>Share n T = (\<lambda>x. { share n v |v. v \<in> (x \<Ztypecolon> T) \<and> 0 < n }) \<close>

lemma \<phi>Share_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> n \<Znrres> T) \<longleftrightarrow> (\<exists>v. p = share n v \<and> v \<in> (x \<Ztypecolon> T) \<and> 0 < n )\<close>
  unfolding \<phi>Share_def \<phi>Type_def by simp

lemma \<phi>Share_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> n \<Znrres> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> 0 < n \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

subparagraph \<open>Auxiliary Tag\<close>

definition half :: \<open>rat \<Rightarrow> rat\<close> where [iff]: \<open>half x = x\<close>

text \<open>Many read-only applicable rules require only non-zero permissions.
  It is reflected as arbitrary schematic variable in the rule, like
    \<^schematic_prop>\<open> x \<Ztypecolon> ?n \<Znrres> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Z\<close>.
  As arbitrary schematic variable, the reasoner may by mistake instantiate it to be the total
  permission. It is not the optimal, and it is better to only assign a half of the permission
    and to leave the remain half to be used potentially later.
  For example, if a rule requires twice the same resource,
    \<^schematic_prop>\<open> (x \<Ztypecolon> ?n \<Znrres> T) * (x \<Ztypecolon> ?m \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Z\<close>.
  The best solution is to assign ?n by a half of the current permission and then assign ?m
    the half of the remaining half.

  Unfortunately, the reasoner can hardly be configured to apply this conservative policy, because
  schematic variables have a semantics of accepting any instantiation and there are many short-cut
  reasoning rule trying to solve greedily a local problem by unification.

  An approach is, if a rule may request a same object by twice, add the tag \<^term>\<open>half\<close> on its
    permission to tell explicitly the reasoner to only assign it a half of the permission.
    \<^schematic_prop>\<open> (x \<Ztypecolon> half ?n \<Znrres> T) * (x \<Ztypecolon> half ?m \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Z\<close>.
\<close>

paragraph \<open>Structural Conversions\<close>

lemma \<phi>Share_1[simp]:
  \<open> (1 \<Znrres> T) = T \<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

lemma \<phi>Share_\<phi>Share[simp]:
  \<open> 0 < n \<and> 0 < m
\<Longrightarrow> n \<Znrres> m \<Znrres> T = n*m \<Znrres> T \<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)
  by (metis share_share_not0)

lemma \<phi>Share_share:
  \<open> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) * (x \<Ztypecolon> m \<Znrres> T) = (x \<Ztypecolon> n+m \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns set_eq_iff; rule; clarsimp)
  using share_sep_left_distrib_0 apply blast
  subgoal for v
  apply (rule exI[where x=\<open>share n v\<close>], rule exI[where x=\<open>share m v\<close>], simp)
    by (metis share_sep_left_distrib_0) .

lemma \<phi>Share_\<phi>MapAt:
  \<open>n \<Znrres> k \<^bold>\<rightarrow> T = k \<^bold>\<rightarrow> n \<Znrres> T\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply blast
  by (metis share_fun_updt share_right_one)

lemma \<phi>Share_\<phi>MapAt_L:
  \<open>n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T = k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule)
  apply (clarsimp simp add: share_push_map) apply blast
  apply (clarsimp simp add: share_push_map[symmetric]) by blast

lemma \<phi>Share_\<phi>Prod:
  \<open>n \<Znrres> (T \<^emph> U) = (n \<Znrres> T) \<^emph> (n \<Znrres> U)\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis share_sep_disj_left share_sep_disj_right share_sep_right_distrib_0)
  using share_sep_right_distrib_0 by blast

lemma \<phi>Share_\<phi>None:
  \<open>0 < n \<Longrightarrow> n \<Znrres> \<circle> = (\<circle> :: ('a::share_one,unit) \<phi>)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

(*
lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> ?n \<Znrres> \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?P @action (?Act::?'b::simplification action)\<close>]:
  \<open>x \<Ztypecolon> n \<Znrres> \<circle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>) @action Act\<close>
  for Act :: \<open>'b::simplification action\<close>
  unfolding Imply_def Action_Tag_def
  by (simp add: \<phi>expns) *)


paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>Share_transformation:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U) \<a>\<n>\<d> P
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> n \<Znrres> U) \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1010]:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U) \<a>\<n>\<d> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n = n'
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> n' \<Znrres> U) \<a>\<n>\<d> P\<close>
  using \<phi>Share_transformation by (simp add: Premise_def)

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> n * m \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n * m \<Znrres> T) \<a>\<n>\<d> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) \<a>\<n>\<d> P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) \<a>\<n>\<d> P\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) \<a>\<n>\<d> P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n \<Znrres> (T \<^emph> U)) \<a>\<n>\<d> P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> (T \<^emph> U)) \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> n \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_mult, 'b) \<phi>\<close>
  unfolding \<r>Clean_def Imply_def apply (simp add: \<phi>expns)
  using share_right_one by blast


paragraph \<open>Action Rules\<close>

lemma [\<phi>reason 1200]:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U) \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> n \<Znrres> U) \<a>\<n>\<d> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U) \<a>\<n>\<d> P @action to Z
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> n \<Znrres> U) \<a>\<n>\<d> P @action to Z\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n' = n
\<Longrightarrow> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U) \<a>\<n>\<d> P @action to Z
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> n \<Znrres> U) \<a>\<n>\<d> P @action to (n' \<Znrres> Z)\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U) \<a>\<n>\<d> P @action as Z
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> n \<Znrres> U) \<a>\<n>\<d> P @action as Z\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n' = n
\<Longrightarrow> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U) \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> n \<Znrres> U) \<a>\<n>\<d> P @action as (z \<Ztypecolon> n' \<Znrres> Z)\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .


paragraph \<open>Simplifications\<close>

lemma [simp]:
  \<open>(n \<Znrres> ExTyp T) = (\<exists>\<phi> c. n \<Znrres> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(n \<Znrres> (T \<phi>\<s>\<u>\<b>\<j> P)) = (n \<Znrres> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)


lemma \<phi>Share_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) = (x' \<Ztypecolon> n \<Znrres> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Share_simp_cong ("x \<Ztypecolon> n \<Znrres> T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>Share_simp_cong} ctxt)
\<close>


subparagraph \<open>Permission\<close>

lemma share_split_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> (x \<Ztypecolon> n+m \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n \<Znrres> T) * (x \<Ztypecolon> m \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share implies_refl Premise_def)

lemma share_merge_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) * (x \<Ztypecolon> m \<Znrres> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> n+m \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share implies_refl Premise_def)


subsubsection \<open>\<phi>-Some\<close>

definition \<phi>Some :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<black_circle> _" [91] 90)
  where \<open>\<phi>Some T = (\<lambda>x. { Some v |v. v \<in> (x \<Ztypecolon> T) })\<close>

abbreviation \<phi>Share_Some ("\<fish_eye> _" [91] 90)
  where \<open>\<phi>Share_Some T \<equiv> \<phi>perm_ins_homo to_share (\<phi>Some T)\<close>

abbreviation \<phi>Share_Some_L ("\<fish_eye>\<^sub>L _" [91] 90)
  where \<open>\<phi>Share_Some_L T \<equiv> [] \<^bold>\<rightarrow> \<phi>perm_ins_homo to_share (\<phi>Some T)\<close>

\<phi>adhoc_overloading \<phi>coercion \<phi>Some \<phi>Share_Some \<phi>Share_Some_L

lemma \<phi>Some_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Some T) \<longleftrightarrow> (\<exists>v. p = Some v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>Some_def by simp

lemma \<phi>Some_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Some T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>Some_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<black_circle> U \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<black_circle> U \<a>\<n>\<d> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<black_circle> U \<a>\<n>\<d> P @action to Z \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<black_circle> U \<a>\<n>\<d> P @action to (\<black_circle> Z) \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<black_circle> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z) \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<black_circle> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> \<black_circle> Z) \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .


lemma [simp]:
  \<open>(\<black_circle> ExTyp T) = (\<exists>\<phi> c. \<black_circle> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<black_circle> (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<black_circle> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>Some_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<black_circle> T) = (x' \<Ztypecolon> \<black_circle> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Some_simp_cong ("x \<Ztypecolon> \<black_circle> T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>Some_simp_cong} ctxt)
\<close>

lemma [\<phi>reason 1200]:
  \<open> v \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> v' \<Ztypecolon> T \<a>\<n>\<d> P
\<Longrightarrow> Some v \<Ztypecolon> Identity \<i>\<m>\<p>\<l>\<i>\<e>\<s> v' \<Ztypecolon> \<black_circle> T \<a>\<n>\<d> P\<close>
  by (clarsimp simp add: \<phi>expns Imply_def)

lemma [\<phi>reason 1200]:
  \<open> is_functional (x \<Ztypecolon> T)
\<Longrightarrow> is_functional (x \<Ztypecolon> \<black_circle> T)\<close>
  by (clarsimp simp add: \<phi>expns is_functional_def)


subsubsection \<open>\<phi>Sep_Disj\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj X Y
\<Longrightarrow> \<phi>Sep_Disj X (m \<Znrres> Y)\<close>
  for X :: \<open>('a::share_sep_disj,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj Y X
\<Longrightarrow> \<phi>Sep_Disj (m \<Znrres> Y) X\<close>
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
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> k1 \<noteq> k2
||| \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>Sep_Disj (k1 \<^bold>\<rightarrow> T) (k2 \<^bold>\<rightarrow> U)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def atomize_Branch
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)+

lemma [\<phi>reason 1200]:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> k1 \<noteq> k2
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


subsubsection \<open>\<phi>Sep_Disj_Identical\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical (n \<Znrres> T)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Identical_\<phi>MapAt[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical (k \<^bold>\<rightarrow> T)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Identical_\<phi>MapAt_L[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical (k \<^bold>\<rightarrow>\<^sub>@ T)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  using push_map_sep_disj by blast

lemma \<phi>Sep_Disj_Identical_Prod[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical U
\<Longrightarrow> \<phi>Sep_Disj_Identical (T \<^emph> U)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis self_disj_I sep_disj_commute sep_disj_multD2 sep_mult_commute)


lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>perm_ins_homo f T)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_ins_homo ((o) f) (k \<^bold>\<rightarrow> T)) \<close>
  by (subst \<phi>perm_ins_homo_MapAt; rule \<phi>Sep_Disj_Identical_\<phi>MapAt)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>perm_ins_homo ((o) f) T)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_ins_homo ((o) f) (k \<^bold>\<rightarrow>\<^sub>@ T)) \<close>
  by (subst \<phi>perm_ins_homo_MapAt_L; rule \<phi>Sep_Disj_Identical_\<phi>MapAt_L)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>perm_ins_homo f T)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_ins_homo f U)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_ins_homo f (T \<^emph> U)) \<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (smt (verit) Imply_def \<phi>Sep_Disj_Identical_Prod \<phi>Sep_Disj_Identical_def \<phi>perm_ins_homo_Prod_imply)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Identical (\<phi>perm_ins_homo to_share (\<phi>Some T))\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Identical (\<phi>perm_ins_homo to_share \<phi>None)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>None :: ('a::share_module_sep,unit) \<phi>) \<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (clarsimp simp add: \<phi>expns)


subsection \<open>Agreement\<close>

definition Agreement :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T agree option, 'x) \<phi>\<close>
  where \<open>Agreement T x = { Some (agree v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma Agreement_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Agreement T) \<longleftrightarrow> (\<exists>v. p = Some (agree v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Agreement_def by simp

lemma Agreement_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Agreement T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

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
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> Agreement T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Agreement U \<a>\<n>\<d> P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns)

lemma Agreement_dup[
  \<phi>reason 1200 for \<open>?x \<Ztypecolon> Agreement ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?U \<a>\<n>\<d> ?P @action action_dup\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>?x \<Ztypecolon> Agreement ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> (?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<a>\<n>\<d> ?P\<close>
]:
  \<open> x \<Ztypecolon> Agreement T \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) @action action_dup\<close>
  unfolding Imply_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for v by (rule exI[where x=\<open>Some (agree v)\<close>]; rule exI[where x=\<open>Some (agree v)\<close>]; simp) .

lemma Agreement_shrink[
  \<phi>reason 1200 for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?U \<a>\<n>\<d> ?P @action action_shrink\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?x \<Ztypecolon> Agreement ?T \<a>\<n>\<d> ?P\<close>
]:
  \<open> (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> Agreement T @action action_shrink \<close>
  unfolding Imply_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)


lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> Agreement T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Agreement U \<a>\<n>\<d> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Agreement U \<a>\<n>\<d> P @action to Z\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Agreement U \<a>\<n>\<d> P @action to (Agreement Z)\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Agreement U \<a>\<n>\<d> P @action as Z\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Agreement T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Agreement U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Agreement Z)\<close>
  unfolding Action_Tag_def using Agreement_cast .


subsection \<open>Nosep\<close>

definition Nosep :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T nosep, 'x) \<phi>\<close>
  where \<open>Nosep T x = nosep ` (x \<Ztypecolon> T)\<close>

\<phi>adhoc_overloading \<phi>coercion \<open>\<lambda>T. \<black_circle> Nosep T\<close> \<open>\<lambda>T. \<fish_eye> Nosep T\<close> \<open>\<lambda>T. \<fish_eye>\<^sub>L Nosep T\<close>

(*TODO: give a configure flag to control this sugar*)
translations
  "\<coercion> T" <= "\<fish_eye> CONST Nosep T"

lemma Nosep_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Nosep T) \<longleftrightarrow> (\<exists>v. p = nosep v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Nosep_def by blast

lemma Nosep_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Nosep T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>Nosep (T \<phi>\<s>\<u>\<b>\<j> P) = (Nosep T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>Nosep (ExTyp T) = (\<exists>\<phi>c. Nosep (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)


paragraph \<open>Rule\<close>

lemma Nosep_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> Nosep T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Nosep U \<a>\<n>\<d> P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> Nosep T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Nosep U \<a>\<n>\<d> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Nosep U \<a>\<n>\<d> P @action to Z\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Nosep U \<a>\<n>\<d> P @action to (Nosep Z)\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Nosep U \<a>\<n>\<d> P @action as Z\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Nosep T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Nosep U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Nosep Z)\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Nosep _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<Ztypecolon> Identity \<a>\<n>\<d> _\<close>]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Identity \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> Nosep T \<i>\<m>\<p>\<l>\<i>\<e>\<s> nosep y \<Ztypecolon> Identity \<a>\<n>\<d> P \<close>
  unfolding Imply_def 
  by (clarsimp simp add: Nosep_expns Identity_expn)


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

lemma \<phi>MayInit_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>MayInit TY T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

paragraph \<open>Conversions\<close>

lemma [simp]:
  \<open>\<phi>MayInit TY (T \<phi>\<s>\<u>\<b>\<j> P) = (\<phi>MayInit TY T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>\<phi>MayInit TY (ExTyp T) = (\<exists>\<phi> c. \<phi>MayInit TY (T c))\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

paragraph \<open>Rules\<close>

(*TODO: improve this*)
lemma \<phi>MayInit_cast[\<phi>reason for \<open>?x \<Ztypecolon> \<phi>MayInit ?TY ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> \<phi>MayInit ?TY' ?U \<a>\<n>\<d> ?P\<close>]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<a>\<n>\<d> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>MayInit_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<a>\<n>\<d> P @action to Z\<close>
  unfolding Action_Tag_def using \<phi>MayInit_cast .


definition \<phi>Uninit :: \<open>('v uninit, unit) \<phi>\<close>
  where \<open>\<phi>Uninit x = {uninitialized}\<close>

lemma \<phi>Uninit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Uninit) \<longleftrightarrow> p = uninitialized\<close>
  unfolding \<phi>Type_def \<phi>Uninit_def by simp

lemma \<phi>Uninit_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Uninit) \<Longrightarrow> C \<Longrightarrow> C\<close> .


section \<open>Misc.\<close>

subsection \<open>Forward Simulation\<close>

definition \<phi>F_simulation
    :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> (('av \<times> 'bv) set, ('a \<times> 'b) set) \<phi>\<close> (infixr "\<Rrightarrow>\<^sub>r" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow>\<^sub>r U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>u y. (v,u) \<in> g \<and> (x,y) \<in> f \<and> u \<in> (y \<Ztypecolon> U)) })\<close>

end
