chapter \<open>Pre-built \<phi>-Types\<close>

theory Phi_Types
  imports Phi_Type_Algebra
begin

section \<open>Preliminary\<close>

consts \<phi>coercion :: \<open>('c1,'a) \<phi> \<Rightarrow> ('c2,'a) \<phi>\<close> ("\<coercion> _" [61] 60)
  \<comment> \<open>merely a syntax sugar to be overloaded.\<close>

(*reconsider this! may depreciate it!*)
text \<open>A semantic type is not always required to be annotated if it is known syntactically.
  We use syntax translation to achieve a sugar to do this.

This is a planning feature has not been implemented\<close>

syntax TY_of_\<phi> :: \<open>('a,'b) \<phi> \<Rightarrow> TY\<close> ("TY'_of'_\<phi>")

ML \<open>Phi_Conv.set_rules__type_form_to_ex_quantified [] ;
    Phi_Conv.set_rules__type_form_to_ex_quantified_single_var [] \<close>

section \<open>Basics\<close>

subsection \<open>Itself\<close> \<comment> \<open>together with the vertical composition forms the only primitives in the algbera of \<phi>-Types\<close>

lemma Itself_is_primitive: \<open>x \<Ztypecolon> Itself \<equiv> x \<Ztypecolon> Itself\<close> .

declare [[\<phi>trace_reasoning = 1]]

ML \<open>(Thm.transfer \<^theory> @{thm' Itself_is_primitive})\<close>

setup \<open>Context.theory_map (
  Phi_Type_Algebra.add_type {no_auto=true}
        (\<^binding>\<open>Itself\<close>, \<^pattern>\<open>Itself\<close>, Phi_Type_Algebra.DIRECT_DEF (Thm.transfer \<^theory> @{thm' Itself_is_primitive}),
         \<^here>, Phi_Type_Algebra.Derivings.empty, [])
   #> snd )\<close>

text \<open>No deriver is available on \<open>Itself\<close>, and they will trap in infinite loops because the fake
  definition \<open>Itself_is_primitive\<close> given to the deriving engine is infinitely recursive.\<close>


subsection \<open>Embedding of Empty\<close>

lemma \<phi>None_def': \<open> (x \<Ztypecolon> \<circle>) = (1 \<Ztypecolon> Itself) \<close>
  by (simp add: BI_eq_iff)

setup \<open>Context.theory_map (
  Phi_Type_Algebra.add_type {no_auto=false}
      (\<^binding>\<open>\<phi>None\<close>, \<^pattern>\<open>\<phi>None\<close>, Phi_Type_Algebra.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>None_def'}),
       \<^here>, Phi_Type_Algebra.Derivings.empty, [])
   #> snd )\<close>

declare [[\<phi>trace_reasoning = 3]]
  
let_\<phi>type \<phi>None
  deriving Basic
       and Functionality
       and Identity_Elements
       and Abstraction_to_Raw

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>None.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L \<circle> (\<lambda>x. True) \<close>),
  (@{thm' \<phi>None.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain \<circle> (\<lambda>x. True) \<close>),
  (@{thm' \<phi>None.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set (\<circle> :: ('c::sep_carrier_1, unit) \<phi>) (\<lambda>x. True) \<close>),
  (@{thm' \<phi>None.Functionality}, \<^pattern_prop>\<open> Functionality \<circle> (\<lambda>x. True) \<close>),
  (@{thm' \<phi>None.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I \<circle> (\<lambda>x. True) (\<lambda>a. True)\<close>),
  (@{thm' \<phi>None.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E \<circle> (\<lambda>x. True)\<close>),
  (@{thm' \<phi>None.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv \<circle> (\<lambda>_ _. True) \<close>),
  (@{thm' \<phi>None.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> 1 \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?xa \<Ztypecolon> \<circle>  \<close>),
  (@{thm' \<phi>None.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> ?x \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c::one,?'c) \<phi>) \<s>\<u>\<b>\<j> y. y = 1 @action to (Itself::(?'c,?'c) \<phi>) \<close>)
]\<close>


subsection \<open>Embedding of \<open>\<top>\<close>\<close>

setup \<open>Context.theory_map (
  Phi_Type_Algebra.add_type {no_auto=false}
      (\<^binding>\<open>\<phi>Any\<close>, \<^pattern>\<open>\<phi>Any::(?'c, ?'x) \<phi>\<close>, Phi_Type_Algebra.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>Any_def}),
       \<^here>, Phi_Type_Algebra.Derivings.empty, [])
   #> snd )\<close>

declare [[\<phi>trace_reasoning = 0]]

let_\<phi>type \<phi>Any deriving Basic

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Any.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L \<top>\<^sub>\<phi> (\<lambda>x. True) \<close>),
  (@{thm' \<phi>Any.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain \<top>\<^sub>\<phi> (\<lambda>x. True) \<close>),
  (@{thm' \<phi>Any.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv \<top>\<^sub>\<phi> (\<lambda>_ _. True) \<close>)
]\<close>

subsection \<open>Embedding of \<open>\<bottom>\<close>\<close>

declare \<phi>Bot_def[embed_into_\<phi>type]

thm \<phi>Bot_def

setup \<open>Context.theory_map (
  Phi_Type_Algebra.add_type {no_auto=false}
        (\<^binding>\<open>\<phi>Bot\<close>, \<^pattern>\<open>\<phi>Bot::(?'c,?'a) \<phi>\<close>, Phi_Type_Algebra.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>Bot_def}),
         \<^here>, Phi_Type_Algebra.Derivings.empty, [])
   #> snd )\<close>

let_\<phi>type \<phi>Bot
  deriving Basic
       and \<open>Abstract_Domain \<bottom>\<^sub>\<phi> (\<lambda>x. False)\<close>
       and \<open>Abstract_Domain\<^sub>L \<bottom>\<^sub>\<phi> (\<lambda>x. False)\<close>
       and Functionality
       and Carrier_Set

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Bot.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L \<bottom>\<^sub>\<phi> (\<lambda>x. False) \<close>),
  (@{thm' \<phi>Bot.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain \<bottom>\<^sub>\<phi> (\<lambda>x. False) \<close>),
  (@{thm' \<phi>Bot.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv \<bottom>\<^sub>\<phi> (\<lambda>_ _. True) \<close>),
  (@{thm' \<phi>Bot.Functionality}, \<^pattern_prop>\<open> Functionality \<bottom>\<^sub>\<phi> (\<lambda>x. True) \<close>),
  (@{thm' \<phi>Bot.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set \<bottom>\<^sub>\<phi> (\<lambda>x. True)  \<close>)
]\<close>

(*TODO: bi-functors of \<phi>Prod?*)

subsection \<open>\<phi>Prod\<close>

setup \<open>Context.theory_map (
  Phi_Type_Algebra.add_type {no_auto=false}
        (\<^binding>\<open>\<phi>Prod\<close>, \<^pattern>\<open>\<phi>Prod::(?'c::sep_magma,?'a\<^sub>1) \<phi> \<Rightarrow> (?'c,?'a\<^sub>2) \<phi> \<Rightarrow> (?'c,?'a\<^sub>1 \<times> ?'a\<^sub>2) \<phi>\<close>,
         Phi_Type_Algebra.DIRECT_DEF (Thm.transfer \<^theory>
            @{lemma' \<open>(x \<Ztypecolon> T \<^emph> U) = (snd x \<Ztypecolon> U) * (fst x \<Ztypecolon> T)\<close>
                      for T :: \<open>('c::sep_magma,'a\<^sub>1) \<phi>\<close> and U :: \<open>('c::sep_magma,'a\<^sub>2) \<phi>\<close>
                  by (simp add: \<phi>Prod_expn'')}),
         \<^here>, Phi_Type_Algebra.Derivings.empty, [])
   #> snd )\<close>

text \<open>We still derive properties of \<open>\<phi>Prod\<close> for consistency of the internal reasoning system,
      even though most of the derived rules are already covered by existing rules.\<close>
  
let_\<phi>type \<phi>Prod
  deriving Basic
       and Functional_Transformation_Functor
       and Functionality
       (* and Separation_Homo, bi commutativity is not supported yet *)

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Prod.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain ?U ?Pa \<Longrightarrow> Abstract_Domain (?T \<^emph> ?U) (\<lambda>x. ?Pa (snd x) \<and> ?P (fst x)) \<close>),
  (@{thm' \<phi>Prod.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?er \<Longrightarrow> Object_Equiv ?U ?eq \<Longrightarrow> Object_Equiv (?T \<^emph> ?U) (\<lambda>x y. ?eq (snd x) (snd y) \<and> ?er (fst x) (fst y)) \<close>),
  (@{thm' \<phi>Prod.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality ?U ?Pa \<Longrightarrow> Functionality (?T \<^emph> ?U) (\<lambda>x. ?P (fst x) \<and> ?Pa (snd x)) \<close>),
  (@{thm' \<phi>Prod.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set ?U ?Pa \<Longrightarrow> Carrier_Set (?T \<^emph> ?U) (\<lambda>x. ?P (fst x) \<and> ?Pa (snd x)) \<close>),
  (@{thm' \<phi>Prod.Transformation_Functor}, \<^pattern_prop>\<open> Transformation_BiFunctor (\<^emph>) (\<^emph>) ?T ?U ?Ta ?Ua Basic_BNFs.fsts Basic_BNFs.snds (\<lambda>x. UNIV) (\<lambda>x. UNIV) rel_prod  \<close>),
  (@{thm' \<phi>Prod.Functional_Transformation_Functor}, \<^pattern_prop>\<open>
      Functional_Transformation_BiFunctor (\<^emph>) (\<^emph>) ?T ?U ?Ta ?Ua Basic_BNFs.fsts Basic_BNFs.snds (\<lambda>x. UNIV) (\<lambda>x. UNIV)
                                          (\<lambda>f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x. P\<^sub>1 (fst x) \<and> P\<^sub>2 (snd x)) (\<lambda>f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2. map_prod f\<^sub>1 f\<^sub>2) \<close>)
]\<close>



subsection \<open>Func\<close>

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def \<phi>Fun :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('c,'a) \<phi>\<close>
  where \<open>\<phi>Fun f x = (f x \<Ztypecolon> Itself)\<close>
  deriving \<open>Identity_Elements\<^sub>E (\<phi>Fun f) (\<lambda>x. f x = 1)\<close>
       and \<open>Identity_Elements\<^sub>I (\<phi>Fun f) (\<lambda>x. f x = 1) (\<lambda>_. True)\<close>
       and Basic
       and Functionality
       and Abstraction_to_Raw


(*The assertions are used to test the property derivers. As the deriviers are changed frequently
  during the development, the assertions check and report if any mistakes are introduced by comparing
  the derived properties with their expected forms.*)
ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Fun.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L (\<phi>Fun ?f) (\<lambda>x. True) \<close>),
  (@{thm' \<phi>Fun.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain (\<phi>Fun ?f) (\<lambda>x. True) \<close>),
  (@{thm' \<phi>Fun.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set (\<phi>Fun ?f) (\<lambda>x. mul_carrier (?f x)) \<close>),
  (@{thm' \<phi>Fun.Functionality}, \<^pattern_prop>\<open> Functionality (\<phi>Fun ?f) (\<lambda>x. True)  \<close>),
  (@{thm' \<phi>Fun.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I (\<phi>Fun ?f) (\<lambda>x. ?f x = 1) (\<lambda>_. True)  \<close>),
  (@{thm' \<phi>Fun.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E (\<phi>Fun ?f) (\<lambda>x. ?f x = 1)  \<close>),
  (@{thm' \<phi>Fun.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv (\<phi>Fun ?f) (\<lambda>x y. ?f x = ?f y)  \<close>),
  (@{thm' \<phi>Fun.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> ?f ?xa \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?xa \<Ztypecolon> \<phi>Fun ?f \<close>),
  (@{thm' \<phi>Fun.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> ?x \<Ztypecolon> \<phi>Fun ?f \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself :: (?'c,?'c) \<phi>) \<s>\<u>\<b>\<j> y. y = ?f ?x @action to (Itself :: (?'c,?'c) \<phi>) \<close>)
]\<close>


subsubsection \<open>Algebraic Properties\<close>

lemma [\<phi>reason add]:
  \<open> closed_homo_sep f
\<Longrightarrow> Object_Sep_Homo\<^sub>I (\<phi>Fun f) UNIV \<close>
  unfolding Object_Sep_Homo\<^sub>I_def Transformation_def
  by (clarsimp simp add: set_mult_expn closed_homo_sep_disj.sep_disj_homo
                         homo_sep_mult.homo_mult closed_homo_sep_def homo_sep_def)

lemma [\<phi>reason add]:
  \<open> homo_sep f
\<Longrightarrow> Object_Sep_Homo\<^sub>E (\<phi>Fun f)\<close>
  unfolding Object_Sep_Homo\<^sub>E_def Transformation_def
  by (clarsimp simp add: set_mult_expn homo_sep_disj_def
                         homo_sep_mult.homo_mult homo_sep_def)


subsection \<open>Embedding of Subjection\<close>

declare [[\<phi>trace_reasoning = 0 ]]

\<phi>type_def SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<s>\<u>\<b>\<j>" 25)
  where [embed_into_\<phi>type]: \<open> (T \<phi>\<s>\<u>\<b>\<j> P) = (\<lambda>x. x \<Ztypecolon> T \<s>\<u>\<b>\<j> P) \<close>
  deriving Sep_Functor_1
       and Functionality
       and Carrier_Set
     (*and \<open>(\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<Longrightarrow> Identity_Elements\<^sub>I T D P) \<Longrightarrow> Identity_Elements\<^sub>I (T \<phi>\<s>\<u>\<b>\<j> Q) (\<lambda>x. Q \<longrightarrow> D x) (\<lambda>x. Q \<and> P x)\<close>*)
     (*and \<open>Identity_Elements\<^sub>E T D \<Longrightarrow> Identity_Elements\<^sub>E (T \<phi>\<s>\<u>\<b>\<j> P) (\<lambda>x. P \<and> D x) \<close>*)
       and Abstraction_to_Raw

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' SubjectionTY.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P \<Longrightarrow> Abstract_Domain\<^sub>L ?T ?Pa) \<Longrightarrow> Abstract_Domain\<^sub>L (?T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>x. ?P \<and> ?Pa x) \<close>),
  (@{thm' SubjectionTY.Abstract_Domain}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P \<Longrightarrow> Abstract_Domain ?T ?Pa) \<Longrightarrow> Abstract_Domain (?T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>x. ?P \<and> ?Pa x) \<close>),
  (@{thm' SubjectionTY.Carrier_Set}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P \<Longrightarrow> Carrier_Set ?T ?Pa) \<Longrightarrow> Carrier_Set (?T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>x. ?P \<longrightarrow> ?Pa x) \<close>),
  (@{thm' SubjectionTY.Functionality}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P \<Longrightarrow> Functionality ?T ?Pa) \<Longrightarrow> Functionality (?T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>x. ?P \<longrightarrow> ?Pa x) \<close>),
  (@{thm' SubjectionTY.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P \<Longrightarrow> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P) \<Longrightarrow> Identity_Elements\<^sub>I (?T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>x. ?P \<longrightarrow> ?T\<^sub>D x) (\<lambda>x. ?P \<and> ?T\<^sub>P x) \<close>),
  (@{thm' SubjectionTY.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (?T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>x. ?P \<and> ?T\<^sub>D x) \<close>),
  (@{thm' SubjectionTY.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?er \<Longrightarrow> Object_Equiv (?T \<phi>\<s>\<u>\<b>\<j> ?P) ?er \<close>),
  (@{thm' SubjectionTY.Transformation_Functor}, \<^pattern_prop>\<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P = ?Pa \<Longrightarrow> Transformation_Functor (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?Pa) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>a. a) \<close>),
  (@{thm' SubjectionTY.Functional_Transformation_Functor}, \<^pattern_prop>\<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P = ?Pa \<Longrightarrow> Functional_Transformation_Functor (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?Pa) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>f a. a) (\<lambda>f P. f) \<close>),
  (@{thm' SubjectionTY.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) ?Ta ?U UNIV (\<lambda>x. x)  \<close>),
  (@{thm' SubjectionTY.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> ?P) ?Ta ?U (\<lambda>x. x) \<close>)
]\<close>

translations "TY_of_\<phi> (T \<phi>\<s>\<u>\<b>\<j> P)" \<rightharpoonup> "TY_of_\<phi> T"

subsubsection \<open>Rules\<close>

paragraph \<open>Simplification Rules\<close>

declare SubjectionTY.unfold [\<phi>programming_simps, assertion_simps]

lemma \<phi>\<s>\<u>\<b>\<j>_\<phi>\<s>\<u>\<b>\<j>[embed_into_\<phi>type, simp]:
  \<open>(T \<phi>\<s>\<u>\<b>\<j> P \<phi>\<s>\<u>\<b>\<j> Q) = (T \<phi>\<s>\<u>\<b>\<j> P \<and> Q)\<close>
  by (rule \<phi>Type_eqI; clarsimp)


subsubsection \<open>Transformation Setup\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> P) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by clarsimp

lemma [\<phi>reason %ToA_red]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> P) \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by (cases x; cases C; clarsimp; blast)

lemma [\<phi>reason %ToA_red]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by clarsimp

lemma [\<phi>reason %ToA_red]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph>[C] U) \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> P) \<^emph>[C] U \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by clarsimp

subsubsection \<open>Algebraic Properties\<close>

text \<open>Here we construct two inner transformations from \<open>a \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P\<close> to \<open>a \<Ztypecolon> T\<close> and another reversely.
  It is essentially an identity transformation from \<open>a\<close> to \<open>a\<close> itself.
  The constraints checks 1. if the identity transformation is supported (a very weak requirement),
        2. the container is always non-empty so that an independent assertion \<open>P\<close> bound at the element
           type is valid globally (this is a necessary condition).  \<close>

lemma \<phi>\<s>\<u>\<b>\<j>_Homo[\<phi>reason_template name Fa.\<phi>subj [assertion_simps]]:
  \<open> Functional_Transformation_Functor Fa Fa (T \<phi>\<s>\<u>\<b>\<j> P) T D R pm fm
\<Longrightarrow> Functional_Transformation_Functor Fa Fa T (T \<phi>\<s>\<u>\<b>\<j> P) D R pm fm
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a. a \<in> D x \<longrightarrow> a \<in> R x) \<and> (fm (\<lambda>x. x) (\<lambda>_. P) x = x \<and> pm (\<lambda>x. x) (\<lambda>_. P) x = P)
\<Longrightarrow> (x \<Ztypecolon> Fa (T \<phi>\<s>\<u>\<b>\<j> P)) = (x \<Ztypecolon> Fa T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Functional_Transformation_Functor_def Transformation_def atomize_eq Premise_def BI_eq_iff
  apply (clarsimp; rule)
  subgoal premises prems for p
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp)
  subgoal premises prems for p
    by (insert prems(2)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp) .


lemma \<phi>\<s>\<u>\<b>\<j>_Homo_ty[\<phi>reason_template name Fa.\<phi>subj_ty [assertion_simps]]:
  \<open> Functional_Transformation_Functor Fa Fa (T \<phi>\<s>\<u>\<b>\<j> P) T D R pm fm
\<Longrightarrow> Functional_Transformation_Functor Fa Fa T (T \<phi>\<s>\<u>\<b>\<j> P) D R pm fm
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a x. a \<in> D x \<longrightarrow> a \<in> R x) \<and> (\<forall>x. fm (\<lambda>x. x) (\<lambda>_. P) x = x \<and> pm (\<lambda>x. x) (\<lambda>_. P) x = P)
\<Longrightarrow> Fa (T \<phi>\<s>\<u>\<b>\<j> P) = (Fa T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Functional_Transformation_Functor_def atomize_eq Premise_def BI_eq_iff
  apply (rule \<phi>Type_eqI_Tr; clarsimp simp add: Transformation_def)
  subgoal premises prems for x v
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp,
        blast)
  subgoal premises prems for x v
    by (insert prems(2)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp) .

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x \<and> P @action \<A>_transitive_simp\<close>
  unfolding Transformation_Functor_def Transformation_def Action_Tag_def
  by simp

subsubsection \<open>Guessing Antecedents\<close>

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Property PC False T' (\<lambda>x. f x \<Ztypecolon> T x) a p c
\<Longrightarrow> Guess_Property PC False T' (\<lambda>x. f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x) a p (\<lambda>x. P x \<and> c x)\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Property PC True T' (\<lambda>x. f x \<Ztypecolon> T x) a p c
\<Longrightarrow> Guess_Property PC True T' (\<lambda>x. f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x) a (\<lambda>x. P x \<and> p x) c\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x) U Ds Dx zi ants conds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x \<phi>\<s>\<u>\<b>\<j> P s x) U
                            Ds (\<lambda>s t (x,y). P s x \<and> P t y \<longrightarrow> Dx s t (x,y)) zi ants conds \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x) U Ds Dx zi ants conds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x \<phi>\<s>\<u>\<b>\<j> P s x) U
                              Ds (\<lambda>s t xy. P (s + t) xy \<longrightarrow> Dx s t xy) zi ants conds \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

paragraph \<open>Commutativity between Tyoprs\<close>

subparagraph \<open>\<open>Guess_Tyops_Commute\<^sub>I\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P) G_def' uF uF' T
                        (\<lambda>x. P \<longrightarrow> D x) r ants ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P) \<and>\<^sub>\<r> conds) \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P x) G_def' uF uF' T
                        (\<lambda>x. P x \<longrightarrow> D x) r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P' T x) uF uF' T D r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P') uF uF' T D r ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P') \<and>\<^sub>\<r> ants) conds \<close>
  unfolding Guess_Tyops_Commute_def ..

subparagraph \<open>\<open>Guess_Tyops_Commute\<^sub>E\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P) G_def' T
                        (\<lambda>x. P \<longrightarrow> D x) r ants ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P) \<and>\<^sub>\<r> conds) \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P x) G_def' T D r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P' T x) T D r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P') T D r ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P') \<and>\<^sub>\<r> ants) conds \<close>
  unfolding Guess_Tyops_Commute_def ..

subsection \<open>Dependent Sum Type\<close>

declare [[\<phi>trace_reasoning = 3]]
   
\<phi>type_def \<phi>Dependent_Sum :: \<open>('c \<Rightarrow> ('a,'b) \<phi>) \<Rightarrow> ('a, 'c \<times> 'b) \<phi>\<close> ("\<Sigma>")
  where \<open>cx \<Ztypecolon> \<Sigma> T \<equiv> (snd cx) \<Ztypecolon> T (fst cx)\<close>
  deriving Basic
    and \<open> (\<And>A. Object_Equiv (T A) (eq A))
      \<Longrightarrow> Object_Equiv (\<Sigma> T) (\<lambda>x y. fst y = fst x \<and> eq (fst x) (snd x) (snd y))\<close>
    and \<open>(\<And>A. Abstract_Domain (T A) (P A)) \<Longrightarrow> Abstract_Domain (\<Sigma> T) (\<lambda>x. P (fst x) (snd x))\<close>
    and \<open>(\<And>A. Abstract_Domain\<^sub>L (T A) (P A)) \<Longrightarrow> Abstract_Domain\<^sub>L (\<Sigma> T) (\<lambda>x. P (fst x) (snd x))\<close>
    and Identity_Elements
    and Functionality
    and Carrier_Set
    and Abstraction_to_Raw
    and \<open>(\<And>a c. a \<Ztypecolon> T c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Itself \<s>\<u>\<b>\<j> b. r a b c @action to Itself)
      \<Longrightarrow> \<forall>(x::?'b \<times> ?'a). x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>b. r (snd x) b (fst x) \<and> y = b) @action to Itself \<close>
    and \<open>(\<And>A. c A \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y A \<Ztypecolon> T A)
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (y a = x)
      \<Longrightarrow> c a \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (a,x) \<Ztypecolon> \<Sigma> T \<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Dependent_Sum.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> (\<And>A. Abstract_Domain\<^sub>L (?T A) (?P A)) \<Longrightarrow> Abstract_Domain\<^sub>L (\<Sigma> ?T) (\<lambda>x. ?P (fst x) (snd x)) \<close>),
  (@{thm' \<phi>Dependent_Sum.Abstract_Domain}, \<^pattern_prop>\<open> (\<And>A. Abstract_Domain (?T A) (?P A)) \<Longrightarrow> Abstract_Domain (\<Sigma> ?T) (\<lambda>x. ?P (fst x) (snd x)) \<close>),
  (@{thm' \<phi>Dependent_Sum.Carrier_Set}, \<^pattern_prop>\<open> (\<And>A. Carrier_Set (?T A) ?P) \<Longrightarrow> Carrier_Set (\<Sigma> ?T) (\<lambda>x. ?P (snd x))  \<close>),
  (@{thm' \<phi>Dependent_Sum.Functionality}, \<^pattern_prop>\<open> (\<And>A. Functionality (?T A) ?P) \<Longrightarrow> Functionality (\<Sigma> ?T) (\<lambda>x. ?P (snd x))  \<close>),
  (@{thm' \<phi>Dependent_Sum.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> (\<And>A. Identity_Elements\<^sub>I (?T A) (?T\<^sub>D A) (?T\<^sub>P A)) \<Longrightarrow> Identity_Elements\<^sub>I (\<Sigma> ?T) (\<lambda>x. ?T\<^sub>D (fst x) (snd x)) (\<lambda>x. ?T\<^sub>P (fst x) (snd x)) \<close>),
  (@{thm' \<phi>Dependent_Sum.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> (\<And>A. Identity_Elements\<^sub>E (?T A) (?T\<^sub>D A)) \<Longrightarrow> Identity_Elements\<^sub>E (\<Sigma> ?T) (\<lambda>x. ?T\<^sub>D (fst x) (snd x)) \<close>),
  (@{thm' \<phi>Dependent_Sum.Object_Equiv}, \<^pattern_prop>\<open> (\<And>A. Object_Equiv (?T A) (?eq A)) \<Longrightarrow> Object_Equiv (\<Sigma> ?T) (\<lambda>x y. fst y = fst x \<and> ?eq (fst x) (snd x) (snd y)) \<close>),
  (@{thm' \<phi>Dependent_Sum.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> (\<And>A. ?c A \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y A \<Ztypecolon> ?T A) \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> ?y ?a = ?x \<Longrightarrow> ?c ?a \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (?a, ?x) \<Ztypecolon> \<Sigma> ?T   \<close>),
  (@{thm' \<phi>Dependent_Sum.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> (\<And>a c. a \<Ztypecolon> ?T c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> (Itself::(?'c,?'c) \<phi>) \<s>\<u>\<b>\<j> b. ?r a b c @action to (Itself::(?'c,?'c) \<phi>)) \<Longrightarrow>
                                                                  ?x \<Ztypecolon> \<Sigma> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c,?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>b. ?r (snd ?x) b (fst ?x) \<and> y = b) @action to (Itself::(?'c,?'c) \<phi>) \<close>)
]\<close>

notation \<phi>Dependent_Sum (binder "\<Sigma> " 22)

text \<open>Though \<^term>\<open>\<Sigma> T\<close> is not a transformation functor not a separation homomoprhism
  as the element \<phi>-type \<open>T\<close> is parameterized,
  there can be properties very akin to them, see the section \<open>Pseudo properties of \<Sigma>\<close> below.\<close>


subsubsection \<open>Rewrites\<close>

declare \<phi>Dependent_Sum.unfold [embed_into_\<phi>type, \<phi>programming_base_simps, assertion_simps, simp]

lemma \<phi>\<s>\<u>\<b>\<j>_over_\<Sigma>[\<phi>programming_simps]:
  \<open>\<Sigma> x. (T x \<phi>\<s>\<u>\<b>\<j> P) \<equiv> (\<Sigma> T) \<phi>\<s>\<u>\<b>\<j> P\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI, simp)

subsubsection \<open>ToA Reasoning\<close>

declare \<phi>Dependent_Sum.intro_reasoning(1)
        [where x=\<open>(a,b)\<close> for a b, simplified apfst_conv apsnd_conv fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.intro_reasoning(2)
        [where x=\<open>(a,b)\<close> for a b, simplified apfst_conv apsnd_conv fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((_, _), _) \<Ztypecolon> \<Sigma> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.intro_reasoning\<^sub>R
        [where x=\<open>(a,b)\<close> for a b, simplified fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> ]

        \<phi>Dependent_Sum.elim_reasoning[\<phi>reason 1000]
        \<phi>Dependent_Sum.elim_reasoning(1)
        [where x=\<open>(a,b)\<close> for a b, simplified fst_conv snd_conv,
         \<phi>reason 1010 for \<open>(_, _) \<Ztypecolon> \<Sigma> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.elim_reasoning(2)
        [where x=\<open>((a,b),w)\<close> for a b w, simplified apfst_conv fst_conv snd_conv,
         \<phi>reason 1010 for \<open>((_,_),_) \<Ztypecolon> \<Sigma> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]

subsubsection \<open>Quasi Functor Properties\<close>

text \<open>Any non-constantly parameterized \<phi>-types are represented by \<open>\<Sigma>\<close>. Therefore,
  \<open>\<Sigma>\<close> is the only parameterized \<phi>-type for which we need to configure its reasoning rules manually.\<close>

text \<open>The following properties are nice but essentially useless for reasoning as we have registered
  the intro- and elim-rules for \<open>\<Sigma>\<close> destructing any \<open>\<Sigma>\<close> occurring in the reasoning.
  So, the properties below are just listed for aesthetics of math.
\<close>

lemma \<Sigma>_pseudo_Transformation_Functor:
  \<open> (\<And>a c. a \<Ztypecolon> T c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U c' \<s>\<u>\<b>\<j> b c'. g (c,a) (c',b))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> U \<s>\<u>\<b>\<j> y. g x y \<close>
  unfolding Transformation_def
  by (cases x; clarsimp; blast)

lemma \<Sigma>_pseudo_Separation_Homo\<^sub>I:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst (fst x) = fst (snd x)
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<^emph> \<Sigma> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst (fst x), (snd (fst x), snd (snd x))) \<Ztypecolon> \<Sigma> c. (T c \<^emph> U c) \<close>
  unfolding Transformation_def Premise_def
  by clarsimp

lemma \<Sigma>_pseudo_Separation_Homo\<^sub>E:
  \<open> x \<Ztypecolon> \<Sigma> c. (T c \<^emph> U c) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst x, fst (snd x)), (fst x, snd (snd x))) \<Ztypecolon> \<Sigma> T \<^emph> \<Sigma> U \<close>
  unfolding Transformation_def Premise_def
  by clarsimp

lemma \<Sigma>_fundef_cong[fundef_cong]:
  \<comment> \<open>The rule fails to be derived due to the absence of the standard
      Transformation Functor property\<close>
  \<open> x = y
\<Longrightarrow> (F (fst y) (snd y) = G (fst y) (snd y))
\<Longrightarrow> \<Sigma> F x = \<Sigma> G y \<close>
  unfolding \<phi>Dependent_Sum_def \<phi>Type_def
  by simp

(*TODO: reasoning rules based on the above pseudo properties*)


subsubsection \<open>\<Sigma>-Homomorphism (Commutativity over \<Sigma>)\<close>


lemma [\<phi>reason_template name F.\<Sigma>\<^sub>I[]]:
  \<open> Functional_Transformation_Functor F F' (T (fst x)) (\<Sigma> T) D R pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D (snd x) \<longrightarrow> (fst x, a) \<in> R (snd x))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> c. F (T c) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fm (\<lambda>a. (fst x, a)) (\<lambda>_. True) (snd x) \<Ztypecolon> F' (\<Sigma> T)\<close>
  unfolding Functional_Transformation_Functor_def Premise_def
  apply clarsimp
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=\<open>snd x\<close>], THEN spec[where x=\<open>\<lambda>a. (fst x, a)\<close>],
                        THEN spec[where x=\<open>\<lambda>_. True\<close>], simplified]
               prems(2-),
        clarsimp simp add: transformation_weaken) .

lemma [\<phi>reason_template name F.\<Sigma>\<^sub>E[]]:
  \<open> (\<And>c. Functional_Transformation_Functor F F' (\<Sigma> T) (T c) D (R c) (pm c) (fm c))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. fst a = c \<and> snd a \<in> R c x )
\<Longrightarrow> x \<Ztypecolon> F (\<Sigma> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fm c snd (\<lambda>_. True) x \<Ztypecolon> F' (T c) \<w>\<i>\<t>\<h> pm c snd (\<lambda>_. True) x \<close>
  unfolding Premise_def Functional_Transformation_Functor_def
  by clarsimp force

lemma [\<phi>reason_template name F.\<Sigma>_rewr[]]:
  \<open> (\<And>c. Functional_Transformation_Functor F F' (\<Sigma> T) (T c) D (R c) (pm c) (fm c))
\<Longrightarrow> Functional_Transformation_Functor F' F (T c) (\<Sigma> T) D' R' pm' fm'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. c = fst a \<and> snd a \<in> R c x ) \<and>
           (\<forall>a. a \<in> D' (fm c snd (\<lambda>_. True) x) \<longrightarrow> (c, a) \<in> R' (fm c snd (\<lambda>_. True) x))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fm' (\<lambda>a. (c, a)) (\<lambda>_. True) (fm c snd (\<lambda>_. True) x) = x
\<Longrightarrow> (x \<Ztypecolon> F (\<Sigma> T)) = (fm c snd (\<lambda>_. True) x \<Ztypecolon> F' (T c))\<close>
  unfolding Functional_Transformation_Functor_def Premise_def
  apply (clarsimp simp del: split_paired_All; rule assertion_eq_intro)

  subgoal premises prems
    by (insert prems(1)[of c, THEN spec[where x=x], THEN spec[where x=snd], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-) ;
        clarsimp simp add: transformation_weaken;
        metis fst_conv snd_eqD transformation_weaken)

  subgoal premises prems
    by (insert prems(2)[THEN spec[where x=\<open>fm c snd (\<lambda>_. True) x\<close>], THEN spec[where x=\<open>\<lambda>a. (c, a)\<close>],
                        THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-),
        clarsimp simp add: transformation_weaken) .



subsection \<open>Nondeterministic Abstraction\<close>

text \<open>Transformation functor requires inner elements to be transformed into some fixed \<phi>-type
  independently with the element. It seems to be a limitation. For example, we want to transform
  a list of unknown bit-length numbers \<open>l \<Ztypecolon> List \<nat>\<^sub>f\<^sub>r\<^sub>e\<^sub>e\<close> where \<open>x \<Ztypecolon> \<nat>\<^sub>f\<^sub>r\<^sub>e\<^sub>e \<equiv> (x \<Ztypecolon> \<nat>[b] \<s>\<u>\<b>\<j> b. x < 2^b)\<close>
  into a set of all lists of such numbers \<open>{l | ? } \<Ztypecolon> List \<nat>[?]\<close> where the question marks denote
  the terms cannot be expressed yet now.

  Such transformation can be expressed by \<^emph>\<open>Dependent Sum Type\<close> \<open>\<Sigma>\<close> and \<^emph>\<open>Set Abstraction\<close> \<open>LooseState\<close> \<close>

declare SubjectionTY_def[embed_into_\<phi>type del] \<comment> \<open>replaced by \<open>Set_Abstraction\<close>\<close>

\<phi>type_def Set_Abstraction :: \<open>('a,'b) \<phi> \<Rightarrow> ('a, 'b set) \<phi>\<close> ("\<S>")
  where [embed_into_\<phi>type]: \<open>s \<Ztypecolon> \<S> T \<equiv> (x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s)\<close>
  deriving Sep_Functor_1 \<comment> \<open>Its Object_Equiv is an example for non-symmetric reachability relation\<close>
       and \<open>Transformation_Functor \<S> \<S> T U (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>g Sx Sy. Sy = {y. \<exists>x\<in>Sx. g x y})\<close>
       and \<open>Functional_Transformation_Functor Set_Abstraction Set_Abstraction T U
                      (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>_ _ _. True) (\<lambda>f P X. { f x |x. x \<in> X \<and> P x })\<close>
       and \<open>Separation_Homo\<^sub>I \<S> \<S> \<S> T U UNIV (\<lambda>x. case x of (A, B) \<Rightarrow> A \<times> B)\<close>
       and Carrier_Set
       and Open_Abstraction_to_Raw
       and \<open>c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {x} \<Ztypecolon> \<S> T \<close>
       and \<open>(\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to Itself)
        \<Longrightarrow> \<forall>s. (s \<Ztypecolon> \<S> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>x. r x y \<and> x \<in> s) @action to Itself)\<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' Set_Abstraction.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (\<S> ?T) (\<lambda>x. \<exists>xa. xa \<in> x \<and> ?P xa) \<close>),
  (@{thm' Set_Abstraction.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (\<S> ?T) (\<lambda>x. \<exists>xa. xa \<in> x \<and> ?P xa)  \<close>),
  (@{thm' Set_Abstraction.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set (\<S> ?T) (\<lambda>x. \<forall>xa. xa \<in> x \<longrightarrow> ?P xa) \<close>),
  (@{thm' Set_Abstraction.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (\<S> ?T) (\<lambda>x. \<forall>xa. xa \<in> x \<longrightarrow> ?T\<^sub>D xa) (\<lambda>x. \<exists>xa. xa \<in> x \<and> ?T\<^sub>P xa) \<close>),
  (@{thm' Set_Abstraction.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (\<S> ?T) (\<lambda>x. \<exists>uu. uu \<in> x \<and> ?T\<^sub>D uu) \<close>),
  (@{thm' Set_Abstraction.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (\<S> ?T) (\<lambda>Sx Sy. \<forall>x. x \<in> Sx \<longrightarrow> (\<exists>y. y \<in> Sy \<and> ?eq x y)) \<close>),
  (@{thm' Set_Abstraction.Transformation_Functor}, \<^pattern_prop>\<open> Transformation_Functor \<S> \<S> ?T ?U (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>g Sx Sy. Sy = {y. \<exists>x\<in>Sx. g x y}) \<close>),
  (@{thm' Set_Abstraction.Functional_Transformation_Functor}, \<^pattern_prop>\<open> Functional_Transformation_Functor \<S> \<S> ?T ?U (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>_ _ _. True) (\<lambda>f P X. {f x |x. x \<in> X \<and> P x}) \<close>),
  (@{thm' Set_Abstraction.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I \<S> \<S> \<S> ?T ?U UNIV (\<lambda>(A, B). A \<times> B) \<close>),
  (@{thm' Set_Abstraction.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E \<S> \<S> \<S> ?Ta ?U (\<lambda>x. (Domain x, Range x)) \<close>)
]\<close>


text \<open>Read it as 'the abstract object is certain element in the set'

Together with the \<^const>\<open>SubjectionTY\<close>, \<^const>\<open>\<phi>Dependent_Sum\<close> and \<^const>\<open>Set_Abstraction\<close> embed
  BI connective \<open>\<and>\<close> (\<^const>\<open>Subjection\<close>) and \<open>\<exists>\<close> (\<^const>\<open>ExSet\<close>) into \<phi>-types. The embedding of \<open>\<exists>\<close>
  is in an algebraic way having good properties like the \<Sigma>-Homomorphism and \<S>-Homomorphism introduced below.

The system reduces the three \<phi>-types actively just like how it reduces BI \<open>\<exists>\<close> and \<open>\<and>\<close>.
Any pure facts in the conjunctions are extracted and stored, and existentially quantified variables are fixed.
This reduction is reversible (meaning loosing no information).

User should define their own \<phi>-types wrapping \<open>\<S>\<close> if they do not want this reduction.
However, a specific fixed variable is generally easier to use than a certain element in a set.

\<open>\<Sigma>\<close>-type usually cannot be reduced because there is no non-trivial homomorphism
\<open>x \<Ztypecolon> F(\<Sigma> T) \<longleftrightarrow> f(x) \<Ztypecolon> \<Sigma>(F T)\<close> that moves a \<open>\<Sigma>\<close> out from a type operator \<open>F\<close>, unless
all the first projection of the elements of \<open>x\<close> are equal. However,
the reasoning about \<open>\<Sigma>\<close> has no problem because the \<open>x\<close> is given, so the parameters of the type i.e.,
the first projections of the elements of \<open>x\<close> are known.
We can apply \<open>\<Sigma>\<^sub>E\<close> and \<open>\<Sigma>\<^sub>I\<close> in the element transformation of \<open>x\<close> by \<open>F\<close>'s transformation functor property,
and the generated proof obligations about \<open>x\<close> are able to specify the type parameter of \<open>T\<close>,
e.g., if all the first projection of the elements of \<open>x\<close> are unchanged throughout the transformation, the
  type parameter of \<open>T\<close> is unchanged).
\<open>x \<Ztypecolon> \<Sigma> T \<longrightarrow> \<pi>\<^sub>2(x) \<Ztypecolon> T (\<pi>\<^sub>1 x)     (\<Sigma>\<^sub>E)\<close>
\<open>x \<Ztypecolon> T(c) \<longrightarrow> (c,x) \<Ztypecolon> \<Sigma> T        (\<Sigma>\<^sub>I)\<close>

\<open>\<S>\<close> type has homomorphism, and it is entailed in Transformation Functor.

\<close>

declare SubjectionTY_def[embed_into_\<phi>type add]
        Set_Abstraction_def[embed_into_\<phi>type del]

subsubsection \<open>Rules\<close>

paragraph \<open>Simplifications\<close>

lemma Set_Abstraction_single[embed_into_\<phi>type]:
  \<open>{x} \<Ztypecolon> \<S> T \<equiv> x \<Ztypecolon> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma Set_Abstraction_unfold_defined:
  \<open> {x. x = y \<and> P} \<Ztypecolon> \<S> T \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> P \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma Set_Abstraction_unfold_Ex:
  \<open> {x. \<exists>a. P x a} \<Ztypecolon> \<S> T \<equiv> {x. P x a} \<Ztypecolon> \<S> T \<s>\<u>\<b>\<j> a. \<top> \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp blast

lemma Set_Abstraction_unfold':
  \<open> NO_MATCH {a} s
\<Longrightarrow> NO_MATCH {x. x = y'\<and> P'} s
\<Longrightarrow> NO_MATCH {x. \<exists>a. P'' x a} s
\<Longrightarrow> (s \<Ztypecolon> \<S> T) = (x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s)\<close>
  using Set_Abstraction.unfold .

lemmas [\<phi>programming_base_simps, assertion_simps, simp] =
  Set_Abstraction_single
  Set_Abstraction_unfold_defined
  Set_Abstraction_unfold_Ex
  Set_Abstraction_unfold'

lemma \<phi>\<s>\<u>\<b>\<j>_over_\<S>[\<phi>programming_simps]:
  \<open>\<S> (T \<phi>\<s>\<u>\<b>\<j> P) \<equiv> (\<S> T) \<phi>\<s>\<u>\<b>\<j> P\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI, simp, blast)

lemma [embed_into_\<phi>type]:
  \<open> NO_MATCH (\<lambda>_. T') T
\<Longrightarrow> f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { (x, f x) |x. P x } \<Ztypecolon> \<S> (\<Sigma> T)\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open> f x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { f x |x. P x } \<Ztypecolon> \<S> T \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open>x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> x \<in> s \<s>\<u>\<b>\<j> x. \<top> \<equiv> s \<Ztypecolon> \<S> T \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open> NO_MATCH (\<lambda>_. T') T
\<Longrightarrow> {x. P c x} \<Ztypecolon> \<S> (T c) \<s>\<u>\<b>\<j> c. \<top> \<equiv> {x. \<exists>c y. x = (c, y) \<and> P c y} \<Ztypecolon> \<S> (\<Sigma> T)\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open> {x. P c x} \<Ztypecolon> \<S> T \<s>\<u>\<b>\<j> c. \<top> \<equiv> {x. \<exists>c. P c x} \<Ztypecolon> \<S> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

paragraph \<open>Conversion Setup\<close>

lemma pure_type_to_ex_quantified_form_3:
  \<open> Collect P \<Ztypecolon> \<S> T \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. P y \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

ML \<open>Phi_Conv.set_rules__type_form_to_ex_quantified
      @{thms' Set_Abstraction_unfold_Ex Set_Abstraction_unfold_defined
              SubjectionTY.unfold} ;
    Phi_Conv.set_rules__type_form_to_ex_quantified_single_var
      @{thms' Set_Abstraction_unfold_Ex pure_type_to_ex_quantified_form_3
              SubjectionTY.unfold} \<close>


paragraph \<open>ToA Reasoning\<close>

declare [[\<phi>trace_reasoning = 1]]

thm Set_Abstraction.intro_reasoning\<^sub>R
thm Set_Abstraction.intro_reasoning
thm Set_Abstraction.elim_reasoning

text \<open>Type-level \<open>Set_Abstraction.intro_reasoning\<close> is not activated as the reasoning uses
  transformation functor.

  see Set_Abstraction.intro_reasoning

NG! TODO!\<close>

thm Set_Abstraction.intro_reasoning(1)  [\<phi>reason 60]
        Set_Abstraction.elim_reasoning(1)[\<phi>reason 1000]

(*TODO!!!*)

lemma [\<phi>reason 2800]:
  \<open> (\<And>a \<in> fst x. (a, snd x) \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P )
\<Longrightarrow> x \<Ztypecolon> (\<S> T) \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def Premise_def Transformation_def meta_Ball_def
  by (cases x; cases C; clarsimp; blast)


subsubsection \<open>\<S>-Homomorphism (Commutativity over \<S>)\<close>

text \<open>The homomorphism of \<open>\<S>\<close> type is entailed in the transformation functor directly.\<close>

lemma \<S>_Homo\<^sub>E [\<phi>reason_template name Fa.\<S>\<^sub>E []]:
  \<open> Transformation_Functor Fa Fb (\<S> T) T D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D s \<and> b \<in> a \<longrightarrow> b \<in> R s)
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> s' : Collect (mapper (\<lambda>S x. x \<in> S) s)) @action \<A>_template_reason
\<Longrightarrow> s \<Ztypecolon> Fa (\<S> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> \<S> (Fb T)\<close>
  unfolding Transformation_Functor_def Transformation_def Premise_def Action_Tag_def Simplify_def
  by clarsimp

text \<open>Does the reverse transformation exist?. The commutativity between \<open>F\<close> and \<open>\<S>\<close> gonna be a problem.\<close>

lemma \<S>_Homo\<^sub>I [\<phi>reason_template name Fa.\<S>\<^sub>I []]:
  \<open> Functional_Transformation_Functor Fa Fb T (\<S> T) D R pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x a. x \<in> s \<and> a \<in> D x \<longrightarrow> f a \<in> R x \<and> a \<in> f a) \<and>
           (\<forall>x \<in> s. fm f (\<lambda>_. True) x = s')
\<Longrightarrow> s \<Ztypecolon> \<S> (Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<close>
  unfolding Functional_Transformation_Functor_def Transformation_def Premise_def
  apply clarsimp
  subgoal premises prems for v x
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=f], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2-),
        clarsimp,
        blast) .

lemma \<S>_Homo_rewr [\<phi>reason_template name Fa.\<S>_rewr []]:
  \<open> Transformation_Functor Fa Fb (\<S> T) T D R mapper
\<Longrightarrow> Functional_Transformation_Functor Fb Fa T (\<S> T) D' R' pm fm
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> s' : Collect (mapper (\<lambda>S x. x \<in> S) s)) @action \<A>_template_reason
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D s \<and> b \<in> a \<longrightarrow> b \<in> R s) \<and>
           ( (\<forall>x a. x \<in> s' \<and> a \<in> D' x \<longrightarrow> s \<in> R' x \<and> a \<in> s) \<and>
             (\<forall>x \<in> s'. fm (\<lambda>_. s) (\<lambda>_. True) x = s) \<comment> \<open>Isabelle simplifier fails to find an instantiation
                  of \<open>f\<close> to reduce the following condition even when the instantiation is simply \<open>\<lambda>_. s\<close>
                  in most of situations. Therefore, here we give a duplicated disjunction substituting
                  \<open>\<lambda>_. s\<close> for \<open>f\<close> directly, so the the simplification works. \<close>
           \<or> (\<forall>x a. x \<in> s' \<and> a \<in> D' x \<longrightarrow> f a \<in> R' x \<and> a \<in> f a) \<and>
             (\<forall>x \<in> s'. fm f (\<lambda>_. True) x = s))
\<Longrightarrow> (s \<Ztypecolon> Fa (\<S> T)) = (s' \<Ztypecolon> \<S> (Fb T)) \<close>
  unfolding Action_Tag_def Simplify_def Premise_def
  by ((clarify, elim disjE);
     (rule assertion_eq_intro,
     (rule \<S>_Homo\<^sub>E[unfolded Premise_def Simplify_def Action_Tag_def, where Fa=Fa and Fb=Fb],
       assumption, simp, simp),
     (clarify, rule \<S>_Homo\<^sub>I[unfolded Premise_def, where Fa=Fb and Fb=Fa],
       assumption, simp)))

lemma \<S>_Homo_rewr_ty [\<phi>reason_template name Fa.\<S>_rewr_ty []]:
  \<open> Transformation_Functor Fa Fb (\<S> T) T D R mapper
\<Longrightarrow> Functional_Transformation_Functor Fb Fa T (\<S> T) D' R' pm fm
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>s. Collect (mapper (\<lambda>S x. x \<in> S) s) = s) @action \<A>_template_reason
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>s a b. a \<in> D s \<and> b \<in> a \<longrightarrow> b \<in> R s) \<and>
           ( (\<forall>s x a. x \<in> s \<and> a \<in> D' x \<longrightarrow> s \<in> R' x \<and> a \<in> s) \<and>
             (\<forall>s x. x \<in> s \<longrightarrow> fm (\<lambda>_. s) (\<lambda>_. True) x = s) \<or>
             (\<forall>s x a. x \<in> s \<and> a \<in> D' x \<longrightarrow> f s a \<in> R' x \<and> a \<in> f s a) \<and>
             (\<forall>s x. x \<in> s \<longrightarrow> fm (f s) (\<lambda>_. True) x = s) )
\<Longrightarrow> Fa (\<S> T) = \<S> (Fb T) \<close>
  unfolding Action_Tag_def Simplify_def Premise_def
  apply (rule \<phi>Type_eqI_BI, clarify)
  subgoal for s
    by (rule \<S>_Homo_rewr[unfolded Premise_def Simplify_def Action_Tag_def, where s'=s and s=s and Fa=Fa and Fb=Fb and f=\<open>f s\<close>],
        assumption, assumption, simp, meson) .

(* TODO: meta analysis, and commutativity of \<open>\<S>\<close>

lemma \<S>_Homo\<^sub>I [\<phi>reason_template name \<S>\<^sub>I []]:

lemma
  \<open> Transformation_Functor Fa Fb T (\<S> T) D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D s \<longrightarrow> {a} \<in> R s)
\<Longrightarrow> s \<Ztypecolon> \<S> (Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<s>\<u>\<b>\<j> s'. mapper (\<lambda>a b. b = {a}) s s' \<close>
  unfolding Action_Tag_def Functional_Transformation_Functor_def Premise_def
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>a. {a}\<close>], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2) ;
        clarsimp simp add: transformation_weaken) .

(*the reverse map cannot be derived using TF.*)

lemma
  \<open> (\<And>a \<in> fst x. a \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U ...)
\<Longrightarrow> x \<Ztypecolon> \<S> T \<^emph>[Cw] \<S> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] \<S> R \<close>

lemma \<S>_Homo\<^sub>I [\<phi>reason_template name \<S>\<^sub>I []]:
  \<open> Functional_Transformation_Functor Fa Fb T (\<S> T) D R pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<exists>f. \<forall>x \<in> s. s' = fm f (\<lambda>_. True) x \<and> (\<forall>a \<in> D x. f a \<in> R x))
\<Longrightarrow> s \<Ztypecolon> \<S> (Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<close>
  unfolding Action_Tag_def Transformation_Functor_def Premise_def
  apply clarsimp
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>a b. b = {a}\<close>], simplified]
               prems(2),
        clarsimp) .
*)

(*
lemma \<S>_Homo\<^sub>I [\<phi>reason_template name \<S>\<^sub>I []]:
  \<open> Transformation_Functor Fa Fb T (\<S> T) D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D s \<longrightarrow> {a} \<in> R s)
\<Longrightarrow> s \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<s>\<u>\<b>\<j> s'. mapper (\<lambda>a b. b = {a}) s s' \<close>
  unfolding Action_Tag_def Transformation_Functor_def Premise_def
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>a b. b = {a}\<close>], simplified]
               prems(2),
        clarsimp) .
*)


text \<open>The above rules are interesting but essentially useless as it is replaced by the following rule,
  which eliminates any \<open>\<S>\<close> in a ready sequent of CoP.

mmm but what if during the separation extraction when a \<open>\<S>\<close> is generated by some previous reasoning?

The above rules are still useful in giving the commutativity between \<open>F\<close> and \<open>\<S>\<close>.
\<close>

lemma [\<phi>reason 1000]:
  \<open>s \<Ztypecolon> \<S> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s @action \<A>_transitive_simp\<close>
  unfolding Action_Tag_def Transformation_def
  by simp


 
subsection \<open>Vertical Composition\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 30)
  where \<open>\<phi>Composition T U x = (y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<Turnstile> (x \<Ztypecolon> U))\<close>
  deriving \<open>Carrier_Set T P \<Longrightarrow> Carrier_Set (T \<Zcomp> U) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> U) \<longrightarrow> P v)\<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Composition.Carrier_Set}, \<^pattern_prop>\<open>Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set (?T \<Zcomp> ?U) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> ?U) \<longrightarrow> ?P v)\<close>)
]\<close>

text \<open>
  We do not use deriver here.
  It is too basic and our reasoner can barely do little about \<phi>-types embedded in a
  satisfaction statement because it as a pure proposition loses the type structure to guide our
  reasoner. As a consequence, almost every property of the \<phi>-type has to be proven manually.

  For this reason, user should use \<open>(T \<Zcomp> U)\<close> instead of a raw satisfaction statement \<open>x \<Turnstile> X\<close>.
  The only meaningful interpretation of the satisfaction statement that we can imagine, is for
  vertical composition of abstractions. Therefore, \<open>(T \<Zcomp> U)\<close> should be able to replace any usage
  of satisfaction statement.
\<close>

subsubsection \<open>Algebraic Properties\<close>

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain U A
\<Longrightarrow> Abstract_Domain T B
\<Longrightarrow> Abstract_Domain (T \<Zcomp> U) (\<lambda>x. A x \<and> Ex B) \<close>
  unfolding Inhabited_def Action_Tag_def Abstract_Domain_def
  by simp blast

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain\<^sub>L U A
\<Longrightarrow> Abstract_Domain\<^sub>L T B
\<Longrightarrow> Abstract_Domain\<^sub>L (T \<Zcomp> U) (\<lambda>x. A x \<and> All B) \<close>
  unfolding Inhabited_def Action_Tag_def Abstract_Domain\<^sub>L_def
  by clarsimp blast

text \<open>The space between the upper bound and the lower bound is inevitable as we lost the exact value
  of the middle-level object in this vertical composition.\<close>

lemma [\<phi>reason 1000]:
  \<open> Functionality U P\<^sub>U
\<Longrightarrow> Functionality T P\<^sub>T
\<Longrightarrow> Functionality (T \<Zcomp> U) (\<lambda>x. P\<^sub>U x \<and> (\<forall>m. m \<Turnstile> (x \<Ztypecolon> U) \<longrightarrow> P\<^sub>T m)) \<close>
  unfolding Functionality_def Premise_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B'
\<Longrightarrow> Transformation_Functor ((\<Zcomp>) B) ((\<Zcomp>) B') T U (\<lambda>x. {x}) (\<lambda>_. UNIV) (\<lambda>r. r)\<close>
  unfolding Transformation_Functor_def Transformation_def \<r>Guard_def Premise_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B'
\<Longrightarrow> Functional_Transformation_Functor ((\<Zcomp>) B) ((\<Zcomp>) B') T U (\<lambda>x. {x}) (\<lambda>_. UNIV) (\<lambda>_ P. P) (\<lambda>f _. f)\<close>
  unfolding Functional_Transformation_Functor_def Transformation_def \<r>Guard_def Premise_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rU x y @action to (Itself :: ('b,'b) \<phi>))
\<Longrightarrow> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'c) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rT x y @action to (Itself :: ('c,'c) \<phi>))
\<Longrightarrow> x \<Ztypecolon> T \<Zcomp> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>m. rT m y \<and> rU x m) @action to (Itself :: ('c,'c) \<phi>)\<close>
  unfolding Transformation_def Action_Tag_def
  by clarsimp  blast

lemma [\<phi>reason 1000]:
  \<open> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> m \<Ztypecolon> T
\<Longrightarrow> m \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U
\<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<Zcomp> U \<close>
  unfolding Action_Tag_def Transformation_def Premise_def
  by clarsimp blast

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>I B D\<^sub>B P\<^sub>B
\<Longrightarrow> Identity_Elements\<^sub>I (B \<Zcomp> T) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> D\<^sub>B v) (\<lambda>x. (\<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> P\<^sub>B v) \<and> Inhabited (x \<Ztypecolon> T))\<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Transformation_def Orelse_shortcut_def
            Inhabited_def
  by clarsimp blast

(*TODO: analysis of completeness*)

lemma [\<phi>reason 1000]:
  \<open> Identity_Elements\<^sub>E B D\<^sub>B
\<Longrightarrow> Identity_Elements\<^sub>E (B \<Zcomp> T) (\<lambda>x. \<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> D\<^sub>B v) \<close>
  unfolding Identity_Element\<^sub>E_def Identity_Elements\<^sub>E_def Transformation_def
  by clarsimp blast
 
lemma [\<phi>reason 1000]:
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv (B \<Zcomp> T) eq \<close>
  unfolding Object_Equiv_def Transformation_def
  by clarsimp blast

lemma \<Psi>_comp:
  \<open> \<Psi>[\<psi>] (x \<Ztypecolon> T) = (x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T) \<close>
  unfolding BI_eq_iff
  by clarsimp

(* TODO?
lemma [\<phi>reason 1200]:
  \<open> y \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE U \<w>\<i>\<t>\<h> P
\<Longrightarrow> y \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE (T \<Zcomp> U) \<w>\<i>\<t>\<h> P\<close>
  \<medium_left_bracket> premises Y[unfolded Transformation_def Itself_expn, simplified, useful]
    construct\<phi> \<open>x \<Ztypecolon> T \<Zcomp> U\<close> \<medium_right_bracket> .
*)

lemma \<phi>Composition_Separation_Homo\<^sub>I[\<phi>reason 1000]:
  \<open> Object_Sep_Homo\<^sub>I B UNIV
\<Longrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U UNIV (\<lambda>x. x)\<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
  by (clarsimp, insert times_set_I, blast)

lemma (*The above rule is reversible. requiring the sep homo domain being the univ is already the weakest.*)
  \<open> S \<noteq> {}
\<Longrightarrow> \<forall>T U. Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U S (\<lambda>x. x)
\<Longrightarrow> Object_Sep_Homo\<^sub>I B UNIV \<close>
  unfolding Separation_Homo\<^sub>I_def Object_Sep_Homo\<^sub>I_def Transformation_def
  apply (clarsimp simp add: set_mult_expn)
  apply (simp add: \<phi>Type_def)
  subgoal premises prems for x y u v
    by (insert prems(2)[THEN spec[where x=\<open>\<lambda>_. {y}\<close>], THEN spec[where x=\<open>\<lambda>_. {x}\<close>], simplified]
               prems(1,3-5),
        auto simp add: Satisfaction_def) .

declare [[\<phi>trace_reasoning = 1]]
  
lemma \<phi>Composition_separatio_functor_unzip[\<phi>reason 1000]:
  \<open> Object_Sep_Homo\<^sub>E B
\<Longrightarrow> Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U (\<lambda>x. x)\<close>
  for B :: \<open>('d::sep_magma,'e::sep_magma) \<phi>\<close>
  unfolding Separation_Homo\<^sub>E_def Transformation_def Object_Sep_Homo\<^sub>E_def
  by (clarsimp simp add: set_mult_expn; blast)

lemma (*The above rule is reversible*)
  \<open> \<forall>T U. Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U (\<lambda>x. x) \<Longrightarrow> Object_Sep_Homo\<^sub>E B \<close>
  unfolding Separation_Homo\<^sub>E_def Object_Sep_Homo\<^sub>E_def Transformation_def
  apply (clarsimp simp add: set_mult_expn)
  apply (simp add: \<phi>Type_def Satisfaction_def)
  subgoal premises prems for x y v
    by (insert prems(1)[THEN spec[where x=\<open>\<lambda>_. {y}\<close>], THEN spec[where x=\<open>\<lambda>_. {x}\<close>], simplified]
               prems(2-3), blast) .



(* subsection \<open>Embedding Universal Quantification\<close>

\<phi>type_def \<phi>Type_univ_quant :: \<open>('c \<Rightarrow> ('a, 'b) \<phi>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b)\<phi>\<close> ("\<forall>\<^sub>\<phi> _" [10] 10)
  where \<open>\<phi>Type_univ_quant T = (\<lambda>x. \<forall>\<^sub>B\<^sub>Ic. x c \<Ztypecolon> T c)\<close>

lemma \<phi>Type_univ_quant_expn[\<phi>expns]:
  \<open>p \<in> (f \<Ztypecolon> (\<forall>\<^sub>\<phi> T)) \<longleftrightarrow> (\<forall>x. p \<in> (f x \<Ztypecolon> T x))\<close>
  unfolding \<phi>Type_univ_quant_def \<phi>Type_def by clarsimp
*)



subsection \<open>Finite Multiplicative Quantification\<close>


declare [[\<phi>trace_reasoning = 0 ]]

text \<open>The type parameter \<open>T\<close> is not paramterized by the quantified variable. It is not a restriction
  as we have \<open>\<Sigma>\<close>. Instead, only when \<open>T\<close> is not parameterized, \<open>\<big_ast>\<^sup>\<phi> I T\<close> forms a semimodule.\<close>

\<phi>type_def \<phi>Mul_Quant :: \<open>'i set \<Rightarrow> ('c::sep_algebra, 'x) \<phi> \<Rightarrow> ('c::sep_algebra, 'i \<Rightarrow> 'x) \<phi>\<close> ("\<big_ast>\<^sup>\<phi>")
  where [embed_into_\<phi>type]: \<open>\<big_ast>\<^sup>\<phi> I T = (\<lambda>x. \<big_ast>i\<in>I. x i \<Ztypecolon> T)\<close>
  deriving Basic
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (\<big_ast>\<^sup>\<phi> I T) (\<lambda>x. \<forall>i \<in> I. P (x i)) \<close>
       (*and Abstract_Domain\<^sub>L (*TODO*)*)
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J \<Longrightarrow> Transformation_Functor (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> J) T U (\<lambda>x. x ` I) (\<lambda>_. UNIV) (\<lambda>g x y. \<forall>i\<in>I. g (x i) (y i))\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J \<Longrightarrow> Functional_Transformation_Functor (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> J) T U (\<lambda>x. x ` I) (\<lambda>_. UNIV) (\<lambda>_ P x. \<forall>i\<in>I. P (x i)) (\<lambda>f _. (o) f)\<close>
       and Sep_Functor_1
       and Functionality
       and Semimodule_NonDistr
       and Closed_Semimodule_Zero
       and Carrier_Set

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Mul_Quant.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (\<big_ast>\<^sup>\<phi> ?I ?T) (\<lambda>x. \<forall>i\<in>?I. ?P (x i))  \<close>),
  (@{thm' \<phi>Mul_Quant.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set (?T:: ?'b \<Rightarrow> ?'c::{sep_algebra,sep_carrier_1} BI) ?P \<Longrightarrow> Carrier_Set (\<big_ast>\<^sup>\<phi> ?I ?T) (\<lambda>x. \<forall>xa. xa \<in> ?I \<longrightarrow> ?P (x xa)) \<close>),
  (@{thm' \<phi>Mul_Quant.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (\<big_ast>\<^sup>\<phi> ?I ?T) (\<lambda>x. \<forall>xa. xa \<in> ?I \<longrightarrow> ?P (x xa)) \<close>),
  (@{thm' \<phi>Mul_Quant.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (\<big_ast>\<^sup>\<phi> ?I ?T) (\<lambda>x. \<forall>xa. xa \<in> ?I \<longrightarrow> ?T\<^sub>D (x xa)) (\<lambda>x. \<forall>xa\<in>?I. ?T\<^sub>P (x xa)) \<close>),
  (@{thm' \<phi>Mul_Quant.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (\<big_ast>\<^sup>\<phi> ?I ?T) (\<lambda>x. finite ?I \<and> (\<forall>xa. xa \<in> ?I \<longrightarrow> ?T\<^sub>D (x xa))) \<close>),
  (@{thm' \<phi>Mul_Quant.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (\<big_ast>\<^sup>\<phi> ?I ?T) (\<lambda>x y. \<forall>xa. xa \<in> ?I \<longrightarrow> ?eq (x xa) (y xa)) \<close>),
  (@{thm' \<phi>Mul_Quant.Transformation_Functor}, \<^pattern_prop>\<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?I = ?J \<Longrightarrow> Transformation_Functor (\<big_ast>\<^sup>\<phi> ?I) (\<big_ast>\<^sup>\<phi> ?J) ?T ?U (\<lambda>x. x ` ?I) (\<lambda>_. UNIV) (\<lambda>g x y. \<forall>i\<in>?I. g (x i) (y i))  \<close>),
  (@{thm' \<phi>Mul_Quant.Functional_Transformation_Functor}, \<^pattern_prop>\<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?I = ?J \<Longrightarrow> Functional_Transformation_Functor (\<big_ast>\<^sup>\<phi> ?I) (\<big_ast>\<^sup>\<phi> ?J) ?T ?U (\<lambda>x. x ` ?I) (\<lambda>_. UNIV) (\<lambda>_ P x. \<forall>i\<in>?I. P (x i)) (\<lambda>f _. (\<circ>) f)  \<close>),
  (@{thm' \<phi>Mul_Quant.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I (\<big_ast>\<^sup>\<phi> ?I) (\<big_ast>\<^sup>\<phi> ?I) (\<big_ast>\<^sup>\<phi> ?I) ?Ta ?U UNIV zip_fun \<close>),
  (@{thm' \<phi>Mul_Quant.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E (\<big_ast>\<^sup>\<phi> ?I) (\<big_ast>\<^sup>\<phi> ?I) (\<big_ast>\<^sup>\<phi> ?I) ?Ta ?U unzip_fun \<close>),
  (@{thm' \<phi>Mul_Quant.Semimodule_Zero}, \<^pattern_prop>\<open> Semimodule_Zero \<big_ast>\<^sup>\<phi> ?T 0 \<close>),
  (@{thm' \<phi>Mul_Quant.Closed_Semimodule_Zero}, \<^pattern_prop>\<open> Closed_Semimodule_Zero \<big_ast>\<^sup>\<phi> ?T 0 \<close>),
  (@{thm' \<phi>Mul_Quant.Semimodule_Identity}, \<^pattern_prop>\<open> Semimodule_Identity \<big_ast>\<^sup>\<phi> ?T {?i} (\<lambda>_. True) (\<lambda>f. f ?i)  \<close>),
  (@{thm' \<phi>Mul_Quant.Semimodule_Scalar_Assoc\<^sub>I}, \<^pattern_prop>\<open> Semimodule_Scalar_Assoc\<^sub>I \<big_ast>\<^sup>\<phi> \<big_ast>\<^sup>\<phi> \<big_ast>\<^sup>\<phi> ?T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<times>) (\<lambda>_ _. case_prod) \<close>),
  (@{thm' \<phi>Mul_Quant.Semimodule_Scalar_Assoc\<^sub>E}, \<^pattern_prop>\<open> Semimodule_Scalar_Assoc\<^sub>E \<big_ast>\<^sup>\<phi> \<big_ast>\<^sup>\<phi> \<big_ast>\<^sup>\<phi> ?T finite finite (\<lambda>_ _ _. True) (\<times>) (\<lambda>_ _. case_prod)  \<close>)
]\<close>



subsubsection \<open>Syntax\<close>

nonterminal "dom_idx"

syntax
  "_one_dom" :: \<open>pttrns \<Rightarrow> 'a set \<Rightarrow> dom_idx\<close> ("_/\<in>_" [0,51] 50)
  "_more_dom":: \<open>dom_idx \<Rightarrow> dom_idx \<Rightarrow> dom_idx\<close> ("_,/ _" [49, 50] 49)
  "_\<phi>Mul_Quant" :: "dom_idx \<Rightarrow> logic \<Rightarrow> logic"  ("(2\<big_ast>[_]/ _)" [49, 1000] 1000)
  "_\<phi>Mul_Quant_mid" :: "dom_idx \<Rightarrow> logic \<Rightarrow> logic"

translations
  "CONST \<phi>Type x (_\<phi>Mul_Quant (_one_dom i I) T)" == "CONST \<phi>Type (\<lambda>i. x) (CONST \<phi>Mul_Quant I T)"
  "CONST \<phi>Type x (_\<phi>Mul_Quant (_more_dom d (_one_dom i I)) T)" == "CONST \<phi>Type (\<lambda>i. x) (_\<phi>Mul_Quant d (CONST \<phi>Mul_Quant I T))"


subsubsection \<open>Configure\<close>

lemma \<phi>Mul_Quant_induct:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> finite I
\<Longrightarrow> (\<And>T x. P {} T x)
\<Longrightarrow> (\<And>I T x i. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> finite I \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<notin> I \<Longrightarrow> P I T x \<Longrightarrow> P (insert i I) T x)
\<Longrightarrow> P I T x\<close>
  unfolding Premise_def
  subgoal premises prems
    by (insert prems(2-);
        induct rule: finite_induct[OF prems(1)]; clarsimp) .

setup \<open>Context.theory_map (
  Phi_Type_Algebra.override_ind_rule (\<^pattern>\<open>\<phi>Mul_Quant\<close>, @{thm' \<phi>Mul_Quant_induct}))\<close>


subsubsection \<open>Algebraic Properties\<close>

text \<open>Instead of deriving the Scalar Distributivity automatically, we give them manually, as the scalar
  distribution of the assertion-level \<open>\<big_ast>\<close> is not activated in the reasoning system by default
  (it is too aggressive to enable it).\<close>

lemma \<phi>Mul_Quant_SDistr_Homo\<^sub>Z[\<phi>reason 1000]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z \<big_ast>\<^sup>\<phi> T (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ D\<^sub>g (f,g). f \<oplus>\<^sub>f[D\<^sub>g] g) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def dom_of_add_set_def
  by (clarsimp simp add: \<phi>Prod_expn' \<phi>Mul_Quant.unfold sep_quant_scalar_distr;
      smt (verit) Mul_Quant_def Transformation_def disjoint_iff plus_set_in_iff prod.cong)

lemma \<phi>Mul_Quant_SDistr_Homo\<^sub>U[\<phi>reason 1000]:
  \<open> Semimodule_SDistr_Homo\<^sub>U \<big_ast>\<^sup>\<phi> T (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ f. (f ,f)) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_def dom_of_add_set_def
  by (clarsimp simp add: \<phi>Mul_Quant.unfold \<phi>Prod_expn' sep_quant_scalar_distr)


subsubsection \<open>Rewrites\<close>

lemma \<phi>Mul_Quant_insert:
  \<open> k \<notin> I
\<Longrightarrow> (x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T) = ((x k, x) \<Ztypecolon> T \<^emph> \<big_ast>\<^sup>\<phi> I T) \<close>
  unfolding \<phi>Mul_Quant.unfold \<phi>Prod_expn'
  by (clarsimp simp add: sep_quant_insert)

subsubsection \<open>Transformations\<close>

paragraph \<open>Reduction for individually inserted elements\<close>

lemma [\<phi>reason %ToA_derived_red-10]: \<comment>\<open>The priority must be lower than the derived \<open> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> {x} T\<close>\<close>
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T) * (x k \<Ztypecolon> T) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Mul_Quant.unfold \<r>Guard_def Premise_def
  by (clarsimp simp add: sep_quant_insert)

lemma [\<phi>reason %ToA_derived_red-10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T) * (x k \<Ztypecolon> T) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Mul_Quant.unfold \<r>Guard_def Premise_def
  by (clarsimp simp add: sep_quant_insert)

lemma [\<phi>reason %ToA_derived_red-10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst (\<lambda>f. (f k, f)) x \<Ztypecolon> (T \<^emph> \<big_ast>\<^sup>\<phi> I T) \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding \<r>Guard_def Premise_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn' \<phi>Mul_Quant_insert)


(* TODO: It is about ToA on literal FMQ domain.

   The proof cannot continue as it requires the \<phi>-type commutativity \<open>x \<Ztypecolon> \<black_circle> \<big_ast>\<^sup>\<phi> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> \<black_circle> T\<close>
   The commutativity between \<phi>-type operators! It should be a meta deriver...

lemma
  \<open> \<g>\<u>\<a>\<r>\<d> NO_MATCH {e} I
\<Longrightarrow> (fst x i, fst wr) \<Ztypecolon> T \<^emph>[Cwi] Wi \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Y \<^emph>[Cri] Ri \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> I \<comment> \<open>The domain of the \<open>\<big_ast>\<close> must be known during reasoning time\<close>
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> J : Set.remove i I
\<Longrightarrow> if Cwi then (fst x, snd x) \<Ztypecolon> \<big_ast>\<^sup>\<phi> J T \<^emph>[Cw] Ws \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> wr \<Ztypecolon> Wi \<^emph>[Crj] Rs \<w>\<i>\<t>\<h> Q \<and>\<^sub>\<r>
                (((snd y, snd wr) \<Ztypecolon> \<half_blkcirc>[Cri] Ri \<^emph> \<half_blkcirc>[Crj] Rs) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>merge)
           else (Cw, Ws) = (False, \<top>\<^sub>\<phi>) \<and>\<^sub>\<r>
                (((snd y, fst x) \<Ztypecolon> \<half_blkcirc>[Cri] Ri \<^emph> \<half_blkcirc>[True] \<big_ast>\<^sup>\<phi> J T) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>merge)
\<Longrightarrow> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T \<^emph>[Cw] Ws \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> Y \<^emph>[Cr] R \<w>\<i>\<t>\<h> Q \<and> P\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_MATCH_def Ant_Seq_def
  apply (cases Cwi; simp add: cond_prod_transformation_rewr;
         simp add: Cond_\<phi>Prod_expn_\<phi>Some \<phi>Prod_expn' \<phi>Prod_expn'')

  \<medium_left_bracket> premises Tr1 and I and J[] and Tr2
    have [simp]: \<open>I = insert i J\<close> using I J by force
    have th1[simp]: \<open>i \<notin> J\<close> using J by fastforce ;; ;;

    simplify (\<phi>Prod_expn'', \<phi>Mul_Quant_insert)

thm \<phi>Mul_Quant_insert
thm Tr2
*)



subsection \<open>Sum Type\<close>

declare [[\<phi>trace_reasoning = 0]]


(*TODO: move me*)
lemma [simp]:
  \<open>pred_sum = case_sum\<close>
  using pred_sum_eq_case_sum by blast


(*TODO: finish me!*)

declare [[\<phi>trace_reasoning = 0]]
  
\<phi>type_def \<phi>Sum :: \<open>('c,'x) \<phi> \<Rightarrow> ('c, 'y) \<phi> \<Rightarrow> ('c, 'x + 'y) \<phi>\<close> (infixl "+\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T +\<^sub>\<phi> U) = (\<lambda>xy. case xy of Inl x \<Rightarrow> x \<Ztypecolon> T | Inr y \<Rightarrow> y \<Ztypecolon> U)\<close>
  deriving \<open>Object_Equiv T eq\<^sub>T \<Longrightarrow> Object_Equiv U eq\<^sub>U \<Longrightarrow> Object_Equiv (T +\<^sub>\<phi> U) (rel_sum eq\<^sub>T eq\<^sub>U)\<close>
       and Abstract_Domain
       and \<open>Abstract_Domain\<^sub>L T T\<^sub>D
        \<Longrightarrow> Abstract_Domain\<^sub>L U U\<^sub>D
        \<Longrightarrow> Abstract_Domain\<^sub>L (T +\<^sub>\<phi> U) (case_sum T\<^sub>D U\<^sub>D)\<close> (*simplification fails to transform the result into the ideal form*)
       and \<open>Carrier_Set T P
        \<Longrightarrow> Carrier_Set U Q
        \<Longrightarrow> Carrier_Set (T +\<^sub>\<phi> U) (pred_sum P Q)\<close> (*simplification fails*)
       and Identity_Elements
       and \<open>Identity_Elements\<^sub>E T T\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E U U\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E (T +\<^sub>\<phi> U) (case_sum T\<^sub>D U\<^sub>D) \<close> (*The inference works, but the result is not in an ideal form,
                                                            so we give the annotation manually*)
       and \<open>Identity_Elements\<^sub>I T T\<^sub>D T\<^sub>P
        \<Longrightarrow> Identity_Elements\<^sub>I U U\<^sub>D U\<^sub>P 
        \<Longrightarrow> Identity_Elements\<^sub>I (T +\<^sub>\<phi> U) (case_sum T\<^sub>D U\<^sub>D) (case_sum T\<^sub>P U\<^sub>P) \<close> (*The inference works*)
       and Functional_Transformation_Functor
       (*and Commutativity_Deriver\<^sub>E_rev*)

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Sum.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain ?U ?Pa \<Longrightarrow> Abstract_Domain (?T +\<^sub>\<phi> ?U) (case_sum ?P ?Pa) \<close>)
]\<close>


subsubsection \<open>Rewrites\<close>

lemma \<phi>Sum_red[simp]:
  \<open>(Inl a \<Ztypecolon> T +\<^sub>\<phi> U) = (a \<Ztypecolon> T)\<close>
  \<open>(Inr b \<Ztypecolon> T +\<^sub>\<phi> U) = (b \<Ztypecolon> U)\<close>
  unfolding \<phi>Sum.unfold
  by simp_all

(* TODO: if so, we can totally replace \<open>\<or>\<^sub>\<phi>\<close> by \<open>+\<^sub>\<phi>\<close>
(*TODO: reduce \<open>(x \<Ztypecolon> T) + (y \<Ztypecolon> U) + (z \<Ztypecolon> Z) \<equiv> {Inl ({Inl x} + {Inr y})} + {Inr z} \<Ztypecolon> \<S> (\<S> (T +\<^sub>\<phi> U) +\<^sub>\<phi> Z)
                                           \<equiv> {Inl (Inl x)} + {Inl (Inr y)} + {Inr z} \<Ztypecolon> \<S> T +\<^sub>\<phi> \<S> U +\<^sub>\<phi> \<S> Z\<close>*)
lemma [embed_into_\<phi>type]:
  \<open> ((x \<Ztypecolon> T) + (y \<Ztypecolon> U)) = ({Inl x} + {Inr y} \<Ztypecolon> \<S> (T +\<^sub>\<phi> U)) \<close>
  unfolding BI_eq_iff
  by (clarsimp simp add: split_sum_ex)

term \<open>{Inl ({Inl x} + {Inr y})} + {Inr z} \<Ztypecolon> \<S> (\<S> (T +\<^sub>\<phi> U) +\<^sub>\<phi> Z)\<close>

*)

subsubsection \<open>Transformations\<close>

\<phi>reasoner_group ToA_splitting_\<phi>Sum = (%ToA_splitting-20, [%ToA_splitting-20, %ToA_splitting-19])
                                      for (\<open>x \<Ztypecolon> T +\<^sub>\<phi> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close>, \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T +\<^sub>\<phi> U\<close>)
                                       in ToA_splitting and < ToA_splitting_If
  \<open>ToA splitting \<open>\<phi>Sum\<close>\<close>

declare \<phi>Sum.intro_reasoning(1)[\<phi>reason %ToA_splitting_\<phi>Sum]
        \<phi>Sum.elim_reasoning (1)[\<phi>reason %ToA_splitting_\<phi>Sum]

lemma [\<phi>reason %ToA_splitting_\<phi>Sum+1 for \<open>(_, _) \<Ztypecolon> (_ +\<^sub>\<phi> _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (case x of Inl a \<Rightarrow> (a, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>a a] W\<^sub>a a | Inr b \<Rightarrow> (b, w\<^sub>b b) \<Ztypecolon> U \<^emph>[C\<^sub>b b] W\<^sub>b b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x, case_sum w\<^sub>a w\<^sub>b x) \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[case_sum C\<^sub>a C\<^sub>b x] case_sum W\<^sub>a W\<^sub>b x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by (cases x; auto simp add: \<phi>Prod_expn' Cond_\<phi>Prod_expn)

lemma [\<phi>reason %ToA_splitting_\<phi>Sum]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> snd x = case_sum w\<^sub>a w\<^sub>b (fst x) \<Longrightarrow>
      (case fst x of Inl a \<Rightarrow> (a, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>a a] W\<^sub>a a | Inr b \<Rightarrow> (b, w\<^sub>b b) \<Ztypecolon> U \<^emph>[C\<^sub>b b] W\<^sub>b b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> snd x = case_sum w\<^sub>a w\<^sub>b (fst x)
\<Longrightarrow> x \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[case_sum C\<^sub>a C\<^sub>b (fst x)] case_sum W\<^sub>a W\<^sub>b (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Premise_def
  by (cases x; case_tac a; auto simp add: \<phi>Prod_expn' Cond_\<phi>Prod_expn)

lemma [\<phi>reason %ToA_splitting_\<phi>Sum]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (case fst y of Inl a \<Rightarrow> (a, snd y) \<Ztypecolon> T \<^emph>[C] R | Inr b \<Rightarrow> (b, snd y) \<Ztypecolon> U \<^emph>[C] R) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  by (cases y; case_tac a; cases C; simp add: \<phi>Prod_expn')


subsubsection \<open>Rule\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma \<phi>Sum_Comm\<^sub>I_temlpate [\<phi>reason_template name F.\<phi>Sum_Comm\<^sub>I[]]:
  \<open> Functional_Transformation_Functor F\<^sub>T F T (T +\<^sub>\<phi> U) D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F U (T +\<^sub>\<phi> U) D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D : (\<lambda>x. case x of Inl u \<Rightarrow> (\<forall>a \<in> D\<^sub>T u. Inl a \<in> R\<^sub>T u)
                              | Inr v \<Rightarrow> (\<forall>b \<in> D\<^sub>U v. Inr b \<in> R\<^sub>U v))) @action \<A>_template_reason
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r : (embedded_func (case_sum (fm\<^sub>T Inl (\<lambda>_. True)) (fm\<^sub>U Inr (\<lambda>_. True)))
                                (pred_sum (pm\<^sub>T Inl (\<lambda>_. True)) (pm\<^sub>U Inr (\<lambda>_. True))))) @action \<A>_template_reason
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F\<^sub>T F\<^sub>U (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U D r \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Functional_Transformation_Functor_def Premise_def
            Action_Tag_def Simplify_def
  by (clarify; case_tac x; clarsimp)

lemma \<phi>Sum_Comm\<^sub>E_temlpate [\<phi>reason_template name F.\<phi>Sum_Comm\<^sub>E[]]:
  \<open> Functional_Transformation_Functor F F'\<^sub>T (T +\<^sub>\<phi> U) T D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F F'\<^sub>U (T +\<^sub>\<phi> U) U D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x a. a \<in> D\<^sub>T x \<and> isl a \<longrightarrow> projl a \<in> R\<^sub>T x) \<and>
           (\<forall>x a. a \<in> D\<^sub>U x \<and> \<not> isl a \<longrightarrow> projr a \<in> R\<^sub>U x)
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] D : (\<lambda>x. (\<forall>a \<in> D\<^sub>T x. isl a) \<or> (\<forall>b \<in> D\<^sub>U x. \<not> isl b))) @action \<A>_template_reason
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] r : (embedded_func (\<lambda>x. if (\<forall>a \<in> D\<^sub>T x. isl a)
                                    then Inl (fm\<^sub>T projl (\<lambda>_. True) x)
                                    else Inr (fm\<^sub>U projr (\<lambda>_. True) x))
                               (\<lambda>x. if (\<forall>a \<in> D\<^sub>T x. isl a)
                                    then pm\<^sub>T projl (\<lambda>_. True) x
                                    else pm\<^sub>U projr (\<lambda>_. True) x))) @action \<A>_template_reason
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U D r \<close>
  unfolding Functional_Transformation_Functor_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Simplify_def Action_Tag_def
  apply (clarify; case_tac \<open>Ball (D\<^sub>T x) isl\<close>; auto)
  subgoal premises prems for x
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=projl], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems (3-),
        clarsimp simp add: Transformation_def split_sum_all Ball_def)
  subgoal premises prems for x
    by (insert prems(2)[THEN spec[where x=x], THEN spec[where x=projr], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-),
        clarsimp simp add: Transformation_def split_sum_all Ball_def) .



(*lemma \<phi>Sum_Comm\<^sub>E [\<phi>reason %\<phi>type_algebra_prop_cut]:
  \<open> Functional_Transformation_Functor F\<^sub>T F T (T +\<^sub>\<phi> U) D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F U (T +\<^sub>\<phi> U) D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F\<^sub>T F\<^sub>U \<phi>Sum \<phi>Sum T U
                   (\<lambda>x. case x of Inl u \<Rightarrow> (\<forall>a \<in> D\<^sub>T u. Inl a \<in> R\<^sub>T u)
                                | Inr v \<Rightarrow> (\<forall>b \<in> D\<^sub>U v. Inr b \<in> R\<^sub>U v))
                   (embedded_func (case_sum (fm\<^sub>T Inl (\<lambda>_. True)) (fm\<^sub>U Inr (\<lambda>_. True)))
                                  (pred_sum (pm\<^sub>T Inl (\<lambda>_. True)) (pm\<^sub>U Inr (\<lambda>_. True)))) \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Functional_Transformation_Functor_def Premise_def
  by (clarify; case_tac x; clarsimp)*)

lemma \<phi>Sum_Comm\<^sub>E [\<phi>reason %\<phi>type_algebra_prop_cut]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Transformation_def
  by (clarsimp simp add: split_sum_all)


subsection \<open>Additive Disjunction\<close>

text \<open>Depreciated! Use \<open>\<phi>Sum\<close> instead!\<close>

\<phi>type_def \<phi>Union :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<or>\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T \<or>\<^sub>\<phi> U) = (\<lambda>x. (fst x \<Ztypecolon> T) + (snd x \<Ztypecolon> U))\<close>
  deriving Basic
       and Identity_Elements
       and \<open>(c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T) \<and> y = undefined \<or>\<^sub>c\<^sub>u\<^sub>t
            (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U) \<and> x = undefined
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> T \<or>\<^sub>\<phi> U \<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Union.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L ?U ?Pa \<Longrightarrow> Abstract_Domain\<^sub>L (?T \<or>\<^sub>\<phi> ?U) (\<lambda>x. ?P (fst x) \<or> ?Pa (snd x)) \<close>),
  (@{thm' \<phi>Union.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain ?U ?Pa \<Longrightarrow> Abstract_Domain (?T \<or>\<^sub>\<phi> ?U) (\<lambda>x. ?P (fst x) \<or> ?Pa (snd x))  \<close>),
  (@{thm' \<phi>Union.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set ?U ?Pa \<Longrightarrow> Carrier_Set (?T \<or>\<^sub>\<phi> ?U) (\<lambda>x. ?Pa (snd x) \<and> ?P (fst x))  \<close>),
  (@{thm' \<phi>Union.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P
                                               \<Longrightarrow> Identity_Elements\<^sub>I ?U ?U\<^sub>D ?U\<^sub>P
                                               \<Longrightarrow> Identity_Elements\<^sub>I (?T \<or>\<^sub>\<phi> ?U) (\<lambda>x. ?U\<^sub>D (snd x) \<and> ?T\<^sub>D (fst x)) (\<lambda>x. ?T\<^sub>P (fst x) \<or> ?U\<^sub>P (snd x)) \<close>),
  (@{thm' \<phi>Union.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D
                                               \<Longrightarrow> Identity_Elements\<^sub>E ?U ?U\<^sub>D
                                               \<Longrightarrow> Identity_Elements\<^sub>E (?T \<or>\<^sub>\<phi> ?U) (\<lambda>x. ?U\<^sub>D (snd x) \<or> ?T\<^sub>D (fst x)) \<close>),
  (@{thm' \<phi>Union.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?er
                                          \<Longrightarrow> Object_Equiv ?U ?eq
                                          \<Longrightarrow> Object_Equiv (?T \<or>\<^sub>\<phi> ?U) (\<lambda>x y. ?er (fst x) (fst y) \<and> ?eq (snd x) (snd y))\<close>)
]\<close>


(*       and \<open>\<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> P c \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x = f c @action to T)
        \<Longrightarrow> \<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> Q c \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U \<s>\<u>\<b>\<j> x. x = g c @action to U)
        \<Longrightarrow> \<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> P c \<or> Q c \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<or>\<^sub>\<phi> U \<s>\<u>\<b>\<j> y. y = (f c, g c) @action to (T \<or>\<^sub>\<phi> U))\<close>*)


subsubsection \<open>Configurations\<close>

declare \<phi>Union_def[embed_into_\<phi>type del]

lemma [embed_into_\<phi>type]:
  \<open>(x \<Ztypecolon> T) + (y \<Ztypecolon> U) \<equiv> (x,y) \<Ztypecolon> T \<or>\<^sub>\<phi> U\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp
 
let_\<phi>type \<phi>Union deriving \<open>Object_Equiv (\<circle> \<or>\<^sub>\<phi> \<circle>) (\<lambda>_ _. True)\<close>



subsection \<open>Embedding Additive Conjunction\<close>

declare [[\<phi>trace_reasoning = 0]]

declare False_def[symmetric, simp]

\<phi>type_def \<phi>Inter :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<and>\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T \<and>\<^sub>\<phi> U) = (\<lambda>x. (fst x \<Ztypecolon> T) \<and>\<^sub>B\<^sub>I (snd x \<Ztypecolon> U))\<close>
  deriving Basic
       and \<open>  Abstract_Domain T P
          \<Longrightarrow> Abstract_Domain U Q
          \<Longrightarrow> Abstract_Domain (T \<and>\<^sub>\<phi> U) (\<lambda>(x,y). P x \<and> Q y)\<close> (*the gusser works actually but the annotation
                                              has to be given in order to disable deriving Abstract_Domain\<^sub>L.
                                              I'm thinking if it means our mechanism of weak dependency is bad.*)
       (*and \<open>  Abstract_Domain\<^sub>L T P
          \<Longrightarrow> Abstract_Domain\<^sub>L U Q
          \<Longrightarrow> Abstract_Domain\<^sub>L (T \<and>\<^sub>\<phi> U) (\<lambda>(x,y). P x \<and> Q y)\<close>
         The lower bound of (T \<and>\<^sub>\<phi> U) is not derivable as there is no sufficiency reasoning for additive conjunction *)
       and Object_Equiv
       and Identity_Elements
       and Functional_Transformation_Functor
       and (*Make_Abstraction_from_Raw (*TODO:simplification*)*)
          \<open> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> T \<and>\<^sub>\<phi> U \<close>
       and Functionality
       and Commutativity_Deriver\<^sub>I_rev

     (*DO NOT REMOVE, they are right but I'm thinking if we really should support so much additive conjunction
              It should be a bi-functor
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = A' \<Longrightarrow>
              Transformation_Functor ((\<and>\<^sub>\<phi>) A) ((\<and>\<^sub>\<phi>) A') Basic_BNFs.snds (\<lambda>_. UNIV) (rel_prod (=))\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B' \<Longrightarrow>
              Transformation_Functor (\<lambda>A. A \<and>\<^sub>\<phi> B) (\<lambda>A. A \<and>\<^sub>\<phi> B') Basic_BNFs.fsts (\<lambda>_. UNIV) (\<lambda>r. rel_prod r (=))\<close>
       and \<open>Functional_Transformation_Functor ((\<and>\<^sub>\<phi>) A) ((\<and>\<^sub>\<phi>) A') Basic_BNFs.snds (\<lambda>_. UNIV)
                                              (rel_prod (=)) (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = A') (pred_prod (\<lambda>a. True)) (map_prod (\<lambda>a. a))\<close>
       and \<open>Functional_Transformation_Functor (\<lambda>A. A \<and>\<^sub>\<phi> B) (\<lambda>A. A \<and>\<^sub>\<phi> B') Basic_BNFs.fsts
                                              (\<lambda>_. UNIV) (\<lambda>r. rel_prod r (=)) (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B') (\<lambda>p. pred_prod p (\<lambda>a. True)) (\<lambda>f. map_prod f (\<lambda>a. a))\<close> *)

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Inter.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain ?U ?Q \<Longrightarrow> Abstract_Domain (?T \<and>\<^sub>\<phi> ?U) (\<lambda>(x, y). ?P x \<and> ?Q y) \<close>),
  (@{thm' \<phi>Inter.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set ?U ?Pa \<Longrightarrow> Carrier_Set (?T \<and>\<^sub>\<phi> ?U) (\<lambda>x. ?Pa (snd x) \<and> ?P (fst x)) \<close>),
  (@{thm' \<phi>Inter.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality ?U ?Pa \<Longrightarrow> Functionality (?T \<and>\<^sub>\<phi> ?U) (\<lambda>x. ?Pa (snd x) \<and> ?P (fst x)) \<close>),
  (@{thm' \<phi>Inter.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow>
             Identity_Elements\<^sub>I ?U ?U\<^sub>D ?U\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (?T \<and>\<^sub>\<phi> ?U) (\<lambda>x. ?U\<^sub>D (snd x) \<or> ?T\<^sub>D (fst x)) (\<lambda>x. ?U\<^sub>P (snd x) \<or> ?T\<^sub>P (fst x))   \<close>),
  (@{thm' \<phi>Inter.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E ?U ?U\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (?T \<and>\<^sub>\<phi> ?U) (\<lambda>x. ?U\<^sub>D (snd x) \<and> ?T\<^sub>D (fst x)) \<close>),
  (@{thm' \<phi>Inter.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?er \<Longrightarrow> Object_Equiv ?U ?eq \<Longrightarrow> Object_Equiv (?T \<and>\<^sub>\<phi> ?U) (\<lambda>x y. ?eq (snd x) (snd y) \<and> ?er (fst x) (fst y)) \<close>)
]\<close>

subsubsection \<open>Rules\<close>

declare \<phi>Inter_def[embed_into_\<phi>type del]

lemma \<phi>Inter_embedding[embed_into_\<phi>type]:
  \<open>(x \<Ztypecolon> T) \<and>\<^sub>B\<^sub>I (y \<Ztypecolon> U) \<equiv> (x, y) \<Ztypecolon> T \<and>\<^sub>\<phi> U\<close>
  unfolding atomize_eq BI_eq_iff
  by simp

lemma [\<phi>reason 1000]:
  \<open> fst x \<Ztypecolon> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ra y @action to Itself
\<Longrightarrow> snd x \<Ztypecolon> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rb y @action to Itself
\<Longrightarrow> x \<Ztypecolon> A \<and>\<^sub>\<phi> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ra y \<and> rb y @action to Itself \<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp

(*TODO: transformation rules for \<open>\<and>\<^sub>\<phi>\<close>*)

(* Commutativity of \<open>\<and>\<^sub>\<phi>\<close> cannot be derived simply from transformation functor. *)

lemma \<phi>Inter_comm\<^sub>E_template[\<phi>reason_template name F.\<phi>Inter_Comm\<^sub>E[]]:
  \<open> Functional_Transformation_Functor F F\<^sub>T (T \<and>\<^sub>\<phi> U) T D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F F\<^sub>U (T \<and>\<^sub>\<phi> U) U D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] D : (\<lambda>x. (\<forall>a \<in> D\<^sub>T x. fst a \<in> R\<^sub>T x) \<and> (\<forall>a \<in> D\<^sub>U x. snd a \<in> R\<^sub>U x))) @action \<A>_template_reason
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] r : (embedded_func (\<lambda>x. (fm\<^sub>T fst (\<lambda>_. True) x, fm\<^sub>U snd (\<lambda>_. True) x))
                                                (\<lambda>x. pm\<^sub>T fst (\<lambda>_. True) x \<and> pm\<^sub>U snd (\<lambda>_. True) x))) @action \<A>_template_reason
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F\<^sub>T F\<^sub>U (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U D r\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Functional_Transformation_Functor_def Premise_def
            Simplify_def Action_Tag_def
  apply clarify
  subgoal premises prems for x
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=fst], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2)[THEN spec[where x=x], THEN spec[where x=snd], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-);
        clarsimp simp add: Transformation_def) .

lemma \<phi>Inter_Comm\<^sub>I [\<phi>reason %\<phi>type_algebra_prop_cut]:
  \<open> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U
                    (\<lambda>(a,b). \<forall>u v c. u \<Turnstile> (a \<Ztypecolon> T) \<and> v \<Turnstile> (b \<Ztypecolon> U) \<and> c \<Turnstile> (u \<Ztypecolon> B) \<and> c \<Turnstile> (v \<Ztypecolon> B) \<longrightarrow>
                            (\<exists>w. c \<Turnstile> (w \<Ztypecolon> B) \<and> w \<Turnstile> (a \<Ztypecolon> T) \<and> w \<Turnstile> (b \<Ztypecolon> U)))
                    (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Transformation_def
  by clarsimp


subsection \<open>Vertical Composition of Function\<close>


text \<open>It is a more specific form than \<open>\<phi>Fun f \<Zcomp> T\<close> on which automation rules (particularly the Sep_Homo)
  can be given more generally.\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>reasoner_group
      identity_elements_of_\<phi>Fun = (100, [100, 140]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
                                                     in identity_element and > derived_identity_element \<open>\<close>
  and carrier_set_of_\<phi>Fun = (60, [60,70]) for \<open>Carrier_Set _ _\<close>
              

                             in carrier_set and > derived_carrier_set and < carrier_set_cut \<open>\<close>

declare [[\<phi>trace_reasoning = 0]]
    
\<phi>type_def \<phi>Fun' :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close> (infixr "\<Zcomp>\<^sub>f" 30)
  where \<open>\<phi>Fun' f T = (\<phi>Fun f \<Zcomp> T)\<close>
  opening extracting_Carrier_Set_sat
          extract_mul_carrier
          Identity_Element_sat
  deriving Basic
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 f
         \<Longrightarrow> Identity_Elements\<^sub>I (f \<Zcomp>\<^sub>f T) (\<lambda>_. True) (\<lambda>x. Inhabited (x \<Ztypecolon> T)) \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one f
         \<Longrightarrow> Identity_Elements\<^sub>I T D P
         \<Longrightarrow> Identity_Elements\<^sub>I (f \<Zcomp>\<^sub>f T) D P \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>I (f \<Zcomp>\<^sub>f T) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> f v = 1) (\<lambda>x. Inhabited (x \<Ztypecolon> T))\<close>
           (%identity_elements_of_\<phi>Fun)
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 f
         \<Longrightarrow> Identity_Elements\<^sub>E (f \<Zcomp>\<^sub>f T) (\<lambda>x. Inhabited (x \<Ztypecolon> T)) \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one f
         \<Longrightarrow> Identity_Elements\<^sub>E T D
         \<Longrightarrow> Identity_Elements\<^sub>E (f \<Zcomp>\<^sub>f T) D \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>E (f \<Zcomp>\<^sub>f T) (\<lambda>x. \<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> f v = 1) \<close>
           (%identity_elements_of_\<phi>Fun)
       and Functionality
       and Functional_Transformation_Functor
       (*and Trivial_\<Sigma>*)
       and \<open>homo_sep \<psi> \<Longrightarrow> Separation_Homo\<^sub>E (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) T U (\<lambda>x. x)\<close>
       and \<open>\<g>\<u>\<a>\<r>\<d> homo_mul_carrier f
        \<Longrightarrow> Carrier_Set U P
        \<Longrightarrow> Carrier_Set (f \<Zcomp>\<^sub>f U) P \<close> \<comment> \<open>Guesser fails. It is
                            still too hard for our guesser to infer \<open>homo_mul_carrier f\<close>\<close>
           (%carrier_set_of_\<phi>Fun+10)
       and \<open>\<g>\<u>\<a>\<r>\<d> constantly_inside_carrier f
        \<Longrightarrow> Carrier_Set (f \<Zcomp>\<^sub>f U) P\<close>
           (%carrier_set_of_\<phi>Fun)
       and Abstraction_to_Raw
       and Commutativity_Deriver
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] inj f
         \<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))\<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Fun'.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (?f \<Zcomp>\<^sub>f ?T) ?P \<close>),
  (@{thm' \<phi>Fun'.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (?f \<Zcomp>\<^sub>f ?T) ?P \<close>),
  (@{thm' \<phi>Fun'.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (?f \<Zcomp>\<^sub>f ?T) ?P \<close>),
  (@{thm' \<phi>Fun'.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (?f \<Zcomp>\<^sub>f ?T) ?eq \<close>),
  (@{thm' \<phi>Fun'.Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?f = ?fa \<Longrightarrow> Transformation_Functor ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?fa) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>a. a)  \<close>),
  (@{thm' \<phi>Fun'.Functional_Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?f = ?fa \<Longrightarrow> Functional_Transformation_Functor ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?fa) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>f a. a) (\<lambda>f P. f) \<close>),
  (@{thm' \<phi>Fun'.\<phi>Sum_Comm\<^sub>E}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?f = ?fa \<and> ?f = ?faa \<Longrightarrow>
        Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?fa) ((\<Zcomp>\<^sub>f) ?faa) (+\<^sub>\<phi>) (+\<^sub>\<phi>) ?T ?U (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>x. True))  \<close>),
  (@{thm' \<phi>Fun'.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c2,?'c2) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @action to (Itself::(?'c2,?'c2) \<phi>))
                                                    \<Longrightarrow> ?x \<Ztypecolon> ?f \<Zcomp>\<^sub>f ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c,?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = ?f x \<and> ?r ?x x) @action to (Itself::(?'c,?'c) \<phi>)  \<close>),
  (@{thm' \<phi>Fun'.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> ?f ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?f \<Zcomp>\<^sub>f ?T  \<close>)
]\<close>

lemmas \<phi>Fun'_\<phi>Sum_comm_rewr = Comm_Tyops_Rewr\<^sub>2_temlpate[OF \<phi>Fun'.\<phi>Sum_Comm\<^sub>E \<phi>Fun'.\<phi>Sum_Comm\<^sub>I, simplified]


subsubsection \<open>Reasoning Rules\<close>

text \<open>The following rule is more general than \<open>\<phi>Fun f \<Zcomp> T\<close> as it in addition supports non-closed homomorphism.\<close>

declare [[\<phi>trace_reasoning = 2]]

lemma \<phi>Fun'_Separation_Homo\<^sub>I[\<phi>reason 1000]:
  \<open> homo_sep \<psi>
\<Longrightarrow> closed_homo_sep \<psi> \<and>\<^sub>\<r> Dx = UNIV \<or>\<^sub>c\<^sub>u\<^sub>t
    Separation_Disj\<^sub>\<phi> \<psi> Dx U T
\<Longrightarrow> Separation_Homo\<^sub>I (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) T U Dx (\<lambda>x. x) \<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
            Separation_Disj\<^sub>\<phi>_def Separation_Disj_def closed_homo_sep_def
            homo_sep_def closed_homo_sep_disj_def Ant_Seq_def
            homo_sep_mult_def homo_sep_disj_def Orelse_shortcut_def TRACE_FAIL_def
  by (clarsimp simp add: Ball_def; metis)

lemma \<phi>Fun'_Scalar_Assoc\<^sub>I:
  \<open> Semimodule_Scalar_Assoc\<^sub>I \<phi>Fun' \<phi>Fun' \<phi>Fun' T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (o) (\<lambda>_ _ x. x) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Transformation_def
  by clarsimp blast

lemma \<phi>Fun'_Scalar_Assoc\<^sub>E:
  \<open> Semimodule_Scalar_Assoc\<^sub>E \<phi>Fun' \<phi>Fun' \<phi>Fun' T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (o) (\<lambda>_ _ x. x) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Transformation_def
  by clarsimp blast

text \<open>Though \<open>\<phi>Fun'\<close> comprises an associative semimodule, we don not activate it in the reasoning
  system because its associative reduction is not expected in usual reasoning.
  Instead, we manually instantiate useful properties.\<close>

lemmas \<phi>Fun'_scalar_assoc = scalar_assoc_template[OF \<phi>Fun'_Scalar_Assoc\<^sub>I \<phi>Fun'_Scalar_Assoc\<^sub>E, simplified]

lemma \<phi>Fun'_comm[\<phi>reason %\<phi>type_algebra_properties]:
  \<open> fun_commute \<psi> \<phi> \<psi>' \<phi>'
\<Longrightarrow> Tyops_Commute (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>') (\<phi>Fun' \<phi>) (\<phi>Fun' \<phi>') T
                  (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))\<close>
  unfolding Tyops_Commute_def fun_commute_def
  by (simp add: \<phi>Fun'_scalar_assoc)


subsubsection \<open>Guessing Property\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute g f g' f'
\<Longrightarrow> Guess_Tyops_Commute both G G' F F'
                        (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) (\<lambda>T x. x \<Ztypecolon> f \<Zcomp>\<^sub>f T) (\<lambda>T x. x \<Ztypecolon> f' \<Zcomp>\<^sub>f T) T
                        (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True\<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute both G G' F F'
                        (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) (\<lambda>T x. x \<Ztypecolon> f \<Zcomp>\<^sub>f T) (\<lambda>T x. x \<Ztypecolon> f' \<Zcomp>\<^sub>f T) T
                        (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) (fun_commute g f g' f') True\<close>
  unfolding Guess_Tyops_Commute_def ..


subsubsection \<open>Meta Analysis\<close>

lemma \<comment> \<open>The rule of \<open>\<phi>Fun'.\<phi>Inter_Comm\<^sub>I\<close> is reversible (for universally quantified x, T, U)\<close>
  \<open>(\<And>T U x. x \<Ztypecolon> (\<psi> \<Zcomp>\<^sub>f T) \<and>\<^sub>\<phi> (\<psi> \<Zcomp>\<^sub>f U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<psi> \<Zcomp>\<^sub>f (T \<and>\<^sub>\<phi> U)) \<Longrightarrow> inj \<psi>\<close>
  unfolding Transformation_def inj_def
  apply clarsimp
  subgoal premises prems for x y
    by (insert prems(1)[of _ \<open>\<lambda>_. {x}\<close> _ \<open>\<lambda>_. {y}\<close>]
               prems(2-),
        clarsimp simp add: \<phi>Type_def Satisfaction_def) .



subsection \<open>Injection into Unital Algebra\<close>

lemma \<phi>Some_def': \<open> \<black_circle> T = (Some \<Zcomp>\<^sub>f T) \<close>
  by (rule \<phi>Type_eqI_BI; simp add: BI_eq_iff)

declare [[\<phi>trace_reasoning = 0]]

setup \<open>Context.theory_map (
  Phi_Type_Algebra.add_type {no_auto=false}
        (\<^binding>\<open>\<phi>Some\<close>, \<^pattern>\<open>\<phi>Some\<close>, Phi_Type_Algebra.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>Some_def'}),
         \<^here>, Phi_Type_Algebra.Derivings.empty, [])
   #> snd )\<close>
  \<comment> \<open>Setup an alternative definition in the language of \<phi>-types so that we can apply
      derivers over these bootstrap \<phi>-types\<close>
let_\<phi>type \<phi>Some
  deriving Sep_Functor
       and Carrier_Set
       and Functionality
       and \<open>Identity_Elements\<^sub>I (\<black_circle> T) (\<lambda>_. False) (\<lambda>_. False)\<close>
       and \<open>Identity_Elements\<^sub>E (\<black_circle> T) (\<lambda>_. False)\<close>
       and Abstraction_to_Raw

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Some.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (\<black_circle> ?T) ?P  \<close>),
  (@{thm' \<phi>Some.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (\<black_circle> ?T) ?P  \<close>),
  (@{thm' \<phi>Some.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set (\<black_circle> ?T) ?P  \<close>),
  (@{thm' \<phi>Some.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (\<black_circle> ?T) ?P   \<close>),
  (@{thm' \<phi>Some.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I (\<black_circle> ?T) (\<lambda>_. False) (\<lambda>_. False)  \<close>),
  (@{thm' \<phi>Some.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E (\<black_circle> ?T) (\<lambda>_. False) \<close>),
  (@{thm' \<phi>Some.Transformation_Functor}, \<^pattern_prop>\<open> Transformation_Functor \<phi>Some \<phi>Some ?T ?U (\<lambda>a. {a}) (\<lambda>x. UNIV) (\<lambda>g. g) \<close>),
  (@{thm' \<phi>Some.Functional_Transformation_Functor}, \<^pattern_prop>\<open> Functional_Transformation_Functor \<phi>Some \<phi>Some ?T ?U (\<lambda>a. {a}) (\<lambda>x. UNIV) (\<lambda>f P. P) (\<lambda>f P. f) \<close>),
  (@{thm' \<phi>Some.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I \<phi>Some \<phi>Some \<phi>Some ?Ta ?U UNIV (\<lambda>x. x) \<close>),
  (@{thm' \<phi>Some.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E \<phi>Some \<phi>Some \<phi>Some ?Ta ?U (\<lambda>x. x) \<close>),
  (@{thm' \<phi>Some.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (\<black_circle> ?T) ?eq \<close>),
  (@{thm' \<phi>Some.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> Some ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<black_circle> ?T \<close>),
  (@{thm' \<phi>Some.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c, ?'c) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @action to (Itself::(?'c, ?'c) \<phi>))
                                                     \<Longrightarrow> ?x \<Ztypecolon> \<black_circle> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c option, ?'c option) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = Some x \<and> ?r ?x x) @action to (Itself::(?'c option, ?'c option) \<phi>) \<close>)
]\<close>

declare \<phi>Some.expansion[\<phi>expns del] \<comment> \<open>removing duplicates\<close>


subsection \<open>Domainoid\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Domainoid ("\<DD>[_]" [4] 1000)
    where \<open>\<DD>[\<delta>] T \<equiv> \<delta> \<Zcomp>\<^sub>f T \<phi>\<s>\<u>\<b>\<j> closed_homo_sep \<delta>\<close>
  \<comment> \<open>\<open>\<Psi>[\<psi>] (x \<Ztypecolon> T) \<equiv> x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T\<close>, therefore \<open>\<phi>Fun \<psi> \<Zcomp> T\<close> is always an exact solution for
      evaluating \<open>\<Psi>[\<psi>] (x \<Ztypecolon> T)\<close>. However, in the case of domainoid extraction, this is not a
      final expression directly giving the domainoids of resources. We want a direct expression
      even if just an upper or lower approximation. Due to this, here
      we introduce a differentiated syntax to emphasize the intention of extracting domainoid,
      on which specific reasoning procedures can be given to reduce the expression further.\<close>
 deriving Sep_Functor
      and \<open> constant_1 \<delta> \<and>\<^sub>\<r> (D,P) = (\<lambda>_. True, \<lambda>_. True) \<or>\<^sub>c\<^sub>u\<^sub>t
            homo_one \<delta> \<and>\<^sub>\<r> Identity_Elements\<^sub>I T D P
        \<Longrightarrow> Identity_Elements\<^sub>I (\<DD>[\<delta>] T) D P \<close>

      and \<open> closed_homo_sep \<delta>
        \<Longrightarrow> constant_1 \<delta> \<and>\<^sub>\<r> Abstract_Domain\<^sub>L T D \<or>\<^sub>c\<^sub>u\<^sub>t
            homo_one \<delta> \<and>\<^sub>\<r> Identity_Elements\<^sub>E T D
        \<Longrightarrow> Identity_Elements\<^sub>E (\<DD>[\<delta>] T) D \<close>

      and Commutativity_Deriver
      and \<open> comm_domainoid_mapper_rev TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' f f'
        \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>'] ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

      and \<open> comm_domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' f f'
        \<Longrightarrow> Tyops_Commute ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') \<DD>[\<delta>] \<DD>[\<delta>'] T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>


subsubsection \<open>Basic Rules\<close>

lemma WS_domainoid:
  \<open> closed_homo_sep \<delta>
\<Longrightarrow> \<Psi>[domainoid_tag \<delta>] (x \<Ztypecolon> T) = (x \<Ztypecolon> \<DD>[\<delta>] T) \<close>
  unfolding Domainoid.unfold BI_eq_iff domainoid_tag_def
  by clarsimp


subsubsection \<open>Approximating Domainoid\<close>

declare [[\<phi>reason_default_pattern \<open>_ \<le> (_ \<Ztypecolon> \<DD>[?d] ?T)\<close> \<Rightarrow> \<open>?var \<le> (_ \<Ztypecolon> \<DD>[?d] ?T)\<close> (300)
                              and \<open>(_ \<Ztypecolon> \<DD>[?d] ?T) \<le> _\<close> \<Rightarrow> \<open>(_ \<Ztypecolon> \<DD>[?d] ?T) \<le> ?var\<close> (300) ]]

lemma [\<phi>reason %BI_approx_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> closed_homo_sep \<delta>
\<Longrightarrow> A' \<le> (x \<Ztypecolon> \<DD>[\<delta>] T)
\<Longrightarrow> A' \<le> \<Psi>[domainoid_tag \<delta>] (x \<Ztypecolon> T) \<close>
  unfolding Premise_def
  by (simp add: WS_domainoid)

lemma [\<phi>reason %BI_approx_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> closed_homo_sep \<delta>
\<Longrightarrow> (x \<Ztypecolon> \<DD>[\<delta>] T) \<le> A'
\<Longrightarrow> \<Psi>[domainoid_tag \<delta>] (x \<Ztypecolon> T) \<le> A' \<close>
  unfolding Premise_def
  by (simp add: WS_domainoid)

lemma [\<phi>reason %BI_approx_success]:
  \<open> (x \<Ztypecolon> \<DD>[(\<lambda>_. d)] T) \<le> (d \<Ztypecolon> Itself) \<close>
  unfolding BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason %BI_approx_success]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Inhabited (x \<Ztypecolon> T)
\<Longrightarrow> (d \<Ztypecolon> Itself) \<le> (x \<Ztypecolon> \<DD>[(\<lambda>_. d)] T) \<close>
  for T :: \<open>('c::discrete_semigroup,'a) \<phi>\<close>
  and d :: \<open>'d::discrete_semigroup\<close>
  unfolding BI_sub_transformation Transformation_def Premise_def Inhabited_def
  by clarsimp

lemma [\<phi>reason %BI_approx_success]:
  \<open> (x \<Ztypecolon> \<DD>[(\<lambda>d. d)] T) \<le> (x \<Ztypecolon> T) \<close>
  unfolding BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason %BI_approx_success]:
  \<open> (x \<Ztypecolon> T) \<le> (x \<Ztypecolon> \<DD>[(\<lambda>d. d)] T) \<close>
  unfolding BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason_template %BI_approx_derived]:
  \<open> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>'] G G' T D (embedded_func f P)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> (f x \<Ztypecolon> G' (\<DD>[\<delta>'] T)) \<le> A'
\<Longrightarrow> (x \<Ztypecolon> \<DD>[\<delta>] (G T)) \<le> A' \<close>
  unfolding Premise_def Tyops_Commute_def BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason_template %BI_approx_derived]:
  \<open> Tyops_Commute G' G \<DD>[\<delta>'] \<DD>[\<delta>] T D (embedded_func f P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = y \<and> D x
\<Longrightarrow> A' \<le> (x \<Ztypecolon> G' (\<DD>[\<delta>'] T))
\<Longrightarrow> A' \<le> (y \<Ztypecolon> \<DD>[\<delta>] (G T)) \<close>
  unfolding Premise_def Tyops_Commute_def BI_sub_transformation Transformation_def
  by clarsimp blast


paragraph \<open>Guess the Forms\<close>

lemma [\<phi>reason %guess_tyop_commute for \<open>Guess_Tyops_Commute False \<DD>[_] ?var _ ?var_F' _ _ _ _ _ _ _ _ _\<close> ]:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>'
\<Longrightarrow> Guess_Tyops_Commute False \<DD>[\<delta>] \<DD>[\<delta>'] F F' uG uG' uF uF' T D r a c
\<Longrightarrow> Guess_Tyops_Commute False \<DD>[\<delta>] \<DD>[\<delta>'] F F' uG uG' uF uF' T D r a c \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute for \<open>Guess_Tyops_Commute True _ ?var_F' \<DD>[_] ?var _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>'
\<Longrightarrow> Guess_Tyops_Commute True F F' \<DD>[\<delta>] \<DD>[\<delta>'] uG uG' uF uF' T D r a c
\<Longrightarrow> Guess_Tyops_Commute True F F' \<DD>[\<delta>] \<DD>[\<delta>'] uG uG' uF uF' T D r a c \<close>
  unfolding Guess_Tyops_Commute_def ..

declare [[ML_print_depth = 100]]

subsubsection \<open>Application \label{phi-types/Domainoid/App}\<close>

lemma [\<phi>reason %abstract_domain]:
  \<open> Abstract_Domain\<^sub>L T D\<^sub>T
\<Longrightarrow> Abstract_Domain\<^sub>L U D\<^sub>U
\<Longrightarrow> domainoid TYPE('c::sep_magma) \<delta>
\<Longrightarrow> (\<And>x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (closed_homo_sep \<delta> \<and> Inhabited (x \<Ztypecolon> T)) \<Longrightarrow> (f x \<Ztypecolon> T') \<le> (x \<Ztypecolon> \<DD>[\<delta>] T))
          \<comment>\<open>expand \<open>\<Psi>[d] A, \<Psi>[d] B\<close> to a simpler (but should still strong) upper approximation\<close>
\<Longrightarrow> (\<And>y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (closed_homo_sep \<delta> \<and> Inhabited (y \<Ztypecolon> U)) \<Longrightarrow> (g y \<Ztypecolon> U') \<le> (y \<Ztypecolon> \<DD>[\<delta>] U))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x y. D\<^sub>T x \<and> D\<^sub>U y \<longrightarrow> (\<exists>a b. a \<Turnstile> (f x \<Ztypecolon> T') \<and> b \<Turnstile> (g y \<Ztypecolon> U') \<and> b ## a))
\<Longrightarrow> Abstract_Domain\<^sub>L (T \<^emph> U) (\<lambda>(x,y). D\<^sub>T x \<and> D\<^sub>U y)\<close>
  unfolding Inhabited_def BI_sub_iff Premise_def Action_Tag_def domainoid_def domainoid_tag_def
            Abstract_Domain\<^sub>L_def
  by (clarsimp simp add: closed_homo_sep_def closed_homo_sep_disj_def; metis)



subsection \<open>Vertical Composition of Scalar Multiplication\<close>

declare [[\<phi>trace_reasoning = 0 ]]

\<phi>type_def \<phi>ScalarMul :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 's \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close> ("\<s>\<c>\<a>\<l>\<a>\<r>[_] _ \<Zcomp> _" [31,31,30] 30)
  where \<open>\<phi>ScalarMul f s T = (scalar_mult f s \<Zcomp>\<^sub>f T)\<close>
  deriving Basic
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 (f s)
         \<Longrightarrow> Identity_Elements\<^sub>I T D P
         \<Longrightarrow> Identity_Elements\<^sub>I (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) D P \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one (f s)
         \<Longrightarrow> Identity_Elements\<^sub>I T D P
         \<Longrightarrow> Identity_Elements\<^sub>I (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) D P \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>I (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> f s v = 1) (\<lambda>x. Inhabited (x \<Ztypecolon> T))\<close>
           (%identity_elements_of_\<phi>Fun)
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 (f s)
         \<Longrightarrow> Identity_Elements\<^sub>E (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) (\<lambda>x. Inhabited (x \<Ztypecolon> T)) \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one (f s)
         \<Longrightarrow> Identity_Elements\<^sub>E T D
         \<Longrightarrow> Identity_Elements\<^sub>E (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) D \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>E (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) (\<lambda>x. \<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> f s v = 1) \<close>
           (%identity_elements_of_\<phi>Fun)
       and Functionality
       and Functional_Transformation_Functor
       (*and Trivial_\<Sigma>*)
       and Abstraction_to_Raw
       and \<open> homo_sep (scalar_mult \<psi> s)
         \<Longrightarrow> closed_homo_sep (scalar_mult \<psi> s) \<or>\<^sub>c\<^sub>u\<^sub>t
             Separation_Disj\<^sub>\<phi> (scalar_mult \<psi> s) Dx U T
         \<Longrightarrow> Separation_Homo\<^sub>I (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) T U Dx (\<lambda>x. x)\<close>
       and \<open> homo_sep (\<psi> s)
         \<Longrightarrow> Separation_Homo\<^sub>E (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) T U (\<lambda>x. x) \<close>
       and \<open> homo_mul_carrier (f s) \<Longrightarrow> Carrier_Set U P \<Longrightarrow> Carrier_Set (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> U) P \<close>
       and \<phi>Fun'.Comm
       and Commutativity_Deriver
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] inj (f s)
         \<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 (\<phi>ScalarMul f s) (\<phi>ScalarMul f s) (\<phi>ScalarMul f s) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U
                             (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))\<close>

       and \<open> comm_domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' (scalar_mult f s) (scalar_mult f' s')
        \<Longrightarrow> Tyops_Commute (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') \<DD>[\<delta>] \<DD>[\<delta>'] T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

       and \<open> comm_domainoid_mapper_rev TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' (scalar_mult f s) (scalar_mult f' s')
        \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>'] (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>ScalarMul.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (\<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T) ?P  \<close>),
  (@{thm' \<phi>ScalarMul.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (\<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T) ?P  \<close>),
  (@{thm' \<phi>ScalarMul.Carrier_Set}, \<^pattern_prop>\<open> homo_mul_carrier (?f ?s) \<Longrightarrow> Carrier_Set ?U ?P \<Longrightarrow> Carrier_Set (\<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?U) ?P  \<close>),
  (@{thm' \<phi>ScalarMul.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (\<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T) ?P \<close>),
  (@{thm' \<phi>ScalarMul.Transformation_Functor}, \<^pattern_prop>\<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?s = ?sa \<and> ?f = ?fa \<Longrightarrow> Transformation_Functor (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?fa ?sa) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>a. a) \<close>),
  (@{thm' \<phi>ScalarMul.Functional_Transformation_Functor}, \<^pattern_prop>\<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?s = ?sa \<and> ?f = ?fa
      \<Longrightarrow> Functional_Transformation_Functor (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?fa ?sa) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>f a. a) (\<lambda>f P. f) \<close>),
  (@{thm' \<phi>ScalarMul.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (\<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T) ?eq \<close>),
  (@{thm' \<phi>ScalarMul.\<phi>Fun'_Comm\<^sub>E}, \<^pattern_prop>\<open> fun_commute ?fa (scalar_mult ?f ?s) ?xc (scalar_mult ?xa ?xb) \<Longrightarrow>
    Tyops_Commute ((\<Zcomp>\<^sub>f) ?fa) ((\<Zcomp>\<^sub>f) ?xc) (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xa ?xb) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' \<phi>ScalarMul.\<phi>Fun'_Comm\<^sub>I}, \<^pattern_prop>\<open> fun_commute (scalar_mult ?f ?s) ?fa (scalar_mult ?xa ?xb) ?xc \<Longrightarrow>
    Tyops_Commute (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xa ?xb) ((\<Zcomp>\<^sub>f) ?fa) ((\<Zcomp>\<^sub>f) ?xc) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),
  (@{thm' \<phi>ScalarMul.\<phi>Sum_Comm\<^sub>E}, \<^pattern_prop>\<open>
      \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (?s = ?sa \<and> ?f = ?fa) \<and> ?s = ?saa \<and> ?f = ?faa \<Longrightarrow>
      Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?fa ?sa) (\<phi>ScalarMul ?faa ?saa) (+\<^sub>\<phi>) (+\<^sub>\<phi>) ?T ?U (\<lambda>x. True)
       (embedded_func (\<lambda>x. x) (\<lambda>x. True)) \<close>),
  (@{thm' \<phi>ScalarMul.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> scalar_mult ?f ?s ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T \<close>),
  (@{thm' \<phi>ScalarMul.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c2,?'c2) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @action to (Itself::(?'c2,?'c2) \<phi>))
                                                          \<Longrightarrow> ?x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c,?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = ?f ?s x \<and> ?r ?x x) @action to (Itself::(?'c,?'c) \<phi>)  \<close>)
]\<close>


subsubsection \<open>Reasoning Rules\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma Semimodule_Identity_by_function [\<phi>reason 1000]:
  \<open> module_scalar_identity \<psi>
\<Longrightarrow> Semimodule_Identity (\<phi>ScalarMul \<psi>) T 1 (\<lambda>_. True) (\<lambda>x. x) \<close>
  unfolding Semimodule_Identity_def module_scalar_identity_def scalar_mult_def BI_eq_iff
  by clarsimp

lemma Semimodule_Scalar_Assoc\<^sub>I_by_function[\<phi>reason 1000]:
  \<open> module_scalar_assoc \<psi> Ds
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) T Ds Ds (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) \<close>
  unfolding module_scalar_assoc_def Semimodule_Scalar_Assoc\<^sub>I_def scalar_mult_def Transformation_def
  by (clarsimp; blast)

lemma Semimodule_Scalar_Assoc\<^sub>E_by_function[\<phi>reason 1000]:
  \<open> module_scalar_assoc \<psi> Ds
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) T Ds Ds (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) \<close>
  unfolding module_scalar_assoc_def Semimodule_Scalar_Assoc\<^sub>E_def scalar_mult_def Transformation_def
  by clarsimp metis

declare [[\<phi>trace_reasoning = 0]]

lemma Semimodule_SDistr_Homo\<^sub>Z_by_function[\<phi>reason 1000]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Functionality T Dx
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> Abstract_Domain T D\<^sub>T
\<Longrightarrow> Carrier_Set T D\<^sub>C
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z (\<phi>ScalarMul \<psi>) T Ds
                            (\<lambda>s t (x,y). (D\<^sub>T x \<longrightarrow> D\<^sub>T y \<longrightarrow> eq x y \<and> Dx y \<and> D\<^sub>C y \<or> eq y x \<and> Dx x \<and> D\<^sub>C x))
                            (\<lambda>_ _. fst) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Transformation_def module_S_distr_def Is_Functional_def
            Object_Equiv_def Functionality_def Abstract_Domain_def Action_Tag_def Inhabited_def
            scalar_mult_def Carrier_Set_def Within_Carrier_Set_def
  by (clarsimp, metis)

text \<open>The domain of abstract objects constrains to ensure the two middle-level objects
  (namely, the concrete objects of \<open>T\<close> and the abstract objects of \<open>\<psi>\<close>) are identical so that
  we can apply the right distributive law \<open>smult (s + t) a = smult s a * smult t a\<close> of module,
  which requires the group objects \<open>a\<close> at the two sides of \<open>*\<close> to be identical.

  To this requirement, the instantiated domains above is the weakest.
\<close>

lemma \<comment> \<open>The instantiated domains above is the weakest upto using the \<open>module_S_distr \<psi> Ds\<close>,
          i.e., \<open>smult (s + t) a = smult s a * smult t a\<close>, when the \<open>Dx\<close>, \<open>eq\<close>, and \<open>D\<^sub>T\<close> are the weakest. \<close>
  \<open> (\<forall>x. p x \<longleftrightarrow> (\<forall>u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> u = v))
\<Longrightarrow> (\<forall>x y. eq x y \<longleftrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T))
\<Longrightarrow> (D\<^sub>Tx \<longleftrightarrow> (\<exists>u. u \<Turnstile> (x \<Ztypecolon> T))) \<and> (D\<^sub>Ty \<longleftrightarrow> (\<exists>u. u \<Turnstile> (y \<Ztypecolon> T)))
\<Longrightarrow> (\<forall>u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (y \<Ztypecolon> T) \<longrightarrow> u = v) \<longrightarrow> ((D\<^sub>Tx \<longrightarrow> eq x y \<and> p y) \<or> (D\<^sub>Ty \<longrightarrow> eq y x \<and> p x)) \<close>
  unfolding Transformation_def
  by auto metis
    
lemma Semimodule_SDistr_Homo\<^sub>U_by_function[\<phi>reason 1000]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Functionality T Dx
\<Longrightarrow> Abstract_Domain T D\<^sub>T
\<Longrightarrow> Carrier_Set T D\<^sub>C
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U (\<phi>ScalarMul \<psi>) T Ds
                            (\<lambda>s t x. D\<^sub>T x \<longrightarrow> Dx x \<and> D\<^sub>C x)
                            (\<lambda>_ _ x. (x,x))\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_def Transformation_def module_S_distr_def Is_Functional_def
            Object_Equiv_def Functionality_def Abstract_Domain_def Action_Tag_def Inhabited_def
            scalar_mult_def Carrier_Set_def Within_Carrier_Set_def
  by (clarsimp, metis)


subsubsection \<open>Commutativity\<close>

paragraph \<open>Guessing Property\<close>

declare Guess_Tyops_Commute_by_unfolding
        [where A=\<open>\<lambda>T x. (x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T)\<close> for f s,
         OF \<phi>ScalarMul.unfold,
         \<phi>reason %guess_tyop_commute]

paragraph \<open>Deriving the Commutativity with Itself\<close>

let_\<phi>type \<phi>ScalarMul deriving \<phi>ScalarMul.Comm\<^sub>I


subsubsection \<open>Guessing Antecedents\<close>

lemma [\<phi>reason %\<phi>TA_guesser for \<open>Guess_Zip_of_Semimodule _ _ _ _ _ (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?\<psi>] s \<Zcomp> T) _ _ _ _ _ _ \<close>]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[\<psi>] s \<Zcomp> T) T Ds
                            (\<lambda>s t (x,y). (D\<^sub>T x \<longrightarrow> D\<^sub>T y \<longrightarrow> eq x y \<and> Dx y \<and> D\<^sub>C y \<or> eq y x \<and> Dx x \<and> D\<^sub>C x))
                            (\<lambda>_ _. fst)
                            (Functionality T Dx \<and>\<^sub>\<r> Object_Equiv T eq \<and>\<^sub>\<r> Abstract_Domain T D\<^sub>T \<and>\<^sub>\<r> Carrier_Set T D\<^sub>C)
                            True \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser for \<open>Guess_Unzip_of_Semimodule _ _ _ _ _ (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?\<psi>] s \<Zcomp> T) _ _ _ _ _ _ \<close>]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[\<psi>] s \<Zcomp> T) T Ds
                            (\<lambda>s t x. D\<^sub>T x \<longrightarrow> Dx x \<and> D\<^sub>C x)
                            (\<lambda>_ _ x. (x,x))
                            (Functionality T Dx \<and>\<^sub>\<r> Abstract_Domain T D\<^sub>T \<and>\<^sub>\<r> Carrier_Set T D\<^sub>C)
                            True \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..


subsubsection \<open>Configuration\<close>

setup \<open>Context.theory_map (Phi_Type_Algebra.Defining_Phi_Type.add 12 (fn phi => fn thy =>
  let exception Found of term * term
      fun find (X as Const(\<^const_name>\<open>\<phi>Composition\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Fun\<close>, _) $ f) $ T)
            = raise Found (X, Const(\<^const_name>\<open>\<phi>Fun'\<close>, dummyT) $ f $ T)
        | find (A $ B) = (find A; find B)
        | find (Abs (_, _, X)) = find X
        | find _ = ()

      open Pretty
      val _ = List.app (find o Thm.prop_of) (#equations phi)
              handle Found (X,Y) => Phi_Reasoner.warn_pretty thy 0 (fn () =>
                  paragraph (text "We have noticed you are using" @ [brk 1,
                      Context.cases Syntax.pretty_term_global Syntax.pretty_term thy X, brk 1] @
                      text "instead of a more specific \<phi>-type" @ [brk 1,
                      Context.cases Syntax.pretty_term_global Syntax.pretty_term thy Y, str ".", brk 1] @
                      text "We highly recommend the later form which replaces the former totally and\
                           \ have more general automation on separation homomorphism." ))
   in thy
  end))\<close>


section \<open>Structural Connectives\<close>

subsection \<open>List Item \& Empty List\<close>

subsubsection \<open>List Item\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def List_Item :: \<open>('v, 'a) \<phi> \<Rightarrow> ('v list, 'a) \<phi>\<close>
  where \<open>List_Item T \<equiv> (\<lambda>v. [v]) \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functionality
       and Functional_Transformation_Functor
       (*and Trivial_\<Sigma>*)
       and Abstraction_to_Raw
       and Carrier_Set
       and \<phi>Inter.Comm\<^sub>I

text \<open>The domainoid of \<open>List_Item\<close> is derived directly from \<open>%BI_approx_success\<close>\<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' List_Item.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (List_Item ?T) ?P \<close>),
  (@{thm' List_Item.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (List_Item ?T) ?P \<close>),
  (@{thm' List_Item.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set (List_Item ?T) ?P  \<close>),
  (@{thm' List_Item.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (List_Item ?T) ?P \<close>),
  (@{thm' List_Item.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (List_Item ?T) ?eq \<close>),
  (@{thm' List_Item.Transformation_Functor}, \<^pattern_prop>\<open> Transformation_Functor List_Item List_Item ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>a. a) \<close>),
  (@{thm' List_Item.Functional_Transformation_Functor}, \<^pattern_prop>\<open> Functional_Transformation_Functor List_Item List_Item ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>f a. a) (\<lambda>f P. f) \<close>),
  (@{thm' List_Item.\<phi>Sum_Comm\<^sub>E}, \<^pattern_prop>\<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 List_Item List_Item List_Item (+\<^sub>\<phi>) (+\<^sub>\<phi>) ?Ta ?U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' List_Item.\<phi>Inter_Comm\<^sub>I}, \<^pattern_prop>\<open> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 List_Item List_Item List_Item (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) ?Ta ?U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' List_Item.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c,?'c) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @action to (Itself::(?'c,?'c) \<phi>))
                                                        \<Longrightarrow> ?x \<Ztypecolon> List_Item ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c list, ?'c list) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = [x] \<and> ?r ?x x) @action to (Itself::(?'c list, ?'c list) \<phi>)  \<close>),
  (@{thm' List_Item.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> [?c] \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> List_Item ?T \<close>)
]\<close>


lemma \<comment> \<open>A example for how to represent list of multi-elements\<close>
  \<open> v1 \<Turnstile> (x1 \<Ztypecolon> T1)
\<Longrightarrow> v2 \<Turnstile> (x2 \<Ztypecolon> T2)
\<Longrightarrow> [v1,v2] \<Turnstile> ((x1, x2) \<Ztypecolon> (List_Item T1 \<^emph> List_Item T2))\<close>
  by (simp add: times_list_def,
      rule exI[where x=\<open>[v2]\<close>],
      rule exI[where x=\<open>[v1]\<close>],
      simp)


subsubsection \<open>Empty List\<close>

declare [[\<phi>trace_reasoning = 0]]
     
\<phi>type_def Empty_List :: \<open>('v list, unit) \<phi>\<close>
  where \<open>Empty_List = (\<lambda>x. [] \<Ztypecolon> Itself)\<close>
  deriving Basic
       and Functionality
       and Identity_Elements
       and Abstraction_to_Raw

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' Empty_List.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L Empty_List (\<lambda>x. True)  \<close>),
  (@{thm' Empty_List.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain Empty_List (\<lambda>x. True)  \<close>),
  (@{thm' Empty_List.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set Empty_List (\<lambda>x. True) \<close>),
  (@{thm' Empty_List.Functionality}, \<^pattern_prop>\<open> Functionality Empty_List (\<lambda>x. True) \<close>),
  (@{thm' Empty_List.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I Empty_List (\<lambda>x. True) (\<lambda>a. True) \<close>),
  (@{thm' Empty_List.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E Empty_List (\<lambda>x. True) \<close>),
  (@{thm' Empty_List.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv Empty_List (\<lambda>x y. True) \<close>)
]\<close>



subsection \<open>Mapping\<close> (*TODO!*)

declare [[\<phi>trace_reasoning = 1]]

\<phi>type_def \<phi>Mapping :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> ('av \<Rightarrow> 'bv, 'a \<Rightarrow> 'b) \<phi>\<close> (infixr "\<Rrightarrow>" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>f \<Ztypecolon> T \<Rrightarrow> U \<equiv> g \<Ztypecolon> Itself \<s>\<u>\<b>\<j> g. (\<forall>v x. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> g v \<Turnstile> (f x \<Ztypecolon> U))\<close>
  deriving (*TODO!*)

text \<open>Again it is a form requiring satisfaction operator, and derivers are very limited on this.\<close>

lemma [\<phi>inhabitance_rule 1000]:
  \<open> (\<And>x. St x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T)
\<Longrightarrow> (\<And>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> Ct x)
\<Longrightarrow> (\<And>x. Ct x \<Longrightarrow> f x \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> Cu x )
\<Longrightarrow> f \<Ztypecolon> T \<Rrightarrow> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<forall>x. St x \<longrightarrow> Ct x \<and> Cu x) \<close>
  unfolding Inhabited_def Action_Tag_def
  apply clarsimp
  apply blast .


subsection \<open>Point on a Mapping\<close>

subsubsection \<open>By Key\<close>

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 75)
  where \<open>\<phi>MapAt k T = (fun_upd 1 k \<Zcomp>\<^sub>f T)\<close>
  deriving Sep_Functor_1
       and Functionality
       and Abstraction_to_Raw
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm
       and \<phi>Inter.Comm\<^sub>I
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) \<DD>[\<delta>] \<DD>[(\<circ>) \<delta>] Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute \<DD>[(\<circ>) \<delta>] \<DD>[\<delta>] ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

\<phi>adhoc_overloading \<phi>coercion \<open>\<lambda>T. [] \<^bold>\<rightarrow> T\<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>MapAt.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (?k \<^bold>\<rightarrow> ?T) ?P \<close>),
  (@{thm' \<phi>MapAt.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (?k \<^bold>\<rightarrow> ?T) ?P \<close>),
  (@{thm' \<phi>MapAt.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set (?T::?'a1 \<Rightarrow> ?'b1::sep_carrier_1 set) ?P \<Longrightarrow> Carrier_Set (?k \<^bold>\<rightarrow> ?T) ?P \<close>),
  (@{thm' \<phi>MapAt.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (?k \<^bold>\<rightarrow> ?T) ?P \<close>),
  (@{thm' \<phi>MapAt.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (?k \<^bold>\<rightarrow> ?T) ?T\<^sub>D ?T\<^sub>P \<close>),
  (@{thm' \<phi>MapAt.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (?k \<^bold>\<rightarrow> ?T) ?T\<^sub>D \<close>),
  (@{thm' \<phi>MapAt.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (?k \<^bold>\<rightarrow> ?T) ?eq \<close>),
  (@{thm' \<phi>MapAt.Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?k = ?ka \<Longrightarrow> Transformation_Functor ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?ka) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>a. a) \<close>),
  (@{thm' \<phi>MapAt.Functional_Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?k = ?ka \<Longrightarrow> Functional_Transformation_Functor ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?ka) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>f a. a) (\<lambda>f P. f)\<close>),
  (@{thm' \<phi>MapAt.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) (?Ta::?'b \<Rightarrow> ?'d::sep_magma_1 set) ?U UNIV (\<lambda>x. x) \<close>),
  (@{thm' \<phi>MapAt.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) (?Ta::?'b \<Rightarrow> ?'d::sep_magma_1 set) ?U (\<lambda>x. x) \<close>),
  (@{thm' \<phi>MapAt.\<phi>Fun'_Comm\<^sub>E}, \<^pattern_prop>\<open> fun_commute ?f (fun_upd 1 ?k) ?xb (fun_upd 1 ?xa) \<Longrightarrow>
        Tyops_Commute ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?xb) ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?xa) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),

  (@{thm' \<phi>MapAt.\<phi>Fun'_Comm\<^sub>I}, \<^pattern_prop>\<open> fun_commute (fun_upd 1 ?k) ?f (fun_upd 1 ?xa) ?xb \<Longrightarrow>
        Tyops_Commute ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?xa) ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?xb) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),

  (@{thm' \<phi>MapAt.\<phi>ScalarMul_Comm\<^sub>I}, \<^pattern_prop>\<open> fun_commute (fun_upd 1 ?k) (scalar_mult ?f ?s) (fun_upd 1 ?xa) (scalar_mult ?xb ?xc) \<Longrightarrow>
    Tyops_Commute ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?xa) (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xb ?xc) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),

  (@{thm' \<phi>MapAt.\<phi>ScalarMul_Comm\<^sub>E}, \<^pattern_prop>\<open> fun_commute (scalar_mult ?f ?s) (fun_upd 1 ?k) (scalar_mult ?xb ?xc) (fun_upd 1 ?xa) \<Longrightarrow>
    Tyops_Commute (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xb ?xc) ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?xa) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),

  (@{thm' \<phi>MapAt.\<phi>Inter_Comm\<^sub>I}, \<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) ?Ta ?U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),

  (@{thm' \<phi>MapAt.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> 1(?k := ?c) \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?k \<^bold>\<rightarrow> ?T  \<close>),
  (@{thm' \<phi>MapAt.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c::one,?'c) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @action to (Itself::(?'c,?'c) \<phi>))
                                                      \<Longrightarrow> ?x \<Ztypecolon> ?k \<^bold>\<rightarrow> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'a \<Rightarrow> ?'c, ?'a \<Rightarrow> ?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = 1(?k := x) \<and> ?r ?x x) @action to (Itself::(?'a \<Rightarrow> ?'c, ?'a \<Rightarrow> ?'c) \<phi>) \<close>)
]\<close>


subsubsection \<open>By List of Keys\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 75)
  where \<open>\<phi>MapAt_L k T = (\<s>\<c>\<a>\<l>\<a>\<r>[push_map] k \<Zcomp> T)\<close>
  deriving Sep_Functor_1
       and Functionality
       and Semimodule_NonDistr_no0
       and Abstraction_to_Raw
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm
       and \<phi>Inter.Comm\<^sub>I
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute \<DD>[(o) \<delta>] \<DD>[(o) \<delta>] ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) T (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) \<DD>[(o) \<delta>] \<DD>[(o) \<delta>] T (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>MapAt_L.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?P \<close>),
  (@{thm' \<phi>MapAt_L.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?P \<close>),
  (@{thm' \<phi>MapAt_L.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set (?T::?'b \<Rightarrow> (?'a list \<Rightarrow> ?'c::sep_carrier_1) set) ?P \<Longrightarrow> Carrier_Set (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?P  \<close>),
  (@{thm' \<phi>MapAt_L.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?P \<close>),
  (@{thm' \<phi>MapAt_L.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?T\<^sub>D ?T\<^sub>P \<close>),
  (@{thm' \<phi>MapAt_L.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?T\<^sub>D \<close>),
  (@{thm' \<phi>MapAt_L.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?eq \<close>),
  (@{thm' \<phi>MapAt_L.Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?k = ?ka \<Longrightarrow> Transformation_Functor ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?ka) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>a. a)  \<close>),
  (@{thm' \<phi>MapAt_L.Functional_Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?k = ?ka \<Longrightarrow> Functional_Transformation_Functor ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?ka) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>f a. a) (\<lambda>f P. f) \<close>),
  (@{thm' \<phi>MapAt_L.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) (?Ta::?'b \<Rightarrow> (?'a list \<Rightarrow> ?'d::sep_magma_1) set) ?U UNIV (\<lambda>x. x) \<close>),
  (@{thm' \<phi>MapAt_L.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) (?Ta::?'b \<Rightarrow> (?'a list \<Rightarrow> ?'d::sep_magma_1) set) ?U (\<lambda>x. x) \<close>),
  (@{thm' \<phi>MapAt_L.Semimodule_Identity}, \<^pattern_prop>\<open> Semimodule_Identity (\<^bold>\<rightarrow>\<^sub>@) ?T 1 (\<lambda>_. True) (\<lambda>x. x)  \<close>),
  (@{thm' \<phi>MapAt_L.Semimodule_Scalar_Assoc\<^sub>E}, \<^pattern_prop>\<open> Semimodule_Scalar_Assoc\<^sub>E (\<^bold>\<rightarrow>\<^sub>@) (\<^bold>\<rightarrow>\<^sub>@) (\<^bold>\<rightarrow>\<^sub>@) ?T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x)  \<close>),
  (@{thm' \<phi>MapAt_L.Semimodule_Scalar_Assoc\<^sub>I}, \<^pattern_prop>\<open> Semimodule_Scalar_Assoc\<^sub>I (\<^bold>\<rightarrow>\<^sub>@) (\<^bold>\<rightarrow>\<^sub>@) (\<^bold>\<rightarrow>\<^sub>@) ?T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) \<close>),
  (@{thm' \<phi>MapAt_L.\<phi>Fun'_Comm\<^sub>I}, \<^pattern_prop>\<open> fun_commute (scalar_mult (\<tribullet>\<^sub>m) ?k) ?f (scalar_mult (\<tribullet>\<^sub>m) ?xa) ?xb \<Longrightarrow>
        Tyops_Commute ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?xa) ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?xb) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),
  (@{thm' \<phi>MapAt_L.\<phi>Fun'_Comm\<^sub>E}, \<^pattern_prop>\<open> fun_commute ?f (scalar_mult (\<tribullet>\<^sub>m) ?k) ?xb (scalar_mult (\<tribullet>\<^sub>m) ?xa) \<Longrightarrow>
        Tyops_Commute ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?xb) ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?xa) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),
  (@{thm' \<phi>MapAt_L.\<phi>ScalarMul_Comm\<^sub>I}, \<^pattern_prop>\<open> fun_commute (scalar_mult (\<tribullet>\<^sub>m) ?k) (scalar_mult ?f ?s) (scalar_mult (\<tribullet>\<^sub>m) ?xa) (scalar_mult ?xb ?xc) \<Longrightarrow>
        Tyops_Commute ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?xa) (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xb ?xc) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' \<phi>MapAt_L.\<phi>ScalarMul_Comm\<^sub>E}, \<^pattern_prop>\<open> fun_commute (scalar_mult ?f ?s) (scalar_mult (\<tribullet>\<^sub>m) ?k) (scalar_mult ?xb ?xc) (scalar_mult (\<tribullet>\<^sub>m) ?xa) \<Longrightarrow>
        Tyops_Commute (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xb ?xc) ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?xa) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),
  (@{thm' \<phi>MapAt_L.\<phi>Inter_Comm\<^sub>I}, \<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) ?Ta ?U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' \<phi>MapAt_L.Make_Abstraction_from_Raw}, \<^pattern_prop>\<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> scalar_mult (\<tribullet>\<^sub>m) ?k ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?T  \<close>),
  (@{thm' \<phi>MapAt_L.Open_Abstraction_to_Raw}, \<^pattern_prop>\<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'a list \<Rightarrow> ?'c::one, ?'a list \<Rightarrow> ?'c) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @action to (Itself::(?'a list \<Rightarrow> ?'c, ?'a list \<Rightarrow> ?'c) \<phi>))
                                                       \<Longrightarrow> ?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'a list \<Rightarrow> ?'c, ?'a list \<Rightarrow> ?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = ?k \<tribullet>\<^sub>m x \<and> ?r ?x x) @action to (Itself::(?'a list \<Rightarrow> ?'c, ?'a list \<Rightarrow> ?'c) \<phi>)  \<close>)
]\<close>

thm \<phi>MapAt_L.\<Sigma>\<^sub>E
thm \<phi>MapAt_L.\<Sigma>_rewr
thm \<phi>MapAt_L.scalar_one
thm \<phi>MapAt_L.scalar_assoc[simplified times_list_def]

abbreviation \<phi>MapAt_L1 :: \<open>'key \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>#" 75)
  where \<open>\<phi>MapAt_L1 key \<equiv> \<phi>MapAt_L [key]\<close>

abbreviation \<phi>MapAt_Lnil :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>[\<^sub>]" 75)
  where \<open>\<phi>MapAt_Lnil key T \<equiv> \<phi>MapAt_L [key] (\<phi>MapAt [] T)\<close>


subsection \<open>Permission Sharing\<close>

declare [[\<phi>trace_reasoning = 0 ]]

text \<open>TODO: Perhaps we need a class for all homomorphic-morphism-based \<phi>-types.\<close>

\<phi>type_def \<phi>Share :: \<open>rat \<Rightarrow> ('c::share,'a) \<phi> \<Rightarrow> ('c, 'a) \<phi>\<close> (infixr "\<odiv>" 75)
  where \<open>\<phi>Share n T = (\<s>\<c>\<a>\<l>\<a>\<r>[share] n \<Zcomp> T \<phi>\<s>\<u>\<b>\<j> 0 < n)\<close>
  deriving Sep_Functor_1
       and Functionality
       (*and SE_Trim_Empty*)
       and Semimodule_no0
       and Carrier_Set
       and Abstraction_to_Raw
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm
       and \<phi>MapAt.Comm
       and \<phi>MapAt_L.Comm
     (*TODO: and \<phi>Inter.Comm\<^sub>I*)
       and \<open>homo_share \<delta>
        \<Longrightarrow> Tyops_Commute ((\<odiv>) n) ((\<odiv>) n) \<DD>[\<delta>] \<DD>[\<delta>] T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
       and \<open>homo_share \<delta>
        \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>] ((\<odiv>) n) ((\<odiv>) n) T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Share.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<Longrightarrow> Abstract_Domain\<^sub>L ?T ?P) \<Longrightarrow> Abstract_Domain\<^sub>L (?n \<odiv> ?T) (\<lambda>x. 0 < ?n \<and> ?P x)  \<close>),
  (@{thm' \<phi>Share.Abstract_Domain}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<Longrightarrow> Abstract_Domain ?T ?P) \<Longrightarrow> Abstract_Domain (?n \<odiv> ?T) (\<lambda>x. 0 < ?n \<and> ?P x) \<close>),
  (@{thm' \<phi>Share.Carrier_Set}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<Longrightarrow> Carrier_Set (?T::?'a \<Rightarrow> ?'b::share_nun_semimodule set) ?P) \<Longrightarrow> Carrier_Set (?n \<odiv> ?T) (\<lambda>x. 0 < ?n \<longrightarrow> ?P x) \<close>),
  (@{thm' \<phi>Share.Functionality}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<Longrightarrow> Functionality ?T ?P) \<Longrightarrow> Functionality (?n \<odiv> ?T) (\<lambda>x. 0 < ?n \<longrightarrow> ?P x) \<close>),
  (@{thm' \<phi>Share.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<Longrightarrow> Identity_Elements\<^sub>I (?T::?'a \<Rightarrow> ?'b::share_one set) ?T\<^sub>D ?T\<^sub>P) \<Longrightarrow> Identity_Elements\<^sub>I (?n \<odiv> ?T) (\<lambda>x. 0 < ?n \<longrightarrow> ?T\<^sub>D x) (\<lambda>x. 0 < ?n \<and> ?T\<^sub>P x) \<close>),
  (@{thm' \<phi>Share.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E (?T::?'a \<Rightarrow> ?'b::share_one set) ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (?n \<odiv> ?T) (\<lambda>x. 0 < ?n \<and> ?T\<^sub>D x) \<close>),
  (@{thm' \<phi>Share.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (?n \<odiv> ?T) ?eq \<close>),
  (@{thm' \<phi>Share.Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?n = ?na \<Longrightarrow> Transformation_Functor ((\<odiv>) ?n) ((\<odiv>) ?na) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>a. a)  \<close>),
  (@{thm' \<phi>Share.Functional_Transformation_Functor}, \<^pattern_prop>\<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?n = ?na \<Longrightarrow> Functional_Transformation_Functor ((\<odiv>) ?n) ((\<odiv>) ?na) ?T ?U (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>f a. a) (\<lambda>f P. f)  \<close>),
  (@{thm' \<phi>Share.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I ((\<odiv>) ?n) ((\<odiv>) ?n) ((\<odiv>) ?n) (?Ta::?'a \<Rightarrow> ?'c::share_nun_semimodule set) ?U UNIV (\<lambda>x. x) \<close>),
  (@{thm' \<phi>Share.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E ((\<odiv>) ?n) ((\<odiv>) ?n) ((\<odiv>) ?n) (?Ta::?'a \<Rightarrow> ?'c::share_nun_semimodule set) ?U (\<lambda>x. x) \<close>),
  (@{thm' \<phi>Share.Semimodule_Identity}, \<^pattern_prop>\<open> Semimodule_Identity (\<odiv>) ?T 1 (\<lambda>_. True) (\<lambda>x. x)  \<close>),
  (@{thm' \<phi>Share.Semimodule_SDistr_Homo\<^sub>U}, \<^pattern_prop>\<open> Functionality (?T::?'a \<Rightarrow> ?'c::share_nun_semimodule set) ?Dx \<Longrightarrow>
    Abstract_Domain ?T ?D\<^sub>T \<Longrightarrow>
    Carrier_Set ?T ?D\<^sub>C \<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U (\<odiv>) ?T ((<) 0) (\<lambda>s t xy. ?D\<^sub>T xy \<longrightarrow> ?Dx xy \<and> ?D\<^sub>C xy) (\<lambda>_ _ x. (x, x))  \<close>),
  (@{thm' \<phi>Share.Semimodule_SDistr_Homo\<^sub>Z}, \<^pattern_prop>\<open> Functionality (?T::?'a \<Rightarrow> ?'c::share_nun_semimodule set) ?Dx \<Longrightarrow>
    Object_Equiv ?T ?eq \<Longrightarrow>
    Abstract_Domain ?T ?D\<^sub>T \<Longrightarrow>
    Carrier_Set ?T ?D\<^sub>C \<Longrightarrow>
    Semimodule_SDistr_Homo\<^sub>Z (\<odiv>) ?T ((<) 0)
     (\<lambda>s t (x, y). ?D\<^sub>T x \<longrightarrow> ?D\<^sub>T y \<longrightarrow> ?eq x y \<and> ?Dx y \<and> ?D\<^sub>C y \<or> ?eq y x \<and> ?Dx x \<and> ?D\<^sub>C x) (\<lambda>_ _. fst)  \<close>),
  (@{thm' \<phi>Share.Semimodule_Scalar_Assoc\<^sub>E}, \<^pattern_prop>\<open> Semimodule_Scalar_Assoc\<^sub>E (\<odiv>) (\<odiv>) (\<odiv>) ?T ((<) 0) ((<) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) \<close>),
  (@{thm' \<phi>Share.Semimodule_Scalar_Assoc\<^sub>I}, \<^pattern_prop>\<open> Semimodule_Scalar_Assoc\<^sub>I (\<odiv>) (\<odiv>) (\<odiv>) ?T ((<) 0) ((<) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x)  \<close>),
  (@{thm' \<phi>Share.\<phi>Fun'_Comm\<^sub>E}, \<^pattern_prop>\<open>  \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?xa) \<Longrightarrow>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<longrightarrow> fun_commute ?f (scalar_mult (\<odivr>) ?n) ?xb (scalar_mult (\<odivr>) ?xa) \<Longrightarrow>
    Tyops_Commute ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?xb) ((\<odiv>) ?n) ((\<odiv>) ?xa) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' \<phi>Share.\<phi>Fun'_Comm\<^sub>I}, \<^pattern_prop>\<open>  \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?xa) \<Longrightarrow>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<longrightarrow> fun_commute (scalar_mult (\<odivr>) ?n) ?f (scalar_mult (\<odivr>) ?xa) ?xb \<Longrightarrow>
    Tyops_Commute ((\<odiv>) ?n) ((\<odiv>) ?xa) ((\<Zcomp>\<^sub>f) ?f) ((\<Zcomp>\<^sub>f) ?xb) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),
  (@{thm' \<phi>Share.\<phi>MapAt_Comm\<^sub>E}, \<^pattern_prop>\<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?n) \<Longrightarrow>
    Tyops_Commute ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) ((\<odiv>) ?n) ((\<odiv>) ?n) (?Ta::?'a \<Rightarrow> ?'b::share_one set) (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),
  (@{thm' \<phi>Share.\<phi>MapAt_Comm\<^sub>I}, \<^pattern_prop>\<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?n) \<Longrightarrow>
    Tyops_Commute ((\<odiv>) ?n) ((\<odiv>) ?n) ((\<^bold>\<rightarrow>) ?k) ((\<^bold>\<rightarrow>) ?k) (?Ta::?'a \<Rightarrow> ?'b::share_one set) (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' \<phi>Share.\<phi>ScalarMul_Comm\<^sub>E}, \<^pattern_prop>\<open>  \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?xa) \<Longrightarrow>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<longrightarrow> fun_commute (scalar_mult ?f ?s) (scalar_mult (\<odivr>) ?n) (scalar_mult ?xb ?xc) (scalar_mult (\<odivr>) ?xa) \<Longrightarrow>
    Tyops_Commute (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xb ?xc) ((\<odiv>) ?n) ((\<odiv>) ?xa) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))  \<close>),
  (@{thm' \<phi>Share.\<phi>ScalarMul_Comm\<^sub>I}, \<^pattern_prop>\<open>  \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?xa) \<Longrightarrow>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < ?n \<longrightarrow> fun_commute (scalar_mult (\<odivr>) ?n) (scalar_mult ?f ?s) (scalar_mult (\<odivr>) ?xa) (scalar_mult ?xb ?xc) \<Longrightarrow>
    Tyops_Commute ((\<odiv>) ?n) ((\<odiv>) ?xa) (\<phi>ScalarMul ?f ?s) (\<phi>ScalarMul ?xb ?xc) ?Ta (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>),
  (@{thm' \<phi>Share.\<phi>MapAt_L_Comm\<^sub>E}, \<^pattern_prop>\<open>  \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?n)
        \<Longrightarrow> Tyops_Commute ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<odiv>) ?n) ((\<odiv>) ?n) (?Ta::?'a \<Rightarrow> (?'b list \<Rightarrow> ?'c::share_one) set) (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))   \<close>),
  (@{thm' \<phi>Share.\<phi>MapAt_L_Comm\<^sub>I}, \<^pattern_prop>\<open>  \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (0 < ?n \<longrightarrow> 0 < ?n)
        \<Longrightarrow> Tyops_Commute ((\<odiv>) ?n) ((\<odiv>) ?n) ((\<^bold>\<rightarrow>\<^sub>@) ?k) ((\<^bold>\<rightarrow>\<^sub>@) ?k) (?Ta::?'a \<Rightarrow> (?'b list \<Rightarrow> ?'c::share_one) set) (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>)
]\<close>

thm \<phi>Share.\<S>_rewr_ty
thm \<phi>MapAt_L.\<phi>Share.comm_rewr

thm \<phi>Share.\<phi>Inter_Comm\<^sub>E
thm \<phi>Share.\<Sigma>_rewr
thm \<phi>Fun'.\<phi>Fun'.comm_rewr


thm \<phi>Share.\<phi>Sum_Comm\<^sub>E

thm \<phi>Share.Identity_Element\<^sub>I
thm \<phi>Share.unfold_sdistr (*TODO: reduce identical antecedents*)
thm \<phi>Share.\<phi>Prod
thm \<phi>Share.\<phi>Prod_ty
thm \<phi>Share.\<phi>None
thm \<phi>Share.scalar_assoc
thm \<phi>Share.scalar_one
thm \<phi>Share.Semimodule_Scalar_Assoc\<^sub>E
thm \<phi>Share.\<S>\<^sub>E
thm \<phi>Share.\<S>\<^sub>I
thm \<phi>Share.\<phi>subj_ty
thm \<phi>Share.simp_cong

subparagraph \<open>Auxiliary Tag\<close>

(*TODO: rename this to partial which is a syntactic const, \<^term>\<open>partial \<odiv> T\<close>, and translate it during
  the parsing time*)


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

subsubsection \<open>Simplification Rules\<close>

declare \<phi>MapAt.\<phi>Share.comm_rewr[symmetric, assertion_simps]
        \<phi>MapAt_L.\<phi>Share.comm_rewr[symmetric, assertion_simps]
        \<phi>Share.\<phi>Prod[symmetric, assertion_simps]

thm \<phi>Share.\<S>\<^sub>I
thm \<phi>Share.\<S>\<^sub>E

paragraph \<open>Implication \& Action Rules\<close>


(* TODO: Applying commutativity between two Scalars according to certain order, automatically during ToA reasoning

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
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> (n \<odiv> T) \<^emph> (n \<odiv> U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> (T \<^emph> U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .
*)

subsection \<open>Injection from partial map to permissioned partial map\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def To_Share
  where \<open>To_Share T \<equiv> (to_share \<Zcomp>\<^sub>f T)\<close>
  deriving Sep_Functor_1
       and \<open>Separation_Homo\<^sub>E (To_Share :: ('c::discrete_semigroup option,'a) \<phi> \<Rightarrow> ('c share option,'a) \<phi>) To_Share To_Share T U (\<lambda>x. x) \<close>
       and \<open>Separation_Disj\<^sub>\<phi> to_share Dx U T
        \<Longrightarrow> Separation_Homo\<^sub>I (To_Share :: ('c::discrete_semigroup option,'a) \<phi> \<Rightarrow> ('c share option,'a) \<phi>) To_Share To_Share T U Dx (\<lambda>x. x) \<close>
       and Functionality
       and Carrier_Set

subsubsection \<open>Syntax\<close>

abbreviation \<phi>Share_Some ("\<fish_eye> _" [91] 90)
  where \<open>\<phi>Share_Some T \<equiv> To_Share (\<phi>Some T)\<close>

abbreviation \<phi>Share_Some_L ("\<fish_eye>\<^sub>L _" [91] 90)
  where \<open>\<phi>Share_Some_L T \<equiv> [] \<^bold>\<rightarrow> To_Share (\<phi>Some T)\<close>

\<phi>adhoc_overloading \<phi>coercion \<phi>Some \<phi>Share_Some \<phi>Share_Some_L


subsection \<open>Injection into Discrete Algebra\<close>

declare [[\<phi>trace_reasoning = 0]]
  
\<phi>type_def Nosep :: \<open>('c, 'a) \<phi> \<Rightarrow> ('c discrete, 'a) \<phi>\<close>
  where \<open>Nosep T = (discrete \<Zcomp>\<^sub>f T)\<close>
  deriving Basic
       and \<open>Carrier_Set (Nosep T) (\<lambda>_. True)\<close>
       and Functionality 
       and Functional_Transformation_Functor
       and Abstraction_to_Raw

\<phi>adhoc_overloading \<phi>coercion \<open>\<lambda>T. \<black_circle> Nosep T\<close> \<open>\<lambda>T. \<fish_eye> Nosep T\<close> \<open>\<lambda>T. \<fish_eye>\<^sub>L Nosep T\<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' Nosep.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L ?T ?P \<Longrightarrow> Abstract_Domain\<^sub>L (Nosep ?T) ?P  \<close>),
  (@{thm' Nosep.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (Nosep ?T) ?P \<close>),
  (@{thm' Nosep.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set (Nosep ?T) (\<lambda>_. True) \<close>),
  (@{thm' Nosep.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (Nosep ?T) ?P   \<close>),
  (@{thm' Nosep.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (Nosep ?T) ?eq \<close>),
  (@{thm' Nosep.Transformation_Functor}, \<^pattern_prop>\<open> Transformation_Functor Nosep Nosep ?T ?U (\<lambda>a. {a}) (\<lambda>x. UNIV) (\<lambda>g. g) \<close>),
  (@{thm' Nosep.Functional_Transformation_Functor}, \<^pattern_prop>\<open> Functional_Transformation_Functor Nosep Nosep ?T ?U (\<lambda>a. {a}) (\<lambda>x. UNIV) (\<lambda>f P. P) (\<lambda>f P. f) \<close>)
]\<close>

(*TODO: give a configure flag to control this sugar*)
translations
  "\<coercion> T" <= "\<fish_eye> CONST Nosep T"


section \<open>Derivatives\<close>

subsection \<open>From FMQ\<close>

subsubsection \<open>Interval in Length Representation\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>Mul_Quant_LenIv :: \<open> nat len_intvl
                              \<Rightarrow> ('c::sep_algebra, 'x) \<phi>
                              \<Rightarrow> ('c::sep_algebra, 'x list) \<phi>\<close> ("\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi>")
  where \<open>l \<Ztypecolon> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T \<equiv> (\<lambda>i. l ! (i - Len_Intvl.start iv)) \<Ztypecolon> \<big_ast>\<^sup>\<phi> (Len_Intvl.set iv) T \<s>\<u>\<b>\<j> length l = len_intvl.len iv\<close>
  deriving Sep_Functor_1
       and Semimodule_NonAssoc
       and \<open>Abstract_Domain T P
        \<Longrightarrow> Abstract_Domain (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>x. length x = len_intvl.len iv \<and> list_all P x) \<close> \<comment> \<open>simplification is not satisfiable\<close>
       and \<open>Carrier_Set T P
        \<Longrightarrow> Carrier_Set (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (list_all P) \<close>  
       and \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (list_all2 eq)\<close>
       and Transformation_Functor  
           tactic: (auto ; subgoal' for r l xb R \<open>induct l arbitrary: iv iva xb R\<close>)
       and \<open>Functionality T P \<Longrightarrow> Functionality (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (list_all P)\<close>
       and \<open>Identity_Elements\<^sub>I T T\<^sub>D T\<^sub>P
        \<Longrightarrow> Identity_Elements\<^sub>I (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (list_all T\<^sub>D) (\<lambda>x. length x = len_intvl.len iv \<and> (\<forall>xa<len_intvl.len iv. T\<^sub>P (x ! xa))) \<close>
       and \<open>Identity_Elements\<^sub>E T T\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>x. length x = len_intvl.len iv \<and> list_all T\<^sub>D x) \<close>

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' \<phi>Mul_Quant_LenIv.Transformation_Functor}, \<^pattern_prop>\<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?iv = ?iva \<Longrightarrow> Transformation_Functor (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iva) ?T ?Ta set (\<lambda>x. UNIV) list_all2 \<close>),
  (@{thm' \<phi>Mul_Quant_LenIv.Functional_Transformation_Functor}, \<^pattern_prop>\<open>
         \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?iv = ?iva \<Longrightarrow>
         Functional_Transformation_Functor (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iva) ?T ?Ta set (\<lambda>x. UNIV) (\<lambda>f. list_all) (\<lambda>f P. map f) \<close>),
  (@{thm' \<phi>Mul_Quant_LenIv.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) ?Ta ?U {(x, y). length x = length y} zip'  \<close>),
  (@{thm' \<phi>Mul_Quant_LenIv.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?iv) ?Ta ?U unzip'  \<close>),
  (@{thm' \<phi>Mul_Quant_LenIv.Semimodule_Zero}, \<^pattern_prop>\<open> Semimodule_Zero \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?T \<lbrakk>?xa : 0\<rwpar>  \<close>),
  (@{thm' \<phi>Mul_Quant_LenIv.Semimodule_Identity}, \<^pattern_prop>\<open> Semimodule_Identity \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?T \<lbrakk>?xa : 1\<rwpar> (\<lambda>l. length l = 1) hd  \<close>),
  (@{thm' \<phi>Mul_Quant_LenIv.Semimodule_SDistr_Homo\<^sub>U}, \<^pattern_prop>\<open>
        Semimodule_SDistr_Homo\<^sub>U \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?T (\<lambda>_. True) (\<lambda>t s x. len_intvl.len s + len_intvl.len t = length x)
                                                   (\<lambda>t s x. (drop (len_intvl.len s) x, take (len_intvl.len s) x))\<close>),
  (@{thm' \<phi>Mul_Quant_LenIv.Semimodule_SDistr_Homo\<^sub>Z}, \<^pattern_prop>\<open>
        Semimodule_SDistr_Homo\<^sub>Z \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> ?T (\<lambda>_. True) (\<lambda>t s (y, x). len_intvl.len s = length x \<and> len_intvl.len t = length y) (\<lambda>t s (y, x). x @ y) \<close>)
]\<close>


section \<open>Semantics Related\<close> (*TODO: move*)

subsection \<open>Value\<close>

subsubsection \<open>Syntax to fetch the latest n-th Val\<close> (*but definitely this title should be moved somewhere*)

(*where I moved it? the function seems still useful*)

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
(* TODO: move somewhere, it is semantics-related
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
  unfolding Transformation_def \<phi>SemType_def by (simp add: \<phi>expns) blas


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
*)



(* not need any more
subsection \<open>Morphism of Separation Homomorphism\<close>

declare [[\<phi>trace_reasoning = 3]]

\<phi>type_def \<phi>sep_homo :: \<open>('a::sep_magma \<Rightarrow> 'c::sep_magma) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close>
  where \<open>\<phi>sep_homo \<psi> T = (\<phi>Fun \<psi> \<Zcomp> T \<phi>\<s>\<u>\<b>\<j> homo_sep \<psi>)\<close>
  deriving Implication
       (*and Is_Functional
       and Open_Abstraction_to_Raw*)

lemma [\<phi>reason add]:
  \<open> Object_Sep_Homo\<^sub>I (\<phi>sep_homo \<psi>) {(y,x). \<psi> x ## \<psi> y \<longrightarrow> x ## y} \<close>
  unfolding Object_Sep_Homo\<^sub>I_def Transformation_def
  by (clarsimp simp add: homo_sep_def homo_sep_mult_def homo_sep_disj_def)

lemma \<phi>Composition_Separation_Homo\<^sub>I'[\<phi>reason 1200]:
  \<open> Separation_Homo\<^sub>I ((\<Zcomp>) (\<phi>sep_homo \<psi>)) ((\<Zcomp>) (\<phi>sep_homo \<psi>)) ((\<Zcomp>) (\<phi>sep_homo \<psi>))
                     (\<lambda>T U xy. Separation_Disj \<psi> (snd xy \<Ztypecolon> U) (fst xy \<Ztypecolon> T))
                     UNIV (\<lambda>x. x)\<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
            Separation_Disj_def
  by (clarsimp; metis homo_sep_def homo_sep_mult_def)
  


lemma \<phi>sep_homo_Prod:
  \<open> (\<phi>sep_homo \<psi> \<Zcomp> (T \<^emph> U)) = (\<phi>sep_homo \<psi> \<Zcomp> T) \<^emph> (\<phi>sep_homo \<psi> \<Zcomp> U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add:; rule; clarsimp)
  using homo_sep.axioms(1) homo_sep.axioms(2) homo_sep_disj_def homo_sep_mult_def apply blas


  

lemma
  \<open> (x \<Ztypecolon> \<phi>sep_homo_morph \<psi>) * (y \<Ztypecolon> \<phi>sep_homo_morph \<psi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> \<phi>sep_homo_morph \<psi> \<w>\<i>\<t>\<h> x ## y
\<Longrightarrow> x ## y\<close>
  unfolding Transformation_def
  apply (clarsimp simp add: homo_sep_def)

lemma [\<phi>reason add]:
  \<open> Object_Sep_Homo\<^sub>E (\<phi>sep_homo_morph \<psi>) \<close>
  unfolding Object_Sep_Homo\<^sub>E_def Transformation_def
  by (clarsimp simp add: homo_sep_def homo_sep_mult_def homo_sep_disj_def)

term \<open>Object_Equiv (\<phi>sep_homo_morph \<psi>) (\<lambda>x y. \<psi> x = \<psi> y)\<close>

\<phi>type_def \<phi>sep_homo :: \<open>('a::sep_magma \<Rightarrow> 'b::sep_magma) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi>sep_homo \<psi> T = (\<lambda>x. x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T \<s>\<u>\<b>\<j> homo_sep \<psi>)\<close>
  deriving (*Basic
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>sep_homo \<psi> T) eq \<close>
       and \<open>Object_Equiv (\<phi>sep_homo T \<circle>) (\<lambda>_ _. True)\<close>
       and Functional_Transformation_Functor
       and*) Separation_Homo\<^sub>E

thm \<phi>sep_homo.unfold

term \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>sep_homo \<psi> T) eq \<close>
term \<open>Object_Equiv (\<phi>sep_homo T \<circle>) (\<lambda>_ _. True)\<close>

*)


(* not need
subsubsection \<open>Insertion Functor\<close>

declare share_orthogonal_homo_pointwise[\<phi>reason 1200]
        share_orthogonal_homo_to_share[\<phi>reason 1200]

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def \<phi>insertion :: \<open>('a::sep_monoid \<Rightarrow> 'b::sep_monoid) \<Rightarrow> 'a set \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi>insertion \<psi> D T = (\<lambda>x. x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T \<s>\<u>\<b>\<j> sep_orthogonal_monoid \<psi> D)\<close>
  deriving Basic
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>insertion \<psi> D T) eq\<close>
       and Object_Equiv\<^sub>O
       (*and Transformation_Functor*)
       

term \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>insertion \<psi> D T) eq\<close>

abbreviation (in sep_orthogonal_monoid) \<open>\<phi> \<equiv> \<phi>insertion \<psi> D\<close>

lemma (in sep_orthogonal_monoid) [\<phi>expns]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<Turnstile> (x \<Ztypecolon> T))\<close>
  by (simp add: sep_orthogonal_monoid_axioms)

paragraph \<open>Implication\<close>
(*
lemma \<phi>insertion_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp; blast) *)

paragraph \<open>Action\<close>

paragraph \<open>Simplification\<close>
(*
lemma [simp]:
  \<open>(\<phi>insertion \<psi> D (ExTyp T)) = (\<exists>\<phi> c. \<phi>insertion \<psi> D (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi>insertion \<psi> D (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<phi>insertion \<psi> D T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)
*)

(*
lemma \<phi>insertion_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi>insertion \<psi> T) = (x' \<Ztypecolon> \<phi>insertion \<psi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>insertion_simp_cong ("x \<Ztypecolon> \<phi>insertion \<psi> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>insertion_simp_cong} ctxt)
\<close>
*)

lemma \<phi>insertion_Prod:
  \<open> \<phi>Sep_Disj U T
\<Longrightarrow> \<phi>insertion f D (T \<^emph> U) = (\<phi>insertion f D T) \<^emph> (\<phi>insertion f D U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>Sep_Disj_def; rule; clarsimp)
  apply (metis homo_sep_def homo_sep_disj_def homo_sep_mult_def sep_orthogonal_1_def sep_orthogonal_def sep_orthogonal_monoid_def)
  
  



lemma \<phi>insertion_\<phi>None:
  assumes prem: \<open>sep_orthogonal_monoid \<psi> D\<close>
  shows \<open>\<phi>insertion \<psi> D \<circle> = \<circle>\<close>
proof -
  interpret sep_orthogonal_monoid \<psi> using prem .
  show \<open>\<phi> \<circle> = \<circle>\<close>
    by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns sep_orthogonal_monoid_axioms)
qed

(* lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> \<phi>insertion ?\<psi> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P @action (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> \<phi>insertion \<psi> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Transformation_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  using inj_at_1_def share_orthogonal_homo'.axioms(5) by blast *)

lemma \<phi>insertion_MapAt:
  \<open>\<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow> T) = (k \<^bold>\<rightarrow> \<phi>insertion f D T)\<close>
proof (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>MapAt_def
            sep_orthogonal_monoid_pointwise_eq; rule; clarsimp)
  fix x :: 'a and va :: 'd
  assume \<open>sep_orthogonal_monoid f D\<close>
  then interpret sep_orthogonal_monoid f .
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> 1(k := va) = 1(k := v) \<and> (\<exists>va. v = f va \<and> va \<in> (x \<Ztypecolon> T))\<close> by fastforce
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. 1(k := f va) = f \<circ> v \<and> (\<exists>va. v = 1(k := va) \<and> va \<in> (x \<Ztypecolon> T))\<close>
    by (metis \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> 1(k := va) = 1(k := v) \<and> (\<exists>va. v = f va \<and> va \<in> (x \<Ztypecolon> T))\<close> comp_def fun_upd_same)
qed

lemma \<phi>insertion_MapAt_L:
  \<open>\<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow>\<^sub>@ T) = (k \<^bold>\<rightarrow>\<^sub>@ \<phi>insertion ((o) f) (pointwise_set D) T)\<close>
proof (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns
            sep_orthogonal_monoid_pointwise_eq; rule; clarsimp)
  fix x :: 'a and va :: \<open>'b list \<Rightarrow> 'd\<close>
  assume \<open>sep_orthogonal_monoid f D\<close>
  then interpret sep_orthogonal_monoid f .
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> k \<tribullet>\<^sub>m va = k \<tribullet>\<^sub>m v \<and> (\<exists>va. v = f \<circ> va \<and> va \<in> (x \<Ztypecolon> T))\<close>
    using homo_one_axioms push_map_homo by blast
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. k \<tribullet>\<^sub>m (f \<circ> va) = f \<circ> v \<and> (\<exists>va. v = k \<tribullet>\<^sub>m va \<and> va \<in> (x \<Ztypecolon> T))\<close>
    by (metis homo_one_axioms push_map_homo)
qed    


lemma \<phi>insertion_Prod_imply:
  \<open>x \<Ztypecolon> \<phi>insertion f D (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<phi>insertion f D T) \<^emph> (\<phi>insertion f D U)\<close>
  unfolding Transformation_def
  apply (cases x; clarsimp simp add: \<phi>expns)
  by (metis homo_sep_def homo_sep_disj_def homo_sep_mult_def sep_orthogonal.axioms(1) sep_orthogonal_1.axioms sep_orthogonal_monoid.axioms share_orthogonal_homo.axioms(1)


thm share_orthogonal_homo.axioms(1)
*)





text \<open>re-enable when needed. DO NOT REMOVE,\<close>

(* TODO: re-enable when needed. DO NOT REMOVE, are still useful but I don't want to repair them right now.
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
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action as Z\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Agreement Z)\<close>
  unfolding Action_Tag_def using Agreement_cast .
*)


(* TODO: re-enable when needed. DO NOT REMOVE, can be useful perhaps but I don't want to repair them right now.
section \<open>Specifc Structures\<close>

subsection \<open>Potentially Uninitialized Structure\<close>

datatype 'V uninit = initialized 'V | uninitialized

instantiation uninit :: (discrete_semigroup) discrete_semigroup begin
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
*)

section \<open>Misc.\<close>

subsection \<open>Forward Simulation\<close> (*TODO*)

definition \<phi>F_simulation
    :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> (('av \<times> 'bv) set, ('a \<times> 'b) set) \<phi>\<close> (infixr "\<Rrightarrow>\<^sub>r" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow>\<^sub>r U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>u y. (v,u) \<in> g \<and> (x,y) \<in> f \<and> u \<in> (y \<Ztypecolon> U)) })\<close>
 

locale test =
  fixes param :: nat
begin

\<phi>type_def AA
  where \<open>(0 \<Ztypecolon> AA) = (param \<Ztypecolon> Itself)\<close>
      | \<open>(Suc n \<Ztypecolon> AA) = (n \<Ztypecolon> AA)\<close>
 
\<phi>type_def XX
  where \<open>x \<Ztypecolon> XX \<equiv> (x + param \<Ztypecolon> Itself)\<close>
  deriving Basic

term XX

end
 
interpretation x1: test 1 .
interpretation x2: test 2 .

thm x1.XX.Object_Equiv
thm x2.XX.Object_Equiv


end
