theory Phi_Types_Test
  imports Phi_Types
begin

subsection \<open>Testing \<phi>-Types\<close>
 
\<phi>type_def List  :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List T) = (x \<Ztypecolon> T\<heavy_comma> l \<Ztypecolon> List T)\<close>
      deriving Sep_Functor_1
           and Functionality
           and \<open> homo_one \<delta>
              \<Longrightarrow> closed_homo_sep \<delta>
              \<Longrightarrow> Tyops_Commute List List \<DD>[\<delta>] \<DD>[\<delta>] Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
           and \<open>homo_one \<delta>
              \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>] List List Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>



ML \<open>assert_derived_properties \<^theory> [
  (@{thm' List.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (List ?T) (list_all ?P) \<close>),
  (@{thm' List.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set (List ?T) (list_all ?P)  \<close>),
  (@{thm' List.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (List ?T) (list_all ?P) \<close>),
  (@{thm' List.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (List ?T) (list_all ?T\<^sub>D) (list_all ?T\<^sub>P) \<close>),
  (@{thm' List.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (List ?T) (list_all ?T\<^sub>D) \<close>),
  (@{thm' List.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (List ?T) (list_all2 ?eq) \<close>),
  (@{thm' List.Transformation_Functor}, \<^pattern_prop>\<open> Transformation_Functor List List ?T ?U set (\<lambda>_. UNIV) list_all2  \<close>),
  (@{thm' List.Functional_Transformation_Functor}, \<^pattern_prop>\<open> Functional_Transformation_Functor List List ?T ?U set (\<lambda>_. UNIV) (\<lambda>f. list_all) (\<lambda>f P. map f) \<close>),
  (@{thm' List.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I List List List ?Ta ?U {(x, y). length x = length y} (case_prod zip) \<close>),
  (@{thm' List.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E List List List ?Ta ?U list.unzip \<close>)
]\<close>

(*lemma [simp]:
  \<open>list.zip (apfst (map g) (unzip' x)) = map (apfst g) x\<close>
  unfolding zip'_def unzip'_def
  by (simp add: zip_eq_conv)*)

thm List.ToA_mapper_sep

thm List.ToA_mapper_sep[where C\<^sub>R=True and C\<^sub>W=True, simplified]

term map2




(* TODO!
context
  fixes T :: \<open>(fiction,'a) \<phi>\<close>
begin

\<phi>type_def List\<^sub>C  :: \<open>(fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List\<^sub>C) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List\<^sub>C) = (x \<Ztypecolon> T\<heavy_comma> l \<Ztypecolon> List\<^sub>C)\<close>
      deriving Sep_Functor_1
           and Functionality
           and \<open> homo_one \<delta>
              \<Longrightarrow> closed_homo_sep \<delta>
              \<Longrightarrow> Tyops_Commute List\<^sub>C List\<^sub>C \<DD>[\<delta>] \<DD>[\<delta>] Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
           and \<open>homo_one \<delta>
              \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>] List\<^sub>C List\<^sub>C Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>


end
*)














     
\<phi>type_def List\<^sub>S  :: \<open>nat \<Rightarrow> (fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>(l \<Ztypecolon> List\<^sub>S 0 T) = (Void \<s>\<u>\<b>\<j> l = [])\<close>
      | \<open>(l \<Ztypecolon> List\<^sub>S (Suc n) T) = (h \<Ztypecolon> T\<heavy_comma> l' \<Ztypecolon> List\<^sub>S n T \<s>\<u>\<b>\<j> h l'. l = h # l')\<close>
  deriving \<open>Identity_Elements\<^sub>E T T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (List\<^sub>S n T) (\<lambda>l. list_all T\<^sub>D l \<and> length l = n)\<close>
       and Identity_Elements\<^sub>I


term \<open>Identity_Elements\<^sub>E T T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (List\<^sub>S n T) (\<lambda>l. list_all T\<^sub>D l \<and> length l = n)\<close>

   
\<phi>type_def List\<^sub>S'  :: \<open>nat \<Rightarrow> (fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List\<^sub>S' n T) = (Void \<s>\<u>\<b>\<j> n = 0)\<close>
      | \<open>(x # l \<Ztypecolon> List\<^sub>S' n T) = (x \<Ztypecolon> T\<heavy_comma> l \<Ztypecolon> List\<^sub>S' (n - 1) T \<s>\<u>\<b>\<j> n = length l + 1)\<close>
      deriving \<open>Identity_Elements\<^sub>I T T\<^sub>D T\<^sub>P
            \<Longrightarrow> Identity_Elements\<^sub>I (List\<^sub>S' n T) (list_all T\<^sub>D) (\<lambda>x. list_all T\<^sub>P x \<and> n = length x)\<close> (*TODO: derive such n = length x*)
           and \<open>Identity_Elements\<^sub>E T T\<^sub>D
            \<Longrightarrow> Identity_Elements\<^sub>E (List\<^sub>S' n T) (\<lambda>x. list_all T\<^sub>D x \<and> n = length x)\<close> 
 (*\<open>Identity_Element\<^sub>I ([] \<Ztypecolon> List\<^sub>S n T) (n = 0)\<close>
           and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> n = 0 \<Longrightarrow> Identity_Element\<^sub>E ([] \<Ztypecolon> List\<^sub>S n T)\<close>
           and \<open>Identity_Element\<^sub>I (l \<Ztypecolon> List\<^sub>S n \<circle>) (n = length l)\<close>
           and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> n = length l \<Longrightarrow> Identity_Element\<^sub>E (l \<Ztypecolon> List\<^sub>S n \<circle>)\<close>
           and*)
           and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (List\<^sub>S' n T) (\<lambda>l. list_all P l \<and> n = length l) \<close>
           (*and Object_Equiv\<^sub>O*)
          (*and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (List\<^sub>S n T) (list_all2 eq)\<close>*)


(*TODO: FIX ME!

  declare if_split_eq1[simp]
  deriving \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 List List List (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>x. Ball (set x) isl \<or> (\<forall>b\<in>set x. \<not> isl b))
 (embedded_func (\<lambda>x. if Ball (set x) isl then Inl (map projl x) else Inr (map projr x)) (list_all (\<lambda>_. True)))\<close>
  (*For some reason, the deriving fails here due to loosing certain conditions during the reasoning I believe,
    but I cannot figure it out now. I will lieave this and go back when I have time.*)
*)



thm List.\<phi>Sum\<^sub>E

term \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 List List List (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>x. Ball (set x) isl \<or> (\<forall>b\<in>set x. \<not> isl b))
 (embedded_func (\<lambda>x. if Ball (set x) isl then Inl (map projl x) else Inr (map projr x)) (list_all (\<lambda>_. True)))\<close>

declare List.\<Sigma>\<^sub>E[\<phi>reason add]
        List.\<Sigma>\<^sub>I[where c=\<open>\<lambda>_. c\<close> for c, \<phi>reason add]

lemma List_\<phi>Dependent_Sum_rewr:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a\<in>set x. fst a = c)
\<Longrightarrow> (x \<Ztypecolon> List (\<Sigma> T)) = ((c, map snd x) \<Ztypecolon> \<Sigma> p. List (T p)) \<close>
  by (rule List.\<phi>Dependent_Sum.rewr;
      simp add: Premise_def;
      metis comp_apply map_idI prod.collapse)

lemmas \<phi>Dependent_Sum_List_rewr = \<phi>Dependent_Sum.List.rewr[where x=\<open>(c,x)\<close> and c=c for c x, simplified]

thm List.\<phi>Dependent_Sum.rewr
thm \<phi>Dependent_Sum.List.rewr


thm List.\<Sigma>\<^sub>I
thm List.\<Sigma>\<^sub>E

thm List.functional_transformation


\<phi>type_def List3 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List3 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List3 T) = (x \<Ztypecolon> List T\<heavy_comma> l \<Ztypecolon> List3 T)\<close>
  deriving Sep_Functor_1
       and Functionality
       (*and SE_Trim_Empty*)

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' List3.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain ?T ?P \<Longrightarrow> Abstract_Domain (List3 ?T) (list_all (list_all ?P)) \<close>),
  (@{thm' List3.Carrier_Set}, \<^pattern_prop>\<open> Carrier_Set ?T ?P \<Longrightarrow> Carrier_Set (List3 ?T) (list_all (list_all ?P)) \<close>),
  (@{thm' List3.Functionality}, \<^pattern_prop>\<open> Functionality ?T ?P \<Longrightarrow> Functionality (List3 ?T) (list_all (list_all ?P)) \<close>),
  (@{thm' List3.Identity_Element\<^sub>I}, \<^pattern_prop>\<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (List3 ?T) (list_all (list_all ?T\<^sub>D)) (list_all (list_all ?T\<^sub>P)) \<close>),
  (@{thm' List3.Identity_Element\<^sub>E}, \<^pattern_prop>\<open> Identity_Elements\<^sub>E ?T ?T\<^sub>D \<Longrightarrow> Identity_Elements\<^sub>E (List3 ?T) (list_all (list_all ?T\<^sub>D)) \<close>),
  (@{thm' List3.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv ?T ?eq \<Longrightarrow> Object_Equiv (List3 ?T) (list_all2 (list_all2 ?eq)) \<close>),
  (@{thm' List3.Transformation_Functor}, \<^pattern_prop>\<open> Transformation_Functor List3 List3 ?T ?U (\<lambda>a. Set.bind (set a) set) (\<lambda>_. UNIV) (\<lambda>a. list_all2 (list_all2 a)) \<close>),
  (@{thm' List3.Functional_Transformation_Functor}, \<^pattern_prop>\<open> Functional_Transformation_Functor List3 List3 ?T ?U (\<lambda>a. Set.bind (set a) set) (\<lambda>_. UNIV) (\<lambda>f a. list_all (list_all a)) (\<lambda>f P. map (map f)) \<close>),
  (@{thm' List3.Separation_Homo\<^sub>I}, \<^pattern_prop>\<open> Separation_Homo\<^sub>I List3 List3 List3 ?Ta ?U {(x, y). list_all2 (\<lambda>x y. length x = length y) x y} (\<lambda>x. map (case_prod zip) (case_prod zip x)) \<close>),
  (@{thm' List3.Separation_Homo\<^sub>E}, \<^pattern_prop>\<open> Separation_Homo\<^sub>E List3 List3 List3 ?Ta ?U (\<lambda>x. (map (map fst) x, map (map snd) x)) \<close>)
]\<close>

(* BOSS:
\<phi>type_def List2 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List2 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List2 T) = (prod (\<lambda>x. x \<Ztypecolon> T) (set x)\<heavy_comma> l \<Ztypecolon> List2 T)\<close>
*)
 
       
\<phi>type_def rounded_Nat :: \<open>nat \<Rightarrow> (nat,nat) \<phi>\<close>
  where \<open>(x \<Ztypecolon> rounded_Nat m) = (x mod m \<Ztypecolon> Itself)\<close>
  deriving Basic
       and Make_Abstraction_from_Raw
       and Functionality

ML \<open>assert_derived_properties \<^theory> [
  (@{thm' rounded_Nat.Abstract_Domain\<^sub>L}, \<^pattern_prop>\<open> Abstract_Domain\<^sub>L (rounded_Nat ?m) (\<lambda>x. True) \<close>),
  (@{thm' rounded_Nat.Abstract_Domain}, \<^pattern_prop>\<open> Abstract_Domain (rounded_Nat ?m) (\<lambda>x. True) \<close>),
  (@{thm' rounded_Nat.Functionality}, \<^pattern_prop>\<open> Functionality (rounded_Nat ?m) (\<lambda>x. True) \<close>),
  (@{thm' rounded_Nat.Object_Equiv}, \<^pattern_prop>\<open> Object_Equiv (rounded_Nat ?m) (\<lambda>x y. x mod ?m = y mod ?m) \<close>)
]\<close>

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

subsection \<open>Testing Transformations\<close>

(*
lemma
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> S
\<Longrightarrow> (i, f i) \<Ztypecolon> \<big_ast>\<^sub>0[i\<in>S] (\<Sigma> j. T j) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((i, f i) \<Ztypecolon> \<big_ast>\<^sub>0[i\<in>S - {i}] (\<Sigma> T)) * (f i \<Ztypecolon> T i) \<close>
  \<medium_left_bracket> \<medium_right_bracket> .
*)

lemma
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> S
\<Longrightarrow> f i \<Ztypecolon> \<big_ast>[i\<in>S] (T i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f i \<Ztypecolon> T i) * (f i \<Ztypecolon> \<big_ast>[i\<in>S - {i}] (T i)) \<close>
  \<medium_left_bracket> \<medium_right_bracket> .

lemma
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> S \<and> j \<in> S \<and> i \<noteq> j
\<Longrightarrow> f i \<Ztypecolon> \<big_ast>[i\<in>S] (T i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f j \<Ztypecolon> T j) * (f i \<Ztypecolon> T i) * (f i \<Ztypecolon> \<big_ast>[i\<in>S - {j} - {i}] (T i)) \<close>
  \<medium_left_bracket> \<medium_right_bracket> .

lemma
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> S \<and> j \<in> S \<and> k \<in> S \<and> i \<noteq> j \<and> i \<noteq> k \<and> j \<noteq> k
\<Longrightarrow> f i \<Ztypecolon> \<big_ast>[i\<in>S] (T i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f k \<Ztypecolon> T k) * (f j \<Ztypecolon> T j) * (f i \<Ztypecolon> T i) * (f i \<Ztypecolon> \<big_ast>[i\<in>S - {k} - {j} - {i}] (T i)) \<close>
  \<medium_left_bracket> \<medium_right_bracket> .

end