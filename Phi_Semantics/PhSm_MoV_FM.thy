theory PhSm_MoV_FM
  imports PhSem_MoV PhSm_V_FMap
begin

section \<open>Semantics\<close>

term AgIdx_N
term fmlookup

debt_axiomatization
      Map_of_Val_fm: \<open>Map_of_Val (\<m>\<a>\<p>_rep vs) =
            (\<lambda>path. case path
                      of AgIdx_V k # path' \<Rightarrow>
                          (case fmlookup vs k of Some v \<Rightarrow> Map_of_Val v path'
                                               | None \<Rightarrow> 1)
                       | _ \<Rightarrow> 1)\<close>

\<phi>type_def ValIdx :: \<open>(VAL,'x) \<phi> \<Rightarrow> (aggregate_index, 'x) \<phi>\<close>
  where \<open>ValIdx T \<equiv> AgIdx_V \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and Transformation_Functor
       and Functional_Transformation_Functor

abbreviation BC_Map :: \<open>(mem_fic,'x) \<phi> \<Rightarrow> (mem_fic, 'a list) \<phi>\<close>

term 1
term fmadd
term fun_upd
(*
\<phi>type_def \<phi>MapTree :: \<open>'x set \<Rightarrow> ('k,'x) \<phi> \<Rightarrow> ('k list \<Rightarrow> 'v::one,'y) \<phi> \<Rightarrow> ('k list \<Rightarrow> 'v, 'x \<rightharpoonup> 'y) \<phi>\<close>
  where \<open>f \<Ztypecolon> \<phi>MapTree D K V \<equiv> g \<Ztypecolon> Itself \<s>\<u>\<b>\<j> g.
                dom f \<subseteq> D \<and>
                (\<forall>k. k \<in> dom f \<longrightarrow> pull_map [concretize K k] g \<Turnstile> (the (f k) \<Ztypecolon> V)) \<close>
*)















lemma
  \<open>  \<close>



end
