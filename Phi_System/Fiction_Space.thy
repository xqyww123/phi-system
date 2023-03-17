theory Fiction_Space
  imports "Phi_Semantics_Framework.Phi_Semantics_Framework"
begin

unspecified_type FIC \<comment> \<open>Deep representation of fictions\<close>
type_synonym fiction_kind = \<open>(FIC, resource) interp\<close>
type_synonym fiction = \<open>fiction_kind \<Rightarrow> FIC\<close>
type_synonym assn = \<open>fiction set\<close>

debt_axiomatization FIC_sort: \<open>OFCLASS(FIC, sep_algebra_class)\<close>
instance FIC :: sep_algebra using FIC_sort .

definition INTERP :: \<open>(fiction, resource) interp\<close>
  where "INTERP = \<F>_fun' id"



definition "Fic_Space (f::fiction) \<longleftrightarrow> finite (dom1 f)"

text \<open>Predicate \<open>Fic_Space\<close> characterizes instances of fictional spaces
      --- the number of fiction kinds must be finite.
      @{thm dom1_def}.
      Recall unit \<open>1\<close> represents empty and none resource. In the case of \<open>\<alpha> option\<close>,
      \<open>1 \<triangleq> None\<close>.\<close>

lemma Fic_Space_Un:
  \<open>a ## b \<Longrightarrow> Fic_Space (a*b) \<longleftrightarrow> Fic_Space a \<and> Fic_Space b\<close>
  unfolding Fic_Space_def by (simp add: dom1_sep_mult_disjoint)

lemma Fic_Space_1[simp]: \<open>Fic_Space 1\<close>
  unfolding Fic_Space_def by simp



class fiction_kind = sep_algebra +
  fixes FIC_inj :: \<open>'a::sep_algebra \<Rightarrow> FIC\<close>
    and FIC_prj :: \<open>FIC \<Rightarrow> 'a\<close>
  assumes \<open>sep_inj_proj FIC_inj FIC_prj\<close>
begin

sublocale FK: sep_inj_proj FIC_inj FIC_prj
  using fiction_kind_axioms[unfolded class.fiction_kind_def class.fiction_kind_axioms_def] by blast

end

term FIC_inj
thm FK.inject_inj














term inject

hide_const (open) inject project

interpretation xx: resource_kind_algebra name fiction_kind.inject fiction_kind.project


end