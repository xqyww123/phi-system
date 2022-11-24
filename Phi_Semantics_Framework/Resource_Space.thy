text \<open>The idea of the locale-based modular semantics framework is using Virtual Datatype~\cite{VDT}
to formalize types and values modularly and using an improved Statespace~\cite{Statespace} to
formalize resources.\<close>

section \<open>Framework for Modular Formalization of Resources \& Fictional Resources\<close>

text \<open>Algebras used in the formalization are given in~\cite{Algebras}.\<close>

theory Resource_Space
  imports "Phi-Algebras.Algebras"
    "Virtual-Datatype.Virtual_Datatype"
  keywords "resource_space" :: thy_defn
    and "fiction_space" :: thy_defn
begin

subsubsection \<open>Syntax Patch\<close>

text \<open>
The section presents the improved Statespace, \<^emph>\<open>resource space\<close>, which is specialized for
  resource models in separation algebra.
In addition, the section also presents a similar construct, \<^emph>\<open>fiction space\<close>,
  for formalize modularly fictions used in fictional separation (i.e., Fictional
  Separation Logic~\cite{FSL}).\<close>

syntax
  "_entry_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"     ("(2_ #=/ _)")
  "_fine_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"  ("_/'((_)')\<^sub>?" [1000, 0] 900)

translations
  "f(x#=y)" => "f(CONST Field.name x := CONST Field.inject x y)"

subsection \<open>Resource Space\<close>

text \<open>The section gives a locale-based approach for modelling modularly compound resource states
  that combine different kinds of resources modelled by different types. 
It is in essence a modified Statespace ~\cite{Statespace} with the sort constraint of \<open>sep_algebra\<close>.

Different kinds of resources can use different types for modelling, and the compound is represented
by a uniform deep representation, a finite partial map of type
  \<^typ>\<open>'NAME \<Rightarrow> ('REP::sep_algebra)\<close>
where \<open>'NAME\<close> is the type of the names of resource kinds that identify each resource kind;
type \<open>'REP\<close> is the deep representation of states of resources.

We reuse \<^typ>\<open>('NAME, 'REP::sep_algebra, 'T::sep_algebra) Virtual_Datatype.Field\<close>
to represent resource kinds.
A resource kind is a triple of \<open>name::'NAME\<close> and \<open>project :: 'REP \<Rightarrow> 'T, inject :: 'T \<Rightarrow> 'REP\<close> between
  the deep representation \<open>'REP\<close> of the states and the model \<open>'T\<close> of this kind of resource.

The model \<open>'T\<close> is required to be a separation algebra, albeit
it does not require the physical resource to be separable because any structure can be
  lifted to a a discrete separable because by introducing a unit element standing for
 none resource or no specification.
\<close>


locale resource_kind =
  inj: homo_sep_mult \<open>Field.inject K\<close> + prj: homo_sep_mult \<open>Field.project K\<close> +
  inj_disj: homo_sep_disj \<open>Field.inject K\<close> + prj_disj: homo_sep_disj \<open>Field.project K\<close>
  for K :: "('NAME, 'REP::sep_algebra, 'T::sep_algebra) Virtual_Datatype.Field"
+ assumes proj_inj[simp]: "Field.project K (Field.inject K x) = x"
    and   mult_in_dom:    \<open>a ## b \<Longrightarrow>
              a * b = Field.inject K c \<longleftrightarrow>
                 (\<exists>a' b'. a = Field.inject K a' \<and> b = Field.inject K b' \<and> a' * b' = c)\<close>
begin

subsubsection \<open>Methods and Sugars of a Resource Kind\<close>

abbreviation "name \<equiv> Field.name K"
abbreviation "inject \<equiv> Field.inject K"
abbreviation "project \<equiv> Field.project K"

abbreviation "clean r \<equiv> r(name := 1)"
  \<comment> \<open>\<open>clean r\<close> removes all resources of kind \<open>K\<close> from the compound resource \<open>r\<close>.
      \<open>1\<close> is the unit element of the separation algebra which represents empty resource or
      none specification.\<close>

abbreviation "get r \<equiv> project (r name)"
  \<comment> \<open>\<open>get r\<close> retrieves the model of resource kind \<open>K\<close> from the compound resource \<open>r\<close>\<close>

abbreviation "updt g r \<equiv> r(name := inject (g (get r)))"
  \<comment> \<open>\<open>updt g r\<close> updates the model of resource kind \<open>k\<close> by using function \<open>g\<close>\<close>

abbreviation "mk x \<equiv> 1(name := inject x)"
  \<comment> \<open>\<open>mk x\<close> makes a compound resource that only has the resource modelled by \<open>x\<close> of kind \<open>K\<close>\<close>

subsubsection \<open>Lemmas for Automation and Analysis\<close>

lemma sep_disj_mk[simp]:
  \<open>mk x ## mk y \<longleftrightarrow> x ## y\<close>
  by (metis fun_sep_disj_1_fupdt(1) inj_disj.sep_disj_homo prj_disj.sep_disj_homo proj_inj)

lemma sep_disj_inject[simp]:
  \<open>inject x ## inject y \<longleftrightarrow> x ## y\<close>
  using sep_disj_mk by force

lemma sep_disj_mk_name[simp]:
  \<open>r ## mk x \<Longrightarrow> r name ## inject x\<close>
  by (metis fun_upd_same sep_disj_fun)

lemma sep_disj_get_name_eq[simp]:
  \<open>get r ## x \<longleftrightarrow> r ## mk x\<close>
  by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv prj_disj.sep_disj_homo proj_inj)

lemma inject_inj[simp]:
  \<open>inject a = inject b \<longleftrightarrow> a = b\<close>
  by (metis proj_inj)

lemma get_homo_mult:
  \<open>a ## b \<Longrightarrow> get (a * b) = get a * get b\<close>
  by (simp add: prj.homo_mult times_fun)

lemma mk_homo_one[simp]: \<open>mk x = 1 \<longleftrightarrow> x = 1\<close>
  by (metis fun_1upd1 fun_upd_eqD inj.homo_one proj_inj)

lemma mk_homo_mult: \<open>a ## b \<Longrightarrow> mk (a * b) = mk a * mk b\<close>
  by (simp add: fun_1upd_homo inj.homo_mult)

lemma mk_inj[simp]: \<open>mk a = mk b \<longleftrightarrow> a = b\<close>
  unfolding fun_eq_iff by simp

lemma inj_homo_one[simp]: \<open>inject x = 1 \<longleftrightarrow> x = 1\<close>
  by (metis inj.homo_one proj_inj)

lemmas proj_homo_one  = prj.homo_one
lemmas proj_homo_mult = prj.homo_mult
lemmas inj_homo_mult = inj.homo_mult

lemmas split = fun_split_1[where ?k = name and ?'a = 'NAME and ?'b = 'REP]

lemma mult_strip_inject_011: \<open>
  NO_MATCH (inject a'') a'
\<Longrightarrow> a' ## inject b
\<Longrightarrow> a' * inject b = inject c \<longleftrightarrow> (\<exists>a. a' = inject a \<and> a * b = c \<and> a ## b)\<close>
  \<comment> \<open>split the deep representation of the kind \<open>K\<close>.
      This lemma is useful in fictional separation especially view shifts.\<close>
  using mult_in_dom by force

lemma times_fun_upd:
  \<open>(R * mk x)(name := inject y) = (clean R * mk y)\<close>
  unfolding times_fun_def fun_upd_def fun_eq_iff by simp

lemma sep_disj_clean[simp]:
  \<open>clean r ## mk any\<close>
  by simp

end

ML_file_debug \<open>Resource_Space.ML\<close>

subsection \<open>Fiction Space\<close>

text \<open>The section presents a modular implementation of fictional separation~\cite{FSL}, using
fictional interpretations given in~\cite{Algebras}.
Readers should read \cite{FSL,Algebras} first before beginning this section.

Akin to resource space, fiction space is a locale-based approach that combines fictions on
different models. Specifically, parameterized by resource type \<open>'RES\<close> (which can be typically
the deep representation \<open>'NAME \<Rightarrow> 'REP\<close> of a resource space discussed above),
a fiction space is a resource space \<open>'FNAME \<Rightarrow> 'FREP\<close> at fictional level, where every kind of
fictional resource \<open>(i::'FNAME, inj\<^sub>i :: 'T\<^sub>i \<Rightarrow> 'FREP, prj\<^sub>i :: 'FREP \<Rightarrow> 'T\<^sub>i)\<close>
is equipped with an interpretation \<open>I\<^sub>i :: 'T\<^sub>i \<Rightarrow> 'RES set\<close> that interprets fictional resources to
concrete resources. This fictional resource is named fiction simply.

Fiction space is therefore a collection of interpretations \<open>{I\<^sub>i}\<close> from their own
fiction models \<open>'T\<^sub>i\<close> to resources \<open>'RES\<close>.
The fiction space then converts this collection of fictions and interpretations to
a union fiction of type \<open>'FNAME \<Rightarrow> 'FREP\<close> and the interpretation from the fiction \<open>'FNAME \<Rightarrow> 'FREP\<close>
to resources \<open>'RES\<close>.

Recalling resource space, \<open>'FNAME\<close> is a type of names that identify each interpretation;
\<open>'FREP\<close> is a representation type in which each fiction \<open>'T\<^sub>i\<close> can be embedded, viz.,
every fiction \<open>'T\<^sub>i\<close> for each \<open>i\<close> is injective to \<open>'FREP\<close>.
By the \<open>prj\<^sub>i\<close> each interpretation \<open>I\<^sub>i\<close> is convertible to representational interpretation
\<open>I'\<^sub>i \<triangleq> I\<^sub>i \<circ> prj\<^sub>i\<close> of type \<open>'FREP \<Rightarrow> 'RES set\<close>, which interprets the representation of fiction \<open>'T\<^sub>i\<close>
to the concrete resources.
The union interpretation is then the finite product of all representational interpretation \<open>I'\<^sub>i\<close>
\[ \<open>INTERP \<triangleq> \<lambda>f. \<Pi>i. I'\<^sub>i(f i)\<close> \]
where lambda variable \<open>f::'FNAME \<Rightarrow> 'FREP\<close> denotes the fictional resource to be interpreted,
and \<open>f i\<close> gets the representation of fictional resource \<open>i\<close>.
\<close>

locale fictional_space =
  fixes INTERPRET :: "'FNAME \<Rightarrow> ('FREP::sep_algebra,'RES::sep_algebra) interp"
    \<comment> \<open>\<^term>\<open>INTERPRET i\<close> gives the interpretation of fiction kind \<open>i\<close>, i.e., \<open>I\<^sub>i\<close> above.\<close>
begin

definition "INTERP = \<F>_fun' INTERPRET"

end

definition "Fic_Space (f::'a\<Rightarrow>'b::positive_sep_magma_1) \<longleftrightarrow> finite (dom1 f)"

text \<open>Predicate \<open>Fic_Space\<close> characterizes instances of fictional spaces
      --- the number of fiction kinds must be finite.
      @{thm dom1_def}.
      Recall unit \<open>1\<close> represents empty and none resource. In the case of \<open>\<alpha> option\<close>,
      \<open>1 \<triangleq> None\<close>.\<close>

lemma Fic_Space_Un[simp]:
  \<open>a ## b \<Longrightarrow> Fic_Space (a*b) \<longleftrightarrow> Fic_Space a \<and> Fic_Space b\<close>
  unfolding Fic_Space_def by (simp add: dom1_sep_mult_disjoint)

lemma Fic_Space_1[simp]: \<open>Fic_Space 1\<close>
  unfolding Fic_Space_def by simp


locale fictional_project_inject =
  fictional_space INTERPRET + resource_kind FK +
  inj: homo_sep_mult \<open>Field.inject FK\<close> + prj: homo_sep_mult \<open>Field.project FK\<close>
  for INTERPRET :: "'FNAME \<Rightarrow> ('FREP::sep_algebra,'RES::sep_algebra) interp"
  and FK :: "('FNAME,'FREP,'T::sep_algebra) Virtual_Datatype.Field"
+ fixes I :: "('T,'RES) interp"
  assumes proj_inj[simp]: "Field.project FK (Field.inject FK x) = x"
    and interpret_reduct[simp]: "\<I> (INTERPRET (Field.name FK)) = \<I> I o Field.project FK"
begin

lemmas inj_homo_mult[simp] = inj.homo_mult[symmetric]
lemmas inj_homo_one = inj.homo_one
lemmas prj_homo_mult[simp] = prj.homo_mult
lemmas prj_homo_one = prj.homo_one


lemma inject_assoc_homo[simp]:
  "R ## inject x \<and> R * inject x ## inject y
\<Longrightarrow> R * inject x * inject y = R * inject (x * y)"
  by (metis mult_in_dom sep_disj_multD2 sep_mult_assoc)

lemma interp_m[simp]: "\<I> INTERP (mk x) = \<I> I x"
  unfolding INTERP_def by (simp add: sep_disj_commute sep_mult_commute)

lemma interp_split:
  "Fic_Space f \<Longrightarrow>
    \<I> INTERP f = \<I> INTERP (clean f) * \<I> I (project (f name))
  \<and> \<I> INTERP (clean f) ## \<I> I (project (f name))"
  unfolding INTERP_def Fic_Space_def
  apply (subst \<F>_fun'_split[where ?f = f and ?k = name])
  by simp_all

lemma interp_split':
  " NO_MATCH (clean f') f
\<Longrightarrow> Fic_Space f
\<Longrightarrow> \<I> INTERP f = \<I> INTERP (clean f) * \<I> I (project (f name))
  \<and> \<I> INTERP (clean f) ## \<I> I (project (f name))"
  using interp_split .

lemma Fic_Space_m[simp]: "Fic_Space (mk x)"
  unfolding Fic_Space_def by simp

lemma Fic_Space_mc[simp]: "Fic_Space (clean f) \<longleftrightarrow> Fic_Space f"
  unfolding Fic_Space_def by simp

lemma Fic_Space_mm[simp]: "Fic_Space (f * mk x) \<longleftrightarrow> Fic_Space f"
  unfolding Fic_Space_def finite_dom1_mult1 times_fun by simp

end

ML_file_debug \<open>fiction_space.ML\<close>

end