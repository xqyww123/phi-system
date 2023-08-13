text \<open>The idea of the locale-based modular semantics framework is using Virtual Datatype~\cite{VDT}
to formalize types and values modularly and using an improved Statespace~\cite{Statespace} to
formalize resources.\<close>

section \<open>Framework for Modular Formalization of Resources \& Fictional Resources\<close>

text \<open>Algebras used in the formalization are given in~\cite{Algebras}.\<close>

theory Resource_Space
  imports "Phi_Algebras.Phi_Fiction" "Phi_Statespace.StateFun"
begin



subsection \<open>Kind\<close>

text \<open>
The section presents the improved Statespace, \<^emph>\<open>resource space\<close>, which is specialized for
  resource models in separation algebra.
In addition, the section also presents a similar construct, \<^emph>\<open>fiction space\<close>,
  for formalize modularly fictions used in fictional separation (i.e., Fictional
  Separation Logic~\cite{FSL}).\<close>

declare [[typedef_overloaded]]

datatype ('CONS_NAME,'REP,'ABS) kind =
  kind (name: 'CONS_NAME) (project: "'REP \<Rightarrow> 'ABS") (inject: "'ABS \<Rightarrow> 'REP") (domain: \<open>'ABS sep_homo_set\<close>)

hide_const (open) name project inject domain

declare [[typedef_overloaded=false]]

syntax
  "_entry_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"     ("(2_ #=/ _)")
  "_fine_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"  ("_/'((_)')\<^sub>?" [1000, 0] 900)

translations
  "f(x#=y)" => "f(CONST kind.name x := CONST kind.inject x y)"



subsection \<open>Resource Space\<close>

text \<open>The section gives a locale-based approach for modelling modularly compound resource states
  that combine different kinds of resources modelled by different types.
It is in essence a modified Statespace ~\cite{Statespace} with the sort constraint of \<open>sep_algebra\<close>.

Different kinds of resources can use different types for modelling, and the compound is represented
by a uniform deep representation, a finite partial map of type
  \<^typ>\<open>'NAME \<Rightarrow> ('REP::sep_algebra)\<close>
where \<open>'NAME\<close> is the type of the names of resource kinds that identify each resource kind;
type \<open>'REP\<close> is the deep representation of states of resources.

We reuse \<^typ>\<open>('NAME, 'REP::sep_algebra, 'T::sep_algebra) kind\<close>
to represent resource kinds.
A resource kind is a triple of \<open>name::'NAME\<close> and \<open>project :: 'REP \<Rightarrow> 'T, inject :: 'T \<Rightarrow> 'REP\<close> between
  the deep representation \<open>'REP\<close> of the states and the model \<open>'T\<close> of this kind of resource.

The model \<open>'T\<close> is required to be a separation algebra, albeit
it does not require the physical resource to be separable because any structure can be
  lifted to a a discrete separable because by introducing a unit element standing for
 none resource or no specification.
\<close>

locale sep_inj_proj =
  inj: homo_sep inject + inj: homo_one inject +
  prj: homo_sep project + prj: homo_one project +
  inj: closed_homo_sep_disj inject
  for inject :: \<open>'T::sep_algebra \<Rightarrow> 'REP::sep_algebra\<close>
  and project:: \<open>'REP::sep_algebra \<Rightarrow> 'T::sep_algebra\<close>
    \<comment> \<open>the project' cannot be arbitrarily any inverse function of the inject',
      but must be the one itself is also a separation homomorphism.\<close>
+ assumes proj_inj[simp]: "project (inject x) = x"
    and   mult_in_dom:    \<open>a ## b \<Longrightarrow>
              a * b = inject c \<longleftrightarrow> (\<exists>a' b'. a = inject a' \<and> b = inject b' \<and> a' * b' = c)\<close>
begin

sublocale inj: sep_orthogonal_monoid inject UNIV
  by (standard; simp; metis mult_in_dom prj.sep_disj_homo_semi proj_inj)

lemma inject_inj[iff]:
  \<open>inject a = inject b \<longleftrightarrow> a = b\<close>
  by (metis proj_inj)

lemma inject_assoc_homo[simp]:
  "R ## inject x \<and> R * inject x ## inject y
\<Longrightarrow> R * inject x * inject y = R * inject (x * y)"
  by (metis mult_in_dom sep_disj_multD2 sep_mult_assoc)

lemma inj_Sep_Homo:
  \<open>Homo_Sep_Homo inject\<close>
  unfolding Sep_Closed_def Homo_Sep_Homo_def
  apply (auto simp add: Sep_Homo_def)
  using mult_in_dom apply auto[1]
  using mult_in_dom apply auto[1]
  by (metis imageI inj.homo_mult)

end

lemma sep_inj_proj_id: \<open>sep_inj_proj id id\<close> by (standard; simp)

lemma sep_inj_proj_comp:
  \<open> sep_inj_proj f1 g1
\<Longrightarrow> sep_inj_proj f2 g2
\<Longrightarrow> sep_inj_proj (f2 o f1) (g1 o g2)\<close>
  unfolding sep_inj_proj_def sep_inj_proj_axioms_def
  apply (clarsimp simp add: homo_sep_comp closed_homo_sep_disj_comp homo_one_def)
  using closed_homo_sep_disj.sep_disj_homo by blast


locale sep_space_entry =
  sep_inj_proj inject' project'
  for name'   :: 'NAME
  and inject' :: \<open>'T::sep_algebra \<Rightarrow> 'REP::sep_algebra\<close>
  and project':: \<open>'REP::sep_algebra \<Rightarrow> 'T::sep_algebra\<close>
begin


abbreviation "name \<equiv> name'"
abbreviation "inject \<equiv> inject'"
abbreviation "project \<equiv> project'"

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

lemma sep_disj_mk[iff]:
  \<open>mk x ## mk y \<longleftrightarrow> x ## y\<close>
  by force

lemma sep_disj_mk_name[simp]:
  \<open>r ## mk x \<Longrightarrow> r name ## inject x\<close>
  by (metis fun_upd_same sep_disj_fun)

lemma sep_disj_get_name:
  \<open>r ## mk x \<longrightarrow> get r ## x\<close>
  by (metis prj.sep_disj_homo_semi proj_inj sep_disj_mk_name)

lemma get_homo_mult:
  \<open>a ## b \<Longrightarrow> get (a * b) = get a * get b\<close>
  by (simp add: prj.homo_mult times_fun)

lemma mk_homo_one[iff]: \<open>mk x = 1 \<longleftrightarrow> x = 1\<close>
  by (metis fun_1upd1 fun_upd_eqD inj.homo_one proj_inj)

lemma mk_homo_mult: \<open>a ## b \<Longrightarrow> mk (a * b) = mk a * mk b\<close>
  by (simp add: fun_1upd_homo inj.homo_mult)

lemma mk_inj[iff]: \<open>mk a = mk b \<longleftrightarrow> a = b\<close>
  unfolding fun_eq_iff by simp
(* 
lemmas split = fun_split_1[where ?k = name and ?'a = 'NAME and ?'b = 'REP]

lemma inject_wand_homo: \<open>
  NO_MATCH (inject a'') a'
\<Longrightarrow> a' ## inject b
\<Longrightarrow> a' * inject b = inject c \<longleftrightarrow> (\<exists>a. a' = inject a \<and> a * b = c \<and> a ## b)\<close>
  \<comment> \<open>split the deep representation of the kind \<open>K\<close>.
      This lemma is useful in fictional separation especially view shifts.\<close>
  using mult_in_dom by force

lemma sep_disj_clean[simp]:
  \<open>clean r ## mk any\<close>
  by simp *)

lemma times_fun_upd:
  \<open>(R * mk x)(name := inject y) = (clean R * mk y)\<close>
  unfolding times_fun_def fun_upd_def fun_eq_iff by simp

end

locale "resource_space" =
  fixes DOMAIN :: \<open>'NAME \<Rightarrow> 'REP::sep_algebra sep_homo_set\<close>
begin

definition SPACE :: \<open>('NAME \<Rightarrow> 'REP) set\<close>
  where \<open>SPACE = {R. finite (dom1 R) \<and> (\<forall>N. R N \<in>\<^sub>S\<^sub>H DOMAIN N) }\<close>

lemma SPACE_1[iff]:
  \<open>1 \<in> SPACE\<close>
  unfolding SPACE_def by simp

lemma SPACE_mult_homo:
  \<open>A ## B \<Longrightarrow> A * B \<in> SPACE \<longleftrightarrow> A \<in> SPACE \<and> B \<in> SPACE\<close>
  unfolding SPACE_def
  by (simp add: times_fun sep_disj_fun_def dom1_sep_mult_disjoint; blast)

(* lemma
  \<open>Sep_Closed {R. \<forall>N. R N \<in>\<^sub>S DOMAIN N }\<close>
  unfolding Sep_Closed_def by (simp add: times_fun sep_disj_fun_def; blast) *)

end


locale resource_kind =
  "resource_space" DOMAIN
+ sep_space_entry \<open>kind.name K\<close> \<open>kind.inject K\<close> \<open>kind.project K\<close>
for DOMAIN :: \<open>'NAME \<Rightarrow> 'REP::sep_algebra sep_homo_set\<close>
and K :: "('NAME, 'REP::sep_algebra, 'T::sep_algebra) kind"
+ assumes raw_domain: "DOMAIN (kind.name K) = kind.inject K `\<^sub>S\<^sub>H kind.domain K"

begin

subsubsection \<open>Methods and Sugars of a Resource Kind\<close>

abbreviation "domain \<equiv> kind.domain K"

lemma in_DOMAIN[simp]:
  \<open>rep \<in>\<^sub>S\<^sub>H DOMAIN name \<longleftrightarrow> (\<exists>x. rep = inject x \<and> x \<in>\<^sub>S\<^sub>H domain)\<close>
  by (simp add: inj_Sep_Homo raw_domain)

lemma \<r>_valid_split:
  \<open>res \<in> SPACE \<longleftrightarrow>
  clean res \<in> SPACE \<and> (\<exists>m. res name = inject m \<and> m \<in>\<^sub>S\<^sub>H domain)\<close>
  apply (subst fun_split_1[where ?k = name and ?'a = 'NAME and ?'b = 'REP];
         simp add: times_fun image_iff SPACE_def)
  using inj_Sep_Homo raw_domain by auto

lemma \<r>_valid_split': \<open>
  NO_MATCH (clean res') res
\<Longrightarrow> res \<in> SPACE \<longleftrightarrow> clean res \<in> SPACE \<and> (\<exists>m. res name = inject m \<and> m \<in>\<^sub>S\<^sub>H domain)\<close>
  using \<r>_valid_split .

lemma inj_prj_in_SPACE[simp]:
  \<open>f \<in> SPACE \<Longrightarrow> inject (project (f name)) = f name\<close>
  by (metis \<r>_valid_split proj_inj)

end

locale resource_kind' =
  resource_kind DOMAIN K
for DOMAIN :: \<open>'NAME \<Rightarrow> 'REP::sep_algebra sep_homo_set\<close>
and K :: "('NAME, 'REP::sep_algebra, 'T::sep_algebra) kind"
and DOM :: \<open>'T::sep_algebra sep_homo_set\<close>
+ assumes domain[simp]: "kind.domain K = DOM"

ML_file \<open>resource_space.ML\<close>


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
  resource_space DOMAIN
  for DOMAIN :: \<open>'FNAME \<Rightarrow> 'FREP::sep_algebra sep_homo_set\<close>
  and INTERPRET :: "'FNAME \<Rightarrow> ('FREP::sep_algebra,'RES::sep_algebra) unital_homo_interp"
    \<comment> \<open>\<^term>\<open>INTERPRET i\<close> gives the interpretation of fiction kind \<open>i\<close>, i.e., \<open>I\<^sub>i\<close> above.\<close>
begin

definition "INTERP = \<F>_FP_homo INTERPRET"

end


locale fiction_kind =
  fictional_space DOMAIN INTERPRET
+ resource_kind DOMAIN FK
  for DOMAIN :: \<open>'FNAME \<Rightarrow> 'FREP::sep_algebra sep_homo_set\<close>
  and INTERPRET :: "'FNAME \<Rightarrow> ('FREP::sep_algebra,'RES::sep_algebra) unital_homo_interp"
  and FK :: "('FNAME,'FREP,'T::sep_algebra) kind"
+ fixes I :: "('T,'RES) interp"
assumes interpret_reduct: "INTERPRET (kind.name FK) = Unital_Homo (I o kind.project FK)"
  and   univ_domain[simp]: "kind.domain FK = sep_homo_set UNIV"
begin

(*lemma \<r>_valid_split:
  \<open>res \<in> SPACE \<longleftrightarrow>
  clean res \<in> SPACE \<and> (\<exists>m. res name = inject m)\<close>
  by (subst split; simp add: times_fun image_iff SPACE_def; blast)

lemma \<r>_valid_split': \<open>
  NO_MATCH (clean res') res
\<Longrightarrow> res \<in> SPACE \<longleftrightarrow> clean res \<in> SPACE \<and> (\<exists>m. res name = inject m)\<close>
  using \<r>_valid_split . *)

  (* by (metis \<r>_valid_split proj_inj) *)

lemma Fic_Space_m[simp]: "mk x \<in> SPACE"
  unfolding SPACE_def by simp

lemma interp_m[simp]: "homo_one I \<Longrightarrow> INTERP (mk x) = I x"
  unfolding INTERP_def
  by (simp add: sep_disj_commute sep_mult_commute interpret_reduct prj.homo_one_axioms,
      metis homo_one.homo_one prj.homo_one_axioms proj_inj)

lemma sep_disj_get_name_eq[simp]:
  \<open>r \<in> SPACE \<Longrightarrow> get r ## x \<longleftrightarrow> r ## mk x\<close>
  by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo inj_prj_in_SPACE)

lemma interp_split:
  " NO_MATCH (clean f') f
\<Longrightarrow> homo_one I
\<Longrightarrow> f \<in> SPACE \<Longrightarrow>
    INTERP f = INTERP (clean f) * I (project (f name))
  \<and> INTERP (clean f) ## I (project (f name))"
  unfolding INTERP_def SPACE_def
  by (subst \<F>_FP_homo_split[where ?f = f and ?k = name],
      simp_all add: interpret_reduct prj.homo_one_axioms)

lemma Fic_Space_mm[simp]: "f ## mk x \<Longrightarrow> f * mk x \<in> SPACE \<longleftrightarrow> f \<in> SPACE"
  unfolding SPACE_def finite_dom1_mult1
  apply clarsimp
  by (smt (verit, ccfv_threshold) Fic_Space_m SPACE_def SPACE_mult_homo finite_dom1_mult1 mem_Collect_eq)

end

ML_file_debug \<open>fiction_space.ML\<close>

hide_type (open) kind
hide_const (open) kind


end