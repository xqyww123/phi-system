text \<open>The idea of the locale-based modular semantics framework is using Virtual Datatype~\cite{VDT}
to formalize types and values modularly and using an improved Statespace~\cite{Statespace} to
formalize resources.\<close>

section \<open>Framework for Modular Formalization of Resources \& Fictional Resources\<close>

text \<open>Algebras used in the formalization are given in~\cite{Algebras}.\<close>

theory Resource_Space
  imports "Phi_Algebras.Algebras" "Phi_Statespace.StateFun"
begin


subsection \<open>Separation Closed Set\<close>

definition Sep_Closed :: \<open>'a::sep_magma_1 set \<Rightarrow> bool\<close>
  where \<open>Sep_Closed S \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> x \<in> S \<and> y \<in> S \<longrightarrow> (x * y) \<in> S) \<and> 1 \<in> S\<close>

lemma Sep_Closed_inter:
  \<open>Sep_Closed S1 \<Longrightarrow> Sep_Closed S2 \<Longrightarrow> Sep_Closed (S1 \<inter> S2)\<close>
  unfolding Sep_Closed_def by blast

lemma Sep_Closed_UNIV[simp]:
  \<open>Sep_Closed UNIV\<close>
  unfolding Sep_Closed_def by simp

typedef (overloaded) ('a::sep_magma_1) sep_closed_set = \<open>Collect (Sep_Closed::'a set \<Rightarrow> bool)\<close>
  morphisms dest_sep_closed_set sep_closed_set
  unfolding Sep_Closed_def by blast

setup_lifting type_definition_sep_closed_set

lift_definition sep_closed_member :: \<open>'a::sep_magma_1 \<Rightarrow> 'a sep_closed_set \<Rightarrow> bool\<close> (infix "\<in>\<^sub>S" 50)
  is \<open>\<lambda>x S. x \<in> S\<close> .

lemma in_sep_closed_set[simp]:
  \<open>Sep_Closed S \<Longrightarrow> x \<in>\<^sub>S sep_closed_set S \<longleftrightarrow> x \<in> S\<close>
  unfolding sep_closed_member_def
  by (simp add: sep_closed_set_inverse)

lemma one_in_sep_closed_set[simp]:
  \<open>1 \<in>\<^sub>S S\<close> for S :: \<open>'a::sep_magma_1 sep_closed_set\<close>
  by (transfer; simp add: Sep_Closed_def)

lemma mult_in_sep_closed_set[simp]:
  \<open>x ## y \<Longrightarrow> x \<in>\<^sub>S S \<and> y \<in>\<^sub>S S \<longrightarrow> x * y \<in>\<^sub>S S\<close> for S :: \<open>'a::sep_algebra sep_closed_set\<close>
  by (transfer; simp add: Sep_Closed_def)

lift_definition sep_closed_inter :: \<open>'a::sep_magma_1 sep_closed_set \<Rightarrow> 'a sep_closed_set \<Rightarrow> 'a sep_closed_set\<close> (infixl "\<inter>\<^sub>S" 65)
  is \<open>\<lambda>S1 S2. S1 \<inter> S2\<close>
  by (clarsimp simp add: Sep_Closed_def; blast)

definition sep_closed_image :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> 'a sep_closed_set \<Rightarrow> 'b sep_closed_set\<close> (infixr "`\<^sub>S" 90)
  where \<open>(f `\<^sub>S S) = sep_closed_set (f ` dest_sep_closed_set S) \<close>

definition Homo_Sep_Closed :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> bool\<close>
  where \<open>Homo_Sep_Closed f \<longleftrightarrow> (\<forall>S. Sep_Closed S \<longrightarrow> Sep_Closed (f ` S))\<close>

lemma in_image_sep_closed[simp]:
  \<open>Homo_Sep_Closed f \<Longrightarrow> x \<in>\<^sub>S f `\<^sub>S S \<longleftrightarrow> (\<exists>x'. x = f x' \<and> x' \<in>\<^sub>S S)\<close>
  by (smt (verit, del_insts) Homo_Sep_Closed_def dest_sep_closed_set dest_sep_closed_set_inverse image_iff in_sep_closed_set mem_Collect_eq sep_closed_image_def)

subsubsection \<open>Common Sep-Closed Sets\<close>

lemma sep_closed_partial_map[simp]:
  \<open>Sep_Closed {vars. finite (dom vars)}\<close>
  unfolding Sep_Closed_def
  by (clarsimp simp add: dom_mult)

lemma sep_closed_partial_map1[simp]:
  \<open>Sep_Closed {h::'a \<Rightarrow> 'b :: sep_no_inverse. finite (dom1 h)}\<close> 
  unfolding Sep_Closed_def
  by (clarsimp simp add: dom1_mult)

lemma Sep_Closed_pointwise:
  \<open> (\<forall>k. P k 1)
\<Longrightarrow> (\<forall>k x y. x ## y \<longrightarrow> P k x \<and> P k y \<longrightarrow> P k (x * y))
\<Longrightarrow>   Sep_Closed {f. \<forall>k. P k (f k) }\<close>
  unfolding Sep_Closed_def
  by (simp add: times_fun; blast)


subsection \<open>Separation Homo Set\<close>

definition Sep_Homo :: \<open>'a::sep_magma_1 set \<Rightarrow> bool\<close>
  where \<open>Sep_Homo S \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> (x * y) \<in> S \<longleftrightarrow> x \<in> S \<and> y \<in> S) \<and> 1 \<in> S\<close>

lemma Sep_Homo_inter:
  \<open>Sep_Homo S1 \<Longrightarrow> Sep_Homo S2 \<Longrightarrow> Sep_Homo (S1 \<inter> S2)\<close>
  unfolding Sep_Homo_def by blast

lemma Sep_Homo_UNIV[simp]:
  \<open>Sep_Homo UNIV\<close>
  unfolding Sep_Homo_def by simp

typedef (overloaded) ('a::sep_magma_1) sep_homo_set = \<open>Collect (Sep_Homo::'a set \<Rightarrow> bool)\<close>
  morphisms dest_sep_homo_set sep_homo_set
  unfolding Sep_Homo_def by blast

setup_lifting type_definition_sep_homo_set

lift_definition sep_homo_member :: \<open>'a::sep_magma_1 \<Rightarrow> 'a sep_homo_set \<Rightarrow> bool\<close> (infix "\<in>\<^sub>S\<^sub>H" 50)
  is \<open>\<lambda>x S. x \<in> S\<close> .

lemma in_sep_homo_set[simp]:
  \<open>Sep_Homo S \<Longrightarrow> x \<in>\<^sub>S\<^sub>H sep_homo_set S \<longleftrightarrow> x \<in> S\<close>
  unfolding sep_homo_member_def
  by (simp add: sep_homo_set_inverse)

lemma one_in_sep_homo_set[simp]:
  \<open>1 \<in>\<^sub>S\<^sub>H S\<close> for S :: \<open>'a::sep_magma_1 sep_homo_set\<close>
  by (transfer; simp add: Sep_Homo_def)

lemma mult_in_sep_homo_set[simp]:
  \<open>x ## y \<Longrightarrow> x * y \<in>\<^sub>S\<^sub>H S \<longleftrightarrow> x \<in>\<^sub>S\<^sub>H S \<and> y \<in>\<^sub>S\<^sub>H S\<close> for S :: \<open>'a::sep_algebra sep_homo_set\<close>
  by (transfer; simp add: Sep_Homo_def)

lift_definition sep_homo_inter :: \<open>'a::sep_magma_1 sep_homo_set \<Rightarrow> 'a sep_homo_set \<Rightarrow> 'a sep_homo_set\<close> (infixl "\<inter>\<^sub>S\<^sub>H" 65)
  is \<open>\<lambda>S1 S2. S1 \<inter> S2\<close>
  by (clarsimp simp add: Sep_Homo_def; blast)

definition sep_homo_image :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> 'a sep_homo_set \<Rightarrow> 'b sep_homo_set\<close> (infixr "`\<^sub>S\<^sub>H" 90)
  where \<open>(f `\<^sub>S\<^sub>H S) = sep_homo_set (f ` dest_sep_homo_set S) \<close>



subsection \<open>Kind\<close>

text \<open>
The section presents the improved Statespace, \<^emph>\<open>resource space\<close>, which is specialized for
  resource models in separation algebra.
In addition, the section also presents a similar construct, \<^emph>\<open>fiction space\<close>,
  for formalize modularly fictions used in fictional separation (i.e., Fictional
  Separation Logic~\cite{FSL}).\<close>

declare [[typedef_overloaded]]

datatype ('CONS_NAME,'REP,'ABS,'DOMAIN) kind =
  kind (name: 'CONS_NAME) (project: "'REP \<Rightarrow> 'ABS") (inject: "'ABS \<Rightarrow> 'REP") (domain: \<open>'DOMAIN\<close>)

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

We reuse \<^typ>\<open>('NAME, 'REP::sep_algebra, 'T::sep_algebra, 'T sep_closed_set) kind\<close>
to represent resource kinds.
A resource kind is a triple of \<open>name::'NAME\<close> and \<open>project :: 'REP \<Rightarrow> 'T, inject :: 'T \<Rightarrow> 'REP\<close> between
  the deep representation \<open>'REP\<close> of the states and the model \<open>'T\<close> of this kind of resource.

The model \<open>'T\<close> is required to be a separation algebra, albeit
it does not require the physical resource to be separable because any structure can be
  lifted to a a discrete separable because by introducing a unit element standing for
 none resource or no specification.
\<close>

locale sep_insertion =
  inj: homo_sep inject + prj: homo_sep project + inj: homo_sep_disj_total inject
  for inject :: \<open>'T::sep_algebra \<Rightarrow> 'REP::sep_algebra\<close>
  and project:: \<open>'REP::sep_algebra \<Rightarrow> 'T::sep_algebra\<close>
    \<comment> \<open>the project' cannot be arbitrarily any inverse function of the inject',
      but must be the one itself is also a separation homomorphism.\<close>
+ assumes proj_inj[simp]: "project (inject x) = x"
    and   mult_in_dom:    \<open>a ## b \<Longrightarrow>
              a * b = inject c \<longleftrightarrow> (\<exists>a' b'. a = inject a' \<and> b = inject b' \<and> a' * b' = c)\<close>
begin

sublocale inj: homo_sep_wand_monoid inject
  by (standard, metis mult_in_dom prj.sep_disj_homo_semi proj_inj)

lemma inject_inj[iff]:
  \<open>inject a = inject b \<longleftrightarrow> a = b\<close>
  by (metis proj_inj)

lemma inject_assoc_homo[simp]:
  "R ## inject x \<and> R * inject x ## inject y
\<Longrightarrow> R * inject x * inject y = R * inject (x * y)"
  by (metis mult_in_dom sep_disj_multD2 sep_mult_assoc)

lemma inj_Sep_Closed:
  \<open>Homo_Sep_Closed inject\<close>
  unfolding Sep_Closed_def Homo_Sep_Closed_def
  apply clarsimp
 
  using image_iff mult_in_dom by fastforce

end

lemma sep_insertion_id: \<open>sep_insertion id id\<close> by (standard; simp)

lemma sep_insertion_comp:
  \<open> sep_insertion f1 g1
\<Longrightarrow> sep_insertion f2 g2
\<Longrightarrow> sep_insertion (f2 o f1) (g1 o g2)\<close>
  unfolding sep_insertion_def sep_insertion_axioms_def
  apply (simp add: homo_sep_comp homo_sep_disj_total_comp)
  using homo_sep_disj_total.sep_disj_homo by blast


locale sep_space_entry =
  sep_insertion inject' project'
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

lemmas split = fun_split_1[where ?k = name and ?'a = 'NAME and ?'b = 'REP]

lemma inject_wand_homo: \<open>
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

locale "resource_space" =
  fixes DOMAIN :: \<open>'NAME \<Rightarrow> 'REP::sep_algebra sep_closed_set\<close>
begin

definition SPACE :: \<open>('NAME \<Rightarrow> 'REP) set\<close>
  where \<open>SPACE = {R. finite (dom1 R) \<and> (\<forall>N. R N \<in>\<^sub>S DOMAIN N) }\<close>

lemma SPACE_1[iff]:
  \<open>1 \<in> SPACE\<close>
  unfolding SPACE_def by simp

lemma SPACE_mult_homo:
  \<open>A ## B \<Longrightarrow> A \<in> SPACE \<and> B \<in> SPACE \<Longrightarrow> A * B \<in> SPACE\<close>
  unfolding SPACE_def
  by (simp add: times_fun sep_disj_fun_def dom1_sep_mult_disjoint; blast)

(* lemma
  \<open>Sep_Closed {R. \<forall>N. R N \<in>\<^sub>S DOMAIN N }\<close>
  unfolding Sep_Closed_def by (simp add: times_fun sep_disj_fun_def; blast) *)

end


locale resource_kind =
  "resource_space" DOMAIN
+ sep_space_entry \<open>kind.name K\<close> \<open>kind.inject K\<close> \<open>kind.project K\<close>
for DOMAIN :: \<open>'NAME \<Rightarrow> 'REP::sep_algebra sep_closed_set\<close>
and K :: "('NAME, 'REP::sep_algebra, 'T::sep_algebra, 'T sep_closed_set) kind"
+ assumes raw_domain: "DOMAIN (kind.name K) = kind.inject K `\<^sub>S kind.domain K"

begin

subsubsection \<open>Methods and Sugars of a Resource Kind\<close>

abbreviation "domain \<equiv> kind.domain K"

lemma inj_in_DOMAIN[simp]:
  \<open>inject x \<in>\<^sub>S DOMAIN name \<longleftrightarrow> x \<in>\<^sub>S domain\<close>
  by (simp add: inj_Sep_Closed raw_domain)

lemma \<r>_valid_split:
  \<open>res \<in> SPACE \<longleftrightarrow>
  clean res \<in> SPACE \<and> (\<exists>m. res name = inject m \<and> m \<in>\<^sub>S domain)\<close>
  apply (subst split; simp add: times_fun image_iff SPACE_def)
  using inj_Sep_Closed raw_domain by auto

lemma \<r>_valid_split': \<open>
  NO_MATCH (clean res') res
\<Longrightarrow> res \<in> SPACE \<longleftrightarrow> clean res \<in> SPACE \<and> (\<exists>m. res name = inject m \<and> m \<in>\<^sub>S domain)\<close>
  using \<r>_valid_split .

lemma inj_prj_in_SPACE[simp]:
  \<open>f \<in> SPACE \<Longrightarrow> inject (project (f name)) = f name\<close>
  by (metis \<r>_valid_split proj_inj)


end

locale resource_kind' =
  resource_kind DOMAIN K
for DOMAIN :: \<open>'NAME \<Rightarrow> 'REP::sep_algebra sep_closed_set\<close>
and K :: "('NAME, 'REP::sep_algebra, 'T::sep_algebra, 'T sep_closed_set) kind"
and DOM :: \<open>'T::sep_algebra sep_closed_set\<close>
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
  fixes DOMAIN :: \<open>'FNAME \<Rightarrow> 'FREP::sep_algebra sep_homo_set\<close>
    and INTERPRET :: "'FNAME \<Rightarrow> ('FREP::sep_algebra,'RES::sep_algebra) interp"
    \<comment> \<open>\<^term>\<open>INTERPRET i\<close> gives the interpretation of fiction kind \<open>i\<close>, i.e., \<open>I\<^sub>i\<close> above.\<close>
begin

definition SPACE :: \<open>('FNAME \<Rightarrow> 'FREP) set\<close>
  where \<open>SPACE = {R. finite (dom1 R) \<and> (\<forall>N. R N \<in>\<^sub>S\<^sub>H DOMAIN N) }\<close>

lemma SPACE_1[iff]:
  \<open>1 \<in> SPACE\<close>
  unfolding SPACE_def by simp

lemma SPACE_mult_homo:
  \<open>A ## B \<Longrightarrow> A * B \<in> SPACE \<longleftrightarrow> A \<in> SPACE \<and> B \<in> SPACE\<close>
  unfolding SPACE_def
  by (simp add: times_fun sep_disj_fun_def dom1_sep_mult_disjoint; blast)


definition "INTERP = \<F>_fun' INTERPRET"

end


locale fiction_kind =
  fictional_space DOMAIN INTERPRET
+ sep_space_entry \<open>kind.name FK\<close> \<open>kind.inject FK\<close> \<open>kind.project FK\<close>
  for DOMAIN :: \<open>'FNAME \<Rightarrow> 'FREP::sep_algebra sep_homo_set\<close>
  and INTERPRET :: "'FNAME \<Rightarrow> ('FREP::sep_algebra,'RES::sep_algebra) interp"
  and FK :: "('FNAME,'FREP,'T::sep_algebra, unit) kind"
+ fixes I :: "('T,'RES) interp"
assumes interpret_reduct[simp]: "\<I> (INTERPRET (kind.name FK)) = \<I> I o kind.project FK"
  and   raw_domain: "DOMAIN (kind.name FK) = sep_homo_set {rep. \<exists>x. rep = kind.inject FK x}"
begin

lemma in_DOMAIN[simp]:
  \<open>rep \<in>\<^sub>S\<^sub>H DOMAIN (kind.name FK) \<longleftrightarrow> (\<exists>x. rep = kind.inject FK x)\<close>
proof -
  have \<open>Sep_Homo {rep. \<exists>x. rep = kind.inject FK x}\<close>
    unfolding Sep_Homo_def by (simp add: mult_in_dom; blast)
  then show ?thesis unfolding raw_domain by simp
qed

(*lemma \<r>_valid_split:
  \<open>res \<in> SPACE \<longleftrightarrow>
  clean res \<in> SPACE \<and> (\<exists>m. res name = inject m)\<close>
  by (subst split; simp add: times_fun image_iff SPACE_def; blast)

lemma \<r>_valid_split': \<open>
  NO_MATCH (clean res') res
\<Longrightarrow> res \<in> SPACE \<longleftrightarrow> clean res \<in> SPACE \<and> (\<exists>m. res name = inject m)\<close>
  using \<r>_valid_split . *)

lemma inj_prj_in_SPACE[simp]:
  \<open>f \<in> SPACE \<Longrightarrow> inject (project (f name)) = f name\<close>
  by (smt (verit, best) fictional_space.SPACE_def in_DOMAIN mem_Collect_eq proj_inj)
  (* by (metis \<r>_valid_split proj_inj) *)


lemma Fic_Space_m[simp]: "mk x \<in> SPACE"
  unfolding SPACE_def by simp

lemma interp_m[simp]: "\<I> INTERP (mk x) = \<I> I x"
  unfolding INTERP_def by (simp add: sep_disj_commute sep_mult_commute inj.inj_at_1)

lemma sep_disj_get_name_eq[simp]:
  \<open>r \<in> SPACE \<Longrightarrow> get r ## x \<longleftrightarrow> r ## mk x\<close>
  by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo inj_prj_in_SPACE)

lemma interp_split:
  "f \<in> SPACE \<Longrightarrow>
    \<I> INTERP f = \<I> INTERP (clean f) * \<I> I (project (f name))
  \<and> \<I> INTERP (clean f) ## \<I> I (project (f name))"
  unfolding INTERP_def SPACE_def
  apply (subst \<F>_fun'_split[where ?f = f and ?k = name])
  by simp_all

lemma interp_split':
  " NO_MATCH (clean f') f
\<Longrightarrow> f \<in> SPACE
\<Longrightarrow> \<I> INTERP f = \<I> INTERP (clean f) * \<I> I (project (f name))
  \<and> \<I> INTERP (clean f) ## \<I> I (project (f name))"
  using interp_split .

lemma Fic_Space_mm[simp]: "f ## mk x \<Longrightarrow> f * mk x \<in> SPACE \<longleftrightarrow> f \<in> SPACE"
  unfolding SPACE_def finite_dom1_mult1
  apply clarsimp
  by (smt (verit, ccfv_threshold) Fic_Space_m SPACE_def SPACE_mult_homo finite_dom1_mult1 mem_Collect_eq)

end

ML_file_debug \<open>fiction_space.ML\<close>

hide_type (open) kind
hide_const (open) kind


end