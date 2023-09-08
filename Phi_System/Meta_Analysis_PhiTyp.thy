theory Meta_Analysis_PhiTyp
  imports Phi_Type_Algebra
begin

section \<open>Completeness of Transformation\<close>

text \<open>Given a \<phi>-type \<open>T\<close>, its objects form a poset where \<open>x \<R> y \<triangleq> x \<Ztypecolon> T \<longrightarrow> y \<Ztypecolon> T\<close> and \<open>\<R>\<close> is the order.
In order to reason a transformation \<open>x \<Ztypecolon> T \<longrightarrow> y \<Ztypecolon> U\<close>, we first infer a family of transformation partial maps \<open>{f\<^sub>i}\<^sub>i\<^sub>\<in>\<^sub>\<I>\<close>
satisfying \<open>\<forall>i\<in>\<I>. x \<Ztypecolon> T \<longrightarrow> f\<^sub>i(x) \<Ztypecolon> U\<close>. Then we check if exists one image \<open>f\<^sub>i(x)\<close> preceding \<open>y\<close> in \<open>\<R>\<close>,
\<open>\<exists>i\<in>\<I>. f\<^sub>i(x) \<R> y\<close> which implies \<open>\<exists>i\<in>\<I>. f\<^sub>i(x) \<Ztypecolon> U \<longrightarrow> y \<Ztypecolon> U\<close>.

Such of a family \<open>{f\<^sub>i}\<^sub>i\<^sub>\<in>\<^sub>\<I>\<close> is complete iff all objects \<open>y \<Ztypecolon> U\<close> to which \<open>x\<close> can transform are included in the
family, \<open>\<forall>x y. (x \<Ztypecolon> T \<longrightarrow> y \<Ztypecolon> U) \<longrightarrow> y \<in> \<Union>\<^sub>i \<R>(f\<^sub>i(x))\<close>. The above reasoning is complete iff the \<open>{f\<^sub>i}\<^sub>i\<^sub>\<in>\<^sub>\<I>\<close> that
we have inferred is complete (also note usually we only infer a lower bound of \<open>\<R>\<close>).

About implementation, a family \<open>{f\<^sub>i}\<close> can be simply represented by a single lambda term parameterized
by free variables.
The domains of the partial maps can be given by boolean conditions constraining the transformation
in a way which also gives the proof obligation of applying the transformation. In this way, it enables
representing them by total maps as that only supported in most of proof assistance.

Note: have to distinguish \<open>{f\<^sub>i}\<^sub>i\<^sub>\<in>\<^sub>\<I>\<close> and the relation \<open>r\<close> in \<open>x \<Ztypecolon> T \<longrightarrow> {y \<Ztypecolon> U |y. r(x,y)}\<close>
In the latter \<open>r\<close>, the \<open>x\<close> is transformed to one of the \<open>y \<in> r(x)\<close> uncertainly, but the in the former,
\<open>x\<close> can be transformed to any of \<open>y \<in> \<Union>\<^sub>i{f\<^sub>i(x)}\<close> arbitrarily.
\<close>

definition Transformation_Order :: \<open>('c,'a) \<phi> \<Rightarrow> ('c,'b) \<phi> \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  where \<open>Transformation_Order T U = (\<lambda>x y. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U)\<close>

definition Complete_Transformation :: \<open>('c,'a) \<phi> \<Rightarrow> ('c,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Complete_Transformation T U f \<longleftrightarrow> f OO Transformation_Order U U = Transformation_Order T U\<close>

definition family_decode \<comment> \<open>Decoding a family of transformation maps (represented in a set) to a relation
                             characterizing which targets are covered from each source\<close>
  where \<open>family_decode fs = (\<lambda>x y. \<exists>f \<in> fs. f x = Some y)\<close>

definition Complete_Transformation'
  where \<open>Complete_Transformation' T U fs \<longleftrightarrow> Complete_Transformation T U (family_decode fs)\<close>


lemma Transformation_Order_id:
  \<open>Transformation_Order T U OO Transformation_Order U U = Transformation_Order T U\<close>
  \<open>Transformation_Order T T OO Transformation_Order T U = Transformation_Order T U\<close>
  unfolding Transformation_Order_def fun_eq_iff relcompp.simps Transformation_def
  by clarsimp blast+

lemma
  \<open>Transformation_Order S T OO Transformation_Order T U \<le> Transformation_Order S U \<close>
  unfolding Transformation_Order_def fun_eq_iff relcompp.simps Transformation_def
  by clarsimp

lemma exists_family_for_any_decoding:
  \<open>\<exists>fs. family_decode fs = f\<close>
  unfolding fun_eq_iff family_decode_def
  by (rule exI[where x=\<open>{ (\<lambda>a. if f a y then Some y else None) | y. True }\<close>],
      clarsimp,
      smt (verit, best) option.distinct(1) option.sel)

lemma Existence_of_Complete_Transformation:
  \<open>\<exists>f. Complete_Transformation T U f\<close>
  unfolding Complete_Transformation_def
  by (rule exI[where x=\<open>Transformation_Order T U\<close>]; simp add: Transformation_Order_id)

theorem Existence_of_Complete_Transformation':
  \<open>\<exists>fs. Complete_Transformation' T U fs\<close>
  unfolding Complete_Transformation'_def
  by (insert Existence_of_Complete_Transformation[of T U],
      smt (verit, ccfv_SIG) exists_family_for_any_decoding)


section \<open>Analysis Properties\<close>

subsection \<open>Object_Equiv\<close>

lemma \<comment>\<open>\<open>Object_Equiv\<close> gives lower approximation of the \<open>Transformation_Order T T\<close>\<close>
  \<open>Object_Equiv T eq \<Longrightarrow> eq \<le> Transformation_Order T T\<close>
  unfolding Object_Equiv_def Transformation_Order_def
  by clarsimp

subsection \<open>Transformation Functor\<close>


definition Complete_Transformation_Functor
  where \<open>Complete_Transformation_Functor F2 F2 T U D R mapper \<longleftrightarrow>
            Transformation_Functor F1 F2 T U D R mapper \<and>
            (\<forall>r. )\<close>
(*TODO!, shall use \<S> for analysing TF*)

(*TODO: *)
lemma Completeness_of_the_conversion_from_FT_to_FTF:
  \<open>\<dots>?\<close>
  sorry

end