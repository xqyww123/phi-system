theory NuInstructions
  imports NuPrime NuSys
begin

section \<open>Common Instructions\<close>

subsection \<open>Drop & Duplicate Value\<close>

context \<phi>empty begin

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?x \<Ztypecolon> Val ?raw ?T \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_dup\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> Val raw T \<longmapsto> x \<Ztypecolon> Val raw T \<heavy_comma> x \<Ztypecolon> Val raw T \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_dup\<close>
  unfolding View_Shift_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_drop\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w Void \<heavy_comma> x \<Ztypecolon> Val raw T \<longmapsto> Void \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_drop\<close>
  unfolding View_Shift_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)

end

subsection \<open>Exception\<close>

text \<open>The opcode for throwing an exception is directly \<^term>\<open>Exception\<close>\<close>

definition \<open>throw raw = det_lift (Exception raw)\<close>

lemma (in \<phi>fiction) throw_\<phi>app[\<phi>reason! for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c throw ?excep \<lbrace> ?X \<longmapsto> ?Any \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?X' \<rbrace>\<close>]:
  \<open> (\<And>v. PROP Filter_Out_Free_Values (X v) (X' v))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c throw excep \<lbrace> X excep \<longmapsto> 0 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s X' \<rbrace>\<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Filter_Out_Free_Values_def Imply_def
  apply clarsimp
  by (meson Imply_def View_Shift_def view_shift_by_implication)

definition op_try :: "('ret,'ex,'RES_N,'RES) proc
                    \<Rightarrow> ('ex sem_value \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc)
                    \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc"
  where \<open>op_try f g s = \<Union>((\<lambda>y. case y of Success x s' \<Rightarrow> {Success x s'} | Exception v s' \<Rightarrow> g v s'
                                   | PartialCorrect \<Rightarrow> {PartialCorrect} | Invalid \<Rightarrow> {Invalid}) ` f s)\<close>

lemma (in \<phi>empty) "__op_try__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>v. E v) \<rbrace>
\<Longrightarrow> (\<And>v. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g v \<lbrace> E v \<longmapsto> Y2 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_try f g \<lbrace> X \<longmapsto> \<lambda>v. Y1 v + Y2 v \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace> \<close>
  unfolding op_try_def \<phi>Procedure_def subset_iff
  apply clarsimp subgoal for comp R x s
    apply (cases s; simp; cases x; clarsimp simp add: \<phi>expns ring_distribs)
    subgoal premises prems for a b u v
      using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
      by (metis (no_types, lifting) INTERP_COM LooseStateTy_expn(1) prems(3) prems(6) prems(7) prems(8) prems(9) set_mult_expn)
    subgoal premises prems for a b c d u v2 proof -
      have \<open>Exception a b \<in> \<S> (\<lambda>v. INTERP_COM (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_COM (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Success c d \<in> \<S> (\<lambda>v. INTERP_COM (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_COM (R \<heavy_comma> E2 v))\<close>
        using prems(2)[of a, THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_COM prems(4) set_mult_expn)
      note this[simplified]
      then show ?thesis
        by (metis INTERP_COM prems(11) set_mult_expn)
    qed
    subgoal premises prems for a b c d u v proof -
      have \<open>Exception a b \<in> \<S> (\<lambda>v. INTERP_COM (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_COM (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Exception c d \<in> \<S> (\<lambda>v. INTERP_COM (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_COM (R \<heavy_comma> E2 v))\<close>
        using prems(2)[THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_COM prems(4) set_mult_expn)
      note this[simplified]
      then show ?thesis
        by (simp add: INTERP_COM set_mult_expn)
    qed
    apply (smt (z3) INTERP_COM LooseStateTy_expn(2) LooseStateTy_expn(3) set_mult_expn)
    by blast .

definition "Union_the_Same_Or_Arbitrary_when_Var Z X Y \<longleftrightarrow> (\<forall>v. (Z::'v \<Rightarrow> 'a set) v = X v + Y v)"

lemma Union_the_Same_Or_Arbitrary_when_Var__the_Same:
  \<open>Union_the_Same_Or_Arbitrary_when_Var Z Z Z\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by simp

lemma Union_the_Same_Or_Arbitrary_when_Var__Arbitrary:
  \<open>Union_the_Same_Or_Arbitrary_when_Var (\<lambda>v. X v + Y v) X Y\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by blast

\<phi>reasoner_ML Union_the_Same_Or_Arbitrary_when_Var 1200
  (conclusion \<open>Union_the_Same_Or_Arbitrary_when_Var ?Z ?X ?Y\<close>) = \<open>
fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Union_the_Same_Or_Arbitrary_when_Var\<close>, _)
          $ Z $ _ $ _) = Thm.major_prem_of sequent
  in (ctxt,
        (if is_Var (Envir.beta_eta_contract Z)
         then @{thm Union_the_Same_Or_Arbitrary_when_Var__Arbitrary}
         else @{thm Union_the_Same_Or_Arbitrary_when_Var__the_Same})
        RS sequent) |> Seq.single
  end
\<close>

proc (in \<phi>empty) (nodef) try'':
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> YY \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  assumes G: \<open>(\<And>v. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g v \<lbrace> E v \<longmapsto> YY \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s EE2 \<rbrace>)\<close>
  argument X
  return YY
  throws EE2
  \<medium_left_bracket> "__op_try__" F G \<medium_right_bracket>. .

proc (in \<phi>empty) (nodef) try':
  assumes A: \<open>Union_the_Same_Or_Arbitrary_when_Var Z Y1 Y2\<close>
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  assumes G: \<open>\<And>v. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g v \<lbrace> E v \<longmapsto> Y2 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>\<close>
  argument X
  return Z
  throws E2
  \<medium_left_bracket> "__op_try__" F G 
      unfold A[unfolded Union_the_Same_Or_Arbitrary_when_Var_def, THEN spec, symmetric]
  \<medium_right_bracket>. .


subsection \<open>Access the Resource\<close>

subsubsection \<open>Legacy\<close>

definition (in \<phi>resource_sem)
    \<phi>M_get_res :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc) \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res R F = (\<lambda>res. F (R res) res)\<close>

definition (in \<phi>resource_sem)
    \<phi>M_get_res_entry :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('k \<rightharpoonup> 'a)) \<Rightarrow> 'k \<Rightarrow> ('a \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc) \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res_entry R k F =
    \<phi>M_get_res R (\<lambda>res. case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition (in \<phi>resource_sem) \<phi>M_set_res :: \<open>
    (('x \<Rightarrow> 'x) \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'RES_N \<Rightarrow> 'RES)
      \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> (unit,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_set_res Updt F = (\<lambda>res. {Success (sem_value ()) (Updt F res)})\<close>

subsubsection \<open>Getters\<close>

paragraph \<open>fine_resource\<close>

definition (in resource)
    \<phi>R_get_res :: \<open>('T \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc) \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_get_res F = (\<lambda>res. F (get res) res)\<close>

lemma (in resource) \<phi>R_get_res[\<phi>reason!]:
  \<open> get res = v
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_def subset_iff by simp

paragraph \<open>nonsepable_mono_resource\<close>

definition (in nonsepable_mono_resource)
    \<phi>R_get_res_entry :: \<open>('T \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc) \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_get_res_entry F = \<phi>R_get_res (\<lambda>v. case v of Some v' \<Rightarrow> F (nonsepable.dest v') | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in nonsepable_mono_resource) \<phi>R_get_res_entry:
  \<open> get res = Some (nonsepable v)
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

paragraph \<open>partial_map_resource\<close>

definition (in partial_map_resource)
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> ('val \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc) \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_get_res_entry k F = \<phi>R_get_res (\<lambda>res.
    case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in partial_map_resource) \<phi>R_get_res_entry[\<phi>reason!]:
  \<open> get res k = Some v
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry k F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

subparagraph \<open>share_fiction_for_partial_mapping_resource\<close>



lemma (in share_fiction_for_partial_mapping_resource) \<phi>R_get_res_entry[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_get_res_entry key F
      \<lbrace> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def del: subsetI)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

paragraph \<open>partial_map_resource2\<close>

definition (in partial_map_resource2)
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> ('val \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc) \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_get_res_entry k k2 F = \<phi>R_get_res (\<lambda>res.
    case res k k2 of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in partial_map_resource2) \<phi>R_get_res_entry[\<phi>reason!]:
  \<open> get res k k2 = Some v
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry k k2 F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def del: subsetI)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry1[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  using \<phi>R_get_res_entry[where n=1, simplified] .


subsubsection \<open>Setters\<close>

paragraph \<open>fine_resource\<close>

definition (in resource) \<phi>R_set_res :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> (unit,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_set_res F = (\<lambda>res. {Success (sem_value ()) (updt F res)})\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_set_res:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := u))}) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__" del: set_mult_expn)

lemma (in share_fiction_for_partial_mapping_resource) "\<phi>R_set_res":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k \<mapsto> u) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def
          expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
          expand_subj[where x=\<open>1(k \<mapsto> u)\<close>, simplified] simp del: set_mult_expn
          del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_set_res[where k=k and res=res], assumption,
        simp add: \<phi>Res_Spec_mult_homo, assumption) .


paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_set_res[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> \<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 := u)))}) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__" del: set_mult_expn)

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_set_res":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k) m \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k := 1(k2 \<mapsto> v)))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k)
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def
                            expand[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close>, simplified]
                            expand_subj[where x=\<open>1(k := 1(k2 \<mapsto> u))\<close>, simplified]
                  simp del: set_mult_expn
                  del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_set_res, assumption, simp add: \<phi>Res_Spec_mult_homo, assumption) .


subsubsection \<open>Dispose\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_dispose_res[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (1(k \<mapsto> any))})
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := None)) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__" \<phi>Res_Spec_mult_homo)

lemma (in share_fiction_for_partial_mapping_resource) "\<phi>R_dispose_res":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k := None))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
                  simp del: set_mult_expn del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_dispose_res, assumption, simp add: \<phi>Res_Spec_mult_homo, simp add: \<phi>Res_Spec_mult_homo) .


paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_dispose_res[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in> Valid)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (1(k := any))})
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := 1)) res \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__" \<phi>Res_Spec_mult_homo)

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_dispose_res":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := 1) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k := f))})
      \<Longrightarrow> P (R.get res) \<and> dom f = dom (R.get res k))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k := 1))
         \<lbrace> to_share o f \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k := f)\<close>, simplified]
                            \<phi>Res_Spec_mult_homo
                  simp del: set_mult_expn del: subsetI)
  subgoal for r res
    apply (rule R.\<phi>R_dispose_res, assumption, standard, simp)
    subgoal premises prems proof -
      have t1: \<open>dom f = dom (R.get res k)\<close>
        using prems(2) prems(3) by blast
      have t2: \<open>f \<subseteq>\<^sub>m R.get res k\<close>
        using R.raw_unit_assertion_implies' prems(3) by blast
      have t3: \<open>R.get res k = f\<close>
        by (metis (no_types, lifting) map_le_antisym map_le_def t1 t2)
      show ?thesis
        using prems(3) t3 \<phi>Res_Spec_mult_homo by blast
    qed . .

subsubsection \<open>Allocate\<close>

definition (in mapping_resource)
    \<phi>R_allocate_res_entry :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> ('key \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc)
                           \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_allocate_res_entry P init F =
    \<phi>R_get_res (\<lambda>res.
    let k = (@k. res k = 1 \<and> P k)
     in \<phi>R_set_res (\<lambda>f. f(k := init))
        \<ggreater> F k
)\<close>

lemma (in mapping_resource) \<phi>R_set_res_new[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> k \<notin> dom1 (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec (R * {mk (1(k := u))})) Any\<close>
  unfolding \<phi>R_set_res_def
  by (simp add: \<phi>expns "__new_rule__" \<phi>Res_Spec_mult_homo del: set_mult_expn)

lemma (in mapping_resource) \<phi>R_allocate_res_entry[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in> Valid \<longrightarrow> m(k := init) \<in> Valid)
\<Longrightarrow> (\<And>k res. res \<in> \<phi>Res_Spec (R * {mk (1(k := init))} \<^bold>s\<^bold>u\<^bold>b\<^bold>j P k)
      \<Longrightarrow> F k res \<subseteq> \<S> Y E)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> \<phi>R_allocate_res_entry P init F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_allocate_res_entry_def \<phi>R_get_res_def
  subgoal premises prems proof -
    let ?m = \<open>get res\<close>
    define k' where \<open>k' = (SOME k. ?m k = 1 \<and> P k)\<close>
    have \<open>\<exists>k'. ?m k' = 1 \<and> P k'\<close>
      using get_res_Valid prems(1) prems(4) by blast
    note this[THEN someI_ex]
    then have t1[simp]: \<open>?m k' = 1 \<and> P k'\<close> unfolding k'_def by blast
    show ?thesis
      unfolding k'_def[symmetric]
      apply (simp, rule \<phi>M_RS_WP_SEQ, rule \<phi>R_set_res_new)
      using prems(2) t1 apply blast
      apply (simp add: dom1_def)
      using \<open>res \<in> \<phi>Res_Spec _\<close> apply this
      by (simp add: prems(3))
  qed .



(*


(*
subsection \<open>Tuple Operations\<close>



subsubsection \<open>Construct Tuple\<close>

definition cons_tup :: "'TY list \<Rightarrow> 'VAL list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "cons_tup tys vs = (
    let N = length tys in
    \<phi>M_assert (N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (rev (take N vs)) tys)
    \<ggreater> Success (V_tup.mk (rev (take N vs))))"

lemma cons_tup_nil:
  \<open>cons_tup [] = \<phi>M_put_Val (V_tup.mk [])\<close>
  unfolding cons_tup_def \<phi>M_put_Val_def
  by simp

lemma cons_tup_cons:
  \<open>cons_tup (TY#TYs) =
    cons_tup TYs \<ggreater>
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (V_tup.mk [v] * tup)
    ))\<close>
  apply (auto split: list.split
    simp add: cons_tup_def fun_eq_iff pair_forall instr_comp_def bind_def
    \<phi>M_get_Val_def \<phi>M_assert_def \<phi>M_put_Val_def Let_def V_tup_mult)
  apply (metis Suc_le_eq list.sel(1) take_hd_drop)
  apply (metis Cons_nth_drop_Suc Suc_le_eq list.sel(3))
  apply (metis Suc_le_eq drop_all leI list.simps(3))
  apply (metis (no_types, lifting) drop_all leI list.ctr_transfer(1) list.sel(1) list.simps(3) list_all2_Cons2 list_all2_appendI list_all2_rev1 rev.simps(2) take_hd_drop)
  apply (smt (verit, del_insts) Suc_le_eq append1_eq_conv list.sel(1) list_all2_Cons2 rev_eq_Cons_iff take_hd_drop)
  by (simp add: take_Suc_conv_app_nth)

lemma (in \<phi>empty) op_cons_tup_nil:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup [] \<lbrace> Void \<longmapsto> () \<Ztypecolon> EmptyTuple \<rbrace>\<close>
  unfolding cons_tup_nil by \<phi>reason

lemma (in \<phi>empty) op_cons_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup TYs \<lbrace> X \<longmapsto> VAL y \<Ztypecolon> Y \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup (TY#TYs) \<lbrace> VAL a \<Ztypecolon> A\<heavy_comma> X \<longmapsto> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> Y) \<rbrace>\<close>
  unfolding cons_tup_cons
  apply \<phi>reason apply (rule \<phi>frame0, assumption)
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  apply \<phi>reason apply (simp add: \<phi>expns) by blast


subsubsection \<open>Destruct Tuple\<close>


definition op_dest_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_dest_tup tys =
    \<phi>M_getV (\<tau>Tuple tys) V_tup.dest (\<lambda>tup.
    \<lambda>(vs, res). Success (rev tup@vs, res))"

lemma op_dest_tup_nil_expn:
  \<open>op_dest_tup [] = \<phi>M_getV (\<tau>Tuple []) V_tup.dest (\<lambda>_. SKIP)\<close>
  by (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)

lemma op_dest_tup_cons_expn:
  \<open>op_dest_tup (TY#TYs) =
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_assert (\<exists>h tup'. tup = V_tup.mk (h#tup') \<and> h \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (hd (V_tup.dest tup)) \<ggreater>
    \<phi>M_put_Val (V_tup.mk (tl (V_tup.dest tup))) \<ggreater>
    op_dest_tup TYs)\<close>
  apply (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)
  by (metis list.discI list.exhaust_sel list.rel_sel list.sel(1))

lemma (in \<phi>empty) op_dest_tup_nil:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup [] \<lbrace> () \<Ztypecolon> EmptyTuple \<longmapsto> Void \<rbrace> \<close>
  unfolding op_dest_tup_nil_expn by \<phi>reason

lemma (in \<phi>empty) op_dest_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup TYs \<lbrace> VAL y \<Ztypecolon> Y \<longmapsto> X \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup (TY#TYs) \<lbrace> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> \<phi>Is_Tuple Y) \<longmapsto> VAL a \<Ztypecolon> A\<heavy_comma> X \<rbrace>\<close>
  unfolding op_dest_tup_cons_expn
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  by (rule \<phi>frame0, assumption)



subsubsection \<open>Accessing Elements\<close>


definition op_get_element :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_element idx TY =
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx) \<ggreater>
    \<phi>M_put_Val (index_value idx v))"

definition op_set_element :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_element idx TY =
    \<phi>M_get_Val (\<lambda>u.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx \<and> u \<in> Well_Type (index_type idx TY)) \<ggreater>
    \<phi>M_put_Val (index_mod_value idx (\<lambda>_. u) v)
  ))"

lemma (in \<phi>empty) op_get_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_element idx TY \<lbrace> VAL x \<Ztypecolon> X \<longmapsto> VAL f x \<Ztypecolon> Y \<rbrace> \<close>
  unfolding op_get_element_def \<phi>Index_getter_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason

lemma (in \<phi>empty) op_set_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> Y) (index_type idx TY)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_element idx TY \<lbrace> VAL x \<Ztypecolon> X\<heavy_comma> VAL y \<Ztypecolon> Y \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> X \<rbrace>\<close>
  unfolding op_set_element_def \<phi>Index_mapper_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
   apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason


*)

*)

end
