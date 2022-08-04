theory NuInstructions
  imports NuPrime NuLLReps
begin

section \<open>A Set of Predefined Minimal Instructions\<close>

context std_sem begin

subsection \<open>Throw Exception\<close>

text \<open>The opcode for throwing an exception is directly \<^term>\<open>Exception\<close>\<close>

lemma (in std) throw_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c Exception \<lbrace> X \<longmapsto> (\<lambda>_::unreachable sem_value. 0) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s X \<rbrace>\<close>
  unfolding \<phi>Procedure_def by blast

subsection \<open>Try-Catch\<close>

definition op_try :: "('ret,'RES_N,'RES) proc \<Rightarrow> ('ret,'RES_N,'RES) proc \<Rightarrow> ('ret,'RES_N,'RES) proc"
  where \<open>op_try f g s = (case f s of Success x s' \<Rightarrow> Success x s' | Exception s' \<Rightarrow> g s'
                                   | PartialCorrect \<Rightarrow> PartialCorrect | Fail \<Rightarrow> Fail)\<close>

lemma (in std) "__op_try__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> E \<longmapsto> Y2 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_try f g \<lbrace> X \<longmapsto> \<lambda>v. Y1 v + Y2 v \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace> \<close>
  unfolding op_try_def \<phi>Procedure_def 
  by (auto 2 5 simp add: ring_distribs)

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

declare [ [\<phi>not_define_new_const] ]

declare [ [\<phi>trace_processing] ]

proc (in std) try'':
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> YY \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> E \<longmapsto> YY \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s EE2 \<rbrace>\<close>
  argument X
  return YY
  throws EE2
  \<medium_left_bracket> ;; "__op_try__"  ;; F G \<medium_right_bracket>. .

proc (in std) try':
  assumes A: \<open>Union_the_Same_Or_Arbitrary_when_Var Z Y1 Y2\<close>
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> E \<longmapsto> Y2 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>\<close>
  argument X
  return Z
  throws E2
  \<medium_left_bracket> "__op_try__" F G 
    unfold A[unfolded Union_the_Same_Or_Arbitrary_when_Var_def, THEN spec, symmetric]
  \<medium_right_bracket>. .

declare [ [\<phi>not_define_new_const = false] ]


subsection \<open>Arithmetic Operations\<close>

subsubsection \<open>Integer arithmetic\<close>

definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_int bits const = Success (sem_value (V_int.mk (bits,const)))"

definition op_const_size_t :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_size_t c = \<phi>M_assume (c < 2 ^ addrspace_bits)
                          \<ggreater> Success (sem_value (V_int.mk (addrspace_bits,c)))"
  \<comment> \<open> `op_const_size_t` checks the overflow during the compilation towards certain decided platform.  \<close>

definition op_add :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'RES_N, 'RES) M"
  where "op_add bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Success (sem_value (V_int.mk (bits, ((val_a + val_b) mod 2^bits))))
  )))"


(* lemma (in std) op_add:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b (\<phi>V_pair vb va) \<lbrace> x \<Ztypecolon> Val va \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vb \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def Premise_def
  by (cases va; cases vb; simp, \<phi>reason) *)


(* lemma (in std)
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c left  \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c right \<lbrace> R2 \<longmapsto> R3\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (left \<ggreater> right \<ggreater> op_add b) \<lbrace> R1 \<longmapsto> R3\<heavy_comma> SYNTHESIS x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  apply (\<phi>reason, assumption) *)

definition op_sub :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'RES_N, 'RES) M"
  where "op_sub bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Success (sem_value (V_int.mk (bits, ((2^bits + val_b - val_a) mod 2^bits))))
  )))"

definition op_umul :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'RES_N, 'RES) M"
  where "op_umul bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Success (sem_value (V_int.mk (bits, ((val_b * val_a) mod 2^bits))))
  )))"

definition op_udiv :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL, 'RES_N, 'RES) M"
  where "op_udiv bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Success (sem_value (V_int.mk (bits, (val_b div val_a))))
  )))"

definition op_lt :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL,'RES_N,'RES) M"
  where "op_lt bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Success (sem_value (V_int.mk (1, (if val_b < val_a then 1 else 0))))
  )))"


definition op_le :: "nat \<Rightarrow> ('VAL \<times> 'VAL, 'VAL,'RES_N,'RES) M"
  where "op_le bits =
      \<phi>M_caseV (\<lambda>va vb.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) va (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) vb (\<lambda>val_b.
      Success (sem_value (V_int.mk (1, (if val_b \<le> val_a then 1 else 0))))
  )))"


definition op_not :: "('VAL, 'VAL,'RES_N,'RES) M"
  where "op_not v =
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) v (\<lambda>v.
    Success (sem_value (V_int.mk (1, 1 - v)))
  )"

definition op_and :: "('VAL \<times> 'VAL, 'VAL,'RES_N,'RES) M"
  where "op_and =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) va (\<lambda>v.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) vb (\<lambda>u.
    Success (sem_value (V_int.mk (1, v+u-1)))
  )))"

definition op_or :: "('VAL \<times> 'VAL, 'VAL,'RES_N,'RES) M"
  where "op_or =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) va (\<lambda>v.
    \<phi>M_getV (\<tau>Int 1) (snd o V_int.dest) vb (\<lambda>u.
    Success (sem_value (V_int.mk (1, min 1 (v+u))))
  )))"

definition op_equal :: "'TY \<Rightarrow> ('VAL \<times> 'VAL, 'VAL,'RES_N,'RES) M"
  where "op_equal TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV TY id va (\<lambda>v.
    \<phi>M_getV TY id vb (\<lambda>u.
    (\<lambda>res. \<phi>M_assert (Can_EqCompare res u v) res) \<ggreater>
    Success (sem_value (V_int.mk (1, (if EqCompare u v then 1 else 0))))
)))"


subsection \<open>Access the Resource\<close>

definition \<phi>M_get_res :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'a ?) \<Rightarrow> ('a \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res R F = (\<lambda>res. F (the_fine (R res)) res)\<close>

definition \<phi>M_get_res_entry :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('k \<rightharpoonup> 'a) ?) \<Rightarrow> 'k \<Rightarrow> ('a \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res_entry R k F = \<phi>M_get_res R (\<lambda>res.
    case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. Fail))\<close>

definition \<phi>M_set_res_entry :: \<open>
    ((('k \<rightharpoonup> 'v) ? \<Rightarrow> ('k \<rightharpoonup> 'v) ?) \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'RES_N \<Rightarrow> 'RES)
      \<Rightarrow> (('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v)) \<Rightarrow> (unit,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_set_res_entry Updt F = (\<lambda>res.
    Success (sem_value ()) (Updt (map_fine F) res))\<close>


subsubsection \<open>Variable Operations\<close>

definition \<phi>M_get_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc"
  where "\<phi>M_get_var vname TY F = \<phi>M_get_res_entry (R_var.get) vname (\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type TY) \<ggreater> F val)"

definition op_get_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_var vname TY = \<phi>M_get_var vname TY (\<lambda>x. Success (sem_value x))"

definition op_set_var :: "varname \<Rightarrow> 'TY \<Rightarrow> ('VAL, unit, 'RES_N, 'RES) M"
  where "op_set_var vname TY v =
          \<phi>M_getV TY id v (\<lambda>v.
          \<phi>M_get_var vname TY (\<lambda>_.
          \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname := Some v))))"

definition op_free_var :: "varname \<Rightarrow> (unit,'RES_N,'RES) proc"
  where "op_free_var vname = \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname := None))"

definition op_var_scope' :: "'TY
                          \<Rightarrow> (varname \<Rightarrow> ('ret,'RES_N,'RES) proc)
                          \<Rightarrow> ('VAL,'ret,'RES_N,'RES) M"
  where "op_var_scope' TY F v =
    \<phi>M_getV TY id v (\<lambda>v.
    \<phi>M_get_res R_var.get (\<lambda>f.
    let vname = (@vname. f vname = None) in
    \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname := Some v)) \<ggreater>
    F vname
  ))"

lemma (in std) \<phi>M_get_var[\<phi>reason!]:
  \<open>v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_var vname TY F \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_get_var_def \<phi>M_get_res_entry_def \<phi>M_get_res_def
  apply (simp add: \<phi>expns R_var.prj.homo_mult times_list_def)
  apply (subst R_var_valid_split)
  apply (auto simp add: \<phi>expns FIC_var_split times_set_def R_var.mult_in_dom mult_strip_fine_011 times_fine times_list_def)
  subgoal premises prems for R fic res vars
  proof -
    note [simp] = \<open>vars ## 1(vname \<mapsto> v)\<close> [THEN sep_disj_fun[where x=vname], simplified]
    note F = \<open>\<forall>_ _. _ \<longrightarrow> F v _ \<in> _\<close>[THEN spec[where x=\<open>res * R_var.mk (Fine (1(vname \<mapsto> v)))\<close>],
                                       THEN spec[where x=R], THEN mp]
    show ?thesis
      apply (simp add: times_fun)
      apply (rule \<phi>M_assert', rule \<open>v \<in> Well_Type TY\<close>, rule F,
             rule exI[where x=\<open>fic * FIC_var.mk (Fine (1(vname \<mapsto> v)))\<close>])
      using prems apply (auto simp add: FIC_var_split times_set_def)
      apply (subst R_var_valid_split)
      apply (auto simp add: R_var.inj_homo_mult[symmetric] times_fine)
      done
  qed
  done

lemma (in std) \<phi>M_set_var[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_set_res_entry R_var.updt (\<lambda>f. f(vname \<mapsto> u)) \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011 times_list_def)
  subgoal premises prems for R fic res vars
  proof -
    note [simp] = \<open>vars ## 1(vname \<mapsto> v)\<close> [THEN sep_disj_fun[where x=vname], simplified]
    have [simp]: \<open>(vars * 1(vname \<mapsto> v))(vname \<mapsto> u) = vars * 1(vname \<mapsto> u)\<close>
      unfolding times_fun_def fun_eq_iff fun_upd_def by simp
    from \<open>vars ## 1(vname \<mapsto> v)\<close> have [simp]: \<open>vars ## 1(vname \<mapsto> u)\<close>
      unfolding sep_disj_fun_def by simp
    show ?thesis
      apply (rule exI[where x=\<open>fic * FIC_var.mk (Fine (1(vname \<mapsto> u))) \<close>])
      apply (auto simp add: R_var_valid_split' FIC_var_split times_set_def prems)
      apply (rule exI[where x = res])
      by (auto simp add: fun_eq_iff times_fun prems R_var.inj_homo_mult[symmetric] times_fine)
  qed
  done


lemma (in std) op_get_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var vname TY \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> v \<Ztypecolon> Var vname Identity \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding op_get_var_def Premise_def
  by (\<phi>reason, assumption, \<phi>reason)
end


lemma (in std) op_set_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_var vname TY rawv \<lbrace> v \<Ztypecolon> Var vname Identity\<heavy_comma> u \<Ztypecolon> Val rawv Identity \<longmapsto> u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding op_set_var_def Premise_def
  by (cases rawv; simp, \<phi>reason, assumption, simp add: \<phi>expns, \<phi>reason)


lemma (in std) op_var_scope':
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> (\<And>vname. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F vname \<lbrace> X\<heavy_comma> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> )
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope' TY F rawv \<lbrace> X\<heavy_comma> v \<Ztypecolon> Val rawv Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding op_var_scope'_def Premise_def
  apply (cases rawv; simp, \<phi>reason, simp add: \<phi>expns)
  unfolding \<phi>Procedure_def
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def \<phi>M_get_res_def Let_def bind_def
  apply (simp add: \<phi>expns)
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011 times_list_def)
  subgoal premises prems for res R ficR ficX vars
  proof -
    note t1 = finite_map_freshness[OF \<open>finite (dom vars)\<close>, OF infinite_varname]
    have t2[simp]: \<open>vars ## 1(SOME fic. vars fic = None \<mapsto> v)\<close>
      unfolding sep_disj_fun_def by simp (meson someI t1)
    have t3[simp]: \<open>vars (SOME vname. vars vname = None) = None\<close>
      by (meson someI t1)
    show ?thesis
      apply (rule \<open>\<forall>a. _\<close>[of \<open>(SOME vname. vars vname = None)\<close>,
        THEN spec, THEN spec, THEN mp])
      apply (rule exI[where x=\<open>ficR * ficX * FIC_var.mk (Fine (1((@x. vars x = None) \<mapsto> v))) \<close>])
      apply (auto simp add: \<phi>expns R_var_valid_split' FIC_var_split times_set_def prems)
      using \<open>ficR \<in> R\<close> \<open>ficX \<in> X\<close> apply (smt (verit) fun_mult_norm) 
      apply (rule exI[where x = res])
      by (simp add: fun_eq_iff times_fun prems R_var.inj_homo_mult[symmetric] times_fine)
  qed
  done

lemma (in std) op_free_var:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_var vname \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> 1 \<rbrace>\<close>
  unfolding op_free_var_def \<phi>Procedure_def \<phi>M_set_res_entry_def
  apply (auto simp add: \<phi>expns R_var_valid_split' R_var.prj.homo_mult FIC_var_split
                        R_var.mult_in_dom mult_strip_fine_011 times_list_def)
  subgoal premises prems for R fic res vars
  proof -
    note [simp] = \<open>vars ## 1(vname \<mapsto> v)\<close> [THEN sep_disj_fun[where x=vname], simplified]
    have [simp]: \<open>(vars * 1(vname \<mapsto> v))(vname := None) = vars\<close>
      unfolding fun_upd_def fun_eq_iff times_fun by simp
    have [simp]: \<open>(res * R_var.mk (Fine (1(vname \<mapsto> v))))(R_var.name := R_var.inject (Fine vars)) = res\<close>
      by (simp add: times_fun_def fun_upd_def fun_eq_iff prems)
    show ?thesis
      apply (rule exI[where x=fic])
      by (auto simp add: prems)
  qed
  done






context std begin







subsection \<open>Branches & Loops\<close>

paragraph \<open>Non-Branching Selection\<close>

definition op_sel :: "'TY \<Rightarrow> ('VAL \<times> 'VAL \<times> 'VAL, 'VAL,'RES_N,'RES) M"
  where "op_sel TY =
    \<phi>M_caseV (\<lambda>vc. \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV (\<tau>Int 1) V_int.dest vc (\<lambda>c.
    \<phi>M_getV TY id va (\<lambda>a.
    \<phi>M_getV TY id vb (\<lambda>b.
    Success (sem_value (if snd c = 1 then b else a)))))))"

paragraph \<open>Branch\<close>

definition op_if :: "('ret,'RES_N,'RES) proc
                  \<Rightarrow> ('ret,'RES_N,'RES) proc
                  \<Rightarrow> ('VAL,'ret,'RES_N,'RES) M"
  where "op_if brT brF v =
    \<phi>M_getV (\<tau>Int 1) V_int.dest v (\<lambda>c. (if snd c = 1 then brT else brF))"

paragraph \<open>While Loop\<close>

inductive SemDoWhile :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> (unit,'RES_N,'RES) state \<Rightarrow> bool" where
  "f s = Success (sem_value (V_int.mk (1,0))) res \<Longrightarrow> SemDoWhile f s (Success (sem_value ()) res)"
| "f s = Success (sem_value (V_int.mk (1,1))) res \<Longrightarrow> SemDoWhile f res s'' \<Longrightarrow> SemDoWhile f s s''"
| "f s = Exception e \<Longrightarrow> SemDoWhile f s (Exception e)"
| "f s = PartialCorrect \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "f s = Fail \<Longrightarrow> SemDoWhile f s Fail"

lemma "\<nexists> y. SemDoWhile (\<lambda>res. Success (sem_value (V_int.mk (1,1))) res) res y"
  apply rule apply (elim exE) subgoal for y 
    thm SemDoWhile.induct
    apply (induct "(\<lambda>res. Success (sem_value (V_int.mk (1,1))) (res::'RES_N \<Rightarrow> 'RES))" res y
           rule: SemDoWhile.induct)
       apply simp_all
    done done

definition op_do_while :: "('VAL,'RES_N,'RES) proc \<Rightarrow> (unit,'RES_N,'RES) proc" where
  "op_do_while f s = (if (\<exists>y. SemDoWhile f s y) then The (SemDoWhile f s) else PartialCorrect)"

lemma SemDoWhile_deterministic:
  assumes "SemDoWhile c s s1"
      and "SemDoWhile c s s2"
    shows "s1 = s2"
proof -
  have "SemDoWhile c s s1 \<Longrightarrow> (\<forall>s2. SemDoWhile c s s2 \<longrightarrow> s1 = s2)"
    apply (induct rule: SemDoWhile.induct)
    by (subst SemDoWhile.simps, simp)+
  thus ?thesis
    using assms by simp
qed

lemma SemDoWhile_deterministic2:
    "SemDoWhile body s x \<Longrightarrow> The ( SemDoWhile body s) = x"
  using SemDoWhile_deterministic by blast


paragraph \<open>Recursion\<close>

inductive SemRec :: "(('a,'a,'RES_N,'RES) M \<Rightarrow> ('a,'a,'RES_N,'RES) M)
            \<Rightarrow> 'a sem_value \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('a,'RES_N,'RES) state \<Rightarrow> bool"
where
  SemRec_I0: "(\<And>g. F g x res = y) \<Longrightarrow> SemRec F x res y"
| SemRec_IS: "SemRec (F o F) x res y \<Longrightarrow> SemRec F x res y"

definition op_recursion :: "'TY list \<Rightarrow> 'TY list
                         \<Rightarrow> (('a,'a,'RES_N,'RES) M \<Rightarrow> ('a,'a,'RES_N,'RES) M)
                         \<Rightarrow> ('a,'a,'RES_N,'RES) M"
  where "op_recursion _ _ F x s = (if (\<exists>t. SemRec F x s t) then The (SemRec F x s) else PartialCorrect)"


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

lemma (in std) op_cons_tup_nil:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup [] \<lbrace> Void \<longmapsto> () \<Ztypecolon> EmptyTuple \<rbrace>\<close>
  unfolding cons_tup_nil by \<phi>reason

lemma (in std) op_cons_tup_cons:
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

lemma (in std) op_dest_tup_nil:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup [] \<lbrace> () \<Ztypecolon> EmptyTuple \<longmapsto> Void \<rbrace> \<close>
  unfolding op_dest_tup_nil_expn by \<phi>reason

lemma (in std) op_dest_tup_cons:
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

lemma (in std) op_get_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_element idx TY \<lbrace> VAL x \<Ztypecolon> X \<longmapsto> VAL f x \<Ztypecolon> Y \<rbrace> \<close>
  unfolding op_get_element_def \<phi>Index_getter_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason

lemma (in std) op_set_element:
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



end

end
