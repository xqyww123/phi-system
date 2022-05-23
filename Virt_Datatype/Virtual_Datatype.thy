theory Virtual_Datatype
  imports "../Statespace/StateSpaceLocale"
  keywords "virtual_datatype" :: thy_decl
begin

locale "virtual_datatype" =
  fixes CONS_OF :: "'value \<Rightarrow> 'CONS"
begin
lemma VDT_distinct[simp]: "CONS_OF x \<noteq> CONS_OF y \<Longrightarrow> x \<noteq> y" by blast
end


locale project_inject_VDT = project_inject _ inject
  for inject :: "'a \<Rightarrow> 'value"
  + fixes CONS :: 'CONS
      and CONS_OF :: "'value \<Rightarrow> 'CONS"
    assumes VDT_cons[simp]: "CONS_OF (inject x) = CONS"
begin
definition "is_instance v \<longleftrightarrow> (\<exists>x. v = inject x)"

lemma is_instanceE[elim!]: "is_instance v \<Longrightarrow> (\<And>x. v = inject x \<Longrightarrow> C) \<Longrightarrow> C"
  using is_instance_def by blast

lemma [simp]: "is_instance (inject v)" using is_instance_def by blast

lemma [simp]: "is_instance v \<Longrightarrow> CONS_OF v = CONS"
  using VDT_cons is_instance_def by force

lemma [simp]: "is_instance v \<Longrightarrow> inject (project v) = v"
  using is_instance_def project_inject_cancel by fastforce 

end


ML_file_debug \<open>Virtual_Datatype.ML\<close>


end