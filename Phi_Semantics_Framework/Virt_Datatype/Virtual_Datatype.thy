theory Virtual_Datatype
  imports "Phi_Statespace.StateFun"
  keywords "virtual_datatype" :: thy_decl
begin

locale "virtual_datatype" =
  fixes CONS_OF :: "'value \<Rightarrow> 'CONS_NAME"
begin

lemma [simp]: "CONS_OF x \<noteq> CONS_OF y \<equiv> True \<Longrightarrow> x \<noteq> y \<equiv> True"
  unfolding atomize_eq by blast

end

datatype ('CONS_NAME,'VAL,'T) Field =
  Field (name: 'CONS_NAME) (project: "'VAL \<Rightarrow> 'T") (inject: "'T \<Rightarrow> 'VAL")

hide_const (open) name project inject


locale project_inject =
  "virtual_datatype" CONS_OF
  for CONS_OF :: "'value \<Rightarrow> 'CONS_NAME"
+ fixes field :: "('CONS_NAME,'value,'a) Field"
assumes name_of[simp]: "CONS_OF (Field.inject field x) = Field.name field"
  and dest_mk[simp]: "Field.project field (Field.inject field x) = x"
begin

abbreviation "mk \<equiv> Field.inject field"
abbreviation "dest \<equiv> Field.project field"
abbreviation "name \<equiv> Field.name field"
definition "is_instance v \<longleftrightarrow> (\<exists>x. v = mk x)"

lemma dest_mk_id[simp]: "dest o mk = id"
  using dest_mk destr_contstr_comp_id by blast

lemma dest_mk_cancle[simp]: "f o dest o mk = f"
  by fastforce

lemma mk_inj[iff]: "mk x = mk y \<longleftrightarrow> x = y"
  by (metis dest_mk)

lemma is_instanceE[elim!]: "is_instance v \<Longrightarrow> (\<And>x. v = mk x \<Longrightarrow> C) \<Longrightarrow> C"
  using is_instance_def by blast

lemma is_instance_mk[simp,intro]: "is_instance (mk x)" using is_instance_def by blast

lemma not_constructor_not_instance[simp]: \<open>CONS_OF v \<noteq> name \<Longrightarrow> \<not> is_instance v \<equiv> True\<close>
  unfolding atomize_eq using name_of by blast
  
lemma is_instance_cons[simp]: "is_instance v \<Longrightarrow> CONS_OF v = name"
  using name_of is_instance_def by force

lemma is_instance_mk_dest[simp]: "is_instance v \<Longrightarrow> mk (dest v) = v"
  using is_instance_def dest_mk by fastforce 

end


ML_file_debug \<open>Virtual_Datatype.ML\<close>

hide_type  (open) Field
hide_const (open) Field

end