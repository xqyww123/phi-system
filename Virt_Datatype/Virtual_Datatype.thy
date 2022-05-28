theory Virtual_Datatype
  imports "../Statespace/StateFun"
  keywords "virtual_datatype" :: thy_decl
begin

locale "virtual_datatype" =
  fixes CONS_OF :: "'value \<Rightarrow> 'CONS"
begin

lemma [simp]: "CONS_OF x \<noteq> CONS_OF y \<Longrightarrow> x \<noteq> y" by blast

end

datatype ('CONS,'VAL,'T) Field =
  Field (cons_of: 'CONS) (project: "'VAL \<Rightarrow> 'T") (inject: "'T \<Rightarrow> 'VAL")

hide_const (open) cons_of project inject


locale project_inject =
  "virtual_datatype" CONS_OF
  for CONS_OF :: "'value \<Rightarrow> 'CONS"
+ fixes field :: "('CONS,'value,'a) Field"
assumes cons_of[simp]: "CONS_OF (Field.inject field x) = Field.cons_of field"
  and dest_mk[simp]: "Field.project field (Field.inject field x) = x"
begin

abbreviation "mk \<equiv> Field.inject field"
abbreviation "dest \<equiv> Field.project field"
abbreviation "cons \<equiv> Field.cons_of field"
definition "is_instance v \<longleftrightarrow> (\<exists>x. v = mk x)"

lemma dest_mk_id[simp]: "dest o mk = id"
  using dest_mk destr_contstr_comp_id by blast

lemma dest_mk_cancle[simp]: "f o dest o mk = f"
  by fastforce

lemma mk_inj[simp,iff]: "mk x = mk y \<longleftrightarrow> x = y"
  by (metis dest_mk)

lemma is_instanceE[elim!]: "is_instance v \<Longrightarrow> (\<And>x. v = mk x \<Longrightarrow> C) \<Longrightarrow> C"
  using is_instance_def by blast

lemma is_instance_mk[simp]: "is_instance (mk v)" using is_instance_def by blast

lemma is_instance_cons[simp]: "is_instance v \<Longrightarrow> CONS_OF v = cons"
  using cons_of is_instance_def by force

lemma is_instance_mk_dest[simp]: "is_instance v \<Longrightarrow> mk (dest v) = v"
  using is_instance_def dest_mk by fastforce 

end


ML_file_debug \<open>Virtual_Datatype.ML\<close>

hide_type (open) Field
hide_const (open) Field

end