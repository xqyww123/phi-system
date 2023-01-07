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

datatype ('CONS_NAME,'REP,'ABS) Field =
  Field (name: 'CONS_NAME) (project: "'REP \<Rightarrow> 'ABS") (inject: "'ABS \<Rightarrow> 'REP")

hide_const (open) name project inject

definition lift_Field :: \<open>('ABS \<Rightarrow> 'ABS')
                       \<Rightarrow> ('ABS' \<Rightarrow> 'ABS)
                       \<Rightarrow> ('CONS_NAME,'REP,'ABS) Field
                       \<Rightarrow> ('CONS_NAME,'REP,'ABS') Field\<close>
  where \<open>lift_Field f g field = (case field of Field name projector injector \<Rightarrow>
            Field name (f o projector) (injector o g))\<close>

lemma lift_Field[simp]:
  \<open>lift_Field f g (Field name projector injector) = Field name (f o projector) (injector o g)\<close>
  unfolding lift_Field_def by simp

locale VDT_field =
  fixes field :: "('CONS_NAME,'value,'a) Field"
  assumes dest_mk[simp]: "Field.project field (Field.inject field x) = x"
begin

abbreviation "mk \<equiv> Field.inject field"
abbreviation "dest \<equiv> Field.project field"
abbreviation "name \<equiv> Field.name field"

lemma dest_mk_id[simp]: "dest o mk = id"
  using dest_mk destr_contstr_comp_id by blast

lemma dest_mk_cancle[simp]: "f o dest o mk = f"
  by fastforce

lemma mk_inj[iff]: "mk x = mk y \<longleftrightarrow> x = y"
  by (metis dest_mk)

definition "domain = {v. (\<exists>x. v = mk x)}"

lemma in_domainE[elim!]: "v \<in> domain \<Longrightarrow> (\<And>x. v = mk x \<Longrightarrow> C) \<Longrightarrow> C"
  using domain_def by blast

lemma mk_in_domain[simp,intro]: "mk x \<in> domain" using domain_def by blast

end

lemma VDT_field_lift:
  \<open>(\<And>x. f (g x) = x) \<Longrightarrow> VDT_field field \<Longrightarrow> VDT_field (lift_Field f g field)\<close>
  unfolding VDT_field_def
  by (cases field; simp)


locale field_entry =
  "virtual_datatype" CONS_OF + VDT_field field
  for CONS_OF :: "'value \<Rightarrow> 'CONS_NAME"
  and field :: "('CONS_NAME,'value,'a) Field"
+ assumes name_of[simp]: "CONS_OF (Field.inject field x) = Field.name field"
begin

lemma not_constructor_not_instance[simp]:
  \<open>CONS_OF v \<noteq> name \<Longrightarrow> v \<notin> domain \<equiv> True\<close>
  unfolding atomize_eq using name_of by blast
  
lemma in_domain_cons[simp]: "v \<in> domain \<Longrightarrow> CONS_OF v = name"
  using name_of domain_def by force

lemma in_domain_mk_dest[simp]: "v \<in> domain \<Longrightarrow> mk (dest v) = v"
  using domain_def dest_mk by fastforce 

end

ML_file_debug \<open>Virtual_Datatype.ML\<close>

hide_type  (open) Field
hide_const (open) Field

end