theory Indirect_Type
  imports "Virt_Datatype/Virtual_Datatype"
begin

type_synonym type_id = nat
datatype 'TY itype = iType 'TY | iTypeRef type_id

locale Indirect_Type =
  fixes Type_Table :: \<open>type_id \<Rightarrow> (string \<times> 'TY) option\<close>
begin

definition \<open>unwind_iType ty = (case ty of iType t \<Rightarrow> t | iTypeRef i \<Rightarrow> snd (the (Type_Table i)))\<close>

lemma unwind_iType[simp]:
  \<open>unwind_iType (iType ty) = ty\<close>
  unfolding unwind_iType_def by simp

end

locale Type_Definition =
  Indirect_Type Type_Table
  for Type_Table :: \<open>type_id \<Rightarrow> (string \<times> 'TY) option\<close>
+ fixes name :: string \<comment> \<open>should be unique\<close>
    and expr :: 'TY
assumes "__ex__": \<open>\<exists>id. Type_Table id = Some (name, expr)\<close>
begin

definition id where \<open>id = (@id. Type_Table id = Some (name, expr))\<close>

lemma expand[simp]:
  \<open>Type_Table id = Some (name, expr)\<close>
  by (metis (mono_tags, lifting) "__ex__" local.id_def someI_ex)

lemma unwind[simp]:
  \<open>unwind_iType (iTypeRef id) = expr\<close>
  unfolding unwind_iType_def by simp

end

end