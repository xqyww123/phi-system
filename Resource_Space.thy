theory Resource_Space
  imports Main "Statespace/StateFun" NoeMisc
  keywords "resource_space" :: thy_defn
begin

subsection \<open>Extensible Resource Declaration\<close>

datatype ('NAME,'REP,'T) Entry =
  Entry (name: 'NAME) (project: "'REP \<Rightarrow> 'T") (inject: "'T \<Rightarrow> 'REP")

hide_const (open) name project inject

locale project_inject =
  inj: homo_mult \<open>Entry.inject entry\<close> + prj: homo_mult \<open>Entry.project entry\<close>
  for entry :: "('NAME, 'REP::comm_monoid_mult, 'T::comm_monoid_mult) Entry"
+ assumes proj_inj[simp]: "Entry.project entry (Entry.inject entry x) = x"
begin

abbreviation "name \<equiv> Entry.name entry"
abbreviation "inject \<equiv> Entry.inject entry"
abbreviation "project \<equiv> Entry.project entry"
abbreviation "clean f \<equiv> f(name := 1)"
abbreviation "get f \<equiv> project (f name)"

lemmas inj_homo_mult[simp] = inj.homo_mult[symmetric]
lemmas inj_homo_one = inj.homo_one
lemmas prj_homo_mult[simp] = prj.homo_mult
lemmas prj_homo_one = prj.homo_one

end


syntax "_Update_RES"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'<(_)'>" [1000, 0] 900)

translations
  "_Update_RES f (_updbinds b bs)" \<rightleftharpoons> "_Update_RES (_Update_RES f b) bs"
  "f<x:=y>" => "CONST fun_upd f (CONST Entry.name x) (CONST Entry.inject x y)"


ML_file_debug \<open>Resource_Space.ML\<close>

hide_const (open) Entry
hide_type (open) Entry

end