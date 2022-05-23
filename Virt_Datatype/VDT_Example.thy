theory VDT_Example
  imports Virtual_Datatype
begin

section \<open>Example\<close>

subsection \<open>Basic Usage\<close>

virtual_datatype T1 :: plus =
  C1 :: nat
  C2 :: bool

print_locale T1
print_locale T1_cons
print_locale T1_fields

context T1 begin

text \<open>\<^typ>\<open>'value\<close> is a sort plus!\<close>
term "mk_C1 a + mk_C2 b"

lemma "dest_C1 (mk_C1 x) = x" by simp

lemma "mk_C1 x \<noteq> mk_C2 y" by simp

lemma "mk_C1 x = mk_C1 y \<longleftrightarrow> x = y" by rule simp_all

lemma "mk_C1 x = mk_C1 y \<longleftrightarrow> x = y" by blast

lemma "CONS_OF (mk_C1 x) = C1" by simp

lemma "C1.is_instance (mk_C1 x)" by simp

thm C1.is_instance_def

(* TODO: a simp proc to automate this *)
lemma "\<not> C1.is_instance (mk_C2 x)" unfolding C1.is_instance_def by simp

end


subsection \<open>Inheritance\<close>

virtual_datatype T2 = T1 + xx: T1[C1=CC1] +
  C3 :: int

virtual_datatype T3 = T2[C1=CC1,CC1=CCC1]

definition (in T1) "trn vx = mk_C1 (if dest_C2 vx then 1 else 0)"

context T2 begin
thm trn_def
thm xx.trn_def
end

context T3 begin
thm trn_def
thm xx.trn_def
thm CCC1.is_instance_def
end


subsection \<open>Recursion\<close>

virtual_datatype TR =
  R_NIL :: "unit"
  R_CONS :: "nat \<times> 'self"

context TR begin
definition "sth = mk_R_CONS (0, mk_R_CONS (1, mk_R_NIL ()))"
end

virtual_datatype Inconsistent =
  Inconsit :: "'self \<Rightarrow> bool"


text \<open>Though, the recursive virtual datatype is unverified in the locale,
  it is justified during interpretation. Virtual datatype like T_inconsistent
  can never be interpreted.

  Thus, we have to emphasize, once the recursive \<close>

datatype my_cons = MY_R_NIL | MY_R_CONS

interpretation interp1: TR MY_R_NIL MY_R_CONS
  "(\<lambda>l. case l of [] \<Rightarrow> MY_R_NIL | _ \<Rightarrow> MY_R_CONS)"
  "(\<lambda>l. case l of [] \<Rightarrow> ())"
  "(\<lambda>_. [])"
  "(\<lambda>l. case l of (a#l') \<Rightarrow> (a,l'))"
  "(\<lambda>(a,l'). a#l')"
  by unfold_locales (auto split: list.split unit.split)
  
thm interp1.sth_def[simplified]

end