(* AUTHOR: Qiyuan Xu, 2022 *)

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

thm T1_cons_def

context T1 begin

text \<open>\<^typ>\<open>'value\<close> is a sort plus!\<close>
term "C1.mk a + C2.mk b"

lemma "C1.dest (C1.mk x) = x" by simp

ML \<open>@{term C1.cons}\<close>

lemma "C1.cons \<noteq> C2.cons" by simp

lemma "C1.mk x \<noteq> C2.mk y" by simp

lemma "C1.mk x = C1.mk y \<longleftrightarrow> x = y" by simp

lemma "CONS_OF (C1.mk x) = C1.cons" by simp

lemma "C1.is_instance (C1.mk x)" by simp

thm C1.is_instance_def

(* TODO: a simp proc to automate this *)
lemma "\<not> C1.is_instance (C2.mk x)" unfolding C1.is_instance_def by simp

end


subsection \<open>Inheritance\<close>
print_locale T1

virtual_datatype T2 = T1 + xx: T1[C1=CC1] +
  C3 :: int

virtual_datatype T3 = T2[C1=CC1,CC1=CCC1]

definition (in T1) "trn vx = C1.mk (if C2.dest vx then 1 else 0)"

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

virtual_datatype 'a TR =
  R_NIL :: "unit"
  R_CONS :: "'a \<times> 'self"

context TR begin
definition "sth = R_CONS.mk (undefined, R_CONS.mk (undefined, R_NIL.mk ()))"
end

virtual_datatype Inconsistent =
  Inconsit :: "'self \<Rightarrow> bool"


text \<open>Though, the recursive virtual datatype is unverified in the locale,
  it is justified during interpretation. Virtual datatype like T_inconsistent
  can never be interpreted.

  Thus, we have to emphasize, once the recursive \<close>

datatype my_cons = MY_R_NIL | MY_R_CONS

interpretation interp1: TR
  "(\<lambda>l. case l of [] \<Rightarrow> MY_R_NIL | _ \<Rightarrow> MY_R_CONS)"
  \<open>Virtual_Datatype.Field MY_R_NIL (\<lambda>_. ()) (\<lambda>_. [])\<close>
  \<open>Virtual_Datatype.Field MY_R_CONS (\<lambda>l. case l of (a#l') \<Rightarrow> (a,l')) (\<lambda>(a,l'). a#l')\<close>
  by unfold_locales (auto split: list.split unit.split)
  
thm interp1.sth_def[simplified]

end