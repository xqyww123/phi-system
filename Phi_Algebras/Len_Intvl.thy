theory Len_Intvl
  imports Algebras
begin

section \<open>Left Closed Right Open Intervals in the Length representation\<close>

subsection \<open>Definition\<close>

datatype 'a len_intvl = Len_Intvl (start: 'a) (len: nat)

notation Len_Intvl ("\<lbrakk>_ : _\<rwpar>")

subsubsection \<open>Helper\<close>

class shift_by_nat =
  fixes shift_by_nat :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>
  assumes shift_by_nat_assoc: \<open>shift_by_nat (shift_by_nat x n) m = shift_by_nat x (n + m)\<close>

class shift_by_nat_ord = shift_by_nat + linorder +
  assumes shift_by_nat_ord: \<open>x \<le> shift_by_nat x n\<close>

subsection \<open>Operations\<close>

definition set :: \<open>'a::shift_by_nat_ord len_intvl \<Rightarrow> 'a set\<close>
  where [iff]: \<open>set i = {start i ..< shift_by_nat (start i) (len i)}\<close>


subsection \<open>Properties\<close>

subsubsection \<open>Partial Addition\<close> \<comment> \<open>as concatenating two adjacent intervals\<close>

instantiation len_intvl :: (shift_by_nat) partial_add_cancel begin

definition plus_len_intvl :: \<open>'a len_intvl \<Rightarrow> 'a len_intvl \<Rightarrow> 'a len_intvl\<close>
  where \<open>plus_len_intvl x y = \<lbrakk> start x : len x + len y \<rwpar>\<close>

definition dom_of_add_len_intvl :: \<open>'a len_intvl \<Rightarrow> 'a len_intvl \<Rightarrow> bool\<close>
  where \<open>dom_of_add_len_intvl x y \<longleftrightarrow> shift_by_nat (start x) (len x) = start y\<close>

lemma plus_len_intvl[iff]:
  \<open> \<lbrakk> a : b \<rwpar> + \<lbrakk> c : d \<rwpar> = \<lbrakk> a : b + d \<rwpar>  \<close>
  unfolding plus_len_intvl_def
  by simp

lemma dom_of_add_len_intvl[iff]:
  \<open> \<lbrakk> a : b \<rwpar> ##\<^sub>+ \<lbrakk> c : d \<rwpar> \<longleftrightarrow> shift_by_nat a b = c \<close>
  unfolding dom_of_add_len_intvl_def
  by simp


instance by (standard; case_tac a; case_tac b; case_tac c; simp)

end

lemma set_add:
  \<open>x ##\<^sub>+ y \<Longrightarrow> set x \<union> set y = set (x + y) \<close>
  by (cases x; cases y;
      simp add: shift_by_nat_assoc[symmetric];
      meson ivl_disj_un_two(3) shift_by_nat_ord)

subsection \<open>Instances\<close>

instantiation nat :: shift_by_nat_ord begin
definition shift_by_nat_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where [iff]: \<open>shift_by_nat_nat \<equiv> (+)\<close>
instance by (standard; simp)
end

instantiation int :: shift_by_nat_ord begin
definition shift_by_nat_int :: \<open>int \<Rightarrow> nat \<Rightarrow> int\<close>
  where [iff]: \<open>shift_by_nat_int x y \<equiv> x + of_nat y\<close>
instance by (standard; simp)
end


hide_const (open) start len set
hide_fact (open) set_add

end