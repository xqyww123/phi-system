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

subsubsection \<open>Set\<close>

definition set :: \<open>'a::shift_by_nat_ord len_intvl \<Rightarrow> 'a set\<close>
  where [iff]: \<open>set i = {start i ..< shift_by_nat (start i) (len i)}\<close>

lemma forall[simp]:
  \<open> (\<forall>i\<in>{len_intvl.start iv..<len_intvl.start iv + len_intvl.len iv}. P i) \<longleftrightarrow>
    (\<forall>i < len_intvl.len iv. P (i + len_intvl.start iv)) \<close>
  by (auto; metis add.commute le_Suc_ex nat_add_left_cancel_less)

lemma forall_alt[simp]:
  \<open> (\<forall>i. len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv \<longrightarrow> P i) \<longleftrightarrow>
    (\<forall>i < len_intvl.len iv. P (i + len_intvl.start iv)) \<close>
  by (auto; metis add.commute le_add_diff_inverse less_diff_conv2)

subsection \<open>List\<close>

abbreviation list\<^sub>N :: \<open>nat len_intvl \<Rightarrow> nat list\<close>
  where \<open>list\<^sub>N iv \<equiv> [start iv ..< start iv + len iv]\<close>


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
  \<open> a ##\<^sub>+ b \<longleftrightarrow> shift_by_nat (start a) (len a) = (start b) \<close>
  unfolding dom_of_add_len_intvl_def
  by (cases a; cases b; simp)

lemma plus_len_intvl_start[simp]:
  \<open> start (a + b) = start a \<close>
  by (cases a; cases b; simp)

lemma plus_len_intvl_len[simp]:
  \<open> len (a + b) = len a + len b \<close>
  by (cases a; cases b; simp)

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
hide_fact (open) set_add forall forall_alt

end