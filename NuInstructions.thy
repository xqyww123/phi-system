theory NuInstructions
  imports NuSys NuBasicAbstractors
  keywords
    "myconsider" :: prf_goal % "proof"
begin

text \<open>Basic instructions\<close>

section \<open>Structural instructions\<close>

subsection \<open>Basic sequential instructions\<close>
subsubsection \<open>op_drop\<close>
definition op_drop :: "('a::lrep) \<times> ('r::lrep) \<Rightarrow> 'r state" where "op_drop x = (case x of (_,r) \<Rightarrow> StatOn r)"
declare op_drop_def[\<nu>instr]
theorem drop_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> X\<boxbar>R \<longmapsto> R \<brangle>" unfolding \<nu>def op_drop_def by auto

subsection \<open>Branch\<close>

subsubsection \<open>op_if\<close>
definition op_if :: " (('s::lrep) \<flower> ('sr::register_collection) \<Rightarrow> (('t::lrep) \<flower> ('tr::register_collection)) state) \<Rightarrow> ('s \<flower> 'sr \<Rightarrow> ('t \<flower> 'tr) state) \<Rightarrow> (1 word \<times> 's) \<flower> 'sr \<Rightarrow> ('t \<flower> 'tr) state"
  where "op_if brT brF x = (case x of (Proc_Ctx (c,s) r) \<Rightarrow> if c = 1 then brT (Proc_Ctx s r) else brF (Proc_Ctx s r))"
declare op_if_def[\<nu>instr]
theorem if_\<nu>proc: "(\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e c \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_true \<blangle> U \<flower> W \<longmapsto> Vt \<flower> Wt \<brangle>) \<Longrightarrow> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> c \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_false \<blangle> U \<flower> W \<longmapsto> Vf \<flower> Wf \<brangle>)
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if branch_true branch_false \<blangle> (c \<tycolon> \<bool>)\<boxbar>U \<flower> W  \<longmapsto> (if c then Vt \<flower> Wt else (Vf \<flower> Wf)) \<brangle>"
  unfolding \<nu>def op_if_def by auto

lemma [simp]: "(if P then (A \<flower> B) else (A' \<flower> B')) = ((if P then A else A') \<flower> (if P then B else B'))" by auto
lemma [simp]: "(if P then (A\<boxbar>B) else (A'\<boxbar>B')) = ((if P then A else A')\<boxbar>(if P then B else B'))" by auto
lemma [simp]: "(if P then (x \<tycolon> N) else (y \<tycolon> N)) = ((if P then x else y) \<tycolon> N)"  by auto


section \<open>Arithmetic instructions\<close>

\<nu>overloads "+" and round_add and "<" and "-"

subsection \<open>Integer arithmetic\<close>

subsubsection \<open>addition\<close>
definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> ('r::lrep) \<Rightarrow> (('a::len) word \<times> 'r) state"
  where "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
declare op_add_def[\<nu>instr]
theorem add_nat[\<nu>overload +]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<longmapsto> x + y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: of_nat_inverse) 

theorem add_nat_mod[\<nu>overload round_add]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR> \<longmapsto> ((x + y) mod 2^(LENGTH('b))) \<tycolon> \<nat>['b] \<boxbar> \<RR> \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: unat_word_ariths)

subsubsection \<open>subtraction\<close>
definition op_sub :: "('a::len) itself \<Rightarrow> 'a word \<times> 'a word \<times> ('r::lrep) \<Rightarrow> ('a word \<times> 'r) state"
  where "op_sub _ p = (case p of (a,b,r) \<Rightarrow> if a \<le> b then StatOn (b - a, r) else STrap)"
declare op_sub_def[\<nu>instr]
theorem sub_nat_\<nu>proc[\<nu>overload -]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<le> y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub TYPE('w::len) \<blangle> x \<tycolon> \<nat>['w]\<boxbar>y \<tycolon> \<nat>['w]\<boxbar>\<R> \<longmapsto> y - x \<tycolon> \<nat>['w]\<boxbar>\<R> \<brangle>"
  unfolding \<nu>def op_sub_def apply auto apply (meson le_less unat_sub) using word_le_nat_alt by blast
  
subsubsection \<open>less\<close>
definition op_lt :: " ('w::len) itself \<Rightarrow> ('w word \<times> 'w word \<times> ('r::lrep)) \<Rightarrow> (1 word \<times> 'r) state"
  where "op_lt _ s = (case s of (a,b,r) \<Rightarrow>  StatOn ((if  a < b then 1 else 0), r))"
declare op_lt_def[\<nu>instr]
theorem op_lt_\<nu>proc[\<nu>overload <]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt (TYPE('w::len)) \<blangle> x \<tycolon> \<nat>['w]\<boxbar>y \<tycolon> \<nat>['w]\<boxbar>\<R> \<longmapsto> (x < y) \<tycolon> \<bool>\<boxbar>\<R> \<brangle>"
  unfolding \<nu>def op_lt_def by (auto simp add: word_less_nat_alt)

section \<open>Tests\<close>

definition [simp]:"difference x y = (if x < y then y - x else x - y)"

proc diff : "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "(difference x y \<tycolon> \<nat>[32])"
  \<bullet> y x < if \<medium_left_bracket> \<bullet> y x - \<medium_right_bracket>  \<medium_left_bracket> \<bullet> x y - \<medium_right_bracket>
  \<bullet> finish

proc add2 : "(( x \<tycolon> \<nat>[32]) named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if "x < 100" and "y < 100"
  \<nu>have x[used]: "x < 100 \<and> y < 100" using that by auto
  \<bullet> x x y + +
  \<nu>obtain z where c: "x < z" by auto
  finish


proc add02: "(( x \<tycolon> \<nat>[32]) named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
if A[used]:"x < 100" and [used]:"y < 100"
    \<bullet> x x y + +
    \<nu>obtain z where c: "x < z" by auto
  finish

thm add2_\<nu>proc


proc add3: "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if [used]:"x < 100" and [used]:"y < 100"
  \<bullet> x x y + +
  \<nu>have gg: "x < 200"  by auto
  finish
thm add3_\<nu>proc

thm add3_\<nu>proc




thm add2_\<nu>proc

ML \<open>map (Attrib.attribute @{context}) @{attributes [elim]}\<close>
end