theory NuInstructions
  imports NuSys NuBasicAbstractors
begin

definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> 'r \<Rightarrow> (('a::len) word \<times> 'r) state"
  where "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
declare op_add_def[\<nu>instr]
\<nu>overloads "+" and round_add and hehe
theorem add_nat[\<nu>overload +]: "x + y < 2^LENGTH('b) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<longmapsto> x + y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<brangle>"
  unfolding op_add_def Procedure_def by auto

theorem add_nat_mod[\<nu>overload round_add]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR> \<longmapsto> (x + y mod 2^(LENGTH('b))) \<tycolon> \<nat>['b] \<boxbar> \<RR> \<brangle>"
  unfolding op_add_def Procedure_def by auto (metis of_nat_unat ucast_id unat_of_nat)

proc add2[\<nu>overload hehe]: "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if "x < 100" and "y < 100"
begin
  \<bullet> x x y + +
finish
thm add2_\<nu>proc
term "\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n a"

proc add3: "(x \<tycolon> \<nat>[32] named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])" for x :: nat if A:"x < 100" and B:"y < 100" begin
  \<bullet> y x hehe
finish

thm add3_\<nu>compilation

ML \<open>NuProcedure.check (Context.Proof @{context}) ("add2", Position.none)\<close>
thm [[\<nu>overload add2]]
ML \<open>NuProcedure.compilation_thm (Context.Proof @{context}) @{term add2}\<close>

qed
  show 
  proof -
 qed
  show ?thesis by this
qed
  then show ?thesis
    by fast
ML_val \<open>Thm.prop_of @{thm this}\<close>
  ML_prf \<open>@{thm obli} RS @{thm this}\<close>

qed
  ML_val \<open>Proof_Context.read_term_schematic @{context} "?\<p>\<r>\<o>\<c>"\<close>
  term ?\<p>\<r>\<o>\<c> 

