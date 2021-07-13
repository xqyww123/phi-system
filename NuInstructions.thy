theory NuInstructions
  imports NuSys NuBasicAbstractors
  keywords
    "myconsider" :: prf_goal % "proof"
begin

definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> ('r::lrep) \<Rightarrow> (('a::len) word \<times> 'r) state"
  where "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
declare op_add_def[\<nu>instr]
\<nu>overloads "+" and round_add and hehe
theorem add_nat[\<nu>overload +]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<longmapsto> x + y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<brangle>"
  unfolding op_add_def Procedure_def by auto

theorem add_nat_mod[\<nu>overload round_add]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR> \<longmapsto> (x + y mod 2^(LENGTH('b))) \<tycolon> \<nat>['b] \<boxbar> \<RR> \<brangle>"
  unfolding op_add_def Procedure_def by auto (metis of_nat_unat ucast_id unat_of_nat)

ML \<open>val _ =
  Outer_Syntax.command \<^command_keyword>\<open>myconsider\<close> "state cases rule"
    (Parse_Spec.obtains >> @{print} >> (Toplevel.proof' o Obtain.consider_cmd));\<close>

proc add3 : "((\<exists>*x. x \<tycolon> \<nat>[32]) named x, (\<exists>*y. y \<tycolon> \<nat>[32]))" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if A[in_using]:"x < 100" and [in_using]:"y < 100"
\<nu>obtain z2 z3 where c: "x < z2" and c2: "x < z3" and c3: "y < z2" by auto
  \<bullet> x x y + +
  finish
  obtain


proc add2 : "(( x \<tycolon> \<nat>[32]) named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if "x < 100" and "y < 100"
  \<nu>have x[in_using]: "x < 100 \<and> y < 100" using that by auto
  \<bullet> x x y +
    \<nu>obtain z where c: "x < z" by auto
  finish


proc add2[\<nu>overload hehe]: "(( x \<tycolon> \<nat>[32]) named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
if A[in_using]:"x < 100" and [in_using]:"y < 100"
    \<bullet> x x y + +
    \<nu>obtain z where c: "x < z" by auto
finish
thm add2_\<nu>proc


proc add3: "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if [in_using]:"x < 100" and [in_using]:"y < 100"
  \<bullet> x x y + +
  \<nu>have gg: "x < 200"  by auto
  finish
thm add3_\<nu>proc

thm add3_\<nu>proc




thm add2_\<nu>proc

ML \<open>map (Attrib.attribute @{context}) @{attributes [elim]}\<close>
end