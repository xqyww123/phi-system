theory NuInstructions
  imports NuSys
begin

definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> 'r \<Rightarrow> (('a::len) word \<times> 'r) state"
  where "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
declare op_add_def[\<nu>instr]
\<nu>procedure "+" and "+'"
theorem add_nat[\<nu>proc "+"]: "x + y < 2^LENGTH('b) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<longmapsto> x + y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<brangle>"
  unfolding op_add_def Procedure_def by auto

theorem add_nat_mod[\<nu>proc "+'"]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR> \<longmapsto> (x + y mod 2^(LENGTH('b))) \<tycolon> \<nat>['b] \<boxbar> \<RR> \<brangle>"
  unfolding op_add_def Procedure_def by auto (metis of_nat_unat ucast_id unat_of_nat)

ML \<open>Term.dest_Type @{typ "32"}\<close>

context includes show_more1 begin
thm meta_eq_to_obj_eq
end

proc add2: "(x \<tycolon> \<nat>[32] named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])" for x :: nat if A:"x < 100" and B:"y < 100" begin
  \<bullet> \<rightarrow> (x,y) x x y + +
finish

qed
  ML_val \<open>Proof_Context.read_term_schematic @{context} "?\<p>\<r>\<o>\<c>"\<close>
  term ?\<p>\<r>\<o>\<c> 

