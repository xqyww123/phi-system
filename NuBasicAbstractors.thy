theory NuBasicAbstractors
  imports NuLLReps
  abbrevs "SState" = "\<B_S>\<B_t>\<B_r>\<B_i>\<B_c>\<B_t>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e>"
      and "LState" = "\<B_L>\<B_o>\<B_o>\<B_s>\<B_e>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e>" 
      and "with_registers" = "\<B_w>\<B_i>\<B_t>\<B_h>_\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r>\<B_s>"
      and "wreg" = "\<B_w>\<B_i>\<B_t>\<B_h>_\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r>\<B_s>"
begin

definition Fusion :: "('a1::lrep,'b1) nu \<Rightarrow> ('a2::lrep,'b2) nu \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) nu" (infixr "\<nuFusion>" 70) 
  where "Fusion N M = Nu (\<lambda>px. case px of ((p1,p2),(x1,x2)) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2))"
lemma Fusion_abst[simp]: "(p1,p2) \<nuLinkL> N \<nuFusion> M \<nuLinkR> (x1,x2) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)"
  unfolding Fusion_def by simp
lemma "Inhabited ((x1,x2) \<tycolon> N1 \<nuFusion> N2) \<longleftrightarrow> Inhabited (x1 \<tycolon> N1) \<and> Inhabited (x2 \<tycolon> N2)"
  unfolding Inhabited_def by simp

lemma [\<nu>share]: "Nu_Share N f1 \<Longrightarrow> Nu_Share M f2 \<Longrightarrow> Nu_Share (N \<nuFusion> M) (\<lambda>x z. case x of (x1,x2) \<Rightarrow> (f1 x1 z, f2 x2 z))"
  for N :: "('a :: sharable_lrep, 'b) nu" and M :: "('c :: sharable_lrep, 'd) nu" 
  unfolding Nu_Share_def by auto
lemma [\<nu>equable]: "\<nu>Equalable N p \<Longrightarrow> \<nu>Equalable M q \<Longrightarrow> \<nu>Equalable (N \<nuFusion> M) (\<lambda>x. case x of ((a1,b1),(a2,b2)) \<Rightarrow> p (a1,a2) \<and> q (b1,b2))"
  unfolding \<nu>Equalable_def by auto


text \<open>Examples for automatic property inference\<close>
schematic_goal [simplified]: "Nu_Share N K \<Longrightarrow> Nu_Share (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> N) ?sh" by (rule \<nu>share)+
schematic_goal [simplified]: "\<nu>Equalable (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<nat>['a :: len]) ?ceq" by (rule \<nu>equable)+


definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> 'r \<Rightarrow> (('a::len) word \<times> 'r) state"
  where op_add_def: "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
theorem add_nat: "x + y < 2^LENGTH('b) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<llangle> x \<tycolon> \<nat>['b::len] \<bbar> y \<tycolon> \<nat>['b] \<bbar> \<RR>emain_stack \<longmapsto> x + y \<tycolon> \<nat>['b] \<bbar> \<RR>emain_stack \<rrangle>"
  unfolding op_add_def by (auto split: state.split)
syntax "__bar__" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "┃" 13)

theorem add_nat_mod: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<llangle> x \<tycolon> \<nat>['b::len] \<bbar> y \<tycolon> \<nat>['b] \<bbar> \<RR> \<longmapsto> (x + y mod 2^(LENGTH('b))) \<tycolon> \<nat>['b] \<bbar> \<RR> \<rrangle>"
  unfolding op_add_def by (auto split: state.split) (metis of_nat_unat ucast_id unat_of_nat)


end