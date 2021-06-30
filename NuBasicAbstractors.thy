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

lemma [\<nu>share]: "Nu_Share N s1 f1 \<Longrightarrow> Nu_Share M s2 f2 \<Longrightarrow> Nu_Share (N \<nuFusion> M) (s1 \<times> s2) (\<lambda>z x. case x of (x1,x2) \<Rightarrow> (f1 z x1, f2 z x2))"
  for N :: "('a :: sharable_lrep, 'b) nu" and M :: "('c :: sharable_lrep, 'd) nu" 
  unfolding Nu_Share_def by auto
lemma [\<nu>equable]: "\<nu>Equalable N p \<Longrightarrow> \<nu>Equalable M q \<Longrightarrow> \<nu>Equalable (N \<nuFusion> M) (\<lambda>x. case x of ((a1,b1),(a2,b2)) \<Rightarrow> p (a1,a2) \<and> q (b1,b2))"
  unfolding \<nu>Equalable_def by auto

lemma [\<nu>disposable]: "\<nu>Disposable (x \<tycolon> X) \<Longrightarrow> \<nu>Disposable (y \<tycolon> Y) \<Longrightarrow> \<nu>Disposable ((x,y) \<tycolon> X \<nuFusion> Y)"
  unfolding \<nu>Disposable_def by auto

text \<open>Examples for automatic property inference\<close>
schematic_goal [simplified]: "Nu_Share (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<bool>) ?set ?sh" by (rule \<nu>share)+
schematic_goal [simplified]: "Nu_Share N s f \<Longrightarrow> Nu_Share (N \<nuFusion> N \<nuFusion> N) ?set ?sh" for N :: "('a::sharable_lrep, 'b) nu"
  including show_more1 by (blast intro: \<nu>share)
schematic_goal [simplified]: "\<nu>Equalable (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<nat>['a :: len]) ?ceq" by (rule \<nu>equable)+
schematic_goal [simplified]: "\<nu>Disposable ((b,x,y) \<tycolon> \<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<nat>['a :: len])" by (rule \<nu>disposable)+
ML_val \<open>
val tm2 = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic @{context})
    "Nu_Share N s f \<Longrightarrow> Nu_Share (N \<nuFusion> N \<nuFusion> N) ?set ?sh"
  |> Thm.cterm_of @{context}
val tm = Thm.cprop_of @{thm th1}
val th = Goal.init tm2
val th2 = SOLVED' (Tactical.REPEAT o Tactic.ares_tac @{context} @{thms \<nu>share}) 1 th |> Seq.hd
\<close>


definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> 'r \<Rightarrow> (('a::len) word \<times> 'r) state"
  where op_add_def: "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
theorem add_nat: "x + y < 2^LENGTH('b) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<longmapsto> x + y \<tycolon> \<nat>['b] \<boxbar> \<RR>emain_stack \<brangle>"
  unfolding op_add_def Procedure_def by auto

theorem add_nat_mod: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b::len] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar> \<RR> \<longmapsto> (x + y mod 2^(LENGTH('b))) \<tycolon> \<nat>['b] \<boxbar> \<RR> \<brangle>"
  unfolding op_add_def Procedure_def by auto (metis of_nat_unat ucast_id unat_of_nat)

definition NuRefine :: " ('a :: lrep, 'b) nu \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) nu " (infixl "\<nuRefine>" 80)
  where "N \<nuRefine> T = Nu (\<lambda>(p,x). x \<in> T \<and>(p \<nuLinkL> N \<nuLinkR> x))"
lemma [simp]: "p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> (p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def by auto
lemma [elim]: "x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>cast]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> x \<tycolon> N \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o x \<in> P" unfolding Cast_def by auto
schematic_goal [simplified]:"\<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<boxbar>B\<boxbar>(x \<tycolon> C \<nuRefine> P)\<boxbar>D) \<longmapsto> (A\<boxbar>B\<boxbar>x \<tycolon> C\<boxbar>E) \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o ?P" by (rule \<nu>cast)+
schematic_goal "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<boxbar>B) \<longmapsto> (A\<boxbar>B) \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o ?P" by (rule \<nu>cast)

end