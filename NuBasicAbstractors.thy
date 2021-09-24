theory NuBasicAbstractors
  imports NuLLReps NuSys
begin

text \<open>Basic \<nu>-abstractors\<close>

text \<open>Examples for automatic property inference\<close>
schematic_goal [simplified]: "\<nu>Share (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<bool>) ?set ?sh" by (rule \<nu>intro)+
(* schematic_goal [simplified]: "\<nu>Share N s f \<Longrightarrow> \<nu>Share (N \<nuFusion> N \<nuFusion> N) ?set ?sh" for N :: "('a::sharable_lrep, 'b) nu"
  including show_more1 by (blast intro: \<nu>intro Premise_I) *)
schematic_goal [simplified]: "\<nu>Equalable (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<nat>['a :: len]) ?ceq" by (rule \<nu>intro)+
schematic_goal [simplified]: "\<nu>Disposable ((b,x,y) \<tycolon> \<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<nat>['a :: len])" by (rule \<nu>intro)+
ML_val \<open>
val tm2 = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic @{context})
    "\<nu>Share N s f \<Longrightarrow> \<nu>Share (N \<nuFusion> N \<nuFusion> N) ?set ?sh"
  |> Thm.cterm_of @{context}
val tm = Thm.cprop_of @{thm th1}
val th = Goal.init tm2
val th2 = SOLVED' (Tactical.REPEAT o Tactic.ares_tac @{context} @{thms \<nu>share}) 1 th |> Seq.hd
\<close>

section \<open>Abstractors for specification\<close>

subsubsection \<open>Refinement\<close>

definition NuRefine :: " ('a :: lrep, 'b) nu \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) nu " (infixl "\<nuRefine>" 80)
  where "N \<nuRefine> T = Nu (\<lambda>(p,x). x \<in> T \<and>(p \<nuLinkL> N \<nuLinkR> x))"
lemma [simp]: "p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> (p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def by auto
lemma [elim]: "x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<and>x \<in> P" unfolding Cast_def by auto

(* section \<open>Others\<close>

definition stepin :: "( ('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> ( ('c::lrep) \<times> 'a \<Rightarrow> ('c \<times> 'b) state)"
  where "stepin f x = (case x of (c,a) \<Rightarrow> bind (f a) (\<lambda>y. StatOn (c,y)))"
lemma stepin: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> u \<tycolon> U \<longmapsto> v \<tycolon> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c stepin f \<blangle> (x,u) \<tycolon> (X \<nuFusion> U) \<longmapsto> (x,v) \<tycolon> (X \<nuFusion> V) \<brangle>"
  unfolding stepin_def \<nu>def bind_def by auto

definition stepinR :: "( ('a::lrep) \<times>('z::lrep) \<Rightarrow> ('z1::lrep) state) \<Rightarrow> ((('c::lrep) \<times> 'a) \<times>'z \<Rightarrow> ('c \<times> 'z1) state)"
  where "stepinR f x = (case x of ((c,a),z) \<Rightarrow> bind (f (a,z)) (\<lambda>y. StatOn (c,y)))"
lemma stepinR: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> (a \<tycolon> A)\<heavy_comma>Z \<longmapsto> Z1 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c stepinR f \<blangle> (c,a) \<tycolon> (C \<nuFusion> A)\<heavy_comma>Z \<longmapsto> c \<tycolon> C\<heavy_comma>Z1 \<brangle>"
  unfolding stepinR_def \<nu>def bind_def by (auto 4 3)
definition op_pairring_make :: "( ('z1::lrep) \<Rightarrow> ( ('b::lrep) \<times> ('z2::lrep) ) state) \<Rightarrow> ('a \<times> ('z1::lrep) \<Rightarrow> (( ('a::lrep) \<times> 'b) \<times> 'z2) state)"
  where "op_pairring_make f s = (case s of (a,z1) \<Rightarrow> bind (f z1) (\<lambda>(b,z2). StatOn ((a,b),z2)))"
lemma op_pairring_make: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> Z1 \<longmapsto> b \<tycolon> B\<heavy_comma>Z2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pairring_make f \<blangle> a \<tycolon> A\<heavy_comma>Z1 \<longmapsto> (a,b) \<tycolon> A \<nuFusion> B\<heavy_comma>Z2 \<brangle>"
  unfolding op_pairring_make_def \<nu>def bind_def by (auto 4 3)

lemma [\<nu>auto_destruct]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> r \<tycolon> R\<heavy_comma>Z \<longmapsto> Z1 \<brangle> \<Longrightarrow>  \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> l \<tycolon> L\<heavy_comma>Z1 \<longmapsto> Z2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (stepinR g \<nuInstrComp> f) \<blangle> (l,r) \<tycolon> (L \<nuFusion> R)\<heavy_comma>Z \<longmapsto> Z2\<brangle>"
  unfolding AutoTag_def by (blast intro: instr_comp stepinR)
lemma [\<nu>auto_construct]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> EoC Z \<longmapsto> l \<tycolon> L\<heavy_comma>EoC Z1 \<brangle> \<Longrightarrow>  \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle>EoC Z1 \<longmapsto> r \<tycolon> R\<heavy_comma>EoC Z' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> op_pairring_make g) \<blangle>EoC Z \<longmapsto> (l,r) \<tycolon> (L \<nuFusion> R)\<heavy_comma>EoC Z'\<brangle>"
  unfolding AutoTag_def by (blast intro: instr_comp op_pairring_make)

schematic_goal "\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<blangle> ?x \<tycolon> ((\<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c A \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c B) \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c D) \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c C\<heavy_comma>Z \<longmapsto> (?Z1::(?'a::lrep) set) \<brangle>" by (rule \<nu>auto_destruct)+
thm \<nu>auto_construct

ML \<open>@{term "29::32"}\<close>
lemma [simplified]: "(10::3) = (0::3)"  by auto
  thm term_def *)

schematic_goal [simplified]:"\<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<heavy_comma>B\<heavy_comma>(x \<tycolon> C \<nuRefine> P)\<heavy_comma>D) \<longmapsto> (A\<heavy_comma>B\<heavy_comma>x \<tycolon> C\<heavy_comma>D) \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e ?P" by (rule \<nu>intro)+
schematic_goal "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<heavy_comma>B) \<longmapsto> (A\<heavy_comma>B) \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e ?P" by (rule \<nu>intro)

end