theory NuBasicAbstractors
  imports NuLLReps NuSys
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

definition NuRefine :: " ('a :: lrep, 'b) nu \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) nu " (infixl "\<nuRefine>" 80)
  where "N \<nuRefine> T = Nu (\<lambda>(p,x). x \<in> T \<and>(p \<nuLinkL> N \<nuLinkR> x))"
lemma [simp]: "p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> (p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def by auto
lemma [elim]: "x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>cast]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> x \<tycolon> N \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e x \<in> P" unfolding Cast_def by auto

definition stepin :: "( ('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> ( ('c::lrep) \<times> 'a \<Rightarrow> ('c \<times> 'b) state)"
  where "stepin f x = (case x of (c,a) \<Rightarrow> bind (f a) (\<lambda>y. StatOn (c,y)))"
lemma stepin: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> u \<tycolon> U \<longmapsto> v \<tycolon> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c stepin f \<blangle> (x,u) \<tycolon> (X \<nuFusion> U) \<longmapsto> (x,v) \<tycolon> (X \<nuFusion> V) \<brangle>"
  unfolding stepin_def \<nu>def bind_def by auto

definition stepinR :: "( ('a::lrep) \<times>('z::lrep) \<Rightarrow> ('z1::lrep) state) \<Rightarrow> ((('c::lrep) \<times> 'a) \<times>'z \<Rightarrow> ('c \<times> 'z1) state)"
  where "stepinR f x = (case x of ((c,a),z) \<Rightarrow> bind (f (a,z)) (\<lambda>y. StatOn (c,y)))"
lemma stepinR: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> (a \<tycolon> A)\<boxbar>Z \<longmapsto> Z1 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c stepinR f \<blangle> (c,a) \<tycolon> (C \<nuFusion> A)\<boxbar>Z \<longmapsto> c \<tycolon> C\<boxbar>Z1 \<brangle>"
  unfolding stepinR_def \<nu>def bind_def by (auto 4 3)
definition op_pairring_make :: "( ('z1::lrep) \<Rightarrow> ( ('b::lrep) \<times> ('z2::lrep) ) state) \<Rightarrow> ('a \<times> ('z1::lrep) \<Rightarrow> (( ('a::lrep) \<times> 'b) \<times> 'z2) state)"
  where "op_pairring_make f s = (case s of (a,z1) \<Rightarrow> bind (f z1) (\<lambda>(b,z2). StatOn ((a,b),z2)))"
lemma op_pairring_make: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> Z1 \<longmapsto> b \<tycolon> B\<boxbar>Z2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pairring_make f \<blangle> a \<tycolon> A\<boxbar>Z1 \<longmapsto> (a,b) \<tycolon> A \<nuFusion> B\<boxbar>Z2 \<brangle>"
  unfolding op_pairring_make_def \<nu>def bind_def by (auto 4 3)

lemma [\<nu>auto_destruct]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> r \<tycolon> R\<boxbar>Z \<longmapsto> Z1 \<brangle> \<Longrightarrow>  \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> l \<tycolon> L\<boxbar>Z1 \<longmapsto> Z2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (stepinR g \<nuInstrComp> f) \<blangle> (l,r) \<tycolon> (L \<nuFusion> R)\<boxbar>Z \<longmapsto> Z2\<brangle>"
  unfolding AutoTag_def by (blast intro: instr_comp stepinR)
lemma [\<nu>auto_construct]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> Z \<longmapsto> l \<tycolon> L\<boxbar>Z1 \<brangle> \<Longrightarrow>  \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> Z1 \<longmapsto> r \<tycolon> R\<boxbar>Z' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> op_pairring_make g) \<blangle> Z \<longmapsto> (l,r) \<tycolon> (L \<nuFusion> R)\<boxbar>Z'\<brangle>"
  unfolding AutoTag_def by (blast intro: instr_comp op_pairring_make)

definition op_const_int :: " ('x::len) word \<Rightarrow> (('a::lrep) \<Rightarrow> ('x word \<times>'a) state) "
  where "op_const_int x r = StatOn (x,r)"
lemma [\<nu>auto_construct]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int (Word.of_nat (numeral x)) \<blangle> Z \<longmapsto> (numeral x) \<tycolon> \<nat>[('x::len)]\<boxbar>Z \<brangle>"
  unfolding op_const_int_def \<nu>def by auto  \<comment> \<open>Only literal number could be constructed automatically\<close>

schematic_goal "\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<blangle> ?x \<tycolon> ((\<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c A \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c B) \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c D) \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c C\<boxbar>Z \<longmapsto> (?Z1::(?'a::lrep) set) \<brangle>" by (rule \<nu>auto_destruct)+
schematic_goal [simplified]:"\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<blangle>(?Z1::(?'a::lrep) set) \<longmapsto> ((\<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c (a::'c::lrep), 233), \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c (b::'d::lrep)) \<tycolon>  ((?N1 \<nuFusion> \<nat>[32]) \<nuFusion> ?N2)\<boxbar>Z \<brangle>" including show_more1 by (rule \<nu>auto_construct)+
thm \<nu>auto_construct

value "8::3 word"

thm \<nu>auto_

definition 



ML \<open>@{term "29::32"}\<close>
lemma [simplified]: "(10::3) = (0::3)"  by auto
  thm term_def

schematic_goal [simplified]:"\<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<boxbar>B\<boxbar>(x \<tycolon> C \<nuRefine> P)\<boxbar>D) \<longmapsto> (A\<boxbar>B\<boxbar>x \<tycolon> C\<boxbar>D) \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e ?P" by (rule \<nu>cast)+
schematic_goal "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<boxbar>B) \<longmapsto> (A\<boxbar>B) \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e ?P" by (rule \<nu>cast)

end