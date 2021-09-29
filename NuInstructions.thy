theory NuInstructions
  imports NuSys NuBasicAbstractors
  keywords
    "myconsider" :: prf_goal % "proof"
begin

text \<open>Basic instructions\<close>

section \<open>Structural instructions\<close>

subsection \<open>Basic sequential instructions\<close>

subsubsection \<open>drop\<close>
definition op_drop :: "('a::lrep) \<times> ('r::lrep) \<Rightarrow> 'r state" where "op_drop x = (case x of (_,r) \<Rightarrow> StatOn r)"
declare op_drop_def[\<nu>instr]
theorem drop_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> R \<heavy_comma> X \<longmapsto> R \<brangle>" unfolding \<nu>def op_drop_def by auto

subsubsection \<open>dup & revert\<close>

definition op_dup :: "('a::{share,lrep}) \<times> ('r::lrep) \<Rightarrow> ('a \<times> 'a \<times> 'r) state"
  where "op_dup x = (case x of (a,r) \<Rightarrow> if shareable a then StatOn (share (Gi 1) a, share (Gi 1) a, r) else STrap)"
declare op_dup_def[\<nu>instr]
theorem dup_\<nu>proc: "\<nu>Share X s sh \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e s x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dup \<blangle> R \<heavy_comma> x \<tycolon> X \<longmapsto> R \<heavy_comma> sh (Gi 1) x \<tycolon> X \<heavy_comma> sh (Gi 1) x \<tycolon> X  \<brangle>"
  unfolding \<nu>def op_dup_def by auto

definition op_revert :: "('a::{share,lrep,sharing_identical}) \<times> 'a \<times> ('r::lrep) \<Rightarrow> ('a \<times> 'r) state"
  where "op_revert x = (case x of (a,b,r) \<Rightarrow> if shareable a \<and> sharing_identical a b then StatOn (share (Gi (-1)) a, r) else STrap)"
declare op_revert_def[\<nu>instr]
theorem revert_\<nu>proc: "\<nu>Share N P sh \<Longrightarrow> \<nu>ShrIdentical N sid \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P a \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e sid a b
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_revert \<blangle> R \<heavy_comma> b \<tycolon> N \<heavy_comma> a \<tycolon> N \<longmapsto> R \<heavy_comma> sh (Gi (-1)) a \<tycolon> N \<brangle>"
  unfolding \<nu>def op_revert_def by (auto 0 4)

subsubsection \<open>tup & det\<close>

definition op_pair :: "('a::lrep) \<times> ('b::lrep) \<times> ('r::stack) \<Rightarrow> (('b \<times> 'a) \<times> 'r) state"
  where "op_pair x = (case x of (a,b,r) \<Rightarrow> StatOn ((b,a),r))"
definition op_depair :: "(('b::lrep) \<times> ('a::lrep)) \<times> ('r::stack) \<Rightarrow> ('a \<times> 'b \<times> 'r) state"
  where "op_depair x = (case x of ((b,a),r) \<Rightarrow> StatOn (a,b,r))"
declare op_pair_def[\<nu>instr] op_depair_def[\<nu>instr]

theorem pr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion> B) \<brangle>" unfolding \<nu>def  op_pair_def by auto
theorem dpr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion> B) \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<brangle>" unfolding \<nu>def  op_depair_def by auto

definition op_crash :: "('r::lrep) \<Rightarrow> ('x::lrep) state" where "op_crash r = SNeg"
lemma op_crash:  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_crash \<blangle> X \<longmapsto> Y \<brangle>" unfolding \<nu>def op_crash_def by auto

subsection \<open>Branch & Loop\<close>

subsubsection \<open>op_if\<close>
definition op_if :: " (('s::lrep) \<flower> ('sr::register_collection) \<Rightarrow> (('t::lrep) \<flower> ('tr::register_collection)) state) \<Rightarrow> ('s \<flower> 'sr \<Rightarrow> ('t \<flower> 'tr) state) \<Rightarrow> (1 word \<times> 's) \<flower> 'sr \<Rightarrow> ('t \<flower> 'tr) state"
  where "op_if brT brF x = (case x of (Proc_Ctx (c,s) r) \<Rightarrow> if c = 1 then brT (Proc_Ctx s r) else brF (Proc_Ctx s r))"
declare op_if_def[\<nu>instr]
theorem if_\<nu>proc: "(\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e c \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_true \<blangle> U \<flower> W \<longmapsto> Vt \<flower> Wt \<brangle>) \<Longrightarrow> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> c \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_false \<blangle> U \<flower> W \<longmapsto> Vf \<flower> Wf \<brangle>)
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if branch_true branch_false \<blangle> U \<heavy_comma> (c \<tycolon> \<bool>) \<flower> W  \<longmapsto> (if c then Vt \<flower> Wt else (Vf \<flower> Wf)) \<brangle>"
  unfolding \<nu>def op_if_def by auto

lemma [simp]: "(if P then (A \<flower> B) else (A' \<flower> B')) = ((if P then A else A') \<flower> (if P then B else B'))" by auto
lemma [simp]: "(if P then (A\<heavy_comma>B) else (A'\<heavy_comma>B')) = ((if P then A else A')\<heavy_comma>(if P then B else B'))" by auto
lemma [simp]: "(if P then \<tort_lbrace>T1\<tort_rbrace> else \<tort_lbrace>T2\<tort_rbrace>) = \<tort_lbrace>if P then T1 else T2\<tort_rbrace>"  by auto
lemma [simp]: "(if P then (x \<tycolon> N) else (y \<tycolon> N)) = ((if P then x else y) \<tycolon> N)"  by auto

subsubsection \<open>while\<close>

consts op_while :: "'c itself \<Rightarrow> (('x::lrep) \<times> ('r::stack) \<flower> ('w::register_collection) \<Rightarrow> (('x \<times> 1 word) \<times> 'r \<flower> 'w) state)
  \<Rightarrow> ('x \<times> 'r \<flower> 'w \<Rightarrow> ('x \<times> 'r \<flower> 'w) state) \<Rightarrow> ('x \<times> 'r \<flower> 'w \<Rightarrow> ('x \<times> 'r \<flower> 'w) state)"
specification ("op_while")
  while_\<nu>proc[simplified PremiseHOL ParamHOL]: "
  ParamHOL P \<Longrightarrow> ParamHOL Rc \<Longrightarrow> ParamHOL Rb \<Longrightarrow> PremiseHOL (wf (Rc O Rb))
  \<Longrightarrow> (\<And>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> (R \<heavy_comma> (x1::'c) \<tycolon> X) \<flower> W \<longmapsto> (R \<heavy_comma> {(y, y \<in> P) | y. (y,x1) \<in> Rc } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (X \<nuFusion> \<bool>)) \<flower> W \<brangle>)
  \<Longrightarrow> (\<And>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> (R \<heavy_comma> x2 \<tycolon> (X \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P)) \<flower> W \<longmapsto> (R \<heavy_comma> {y. (y,x2) \<in> Rb} \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X) \<flower> W \<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_while TYPE('c) brC brB \<blangle> (R \<heavy_comma> x \<tycolon> X) \<flower> W \<longmapsto> (R \<heavy_comma> - P \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X) \<flower> W \<brangle>"
  apply (rule exI) using op_crash by auto

subsubsection \<open>recursion\<close>

consts op_recursion :: " 'a itself \<times> 'b itself \<Rightarrow>
    ((('u::lrep) \<times> void \<Rightarrow> (('v::lrep) \<times> void) state) \<Rightarrow> ('u \<times> void \<Rightarrow> ('v \<times> void) state)) \<Rightarrow> ('u \<times> ('r::stack) \<Rightarrow> ('v \<times> 'r) state) "
specification ("op_recursion")
  recursion_\<nu>proc[simplified PremiseHOL ParamHOL]:
  "ParamHOL h \<Longrightarrow> ParamHOL M \<Longrightarrow> ParamHOL WF \<Longrightarrow> PremiseHOL (wf WF) \<Longrightarrow>
  (\<And>x' g. (\<And>x''. PremiseHOL ((x'',x') \<in> WF) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> \<^bold>E\<^bold>N\<^bold>D Void \<heavy_comma> x'' \<tycolon> N \<longmapsto> \<^bold>E\<^bold>N\<^bold>D Void \<heavy_comma> h x'' \<tycolon> M \<brangle>)
      \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f g \<blangle> \<^bold>E\<^bold>N\<^bold>D Void \<heavy_comma>  x' \<tycolon> N \<longmapsto> \<^bold>E\<^bold>N\<^bold>D Void\<heavy_comma> h x' \<tycolon> M \<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion (TYPE('a), TYPE('d)) f \<blangle> R\<heavy_comma> (x::'a) \<tycolon> N \<longmapsto> R\<heavy_comma> (h x::'d) \<tycolon> M \<brangle>"
  apply (rule exI) using op_crash by auto

section \<open>Arithmetic instructions\<close>

\<nu>overloads "+" and round_add and "<" and "-" and "="


subsection \<open>Integer arithmetic\<close>

subsubsection \<open>constant\<close>

definition op_const_int :: "('w::len) itself \<Rightarrow> ('w::len) word \<Rightarrow> ('r::stack) \<Rightarrow> ('w word \<times> 'r) state"
  where "op_const_int _ c r = StatOn (c,r)"
theorem const_nat_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) c \<blangle> R \<longmapsto> R \<heavy_comma> unat c \<tycolon> \<nat>['w] \<brangle>"
  unfolding \<nu>def op_const_int_def by auto
theorem const_nat_round_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (of_nat n) \<blangle> R \<longmapsto> R \<heavy_comma> n \<tycolon> \<nat>\<^sup>r['w] \<brangle>"
  unfolding \<nu>def op_const_int_def by auto

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t ((numeral x) \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (Word.of_nat (numeral x)) \<blangle> Z \<longmapsto> Z \<heavy_comma> (numeral x) \<tycolon> \<nat>['w] \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 apply auto by (metis mod_if unat_bintrunc unat_numeral)
  \<comment> \<open>Only literal number could be constructed automatically\<close>
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (0 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<blangle> Z \<longmapsto> Z \<heavy_comma> 0 \<tycolon> \<nat>['w] \<brangle>"
  unfolding AutoConstruct_def using const_nat_\<nu>proc by (metis unat_0) 
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (1 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<blangle> Z \<longmapsto> Z \<heavy_comma> 1 \<tycolon> \<nat>['w] \<brangle>"
  unfolding AutoConstruct_def using const_nat_\<nu>proc by (metis unat_1)

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t ((numeral x) \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (Word.of_nat (numeral x)) \<blangle> Z \<longmapsto> Z \<heavy_comma> (numeral x) \<tycolon> \<nat>\<^sup>r['w] \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by auto
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (0 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<blangle> Z \<longmapsto> Z \<heavy_comma> 0 \<tycolon> \<nat>\<^sup>r['w] \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by auto
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (1 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<blangle> Z \<longmapsto> Z \<heavy_comma> 1 \<tycolon> \<nat>\<^sup>r['w] \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by auto

(* schematic_goal "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t 3 \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f
  \<blangle>\<flower_L>\<medium_left_bracket> A \<flower_L>\<flower>\<flower_R>X\<medium_right_bracket>\<flower_R>   \<longmapsto> ?T \<brangle>" by (rule \<nu>intro) *)

subsubsection \<open>plus\<close>

instantiation typing :: (lrep, plus) plus begin
definition plus_typing :: "('a,'b) typing \<Rightarrow> ('a,'b) typing \<Rightarrow> ('a,'b) typing"
  where "nu_of a = nu_of b \<Longrightarrow> plus_typing a b = (case a of xa \<tycolon> Na \<Rightarrow> case b of xb \<tycolon> Nb \<Rightarrow> xa + xb \<tycolon> Na)"
lemma [simp]: "(x \<tycolon> N) + (y \<tycolon> N) = (x + y \<tycolon> N)" using plus_typing_def by auto
instance by standard
end

definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> ('r::lrep) \<Rightarrow> (('a::len) word \<times> 'r) state"
  where "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
declare op_add_def[\<nu>instr]

theorem add_nat_\<nu>proc[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b::len) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle>\<R> \<heavy_comma> x \<tycolon> \<nat>['b] \<heavy_comma> y \<tycolon> \<nat>['b] \<longmapsto> \<R> \<heavy_comma> x + y \<tycolon> \<nat>['b] \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: of_nat_inverse) 

theorem add_nat_mod[\<nu>overload round_add]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> \<RR> \<heavy_comma> y \<tycolon> \<nat>['b::len] \<heavy_comma> x \<tycolon> \<nat>['b] \<longmapsto> \<RR> \<heavy_comma> ((x + y) mod 2^(LENGTH('b))) \<tycolon> \<nat>['b]  \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: unat_word_ariths)

theorem add_nat_round[\<nu>overload +]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>\<^sup>r['b::len]\<heavy_comma> y \<tycolon> \<nat>\<^sup>r['b] \<longmapsto> R\<heavy_comma> (x + y) \<tycolon> \<nat>\<^sup>r['b] \<brangle>"
  unfolding op_add_def Procedure_def by auto


subsubsection \<open>subtraction\<close>
definition op_sub :: "('a::len) itself \<Rightarrow> 'a word \<times> 'a word \<times> ('r::lrep) \<Rightarrow> ('a word \<times> 'r) state"
  where "op_sub _ p = (case p of (a,b,r) \<Rightarrow> if a \<le> b then StatOn (b - a, r) else STrap)"
declare op_sub_def[\<nu>instr]
theorem sub_nat_\<nu>proc[\<nu>overload -]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub TYPE('w::len) \<blangle> \<R> \<heavy_comma> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w] \<longmapsto> \<R> \<heavy_comma> x - y \<tycolon> \<nat>['w] \<brangle>"
  unfolding \<nu>def op_sub_def apply auto apply (meson le_less unat_sub) using word_le_nat_alt by blast
  
subsubsection \<open>less\<close>
definition op_lt :: " ('w::len) itself \<Rightarrow> ('w word \<times> 'w word \<times> ('r::lrep)) \<Rightarrow> (1 word \<times> 'r) state"
  where "op_lt _ s = (case s of (a,b,r) \<Rightarrow>  StatOn ((if  b < a then 1 else 0), r))"
declare op_lt_def[\<nu>instr]
theorem op_lt_\<nu>proc[\<nu>overload <]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt (TYPE('w::len)) \<blangle>\<R>\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w] \<longmapsto> \<R>\<heavy_comma> (x < y) \<tycolon> \<bool> \<brangle>"
  unfolding \<nu>def op_lt_def by (auto simp add: word_less_nat_alt)

subsubsection \<open>equal\<close>

definition op_equal :: " ('a::{ceq,lrep}) \<times> 'a \<times> ('r::stack) \<Rightarrow> (1 word \<times> 'r) state"
  where "op_equal s = (case s of (a,b,r) \<Rightarrow>
    if ceqable b a then StatOn ((if ceq b a then 1 else 0), r) else STrap)"
theorem op_equal[\<nu>overload =]:
  "\<nu>CEqual N P eq \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P a b \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal \<blangle> R\<heavy_comma> a \<tycolon> N\<heavy_comma> b \<tycolon> N \<longmapsto> R\<heavy_comma> eq a b \<tycolon> \<bool> \<brangle>"
  unfolding \<nu>def op_equal_def by (auto 4 5)

section \<open>Tuple Operations\<close>

subsection \<open>Tuple construction & destruction\<close>

subsubsection \<open>op_constr_tuple\<close>

definition op_constr_tuple :: "('a::field_list) \<times> ('r::stack) \<Rightarrow> ('a tuple \<times> 'r) state"
  where "op_constr_tuple = (\<lambda>(a,r). StatOn (Tuple a, r))"

theorem tup_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_constr_tuple \<blangle> R\<heavy_comma> x \<tycolon> X \<longmapsto> R\<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace> \<brangle>"
  unfolding op_constr_tuple_def Procedure_def by simp

subsubsection \<open>op_destr_tuple\<close>

definition op_destr_tuple :: "('a::field_list) tuple \<times> ('r::stack) \<Rightarrow> ('a \<times> 'r) state"
  where "op_destr_tuple ar = (case ar of (Tuple a, r) \<Rightarrow> StatOn (a,r))"

theorem det_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_destr_tuple \<blangle> R\<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace> \<longmapsto> R\<heavy_comma> x \<tycolon> X \<brangle>"
  unfolding Procedure_def op_destr_tuple_def by (simp add: tuple_forall)

section \<open>Memory Operations\<close>

subsection \<open>Allocation\<close>

\<nu>overloads alloc

subsubsection \<open>op_alloc_id_space\<close>

definition op_alloc_id_space :: " identifier \<times> ('r::stack) \<Rightarrow> (identifier \<times> identifier \<times> ('r::stack)) state"
  where "op_alloc_id_space s = (case s of (i,r) \<Rightarrow> StatOn (alloc_identifier_space i, alloc_identifier i, r))"

theorem op_alloc_id_space_\<nu>proc[\<nu>overload alloc]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc_id_space \<blangle> R\<heavy_comma> i\<hyphen>j \<tycolon> IdSrc \<longmapsto> R\<heavy_comma> i\<hyphen>j+1 \<tycolon> IdSrc \<heavy_comma> i\<hyphen>j\<hyphen>0 \<tycolon> IdSrc\<brangle>"
  unfolding op_alloc_id_space_def Procedure_def by (simp add: lrep_exps)

subsubsection \<open>op_alloc\<close>

definition op_alloc :: "('spc::len) itself \<Rightarrow> ('x::{zero,field}) itself
    \<Rightarrow> identifier \<times> ('bits::len) word \<times> ('r::stack) \<Rightarrow> (identifier \<times> ('spc, 'x) memref \<times>'r) state"
  where "op_alloc _ _ s = (case s of (i,n,r) \<Rightarrow> if segment_size i = unat n \<and> segment_type i = llty TYPE('x) then
    StatOn (alloc_identifier i, Tuple (memptr (0 \<left_fish_tail>i |+ 0), 0 \<left_fish_tail> memcon (i |+ 0) 0), r) else SNeg)"

theorem op_alloc_\<nu>proc[\<nu>overload alloc]:
  "\<nu>Zero N zero \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc TYPE('spc::len) TYPE('x)
      \<blangle> R\<heavy_comma> n \<tycolon> \<nat>[('bits::len)] \<heavy_comma> i\<hyphen>j \<tycolon> IdSrc \<longmapsto> R\<heavy_comma> Gi 0 \<left_fish_tail>(i\<hyphen>j |+ 0) \<R_arr_tail> Gi 0 \<left_fish_tail> zero \<tycolon> Ref N \<heavy_comma> i\<hyphen>j + 1 \<tycolon> IdSrc \<brangle>"
  for N :: "('x::{zero,field},'b) nu"
  unfolding \<nu>def op_alloc_def by auto

section \<open>Tests\<close>

ML \<open>Locale.get_locales @{theory}\<close>
ML \<open>val ctx = Locale.init "NuPrim.ceq_lrep" @{theory}
val x = Assumption.all_prems_of ctx\<close>

(* schematic_goal [simplified, simplified \<nu>post_construct]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (233 \<tycolon> \<nat>[32], ((copy_reg::((32 word register \<times> 32 word register), (32 word register \<times> 32 word register), (32 word) register, 32 word register) address \<Rightarrow> (32 word, nat) typing)) (address_left address_here)
+ (233 \<tycolon>  \<nat>[32])) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<blangle>((?Z1::(?'a::lrep) set) \<flower> \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r A = \<tort_lbrace> 16 \<tycolon> \<nat>[32]\<tort_rbrace> and_ty \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r B = \<tort_lbrace> 0 \<tycolon> \<nat>[32] \<tort_rbrace>) \<longmapsto> (?Z2::(?'b::lrep) set) \<brangle>"
  by  (\<nu>resolve \<nu>intro (\<nu>intro'))  *)


declare Nat.One_nat_def[simp del]

fun fib :: "nat \<Rightarrow> nat"
  where "fib x = (if x = 0 then 1 else if x = 1 then 1 else fib (x-1) + fib (x-2))"

proc fibx : "x \<tycolon> \<nat>[32]" \<longmapsto> "fib x \<tycolon> \<nat>\<^sup>r[32]"
  \<bullet> x recursion fib \<open>\<nat>\<^sup>r[32]\<close> less_than \<medium_left_bracket> (g_\<nu>proc)
  \<bullet> \<rightarrow> x x 0 = if \<medium_left_bracket> \<bullet> \<open>1\<tycolon>\<nat>\<^sup>r[32]\<close> \<medium_right_bracket> \<medium_left_bracket> (c0[used])
      \<bullet> x 1 = if \<medium_left_bracket> \<bullet> \<open>1\<tycolon>\<nat>\<^sup>r[32]\<close> \<medium_right_bracket> \<medium_left_bracket> (c1[used]) \<bullet> x 1 - g \<rightarrow> f1 x 2 - g \<rightarrow> f2 f1 f2 + \<medium_right_bracket>
  \<medium_right_bracket> \<medium_right_bracket>
  finish

  thm fibx_\<nu>proc

fun ackman :: "(nat \<times> nat) \<Rightarrow> nat"
  where "ackman (0,n) = Suc n"
  | "ackman (Suc m, 0) = ackman (m,1)"
  | "ackman (Suc m, Suc n) = ackman (m, ackman (Suc m, n))"

thm begin_proc_ctx
proc ackman : "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "ackman (x,y) \<tycolon> \<nat>[32]" if cond: "ackman (x,y) < 2^32"
  \<bullet> x y pr cast where \<open>{xy. ackman xy < 2^32}\<close> affirm using cond by simp
  \<bullet> recursion ackman \<open>\<nat>[32]\<close> \<open>less_than <*lex*> less_than\<close> \<medium_left_bracket> (g_\<nu>proc)
  \<nu>obtain m n where th1[simp]: "x' = (m,n)" by (cases x')
  \<bullet> cast E \<Longrightarrow> th2[used] \<bullet> dpr \<rightarrow> (m,n) m 0 = if \<medium_left_bracket> \<bullet> n 1 + \<medium_right_bracket> \<medium_left_bracket> \<bullet> m 1 -
  \<bullet> n 0 = if \<medium_left_bracket> \<bullet> 1 pr 
  \<bullet> cast where \<open>{xy. ackman xy < 2^32}\<close> affirm apply (cases m) by auto
  \<bullet> g \<medium_right_bracket> \<medium_left_bracket> \<bullet> m n 1 - pr
\<bullet> cast where \<open>{xy. ackman xy < 2^32}\<close> affirm apply (cases m; cases n) by auto
  note c
  \<nu>debug 
  note c

end

definition [simp]:"difference x y = (if x < y then y - x else x - y)"
xproc diff : "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "(difference x y \<tycolon> \<nat>[32])"
  \<bullet> x while \<open>{x. 0 < x}\<close> Id less_than \<medium_left_bracket> \<bullet> \<rightarrow> a a 0 a < pr \<medium_right_bracket> \<medium_left_bracket> \<bullet> cast E \<Longrightarrow> th1[used] \<bullet> 1 -  \<medium_right_bracket>
  \<bullet> cast E \<nu>choose a where "some = a" by auto
  \<bullet> \<Longrightarrow> th1[simp] drop_fact th1
  \<bullet> drop x y < if \<medium_left_bracket> \<bullet> y x - \<medium_right_bracket> \<medium_left_bracket> \<bullet> x y - \<medium_right_bracket>
  finish

end

proc add2 : "(( x \<tycolon> \<nat>[32]) named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if "x < 100" and "y < 100"
  \<nu>have x[used]: "x < 100 \<and> y < 100" using that by auto
  \<bullet> x x y + < if \<medium_left_bracket>
  \<nu>obtain z where c: "x < z" by auto \<medium_right_bracket>
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