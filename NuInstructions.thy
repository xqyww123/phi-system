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
lemma [simp]: "(if P then \<tort_lbrace>T1\<tort_rbrace> else \<tort_lbrace>T2\<tort_rbrace>) = \<tort_lbrace>if P then T1 else T2\<tort_rbrace>"  by auto
lemma [simp]: "(if P then (x \<tycolon> N) else (y \<tycolon> N)) = ((if P then x else y) \<tycolon> N)"  by auto


section \<open>Arithmetic instructions\<close>

\<nu>overloads "+" and round_add and "<" and "-"


subsection \<open>Integer arithmetic\<close>

subsubsection \<open>constant\<close>

definition op_const_int :: "('w::len) itself \<Rightarrow> ('w::len) word \<Rightarrow> ('r::lrep) \<Rightarrow> ('w word \<times> 'r) state"
  where "op_const_int _ c r = StatOn (c,r)"
theorem const_nat_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) c \<blangle> R \<longmapsto> unat c \<tycolon> \<nat>['w]\<boxbar>R \<brangle>"
  unfolding \<nu>def op_const_int_def by auto

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t ((numeral x) \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (Word.of_nat (numeral x)) \<blangle> EoC Z \<longmapsto> (numeral x) \<tycolon> \<nat>['w]\<boxbar>EoC Z \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 apply auto by (metis mod_if unat_bintrunc unat_numeral)
  \<comment> \<open>Only literal number could be constructed automatically\<close>
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (0 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<blangle> EoC Z \<longmapsto> 0 \<tycolon> \<nat>['w]\<boxbar>EoC Z \<brangle>"
  unfolding EoC_def AutoConstruct_def using const_nat_\<nu>proc by (metis unat_0) 
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (1 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<blangle> EoC Z \<longmapsto> 1 \<tycolon> \<nat>['w]\<boxbar>EoC Z \<brangle>"
  unfolding EoC_def AutoConstruct_def using const_nat_\<nu>proc by (metis unat_1) 

subsubsection \<open>plus\<close>

instantiation typing :: (lrep, plus) plus begin
definition plus_typing :: "('a,'b) typing \<Rightarrow> ('a,'b) typing \<Rightarrow> ('a,'b) typing"
  where "nu_of a = nu_of b \<Longrightarrow> plus_typing a b = (case a of xa \<tycolon> Na \<Rightarrow> case b of xb \<tycolon> Nb \<Rightarrow> xa + xb \<tycolon> Na)"
lemma [simp]: "(x \<tycolon> N) + (y \<tycolon> N) = (x + y \<tycolon> N)" using plus_typing_def by auto
instance by standard
end

lemma[\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (A,B) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> (EoC Z \<flower> W1) \<longmapsto> (xa \<tycolon> Na\<boxbar> xb \<tycolon> Nb\<boxbar>EoC Z \<flower> W2) \<brangle> \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (+) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c add \<blangle> (xa \<tycolon> Na\<boxbar> xb \<tycolon> Nb\<boxbar>EoC Z \<flower> W2) \<longmapsto> (xc \<tycolon> Nc\<boxbar>EoC Z \<flower> W3)\<brangle> \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (A + B) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> add) \<blangle>  (EoC Z \<flower> W1) \<longmapsto> (xc \<tycolon> Nc\<boxbar>EoC Z \<flower> W3) \<brangle>"
  unfolding EoC_def AutoConstruct_def by rule+

definition op_add :: "nat \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> ('r::lrep) \<Rightarrow> (('a::len) word \<times> 'r) state"
  where "op_add w p = (case p of (a,b,r) \<Rightarrow> if LENGTH('a) = w then StatOn (a+b, r) else STrap)"
declare op_add_def[\<nu>instr]

theorem add_nat_\<nu>proc[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b::len) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar>\<R> \<longmapsto> x + y \<tycolon> \<nat>['b] \<boxbar>\<R> \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: of_nat_inverse) 

lemma[\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b::len) \<Longrightarrow>
  \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (+) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle> x \<tycolon> \<nat>['b] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar>EoC Z \<longmapsto> x + y \<tycolon> \<nat>['b] \<boxbar>EoC Z \<brangle>"
  unfolding AutoConstruct_def EoC_def by (auto simp add: add_nat_\<nu>proc)
lemma[\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b::len) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> EoC Z \<longmapsto> x \<tycolon> \<nat>['b] \<boxbar> y \<tycolon> \<nat>['b] \<boxbar>EoC Z \<brangle> \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> op_add (LENGTH('b))) \<blangle> EoC Z \<longmapsto> \<tort_lbrace>(x \<tycolon> \<nat>['b]) + (y \<tycolon> \<nat>['b])\<tort_rbrace> \<boxbar>EoC Z \<brangle>"
  by (auto simp add: add_nat_\<nu>proc)


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

ML \<open>Locale.get_locales @{theory}\<close>
ML \<open>val ctx = Locale.init "NuPrim.ceq_lrep" @{theory}
val x = Assumption.all_prems_of ctx\<close>

schematic_goal [simplified, simplified \<nu>post_construct]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (233 \<tycolon> \<nat>[32], ((copy_reg::((32 word register \<times> 32 word register), (32 word register \<times> 32 word register), (32 word) register, 32 word register) address \<Rightarrow> (32 word, nat) typing)) (address_left address_here)
+ (233 \<tycolon>  \<nat>[32])) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<blangle>((?Z1::(?'a::lrep) set) \<flower> \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r A = \<tort_lbrace> 16 \<tycolon> \<nat>[32]\<tort_rbrace> and_ty \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r B = \<tort_lbrace> 0 \<tycolon> \<nat>[32] \<tort_rbrace>) \<longmapsto> (?Z2::(?'b::lrep) set) \<brangle>"
  by  (\<nu>resolve \<nu>intro (\<nu>intro')) 

 thm \<nu>intro

definition [simp]:"difference x y = (if x < y then y - x else x - y)"

context includes show_more begin
thm address_here_mapper
thm new_reg [OF address_left_mapper[OF address_here_mapper] ]
thm new_reg
term address_here
thm address_here_mapper[THEN new_reg]
thm new_reg[OF address_here_mapper]
end

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