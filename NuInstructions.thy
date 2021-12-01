theory NuInstructions
  imports NuSys NuBasicAbstractors NuLLReps
  keywords
     "\<up>:" "\<Up>:" "\<down>:" "\<Down>:" "subj" "always" "heap" "--" :: quasi_command
  abbrevs "|^" = "\<up>"
    and "||^" = "\<Up>"
    and "|v" = "\<down>"
    and "||v" = "\<Down>"
    and "<up>" = "\<up>"
    and "<down>" = "\<down>"
    and "<Up>" = "\<Up>"
    and "<Down>" = "\<Down>"
begin

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]
declare Separation_assoc[simp]

text \<open>Basic instructions\<close>

section \<open>Structural instructions\<close>

subsection \<open>Basic sequential instructions\<close>

subsubsection \<open>crash\<close>

definition op_crash :: "('x::stack) \<longmapsto> ('y::stack)" where "op_crash _ = PartialCorrect"
lemma crash_\<nu>app[no_atp]:  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_crash \<blangle> X \<longmapsto> Y \<brangle>" unfolding \<nu>def op_crash_def by auto


subsubsection \<open>drop\<close>

definition op_drop :: "('a::lrep) \<times> ('r::stack) \<longmapsto> 'r" where
  "op_drop x = (case x of (h,a,r) \<Rightarrow> Success (h,r))"
declare op_drop_def[\<nu>instr]
theorem drop_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> R\<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_drop_def by (auto simp add: nu_exps)

subsubsection \<open>duplication\<close>

definition op_dup :: "('a::lrep) \<times> ('r::stack) \<longmapsto> ('a \<times> 'a \<times> 'r)"
  where "op_dup x = (case x of (h,a,r) \<Rightarrow> Success (h, a, a, r))"
declare op_dup_def[\<nu>instr]
theorem dup_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dup \<blangle> R\<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> X\<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing\<brangle>"
  unfolding \<nu>def op_dup_def by (auto simp add: nu_exps)


subsubsection \<open>pair & de-pair\<close>

definition op_pair :: "('a::lrep) \<times> ('b::lrep) \<times> ('r::stack) \<longmapsto> (('b \<times> 'a) \<times> 'r)"
  where "op_pair = (\<lambda>(h,a,b,r). Success (h,(b,a),r))"
definition op_depair :: "(('b::lrep) \<times> ('a::lrep)) \<times> ('r::stack) \<longmapsto> ('a \<times> 'b \<times> 'r)"
  where "op_depair = (\<lambda>(h,(b,a),r). Success (h,a,b,r))"
(* declare op_pair_def[\<nu>instr] op_depair_def[\<nu>instr] *)

lemma pr_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B)\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def  op_pair_def by (auto simp add: nu_exps)
lemma dpr_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B)\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def  op_depair_def by (auto simp add: nu_exps)

lemma hpr_\<nu>app: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<heavy_asterisk> h1 \<tycolon> H1 \<heavy_asterisk> h2 \<tycolon> H2 \<longmapsto> H \<heavy_asterisk> (h2,h1) \<tycolon> H2 \<^emph> H1"
  unfolding Cast_def SepNu_to_SepSet Separation_assoc by blast
lemma hdpr_\<nu>app: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<heavy_asterisk> (h2,h1) \<tycolon> H2 \<^emph> H1 \<longmapsto> H \<heavy_asterisk> h1 \<tycolon> H1 \<heavy_asterisk> h2 \<tycolon> H2"
  unfolding Cast_def SepNu_to_SepSet Separation_assoc by blast

(* \<nu>processor pair_auto_dest 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<flower> W)\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema} |> NuSys.accept_proc ctx)\<close>
\<nu>processor pair_auto_dest' 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B))\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema'} |> NuSys.accept_proc ctx)\<close> *)

subsubsection \<open>let & local_value\<close>

definition op_let :: " ('v::lrep \<Rightarrow> 's::stack \<longmapsto> 't::stack) \<Rightarrow> ('v \<times> 's \<longmapsto> 't)"
  where "op_let body = (\<lambda>(h,v,s). body v (h,s))"
lemma op_let: " (\<And>p. p \<nuLinkL> A \<nuLinkR> a \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body p \<blangle> X \<longmapsto> X' \<brangle>) \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_let body \<blangle> X\<heavy_comma>^ a \<tycolon> A \<longmapsto> X' \<brangle>"
  unfolding Procedure_def op_let_def by (auto simp add: nu_exps)

definition op_local_value :: " 'v::lrep \<Rightarrow> 's::stack \<longmapsto> 'v \<times> 's "
  where "op_local_value v = (\<lambda>(h,s). Success (h,v,s))"
lemma op_local_value: "v \<nuLinkL> A \<nuLinkR> a \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_local_value v \<blangle> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> S\<heavy_comma> a \<tycolon> A\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding Procedure_def op_local_value_def by (auto simp add: nu_exps)

ML_file "library/local_value.ML"

\<nu>processor let_local_value 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [\<HH>] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H)\<close> \<open>let open Parse in
  fn ctx => fn sequent => (($$$ "\<rightarrow>" || $$$ "--") -- list1 binding) >> (fn (keyword,idts) => fn _ =>
    Local_Value.mk_let (keyword = "--") (rev idts) sequent ctx
) end\<close>


subsubsection \<open>function call\<close>
  \<comment> \<open>A function is the program function in the ordinary meaning that called by pushing stack frame, rarely inline
    (whereas a procedure is generally inline), which is a procedure of \<^term>\<open>Void\<close> as its stack remainder so that
    it can only access its arguments and never the stack remainder.
    A function always corresponds an LLVM function, whereas other ordinary procedures are totally inline at the calling place generally
      except some cases of optimization.
    Only a function but no other ordinary procedure locates at a decided address in memory during the runtime,
    so that has function pointers to it, and therefore can be indirectly called by the pointer. \<close>



(* definition strip_end_tail :: " ('a::lrep \<times> void \<longmapsto> ('b::lrep \<times> void)) \<Rightarrow> 'a \<times> ('r::stack) \<longmapsto> ('b \<times> 'r)"
  where "strip_end_tail f s = (case s of (a,r) \<Rightarrow> bind (f (a,void)) (\<lambda>(b,_). StatOn (b,r)))"
lemma strip_end_tail: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> A \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c strip_end_tail f \<blangle> R\<heavy_comma> A \<longmapsto> R\<heavy_comma> B \<brangle>"
  unfolding strip_end_tail_def Procedure_def bind_def by (auto 4 4)
*)


subsection \<open>Branches & Loops\<close>

subsubsection \<open>sel\<close>

definition op_sel :: " (1 word \<times> 'a \<times> 'a \<times> 'r) \<longmapsto> ('a \<times> 'r)"
  where "op_sel s = (case s of (heap,c,b,a,r) \<Rightarrow> if c = 1 then Success (heap,a,r) else Success (heap,b,r))"

lemma sel_\<nu>app: " \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sel \<blangle> R\<heavy_comma> a \<tycolon> T\<heavy_comma> b \<tycolon> T\<heavy_comma> c \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (if c then a else b) \<tycolon> T\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle> "
  unfolding Procedure_def op_sel_def by (auto simp add: nu_exps)

subsubsection \<open>if\<close>

definition op_if :: " ('s::stack \<longmapsto> 't::stack) \<Rightarrow> ('s \<longmapsto> 't) \<Rightarrow> (1 word \<times> 's) \<longmapsto> 't"
  where "op_if brT brF s = (case s of (heap,c,r) \<Rightarrow> if c = 1 then brT (heap,r) else brF (heap,r))"
declare op_if_def[\<nu>instr]

theorem if_\<nu>app:
  "(cond \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_true \<blangle> X \<longmapsto> Y\<^sub>T \<brangle>)
    \<longrightarrow> SameNuTy Y\<^sub>T Y\<^sub>F
    \<longrightarrow> (\<not> cond \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_false \<blangle> X \<longmapsto> Y\<^sub>F \<brangle>)
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if branch_true branch_false \<blangle> X \<heavy_comma>^ cond \<tycolon> \<bool> \<longmapsto> (if cond then Y\<^sub>T else Y\<^sub>F) \<brangle>"
  unfolding \<nu>def op_if_def by (auto simp add: nu_exps)
(* text \<open>Despite the feasibility of divergence of \<nu>-types in the branch, i.e.
  \<^term>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if branch_true branch_false \<blangle> x \<tycolon> X \<heavy_comma>^ cond \<tycolon> \<bool> \<longmapsto> (if cond then y\<^sub>T else y\<^sub>F) \<tycolon> (if cond then Y\<^sub>T else Y\<^sub>F ) \<brangle>\<close>,
  from the design of the programming principles, considering the role of \<nu>-types which encodes the invariant properties,
  we prohibit the divergence of \<nu>-types.\<close> *)

lemma [simp]: "(if P then \<tort_lbrace>x \<tycolon> X\<tort_rbrace> else \<tort_lbrace>y \<tycolon> Y\<tort_rbrace>) = \<tort_lbrace>(if P then x else y) \<tycolon> (if P then X else Y)\<tort_rbrace>" by simp
lemma [simp]: "(if P then (a,b) else (a',b')) = ((if P then a else a'), (if P then b else b'))" by simp
(* lemma AA: "(if P then A else B) = (\<lambda>x. if P then A x else B x)" by simp *)
lemma [simp]: "(if P then (S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) else (S'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H')) = ((if P then S else S')\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (if P then H else H'))" by simp
lemma [simp]: "(if P then (A\<heavy_comma> B) else (A'\<heavy_comma> B')) = ((if P then A else A')\<heavy_comma> (if P then B else B'))" by simp
lemma [simp]: "(if P then (A \<heavy_asterisk> B) else (A' \<heavy_asterisk> B')) = ((if P then A else A') \<heavy_asterisk> (if P then B else B'))" by simp
(* lemma [simp]: "(if P then (A \<^bold>a\<^bold>n\<^bold>d B) else (A' \<^bold>a\<^bold>n\<^bold>d B')) = ((if P then A else A') \<^bold>a\<^bold>n\<^bold>d (if P then B else B'))"  by auto *)
lemma [simp]: "(if P then Labelled name T else Labelled name' T') = Labelled name (if P then T else T')" unfolding Labelled_def by simp
lemma [simp]: "(if P then a \<R_arr_tail> x else a \<R_arr_tail> x') = a \<R_arr_tail> (if P then x else x')" by auto


subsubsection \<open>do while\<close>

inductive SemDoWhile :: "('r \<longmapsto> 1 word \<times> 'r) \<Rightarrow> heap \<times> 'r \<Rightarrow> 'r state \<Rightarrow> bool" where
  "f s = Success (h,0,r) \<Longrightarrow> SemDoWhile f s (Success (h,r))"
| "f s = PartialCorrect \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "f s = Fail \<Longrightarrow> SemDoWhile f s Fail"
| "f s = Success (h,1,r) \<Longrightarrow> SemDoWhile f (h,r) s'' \<Longrightarrow> SemDoWhile f s s''"

lemma SemDoWhile_deterministic:
  assumes "SemDoWhile c s s1"
      and "SemDoWhile c s s2"
    shows "s1 = s2"
proof -
  have "SemDoWhile c s s1 \<Longrightarrow> (\<forall>s2. SemDoWhile c s s2 \<longrightarrow> s1 = s2)"
    by (induct rule: SemDoWhile.induct) (subst SemDoWhile.simps, simp)+
  thus ?thesis
    using assms by simp
qed

lemma SemDoWhile_deterministic2: " SemDoWhile body s x \<Longrightarrow> The ( SemDoWhile body s) = x"
  using SemDoWhile_deterministic by blast

definition DoWhile :: "('r \<longmapsto> 1 word \<times> 'r) \<Rightarrow> 'r \<longmapsto> 'r" where
  "DoWhile f s = (if (\<exists>y. SemDoWhile f s y) then The (SemDoWhile f s) else PartialCorrect)"

lemma "__DoWhile___\<nu>app": "(\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<blangle> X x \<longmapsto> \<exists>* x'. X x' \<heavy_comma>^ P x' \<tycolon> \<bool> \<brangle>)
  \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c DoWhile body \<blangle> X x \<longmapsto> \<exists>* x'. X x' \<and>\<^sup>s (\<not> P x') \<brangle>"
(*  for X :: "(heap \<times> 'a::lrep, 'b) \<nu>" *)
  unfolding DoWhile_def Procedure_def Auto_def
  apply (auto simp add: SemDoWhile_deterministic2 simp add: nu_exps)
  subgoal for a b xa
    apply (rotate_tac 2)
    by (induct  body "(a, b)" xa arbitrary: a b x rule: SemDoWhile.induct) (auto 0 7 simp add: nu_exps)
  done


lemma do_while_\<nu>app:
  "Variant_Cast vars S S' \<longrightarrow>
  \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m cond \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond vars \<longrightarrow>
  (\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<blangle> S' x \<longmapsto> \<exists>* x'. (S' x' \<heavy_comma>^ cond x' \<tycolon> \<bool>) \<brangle>) \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c DoWhile body \<blangle> S \<longmapsto> \<exists>* x'. S' x' \<and>\<^sup>s (\<not> cond x') \<brangle>"
  unfolding Variant_Cast_def Premise_def apply simp
  using "__DoWhile___\<nu>app"[of "cond" _ "S'", unfolded Premise_def] by blast


subsubsection \<open>while\<close>

proc while: \<open>S'\<close> \<longmapsto> \<open>\<exists>* x. S x \<and>\<^sup>s (\<not> cond x)\<close>
  for S' :: " (heap \<times> 'b::stack) set"
  requires [unfolded Variant_Cast_def, simp]: "Variant_Cast vars S' S"
    and Cond_\<nu>app: "\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<blangle> S x \<longmapsto> \<exists>* x'. (S x'\<heavy_comma>^ cond x' \<tycolon> \<bool>)\<brangle>"
    and Body_\<nu>app: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<blangle> S x \<longmapsto> \<exists>* x'. S x' \<brangle>"
  \<bullet> Cond if \<medium_left_bracket> do_while x' \<open>cond x'\<close> \<medium_left_bracket> Body Cond \<medium_right_bracket> subj \<open>\<not> cond x'\<close> \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>
  finish


subsubsection \<open>recursion\<close>

inductive SemRec :: "(('x \<longmapsto> 'y) \<Rightarrow> ('x \<longmapsto> 'y)) \<Rightarrow> heap \<times> 'x \<Rightarrow> 'y state \<Rightarrow> bool" where
  SemRec_I0: "(\<And>g. F g x = y) \<Longrightarrow> SemRec F x y"
| SemRec_IS: "SemRec (F o F) x y \<Longrightarrow> SemRec F x y"

lemma SemRec_IR: "SemRec F x y \<Longrightarrow> SemRec (F o F) x y"
  by (induct rule: SemRec.induct, rule SemRec_I0, simp)

lemma SemRec_deterministic:
  assumes "SemRec c s s1" and "SemRec c s s2" shows "s1 = s2"
proof -
  have "SemRec c s s1 \<Longrightarrow> (\<forall>s2. SemRec c s s2 \<longrightarrow> s1 = s2)"
    apply (induct rule: SemRec.induct)
     apply clarify
    subgoal for F a b y s2 apply (rotate_tac 1)
      apply (induct rule: SemRec.induct) by auto 
    apply clarify apply (blast intro: SemRec_IR) done
  thus ?thesis using assms by simp
qed

lemma SemRec_deterministic2: " SemRec body s x \<Longrightarrow> The ( SemRec body s) = x"
  using SemRec_deterministic by blast

definition op_recursion :: "(('x \<longmapsto> 'y) \<Rightarrow> ('x \<longmapsto> 'y)) \<Rightarrow> 'x \<longmapsto> 'y"
  where "op_recursion F s = (if (\<exists>t. SemRec F s t) then The (SemRec F s) else PartialCorrect)"

lemma op_recursion:
  "(\<And>g x'. (\<forall>x''. \<^bold>f\<^bold>u\<^bold>n\<^bold>c g \<blangle> X x'' \<longmapsto> Y x'' \<brangle>) \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c F g \<blangle> X x' \<longmapsto> Y x' \<brangle>) \<Longrightarrow>
    (\<forall>x. \<^bold>f\<^bold>u\<^bold>n\<^bold>c op_recursion F \<blangle> X x \<longmapsto> Y x \<brangle>)"
  (* for X :: "'b \<Rightarrow> (heap \<times> 'a::lrep, 'b) \<nu>" *)
  unfolding op_recursion_def Procedure_def Function_def atomize_all
  apply (auto simp add: SemRec_deterministic2)
  subgoal for x a b xa apply (rotate_tac 1) apply (induct rule:  SemRec.induct) by (auto 0 6) done

section \<open>Arithmetic instructions\<close>

\<nu>overloads "+" and round_add and "<" and "\<le>" and "-" and "=" and "not"

subsection \<open>Integer arithmetic\<close>

subsubsection \<open>constant\<close>

definition op_const_int :: "('w::len) itself \<Rightarrow> ('w::len) word \<Rightarrow> ('r::stack) \<longmapsto> 'w word \<times> 'r"
  where "op_const_int _ c = (\<lambda>(heap,r). Success (heap,c,r))"
theorem const_nat_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) c \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> unat c \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_const_int_def by (auto simp add: nu_exps)
(* theorem const_nat_round_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (of_nat n) \<blangle> R \<longmapsto> R \<heavy_comma> n \<tycolon> \<nat>\<^sup>r['w] \<brangle>"
  unfolding \<nu>def op_const_int_def by auto *)

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t ((numeral x) \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (Word.of_nat (numeral x))
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> (numeral x) \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps) (metis mod_if unat_bintrunc unat_numeral)
  \<comment> \<open>Only literal number could be constructed automatically\<close>
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (0 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> 0 \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding AutoConstruct_def using const_nat_\<nu>app by (metis unat_0) 
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (1 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> 1 \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding AutoConstruct_def using const_nat_\<nu>app by (metis unat_1)

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t ((numeral x) \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (Word.of_nat (numeral x))
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (numeral x) \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps)
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (0 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> 0 \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps)
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (1 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> 1 \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps)

(* schematic_goal "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t 3 \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f
  \<blangle>\<flower_L>\<medium_left_bracket> A \<flower_L>\<flower>\<flower_R>X\<medium_right_bracket>\<flower_R>   \<longmapsto> ?T \<brangle>" by (rule \<nu>intro) *)

subsubsection \<open>plus\<close>

(* instantiation typing :: (lrep, plus) plus begin
definition plus_typing :: "('a,'b) typing \<Rightarrow> ('a,'b) typing \<Rightarrow> ('a,'b) typing"
  where "nu_of a = nu_of b \<Longrightarrow> plus_typing a b = (case a of xa \<tycolon> Na \<Rightarrow> case b of xb \<tycolon> Nb \<Rightarrow> xa + xb \<tycolon> Na)"
lemma [simp]: "(x \<tycolon> N) + (y \<tycolon> N) = (x + y \<tycolon> N)" using plus_typing_def by auto
instance by standard
end *)

definition op_add :: "'a itself \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> ('r::lrep) \<longmapsto> ('a::len) word \<times> 'r"
  where "op_add _ = (\<lambda>(h,a,b,r). Success (h,a+b, r))"
declare op_add_def[\<nu>instr]

theorem add_nat_\<nu>app[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b::len) \<longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add TYPE('b) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['b] \<heavy_comma> y \<tycolon> \<nat>['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> x + y \<tycolon> \<nat>['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: of_nat_inverse nu_exps)

theorem add_nat_round[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add TYPE('b) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>\<^sup>r['b::len]\<heavy_comma> y \<tycolon> \<nat>\<^sup>r['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (x + y) \<tycolon> \<nat>\<^sup>r['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: nu_exps)

(* theorem add_nat_mod[\<nu>overload round_add]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle>\<^bold>E\<^bold>N\<^bold>D \<RR> \<heavy_comma> y \<tycolon> \<nat>['b::len] \<heavy_comma> x \<tycolon> \<nat>['b] \<longmapsto> \<^bold>E\<^bold>N\<^bold>D \<RR> \<heavy_comma> ((x + y) mod 2^(LENGTH('b))) \<tycolon> \<nat>['b]  \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: unat_word_ariths)
*)

subsubsection \<open>subtraction\<close>
definition op_sub :: "('a::len) itself \<Rightarrow> 'a word \<times> 'a word \<times> ('r::lrep) \<longmapsto> 'a word \<times> 'r"
  where "op_sub _ = (\<lambda>(h,a,b,r) \<Rightarrow> Success (h,b - a, r))"
declare op_sub_def[\<nu>instr]
theorem sub_nat_\<nu>app[\<nu>overload -]:
    "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x \<longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> x - y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_sub_def by (auto simp add: nu_exps) (meson unat_sub_if_size)
  
subsubsection \<open>less\<close>

definition op_lt :: " ('w::len) itself \<Rightarrow> 'w word \<times> 'w word \<times> ('r::lrep) \<longmapsto> 1 word \<times> 'r"
  where "op_lt _ = (\<lambda>(h,a,b,r).  Success (h, (if  b < a then 1 else 0), r))"
declare op_lt_def[\<nu>instr]
theorem op_lt_\<nu>app[\<nu>overload <]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (x < y) \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_lt_def by (auto simp add: word_less_nat_alt nu_exps)

definition op_le :: " ('w::len) itself \<Rightarrow> 'w word \<times> 'w word \<times> ('r::lrep) \<longmapsto> 1 word \<times> 'r "
  where "op_le _ = (\<lambda>(h,a,b,r).  Success (h, (if  b \<le> a then 1 else 0), r))"
theorem op_le_\<nu>app[\<nu>overload \<le>]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (x \<le> y) \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_le_def by (auto simp add: word_le_nat_alt nu_exps)

subsubsection \<open>bit-wise not\<close>

definition op_not :: "('w::len) itself \<Rightarrow> 'w word \<times> ('r::stack) \<longmapsto> 'w word \<times> 'r"
  where "op_not len = (\<lambda>(h,x,r). Success (h,not x,r))"

lemma boolean_not_\<nu>app[\<nu>overload not]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_not TYPE(1) \<blangle> R\<heavy_comma> x \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> \<not> x \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding Procedure_def op_not_def apply (auto simp add: lrep_exps nu_exps)
  by (metis even_take_bit_eq even_zero iszero_def odd_numeral one_neq_zero)

subsubsection \<open>equal\<close>

definition op_equal :: " ('a::{ceq,lrep}) \<times> 'a \<times> ('r::stack) \<longmapsto> 1 word \<times> 'r"
  where "op_equal = (\<lambda>(h,a,b,r). if ceqable h b a then Success (h,(if ceq b a then 1 else 0), r) else Fail)"
theorem op_equal[\<nu>overload =]:
  "\<nu>Equal N P eq \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P a b \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal \<blangle> R\<heavy_comma> a \<tycolon> N\<heavy_comma> b \<tycolon> N\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> eq a b \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_equal_def by (auto 0 6 simp add: nu_exps)

section \<open>Tuple Operations\<close>

subsection \<open>Tuple construction & destruction\<close>

subsubsection \<open>op_constr_tuple\<close>

definition op_constr_tuple :: "('a::field_list) \<times> ('r::stack) \<longmapsto> 'a tuple \<times> 'r"
  where "op_constr_tuple = (\<lambda>(h,a,r). Success (h, Tuple a, r))"

theorem tup_\<nu>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_constr_tuple \<blangle> R \<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace> \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_constr_tuple_def Procedure_def by (simp add: pair_forall nu_exps)

subsubsection \<open>op_destr_tuple\<close>

definition op_destr_tuple :: "('a::field_list) tuple \<times> ('r::stack) \<longmapsto> 'a \<times> 'r"
  where "op_destr_tuple s = (case s of (h,Tuple a, r) \<Rightarrow> Success (h,a,r))"

theorem det_\<nu>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_destr_tuple \<blangle> R\<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding Procedure_def op_destr_tuple_def by (simp add: tuple_forall pair_forall nu_exps)

subsection \<open>Field Index\<close>

definition FieldIndex :: " ('a,'a,'ax,'ax) index \<Rightarrow> ('ax::lrep,'bx) \<nu> \<Rightarrow> ('a::lrep,'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'bx) \<Rightarrow> (('bx \<Rightarrow> 'bx) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>bool"
  where "FieldIndex adr X A gt mp \<longleftrightarrow> (\<forall>a f. \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<blangle> \<tort_lbrace>gt a \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> \<tort_lbrace>f (gt a) \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>mp f a \<tycolon> A\<tort_rbrace> \<brangle>)"

lemma [final_proc_rewrite2]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e FieldIndex a X A g m \<equiv> FieldIndex a X A g m" unfolding Premise_def .

lemma FieldIndex_here: "FieldIndex index_here X X id id"
  unfolding FieldIndex_def \<nu>index_def index_here_def by auto
lemma FieldIndex_left: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_left f) X (A \<cross_product> R) (gt o fst) (apfst o mp)"
  unfolding FieldIndex_def \<nu>index_def index_left_def by (auto simp add: nu_exps)
lemma FieldIndex_right: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_right f) X (R \<cross_product> A) (gt o snd) (apsnd o mp)"
  unfolding FieldIndex_def \<nu>index_def index_right_def by (auto simp add: nu_exps)

definition index_enter_tup :: "(('a::field_list),('b::field_list),'x,'y) index \<Rightarrow> ('a tuple, 'b tuple, 'x, 'y) index"
  where "index_enter_tup adr = (case adr of Index g m \<Rightarrow> Index (case_tuple g) (map_tuple o m))"
lemma FieldIndex_tupl: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_enter_tup f) X \<lbrace> A \<rbrace> gt mp"
  unfolding FieldIndex_def \<nu>index_def index_enter_tup_def by (auto simp add: tuple_forall nu_exps)

\<nu>processor field_index 110 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn major => Parse.nat >> (fn i => fn _ =>
  let open NuBasics NuHelp
    val arity = Logic.dest_implies (prop_of major) |> #1
        |> dest_Trueprop |> dest_quinop \<^const_name>\<open>FieldIndex\<close> |> #3
        |> dest_monop \<^const_name>\<open>NuTuple\<close> |> strip_binop_r \<^const_name>\<open>Fusion\<close> |> length
    val path1 = funpow (i-1) (fn th => th RS @{thm FieldIndex_right})
        (@{thm FieldIndex_here}
              |> (fn th => if arity = i then th else th RS @{thm FieldIndex_left}))
  in 
    (path1 RS (@{thm FieldIndex_tupl} RS major), ctx)
  end)\<close>


section \<open>Memory & Pointer Operations\<close>

 \<nu>overloads merge and split

subsection \<open>Pointer Arithmetic\<close>

definition op_shift_pointer :: "llty \<Rightarrow> size_t word \<times> memptr \<times> 'r::stack \<longmapsto> memptr \<times> 'r::stack"
  where "op_shift_pointer ty s = (case s of (heap, delta, memptr (seg |+ ofs), r) \<Rightarrow>
    Success (heap, memptr (seg |+ (ofs + delta * of_nat (size_of ty))), r))"

(* theorem op_shift_pointer_raw[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer ty \<blangle> R\<heavy_comma> addr \<tycolon> RawPointer\<heavy_comma> delta \<tycolon> Identity\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto>
      R\<heavy_comma> shift_addr addr (delta * of_nat (size_of ty)) \<tycolon> RawPointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_shift_pointer_def by (cases addr) (simp add: lrep_exps) *)

  
theorem op_shift_pointer[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e address_llty addr = ty \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e offset_of addr + delta \<le> address_len addr \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer ty \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> delta \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto>
      R\<heavy_comma> addr ||+ delta \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_shift_pointer_def by (cases addr) (auto simp add: lrep_exps same_addr_offset_def nu_exps)


theorem op_shift_pointer_slice[ unfolded Separation_assoc, \<nu>overload split ]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < length xs \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer LLTY('p) \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p addr \<R_arr_tail> xs \<tycolon> Array T
      \<longmapsto> R\<heavy_comma> addr ||+ n \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (addr \<R_arr_tail> take n xs \<tycolon> Array T \<heavy_asterisk> shift_addr addr n \<R_arr_tail> drop n xs \<tycolon> Array T) \<brangle>"
  for T :: "('p::field, 'x) \<nu>"
  unfolding \<nu>def op_shift_pointer_def Array_def Heap_Divider_def apply (cases addr)
  apply (auto simp add: lrep_exps same_addr_offset_def raw_offset_of_def distrib_right nu_exps
        add.commute add.left_commute intro: heap_split_id)
  subgoal for x1 x2 aa b H h1 h2
    by (rule heap_split_id, simp, rule heap_split_by_addr_set[of _ _ "{(x1 |+ x2 + i) | i. i < n}"]) (auto simp add: nu_exps)
  done

(*
theorem op_slice_merge[\<nu>overload merge]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e shift_addr addr1 (length xs1) = addr2 \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> \<^bold>E\<^bold>N\<^bold>D R\<heavy_comma> addr1 \<R_arr_tail> xs1 \<tycolon> Slice T\<heavy_comma> addr2 \<R_arr_tail> xs2 \<tycolon> Slice T
      \<longmapsto> \<^bold>E\<^bold>N\<^bold>D R\<heavy_comma> addr1 \<R_arr_tail> xs1 @ xs2 \<tycolon> Slice T \<brangle>"
  unfolding \<nu>def op_drop_def apply (cases addr1; cases addr2)
  apply (auto 0 0 simp add: lrep_exps nth_append)
  by (metis add.assoc add_diff_inverse_nat diff_add_inverse diff_less_mono not_le
*)
subsection \<open>Allocation\<close>

definition "heap_assignN n v seg heap = (\<lambda>key. case key of MemAddress (seg' |+ ofs') \<Rightarrow>
      if seg' = seg \<and> ofs' < n then v else
      if seg' = seg \<and> ofs' = n then Some DM_none else heap key | _ \<Rightarrow> heap key)"

lemma malloc_split: "Heap h \<Longrightarrow> P h (heap_assignN n v (malloc h) Map.empty) \<Longrightarrow>
    \<exists>h1 h2. heap_assignN n v (malloc h) h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  apply (rule exI[of _ h], rule exI[of _ "heap_assignN n v (malloc h) Map.empty"], simp)
  subgoal premises prems
    unfolding heap_assignN_def using prems(1)
    by (simp add: map_add_def fun_eq_iff resource_key_forall disjoint_rewL memaddr_forall dom_def
          malloc option.case_eq_if) done

(* lemma heap_assignN_subset: "Heap h \<Longrightarrow> h \<subseteq>\<^sub>m heap_assignN n v (malloc h) h"
  unfolding heap_assignN_def map_le_def Ball_def by (simp add: malloc2 resource_key_forall memaddr_forall) *)

lemma [intro]: "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" proof -
  have "AvailableSegments h \<subseteq> {seg} \<union> AvailableSegments (heap_assignN n v seg h)"
    unfolding AvailableSegments_def heap_assignN_def by auto 
  then show "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" 
    unfolding Heap_def using infinite_super by auto
qed

lemma heap_assignN_eval: "v \<in> T \<Longrightarrow> i < n \<Longrightarrow> heap_assignN n (Some (deepize v)) seg h \<^bold>a\<^bold>t (seg |+ i) \<^bold>i\<^bold>s T"
  unfolding MemAddrState_def addr_allocated_def heap_assignN_def by auto


definition op_alloc :: "('x::{zero,field}) itself \<Rightarrow> size_t word \<times> ('r::stack) \<longmapsto> memptr \<times>'r"
  where "op_alloc _ s = (case s of (heap,n,r) \<Rightarrow>  let seg = malloc heap in
  if segment_len seg = unat n \<and> segment_llty seg = LLTY('x) then
    Success (heap_assignN (unat n) (Some (deepize (0 :: 'x))) seg heap, memptr (seg |+ 0), r)
  else PartialCorrect)"





      
theorem alloc_array_\<nu>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N \<Longrightarrow> \<nu>Zero N zero \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc TYPE('x)
      \<blangle> R\<heavy_comma> n \<tycolon> \<nat>[size_t] \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing
        \<longmapsto> (\<exists>*seg. (R\<heavy_comma> (seg |+ 0) \<tycolon> Pointer \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (seg |+ 0) \<R_arr_tail> replicate n zero \<tycolon> Array N)) \<brangle>"
  for N :: "('x::{zero,field},'b)\<nu>"
  unfolding \<nu>def op_alloc_def Array_def Heap_Divider_def
  apply (auto simp add: lrep_exps list_all2_conv_all_nth Let_def same_addr_offset_def nu_exps)
  apply (rule malloc_split, simp add: heap_assignN_eval)
  apply (auto simp add: heap_assignN_eval nu_exps) done


proc alloc : \<open>R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing\<close> \<longmapsto> \<open>\<exists>*ptr. (R\<heavy_comma> ptr \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> zero \<tycolon> Ref T)\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m T" and [\<nu>intro]: "\<nu>Zero T zero"
  have A[simp]: "replicate 1 zero = [zero]" by (simp add: One_nat_def)
  \<bullet>\<open>1 \<tycolon> \<nat>[size_t]\<close> alloc_array T
  finish

subsection \<open>Load & Store\<close>

\<nu>overloads \<up> and "\<up>:" and \<Up> and "\<Up>:" and \<down> and "\<down>:" and \<Down> and "\<Down>:"

abbreviation "list_map_at f i l \<equiv> list_update l i (f (l ! i))"

subsubsection \<open>load\<close>

definition op_load :: " llty \<Rightarrow> ('a::lrep,'a,'ax,'ax) index \<Rightarrow> memptr \<times> ('r::stack) \<longmapsto> 'ax::field \<times>'r "
  where "op_load lty idx s = (case s of (heap, memptr adr, r) \<Rightarrow>
    (case heap (MemAddress (logical_addr_of adr)) of Some data \<Rightarrow>
      if lty = LLTY('a) then Success (heap, get_idx idx (shallowize data), r) else Fail
    | _ \<Rightarrow> Fail))"

theorem op_load[ \<nu>overload "\<up>:" ]:
  "FieldIndex field_index Y X gt mp \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load LLTY('x) field_index \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> addr \<R_arr_tail> x \<tycolon> Ref X \<longmapsto> R\<heavy_comma> gt x \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> addr \<R_arr_tail> x \<tycolon> Ref X\<brangle> "
  for X :: "('x::field, 'c) \<nu>"
  unfolding op_load_def Procedure_def FieldIndex_def \<nu>index_def Heap_Divider_def
  by (cases field_index, cases addr)  (auto simp add: lrep_exps MemAddrState_def nu_exps split: option.split iff: addr_allocated_def)

lemmas [ \<nu>overload "\<up>" ] = op_load[THEN mp, OF FieldIndex_here, simplified]

proc i_load_n[\<nu>overload "\<up>:"]:
  \<open>a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs \<tycolon> Array X\<close> \<longmapsto> \<open>gt (xs ! i) \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<nu>"
  requires [used]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs" and idx: "FieldIndex field_index Y X gt mp"
  \<bullet> +\<up>: idx
  finish

lemmas [ \<nu>overload "\<up>" ] = i_load_n_\<nu>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]


subsubsection \<open>store\<close>

definition op_store :: " llty \<Rightarrow> ('a::lrep,'a,'ax,'ax) index \<Rightarrow> 'ax::field \<times> memptr \<times> ('r::stack) \<longmapsto> memptr \<times> 'r "
  where "op_store lty idx s = (case s of (heap, x, memptr addr, r) \<Rightarrow>
    (let key = MemAddress (logical_addr_of addr) in
    case heap key of Some data \<Rightarrow>
      if lty = LLTY('a) then Success (heap(key \<mapsto> map_deepmodel (map_idx idx (\<lambda>_. x)) data), memptr addr, r) else Fail
    | _ \<Rightarrow> Fail))"

theorem op_store[ \<nu>overload "\<down>:" ]:
  "FieldIndex field_index Y X gt mp \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store LLTY('x) field_index
    \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> y \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p addr \<R_arr_tail> x \<tycolon> Ref X \<longmapsto> R \<heavy_comma> addr \<tycolon> Pointer \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p addr \<R_arr_tail> mp (\<lambda>_. y) x \<tycolon> Ref X\<brangle> "
  for X :: "('x::field, 'c) \<nu>"
  unfolding op_store_def Procedure_def FieldIndex_def \<nu>index_def Heap_Divider_def Stack_Delimiter_def
  apply (cases field_index, cases addr)
  apply (auto simp add: lrep_exps Let_def nu_exps split: option.split iff: addr_allocated_def)
  subgoal premises prems for x1 x2 x1a x2a aa ofs b x2b H h1 h2 proof -
    have t1: "\<And>v. (h1 ++ h2)(MemAddress (x1a |+ x2a) \<mapsto> v) = h1 ++ (h2(MemAddress (x1a |+ x2a) \<mapsto> v))"
      using prems disjoint_rewR by simp
    have t2: "\<And>v.  dom (h2(MemAddress (x1a |+ x2a) \<mapsto> v)) = dom h2"
      using prems by auto
    show ?thesis apply (unfold t1, rule heap_split_id, unfold t2, simp add: prems)
      using prems by (auto simp add: nu_exps MemAddrState_def)
  qed done

lemmas [ \<nu>overload "\<down>" ] = op_store[THEN mp, OF FieldIndex_here, simplified]

proc i_store_n[\<nu>overload "\<down>:"]:
  \<open>R\<heavy_comma> a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> y \<tycolon> Y \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p a \<R_arr_tail> xs \<tycolon> Array X\<close> \<longmapsto> \<open>R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p a \<R_arr_tail> xs[i := mp (\<lambda>_. y) (xs ! i)] \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<nu>"
  requires [used]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs" and idx: "FieldIndex field_index Y X gt mp"
  \<bullet> \<rightarrow> y
  \<bullet> + y
  \<bullet> \<down>: idx drop
  finish

lemmas [ \<nu>overload "\<down>" ] = i_store_n_\<nu>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]


fun fib where
  "fib 0 = 1" | "fib (Suc 0) = 1" | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

(* int fib (int i) { if (i \<le> 1) return 1; else return fib (i-2) + fib (i-1); } *)
rec_proc Fib: \<open>i \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>fib i \<tycolon> \<nat>\<^sup>r[32]\<close> var i
  \<bullet> -- i 1 \<le> if \<medium_left_bracket> \<open>1\<tycolon> \<nat>\<^sup>r[32]\<close> \<medium_right_bracket> \<medium_left_bracket> i 2 - Fib i 1 - Fib + \<medium_right_bracket>
  \<bullet> cast ie \<open>fib i\<close> affirm by (cases i rule: fib.cases) auto
  finish


end
