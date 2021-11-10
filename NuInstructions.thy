theory NuInstructions
  imports NuSys NuBasicAbstractors
  keywords
     "\<up>:" "\<Up>:" "\<down>:" "\<Down>:" "subj" "of" "while" "until" "always" "var" "heap" :: quasi_command
  abbrevs "|^" = "\<up>"
    and "||^" = "\<Up>"
    and "|v" = "\<down>"
    and "||v" = "\<Down>"
    and "<up>" = "\<up>"
    and "<down>" = "\<down>"
    and "<Up>" = "\<Up>"
    and "<Down>" = "\<Down>"
begin

declare Nat.One_nat_def[simp del]

text \<open>Basic instructions\<close>

section \<open>Structural instructions\<close>

subsection \<open>Basic sequential instructions\<close>

subsubsection \<open>crash\<close>

definition op_crash :: "('x::stack) \<longmapsto> ('y::stack)" where "op_crash _ = PartialCorrect"
lemma crash_\<nu>proc[no_atp]:  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_crash \<blangle> x \<tycolon> X \<longmapsto> y \<tycolon> Y \<brangle>" unfolding \<nu>def op_crash_def by auto


subsubsection \<open>drop\<close>

definition op_drop :: "('a::lrep) \<times> ('r::stack) \<longmapsto> 'r" where
  "op_drop x = (case x of (h,a,r) \<Rightarrow> Success (h,r))"
declare op_drop_def[\<nu>instr]
theorem drop_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> R\<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>" unfolding \<nu>def op_drop_def by auto

subsubsection \<open>duplication\<close>

definition op_dup :: "('a::lrep) \<times> ('r::stack) \<longmapsto> ('a \<times> 'a \<times> 'r)"
  where "op_dup x = (case x of (h,a,r) \<Rightarrow> Success (h, a, a, r))"
declare op_dup_def[\<nu>instr]
theorem dup_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dup \<blangle> R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> x \<tycolon> X \<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<brangle>"
  unfolding \<nu>def op_dup_def by auto


subsubsection \<open>pair & de-pair\<close>

definition op_pair :: "('a::lrep) \<times> ('b::lrep) \<times> ('r::stack) \<longmapsto> (('b \<times> 'a) \<times> 'r)"
  where "op_pair = (\<lambda>(h,a,b,r). Success (h,(b,a),r))"
definition op_depair :: "(('b::lrep) \<times> ('a::lrep)) \<times> ('r::stack) \<longmapsto> ('a \<times> 'b \<times> 'r)"
  where "op_depair = (\<lambda>(h,(b,a),r). Success (h,a,b,r))"
(* declare op_pair_def[\<nu>instr] op_depair_def[\<nu>instr] *)

theorem pr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B)\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def  op_pair_def by auto
theorem dpr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B)\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def  op_depair_def by auto


(* \<nu>processor pair_auto_dest 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<flower> W)\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema} |> NuSys.accept_proc ctx)\<close>
\<nu>processor pair_auto_dest' 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B))\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema'} |> NuSys.accept_proc ctx)\<close> *)

subsubsection \<open>let & local_value\<close>

definition op_let :: " ('v::lrep \<Rightarrow> 's::stack \<longmapsto> 't::stack) \<Rightarrow> ('v \<times> 's \<longmapsto> 't)"
  where "op_let body = (\<lambda>(h,v,s). body v (h,s))"
lemma op_let: " (\<And>p. p \<nuLinkL> T \<nuLinkR> x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body p \<blangle> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> SH' \<brangle>) \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_let body \<blangle> S\<heavy_comma> x \<tycolon> T\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> SH' \<brangle>"
  unfolding Procedure_def op_let_def by auto

definition op_local_value :: " 'v::lrep \<Rightarrow> 's::stack \<longmapsto> 'v \<times> 's "
  where "op_local_value v = (\<lambda>(h,s). Success (h,v,s))"
lemma op_local_value: "v \<nuLinkL> T \<nuLinkR> x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_local_value v \<blangle> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> S\<heavy_comma> x \<tycolon> T\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding Procedure_def op_local_value_def by auto

ML_file "library/local_value.ML"

\<nu>processor let_local_value 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H)\<close> \<open>let open Parse in
  fn _ => fn meta => ($$$ "\<rightarrow>" |-- list1 binding) >> (fn idts => fn _ =>
    raise Process_State_Call'' meta (Local_Value.mk_let (rev idts)))
end\<close>

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

subsubsection \<open>op_if\<close>

definition op_if :: " ('s::stack \<longmapsto> 't::stack) \<Rightarrow> ('s \<longmapsto> 't) \<Rightarrow> (1 word \<times> 's) \<longmapsto> 't"
  where "op_if brT brF s = (case s of (heap,c,r) \<Rightarrow> if c = 1 then brT (heap,r) else brF (heap,r))"
declare op_if_def[\<nu>instr]
theorem if_\<nu>proc: "(c \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_true \<blangle> U\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> Vt \<brangle>) \<longrightarrow> (\<not> c \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_false \<blangle> U\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> Vf \<brangle>)
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if branch_true branch_false \<blangle> U\<heavy_comma> c \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> (if c then Vt else Vf) \<brangle>"
  unfolding \<nu>def op_if_def by auto

lemma [simp]: "(if P then \<tort_lbrace>x \<tycolon> X\<tort_rbrace> else \<tort_lbrace>y \<tycolon> Y\<tort_rbrace>) = \<tort_lbrace>(if P then x else y) \<tycolon> (if P then X else Y)\<tort_rbrace>" by simp
lemma [simp]: "(if P then (a,b) else (a',b')) = ((if P then a else a'), (if P then b else b'))" by simp
lemma [simp]: "(if P then (A <stack-div> B) else (A' <stack-div> B')) = ((if P then A else A') <stack-div> (if P then B else B'))" by simp
lemma [simp]: "(if P then (A <heap-sep> B) else (A' <heap-sep> B')) = ((if P then A else A') <heap-sep> (if P then B else B'))" by simp
(* lemma [simp]: "(if P then (A \<^bold>a\<^bold>n\<^bold>d B) else (A' \<^bold>a\<^bold>n\<^bold>d B')) = ((if P then A else A') \<^bold>a\<^bold>n\<^bold>d (if P then B else B'))"  by auto *)
lemma [simp]: "(if P then Named name T else Named name' T') = Named name (if P then T else T')" unfolding Named_def by simp
lemma [simp]: "(if P then a \<R_arr_tail> x else a \<R_arr_tail> x') = a \<R_arr_tail> (if P then x else x')" by auto

subsubsection \<open>Stack Head\<close> \<comment> \<open>A technically auxiliary \<nu>-abstractor\<close>

definition Nu_Front_Stack :: "('a::lrep,'ax) \<nu> \<Rightarrow> (heap \<times> 'stack,'hsx) \<nu> \<Rightarrow> (heap \<times> 'a \<times> 'stack, 'ax \<times> 'hsx) \<nu>"
  where "Nu_Front_Stack A Ctx = (\<lambda>(ax,hsx). {(h,a,s). (a \<nuLinkL> A \<nuLinkR> ax) \<and> ((h,s) \<nuLinkL> Ctx \<nuLinkR> (hsx))} )"

consts "Front_Stack_sugar" :: " 'just \<Rightarrow> 'a \<Rightarrow> 'sugar " ( "_/ \<heavy_comma>^ _" [13,14] 13) \<comment> \<open>Note it is left associative\<close>
translations " c \<tycolon> Ctx \<heavy_comma>^ a \<tycolon> A " == " (CONST Pair a c) \<tycolon> (CONST Nu_Front_Stack A Ctx) "
  " Ctx \<heavy_comma>^ A " => " (CONST Pair (_\<nu>typing_x A) (_\<nu>typing_x Ctx)) \<tycolon> (CONST Nu_Front_Stack (_\<nu>typing_ty A) (_\<nu>typing_ty Ctx)) "

text \<open>Normally the stack elements are written `before` the heap elements, \<^term>\<open>s1 \<tycolon> S1\<heavy_comma> s2 \<tycolon> S2\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H\<close>.
  The \<^term>\<open>Nu_Front_Stack\<close> allows one writes the stack elements `after` the heap, as \<^term>\<open>s1 \<tycolon> S1\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<heavy_comma>^ s2 \<tycolon> S2\<close>.
  Both of the two \<nu>-types specify the same low concretes.
  It is useful when one needs to specify over the whole remaining stack and heap, e.g., theorem `Until` (see later)
    which requires body to return \<^term>\<open>x \<tycolon> X \<heavy_comma>^ loop_condition \<tycolon> \<bool>\<close> where the \<^term>\<open>x \<tycolon> X\<close> instantiated by caller
    specifies all the heap and remaining stack except the leading loop_condition.\<close>

lemma [simp]: "(h,a,s) \<nuLinkL> Nu_Front_Stack A Ctx \<nuLinkR> (ax,hsx) \<longleftrightarrow> (a \<nuLinkL> A \<nuLinkR> ax) \<and> ((h,s) \<nuLinkL> Ctx \<nuLinkR> hsx)"
  unfolding Nu_Front_Stack_def Refining_def by simp
lemma [simp]: "\<tort_lbrace> (a,h,s) \<tycolon> Nu_Front_Stack A (NuTopCtx H S) \<tort_rbrace> = \<tort_lbrace> (h,a,s) \<tycolon> NuTopCtx H (A <stack-div> S) \<tort_rbrace>" by auto
lemma [simp]: "\<tort_lbrace>c \<tycolon> Ctx \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<heavy_comma>^ x \<tycolon> T\<tort_rbrace> = \<tort_lbrace> (c \<tycolon> Ctx \<heavy_comma>^ x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<tort_rbrace>" unfolding Auto_def by auto

lemma Nu_Front_Stack_cong: "\<tort_lbrace>c \<tycolon> Ctx\<tort_rbrace> \<equiv> \<tort_lbrace>c' \<tycolon> Ctx'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>c \<tycolon> Ctx \<heavy_comma>^ x \<tycolon> T\<tort_rbrace> \<equiv> \<tort_lbrace>c' \<tycolon> Ctx' \<heavy_comma>^ x \<tycolon> T\<tort_rbrace>"
  unfolding atomize_eq by auto
simproc_setup Nu_Front_Stack_cong ("\<tort_lbrace>c \<tycolon> Ctx \<heavy_comma>^ x \<tycolon> T\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm Nu_Front_Stack_cong})\<close>

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> c \<tycolon> Ctx \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> c \<tycolon> Ctx \<heavy_comma>^ (x \<tycolon> X) \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Intro_def Cast_def by simp
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t c \<tycolon> Ctx \<longmapsto> (R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q
    \<Longrightarrow> \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t c \<tycolon> Ctx \<heavy_comma>^ (x \<tycolon> X) \<longmapsto> (R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Dest_def Cast_def by simp blast


subsubsection \<open>until\<close>

inductive SemUnt :: "('r \<longmapsto> 1 word \<times> 'r) \<Rightarrow> heap \<times> 'r \<Rightarrow> 'r state \<Rightarrow> bool" where
  "f s = Success (h,0,r) \<Longrightarrow> SemUnt f s (Success (h,r))"
| "f s = PartialCorrect \<Longrightarrow> SemUnt f s PartialCorrect"
| "f s = Success (h,1,r) \<Longrightarrow> SemUnt f (h,r) s'' \<Longrightarrow> SemUnt f s s''"

lemma SemUnt_deterministic:
  assumes "SemUnt c s s1"
      and "SemUnt c s s2"
    shows "s1 = s2"
proof -
  have "SemUnt c s s1 \<Longrightarrow> (\<forall>s2. SemUnt c s s2 \<longrightarrow> s1 = s2)"
    by (induct rule: SemUnt.induct) (subst SemUnt.simps, simp)+
  thus ?thesis
    using assms by simp
qed

lemma SemUnt_deterministic2: " SemUnt body s x \<Longrightarrow> The ( SemUnt body s) = x"
  using SemUnt_deterministic by blast 

definition Until :: "('r \<longmapsto> 1 word \<times> 'r) \<Rightarrow> 'r \<longmapsto> 'r" where
  "Until f s = (if (\<exists>y. SemUnt f s y) then The (SemUnt f s) else PartialCorrect)"


lemma "__Until___\<nu>proc": "(\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<blangle> x \<tycolon> X \<longmapsto> \<exists>* x'. x' \<tycolon> X \<heavy_comma>^ c x' \<tycolon> \<bool> \<brangle>)
  \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Until body \<blangle> x \<tycolon> X \<longmapsto> \<exists>*x'. x' \<tycolon> X \<and>\<^sup>\<nu>' (\<not> c x') \<brangle>"
  for X :: "(heap \<times> 'a::lrep, 'b) \<nu>"
  unfolding Until_def Procedure_def Auto_def
  apply (auto simp add: SemUnt_deterministic2)
  subgoal for a b xa
    apply (rotate_tac 1)
    by (induct  body "(a, b)" xa arbitrary: a b x rule: SemUnt.induct) (auto 0 7)
  done

definition "decorated_All \<equiv> All"
definition "decorated_ExNu \<equiv> ExNu"

ML_file \<open>library/loop.ML\<close>

\<nu>processor until 110 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> T)\<close> \<open>fn ctx => fn meta => 
let open Parse Scan NuHelp NuBasics in
  $$$ "until" |-- vars -- option ($$$ "in" |-- list1 term)
     -- option ($$$ "heap" |-- list1 term) -- ($$$ "subj" |-- term) -- Scan.option ($$$ "always" |-- term)
    >> (fn ((((vars, stack_schema), heap_schema), subj), always) => fn _ =>
      NuLoop.mk_loop_proc @{thm "__Until___\<nu>proc"} vars stack_schema heap_schema subj always ctx meta)
end\<close>

subsubsection \<open>while\<close>


proc "while": \<open>x \<tycolon> X\<close> \<longmapsto> \<open>x \<tycolon> X\<close>
  requires Cond_\<nu>proc: "\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<blangle> x \<tycolon> X \<longmapsto> \<exists>* x'. x' \<tycolon> X \<heavy_comma>^ c x \<tycolon> \<bool> \<brangle>"
    and Body_\<nu>proc: "\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<blangle> x \<tycolon> X \<longmapsto> \<exists>* x'. x' \<tycolon> X' \<brangle>"
  \<bullet> "__Until__" \<medium_left_bracket> \<bullet> Cond 

(*
  term \<open>(\<lambda>c. c) \<tycolon> Named (NAME xx) (ExNu (\<lambda>c. T))\<close>

proc' i_while: \<open>(R \<heavy_comma> x \<tycolon> X) \<flower> W\<close> \<longmapsto> \<open>(R \<heavy_comma> - P \<tycolon> <some'> (X <schema> sch <where''> Always)) \<flower> W\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m sch" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m Always" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P"
    and [simplified StructuralTag_def, intro]: "<Structural> sch y = x" and [intro]: "y \<in> Always"
    and brC: \<open>(\<And>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> (R \<heavy_comma> x1 \<tycolon> X <schema> sch <where''> Always) \<flower> W \<longmapsto> (R \<heavy_comma> { (y \<in> P, y) |y. True } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (\<bool> \<nuFusion> X <schema> sch <where''> Always)) \<flower> W \<brangle>)\<close>
    and brB: \<open>(\<And>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> (R \<heavy_comma> x2 \<tycolon> (X <schema> sch <where''> Always <where'> P)) \<flower> W \<longmapsto> (R \<heavy_comma> UNIV \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (X <schema> sch <where''> Always)) \<flower> W \<brangle>)\<close>
  \<bullet> cast i_schema sch cast refine' Always  i_while_raw P \<Longleftarrow> brC \<Longleftarrow> brB[simplified SchemaCondition_simp] finish




(* lemma Until': "(\<forall>s h s' h'. \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<blangle> s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<longmapsto> s' \<tycolon> S\<heavy_comma> c h' s' \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h' \<tycolon> H \<brangle>)
  \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Until body \<blangle> s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<longmapsto> (s' \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h' \<tycolon> H) \<and> \<not> c h' s'\<brangle>"
  unfolding Until_def Procedure_def apply (auto simp add: SemUnt_deterministic2)
  subgoal for a b x apply (rotate_tac 1)
    apply (induct  body "(a, b)" x arbitrary: a b rule: SemUnt.induct)
    apply (auto 4 7)
    subgoal premises prems for f ha r s'' a b proof -
note prems
      show ?thesis apply (rule prems(3)) using prems by (auto 4 7)
    qed
    done done *)
*)

  subsubsection \<open>recursion\<close>


inductive SemRec :: "(('r \<longmapsto> 'r) \<Rightarrow> ('r \<longmapsto> 'r)) \<Rightarrow> heap \<times> 'r \<Rightarrow> 'r state \<Rightarrow> bool" where
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

definition op_recursion :: "(('r \<longmapsto> 'r) \<Rightarrow> ('r \<longmapsto> 'r)) \<Rightarrow> 'r \<longmapsto> 'r"
  where "op_recursion F s = (if (\<exists>t. SemRec F s t) then The (SemRec F s) else PartialCorrect)"

lemma op_recursion:
    "(\<forall>x' g. (\<forall>x''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> x'' \<tycolon> X \<longmapsto> f x'' \<tycolon> Y \<brangle>) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g \<blangle> x' \<tycolon> X \<longmapsto> f x' \<tycolon> Y \<brangle>) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion F \<blangle> x \<tycolon> X \<longmapsto> f x \<tycolon> Y \<brangle>"
  unfolding op_recursion_def Procedure_def
  apply (auto simp add: SemRec_deterministic2)
  subgoal for a b xa apply (rotate_tac 1) apply (induct rule:  SemRec.induct) by (auto 0 6) done


subsubsection \<open>while\<close>
(*
consts op_while_WF :: "'c itself \<Rightarrow> ('x::lrep \<times> 'r::stack \<longmapsto> ('x \<times> 1 word) \<times> 'r) \<Rightarrow> ('x \<times> 'r \<longmapsto> 'x \<times> 'r) \<Rightarrow> 'x \<times> 'r \<longmapsto> 'x \<times> 'r"
specification ("op_while_WF")
  while_WF_\<nu>proc: "
  \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m Rc \<longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m Rb \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e wf (Rc O Rb)
  \<longrightarrow> (\<forall>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> R \<heavy_comma> (x1::'c) \<tycolon> X \<longmapsto> R \<heavy_comma> {(y, y \<in> P) | y. (y,x1) \<in> Rc } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (X \<nuFusion> \<bool>) \<brangle>)
  \<longrightarrow> (\<forall>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> R \<heavy_comma> x2 \<tycolon> (X \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P) \<longmapsto> R \<heavy_comma> {y. (y,x2) \<in> Rb} \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X \<brangle>)
  \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_while_WF TYPE('c) brC brB \<blangle> R \<heavy_comma> x \<tycolon> X \<longmapsto> R \<heavy_comma> - P \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X \<brangle>"
  apply (rule exI) using op_crash by auto

consts op_while :: "'c itself \<Rightarrow> ('x::lrep \<times> 'r::stack \<longmapsto> (1 word \<times> 'x) \<times> 'r) \<Rightarrow> ('x \<times> 'r \<longmapsto> 'x \<times> 'r) \<Rightarrow> ('x \<times> 'r \<longmapsto> 'x \<times> 'r)"
specification ("op_while")
  i_while_raw_\<nu>proc: "
  \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<longrightarrow> (\<forall>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> R \<heavy_comma> (x1::'c) \<tycolon> X \<longmapsto> R \<heavy_comma> {(y \<in> P, y) |y. True } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (\<bool> \<nuFusion> X)\<brangle>)
  \<longrightarrow> (\<forall>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> R \<heavy_comma> x2 \<tycolon> (X \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P) \<longmapsto> R \<heavy_comma> UNIV \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X \<brangle>)
  \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_while TYPE('c) brC brB \<blangle> R \<heavy_comma> x \<tycolon> X \<longmapsto> R \<heavy_comma> - P \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X\<brangle>"
  apply (rule exI) using op_crash by auto


subsubsection \<open>recursion\<close>

consts op_recursion_WF :: " 'a itself \<times> 'b itself \<Rightarrow>
    (('u::lrep \<times> void \<longmapsto> ('v::lrep) \<times> void) \<longmapsto> ('u \<times> void \<longmapsto> 'v \<times> void)) \<Rightarrow> ('u \<times> 'r::stack \<longmapsto> 'v \<times> 'r) "
specification ("op_recursion_WF")
  recursion_WF_\<nu>proc:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m h \<longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m M \<longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m WF \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e wf WF \<longrightarrow>
  (\<forall>x' g. (\<forall>x''. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (x'',x') \<in> WF \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> \<^bold>E\<^bold>N\<^bold>D \<heavy_comma> x'' \<tycolon> N \<longmapsto> \<^bold>E\<^bold>N\<^bold>D \<heavy_comma> h x'' \<tycolon> M \<brangle>)
      \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f g \<blangle> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma>  x' \<tycolon> N \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> h x' \<tycolon> M \<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion_WF (TYPE('a), TYPE('d)) f \<blangle> R\<heavy_comma> (x::'a) \<tycolon> N \<longmapsto> R\<heavy_comma> (h x::'d) \<tycolon> M \<brangle>"
  apply (rule exI) using op_crash by auto

consts op_recursion :: " 'a itself \<times> 'b itself \<Rightarrow>
    ((('u::lrep) \<times> void \<Rightarrow> (('v::lrep) \<times> void) state) \<Rightarrow> ('u \<times> void \<Rightarrow> ('v \<times> void) state)) \<Rightarrow> ('u \<times> ('r::stack) \<Rightarrow> ('v \<times> 'r) state) "
specification ("op_recursion")
  recursion_\<nu>proc[simplified PremiseHOL ParamHOL]:
  "ParamHOL h \<Longrightarrow> ParamHOL M\<Longrightarrow>
  (\<And>x' g. (\<And>x''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> x'' \<tycolon> N \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> h x'' \<tycolon> M \<brangle>)
      \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f g \<blangle> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma>  x' \<tycolon> N \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> h x' \<tycolon> M \<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion (TYPE('a), TYPE('d)) f \<blangle> R\<heavy_comma> (x::'a) \<tycolon> N \<longmapsto> R\<heavy_comma> (h x::'d) \<tycolon> M \<brangle>"
  apply (rule exI) using op_crash by auto

proc' i_recursion: \<open>R\<heavy_comma> x \<tycolon> N\<close> \<longmapsto> \<open>R\<heavy_comma> h y \<tycolon> M\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m M" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m sch" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m h"
    and [simplified StructuralTag_def, intro]: "<Structural> sch y = x"
    and [simplified StructuralTag_def, intro]: "<Structural> y \<in> P"
    and g[simplified SchemaCondition_def]:
      \<open>(\<And>x' g. (\<And>x''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> \<^bold>E\<^bold>N\<^bold>D \<heavy_comma> x'' \<tycolon>  N <schema> sch <where> P \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> h x'' \<tycolon> M \<brangle>)
        \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f g \<blangle> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma>  x' \<tycolon> N <schema> sch <where'> P \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> h x' \<tycolon> M \<brangle>)\<close>
  \<bullet> cast i_schema sch cast refine P recursion h M \<Longleftarrow>' g[intro_forall ?x' ?g] 
  finish 

proc' i'_while: \<open>(R \<heavy_comma> x \<tycolon> X) \<flower> W\<close> \<longmapsto> \<open>(R \<heavy_comma> - P \<tycolon> <some'> (X <schema> sch)) \<flower> W\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m sch" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P" and [THEN someI_ex, intro]: "\<exists>y. sch y = x" 
    and brC: \<open>(\<And>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> (R \<heavy_comma> x1 \<tycolon> X <schema> sch) \<flower> W \<longmapsto> (R \<heavy_comma> { (y \<in> P, y) |y. True } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (\<bool> \<nuFusion> X <schema> sch)) \<flower> W \<brangle>)\<close>
    and brB: \<open>(\<And>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> (R \<heavy_comma> x2 \<tycolon> (X <schema> sch <where'> P)) \<flower> W \<longmapsto> (R \<heavy_comma> UNIV \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (X <schema> sch)) \<flower> W \<brangle>)\<close>
  \<bullet> cast i_schema sch  i_while_raw P \<Longleftarrow> brC \<Longleftarrow> brB[simplified SchemaCondition_simp] finish

*)

section \<open>Arithmetic instructions\<close>

\<nu>overloads "+" and round_add and "<" and "\<le>" and "-" and "="

subsection \<open>Integer arithmetic\<close>

subsubsection \<open>constant\<close>

definition op_const_int :: "('w::len) itself \<Rightarrow> ('w::len) word \<Rightarrow> ('r::stack) \<longmapsto> 'w word \<times> 'r"
  where "op_const_int _ c = (\<lambda>(heap,r). Success (heap,c,r))"
theorem const_nat_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) c \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> unat c \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_const_int_def by auto
(* theorem const_nat_round_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (of_nat n) \<blangle> R \<longmapsto> R \<heavy_comma> n \<tycolon> \<nat>\<^sup>r['w] \<brangle>"
  unfolding \<nu>def op_const_int_def by auto *)

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t ((numeral x) \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (Word.of_nat (numeral x)) \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> (numeral x) \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 apply auto by (metis mod_if unat_bintrunc unat_numeral)
  \<comment> \<open>Only literal number could be constructed automatically\<close>
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (0 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> 0 \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding AutoConstruct_def using const_nat_\<nu>proc by (metis unat_0) 
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (1 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> 1 \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding AutoConstruct_def using const_nat_\<nu>proc by (metis unat_1)

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t ((numeral x) \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (Word.of_nat (numeral x)) \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> (numeral x) \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by auto
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (0 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> 0 \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by auto
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (1 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> 1 \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by auto

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

theorem add_nat_\<nu>proc[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b::len) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add TYPE('b) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['b] \<heavy_comma> y \<tycolon> \<nat>['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> x + y \<tycolon> \<nat>['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: of_nat_inverse) 

theorem add_nat_round[\<nu>overload +]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add TYPE('b) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>\<^sup>r['b::len]\<heavy_comma> y \<tycolon> \<nat>\<^sup>r['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> (x + y) \<tycolon> \<nat>\<^sup>r['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_add_def Procedure_def by auto

(* theorem add_nat_mod[\<nu>overload round_add]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle>\<^bold>E\<^bold>N\<^bold>D \<RR> \<heavy_comma> y \<tycolon> \<nat>['b::len] \<heavy_comma> x \<tycolon> \<nat>['b] \<longmapsto> \<^bold>E\<^bold>N\<^bold>D \<RR> \<heavy_comma> ((x + y) mod 2^(LENGTH('b))) \<tycolon> \<nat>['b]  \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: unat_word_ariths)
*)

subsubsection \<open>subtraction\<close>
definition op_sub :: "('a::len) itself \<Rightarrow> 'a word \<times> 'a word \<times> ('r::lrep) \<longmapsto> 'a word \<times> 'r"
  where "op_sub _ = (\<lambda>(h,a,b,r) \<Rightarrow> Success (h,b - a, r))"
declare op_sub_def[\<nu>instr]
theorem sub_nat_\<nu>proc[\<nu>overload -]:
    "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> x - y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_sub_def by auto (meson unat_sub_if_size)
  
subsubsection \<open>less\<close>

definition op_lt :: " ('w::len) itself \<Rightarrow> 'w word \<times> 'w word \<times> ('r::lrep) \<longmapsto> 1 word \<times> 'r"
  where "op_lt _ = (\<lambda>(h,a,b,r).  Success (h, (if  b < a then 1 else 0), r))"
declare op_lt_def[\<nu>instr]
theorem op_lt_\<nu>proc[\<nu>overload <]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> (x < y) \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_lt_def by (auto simp add: word_less_nat_alt)

definition op_le :: " ('w::len) itself \<Rightarrow> 'w word \<times> 'w word \<times> ('r::lrep) \<longmapsto> 1 word \<times> 'r "
  where "op_le _ = (\<lambda>(h,a,b,r).  Success (h, (if  b \<le> a then 1 else 0), r))"
theorem op_le_\<nu>proc[\<nu>overload \<le>]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> (x \<le> y) \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_le_def by (auto simp add: word_le_nat_alt)

subsubsection \<open>equal\<close>

definition op_equal :: " ('a::{ceq,lrep}) \<times> 'a \<times> ('r::stack) \<longmapsto> 1 word \<times> 'r"
  where "op_equal = (\<lambda>(h,a,b,r). if ceqable h b a then Success (h,(if ceq b a then 1 else 0), r) else Fail)"
theorem op_equal[\<nu>overload =]:
  "\<nu>Equal N P eq \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P a b \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal \<blangle> R\<heavy_comma> a \<tycolon> N\<heavy_comma> b \<tycolon> N\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> eq a b \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_equal_def by (auto 0 6)

section \<open>Tuple Operations\<close>

subsection \<open>Tuple construction & destruction\<close>

subsubsection \<open>op_constr_tuple\<close>

definition op_constr_tuple :: "('a::field_list) \<times> ('r::stack) \<longmapsto> 'a tuple \<times> 'r"
  where "op_constr_tuple = (\<lambda>(h,a,r). Success (h, Tuple a, r))"

theorem tup_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_constr_tuple \<blangle> R \<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace> \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_constr_tuple_def Procedure_def by simp

subsubsection \<open>op_destr_tuple\<close>

definition op_destr_tuple :: "('a::field_list) tuple \<times> ('r::stack) \<longmapsto> 'a \<times> 'r"
  where "op_destr_tuple s = (case s of (h,Tuple a, r) \<Rightarrow> Success (h,a,r))"

theorem det_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_destr_tuple \<blangle> R\<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding Procedure_def op_destr_tuple_def by (simp add: tuple_forall)

subsection \<open>Field Index\<close>

definition FieldIndex :: " ('a,'a,'ax,'ax) index \<Rightarrow> ('ax::lrep,'bx) \<nu> \<Rightarrow> ('a::lrep,'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'bx) \<Rightarrow> (('bx \<Rightarrow> 'bx) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>bool"
  where "FieldIndex adr X A gt mp \<longleftrightarrow> (\<forall>a f. \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<blangle> \<tort_lbrace>gt a \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> \<tort_lbrace>f (gt a) \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>mp f a \<tycolon> A\<tort_rbrace> \<brangle>)"

lemma [final_proc_rewrite2]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e FieldIndex a X A g m \<equiv> FieldIndex a X A g m" unfolding Premise_def .

lemma FieldIndex_here: "FieldIndex index_here X X id id"
  unfolding FieldIndex_def \<nu>index_def index_here_def by auto
lemma FieldIndex_left: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_left f) X (A \<cross_product> R) (gt o fst) (apfst o mp)"
  unfolding FieldIndex_def \<nu>index_def index_left_def by auto
lemma FieldIndex_right: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_right f) X (R \<cross_product> A) (gt o snd) (apsnd o mp)"
  unfolding FieldIndex_def \<nu>index_def index_right_def by auto

definition index_enter_tup :: "(('a::field_list),('b::field_list),'x,'y) index \<Rightarrow> ('a tuple, 'b tuple, 'x, 'y) index"
  where "index_enter_tup adr = (case adr of Index g m \<Rightarrow> Index (case_tuple g) (map_tuple o m))"
lemma FieldIndex_tupl: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_enter_tup f) X \<lbrace> A \<rbrace> gt mp"
  unfolding FieldIndex_def \<nu>index_def index_enter_tup_def by (auto simp add: tuple_forall)

\<nu>processor field_index 110 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn meta => Parse.nat >> (fn i => fn _ =>
  NuBasics.elim_SPEC meta |> apfst (fn major =>
  let open NuBasics NuHelp
    val arity = Logic.dest_implies (prop_of major) |> #1 |> dest_Trueprop |> dest_quinop \<^const_name>\<open>FieldIndex\<close> |> #3
        |> dest_monop \<^const_name>\<open>NuTuple\<close> |> strip_binop_r \<^const_name>\<open>Fusion\<close> |> length
    val path1 = funpow (i-1) (fn th => th RS @{thm FieldIndex_right})
        (@{thm FieldIndex_here} |> (fn th => if arity = i then th else th RS @{thm FieldIndex_left}))
  in 
    (path1 RS (@{thm FieldIndex_tupl} RS major))
  end) |> NuBasics.intro_SPEC )\<close>


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
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer ty \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> delta \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto>
      R\<heavy_comma> addr ||+ delta \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_shift_pointer_def  by (cases addr) (auto simp add: lrep_exps same_addr_offset_def)


theorem op_shift_pointer_slice[ unfolded Separation_assoc, \<nu>overload split ]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < length xs \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer LLTY('p) \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> addr \<R_arr_tail> xs \<tycolon> Array T
      \<longmapsto> R\<heavy_comma> addr ||+ n \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> (addr \<R_arr_tail> take n xs \<tycolon> Array T \<heavy_asterisk> shift_addr addr n \<R_arr_tail> drop n xs \<tycolon> Array T) \<brangle>"
  for T :: "('p::field, 'x) \<nu>"
  unfolding \<nu>def op_shift_pointer_def Array_def Heap_Delimiter_def apply (cases addr)
  apply (auto simp add: lrep_exps same_addr_offset_def raw_offset_of_def distrib_right
        add.commute add.left_commute intro: heap_split_id )
  subgoal for x1 x2 aa h1 h2 b
    by (rule heap_split_id, simp, rule heap_split_by_addr_set[of _ _ "{(x1 |+ x2 + i) | i. i < n}"]) (auto)
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





      
theorem alloc_array_\<nu>proc:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N \<Longrightarrow> \<nu>Zero N zero \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc TYPE('x)
      \<blangle> R\<heavy_comma> n \<tycolon> \<nat>[size_t] \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H
        \<longmapsto> (\<exists>*seg. (R\<heavy_comma> (seg |+ 0) \<tycolon> Pointer \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> (seg |+ 0) \<R_arr_tail> replicate n zero \<tycolon> Array N)) \<brangle>"
  for N :: "('x::{zero,field},'b)\<nu>"
  unfolding \<nu>def op_alloc_def Array_def Heap_Delimiter_def
  apply (auto simp add: lrep_exps list_all2_conv_all_nth Let_def same_addr_offset_def) 
  apply (rule malloc_split, simp add: heap_assignN_eval)
  apply (auto simp add: heap_assignN_eval) done

(*
proc alloc : \<open>i\<hyphen>j \<tycolon> IdSrc\<close> \<longmapsto> \<open>Gi 0 \<left_fish_tail>(i\<hyphen>j |+ 0) \<R_arr_tail> Gi 0 \<left_fish_tail> zero \<tycolon> Ref N \<heavy_comma> i\<hyphen>j + 1 \<tycolon> IdSrc\<close>
  for N :: "('x::{zero,field},'b) nu"
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N" and [\<nu>intro]: "\<nu>Zero N zero"
  \<nu>have A[simp]: "replicate 1 zero = [zero]" by (simp add: One_nat_def)
  \<bullet> 1 \<leftarrow> v alloc_array N
  finish
*)
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
  unfolding op_load_def Procedure_def FieldIndex_def \<nu>index_def Heap_Delimiter_def
  by (cases field_index, cases addr)  (auto simp add: lrep_exps MemAddrState_def split: option.split iff: addr_allocated_def)

lemmas [ \<nu>overload "\<up>" ] = op_load[THEN mp, OF FieldIndex_here, simplified]

proc i_load_n[\<nu>overload "\<up>:"]:
  \<open>a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs \<tycolon> Array X\<close> \<longmapsto> \<open>gt (xs ! i) \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<nu>"
  requires [used]: "i < length xs" and idx: "FieldIndex field_index Y X gt mp"
  \<bullet> + \<up>: idx
  finish

lemmas [ \<nu>overload "\<up>" ] = i_load_n_\<nu>proc[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]


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
    \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> y \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> addr \<R_arr_tail> x \<tycolon> Ref X \<longmapsto> R \<heavy_comma> addr \<tycolon> Pointer \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> addr \<R_arr_tail> mp (\<lambda>_. y) x \<tycolon> Ref X\<brangle> "
  for X :: "('x::field, 'c) \<nu>"
  unfolding op_store_def Procedure_def FieldIndex_def \<nu>index_def Heap_Delimiter_def Stack_Delimiter_def
  apply (cases field_index, cases addr)
  apply (auto simp add: lrep_exps Let_def split: option.split iff: addr_allocated_def)
  subgoal premises prems for x1 x2 x1a x2a aa ofs b x2b h1 h2 proof -
    have t1: "\<And>v. (h1 ++ h2)(MemAddress (x1a |+ x2a) \<mapsto> v) = h1 ++ (h2(MemAddress (x1a |+ x2a) \<mapsto> v))"
      using prems disjoint_rewR by simp
    have t2: "\<And>v.  dom (h2(MemAddress (x1a |+ x2a) \<mapsto> v)) = dom h2"
      using prems by auto
    show ?thesis apply (unfold t1, rule heap_split_id, unfold t2, simp add: prems)
      using prems by (auto simp add: MemAddrState_def)
  qed done

lemmas [ \<nu>overload "\<down>" ] = op_store[THEN mp, OF FieldIndex_here, simplified]

proc i_store_n[\<nu>overload "\<down>:"]:
  \<open>R\<heavy_comma> a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> y \<tycolon> Y \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs \<tycolon> Array X\<close> \<longmapsto> \<open>R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs[i := mp (\<lambda>_. y) (xs ! i)] \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<nu>"
  requires [used]: "i < length xs" and idx: "FieldIndex field_index Y X gt mp"
  \<bullet> \<rightarrow> y + y \<down>: idx drop
  finish

lemmas [ \<nu>overload "\<down>" ] = i_store_n_\<nu>proc[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]



ML \<open>@{type_name set}\<close>
proc test: \<open>R\<heavy_comma> i \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>R\<heavy_comma> 0 \<tycolon> \<nat>[32]\<close>
  \<bullet> until i subj \<open>0 < i\<close> \<medium_left_bracket> \<bullet> \<rightarrow> i i 1 -
  \<bullet> 0 i <
  thm decorated_All_def[symmetric]
  \<medium_left_bracket>  \<nu>debug note that 

  thm XXXX

end
