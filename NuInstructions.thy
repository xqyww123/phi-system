theory NuInstructions
  imports NuSys NuBasicAbstractors
  keywords
     "\<up>:" "\<Up>:" "\<down>:" "\<Down>:" "subj" "of" "while" "always" :: quasi_command
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

subsubsection \<open>drop\<close>

definition op_drop :: "('a::lrep) \<times> ('r::lrep) \<Rightarrow> 'r state" where
  "op_drop x = (case x of (a,r) \<Rightarrow> if disposable a then StatOn r else STrap)"
declare op_drop_def[\<nu>instr]
theorem drop_\<nu>proc: "\<nu>Disposable X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> R \<heavy_comma> X \<longmapsto> R \<brangle>" unfolding \<nu>def op_drop_def by auto

definition op_fake_drop :: "('a::lrep) \<times> ('r::lrep) \<Rightarrow> 'r state" where
  "op_fake_drop x = (case x of (_,r) \<Rightarrow> StatOn r)"
theorem fake_drop_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_fake_drop \<blangle> R \<heavy_comma> X \<longmapsto> R \<brangle>" unfolding \<nu>def op_fake_drop_def by auto

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



\<nu>processor pair_auto_dest 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<flower> W)\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema} |> NuSys.accept_proc ctx)\<close>
\<nu>processor pair_auto_dest' 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B))\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema'} |> NuSys.accept_proc ctx)\<close>

definition op_crash :: "('r::lrep) \<Rightarrow> ('x::lrep) state" where "op_crash r = SNeg"
lemma op_crash:  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_crash \<blangle> X \<longmapsto> Y \<brangle>" unfolding \<nu>def op_crash_def by auto

subsubsection \<open>calling conversion\<close>

definition strip_end_tail :: " (('a::lrep) \<times> void \<Rightarrow> (('b::lrep) \<times> void) state) \<Rightarrow> 'a \<times> ('r::stack) \<Rightarrow> ('b \<times> 'r) state"
  where "strip_end_tail f s = (case s of (a,r) \<Rightarrow> bind (f (a,void)) (\<lambda>(b,_). StatOn (b,r)))"
lemma strip_end_tail: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> A \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c strip_end_tail f \<blangle> R\<heavy_comma> A \<longmapsto> R\<heavy_comma> B \<brangle>"
  unfolding strip_end_tail_def Procedure_def bind_def by (auto 4 4)

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
lemma [simp]: "(if P then (A and_ty B) else (A' and_ty B')) = ((if P then A else A') and_ty (if P then B else B'))"  by auto
lemma [simp]: "(if P then RegisterTy name T else RegisterTy name' T') = RegisterTy name (if P then T else T')" by (auto simp add: name_tag_eq)
(*TODO: maybe too radical*)
lemma [simp]: "(if P then a \<R_arr_tail> x else a' \<R_arr_tail> x') = (if P then a else a') \<R_arr_tail> (if P then x else x')" by auto

subsubsection \<open>while\<close>

consts op_while_WF :: "'c itself \<Rightarrow> (('x::lrep) \<times> ('r::stack) \<flower> ('w::register_collection) \<Rightarrow> (('x \<times> 1 word) \<times> 'r \<flower> 'w) state)
  \<Rightarrow> ('x \<times> 'r \<flower> 'w \<Rightarrow> ('x \<times> 'r \<flower> 'w) state) \<Rightarrow> ('x \<times> 'r \<flower> 'w \<Rightarrow> ('x \<times> 'r \<flower> 'w) state)"
specification ("op_while_WF")
  while_WF_\<nu>proc[simplified PremiseHOL ParamHOL]: "
  ParamHOL P \<Longrightarrow> ParamHOL Rc \<Longrightarrow> ParamHOL Rb \<Longrightarrow> PremiseHOL (wf (Rc O Rb))
  \<Longrightarrow> (\<And>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> (R \<heavy_comma> (x1::'c) \<tycolon> X) \<flower> W \<longmapsto> (R \<heavy_comma> {(y, y \<in> P) | y. (y,x1) \<in> Rc } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (X \<nuFusion> \<bool>)) \<flower> W \<brangle>)
  \<Longrightarrow> (\<And>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> (R \<heavy_comma> x2 \<tycolon> (X \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P)) \<flower> W \<longmapsto> (R \<heavy_comma> {y. (y,x2) \<in> Rb} \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X) \<flower> W \<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_while_WF TYPE('c) brC brB \<blangle> (R \<heavy_comma> x \<tycolon> X) \<flower> W \<longmapsto> (R \<heavy_comma> - P \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X) \<flower> W \<brangle>"
  apply (rule exI) using op_crash by auto

consts op_while :: "'c itself \<Rightarrow> (('x::lrep) \<times> ('r::stack) \<flower> ('w::register_collection) \<Rightarrow> ((1 word \<times> 'x) \<times> 'r \<flower> 'w) state)
  \<Rightarrow> ('x \<times> 'r \<flower> 'w \<Rightarrow> ('x \<times> 'r \<flower> 'w) state) \<Rightarrow> ('x \<times> 'r \<flower> 'w \<Rightarrow> ('x \<times> 'r \<flower> 'w) state)"
specification ("op_while")
  i_while_raw_\<nu>proc[simplified PremiseHOL ParamHOL]: "
  ParamHOL P
  \<Longrightarrow> (\<And>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> (R \<heavy_comma> (x1::'c) \<tycolon> X) \<flower> W \<longmapsto> (R \<heavy_comma> {(y \<in> P, y) |y. True } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (\<bool> \<nuFusion> X)) \<flower> W \<brangle>)
  \<Longrightarrow> (\<And>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> (R \<heavy_comma> x2 \<tycolon> (X \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P)) \<flower> W \<longmapsto> (R \<heavy_comma> UNIV \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X) \<flower> W \<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_while TYPE('c) brC brB \<blangle> (R \<heavy_comma> x \<tycolon> X) \<flower> W \<longmapsto> (R \<heavy_comma> - P \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e X) \<flower> W \<brangle>"
  apply (rule exI) using op_crash by auto

proc' i_while: \<open>(R \<heavy_comma> x \<tycolon> X) \<flower> W\<close> \<longmapsto> \<open>(R \<heavy_comma> - P \<tycolon> <some'> (X <schema> sch <where''> Always)) \<flower> W\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m sch" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m Always" and "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P"
    and [simplified StructuralTag_def, intro]: "<Structural> sch y = x" and [intro]: "y \<in> Always"
    and brC: \<open>(\<And>x1. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brC \<blangle> (R \<heavy_comma> x1 \<tycolon> X <schema> sch <where''> Always) \<flower> W \<longmapsto> (R \<heavy_comma> { (y \<in> P, y) |y. True } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (\<bool> \<nuFusion> X <schema> sch <where''> Always)) \<flower> W \<brangle>)\<close>
    and brB: \<open>(\<And>x2. \<^bold>p\<^bold>r\<^bold>o\<^bold>c brB \<blangle> (R \<heavy_comma> x2 \<tycolon> (X <schema> sch <where''> Always <where'> P)) \<flower> W \<longmapsto> (R \<heavy_comma> UNIV \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (X <schema> sch <where''> Always)) \<flower> W \<brangle>)\<close>
  \<bullet> cast i_schema sch cast refine' Always  i_while_raw P \<Longleftarrow> brC \<Longleftarrow> brB[simplified SchemaCondition_simp] finish


ML \<open>@{term "(a,b)"}\<close>
\<nu>processor while 110 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (T \<flower> W)\<close> \<open>fn ctx => fn meta => let open Parse Scan NuHelp NuBasics in
  $$$ "while" |-- vars -- option ($$$ "in" |-- term) -- ($$$ "subj" |-- term) -- Scan.option ($$$ "always" |-- term) >> (fn (((vars, schema), subj), always) => fn _ =>
  let open NuHelp
    val (vars',ctx) = Proof_Context.add_fixes (map (fn (a,b,c) => (a,Option.map (Syntax.read_typ ctx) b,c)) vars) ctx
    val vars = (map (fn (x,_,_) => Binding.name_of x) vars) ~~ vars'
    val always = case always of SOME x =>
          Syntax.parse_term ctx x |> tuple_abs vars |> mk_monop \<^const_name>\<open>Collect\<close>
      | NONE => Const (\<^const_name>\<open>Orderings.top_class.top\<close>, dummyT)
    val (arity,schema) = case schema of SOME sch =>
                    let val raw = Syntax.parse_term ctx sch
                    in (length (strip_binop_r \<^const_name>\<open>Pair\<close> raw), tuple_abs vars raw) end
                | _ => (length vars, Const (\<^const_name>\<open>id\<close>, dummyT))
    val subj = tuple_abs vars (Syntax.parse_term ctx subj) |> mk_monop \<^const_name>\<open>Collect\<close>
    val apply_pr = apply_proc_naive @{thm pr_auto_schema} #> NuSys.accept_proc ctx
  in meta |> funpow (arity-1) apply_pr |> apply_proc_naive @{thm i_while_\<nu>proc}
         |> NuSys.set_param ctx schema |> NuSys.set_param ctx always  |> NuSys.set_param ctx subj
  end
) end\<close>

subsubsection \<open>recursion\<close>

consts op_recursion_WF :: " 'a itself \<times> 'b itself \<Rightarrow>
    ((('u::lrep) \<times> void \<Rightarrow> (('v::lrep) \<times> void) state) \<Rightarrow> ('u \<times> void \<Rightarrow> ('v \<times> void) state)) \<Rightarrow> ('u \<times> ('r::stack) \<Rightarrow> ('v \<times> 'r) state) "
specification ("op_recursion_WF")
  recursion_WF_\<nu>proc[simplified PremiseHOL ParamHOL]:
  "ParamHOL h \<Longrightarrow> ParamHOL M \<Longrightarrow> ParamHOL WF \<Longrightarrow> PremiseHOL (wf WF) \<Longrightarrow>
  (\<And>x' g. (\<And>x''. PremiseHOL ((x'',x') \<in> WF) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> \<^bold>E\<^bold>N\<^bold>D \<heavy_comma> x'' \<tycolon> N \<longmapsto> \<^bold>E\<^bold>N\<^bold>D \<heavy_comma> h x'' \<tycolon> M \<brangle>)
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


section \<open>Basic instructions\<close>

subsection \<open>Ghost\<close>

\<nu>overloads ghost and ghostize

definition op_ghost :: "('r \<Rightarrow> 'a) ghost \<Rightarrow> ('r::stack) \<Rightarrow> ('a ghost \<times> 'r) state"
  where "op_ghost gen r = StatOn (map_ghost (\<lambda>g. g r) gen,r)"

(* TODO: this procedure is too dangerous to disable the compilation *)
lemma [\<nu>intro]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (x \<tycolon> Ghost) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_ghost (ghost (\<lambda>_. x)) \<blangle> R \<longmapsto> R \<heavy_comma> x \<tycolon> Ghost \<brangle>"
  unfolding op_ghost_def \<nu>def by simp

lemma [\<nu>overload ghost]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_ghost (ghost (\<lambda>(x,r). unat x)) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['bits::len] \<longmapsto> R\<heavy_comma> x \<tycolon> \<nat>['bits]\<heavy_comma> x \<tycolon> Ghost \<brangle>"
  unfolding op_ghost_def Procedure_def by simp

proc i_ghostize_nat[\<nu>overload ghostize]: \<open>x \<tycolon> \<nat>['bits::len]\<close> \<longmapsto> \<open>x \<tycolon> Ghost \<close>
  \<bullet> x ghost \<rightarrow> y drop y finish

lemma [\<nu>overload ghost]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_ghost (ghost (\<lambda>(x,r). sint x)) \<blangle> R\<heavy_comma> x \<tycolon> \<int>['bits::len] \<longmapsto> R\<heavy_comma> x \<tycolon> \<int>['bits]\<heavy_comma> x \<tycolon> Ghost \<brangle>"
  unfolding op_ghost_def Procedure_def by simp

proc i_ghostize_int[\<nu>overload ghostize]: \<open>x \<tycolon> \<int>['bits::len]\<close> \<longmapsto> \<open>x \<tycolon> Ghost \<close>
  \<bullet> x ghost \<rightarrow> y drop y finish

section \<open>Arithmetic instructions\<close>

\<nu>overloads "+" and round_add and "<" and "\<le>" and "-" and "="


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

definition op_le :: " ('w::len) itself \<Rightarrow> ('w word \<times> 'w word \<times> ('r::lrep)) \<Rightarrow> (1 word \<times> 'r) state"
  where "op_le _ s = (case s of (a,b,r) \<Rightarrow>  StatOn ((if  b \<le> a then 1 else 0), r))"
theorem op_le_\<nu>proc[\<nu>overload \<le>]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le (TYPE('w::len)) \<blangle>\<R>\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w] \<longmapsto> \<R>\<heavy_comma> (x \<le> y) \<tycolon> \<bool> \<brangle>"
  unfolding \<nu>def op_le_def by (auto simp add: word_le_nat_alt)

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

section \<open>Memory & Pointer Operations\<close>

subsection \<open>Allocation\<close>

\<nu>overloads spawn

subsubsection \<open>op_alloc_id_space\<close>

definition op_alloc_id_space :: " identifier \<times> ('r::stack) \<Rightarrow> (identifier \<times> identifier \<times> ('r::stack)) state"
  where "op_alloc_id_space s = (case s of (i,r) \<Rightarrow> StatOn (alloc_identifier_space i, alloc_identifier i, r))"

theorem alloc_id_space_\<nu>proc[\<nu>overload spawn]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc_id_space \<blangle> R\<heavy_comma> i\<hyphen>j \<tycolon> IdSrc \<longmapsto> R\<heavy_comma> i\<hyphen>j+1 \<tycolon> IdSrc \<heavy_comma> i\<hyphen>j\<hyphen>0 \<tycolon> IdSrc\<brangle>"
  unfolding op_alloc_id_space_def Procedure_def by (simp add: lrep_exps)

subsubsection \<open>op_alloc\<close>

definition op_alloc :: "('x::{zero,field}) itself
    \<Rightarrow> identifier \<times> ('bits::len) word \<times> ('r::stack) \<Rightarrow> (identifier \<times> (0, 'x) memref \<times>'r) state"
  where "op_alloc _ s = (case s of (i,n,r) \<Rightarrow> if segment_len i = unat n \<and> segment_llty i = llty TYPE('x) then
    StatOn (alloc_identifier i, Tuple ((memptr (0 \<left_fish_tail>i |+ 0) :: 0 memptr),
          0 \<left_fish_tail> memcon (\<lambda>adr. case adr of (seg |+ ofs) \<Rightarrow> if seg = i \<and> ofs < int (unat n) then Some 0 else None)), r)
  else SNeg)"

theorem alloc_array_\<nu>proc:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N \<Longrightarrow> \<nu>Zero N zero \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc TYPE('x)
      \<blangle> R\<heavy_comma> n \<tycolon> \<nat>[('bits::len)] \<heavy_comma> i\<hyphen>j \<tycolon> IdSrc \<longmapsto> R\<heavy_comma> Gi 0 \<left_fish_tail>(i\<hyphen>j |+ 0) \<R_arr_tail> Gi 0 \<left_fish_tail> replicate n zero \<tycolon> RefS N \<heavy_comma> i\<hyphen>j + 1 \<tycolon> IdSrc \<brangle>"
  for N :: "('x::{zero,field},'b) nu"
  unfolding \<nu>def op_alloc_def by (auto simp add: list_all2_conv_all_nth)

proc alloc : \<open>i\<hyphen>j \<tycolon> IdSrc\<close> \<longmapsto> \<open>Gi 0 \<left_fish_tail>(i\<hyphen>j |+ 0) \<R_arr_tail> Gi 0 \<left_fish_tail> zero \<tycolon> Ref N \<heavy_comma> i\<hyphen>j + 1 \<tycolon> IdSrc\<close>
  for N :: "('x::{zero,field},'b) nu"
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N" and [\<nu>intro]: "\<nu>Zero N zero"
  \<nu>have A[simp]: "replicate 1 zero = [zero]" by (simp add: One_nat_def)
  \<bullet> 1 \<leftarrow> v alloc_array N
  finish

subsection \<open>Pointer Arithmetic & Split\<close>

\<nu>overloads split and pop

subsubsection \<open>op_shift_pointer\<close>

definition op_shift_pointer :: "llty \<Rightarrow> ('bits::len) word \<times> ('spc::len0) memptr \<times> ('r::stack) \<Rightarrow> ('spc memptr \<times> 'r) state"
  where "op_shift_pointer ty s = (case s of (d, memptr(z \<left_fish_tail> seg |+ i), r) \<Rightarrow>
    if segment_llty seg = ty then StatOn (memptr (z \<left_fish_tail> seg |+ (i + sint d)), r) else STrap)"

theorem op_shift_pointer[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer ty \<blangle> R\<heavy_comma> z \<left_fish_tail> seg |+ i \<tycolon> SlidePtr['spc::len0] ty\<heavy_comma> d \<tycolon> \<int>['bits::len] \<longmapsto> R\<heavy_comma> z \<left_fish_tail> seg |+ (i + d) \<tycolon> SlidePtr['spc] ty \<brangle>"
  unfolding op_shift_pointer_def Procedure_def by (simp add: lrep_exps)

theorem op_shift_pointer_within[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e within_seg 0 (seg |+ (i + d)) \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer ty \<blangle> R\<heavy_comma> z \<left_fish_tail> seg |+ i \<tycolon> Pointer['spc::len0] ty\<heavy_comma> d \<tycolon> \<int>['bits::len] \<longmapsto> R\<heavy_comma> z \<left_fish_tail> seg |+ (i + d) \<tycolon> Pointer['spc] ty \<brangle>"
  unfolding op_shift_pointer_def Procedure_def by (auto simp add: lrep_exps)

definition op_shift_pointer' :: "llty \<Rightarrow> ('bits::len) word \<times> ('spc::len0) memptr \<times> ('r::stack) \<Rightarrow> ('spc memptr \<times> 'r) state"
  where "op_shift_pointer' ty s = (case s of (d, memptr(z \<left_fish_tail> seg |+ i), r) \<Rightarrow>
    if segment_llty seg = ty then StatOn (memptr (z \<left_fish_tail> seg |+ (i + uint d)), r) else STrap)"

theorem op_shift_pointer'[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer' ty \<blangle> R\<heavy_comma> z \<left_fish_tail> seg |+ i \<tycolon> SlidePtr['spc::len0] ty\<heavy_comma> d \<tycolon> \<nat>['bits::len] \<longmapsto> R\<heavy_comma> z \<left_fish_tail> seg |+ (i + int d) \<tycolon> SlidePtr['spc] ty \<brangle>"
  unfolding op_shift_pointer'_def Procedure_def by (auto simp add: lrep_exps)

theorem op_shift_pointer_within'[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e within_seg 0 (seg |+ (i + int d)) \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer' ty \<blangle> R\<heavy_comma> z \<left_fish_tail> seg |+ i \<tycolon> Pointer['spc::len0] ty\<heavy_comma> d \<tycolon> \<nat>['bits::len] \<longmapsto> R\<heavy_comma> z \<left_fish_tail> seg |+ (i + int d) \<tycolon> Pointer['spc] ty \<brangle>"
  unfolding op_shift_pointer'_def Procedure_def by (auto simp add: lrep_exps)

subsubsection \<open>op_separate_mem\<close>

definition op_separate_mem :: " memadr set \<Rightarrow> ('x::field) memobj \<times> ('r::stack) \<Rightarrow> ('x memobj \<times> 'x memobj \<times> 'r) state "
  where "op_separate_mem P s = (case s of (z \<left_fish_tail> memcon f, r) \<Rightarrow> StatOn (z \<left_fish_tail> memcon (f |` P), z \<left_fish_tail> memcon (f |` (- P)),  r))"

definition op_merge_mem :: " ('x::field) memobj \<times> 'x memobj \<times> ('r::stack) \<Rightarrow> ('x memobj \<times> 'r) state "
  where "op_merge_mem s = (case s of (z1 \<left_fish_tail> memcon f1, z2 \<left_fish_tail> memcon f2, r) \<Rightarrow>
    if z1 = z2 \<and> (dom f1 \<inter> dom f2) = {} then StatOn (z2 \<left_fish_tail> memcon (f1 ++ f2), r) else STrap)"

(* theorem op_slice_mem_\<nu>proc[\<nu>overload split]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n \<le> length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_slice_mem \<blangle> R\<heavy_comma> z \<left_fish_tail> (seg |+ i) \<R_arr_tail> xs \<tycolon> MemSlice N\<heavy_comma> n \<tycolon> Ghost
    \<longmapsto> R\<heavy_comma> z \<left_fish_tail> (seg |+ i) \<R_arr_tail> (take n xs) \<tycolon> MemSlice N\<heavy_comma> z \<left_fish_tail> (seg |+ (i + int n)) \<R_arr_tail> (drop n xs) \<tycolon> MemSlice N \<brangle>"
  unfolding op_slice_mem_def Procedure_def Premise_def by (auto simp add: lrep_exps list_all2_conv_all_nth) 

proc op_slice_mem2[\<nu>overload split]:
  \<open>z \<left_fish_tail> (seg |+ i) \<R_arr_tail> xs \<tycolon> MemSlice N\<heavy_comma> n \<tycolon> \<nat>['bits::len]\<close>
  \<longmapsto> \<open>z \<left_fish_tail> (seg |+ i) \<R_arr_tail> (take n xs) \<tycolon> MemSlice N\<heavy_comma> z \<left_fish_tail> (seg |+ (i + int n)) \<R_arr_tail> (drop n xs) \<tycolon> MemSlice N\<close>
  requires [intro]: " n \<le> length xs"
  \<bullet> \<leftarrow> v n ghostize  op_slice_mem finish

subsubsection \<open>i_split_ref\<close>

proc i_split_ref[\<nu>overload split]: \<open>zp \<left_fish_tail> (seg |+ i) \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] N\<heavy_comma> n \<tycolon> \<nat>['bits::len]\<close>
  \<longmapsto> \<open>zp + Gi 1 \<left_fish_tail> (seg |+ (i + int n)) \<R_arr_tail> z \<left_fish_tail> (drop n xs) \<tycolon> RefS['spc] N\<heavy_comma> zp + Gi 1 \<left_fish_tail> (seg |+ i) \<R_arr_tail> z \<left_fish_tail> (take n xs) \<tycolon> RefS['spc] N\<close>
  requires [used]: "n \<le> length xs"
  \<bullet> \<leftarrow> v cast E det dpr n split \<rightarrow> (m1,m2) dup n
  \<bullet> !! + cast fixtyp affirm by (auto 0 3)
  \<bullet> \<leftarrow> m2 pr tup cast RefS \<rightarrow> m2
  \<bullet> \<leftarrow> m1 pr tup cast RefS \<rightarrow> m1 \<leftarrow> (m2,m1)
  finish

proc i_pop_refs[simplified length_greater_0_conv, \<nu>overload pop]:
  \<open>zp \<left_fish_tail> (seg |+ i) \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] N\<close>
    \<longmapsto> \<open>zp + Gi 1 \<left_fish_tail> (seg |+ (i + 1)) \<R_arr_tail> z \<left_fish_tail> tl xs \<tycolon> RefS['spc] N \<heavy_comma> zp + Gi 1 \<left_fish_tail> (seg |+ i) \<R_arr_tail> z \<left_fish_tail> hd xs \<tycolon> Ref['spc] N\<close>
  requires [used]: "0 < length xs"
  \<nu>have A[simp]: "take 1 xs = [hd xs]" by (simp add: One_nat_def take_Suc)
  \<nu>have B[simp]: "drop 1 xs = tl xs" by (simp add: One_nat_def drop_Suc) 
  \<bullet> $v \<open>1 \<tycolon> \<nat>[32]\<close> split affirm by linarith \<bullet>
  finish *)

subsection \<open>Load & Store\<close>

\<nu>overloads \<up> and "\<up>:" and \<Up> and "\<Up>:" and \<down> and "\<down>:" and \<Down> and "\<Down>:"

abbreviation "list_map_at f i l \<equiv> list_update l i (f (l ! i))"

subsubsection \<open>Field Path Refining\<close>

definition AdrRefining :: " ('a,'a,'ax,'ax) address \<Rightarrow> ('ax::lrep,'bx) nu \<Rightarrow> ('a::lrep,'b) nu \<Rightarrow> ('b \<Rightarrow> 'bx) \<Rightarrow> (('bx \<Rightarrow> 'bx) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>bool"
  where "AdrRefining adr X A gt mp \<longleftrightarrow> (\<forall>a f. \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> \<tort_lbrace>gt a \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> \<tort_lbrace>f (gt a) \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>mp f a \<tycolon> A\<tort_rbrace> \<brangle>)"

lemma [final_proc_rewrite2]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e AdrRefining a X A g m \<equiv> Trueprop (AdrRefining a X A g m)" unfolding Premise_def .

lemma AdrRefining_here: "AdrRefining address_here X X id id"
  unfolding AdrRefining_def \<nu>address_def address_here_def by auto
lemma AdrRefining_left: "AdrRefining f X A gt mp \<Longrightarrow> AdrRefining (address_left f) X (A \<nuFusion> R) (gt o fst) (apfst o mp)"
  unfolding AdrRefining_def \<nu>address_def address_left_def by auto
lemma AdrRefining_right: "AdrRefining f X A gt mp \<Longrightarrow> AdrRefining (address_right f) X (R \<nuFusion> A) (gt o snd) (apsnd o mp)"
  unfolding AdrRefining_def \<nu>address_def address_right_def by auto

definition address_enter_tup :: "(('a::field_list),('b::field_list),'x,'y) address \<Rightarrow> ('a tuple, 'b tuple, 'x, 'y) address"
  where "address_enter_tup adr = (case adr of Address g m \<Rightarrow> Address (case_tuple g) (map_tuple o m))"
lemma AdrRefining_tupl: "AdrRefining f X A gt mp \<Longrightarrow> AdrRefining (address_enter_tup f) X \<lbrace> A \<rbrace> gt mp"
  unfolding AdrRefining_def \<nu>address_def address_enter_tup_def by (auto simp add: tuple_forall)

\<nu>processor field_accessing 110 \<open>AdrRefining f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn meta => Parse.nat >> (fn i => fn _ =>
  NuBasics.elim_SPEC meta |> apfst (fn major =>
  let open NuBasics NuHelp
    val arity = Logic.dest_implies (prop_of major) |> #1 |> dest_Trueprop |> dest_quinop \<^const_name>\<open>AdrRefining\<close> |> #3
        |> dest_monop \<^const_name>\<open>NuTuple\<close> |> strip_binop_r \<^const_name>\<open>Fusion\<close> |> length
    val path1 = funpow (i-1) (fn th => th RS @{thm AdrRefining_right})
        (@{thm AdrRefining_here} |> (fn th => if arity = i then th else th RS @{thm AdrRefining_left}))
  in 
    (path1 RS (@{thm AdrRefining_tupl} RS major))
  end) |> NuBasics.intro_SPEC )\<close>

subsubsection \<open>load\<close>

definition op_load :: " ('a,'a,'ax,'ax) address
      \<Rightarrow> ('spc::len0) memptr \<times>('a::field) memobj \<times> ('r::stack)
      \<Rightarrow> (('ax::{field,share}) \<times> ('spc::len0) memptr \<times>('a::field) memobj \<times> 'r) state "
  where "op_load path s = (case s of (memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon f, r) \<Rightarrow>
    (case f adr of Some data \<Rightarrow>
    if shareable (get_at path data) then
      StatOn (share (z + Gi 1) (get_at path data),
          memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon (f(adr := Some (map_at path (share (Gi 1)) data))), r)
    else STrap | _ \<Rightarrow> STrap))"

lemma [elim!]: "rel_option R p (Some x) \<Longrightarrow> (\<And>p'. p = Some p' \<Longrightarrow> R p' x \<Longrightarrow> C) \<Longrightarrow> C" by (cases p) auto
lemma rel_option_elim: "rel_option R p x \<Longrightarrow> (p = None \<Longrightarrow> x = None \<Longrightarrow> C) \<Longrightarrow> (\<And>p' x'. p = Some p' \<Longrightarrow> x = Some x' \<Longrightarrow> R p' x' \<Longrightarrow> C) \<Longrightarrow>  C"
  by (cases p; cases x) auto 

theorem op_load[\<nu>overload "\<up>:"]:
  "AdrRefining field_index Y X gt mp \<Longrightarrow> \<nu>Share Y P sh
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e m a = Some x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P (gt x)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load field_index \<blangle> R\<heavy_comma> z \<left_fish_tail>m \<tycolon> MemMap X\<heavy_comma> zp \<left_fish_tail> a \<tycolon> RawPtr['spc::len0]
    \<longmapsto> R\<heavy_comma> z \<left_fish_tail>m(a := Some (mp (sh (Gi 1)) x)) \<tycolon> MemMap X\<heavy_comma> zp \<left_fish_tail> a \<tycolon> RawPtr['spc::len0]\<heavy_comma> sh (z + Gi 1) (gt x) \<tycolon> Y\<brangle> "
unfolding op_load_def \<nu>def \<nu>Share_def AdrRefining_def \<nu>address_def  apply
      (auto split: option.split simp add: lrep_exps list_all2_conv_all_nth nth_list_update)
  by (metis option.rel_inject option.rel_distinct)+

proc i_load_n[\<nu>overload "\<up>:"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> mp (sh (Gi 1)) x \<tycolon> RefS['spc] X\<heavy_comma> sh (z + Gi 1) (gt x) \<tycolon> Y\<close>
  \<bullet> v cast E det dpr 

theorem op_load[\<nu>overload "\<up>:"]: "
  AdrRefining field_index Y X gt mp \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<nu>Share Y P sh
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P (gt (xs ! i))
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load field_index \<blangle> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<heavy_comma> i \<tycolon> \<nat>['bits::len]
    \<longmapsto> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> (list_map_at (mp (sh (Gi 1))) i xs) \<tycolon> RefS['spc] X\<heavy_comma> sh (z + Gi 1) (gt (xs ! i)) \<tycolon> Y\<brangle> "
  unfolding op_load_def \<nu>def \<nu>Share_def AdrRefining_def \<nu>address_def  by
      (auto 4 4 simp add: lrep_exps list_all2_conv_all_nth nth_list_update)

proc i_load1[\<nu>overload "\<up>:"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> mp (sh (Gi 1)) x \<tycolon> Ref['spc] X\<heavy_comma> sh (z + Gi 1) (gt x) \<tycolon> Y\<close>
  for Y :: "('b::{share,field},'c) nu"
  requires [\<nu>intro]: "AdrRefining field_index Y X gt mp" and [\<nu>intro]: "\<nu>Share Y P sh" and [simp]: "P (gt x)" 
  \<bullet> \<leftarrow> v \<open>0 \<tycolon> \<nat>[32]\<close> \<up>:
finish

proc i_load_here[\<nu>overload "\<up>"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X \<heavy_comma> i \<tycolon> \<nat>['bits::len]\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> list_map_at (sh (Gi 1)) i xs \<tycolon> RefS['spc] X\<heavy_comma> sh (z + Gi 1) (xs ! i) \<tycolon> X\<close>
  requires [intro]:"i < length xs" and [\<nu>intro]: "\<nu>Share X P sh" and [intro]: "P (xs ! i)"
  \<bullet> \<leftarrow> (v,i) \<up>: \<Longleftarrow> AdrRefining_here
finish

proc i_load_here1[\<nu>overload "\<up>"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> sh (Gi 1) x \<tycolon> Ref['spc] X\<heavy_comma> sh (z + Gi 1) x \<tycolon> X\<close>
  requires [\<nu>intro]: "\<nu>Share X P sh" and [intro]: "P x"
  \<bullet> \<leftarrow> v \<open>0 \<tycolon> \<nat>[32]\<close> \<up>: \<Longleftarrow> AdrRefining_here
  finish

subsubsection \<open>move\<close>

definition op_move :: " ('a,'a,'ax,'ax) address
      \<Rightarrow> ('bits::len) word \<times> ('spc::len0,('a::field)) memref \<times> ('r::stack)
      \<Rightarrow> (('ax::{field,share}) \<times> ('spc,'a) memref \<times> 'r) state "
  where "op_move path s = (case s of (i, Tuple (memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon adr' as), r) \<Rightarrow>
    if z = Gi 0 \<and> adr' = adr then
      StatOn (get_at path (as ! unat i),
          Tuple (memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon adr (list_map_at (map_at path dpriv) (unat i) as)), r)
    else STrap)"

theorem op_move[\<nu>overload "\<Up>:"]: "
  AdrRefining field_index Y X gt mp \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<nu>Deprive Y dp
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_move field_index \<blangle> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<heavy_comma> i \<tycolon> \<nat>['bits::len]
    \<longmapsto> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> (list_map_at (mp dp) i xs) \<tycolon> RefS['spc] X\<heavy_comma> gt (xs ! i) \<tycolon> Y\<brangle> "
  unfolding op_move_def \<nu>def AdrRefining_def \<nu>address_def  by
      (auto simp del: share_id simp add: lrep_exps list_all2_conv_all_nth nth_list_update)

proc i_move1[\<nu>overload "\<Up>:"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> mp dp x \<tycolon> Ref['spc] X\<heavy_comma> gt x \<tycolon> Y\<close>
  for Y :: "('b::{share,field},'c) nu"
  requires [\<nu>intro]: "AdrRefining field_index Y X gt mp" and [\<nu>intro]: "\<nu>Deprive Y dp"
  \<bullet> \<leftarrow> v \<open>0 \<tycolon> \<nat>[32]\<close> \<Up>: 
finish

proc i_move_here[\<nu>overload \<Up>]: \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<heavy_comma> i \<tycolon> \<nat>['bits::len]\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> (list_map_at dp i xs) \<tycolon> RefS['spc] X\<heavy_comma> xs ! i \<tycolon> X\<close>
  for X :: "('a::{share,field},'c) nu"
  requires [intro]:"i < length xs" and [\<nu>intro]: "\<nu>Deprive X dp"
  \<bullet> \<leftarrow> (v,i) \<Up>: \<Longleftarrow> AdrRefining_here 
finish

proc i_move_here1[\<nu>overload \<Up>]: \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<heavy_comma> i \<tycolon> \<nat>['bits::len]\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> dp x \<tycolon> Ref['spc] X\<heavy_comma> x \<tycolon> X\<close>
  for X :: "('a::{share,field},'c) nu"
  requires [\<nu>intro]: "\<nu>Deprive X dp"
  \<bullet> \<leftarrow> v \<Up>: \<Longleftarrow> AdrRefining_here 
finish

subsubsection \<open>store\<close>

definition op_store :: " ('a,'a,'ax,'ax) address
      \<Rightarrow> ('bits::len) word \<times> ('ax::field) \<times> ('spc::len0,('a::field)) memref \<times> ('r::stack)
      \<Rightarrow> (('spc,'a) memref \<times> 'r) state "
  where "op_store path s = (case s of (i, y, Tuple (memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon adr' as), r) \<Rightarrow>
    if z = Gi 0 \<and> adr' = adr then
      StatOn (Tuple (memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon adr (list_map_at (map_at path (\<lambda>_. y)) (unat i) as)), r)
    else STrap)"

theorem op_store[\<nu>overload "\<Down>:"]: "
  AdrRefining field_index Y X gt mp \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store field_index \<blangle> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<heavy_comma> y \<tycolon> Y\<heavy_comma> i \<tycolon> \<nat>['bits::len]
    \<longmapsto> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> (list_map_at (mp (\<lambda>_. y)) i xs) \<tycolon> RefS['spc] X\<brangle> "
  unfolding op_store_def \<nu>def AdrRefining_def \<nu>address_def  by
      (auto simp add: lrep_exps list_all2_conv_all_nth nth_list_update)

proc i_store1[\<nu>overload "\<Down>:"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<heavy_comma> y \<tycolon> Y\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> mp (\<lambda>_. y) x \<tycolon> Ref['spc] X\<close>
  for Y :: "('b::{share,field},'c) nu"
  requires [\<nu>intro]: "AdrRefining field_index Y X gt mp"
  \<bullet> $v $y \<open>0 \<tycolon> \<nat>[32]\<close> \<Down>: 
finish

proc i_store_here[\<nu>overload "\<Down>"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<heavy_comma> y \<tycolon> X\<heavy_comma> i \<tycolon> \<nat>['bits::len]\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> xs[i := y] \<tycolon> RefS['spc] X\<close>
  requires [intro]: "i < length xs"
  \<bullet> $v $y i \<Down>: \<Longleftarrow> AdrRefining_here
finish

proc i_store_here1[\<nu>overload "\<Down>"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<heavy_comma> y \<tycolon> X\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> Gi 0 \<left_fish_tail> y \<tycolon> Ref['spc] X\<close>
  for X :: "('a::{share,field},'b) nu"
  \<bullet> \<leftarrow> (v,y) \<Down>: \<Longleftarrow> AdrRefining_here
finish

subsubsection \<open>revert\<close>

definition op_revert_m :: " ('a,'a,'ax,'ax) address
      \<Rightarrow> ('ax::{field,share,sharing_identical}) \<times> ('bits::len) word \<times> ('spc::len0,('a::field)) memref \<times> ('r::stack)
      \<Rightarrow> (('spc,'a) memref \<times> 'r) state "
  where "op_revert_m path s = (case s of (y, i, Tuple (memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon adr' as), r) \<Rightarrow>
    if  adr' = adr then
      StatOn (Tuple (memptr (zp \<left_fish_tail> adr), z \<left_fish_tail> memcon adr (list_map_at (map_at path (share (Gi (-1)))) (unat i) as)), r)
    else STrap)"

theorem op_revert_m[\<nu>overload "\<down>:"]: "
  AdrRefining field_index Y X gt mp \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<nu>Share Y P sh \<Longrightarrow> \<nu>ShrIdentical Y sid
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P (gt (xs ! i)) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e sid (sh z (gt (xs ! i))) y
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_revert_m field_index \<blangle> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<heavy_comma> i \<tycolon> \<nat>['bits::len]\<heavy_comma> y \<tycolon> Y
    \<longmapsto> R\<heavy_comma> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> (list_map_at (mp (sh (Gi (-1)))) i xs) \<tycolon> RefS['spc] X\<brangle> "
  unfolding op_revert_m_def \<nu>def \<nu>Share_def AdrRefining_def \<nu>address_def  by
      (auto 4 4 simp add: lrep_exps list_all2_conv_all_nth nth_list_update)

proc i_revert1[\<nu>overload "\<down>:"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<heavy_comma> y \<tycolon> Y\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> mp (sh (Gi (-1))) x \<tycolon> Ref['spc] X\<close>
  for Y :: "('b::{share,field,sharing_identical},'c) nu"
  requires [\<nu>intro]: "AdrRefining field_index Y X gt mp" and [\<nu>intro]: "\<nu>Share Y P sh" and [\<nu>intro]: "\<nu>ShrIdentical Y sid"
    and [simp]: "P (gt x)" and [simp]: "sid (sh z (gt x)) y"
  \<bullet> \<leftarrow> v \<open>0 \<tycolon> \<nat>[32]\<close> \<leftarrow> y \<down>: 
finish

proc i_revert_here[\<nu>overload "\<down>"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] X\<heavy_comma> i \<tycolon> \<nat>['bits::len]\<heavy_comma> y \<tycolon> X\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> list_map_at (sh (Gi (-1))) i xs \<tycolon> RefS['spc] X\<close>
  for X :: "('a::{share,field,sharing_identical},'b) nu"
  requires [intro]: "i < length xs" and [\<nu>intro]: "\<nu>Share X P sh" and [\<nu>intro]: "\<nu>ShrIdentical X sid"
    and [simp]: "P (xs ! i)" and [simp]: "sid (sh z (xs ! i)) y"
  \<bullet> \<leftarrow> (v,i,y) \<down>: \<Longleftarrow> AdrRefining_here
finish

proc i_revert_here1[\<nu>overload "\<down>"]: \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc::len0] X\<heavy_comma> y \<tycolon> X\<close>
  \<longmapsto> \<open>zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> sh (Gi (-1)) x \<tycolon> Ref['spc] X\<close>
  for X :: "('a::{share,sharing_identical,field},'b) nu"
  requires [\<nu>intro]: "\<nu>Share X P sh" and [\<nu>intro]: "\<nu>ShrIdentical X sid"
    and [simp]: "P x" and [simp]: "sid (sh z x) y"
  \<bullet> \<leftarrow> (v,y) \<down>: \<Longleftarrow> AdrRefining_here
finish

  
end