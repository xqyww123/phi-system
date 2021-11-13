theory NuBasicAbstractors
  imports NuLLReps NuSys
  abbrevs "<some>" = "\<^bold>s\<^bold>o\<^bold>m\<^bold>e"
begin

\<nu>cast_overloads singular and plural

text \<open>Basic \<nu>-abstractors\<close>

(* text \<open>Examples for automatic property inference\<close>
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
*)
section \<open>Abstractors for specification\<close>

subsubsection \<open>Identity\<close>

definition Identity :: " ('a::lrep, 'a) \<nu> " where "Identity x = {x}"
lemma [simp]: "p \<nuLinkL> Identity \<nuLinkR> x \<longleftrightarrow> p = x" unfolding Refining_def Identity_def by auto

subsubsection \<open>Refinement\<close>

definition NuRefine :: " ('a, 'b) \<nu> \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) \<nu> " (infixl "\<nuRefine>" 80)
  where "(N \<nuRefine> T) x = {p. (x \<in> T \<and>(p \<nuLinkL> N \<nuLinkR> x))}"

notation NuRefine (infixl "<where>" 80)

lemma [simp]: " p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> ( p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def Refining_def by auto
lemma [elim,\<nu>elim]: " x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> S \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x \<tycolon> M <where> S"
  unfolding Intro_def Cast_def by auto
lemma [\<nu>intro]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M <where> S \<longmapsto> x \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h x \<in> S"
  unfolding Dest_def Cast_def by auto
lemma refine_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N <where> P)" unfolding Cast_def by auto

abbreviation AutoRefine (infixl "<auto-where>" 80)
  where "AutoRefine \<equiv> Auto NuRefine"
lemma [simp]:"\<tort_lbrace>x \<tycolon> Auto NuRefine T P \<tort_rbrace> = \<tort_lbrace> x \<tycolon> Auto NuAddition T (x \<in> P) \<tort_rbrace>"
  unfolding Auto_def by auto

(* lemma [\<nu>intro]: "(x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<and>x \<in> P" unfolding Cast_def by auto
lemma [\<nu>intro]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where> P \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q" unfolding Cast_def by auto
(* lemma [\<nu>cast_overload E]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P) \<longmapsto> x \<tycolon> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h x \<in> P" unfolding Cast_def by auto *)
*)
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e z \<in> S \<Longrightarrow> \<nu>Zero N z \<Longrightarrow> \<nu>Zero (N <where> S) z" unfolding \<nu>Zero_def Premise_def by simp
lemma "\<nu>Equal (N <where> P) can_eq eq \<longleftrightarrow> \<nu>Equal N (\<lambda>x y. x \<in> P \<and> y \<in> P \<and> can_eq x y) eq"
  unfolding \<nu>Equal_def by auto

(* definition SchemaCondition (infixl "<where''>" 80) where "SchemaCondition = NuRefine"
abbreviation WorkingSchemaCondition (infixl "<where''''>" 80) where "WorkingSchemaCondition \<equiv> WorkingProtector SchemaCondition"

lemma [simp]: "\<tort_lbrace>x \<tycolon> N <where'> P\<tort_rbrace> = (\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<addition> (x \<in> P))" unfolding SchemaCondition_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where> P \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where'> P \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q" unfolding SchemaCondition_def . 
lemma SchemaCondition_simp: "\<tort_lbrace> x \<tycolon> N <where'> P\<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P\<tort_rbrace>" unfolding SchemaCondition_def by auto
lemma refine'_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N <where''> P)" unfolding WorkingProtector_def Cast_def by auto
*)
subsubsection \<open>Down Lifting\<close>

definition DownLift :: "('a, 'b) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<nu>" (infixl "<down-lift>" 80)
  where "DownLift N g x = {p. ( p \<nuLinkL> N \<nuLinkR> g x)}"

lemma DownLift_exp[simp]: " p \<nuLinkL> N <down-lift> g \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> N \<nuLinkR> g x"
  unfolding DownLift_def Refining_def by simp
lemma [elim,\<nu>elim]: " x \<ratio> N <down-lift> g \<Longrightarrow> ( g x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by simp

(* lemma [\<nu>cast_overload E]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> g x \<tycolon> N" unfolding Cast_def by simp *)
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (g y = x) \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M <down-lift> g"
  unfolding Intro_def Cast_def by auto
lemma [\<nu>intro]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <down-lift> g \<longmapsto> g y \<tycolon> M"
  unfolding Dest_def Cast_def by auto

lemma [\<nu>intro]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <down-lift> g" unfolding Cast_def by auto
lemma "\<down>lift_\<nu>cast": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <down-lift> g" unfolding Cast_def by auto


abbreviation AutoDownLift (infixl "<auto-down-lift>" 80)
  where "AutoDownLift \<equiv> Auto DownLift"

lemma [simp]:"\<tort_lbrace>x \<tycolon> Auto DownLift T f \<tort_rbrace> = \<tort_lbrace> f x \<tycolon> T \<tort_rbrace>" unfolding Auto_def by auto

(* term image
lemma "\<nu>Equal (N <down-lift> g) can_eq eq \<longleftrightarrow> \<nu>Equal N (inv_imagep can_eq g) (inv_imagep eq g)"
  unfolding \<nu>Equal_def by auto *)

(* definition Schema (infixl "<schema>" 80) where "Schema = DownLift"
lemma i_schema_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <schema> g" unfolding Cast_def Schema_def by auto
lemma [simp]: "\<tort_lbrace> x \<tycolon> N <schema> id \<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<tort_rbrace>" and [simp]: "\<tort_lbrace> (a,b) \<tycolon> N <schema> f \<tort_rbrace> = \<tort_lbrace> f (a,b) \<tycolon> N \<tort_rbrace>" unfolding Schema_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> <Structural> g y = y1  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <schema> g"
  unfolding Schema_def Cast_def StructuralTag_def by auto *)

subsubsection \<open>Up Lifting\<close>

definition UpLift :: "(('a::lrep), 'c) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<nu>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> ( p \<nuLinkL> N \<nuLinkR> y))}"

lemma [simp]: " p \<nuLinkL> N <up-lift> f \<nuLinkR> x \<longleftrightarrow> (\<exists>y. (f y = x) \<and> (p \<nuLinkL> N \<nuLinkR> y))"
  unfolding UpLift_def Refining_def by auto
lemma [elim,\<nu>elim]: " x \<ratio> N <up-lift> f \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> y \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma [\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> g x \<tycolon> M <up-lift> g"
  unfolding Intro_def Cast_def by auto
lemma [\<nu>intro]: "(\<And> x.  (g x = y) \<Longrightarrow> \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<Longrightarrow> \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Dest_def Cast_def by auto

lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> (\<exists>* x. x \<tycolon> M \<and>\<^sup>\<nu> (g x = y))"
  unfolding Dest_def Cast_def by auto

lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> f x \<tycolon> N <up-lift> f" unfolding Cast_def by auto
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> f x \<tycolon> N <up-lift> f" unfolding Cast_def by auto

lemma "\<nu>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<nu>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<nu>Equal_def by (auto 0 6)

subsubsection \<open>Operator Some\<close>
(*
definition NuSome :: " ('a :: lrep, 'b) \<nu> \<Rightarrow> ('a :: lrep, 'b set) \<nu> " ("<some>")
  where "NuSome N h p S = (\<exists>x. x \<in> S \<and> ([h] p \<nuLinkL> N \<nuLinkR> x))"
notation NuSome ("\<^bold>s\<^bold>o\<^bold>m\<^bold>e")

lemma [simp]: "[h] p \<nuLinkL> \<^bold>s\<^bold>o\<^bold>m\<^bold>e N \<nuLinkR> X \<longleftrightarrow> (\<exists>x. x \<in> X \<and> ([h] p \<nuLinkL> N \<nuLinkR> x))" unfolding NuSome_def Refining_def Nu_def by auto
lemma [elim,\<nu>elim]: "[h] X \<ratio> ( \<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> [h] x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X \<subseteq> X' \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> X' \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by (auto 2 3)
lemma [\<nu>intro]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> Y \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e M) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Cast_def by auto
lemma someI_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> X \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by auto
lemma someE_\<nu>cast[\<nu>cast_overload E]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> (\<exists>*some. \<tort_lbrace>some \<tycolon> N \<tort_rbrace> \<addition> (some \<in> X))" unfolding Cast_def by auto

subsubsection \<open>AutoSome and AutoExTy\<close>

definition SchemaSome :: " ('a :: lrep, 'b) \<nu> \<Rightarrow> ('a :: lrep, 'b set) \<nu> " ("<some''>") where "SchemaSome = NuSome"

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> <some'> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding SchemaSome_def .
lemma [simp]: "\<tort_lbrace> s \<tycolon> <some'> N \<tort_rbrace> = (\<exists>* x. \<tort_lbrace> x \<tycolon> N \<tort_rbrace> \<addition> (x \<in> s))" unfolding SchemaSome_def by (rule ext) auto


lemma
  assumes A: "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> s \<tycolon> <some'> N)"
  shows SchemaSome_ex: "\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> x \<tycolon> N) \<addition> (x \<in> s)"
proof -
  have t1: "\<tort_lbrace> s \<tycolon> <some'> N \<tort_rbrace> = (\<exists>*x. \<tort_lbrace> x \<tycolon> N \<tort_rbrace> \<addition> (x \<in> s))" unfolding SchemaSome_def by (rule ext) auto
  show ?thesis using A[simplified t1, simplified, simplified ExTyp_strip] .
qed
*)
subsection \<open>\<nu>-abstraction : DeepModel\<close>

definition DeepModel :: "('a::lrep, 'b) \<nu> \<Rightarrow> (deep_model, 'b) \<nu>"
  where "DeepModel T x = {p. shallowize p \<nuLinkL> T \<nuLinkR> x}"

lemma [simp]: "deepize p \<nuLinkL> DeepModel T \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> T \<nuLinkR> x" unfolding DeepModel_def Refining_def by simp

subsection \<open>\<nu>-abstraction : Ref\<close>

definition Ref  :: "('a::lrep, 'b) \<nu> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b) \<nu>"
  where "Ref T xx = {heap. (case xx of addr \<R_arr_tail> x \<Rightarrow> heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T)}"

lemma [simp]: "heap \<nuLinkL> Ref T \<nuLinkR> addr \<R_arr_tail> x \<longleftrightarrow> (heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T)"
  by (auto simp add: lrep_exps Ref_def Refining_def)
lemma [elim]: " addr \<R_arr_tail> x \<ratio> Ref T \<Longrightarrow> (x \<ratio> T \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (auto simp add: MemAddrState_def)

subsection \<open>\<nu>-abstraction : Array'\<close>

definition Array' :: "('a::field, 'b) \<nu> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b option list) \<nu>"
  where "Array' N x' = {heap. (case x' of (base |+ ofs) \<R_arr_tail> xs \<Rightarrow>
    (\<forall>i < length xs. pred_option (\<lambda>x. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s x \<tycolon> N) (xs ! i)) \<and>
    ofs + length xs \<le> segment_len base \<and> segment_llty base = LLTY('a))}"

lemma [simp]: "heap \<nuLinkL> Array' N \<nuLinkR> (base |+ ofs) \<R_arr_tail> xs \<longleftrightarrow>
    (ofs + length xs \<le> segment_len base \<and>
    segment_llty base = LLTY('a) \<and>
    (\<forall>i < length xs. pred_option (\<lambda>x. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s x \<tycolon> N) (xs ! i))
)" for N :: "('a::field, 'b) \<nu>"
  by (auto simp add: lrep_exps Array'_def Refining_def)

lemma [elim,\<nu>elim]: "a \<R_arr_tail> xs \<ratio> Array' N \<Longrightarrow> (
    (\<And>i. i < length xs \<Longrightarrow> pred_option (\<lambda>x. x \<ratio> N) (xs ! i)) \<Longrightarrow> offset_of a + length xs \<le> address_len a \<Longrightarrow> address_llty a = LLTY('a)
  \<Longrightarrow> C) \<Longrightarrow> C"
   for N :: "('a::field, 'b) \<nu>"
  unfolding Inhabited_def[of "\<tort_lbrace>a \<R_arr_tail> xs \<tycolon> Array' N\<tort_rbrace>"]
  by (cases a) (auto simp add: lrep_exps pred_option_def list_all2_conv_all_nth)

lemma Array'_to_Ref_\<nu>proc[\<nu>intro]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! i) \<noteq> None \<Longrightarrow>
  \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> (a ||+ i) \<R_arr_tail> the (xs ! i) \<tycolon> Ref N"
  unfolding Dest_def Cast_def Heap_Delimiter_def
  apply (cases a) apply auto apply (rule heap_split_by_addr_set[of _  _ "-{a ||+ i}"])
  by (auto simp add: pred_option_def Ball_def nth_list_update)

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow>
  \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> (a ||+ i) \<R_arr_tail> y \<tycolon> Ref N \<longmapsto> a \<R_arr_tail> xs[i := Some y] \<tycolon> Array' N"
  unfolding Intro_def Cast_def Heap_Delimiter_def
  apply (cases a) apply (auto simp add: pred_option_def Ball_def)
  by (metis MemAddrState_add_I1 MemAddrState_add_I2 nth_list_update option.sel)

(* lemma Array'_dual_Ref_\<nu>proc [\<nu>intro]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! i) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> the (xs ! i) \<tycolon> Ref N \<medium_right_bracket>
  \<^bold>d\<^bold>u\<^bold>a\<^bold>l a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> y \<tycolon> Ref N \<medium_right_bracket> \<longmapsto> a \<R_arr_tail> xs[i := Some y] \<tycolon> Array' N"
  unfolding CastDual_def Heap_Cast_Goal_def apply (simp add: Array'_to_Ref_\<nu>proc)
  unfolding Cast_def apply (cases a) apply (auto simp add: pred_option_def Ball_def)
  by (metis MemAddrState_add_I1 MemAddrState_add_I2 nth_list_update option.sel)
*)


subsection \<open>\<nu>-abstraction : Array\<close>

definition Array :: "('a::field, 'b) \<nu> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b list) \<nu>"
  where "Array N = Array' N <down-lift> (map_object id (map Some)) "

(* lemma [simp]: "heap \<nuLinkL> Array N \<nuLinkR> (base |+ ofs) \<R_arr_tail> xs \<longleftrightarrow>
    (ofs + length xs \<le> segment_len base \<and>
    segment_llty base = LLTY('a) \<and>
    (\<forall>i < length xs. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s xs ! i \<tycolon> N)
)" for N :: "('a::field, 'b) \<nu>"
  by (auto simp add: lrep_exps Array_def) *)
  
lemma [elim,\<nu>elim]: "a \<R_arr_tail> xs \<ratio> Array N \<Longrightarrow> (
    (\<And>i. i < length xs \<Longrightarrow> xs ! i \<ratio> N) \<Longrightarrow> offset_of a + length xs \<le> address_len a \<Longrightarrow> address_llty a = LLTY('a)
  \<Longrightarrow> C) \<Longrightarrow> C"
   for N :: "('a::field, 'b) \<nu>"
  unfolding Inhabited_def[of "\<tort_lbrace>a \<R_arr_tail> xs \<tycolon> Array N\<tort_rbrace>"]
  unfolding Array_def
  by (cases a) (auto simp add: lrep_exps list_all2_conv_all_nth)

lemma [THEN cast_trans, simplified, \<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> map Some xs \<tycolon> Array' N"
  unfolding Cast_def Array_def by (cases a) auto

definition mapSome :: " 'a list \<Rightarrow> 'a option list " where "mapSome = map Some"
lemma [simp]: "length (mapSome l) = length l" unfolding mapSome_def by auto
lemma [simp]: "i < length l \<Longrightarrow> mapSome l ! i = Some (l ! i)" unfolding mapSome_def by auto
lemma [simp]: "i < length l \<Longrightarrow> (mapSome l) [i := Some v] = mapSome (l [i:=v])" unfolding mapSome_def by (metis map_update)
lemma [simp]: "i < length l \<Longrightarrow> the (mapSome l ! i) = l ! i" unfolding mapSome_def by auto


lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs' = mapSome xs2 \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t  a \<R_arr_tail> xs' \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N"
  unfolding Cast_def Intro_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def)
lemma [\<nu>intro]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> mapSome xs \<tycolon> Array' N"
  unfolding Cast_def Dest_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def)


(* lemma [THEN cast_dual_trans, \<nu>intro]: 
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> mapSome xs \<tycolon> Array' N
  \<^bold>d\<^bold>u\<^bold>a\<^bold>l a \<R_arr_tail> xs' \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N \<^bold>w\<^bold>h\<^bold>e\<^bold>n xs' = mapSome xs2"
  unfolding Cast_def CastDual_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def) *)


subsection \<open>Numbers\<close>

\<nu>cast_overloads nat and int

lemma unat_nat: assumes a0:"0 < x" and a1:"sint (xa::('a::len) word) = x"
  shows "unat xa = nat x"
proof-
  have a00:"0 < sint xa"
    by (simp add: a0 a1)
  then have "bit xa (LENGTH('a) - Suc 0)  = False"
    using bit_last_iff by force  
  moreover have "signed_take_bit (LENGTH('a) - Suc 0) xa = xa"
    by (metis scast_id signed_scast_eq) 
  moreover have "sint xa =  signed_take_bit (LENGTH('a) - Suc 0) (uint xa)"using sint_uint by auto
  ultimately have "uint xa = sint xa"
    using bit_uint_iff signed_take_bit_eq_if_positive uint_take_bit_eq 
    by metis 
  then show ?thesis using a0 a1 by auto
qed
  

lemma [\<nu>cast_overload nat]: 
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> \<int>['bits::len] \<longmapsto> nat x \<tycolon> \<nat>['bits]"
  unfolding Cast_def Premise_def apply (simp add: lrep_exps) using unat_nat  by auto

lemma sint_int: assumes a0:"x < 2 ^ (LENGTH('bits::len) - Suc 0)" and a1:"unat (xa::'bits word) = x"
  shows "sint xa = int x"
proof-
  have a00:"unat xa <  2 ^ (LENGTH('bits) - Suc 0)"
    by (simp add: a0 a1)  
  then have "bit xa (LENGTH('bits) - Suc 0)  = False"
    apply transfer apply auto  
    by (metis bit_take_bit_iff decr_length_less_iff linorder_not_le 
        order_less_irrefl take_bit_int_eq_self_iff take_bit_nonnegative) 
  moreover have "sint xa =  signed_take_bit (LENGTH('bits) - Suc 0) (uint xa)"using sint_uint by auto
  ultimately have "uint xa = sint xa"
    using bit_uint_iff signed_take_bit_eq_if_positive uint_take_bit_eq 
    by (metis scast_id signed_of_int  word_of_int_uint)     
  then show ?thesis using a0 a1 by auto
qed

lemma [\<nu>cast_overload int]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^(LENGTH('bits) - 1) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> \<nat>['bits::len] \<longmapsto> int x \<tycolon> \<int>['bits]"
  unfolding Cast_def Premise_def apply (simp add: lrep_exps) using sint_int by auto

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


end

