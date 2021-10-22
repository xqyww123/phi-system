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

definition Identity :: " ('a::lrep, 'a) \<nu> " where "Identity h p x \<longleftrightarrow> p = x"
lemma [simp]: "[h] p \<nuLinkL> Identity \<nuLinkR> x \<longleftrightarrow> p = x" unfolding Refining_ex Identity_def Nu_def by auto

subsubsection \<open>Refinement\<close>

definition NuRefine :: " ('a :: lrep, 'b) \<nu> \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) \<nu> " (infixl "\<nuRefine>" 80)
  where "(N \<nuRefine> T) heap p x = (x \<in> T \<and>([heap] p \<nuLinkL> N \<nuLinkR> x))"

notation NuRefine (infixl "<where>" 80) and NuRefine (infixl "\<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e" 80)

lemma [simp]: "[h] p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> ([h] p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def Refining_ex Nu_def by auto
lemma [elim,\<nu>elim]: "[h] x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> [h] x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "(x \<in> P \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q) \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<and>x \<in> P" unfolding Cast_def by auto
lemma [\<nu>intro]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> P \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where> P \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q" unfolding Cast_def by auto
lemma [\<nu>cast_overload E]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P) \<longmapsto> x \<tycolon> N \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e x \<in> P" unfolding Cast_def by auto
lemma refine_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P)" unfolding Cast_def by auto

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e z \<in> S \<Longrightarrow> \<nu>Zero N z \<Longrightarrow> \<nu>Zero (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S) z" unfolding \<nu>Zero_def Premise_def by simp
lemma "\<nu>Equal (N <where> P) can_eq eq \<longleftrightarrow> \<nu>Equal N (\<lambda>x y. x \<in> P \<and> y \<in> P \<and> can_eq x y) eq"
  unfolding \<nu>Equal_def by auto

definition SchemaCondition (infixl "<where''>" 80) where "SchemaCondition = NuRefine"
abbreviation WorkingSchemaCondition (infixl "<where''''>" 80) where "WorkingSchemaCondition \<equiv> WorkingProtector SchemaCondition"

lemma [simp]: "\<tort_lbrace>x \<tycolon> N <where'> P\<tort_rbrace> = (\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<addition> (x \<in> P))" unfolding SchemaCondition_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where> P \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where'> P \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q" unfolding SchemaCondition_def . 
lemma SchemaCondition_simp: "\<tort_lbrace> x \<tycolon> N <where'> P\<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P\<tort_rbrace>" unfolding SchemaCondition_def by auto
lemma refine'_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N <where''> P)" unfolding WorkingProtector_def Cast_def by auto

subsubsection \<open>Down Lifting\<close>

definition DownLift :: "(('a::lrep), 'b) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<nu>" (infixl "<down-lift>" 80)
  where "DownLift N g heap p x = ([heap] p \<nuLinkL> N \<nuLinkR> g x)"

lemma DownLift_exp[simp]: "[h] p \<nuLinkL> N <down-lift> g \<nuLinkR> x \<longleftrightarrow> [h] p \<nuLinkL> N \<nuLinkR> g x"
  unfolding DownLift_def Refining_ex Nu_def by simp
lemma [elim,\<nu>elim]: "[h] x \<ratio> N <down-lift> g \<Longrightarrow> ([h] g x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by simp

lemma [\<nu>cast_overload E]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> g x \<tycolon> N" unfolding Cast_def by simp
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma [\<nu>intro]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <down-lift> g" unfolding Cast_def by auto
lemma "\<down>lift_\<nu>cast": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <down-lift> g" unfolding Cast_def by auto

(* term image
lemma "\<nu>Equal (N <down-lift> g) can_eq eq \<longleftrightarrow> \<nu>Equal N (inv_imagep can_eq g) (inv_imagep eq g)"
  unfolding \<nu>Equal_def by auto *)

definition Schema (infixl "<schema>" 80) where "Schema = DownLift"
lemma i_schema_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <schema> g" unfolding Cast_def Schema_def by auto
lemma [simp]: "\<tort_lbrace> x \<tycolon> N <schema> id \<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<tort_rbrace>" and [simp]: "\<tort_lbrace> (a,b) \<tycolon> N <schema> f \<tort_rbrace> = \<tort_lbrace> f (a,b) \<tycolon> N \<tort_rbrace>" unfolding Schema_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> <Structural> g y = y1  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <schema> g"
  unfolding Schema_def Cast_def StructuralTag_def by auto

subsubsection \<open>Up Lifting\<close>

definition UpLift :: "(('a::lrep), 'c) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<nu>" (infixl "<up-lift>" 80)
  where "UpLift N f h p x = (\<exists>y. f y = x \<and> ([h] p \<nuLinkL> N \<nuLinkR> y))"

lemma [simp]: "[h] p \<nuLinkL> N <up-lift> f \<nuLinkR> x \<longleftrightarrow> (\<exists>y. (f y = x) \<and> ([h] p \<nuLinkL> N \<nuLinkR> y))"
  unfolding UpLift_def Refining_ex Nu_def by auto
lemma [elim,\<nu>elim]: "[h] x \<ratio> N <up-lift> f \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> [h] y \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma "\<nu>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<nu>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<nu>Equal_def by (auto 0 6)

subsubsection \<open>Operator Some\<close>

definition NuSome :: " ('a :: lrep, 'b) \<nu> \<Rightarrow> ('a :: lrep, 'b set) \<nu> " ("<some>")
  where "NuSome N h p S = (\<exists>x. x \<in> S \<and> ([h] p \<nuLinkL> N \<nuLinkR> x))"
notation NuSome ("\<^bold>s\<^bold>o\<^bold>m\<^bold>e")

lemma [simp]: "[h] p \<nuLinkL> \<^bold>s\<^bold>o\<^bold>m\<^bold>e N \<nuLinkR> X \<longleftrightarrow> (\<exists>x. x \<in> X \<and> ([h] p \<nuLinkL> N \<nuLinkR> x))" unfolding NuSome_def Refining_ex Nu_def by auto
lemma [elim,\<nu>elim]: "[h] X \<ratio> ( \<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> [h] x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X \<subseteq> X' \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> X' \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by (auto 2 3)
lemma [\<nu>intro]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> Y \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e M) \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" unfolding Cast_def by auto
lemma someI_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> X \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by auto
lemma someE_\<nu>cast[\<nu>cast_overload E]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> (\<exists>*some. \<tort_lbrace>some \<tycolon> N \<tort_rbrace> \<addition> (some \<in> X))" unfolding Cast_def by auto

subsubsection \<open>AutoSome and AutoExTy\<close>

definition SchemaSome :: " ('a :: lrep, 'b) \<nu> \<Rightarrow> ('a :: lrep, 'b set) \<nu> " ("<some''>") where "SchemaSome = NuSome"

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> <some'> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
  unfolding SchemaSome_def .
lemma [simp]: "\<tort_lbrace> s \<tycolon> <some'> N \<tort_rbrace> = (\<exists>* x. \<tort_lbrace> x \<tycolon> N \<tort_rbrace> \<addition> (x \<in> s))" unfolding SchemaSome_def by (rule ext) auto


lemma
  assumes A: "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> s \<tycolon> <some'> N)"
  shows SchemaSome_ex: "\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> x \<tycolon> N) \<addition> (x \<in> s)"
proof -
  have t1: "\<tort_lbrace> s \<tycolon> <some'> N \<tort_rbrace> = (\<exists>*x. \<tort_lbrace> x \<tycolon> N \<tort_rbrace> \<addition> (x \<in> s))" unfolding SchemaSome_def by (rule ext) auto
  show ?thesis using A[simplified t1, simplified, simplified ExTyp_strip] .
qed

subsection \<open>\<nu>-abstraction : DeepModel\<close>

definition DeepModel :: "('a::lrep, 'b) \<nu> \<Rightarrow> (deep_model, 'b) \<nu>"
  where "DeepModel T h p x \<longleftrightarrow> [h] shallowize p \<nuLinkL> T \<nuLinkR> x"

lemma [simp]: "[h] deepize p \<nuLinkL> DeepModel T \<nuLinkR> x \<longleftrightarrow> [h] p \<nuLinkL> T \<nuLinkR> x" unfolding DeepModel_def Refining_ex Nu_def by auto

subsection \<open>\<nu>-abstraction : Ref\<close>

definition Ref  :: "('a::lrep, 'b) \<nu> \<Rightarrow> ('spc::len0 memptr, nat memaddr \<R_arr_tail> 'b) \<nu>"
  where "Ref T heap p x \<longleftrightarrow> (case x of adr \<R_arr_tail> xx \<Rightarrow> ([heap] p \<nuLinkL> Pointer \<nuLinkR> adr) \<and>
    (\<exists>v. heap (MemAddress adr) = Some v \<and> ([heap] shallowize v \<nuLinkL> T \<nuLinkR> xx)))"

lemma [simp]: "Nu (Ref T)" unfolding Nu_def Ref_def by (auto simp add: lrep_exps)
lemma [simp]:
  "[heap] addrp \<nuLinkL> Ref T \<nuLinkR> addr \<R_arr_tail> x \<longleftrightarrow>
    ([heap] addrp \<nuLinkL> Pointer \<nuLinkR> addr) \<and> (\<exists>v. heap (MemAddress addr) = Some v \<and> ([heap] shallowize v \<nuLinkL> T \<nuLinkR> x))"
  by (auto simp add: lrep_exps Ref_def Refining_ex)
lemma [\<nu>intro]: "\<nu>Resources T rcss \<Longrightarrow> \<nu>Resources (Ref T) (\<lambda>x. total (key_of x) \<union> rcss (val_of x))"
  unfolding \<nu>def by (auto simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Equal (Ref N) (\<lambda>x y. True) (inv_imagep (=) key_of)"
  unfolding \<nu>Equal_def  using raw_offset_of_inj by (auto simp add: lrep_exps same_addr_offset_def addr'_allocated_def)

subsection \<open>\<nu>-abstraction : Slice\<close>


definition Slice :: "('a::field, 'b) \<nu> \<Rightarrow> ('spc::len0 memptr, nat memaddr \<R_arr_tail> 'b list) \<nu>"
  where "Slice N heap p x' = (case x' of (base |+ ofs) \<R_arr_tail> xs \<Rightarrow> case p of memptr addrp \<Rightarrow>
        (the_same_addr addrp (base |+ ofs)) \<and>
        ofs + length xs \<le> segment_len base \<and>
        segment_llty base = LLTY('a) \<and>
        (\<forall>i < length xs. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s xs ! i \<tycolon> N) \<and>
        (\<forall>i \<le> segment_len base. allocated heap (base |+ i)) \<and>
        (\<forall>i < length xs. \<nu>Independent \<tort_lbrace>xs ! i \<tycolon> N\<tort_rbrace>  (write base))
    )"
abbreviation "Slice_explicit_ty" :: "'spc::len itself \<Rightarrow> ('a::field, 'b) \<nu> \<Rightarrow> ('spc::len memptr, nat memaddr \<R_arr_tail> 'b list) \<nu>"
  where "Slice_explicit_ty _ \<equiv> Slice"
syntax "_Slice_explicit_ty_" :: "type \<Rightarrow> logic" ("Slice[_]")
translations "Slice['ty]"  == "CONST Slice_explicit_ty TYPE('ty)"

lemma [simp]: "Nu (Slice N)" unfolding Nu_def Slice_def  by (auto simp add: lrep_exps)
  
lemma [simp]: "[heap] memptr p \<nuLinkL> Slice N \<nuLinkR> (base |+ ofs) \<R_arr_tail> xs \<longleftrightarrow>
    (the_same_addr p (base |+ ofs)) \<and> 
    ofs + length xs \<le> segment_len base \<and>
    segment_llty base = LLTY('a) \<and>
    (\<forall>i < length xs. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s xs ! i \<tycolon> N) \<and>
    (\<forall>i \<le> segment_len base. allocated heap (base |+ i)) \<and>
    (\<forall>i < length xs. \<nu>Independent \<tort_lbrace>xs ! i \<tycolon> N\<tort_rbrace>  (write base)
)" for N :: "('a::field, 'b) \<nu>"
  by (auto simp add: lrep_exps Slice_def Refining_ex)


lemma [elim,\<nu>elim]: "[h] a \<R_arr_tail> xs \<ratio> Slice N \<Longrightarrow> (
    (\<And>i. i < length xs \<Longrightarrow> ([h] xs ! i \<ratio> N) \<and> (h \<^bold>a\<^bold>t a ||+ i \<^bold>i\<^bold>s xs ! i \<tycolon> N) \<and> \<nu>Independent \<tort_lbrace>xs ! i \<tycolon> N\<tort_rbrace> (write (segment_of_addr a)))
     \<Longrightarrow> (\<And>i. i \<le> length xs \<Longrightarrow> allocated h (segment_of_addr a |+ i))
  \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (cases a) (auto simp add: lrep_exps list_all2_conv_all_nth)
thm addr'_allocated_def
lemma [\<nu>intro]: "\<nu>Equal (Slice N) (\<lambda>x y. True) (inv_imagep (=) key_of)"
  unfolding \<nu>Equal_def using raw_offset_of_inj
  by (auto simp add: lrep_exps addr'_allocated_def same_addr_offset_inj same_addr_offset_inj2)  

lemma [\<nu>intro]: "alive (segment_of_addr addr) \<perpendicular> claim \<Longrightarrow> write (array addr (length xs)) \<perpendicular> claim \<Longrightarrow>
  \<forall>i < length xs. \<nu>Independent \<tort_lbrace>xs ! i \<tycolon> T\<tort_rbrace> claim \<Longrightarrow> \<nu>Independent \<tort_lbrace> addr \<R_arr_tail> xs \<tycolon> Slice T \<tort_rbrace> claim"
  apply (cases addr, rule \<nu>Independent_I) by (auto 0 0 simp add: lrep_exps) blast+


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

lemma [\<nu>cast_overload int]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^(LENGTH('bits) - 1) \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> \<nat>['bits::len] \<longmapsto> int x \<tycolon> \<int>['bits]"
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

