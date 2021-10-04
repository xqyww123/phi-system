theory NuBasicAbstractors
  imports NuLLReps NuSys
  abbrevs "<where>" = "\<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e"
    and "<some>" = "\<^bold>s\<^bold>o\<^bold>m\<^bold>e"
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

subsubsection \<open>Refinement\<close>

definition NuRefine :: " ('a :: lrep, 'b) nu \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) nu " (infixl "\<nuRefine>" 80) where "(N \<nuRefine> T) p x = (x \<in> T \<and>(p \<nuLinkL> N \<nuLinkR> x))"

notation NuRefine (infixl "<where>" 80) and NuRefine (infixl "\<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e" 80)

lemma [simp]: "p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> (p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def Refining_ex by auto
lemma [elim,\<nu>elim]: "x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "(x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<and>x \<in> P" unfolding Cast_def by auto
lemma [\<nu>cast_overload E]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P) \<longmapsto> x \<tycolon> N \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e x \<in> P" unfolding Cast_def by auto
lemma where_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P)" unfolding Cast_def by auto

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<forall>x. P' x \<longrightarrow> P x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<forall>x z. P' x \<and> x \<in> S \<and> (x \<ratio> N) \<longrightarrow> s z x \<in> S \<Longrightarrow> \<nu>Share N P s \<Longrightarrow> \<nu>Share (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S) P' s"
  unfolding \<nu>Share_def by (auto 0 3)
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<forall>x. x \<in> S \<and> (x \<ratio> N) \<longrightarrow> dp x \<in> S \<Longrightarrow> \<nu>Deprive N dp \<Longrightarrow> \<nu>Deprive (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S) dp"
  unfolding \<nu>Deprive_def by (auto 0 3)
lemma [\<nu>intro]: "\<nu>CEqual N P eq \<Longrightarrow> \<nu>CEqual (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S) P eq" unfolding \<nu>CEqual_def by auto
lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>Ownership (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S) ow" unfolding \<nu>Ownership_def by simp
lemma [\<nu>intro]: "\<nu>ShrIdentical N sid \<Longrightarrow> \<nu>ShrIdentical (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S) sid" unfolding \<nu>ShrIdentical_def by auto
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S)\<tort_rbrace>" unfolding \<nu>Disposable_def by simp
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e z \<in> S \<Longrightarrow> \<nu>Zero N z \<Longrightarrow> \<nu>Zero (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e S) z" unfolding \<nu>Zero_def Premise_def by simp

definition SchemaCondition (infixl "<where''>" 80) where "SchemaCondition = NuRefine"

lemma [simp]: "\<tort_lbrace>x \<tycolon> N <where'> P\<tort_rbrace> = (\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<addition> (x \<in> P))" unfolding SchemaCondition_def by auto
lemma SchemaCondition_simp: "\<tort_lbrace> x \<tycolon> N <where'> P\<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P\<tort_rbrace>" unfolding SchemaCondition_def by auto

subsubsection \<open>Down Lifting\<close>

definition DownLift :: "(('a::lrep), 'b) nu \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) nu" (infixl "<down-lift>" 80)
  where "DownLift N g p x = (p \<nuLinkL> N \<nuLinkR> g x)"

lemma DownLift_exp[simp]: "p \<nuLinkL> N <down-lift> g \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> N \<nuLinkR> g x" unfolding DownLift_def Refining_ex by simp
lemma [elim,\<nu>elim]: "x \<ratio> N <down-lift> g \<Longrightarrow> (g x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by simp

lemma [\<nu>cast_overload E]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> g x \<tycolon> N" unfolding Cast_def by simp
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <down-lift> g" unfolding Cast_def by auto
lemma "\<down>lift_\<nu>cast": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <down-lift> g" unfolding Cast_def by auto

definition Schema (infixl "<schema>" 80) where "Schema = DownLift"
lemma i_schema_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <schema> g" unfolding Cast_def Schema_def by auto
lemma [simp]: "\<tort_lbrace> x \<tycolon> N <schema> id \<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<tort_rbrace>" and [simp]: "\<tort_lbrace> (a,b) \<tycolon> N <schema> f \<tort_rbrace> = \<tort_lbrace> f (a,b) \<tycolon> N \<tort_rbrace>" unfolding Schema_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <schema> g"
  unfolding Schema_def Cast_def by auto

subsubsection \<open>Up Lifting\<close>

definition UpLift :: "(('a::lrep), 'c) nu \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) nu" (infixl "<up-lift>" 80)
  where "UpLift N f p x = (\<exists>y. f y = x \<and> (p \<nuLinkL> N \<nuLinkR> y))"

lemma [simp]: "p \<nuLinkL> N <up-lift> f \<nuLinkR> x \<longleftrightarrow> (\<exists>y. (f y = x) \<and> (p \<nuLinkL> N \<nuLinkR> y))" unfolding UpLift_def Refining_ex by simp
lemma [elim,\<nu>elim]: "x \<ratio> N <up-lift> f \<Longrightarrow> (\<And>y. y \<ratio> N \<Longrightarrow> f y = x \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

subsubsection \<open>Operator Some\<close>

definition NuSome :: " ('a :: lrep, 'b) nu \<Rightarrow> ('a :: lrep, 'b set) nu " ("<some>")
  where "NuSome N p S = (\<exists>x. x \<in> S \<and> (p \<nuLinkL> N \<nuLinkR> x))"
notation NuSome ("\<^bold>s\<^bold>o\<^bold>m\<^bold>e")

lemma [simp]: "p \<nuLinkL> \<^bold>s\<^bold>o\<^bold>m\<^bold>e N \<nuLinkR> X \<longleftrightarrow> (\<exists>x. x \<in> X \<and> (p \<nuLinkL> N \<nuLinkR> x))" unfolding NuSome_def Refining_ex by auto
lemma [elim,\<nu>elim]: "X \<ratio> ( \<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X \<subseteq> X' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> X' \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by (auto 2 3)
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> Y \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e M) \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" unfolding Cast_def by auto
lemma someI_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> X \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by auto
lemma someE_\<nu>cast[\<nu>cast_overload E]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> (\<exists>*some. \<tort_lbrace>some \<tycolon> N \<tort_rbrace> \<addition> (some \<in> X))" unfolding Cast_def by auto

subsubsection \<open>MemObj\<close>

definition "MemObj N = MemSlice N <down-lift> (\<lambda>x. case x of z \<left_fish_tail> a \<R_arr_tail> x \<Rightarrow> z \<left_fish_tail> a \<R_arr_tail> [x] | \<down_fish_tail> \<Rightarrow> \<down_fish_tail>)"

lemma [simp]: "p \<nuLinkL> MemObj N \<nuLinkR> z \<left_fish_tail> a \<R_arr_tail> x \<longleftrightarrow> p \<nuLinkL> MemSlice N \<nuLinkR> z \<left_fish_tail> a \<R_arr_tail> [x]"
  and [simp]: "p \<nuLinkL> MemObj N \<nuLinkR> \<down_fish_tail> \<longleftrightarrow> p \<nuLinkL> MemSlice N \<nuLinkR> \<down_fish_tail>"
  unfolding MemObj_def by auto

lemma [\<nu>intro]: "\<nu>Share (MemObj N) (\<lambda>x. True) share"
  unfolding \<nu>Share_def by (simp add: owning_forall memcon_forall memptr_forall object_forall)
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>\<down_fish_tail> \<tycolon> MemObj N\<tort_rbrace>" unfolding \<nu>Disposable_def by simp
lemma [\<nu>intro]: "\<nu>CEqual (MemObj N) (\<lambda>x y. True) (\<lambda>x y. True)" unfolding \<nu>CEqual_def by simp
lemma [\<nu>intro]: "\<nu>Ownership (MemObj N) ownership"
  unfolding \<nu>Ownership_def by (simp add: owning_forall memcon_forall memptr_forall object_exists)
lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>ShrIdentical (MemObj N) (rel_owning (rel_object (inv_imagep (=) ow)))"
  unfolding \<nu>Ownership_def \<nu>ShrIdentical_def
  by (simp add: lrep_exps list_all2_conv_all_nth) auto
lemma [\<nu>intro]: "\<nu>Zero (MemObj N) \<down_fish_tail>" unfolding \<nu>Zero_def by simp

lemma [\<nu>intro, \<nu>cast_overload singular]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t z \<left_fish_tail> a \<R_arr_tail> [x] \<tycolon> MemSlice N \<longmapsto> z \<left_fish_tail> a \<R_arr_tail> x \<tycolon> MemObj N" unfolding Cast_def by simp
lemma [\<nu>intro, \<nu>cast_overload plural]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t z \<left_fish_tail> a \<R_arr_tail> x \<tycolon> MemObj N \<longmapsto> z \<left_fish_tail> a \<R_arr_tail> [x] \<tycolon> MemSlice N" unfolding Cast_def by simp

subsubsection \<open>Slice Reference\<close>

type_synonym ('spc,'x) memref = "('spc memptr \<times> 'x memobj) tuple"

abbreviation "address_of_ref x \<equiv> (case x of _ \<left_fish_tail> a \<R_arr_tail> _ \<Rightarrow> a)"

definition "RefS' spc N = \<lbrace> Pointer' spc (llty (TYPE('b))) \<nuFusion> MemSlice N \<rbrace>
  <down-lift> (\<lambda>x. case x of (zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x) \<Rightarrow> (zp \<left_fish_tail> a, z \<left_fish_tail> a \<R_arr_tail> x) | (zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail>) \<Rightarrow> (zp \<left_fish_tail> a, \<down_fish_tail>) | \<down_fish_tail> \<Rightarrow> (\<down_fish_tail>,\<down_fish_tail>))"
  for N :: "('b::field, 'c) nu"
syntax "_RefS'_" :: "type => logic" ("RefS'[_']")
translations "RefS['spc]" == "CONST RefS' (TYPE('spc))"
abbreviation "RefS \<equiv> RefS[0]"

lemma [simp]: "p \<nuLinkL> RefS['spc::len0] N \<nuLinkR> (zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x) \<longleftrightarrow>
    (p \<nuLinkL> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace> \<nuLinkR> (zp \<left_fish_tail> a, z \<left_fish_tail> a \<R_arr_tail> x))"
  and [simp]: "p \<nuLinkL> RefS['spc] N \<nuLinkR> (zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail>) \<longleftrightarrow>
    (p \<nuLinkL> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace> \<nuLinkR> (zp \<left_fish_tail> a, \<down_fish_tail>))"
  and [simp]: "p \<nuLinkL> RefS['spc] N \<nuLinkR> \<down_fish_tail> \<longleftrightarrow> p \<nuLinkL> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace> \<nuLinkR> (\<down_fish_tail>, \<down_fish_tail>)"
  for N :: "('b::field, 'c) nu"
  unfolding RefS'_def by simp+
lemma [elim,\<nu>elim]: "zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<ratio> RefS' spc N \<Longrightarrow> (zp \<left_fish_tail> a \<ratio> Pointer' spc LLTY['b] \<Longrightarrow> z \<left_fish_tail> a \<R_arr_tail> xs \<ratio> MemSlice N \<Longrightarrow> C) \<Longrightarrow> C"
  for N :: "('b::field, 'c) nu" unfolding Inhabited_def RefS'_def by (simp add: lrep_exps)

abbreviation "share_ref z x \<equiv> (case x of (zp \<left_fish_tail> a \<R_arr_tail> zx \<left_fish_tail> x) \<Rightarrow> (zp + z \<left_fish_tail> a \<R_arr_tail> zx + z \<left_fish_tail> x) | (zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail>) \<Rightarrow> (zp + z \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail>) | \<down_fish_tail> \<Rightarrow> \<down_fish_tail>)"
lemma [\<nu>intro]: "\<nu>Share (RefS['spc::len0] N) (\<lambda>x. T) share_ref" unfolding \<nu>Share_def by (simp add: lrep_exps)

lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>ShrIdentical (RefS['spc::len0] N) (rel_owning (rel_object (rel_owning (list_all2 (inv_imagep (=) ow)))))"
  unfolding \<nu>ShrIdentical_def \<nu>Ownership_def by (auto simp add: lrep_exps list_all2_conv_all_nth) (auto 0 3)

abbreviation "ownership_ref ref \<equiv>
  (case ref of zp \<left_fish_tail> a \<R_arr_tail> x \<Rightarrow> OWS_C (OWS_1 zp) (ownership x) | \<down_fish_tail> \<Rightarrow> OWS_C OWS_0 OWS_0)"
lemma [\<nu>intro]: "\<nu>Ownership (RefS['spc::len0] N) ownership_ref"
  unfolding \<nu>Ownership_def by (simp add: lrep_exps)

lemma [\<nu>intro]: "\<nu>Deprive (RefS['spc::len0] N) (\<lambda>x. \<down_fish_tail>)" unfolding \<nu>Deprive_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>CEqual (RefS['spc::len0] N) (rel1_owning (\<lambda>x y. True)) (rel_owning (rel_object (\<lambda>x y. True)))"
  unfolding \<nu>CEqual_def by (auto simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Zero (RefS['spc::len0] N) \<down_fish_tail>" unfolding \<nu>Zero_def by simp

lemma [\<nu>cast_overload E]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] N \<longmapsto> (zp \<left_fish_tail> a, z \<left_fish_tail> a \<R_arr_tail> xs) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace>"
and [\<nu>cast_overload E]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail> \<tycolon> RefS['spc::len0] N \<longmapsto> (zp \<left_fish_tail> a, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace>"
and [\<nu>cast_overload E]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<down_fish_tail> \<tycolon> RefS['spc::len0] N \<longmapsto> (\<down_fish_tail>, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace>"
  for N :: "('b::field, 'c) nu"
  unfolding Cast_def by (simp add: lrep_exps)+

\<nu>cast_overloads RefS
lemma [\<nu>cast_overload RefS]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (zp \<left_fish_tail> a, z \<left_fish_tail> a \<R_arr_tail> xs) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace> \<longmapsto> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> xs \<tycolon> RefS['spc::len0] N"
and [\<nu>cast_overload RefS]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (zp \<left_fish_tail> a, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace> \<longmapsto> zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail> \<tycolon> RefS['spc::len0] N"
and [\<nu>cast_overload RefS]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (\<down_fish_tail>, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemSlice N \<rbrace> \<longmapsto> \<down_fish_tail> \<tycolon> RefS['spc::len0] N"
  for N :: "('b::field, 'c) nu"
  unfolding Cast_def by (simp add: lrep_exps)+

subsubsection \<open>Single Reference\<close>

definition "Ref' spc N = RefS' spc N
    <down-lift> (\<lambda>x. case x of zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<Rightarrow> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> [x] | zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail> \<Rightarrow> zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail> | \<down_fish_tail> \<Rightarrow> \<down_fish_tail>)"
  for N :: "('b::field, 'c) nu"
syntax "_Ref'_" :: "type => logic" ("Ref'[_']")
translations "Ref['spc]" == "CONST Ref' (TYPE('spc))"
abbreviation "Ref \<equiv> Ref[0]"

lemma [simp]: "p \<nuLinkL> Ref['spc::len0] N \<nuLinkR> (zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x) \<longleftrightarrow> p \<nuLinkL> RefS['spc] N \<nuLinkR>(zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> [x])"
  and [simp]: "p \<nuLinkL> Ref['spc] N \<nuLinkR> (zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail>) \<longleftrightarrow> p \<nuLinkL> RefS['spc] N \<nuLinkR>(zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail>)"
  and [simp]: "p \<nuLinkL> Ref['spc] N \<nuLinkR> \<down_fish_tail> \<longleftrightarrow> p \<nuLinkL> RefS['spc] N \<nuLinkR> \<down_fish_tail>"
  unfolding Ref'_def by auto

lemma [\<nu>intro]: "\<nu>Share (Ref['spc::len0] N) (\<lambda>x. T) share_ref" unfolding \<nu>Share_def by (simp add: lrep_exps)

lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>ShrIdentical (Ref['spc::len0] N) (rel_owning (rel_object (rel_owning (inv_imagep (=) ow))))"
  unfolding \<nu>ShrIdentical_def \<nu>Ownership_def by (auto simp add: lrep_exps list_all2_conv_all_nth)

lemma [\<nu>intro]: "\<nu>Ownership (Ref['spc::len0] N) ownership_ref"
  unfolding \<nu>Ownership_def by (simp add: lrep_exps)

lemma [\<nu>intro]: "\<nu>Deprive (Ref['spc::len0] N) (\<lambda>x. \<down_fish_tail>)" unfolding \<nu>Deprive_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>CEqual (Ref['spc::len0] N) (rel1_owning (\<lambda>x y. True)) (rel_owning (rel_object (\<lambda>x y. True)))"
  unfolding \<nu>CEqual_def by (auto simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Zero (Ref['spc::len0] N) \<down_fish_tail>" unfolding \<nu>Zero_def by simp

lemma [\<nu>intro, \<nu>cast_overload singular]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> [x] \<tycolon> RefS['spc::len0] N \<longmapsto> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc] N" unfolding Cast_def by simp
lemma [\<nu>intro, \<nu>cast_overload plural]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc::len0] N \<longmapsto> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> [x] \<tycolon> RefS['spc] N" unfolding Cast_def by simp

lemma [\<nu>cast_overload E]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc::len0] N \<longmapsto> (zp \<left_fish_tail> a, z \<left_fish_tail> a \<R_arr_tail> x) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemObj N \<rbrace>"
and [\<nu>cast_overload E]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail> \<tycolon> Ref['spc::len0] N \<longmapsto> (zp \<left_fish_tail> a, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemObj N \<rbrace>"
and [\<nu>cast_overload E]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<down_fish_tail> \<tycolon> Ref['spc::len0] N \<longmapsto> (\<down_fish_tail>, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemObj N \<rbrace>"
  for N :: "('b::field, 'c) nu"
  unfolding Cast_def by (simp add: lrep_exps)+

\<nu>cast_overloads Ref
lemma [\<nu>cast_overload Ref]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (zp \<left_fish_tail> a, z \<left_fish_tail> a \<R_arr_tail> x) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemObj N \<rbrace> \<longmapsto> zp \<left_fish_tail> a \<R_arr_tail> z \<left_fish_tail> x \<tycolon> Ref['spc::len0] N"
and [\<nu>cast_overload Ref]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (zp \<left_fish_tail> a, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemObj N \<rbrace> \<longmapsto> zp \<left_fish_tail> a \<R_arr_tail> \<down_fish_tail> \<tycolon> Ref['spc::len0] N"
and [\<nu>cast_overload Ref]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (\<down_fish_tail>, \<down_fish_tail>) \<tycolon> \<lbrace> Pointer['spc] LLTY['b] \<nuFusion> MemObj N \<rbrace> \<longmapsto> \<down_fish_tail> \<tycolon> Ref['spc::len0] N"
  for N :: "('b::field, 'c) nu"
  unfolding Cast_def by (simp add: lrep_exps)+

subsection \<open>Numbers\<close>

\<nu>cast_overloads nat and int

value \<open>sint (7::4 word)\<close>

lemma [\<nu>cast_overload nat]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> \<int>['bits::len] \<longmapsto> nat x \<tycolon> \<nat>['bits]"
  unfolding Cast_def Premise_def apply (simp add: lrep_exps) sorry

lemma [\<nu>cast_overload int]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^(LENGTH('bits) - 1) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> \<nat>['bits::len] \<longmapsto> int x \<tycolon> \<int>['bits]"
  unfolding Cast_def Premise_def apply (simp add: lrep_exps)

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