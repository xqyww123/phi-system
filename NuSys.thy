(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrime NuLLReps
  keywords
    "proc" "proc'" "rec_proc" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "cast" "requires" "\<Longleftarrow>" "\<Longleftarrow>'" "$" "var" "always" :: quasi_command
  and "\<bullet>" "affirm" "\<nu>have" "\<nu>obtain" "\<nu>choose" "\<nu>choose2" "\<medium_left_bracket>" "\<medium_right_bracket>" "\<Longrightarrow>" "drop_fact" "\<nu>debug" "\<nu>debug'"
          "\<nu>note" "\<nu>choose_quick" :: prf_decl % "proof"
  and "\<nu>processor" "\<nu>processor_resolver" "\<nu>exty_simproc" :: thy_decl % "ML"
  and "\<nu>overloads" "\<nu>cast_overloads" :: thy_decl
  and "finish" :: "qed" % "proof"
abbrevs
  "!!" = "!!"
  and "<implies>" = "\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s"
begin

section \<open>Preliminary constants and settings used in the system\<close>

named_theorems used \<open>theorems that will be inserted in ANY proof environments,
which basically has the same effect as the using command.\<close>
  and final_proc_rewrite \<open>rules used to rewrite the generated procedure theorem in the final stage\<close>
  and final_proc_rewrite2

lemmas [final_proc_rewrite] = WorkingProtector_def
lemma [final_proc_rewrite2]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<nu>Zero N zr \<equiv> (\<nu>Zero N zr)" unfolding Premise_def .
  
definition  FailedPremise :: "bool \<Rightarrow> bool" where "FailedPremise \<equiv> Premise"
lemma FailedPremise_I: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> FailedPremise P" unfolding FailedPremise_def .
lemma FailedPremise_D: "FailedPremise P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding FailedPremise_def .

section \<open>Mechanisms - I\<close>

  subsection \<open>Cast\<close>

definition Cast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _ \<^bold>w\<^bold>h\<^bold>e\<^bold>n _)" [13,13,13,13] 12)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q) \<longleftrightarrow> (\<forall>v. Q \<longrightarrow> v \<in> A \<longrightarrow> v \<in> B \<and> P)"
consts SimpleCast1 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
consts SimpleCast2 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _ \<^bold>w\<^bold>h\<^bold>e\<^bold>n _)" [13,13,13] 12)
consts SimpleCast3 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _)" [13,13] 12)
translations
  "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>w\<^bold>h\<^bold>e\<^bold>n CONST True)"
  "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n CONST True)"
  "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>h\<^bold>e\<^bold>n P)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>w\<^bold>h\<^bold>e\<^bold>n P)"

definition CastDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _/ \<^bold>w\<^bold>h\<^bold>e\<^bold>n _)" [13,13,13,13,13] 12)
  where "CastDual A B P A' B' P' \<longleftrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<and> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P')"
consts SimpCastDual1 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _/ \<^bold>w\<^bold>h\<^bold>e\<^bold>n _)" [13,13,13,13] 12)
consts SimpCastDual2 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13,13] 12)
consts SimpCastDual3 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13] 12)
translations
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n CONST True"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n CONST True"

translations
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l a' \<tycolon> A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<tort_lbrace>a' \<tycolon> A'\<tort_rbrace> \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> b' \<tycolon> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> \<tort_lbrace>b' \<tycolon> B'\<tort_rbrace> \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"


(* abbreviation SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<equiv> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h True)" *)
(* lemma CastE[elim]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Cast_def Inhabited_def by (auto intro: Inhabited_subset)
lemma CastI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Cast_def Inhabited_def by auto *)
lemma cast_id[\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" unfolding Cast_def by fast
lemma cast_dual_id[\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B" unfolding CastDual_def  by (simp add: cast_id)

lemma "=_\<nu>cast": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma [\<nu>intro']: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e N = N' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<longmapsto> \<tort_lbrace>x' \<tycolon> N'\<tort_rbrace>" unfolding Cast_def Premise_def by simp
lemma [\<nu>intro0]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x" unfolding Premise_def by simp

lemma cast_trans: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def by auto
(* lemma dual_cast_fallback[\<nu>intro']: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<and> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t C \<longmapsto> C)" unfolding Cast_def by fast *)


section \<open>Essential \<nu>-abstractor\<close>

subsection \<open>Separation Conjecture\<close>

definition disjoint :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " (infixl "\<perpendicular>" 60) where "disjoint A B \<longleftrightarrow> (A \<inter> B = {})"
lemma disjoint_rewL: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<notin> B)" unfolding disjoint_def by auto
lemma disjoint_rewR: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> B \<longrightarrow> x \<notin> A)" unfolding disjoint_def by auto

lemma [iff]: "{} \<perpendicular> S" and [iff]: "S \<perpendicular> {}" unfolding disjoint_def by auto

definition Separation :: " (heap, 'a) \<nu> \<Rightarrow> (heap, 'b) \<nu> \<Rightarrow> (heap, 'a \<times> 'b) \<nu>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>h (a,b). (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> (h1 \<nuLinkL> A \<nuLinkR> a) \<and> (h2 \<nuLinkL> B \<nuLinkR> b)))"

lemma [iff]: "h \<nuLinkL> A \<^emph> B \<nuLinkR> (a,b) \<longleftrightarrow>
  (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> (h1 \<nuLinkL> A \<nuLinkR> a) \<and> (h2 \<nuLinkL> B \<nuLinkR> b))"
  unfolding Separation_def Refining_ex by simp

definition Heap_Delimiter :: "(heap,'ax) \<nu> \<Rightarrow> (heap,'bx) \<nu> \<Rightarrow> (heap, 'ax \<times> 'bx) \<nu>" (infixr "<heap-sep>" 70)
  where "A <heap-sep> B = A \<^emph> B"
abbreviation Heap_Delimiter_sugar :: " (heap, 'ax) typing \<Rightarrow> (heap, 'bx) typing \<Rightarrow> (heap, 'bx \<times> 'ax) typing " ( "_/ \<heavy_asterisk> _" [14,15] 14)
  where "(A \<heavy_asterisk> B) \<equiv> (typing_img B, typing_img A) \<tycolon> (typing_nu B <heap-sep> typing_nu A)"

lemma [simp]: " (a \<tycolon> A \<heavy_asterisk> b \<tycolon> B) = ((b,a) \<tycolon> (B <heap-sep> A)) " by auto
translations " (a \<tycolon> A) \<heavy_asterisk> (b \<tycolon> B) " \<rightleftharpoons> " (CONST Pair b a) \<tycolon> (B <heap-sep> A) "

lemma [cong]: "\<tort_lbrace> a \<tycolon> A \<tort_rbrace> \<equiv> \<tort_lbrace>a' \<tycolon> A'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace> b \<tycolon> B \<tort_rbrace> \<equiv> \<tort_lbrace>b' \<tycolon> B'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace> a \<tycolon> A \<heavy_asterisk> b \<tycolon> B \<tort_rbrace> \<equiv> \<tort_lbrace> a' \<tycolon> A' \<heavy_asterisk> b' \<tycolon> B' \<tort_rbrace>"
  unfolding atomize_eq unfolding Heap_Delimiter_def by auto





(*definition Separation :: " heap set \<Rightarrow> heap set \<Rightarrow> heap set" (infixl "\<heavy_asterisk>" 14)
  where "Separation H1 H2 = {h. (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> h1 \<in> H1 \<and> h2 \<in> H2) }"
definition NonSeparation :: " heap set \<Rightarrow> heap set \<Rightarrow> heap set" (infixl "\<dbl_and>" 13)
  where "NonSeparation H1 H2 = {h. h \<in> H1 \<and> (\<exists>h'. h' \<subseteq>\<^sub>m h \<and> h' \<in> H2)}"

translations
  "H \<heavy_asterisk> x \<tycolon> T" == "H \<heavy_asterisk> \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"
  "x \<tycolon> T \<heavy_asterisk> H" == "\<tort_lbrace> x \<tycolon> T \<tort_rbrace> \<heavy_asterisk> H"
  "H \<dbl_and> x \<tycolon> T" == "H \<dbl_and> \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"
  "x \<tycolon> T \<dbl_and> H" == "\<tort_lbrace> x \<tycolon> T \<tort_rbrace> \<dbl_and> H"

lemma [iff]: "h \<in> (H1 \<heavy_asterisk> H2) \<longleftrightarrow> (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> h1 \<in> H1 \<and> h2 \<in> H2)" unfolding Separation_def by simp
lemma [iff]: "h \<in> (H1 \<dbl_and> H2) \<longleftrightarrow> (h \<in> H1 \<and> (\<exists>h'. h' \<subseteq>\<^sub>m h \<and> h' \<in> H2))" unfolding NonSeparation_def by simp
*)

lemma [simp]: "A \<inter> S \<perpendicular> A \<inter> -S"
  unfolding disjoint_def by auto
lemma heap_split_id: "P h1' h2' \<Longrightarrow> \<exists>h1 h2. h1' ++ h2' = h1 ++ h2 \<and> P h1 h2" by auto
lemma heap_split_by_set: "P (h |` S) (h |` (- S)) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  by (rule exI[of _ "h |` S"], rule exI[of _ "h |` (- S)"])
    (auto simp add: map_add_def option.case_eq_if restrict_map_def disjoint_def disjoint_iff domIff)
lemma heap_split_by_addr_set: "P (h |` (MemAddress ` S)) (h |` (- (MemAddress ` S))) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  using heap_split_by_set .

lemma Separation_comm: " \<tort_lbrace> a \<tycolon> A \<heavy_asterisk> b \<tycolon> B\<tort_rbrace> = \<tort_lbrace>b \<tycolon> B \<heavy_asterisk> a \<tycolon> A\<tort_rbrace>" unfolding Heap_Delimiter_def
  by (auto 4 4 simp add: disjoint_def inf_commute dest: map_add_comm )
 
lemma Separation_assoc: "\<tort_lbrace> a \<tycolon> A \<heavy_asterisk> (b \<tycolon> B \<heavy_asterisk> c \<tycolon> C)\<tort_rbrace> = \<tort_lbrace>a \<tycolon> A \<heavy_asterisk> b \<tycolon> B \<heavy_asterisk> c \<tycolon> C\<tort_rbrace>"
  unfolding Heap_Delimiter_def
  by (auto simp add: disjoint_def) 
    (metis (no_types, lifting) Un_empty dom_map_add inf_sup_distrib1 inf_sup_distrib2 map_add_assoc)+

(* lemma NonSeparation_distrib_L: "h \<in> (A \<heavy_asterisk> (B \<dbl_and> P)) \<Longrightarrow> h \<in> (A \<heavy_asterisk> B \<dbl_and> P)"
  using map_le_map_add map_le_trans by blast
lemma NonSeparation_distrib_R: "h \<in> ((A \<dbl_and> P) \<heavy_asterisk> B) \<Longrightarrow> h \<in> (A \<heavy_asterisk> B \<dbl_and> P)"
  by (metis NonSeparation_distrib_L Separation_comm) *)
  

lemma [elim!,\<nu>elim]: "Inhabited \<tort_lbrace> a \<tycolon> A \<heavy_asterisk> b \<tycolon> B \<tort_rbrace> \<Longrightarrow> (a \<ratio> A \<Longrightarrow> b \<ratio> B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def Heap_Delimiter_def by auto
(* lemma [elim!,\<nu>elim]: "Inhabited (A \<dbl_and> B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by auto *)

subsubsection \<open>Fusion and Stack Delimiter operator\<close>

definition Fusion :: "('a1::lrep,'b1) \<nu> \<Rightarrow> ('a2::lrep,'b2) \<nu> \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) \<nu>" (infixr "\<cross_product>" 70) 
  where "Fusion N M p x = (case p of (p1,p2) \<Rightarrow> case x of (x1,x2) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2))"

lemma [simp]: "(p1,p2) \<nuLinkL> N \<cross_product> M \<nuLinkR> (x1,x2) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)"
  by (simp add: Fusion_def Refining_ex)
lemma [elim,\<nu>elim]: "(x1,x2) \<ratio> N1 \<cross_product> N2 \<Longrightarrow> (x1 \<ratio> N1 \<Longrightarrow> x2 \<ratio> N2 \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma [\<nu>intro]: "\<nu>Zero N z1 \<Longrightarrow> \<nu>Zero M z2 \<Longrightarrow> \<nu>Zero (N \<cross_product> M) (z1,z2)" unfolding \<nu>Zero_def by simp

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M \<longmapsto> y' \<tycolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (x,y) \<tycolon> N \<cross_product> M \<longmapsto> (x',y') \<tycolon> N' \<cross_product> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q" unfolding Cast_def by auto

definition Stack_Delimiter :: "('a::lrep,'ax) \<nu> \<Rightarrow> ('b::lrep,'bx) \<nu> \<Rightarrow> ('a \<times> 'b, 'ax \<times> 'bx) \<nu>" (infixr "<stack-div>" 70)
  where "A <stack-div> B = A \<cross_product> B"
abbreviation Stack_Delimiter_sugar :: " ('a :: stack, 'ax) typing \<Rightarrow> ('b :: lrep, 'bx) typing \<Rightarrow> ('b \<times> 'a, 'bx \<times> 'ax) typing " ( "_/ \<heavy_comma> _" [14,15] 14)
  where "(A \<heavy_comma> B) \<equiv> (typing_img B, typing_img A) \<tycolon> (typing_nu B <stack-div> typing_nu A)"

lemma [simp]: " (a \<tycolon> A \<heavy_comma> b \<tycolon> B) = ((b,a) \<tycolon> (B <stack-div> A)) " by auto
translations " (a \<tycolon> A) \<heavy_comma> (b \<tycolon> B) " \<rightleftharpoons> " (CONST Pair b a) \<tycolon> (B <stack-div> A) "

lemma [cong]: "\<tort_lbrace> a \<tycolon> A \<tort_rbrace> \<equiv> \<tort_lbrace>a' \<tycolon> A'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace> b \<tycolon> B \<tort_rbrace> \<equiv> \<tort_lbrace>b' \<tycolon> B'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace> a \<tycolon> A\<heavy_comma> b \<tycolon> B \<tort_rbrace> \<equiv> \<tort_lbrace> a' \<tycolon> A' \<heavy_comma> b' \<tycolon> B' \<tort_rbrace>"
  unfolding atomize_eq unfolding Stack_Delimiter_def by auto


subsection \<open>Existential Nu-type\<close>

definition ExNu :: " ('c \<Rightarrow> ('a,'b) \<nu>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b) \<nu> "
  where "ExNu N p x = (\<exists>c. p \<nuLinkL> N c \<nuLinkR> x c)"
lemma [simp]: "p \<nuLinkL> ExNu N \<nuLinkR> x \<longleftrightarrow> (\<exists>c. p \<nuLinkL> N c \<nuLinkR> x c)" unfolding ExNu_def Refining_ex by simp

abbreviation ExNu_sugar :: " ('c \<Rightarrow> ('a,'b) typing) \<Rightarrow> ('a, 'c \<Rightarrow> 'b) typing " (binder "\<exists>* " 10)
  where "ExNu_sugar P \<equiv> (\<lambda>c. typing_img (P c)) \<tycolon> ExNu (\<lambda>c. typing_nu (P c))"
translations "\<exists>* a b. P" \<rightleftharpoons> "\<exists>* a. (\<exists>*b. P)"
  "\<exists>* c. x \<tycolon> T" => "(\<lambda>c. x) \<tycolon> CONST ExNu (\<lambda>c. T)"
  "\<exists>* c. x \<tycolon> T" <= "(\<lambda>c. x) \<tycolon> CONST ExNu (\<lambda>c''''''. T)" (*TODO: print translation that alpha-convert the c''''' *)
notation ExNu_sugar (binder "\<exists>\<^sup>\<nu> " 10)


lemma [simp]: "p \<in> \<S>  \<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace> \<longleftrightarrow> (\<exists>z. p \<in> \<S>  \<tort_lbrace> x z \<tycolon> T z\<tort_rbrace> )" by (auto 4 3)
lemma [simp]: "p \<in> \<S_S> \<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace> \<longleftrightarrow> (\<exists>z. p \<in> \<S_S> \<tort_lbrace>x z \<tycolon> T z\<tort_rbrace>)" by (auto 4 3)
lemma [simp]: "\<tort_lbrace>x \<tycolon> ExNu T \<heavy_comma> y \<tycolon> R\<tort_rbrace> = \<tort_lbrace>\<exists>* c. x c \<tycolon> T c \<heavy_comma> y \<tycolon> R \<tort_rbrace>" unfolding Stack_Delimiter_def by auto
lemma [simp]: "\<tort_lbrace>y \<tycolon> L \<heavy_comma> x \<tycolon> ExNu T\<tort_rbrace> = \<tort_lbrace>\<exists>* c. y \<tycolon> L \<heavy_comma> x c \<tycolon> T c \<tort_rbrace>" unfolding Stack_Delimiter_def by auto
lemma ExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> ExNu T)) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding CurrentConstruction_def by auto

(* definition ExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" (binder "\<exists>* " 10)
  where   "ExTyp T = {x. (\<exists>z. x \<in> T z)}"
notation ExTyp (binder "\<exists>'' " 10)
  \<comment> \<open>which represents there exists some \<nu>-images (or rarely abstractors) subject to the typing.
    And then the image subjecting the typing could be fixed as a local variable by the \<nu>-obtain command. \<close>

lemma [simp]: "x \<in> ExTyp T \<longleftrightarrow> (\<exists>z. x \<in> T z)" unfolding ExTyp_def  by auto
lemma [simp]: "x \<in> \<S> (ExTyp T) \<longleftrightarrow> (\<exists>z. x \<in> \<S> (T z))" by (auto 4 3)
lemma [simp]: "x \<in> \<S_S> (ExTyp T) \<longleftrightarrow> (\<exists>z. x \<in> \<S_S> (T z))" by (auto 4 3)
lemma [simp]: "(ExTyp A \<heavy_comma> R) = (\<exists>* x. (A x \<heavy_comma> R))" by auto
lemma [simp]: "(S\<heavy_comma> ExTyp T) = (\<exists>* z. (S \<heavy_comma> T z))" by auto
lemma ExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (ExTyp T)) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding CurrentConstruction_def by auto *)


(* definition AutoExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" (binder "\<exists>*''" 10)
  where "AutoExTyp T = {x. (\<exists>z. x \<in> (T z))}"

lemma [simp]: "x \<in> (AutoExTyp T) \<equiv> (\<exists>z. x \<in> T z)" unfolding AutoExTyp_def by auto
lemma [simp]: "(R\<heavy_comma> AutoExTyp T) = (\<exists>*' x. (R\<heavy_comma> T x))" unfolding AutoExTyp_def by auto
lemma [simp]: "(AutoExTyp T\<heavy_comma> R) = (\<exists>*' x. (T x\<heavy_comma> R))" unfolding AutoExTyp_def by auto
lemma [simp]: "(AutoExTyp T \<flower> R) = (\<exists>*' x. (T x \<flower> R))" unfolding AutoExTyp_def BinderNameTag_def by auto

lemma [simp]: "AutoExTyp T = (\<exists>*' a b. T (a,b))" unfolding AutoExTyp_def by auto

lemma AutoExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (AutoExTyp T)) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding AutoExTyp_def CurrentConstruction_def by (rule eq_reflection) auto *)

subsection \<open>Addition Nu-type : coheres true proposition\<close>

definition AddtionTy :: " 'a set \<Rightarrow> bool \<Rightarrow> 'a set " (infixl "\<addition>" 50)
  where " (T \<addition> P) = {x. x \<in> T \<and> P}"
lemma [simp]: "T \<addition> True = T" unfolding AddtionTy_def by simp
lemma [simp]: "x \<in> (T \<addition> P) \<longleftrightarrow> x \<in> T \<and> P" unfolding AddtionTy_def by simp
(* lemma [intro]: "P \<Longrightarrow> [h] x \<in>\<^sub>\<nu> T \<Longrightarrow> [h] x \<in>\<^sub>\<nu> (T \<addition> P)" by simp
lemma [elim]: "[h] x \<in>\<^sub>\<nu> (T \<addition> P) \<Longrightarrow> ([h] x \<in>\<^sub>\<nu> T \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C" by simp*)
lemma [simp]: "(R \<heavy_comma> T \<addition> P) = ((R \<heavy_comma> T) \<addition> P)" by auto
lemma t1: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<addition> P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P" unfolding CurrentConstruction_def by (cases s) auto
lemma [simp]: "((((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<and> B) \<and> C) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<equiv> (((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<and> (B \<and> C)) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)" by simp

lemma move_fact_to_star1[simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<addition> Q) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP NoFact) (PROP L) (PROP I))
    \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop Q) (PROP L) (PROP I))"
  unfolding t1 SpecTop_imp conj_imp FactCollection_imp
  by (intro equal_intr_rule SpecTop_I FactCollection_I conjI NoFact) (* (unfold SpecTop_imp conj_imp FactCollection_imp) *)
lemma move_fact_to_star2[simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<addition> Q) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop P) (PROP L) (PROP I))
    \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection  (Trueprop (Q \<and> P)) (PROP L) (PROP I))"
  unfolding t1 SpecTop_imp conj_imp FactCollection_imp
  by (intro equal_intr_rule SpecTop_I FactCollection_I conjI) (* (unfold SpecTop_imp conj_imp FactCollection_imp) *)


section \<open>Syntax\<close>

subsection \<open>Logical image models\<close>

text \<open>A set of models having common meanings, useful for representing logical images\<close>

consts val_of :: " 'a \<Rightarrow> 'b "
consts key_of :: " 'a \<Rightarrow> 'b "

datatype ('a, 'b) object (infixr "\<R_arr_tail>" 60) = object (key_of_obj: 'a) (val_of_obj: 'b) (infixr "\<R_arr_tail>" 60)
adhoc_overloading key_of key_of_obj and val_of val_of_obj
declare object.sel[iff]

lemma object_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_All[lrep_exps]: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a \<R_arr_tail> b))" 
proof fix a b assume "(\<And>x. PROP P x) " then show "PROP P (a \<R_arr_tail> b)" .
next fix x assume "\<And>a b. PROP P (a \<R_arr_tail> b)"
    from \<open>PROP P (key_of x \<R_arr_tail> val_of x)\<close> show "PROP P x" by simp
qed

subsection \<open>Argument and return list\<close>

consts "Arg_Ret_Pair_sugar" :: " (heap \<times> 'a::lrep) set \<Rightarrow> (heap \<times> 'b::lrep) set \<Rightarrow> 'wow_sugar" (infix "\<longmapsto>" 2)

ML \<open>local open Ast in
  fun tr_pair_i ret (Appl [Constant \<^syntax_const>\<open>_tuple_args\<close>, X, Y])
        = tr_pair_i (Appl [Constant \<^const_syntax>\<open>Stack_Delimiter\<close>, ret, X]) Y
    | tr_pair_i ret (Appl [Constant \<^syntax_const>\<open>_tuple_arg\<close>, y])
        = Appl [Constant \<^const_syntax>\<open>Stack_Delimiter\<close>, ret, y]
  fun tr_pair (Appl [Constant \<^syntax_const>\<open>_tuple\<close>, X, Y]) = tr_pair_i X Y
    | tr_pair x = x
  fun tr_stack (Appl [Constant \<^const_syntax>\<open>Stack_Delimiter\<close>, X, Y])
        = Appl [Constant \<^const_syntax>\<open>Stack_Delimiter\<close>, tr_stack X, Y]
    | tr_stack (a as Appl [Constant \<^const_syntax>\<open>typing\<close>, _, _])
        = Appl [Constant \<^const_syntax>\<open>Stack_Delimiter\<close>, Variable "\<R>", a]
    | tr_stack variable = variable
  val tr_stack_final = tr_stack o tr_pair
  fun tr_context (Appl [Constant \<^const_syntax>\<open>Context\<close>, X, Y])
        = (Appl [Constant \<^const_syntax>\<open>Context\<close>, tr_stack_final X, Y])
    | tr_context (X as Appl [Constant \<^const_syntax>\<open>Stack_Delimiter\<close>, _, _])
        = (Appl [Constant \<^const_syntax>\<open>Context\<close>, tr_stack_final X, Variable "\<H>"])
    | tr_context (X as Appl [Constant \<^const_syntax>\<open>typing\<close>, _, _])
        = (Appl [Constant \<^const_syntax>\<open>Context\<close>, tr_stack_final X, Variable "\<H>"])
    | tr_context v = v
  fun tr_context_final x = tr_context (tr_pair x)
  fun tr_proc ([f, T, U])
    = (Appl [Constant \<^const_syntax>\<open>Procedure\<close>, f, tr_context_final T, tr_context_final U])
  fun tr_arg_ret_pair ([T, U])
    = (Appl [Constant \<^const_syntax>\<open>Arg_Ret_Pair_sugar\<close>, tr_context_final T, tr_context_final U])
end\<close>

parse_ast_translation \<open>[
  (\<^const_syntax>\<open>Procedure\<close>, K tr_proc),
  (\<^const_syntax>\<open>Arg_Ret_Pair_sugar\<close>, K tr_arg_ret_pair)
]\<close>

section \<open>Mechanisms - II\<close>



subsection \<open>Heap\<close>

definition Nothing :: "heap set" where  "Nothing = {Map.empty}"
term "Map.empty"
lemma Separation_emptyL: "(Nothing \<heavy_asterisk> S) = S" and Separation_emptyR: "(S \<heavy_asterisk> Nothing) = S"
  unfolding Nothing_def Separation_def by auto

subsubsection \<open>Syntax & Auxiliary\<close>

consts ResourceState :: " heap \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> bool" ("_ \<^bold>a\<^bold>t _ \<^bold>i\<^bold>s _ " [16,16,12] 11)
consts allocated :: " heap \<Rightarrow> 'a \<Rightarrow> bool"

translations "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s x \<tycolon> T" \<rightleftharpoons> "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"

definition "addr_allocated heap addr \<longleftrightarrow> MemAddress addr \<in> dom heap"
adhoc_overloading allocated addr_allocated

(* lemma addr_allocated_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> addr_allocated h addr \<Longrightarrow> addr_allocated h' addr"
  unfolding addr_allocated_def by auto
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto *)
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto

definition MemAddrState :: "heap \<Rightarrow> nat memaddr \<Rightarrow> 'b::lrep set \<Rightarrow> bool"
  where "MemAddrState h addr S \<longleftrightarrow> addr_allocated h addr \<and> shallowize (the (h (MemAddress addr))) \<in> S"
adhoc_overloading ResourceState MemAddrState

(*lemma MemAddrState_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> MemAddrState h' addr S"
  unfolding MemAddrState_def addr_allocated_def by auto (metis \<nu>set_mono domI map_le_def option.sel) *)

lemma MemAddrState_I_neq[intro]: "k2 \<noteq> k \<Longrightarrow> MemAddrState h k2 S \<Longrightarrow> MemAddrState (h(MemAddress k := v)) k2 S"
  and MemAddrState_I_eq[intro]: "v' \<in> S \<Longrightarrow> MemAddrState (h(MemAddress k \<mapsto> deepize v')) k S"
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_E[elim]:
  "MemAddrState h addr S \<Longrightarrow> (addr_allocated h addr \<Longrightarrow> Inhabited S \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding MemAddrState_def by auto
lemma MemAddrState_I:
  "addr_allocated h addr \<Longrightarrow> shallowize (the (h (MemAddress addr))) \<in> S \<Longrightarrow> MemAddrState h addr S"
  unfolding MemAddrState_def by auto

(* lemma MemAddrState_retained_N[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<nu>Independent S claim
    \<Longrightarrow> Alive k \<in> claim \<Longrightarrow> MemAddrState (h(k:=None)) addr S"
  unfolding MemAddrState_def \<nu>Independent_def by auto
lemma MemAddrState_retained_S[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<nu>Independent S claim
    \<Longrightarrow> Write k \<in> claim \<Longrightarrow> MemAddrState (h(k \<mapsto> v)) addr S"
  unfolding MemAddrState_def \<nu>Independent_def by auto

*)


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> a \<in> S \<Longrightarrow> h |` (MemAddress ` S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> a \<notin> S \<Longrightarrow> h |` (- MemAddress ` S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def
  by auto (metis ComplI imageE option.sel resource_key.inject(1) restrict_map_def)

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)


subsubsection \<open>Cast\<close>

definition Heap_Cast_Goal :: " heap set \<Rightarrow> heap set " ("\<medium_left_bracket> _ \<medium_right_bracket>") where "Heap_Cast_Goal x = x"
  \<comment> \<open>The protector marks the goal to be gained\<close>
translations "\<medium_left_bracket> x \<tycolon> T \<medium_right_bracket>" \<rightleftharpoons> "\<medium_left_bracket> \<tort_lbrace> x \<tycolon> T \<tort_rbrace> \<medium_right_bracket>"

lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m" unfolding Heap_Cast_Goal_def using cast_dual_id .

lemma context_cast[\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t K \<longmapsto> K' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> H' \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (K\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<longmapsto> (K'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H') \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def Heap_Cast_Goal_def by (auto simp add: pair_forall)

lemma context_cast_dual[\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t K \<longmapsto> K' \<^bold>w\<^bold>i\<^bold>t\<^bold>h PK
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> H' \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h PH \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H2 \<medium_right_bracket> \<longmapsto> H2' \<^bold>w\<^bold>h\<^bold>e\<^bold>n QH
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (K\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<longmapsto> (K'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H') \<^bold>w\<^bold>i\<^bold>t\<^bold>h PK \<and> PH \<^bold>d\<^bold>u\<^bold>a\<^bold>l (K2\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H2) \<longmapsto> (K2\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H2') \<^bold>w\<^bold>h\<^bold>e\<^bold>n QH"
  unfolding CastDual_def Cast_def Heap_Cast_Goal_def by (auto simp add: pair_forall)

(* lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> H' \<heavy_asterisk> y \<tycolon> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> y\<^sub>m \<tycolon> Y \<longmapsto> x\<^sub>m \<tycolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> H' \<heavy_asterisk> \<medium_left_bracket> y \<tycolon> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> y\<^sub>m \<tycolon> Y \<medium_right_bracket> \<longmapsto> x\<^sub>m \<tycolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Heap_Cast_Goal_def . *)
(* lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B" unfolding CastDual_def  by (simp add: cast_id) *)

lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> H \<longmapsto> L \<heavy_asterisk> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>d\<^bold>u\<^bold>a\<^bold>l L \<heavy_asterisk> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> L \<heavy_asterisk> H\<^sub>m" unfolding Heap_Cast_Goal_def using cast_dual_id .

lemma heap_idx_this[\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Nothing \<heavy_asterisk> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>d\<^bold>u\<^bold>a\<^bold>l Nothing \<heavy_asterisk> \<medium_left_bracket> X\<^sub>m \<medium_right_bracket> \<longmapsto> X\<^sub>m"
  unfolding Cast_def Separation_emptyL Heap_Cast_Goal_def CastDual_def by simp

lemma heap_idx_L[\<nu>intro0]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<heavy_asterisk> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l S'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> X\<^sub>m \<medium_right_bracket> \<longmapsto> S\<^sub>m \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> S \<longmapsto> L \<heavy_asterisk> S' \<heavy_asterisk> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l L \<heavy_asterisk> S'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> X\<^sub>m \<medium_right_bracket> \<longmapsto> L \<heavy_asterisk> S\<^sub>m \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def
  by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq)

lemma heap_idx_R[\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<heavy_asterisk> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l S'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> X\<^sub>m \<medium_right_bracket> \<longmapsto> S\<^sub>m \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<heavy_asterisk> R \<longmapsto> S' \<heavy_asterisk> R \<heavy_asterisk> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l S'\<^sub>m \<heavy_asterisk> R \<heavy_asterisk> \<medium_left_bracket> X\<^sub>m \<medium_right_bracket> \<longmapsto> S\<^sub>m \<heavy_asterisk> \<medium_left_bracket> R \<medium_right_bracket> \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def
  by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq)

lemma [\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S1 \<heavy_asterisk> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>d\<^bold>u\<^bold>a\<^bold>l S1\<^sub>m \<heavy_asterisk> \<medium_left_bracket> X\<^sub>m \<medium_right_bracket> \<longmapsto> S\<^sub>m \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q1
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S1 \<longmapsto> \<medium_left_bracket> S2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> S2\<^sub>m \<medium_right_bracket> \<longmapsto> S1\<^sub>m \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q2
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> \<medium_left_bracket> S2 \<heavy_asterisk> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> S2\<^sub>m \<heavy_asterisk> X\<^sub>m \<medium_right_bracket> \<longmapsto> S\<^sub>m \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q1 \<and> Q2"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def
  by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq)

(* TODO: implement the Different tactic and then enable the \<nu>intro' *)
lemma [ \<nu>intro' ]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> D \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n P' \<Longrightarrow> Different \<tort_lbrace> x \<tycolon> T \<tort_rbrace> D \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P'
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t D \<longmapsto> D' \<heavy_asterisk> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l I'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> I \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q2  
  \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t I \<longmapsto> x\<^sub>m \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q' \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> D' \<heavy_asterisk> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l I'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> x\<^sub>m \<tycolon> T \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q \<and> Q2"
  unfolding Dest_def Intro_def CastDual_def Different_def Heap_Cast_Goal_def Cast_def
  by (auto simp add: Premise_def)



lemma heap_put_this: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t Nothing \<heavy_asterisk> X \<longmapsto> X" unfolding Cast_def Separation_emptyL by simp
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<heavy_asterisk> X \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> S \<heavy_asterisk> X \<longmapsto> L \<heavy_asterisk> S' "
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq)
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<heavy_asterisk> X \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (S \<heavy_asterisk> R) \<heavy_asterisk> X \<longmapsto> S' \<heavy_asterisk> R "
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq)



lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> S \<longmapsto> L \<heavy_asterisk> S'"
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq) 
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<heavy_asterisk> R \<longmapsto> S' \<heavy_asterisk> R"
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq)





(* subsection \<open>Register\<close>

definition AndTy :: " 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> ('a \<times> 'b) \<nu>set " (infixr "\<^bold>a\<^bold>n\<^bold>d" 3)
  where "(A \<^bold>a\<^bold>n\<^bold>d B) = Abs_\<nu>set (\<lambda>heap. set_of_\<nu> A heap \<times> set_of_\<nu> B heap) "
lemma [simp]: "[heap] (a, b) \<in>\<^sub>\<nu> (A \<^bold>a\<^bold>n\<^bold>d B) \<longleftrightarrow> [heap] a \<in>\<^sub>\<nu> A \<and> [heap] b \<in>\<^sub>\<nu> B"
  unfolding AndTy_def by transfer (auto simp add: NuSet_def Abs_\<nu>set_inverse)
lemma [intro]: "[h] a \<in>\<^sub>\<nu> A \<Longrightarrow> [h] b \<in>\<^sub>\<nu> B \<Longrightarrow> [h] (a, b) \<in>\<^sub>\<nu> (A \<^bold>a\<^bold>n\<^bold>d B)" by simp
lemma [elim]: "[h] ab \<in>\<^sub>\<nu> (A \<^bold>a\<^bold>n\<^bold>d B) \<Longrightarrow> (\<And>a b. ab = (a, b) \<Longrightarrow> [h] a \<in>\<^sub>\<nu> A \<Longrightarrow> [h] b \<in>\<^sub>\<nu> B \<Longrightarrow> C) \<Longrightarrow> C" by (cases ab) simp
lemma [elim!,\<nu>elim]: "Inhabited (A \<^bold>a\<^bold>n\<^bold>d B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<nu>Resources_of_set A as \<Longrightarrow> \<nu>Resources_of_set B bs \<Longrightarrow> \<nu>Resources_of_set (A \<^bold>a\<^bold>n\<^bold>d B) (as \<union> bs)"
  unfolding \<nu>Resources_of_set_def  by auto

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A \<^bold>a\<^bold>n\<^bold>d B) \<longmapsto> (A' \<^bold>a\<^bold>n\<^bold>d B') \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def by auto
lemma StackDelimiter_to_AndTy: " (A\<heavy_comma> B) \<equiv> (B \<^bold>a\<^bold>n\<^bold>d A) " unfolding Stack_Delimiter_def AndTy_def by simp
*)

subsection \<open>Cast\<close>

theorem apply_cast: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H)) \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<addition> P)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Cast_def by (auto 4 6)
theorem "cast": "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  for T' :: "(heap \<times> 'a::lrep) set" unfolding Cast_def CurrentConstruction_def by auto

(* theorem proc_cast': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> A \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A' \<longmapsto> B' \<brangle>"
  unfolding Procedure_def Cast_def by (auto 0 4) *)

lemma [\<nu>intro']: "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Intro_def .
lemma [\<nu>intro']: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Dest_def .

lemma "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" unfolding Intro_def using cast_id .
lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" unfolding Dest_def using cast_id .
  \<comment> \<open>All intro-cast or dest-cast involved in the reasoner constitute a directed acyclic graph WITH self-loop.
    Note the self-loop has the lowest priority, so that the self-loop only be tried ONCE in the whole reasoning
      (when all other rules cannot be applied), and only longest inference chains (who cannot be extended by
      any other rules) will be tried by self-loop.
    \<^term>\<open>Different\<close> can be used to assert the non-self-loop.\<close>

subsection \<open>Conversion\<close>

(* definition AutoTag :: "bool \<Rightarrow> bool" ("\<^bold>a\<^bold>u\<^bold>t\<^bold>o _" [100] 99) where [\<nu>def]: "\<^bold>a\<^bold>u\<^bold>t\<^bold>o P \<longleftrightarrow> P"
lemma [\<nu>intro]: "[heap] \<^bold>c\<^bold>a\<^bold>s\<^bold>t U \<longmapsto> U' \<Longrightarrow> \<^bold>a\<^bold>u\<^bold>t\<^bold>o \<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> U \<longmapsto> U' \<brangle>"
  unfolding AutoTag_def Cast_def Procedure_def nop_def by auto *)
  
definition Conversion :: "('a::lrep \<longmapsto> 'b::lrep) \<Rightarrow> (heap\<times>'a) set \<Rightarrow> (heap\<times>'b) set \<Rightarrow> ( ('c::lrep) \<longmapsto> ('d::lrep)) \<Rightarrow> (heap\<times>'c) set \<Rightarrow> (heap\<times>'d) set \<Rightarrow> bool"
    ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)/ \<long_dobule_mapsto> _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)" [101,2,2,101,2,2] 100)
    where [\<nu>def]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> g \<blangle> U' \<longmapsto> V' \<brangle> \<longleftrightarrow>( \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> V' \<brangle> )"

lemma conversion: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f' \<blangle> U' \<longmapsto> V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U' \<longmapsto> V' \<brangle>"
  for f :: " ('a::lrep) \<longmapsto> ('b::lrep)" and f' :: " ('c::lrep) \<longmapsto> ('d::lrep)" unfolding Conversion_def by fast

lemma [\<nu>intro0]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U \<longmapsto> V \<brangle>" unfolding Conversion_def by fast

lemma conversion_cast[\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (P \<longrightarrow> Q) \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U' \<longmapsto> V'\<brangle>"
  unfolding Conversion_def Procedure_def Cast_def CastDual_def id_def
  by (metis Cast_def CurrentConstruction_def LooseStateTy_introByStrict LooseStateTy_upgrade Premise_def "cast")
(* lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> U \<brangle> \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> (g \<nuInstrComp> f) \<blangle> U' \<longmapsto> V\<brangle>"
  unfolding Conversion_def using instr_comp by fast *)

theorem apply_proc_conv: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> S' \<longmapsto> T' \<brangle> \<long_dobule_mapsto> g \<blangle> S \<longmapsto> T\<brangle>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S' \<longmapsto> T' \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Conversion_def by auto

lemma conversion_trans: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n g \<blangle> Xg \<longmapsto> Yg \<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf \<brangle> \<long_dobule_mapsto> g \<blangle> Xg \<longmapsto> Yg \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf\<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>"
  unfolding Conversion_def by blast


 subsubsection \<open>Auto construct & destruct\<close>

definition AutoConstruct :: " 'exp \<Rightarrow> ('a::lrep \<longmapsto> 'b::lrep) \<Rightarrow> (heap \<times> 'a) set \<Rightarrow> (heap \<times> 'b) set \<Rightarrow> bool "("\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t _/ \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<blangle>_/ \<longmapsto> _ \<brangle>)" [20,101,10,10] 100)
  where [\<nu>def]:"AutoConstruct exp f S T \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>"
lemma AutoConstruct: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> AutoConstruct exp f S T \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)" for exp :: "'exp"
  unfolding AutoConstruct_def using apply_proc .

(* lemma [simp]: "(Inhabited A \<and> Inhabited B) \<or> (Inhabited A' \<and> Inhabited B')
  \<Longrightarrow> (A\<heavy_comma>B) = (A'\<heavy_comma>B') \<longleftrightarrow> A = A' \<and> B = B'" unfolding Stack_Delimiter_def Inhabited_def by (auto simp add: times_eq_iff) 
lemma  [elim]: "(A\<heavy_comma>B) = (A'\<heavy_comma>B') \<Longrightarrow> (A = {} \<or> B = {} \<Longrightarrow> A' = {} \<or> B' = {} \<Longrightarrow> C) \<Longrightarrow> (A = A' \<Longrightarrow> B = B' \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Stack_Delimiter_def by (auto simp add: times_eq_iff)
*)



subsection \<open>Index for Shallow Representation\<close>

text \<open>Indexes provide the function to access and map the addressed part in a nested structure (e.g. a nested pair @{term "(a,((b,c),d))"}.
  It is achieved by nested composition of address functions. For example "get_at (address_L (address_R address_here))"
  returns @{term b} for the pattern @{term "((a,b),c)"}, and "map_at (address_L (address_R address_here)) f"
  maps a @{term "((a,b),c)"} to @{term "((a, f b),c)"}\<close>

named_theorems \<nu>index_def

datatype ('a,'b,'x,'y) index = Index (get_idx: "'a \<Rightarrow> 'x") (map_idx: "('x \<Rightarrow> 'y) \<Rightarrow> 'a \<Rightarrow> 'b")
declare  index.split[split] Map'_def[\<nu>index_def]

definition index_here :: "('a,'b,'a,'b) index" where "index_here = Index id id"
definition index_left :: "('a,'b,'x,'y) index \<Rightarrow> ('a \<times> 'r, 'b \<times> 'r, 'x, 'y) index"
  where "index_left adr = (case adr of Index g m \<Rightarrow> Index (g \<circ> fst) (apfst o m))"
definition index_right :: "('a,'b,'x,'y) index \<Rightarrow> ('l \<times> 'a, 'l \<times> 'b, 'x, 'y) index"
  where "index_right adr = (case adr of Index g m \<Rightarrow> Index (g \<circ> snd) (apsnd o m))"


definition AdrGet :: " ('a,'b,'x,'y) index \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<blangle> _ \<^bold>@ _ \<brangle>)" [101,4,4] 100)
  where [\<nu>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<blangle> X \<^bold>@ A \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx adr \<blangle> A \<longmapsto> X \<brangle>"
definition AdrMap :: " ('a,'b,'x,'y) index \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> 'y set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<blangle> _ \<^bold>@ _ \<longmapsto> _ \<^bold>@ _ \<brangle>)" [101,4,4,4,4] 100)
  where [\<nu>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx idx \<blangle> A \<longmapsto> X \<brangle> \<and>
    (\<forall>f. (\<forall>a. a \<in> X \<longrightarrow> f a \<in> Y) \<longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> map_idx idx f  a \<in> B))"
declare Map_def[\<nu>index_def]

lemma index_here_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>index_def  index_here_def by auto
lemma index_here_mapper[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>index_def  index_here_def by auto
(* lemma index_left_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left f \<blangle> X \<^bold>@ (A \<^bold>a\<^bold>n\<^bold>d R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases f) auto
lemma index_right_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d A) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto *)
lemma index_stack_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (A\<heavy_comma> N) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto
(* lemma index_left_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left f \<blangle> X \<^bold>@ (A \<^bold>a\<^bold>n\<^bold>d R) \<longmapsto> Y \<^bold>@ (B \<^bold>a\<^bold>n\<^bold>d R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases f) auto
lemma index_right_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d A) \<longmapsto> Y \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d B) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto *)
lemma index_stack_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (A\<heavy_comma> N) \<longmapsto> Y \<^bold>@ (B\<heavy_comma> N) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto

(*
subsection \<open>Register\<close>

definition RegisterCollection :: " 'a \<Rightarrow> 'a " where "RegisterCollection x = x"

lemma RegisterCollection_rew[final_proc_rewrite]: "RegisterCollection x \<equiv> x" unfolding RegisterCollection_def .
lemma Named_rew[final_proc_rewrite]: "Named name x \<equiv> x" unfolding Named_def .

lemma index_reg_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ RegisterCollection A \<brangle>"
  unfolding RegisterCollection_def .
lemma index_reg_mapper[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A  \<longmapsto> Y \<^bold>@ B \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ RegisterCollection A \<longmapsto> Y \<^bold>@ RegisterCollection B \<brangle>"
  unfolding RegisterCollection_def .

(* definition new_reg_0 :: "(('x::lrep) \<times> ('R::lrep) \<flower> void) \<Rightarrow> ('R \<flower> 'x register) state"
  where "new_reg_0 s = (case s of Proc_Ctx (x,R) void \<Rightarrow> StatOn (Proc_Ctx R (Register (NAME _) x)))"
definition new_reg_L :: "('G, 'G2, 't, 'x register \<times> 't) index \<Rightarrow> (('x::lrep) \<times> ('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg_L adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (Register (NAME _) x,t)) G)))"
definition new_reg_R :: "('G, 'G2, 't, 't \<times> 'x register) index \<Rightarrow> (('x::lrep) \<times> ('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg_R adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (t, Register (NAME _) x)) G)))" *)

subsubsection \<open>Instruction Definitions\<close>

definition new_reg :: "('r::stack, 'r2::stack, 'x::lrep, void \<times> 'x) index \<Rightarrow> 'r \<longmapsto> 'r2"
  where "new_reg idx h r = Success h (map_idx idx (Pair void) r)"
definition delete_reg :: "('r::stack, 'r2::stack, 'x::lrep \<times> 'b::lrep, 'b) index \<Rightarrow> 'r \<longmapsto> 'r2"
  where "delete_reg idx h s = Success h (map_idx idx snd s)"

definition store_reg :: "('r::stack, 'r2::stack, 'x::lrep, 'y::lrep) index \<Rightarrow> 'y \<times> 'r \<longmapsto> 'r2"
  where "store_reg idx h = (\<lambda>(y,r). Success h (map_idx idx (\<lambda>x.  y) r))"
definition load_reg :: "('r::stack, 'r::stack, 'x::lrep, 'x::lrep) index \<Rightarrow> 'r \<longmapsto> 'x \<times> 'r"
  where "load_reg idx h r = Success h (get_idx idx r, r)"
definition move_reg :: "('r::stack, 'r2::stack, 'x::lrep, void) index \<Rightarrow> 'r \<longmapsto> 'x \<times> 'r2"
  where "move_reg idx h r = Success h (get_idx idx r, map_idx idx (\<lambda>_. void) r)"

subsubsection \<open>Instruction Specifications\<close>

lemma new_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> W \<^bold>@ G \<longmapsto> ( \<ltbrak>\<n>\<a>\<m>\<e>\<rtbrak>. Void \<^bold>a\<^bold>n\<^bold>d W) \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg idx \<blangle> G \<longmapsto> G2 \<brangle>"
  unfolding \<nu>index_def \<nu>def new_reg_def by (cases idx) auto

lemma delete_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle>(W \<^bold>a\<^bold>n\<^bold>d Z) \<^bold>@ G \<longmapsto> Z \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c delete_reg idx \<blangle> G \<longmapsto> G2 \<brangle>"
  unfolding \<nu>index_def \<nu>def delete_reg_def  by (cases idx) auto

lemma store_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> Named name X \<^bold>@ G \<longmapsto> Named name Y \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c store_reg idx \<blangle> G\<heavy_comma> Y \<longmapsto> G2 \<brangle>"
  unfolding \<nu>index_def \<nu>def store_reg_def by (cases idx) auto

lemma load_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> Named name  \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>@ R \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c load_reg idx \<blangle> R \<longmapsto> R \<heavy_comma> x \<tycolon> X \<brangle>"
  unfolding \<nu>index_def \<nu>def load_reg_def by auto

lemma move_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> Named name X \<^bold>@ R \<longmapsto> Named name Void \<^bold>@ R' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c move_reg idx \<blangle> R \<longmapsto> R' \<heavy_comma> X \<brangle>"
  unfolding \<nu>index_def \<nu>def move_reg_def by (cases idx) auto

(* schematic_goal "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right (index_left (index_left (index_here))) \<blangle> ?X \<^bold>@ ?A \<brangle>" by (rule \<nu>intro)+
schematic_goal th1: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x (?adr::('a \<times> 'b \<times> 'c,?'z, 'b, ?'x) index) \<blangle> X \<^bold>@ (A \<^bold>a\<^bold>n\<^bold>d X \<^bold>a\<^bold>n\<^bold>d C) \<longmapsto> ?Y \<^bold>@ ?Z \<brangle>" 
  including show_more by (rule \<nu>intro)+ *)

subsubsection \<open>Initial registers\<close>

definition op_init_registers :: "('s::stack, 's2::stack, 'r::stack, void) index \<Rightarrow> 's \<longmapsto> 's2 \<times> 'r"
  where "op_init_registers idx h s = Success h (map_idx idx (\<lambda>_. void) s, get_idx idx s)"

lemma op_init_register:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> RegisterCollection R \<^bold>@ S \<longmapsto> Void \<^bold>@ S' \<brangle>
      \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_init_registers idx \<blangle> S \<longmapsto> RegisterCollection (S' \<^bold>a\<^bold>n\<^bold>d R) \<brangle>"
  unfolding RegisterCollection_def op_init_registers_def \<nu>def \<nu>index_def by auto
*)
subsection \<open>Structural Pairs\<close>

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def .
(*
lemma [\<nu>intro]: "<Structural> f x y = (a,b) \<Longrightarrow> <Structural> case_prod f (x,y) = (a,b)"
  unfolding StructuralTag_def by simp
lemma [\<nu>intro0]: "<Structural> x = a \<Longrightarrow> <Structural> y = b \<Longrightarrow> <Structural> (x,y) = (a,b) "
  unfolding StructuralTag_def Premise_def by simp
lemma [\<nu>intro0]: "<Structural> x = x" unfolding StructuralTag_def by fast
lemma [\<nu>intro]: "<Structural> x \<in> UNIV" unfolding StructuralTag_def by fast
lemma [\<nu>intro]: "<Structural> P x \<Longrightarrow> <Structural> x \<in> Collect P" unfolding StructuralTag_def by fast
lemma [\<nu>intro]: "<Structural> P x y \<Longrightarrow> <Structural> case_prod P (x,y)" unfolding StructuralTag_def by fast

definition op_pair :: "('a::lrep) \<times> ('b::lrep) \<times> ('r::stack) \<longmapsto> (('b \<times> 'a) \<times> 'r)"
  where "op_pair h x = (case x of (a,b,r) \<Rightarrow> Success h ((b,a),r))"
definition op_depair :: "(('b::lrep) \<times> ('a::lrep)) \<times> ('r::stack) \<longmapsto> ('a \<times> 'b \<times> 'r)"
  where "op_depair h x = (case x of ((b,a),r) \<Rightarrow> Success h (a,b,r))"
(* declare op_pair_def[\<nu>instr] op_depair_def[\<nu>instr] *)

theorem pr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B) \<brangle>" unfolding \<nu>def  op_pair_def by auto
theorem dpr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B) \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<brangle>" unfolding \<nu>def  op_depair_def by auto
(*
lemma pr_auto_schema: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c call op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<flower> W \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product>' B) \<flower> W \<brangle>"
  unfolding AutoFusion_def by (rule call) (rule pr_\<nu>proc)
lemma dpr_auto_schema: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c call op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product>' B) \<flower> W \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<flower> W \<brangle>"
  unfolding AutoFusion_def by (rule call) (rule dpr_\<nu>proc)
lemma pr_auto_schema': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product>' B) \<brangle>"
  unfolding AutoFusion_def by (rule pr_\<nu>proc)
lemma dpr_auto_schema': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product>' B) \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<brangle>"
  unfolding AutoFusion_def by (rule dpr_\<nu>proc)
*)
section \<open>Sugars\<close>

consts EmptyStack_sugar :: " 'sugar " ("\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k")
consts Register_sugar :: " 'i_am \<Rightarrow> 'just \<Rightarrow> 'a_sugar " ("(2_)//\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s\<^bold>: (2_)" [14,14] 13)

translations
  "R \<heavy_comma> x \<tycolon> N" == "R \<heavy_comma> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
  "x \<tycolon> N \<heavy_comma> R" == "\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<heavy_comma> R"
  "x" <= "x \<^bold>a\<^bold>n\<^bold>d CONST Void"
  "P" <= "CONST AndFact P (CONST NoFact)"
  "x" <= "CONST RegisterCollection (CONST End_of_Contextual_Stack R)\<heavy_comma> x"
  "x" <= "CONST End_of_Contextual_Stack R \<heavy_comma> x"
  "\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k" <= "CONST RegisterCollection (CONST End_of_Contextual_Stack R)"
  "CONST Register_sugar \<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k G" <= "CONST RegisterCollection G"
  "\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k" <= "CONST End_of_Contextual_Stack R"
  "CONST Register_sugar T G" <= "(CONST RegisterCollection G)\<heavy_comma> T"
  "CONST Register_sugar (T\<heavy_comma> U) G " <= "CONST Register_sugar T G \<heavy_comma> U"

translations "_linebreak_collection_ P Q" <= "CONST AndFact P Q"
translations "P" <= "CONST AndFact P (CONST NoFact)"

*)
section \<open>Main implementation of the system\<close>

ML_file_debug NuHelp.ML
ML_file "./general/binary_tree.ML"
ML_file "./general/auto_level.ML"
(* ML_file "./library/path.ML" *)
ML_file_debug NuBasics.ML
ML_file "./library/general.ML"
ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/procedure.ML"
ML_file "./library/exty.ML"
ML_file NuSys.ML
(* ML_file "./library/registers.ML" *)
ML_file "./library/processors.ML"
ML_file "./library/obtain.ML"
ML_file NuToplevel.ML 

section \<open>Attributes and Commands\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<nu>instr"}, NuInstructions.list_definitions #> map snd))  \<close>
attribute_setup \<nu>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<nu>-system\<close>

attribute_setup \<nu>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (NuProcessor.get_attr ctx name) (ctx,toks))
  || Scan.lift NuProcessor.process_attr\<close>
  \<open>Evaluate the \<nu>-system process or the process of the given processor on the target theorem\<close>

method_setup \<nu>resolve = \<open>let open Scan Parse in
  option (Attrib.thms -- option (lift ($$$ "(") |-- Attrib.thms --| lift ($$$ ")") -- (lift ($$$ "(") |-- Attrib.thms --| lift ($$$ ")")))) >> (fn ths => fn ctx =>
    Method.METHOD (fn th2 => NuSys.auto_resolve ths th2 ctx))
end\<close>

ML \<open>

local open Scan NuToplevel NuSys Parse 
val nustatement = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- opt_attribs -- Scan.repeat1 Parse.propp);
val structured_statement =
  nustatement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));
in

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>exty_simproc\<close> "setup the pecific simproc for \<^const>\<open>ExTy\<close>"
  (Parse.binding >> NuExTyp.set_simproc_cmd)

val statement1 = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.propp);
val requires_statement = Scan.optional (Parse.$$$ "requires" |-- Parse.!!! statement1) [];
val requires_opt1 = Scan.option (Parse.$$$ "requires" |-- Parse.term);
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- requires_statement) >>
        (fn ((((b,arg_ret),fixes),includes),preconds) =>  
            (begin_proc_cmd false b arg_ret fixes includes preconds)));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc'\<close> "begin a procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- requires_statement) >>
        (fn ((((b,arg_ret),fixes),includes),preconds) =>  
            (begin_proc_cmd true b arg_ret fixes includes preconds)));

val loop_variables = $$$ "var" |-- !!! vars;
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close> "begin a recursive procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term -- loop_variables -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- requires_opt1) >>
        (fn (((((b,arg_ret),lvars),fixes),includes),preconds) =>  
            (begin_rec_proc_cmd b arg_ret lvars fixes includes preconds)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finish\<close> "Finish the procedure construction"
    (Scan.succeed (Toplevel.end_proof NuToplevel.finish_proc_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>debug\<close> "The \<nu>construction"
    (Scan.succeed (Toplevel.proof (fn stat =>
      stat |> Proof.map_context (NuSys.load_specthm (Proof.the_fact stat)))))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>debug'\<close> "The \<nu>construction"
    (Scan.succeed (Toplevel.proof (fn stat =>
      stat |> Proof.map_context (NuSys.open_meta (Proof.the_fact stat)))))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>note\<close> "note command in \<nu> version"
    (Parse_Spec.name_facts >> (fn facts => Toplevel.proof (fn stat =>
      let val meta = Proof.the_fact stat
      in stat |> Proof.note_thmss_cmd facts |> Proof.set_facts [meta] end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<bullet>\<close> "The \<nu>construction"
    (fn toks => (Toplevel.proof (NuToplevel.process_cmd (toks @ [Token.eof])),
      if hd toks |> Token.is_eof then [Token.eof] else []))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>affirm\<close> "proof for premise"
    (Scan.succeed (Toplevel.proof' (snd oo NuToplevel.prove_prem)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>have\<close> "proof for premise"
    (and_list1 ((binding -- opt_attribs -- opt_attribs --| $$$ ":") -- and_list1 (prop -- repeat prop)) >>
      (Toplevel.proof' o (snd ooo NuToplevel.have_aux_cmd)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>obtain\<close> "generalized elimination"
    (Parse.parbinding -- Scan.optional (Parse.vars --| Parse.where_) [] -- structured_statement
      >> (fn ((a, b), (c, d, e)) => Toplevel.proof' (NuObtain.obtain_cmd a b c d e)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>choose\<close> "existential elimination"
    ( !!! vars --| $$$ "where" -- Scan.repeat1 Parse.prop
      >> (fn (b, c) => Toplevel.proof' (NuObtain.choose_cmd b c)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>choose2\<close> "existential elimination"
    ( Scan.repeat1 Parse.binding >> (Toplevel.proof o NuObtain.chooseV));


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>choose_quick\<close> "existential elimination"
    ( Scan.succeed (Toplevel.proof (NuObtain.obtain_quick_pairs)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "construct nested sub-procedure"
    (optional ($$$ "(" |-- and_list (binding -- opt_attribs) --| $$$ ")") [] >> (Toplevel.proof' o NuToplevel.begin_block_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "finish the nested sub-procedure construction"
    (Scan.succeed (Toplevel.proof' NuToplevel.end_block_cmd));

(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>reg\<close> "declare local registers"
    (Scan.repeat Parse.short_ident >> (fn names => Toplevel.proof (fn stat =>
      Proof.set_facts [Proof.the_fact stat |> NuRegisters.new_regs (Proof.context_of stat) names] stat))) *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<Longrightarrow>\<close> "name the star fact"
    (Parse.binding -- Parse.opt_attribs >> (Toplevel.proof o NuToplevel.name_star_fact_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>drop_fact\<close> "drop a fact"
    (Parse.list Parse.binding >> (fn names => Toplevel.proof (fold NuToplevel.drop_fact_cmd names)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor\<close> "define \<nu>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword) -- Parse.nat -- Parse.term -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
        >> NuProcessor.setup_cmd)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor_resolver\<close> "define \<nu>processor resolver"
      (Parse.binding -- Parse.nat -- (Parse.term -- Parse.for_fixes) -- Parse.name_position -- Scan.optional Parse.text ""
        >> (fn ((((b,precedence),pattern),facts),comment) => NuProcessors.setup_resolver b precedence pattern facts comment))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>overloads\<close> "declare procedure overloads"
    (and_list1 (binding -- Scan.optional Parse.text "") >>
        (fold (fn (b,s) => NuProcedure.declare_overloading b s #> #2)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>cast_overloads\<close> "declare cast overloads"
    (and_list1 (binding -- Scan.optional Parse.text "") >>
        (fold (fn (b,s) => NuProcedure.declare_overloading_cast b s #> #2)))

end
\<close>

attribute_setup intro_forall = \<open>Scan.lift (Scan.repeat Args.var) >> (fn tms =>
  Thm.rule_attribute [] (fn ctx => fn th => 
    let open Thm
    val vs = add_vars th []
    val foralls = map (fn tm => case find_first (fn v => #1 (dest_Var (term_of v)) = tm) vs
                  of SOME y => y | _ => error (#1 tm ^ " is not a var ")) tms
    in Drule.forall_intr_list foralls th end)) \<close>

attribute_setup \<nu>overload = \<open>Scan.lift (Parse.and_list1 NuProcedure.parser) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuProcedure.overload th) bindings))\<close>
attribute_setup \<nu>cast_overload = \<open>Scan.lift (Parse.and_list1 NuProcedure.parser) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuProcedure.overload_cast th) bindings))\<close>

section \<open>Processors\<close>

subsubsection \<open>Controls\<close>

\<nu>processor set_auto_level 10 \<open>PROP P\<close> \<open>(fn ctx => fn th => NuParse.auto_level_force #->
  (fn auto_level' => NuProcessor.process (AutoLevel.reduce auto_level' ctx) th #> (fn x => raise ProcessTerminated x)))\<close>

\<nu>processor repeat 12 \<open>PROP P\<close> \<open>let
    fun repeat n f x = if n <= 0 then x else ((repeat (n-1) f (f x)) handle _ => x)
  in fn ctx => fn th => Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*")
    >> (fn (tok,n) => fn _ => (case Int.fromString n of SOME n => funpow n | _ => repeat 32)
        (NuProcessor.process ctx #> (fn p => p [tok,Token.eof] |> #1)) th)
  end\<close>

subsubsection \<open>Essential functions\<close>

\<nu>processor accept_proc 300 \<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn th => Scan.succeed (fn _ => NuSys.accept_proc ctx th)\<close>

\<nu>processor move_fact 50 \<open>(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<addition> P)\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta RS @{thm move_fact_to_star1} handle THM _ => meta RS @{thm move_fact_to_star2})\<close>

\<nu>processor call 9000 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open> fn ctx => fn meta => NuProcedure.parser >> (fn binding => fn _ =>
    let open NuBasics NuSys
  val procs = NuProcedure.procedure_thm ctx binding
  (* val xa = hd procs |> Thm.concl_of |> auto_fusion_arity |> @{print}
  val meta =funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema} #> accept_proc ctx) meta
    handle THM _ => funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema'} #> accept_proc ctx) meta *)
val ctx = NuSys.load_specthm meta ctx
    in NuSys.apply_procs ctx procs meta end)\<close>

\<nu>processor cast 8900 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
  \<open> fn ctx => fn meta => (Parse.$$$ "cast" |-- (Parse.$$$ "(" |-- Parse.list NuProcedure.parser --| Parse.$$$ ")" || (NuProcedure.parser >> single)))
    >> (fn bindings => fn _ =>
      let val ctx = NuSys.load_specthm meta ctx
      in fold (NuSys.apply_casts ctx o NuProcedure.cast_thm ctx) bindings meta end)\<close>

\<nu>processor set_param 5000 \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Parse.term >> (fn term => fn _ =>
    NuSys.set_param ctx (Syntax.parse_term ctx term) meta)\<close>

\<nu>processor rule 8800 \<open>PROP P \<Longrightarrow> PROP Q\<close>
  \<open>fn ctx => fn meta => (NuProcedure.parser -- Parse.opt_attribs) >> (fn (name,attrs) => fn _ =>
    let open NuBasics
    val ctx = NuSys.load_specthm meta ctx
    val attrs = map (Attrib.attribute_cmd ctx o Attrib.check_src ctx) attrs
    val ths = Proof_Context.get_fact ctx (Facts.Named (name, NONE)) 
    val (ths,ctx) = fold_map (Thm.proof_attributes attrs) ths ctx
    in elim_SPEC meta |> apfst (fn major =>
    case Thm.biresolution NONE false (ths |> map (pair false) |> @{print}) 1 major |> Seq.pull
      of SOME (th, _) => th | _ => raise THM ("RSN: no unifiers", 1, major::ths)) |> intro_SPEC end)\<close>

\<nu>processor rule_by_COMP 1000 \<open>PROP P \<Longrightarrow> PROP Q\<close>
  \<open>fn ctx => fn meta => (Parse.$$$ "\<Longleftarrow>'" |-- NuProcedure.parser -- Parse.opt_attribs) >> (fn (name,attrs) => fn _ =>
    let open NuBasics
    val ctx = NuSys.load_specthm meta ctx
    val attrs = map (Attrib.attribute_cmd ctx o Attrib.check_src ctx) attrs
    val [th] = Proof_Context.get_fact ctx (Facts.Named (name, NONE)) 
    val ([th],ctx) = fold_map (Thm.proof_attributes attrs) [th] ctx
    in elim_SPEC meta |> apfst (fn major => th COMP major) |> intro_SPEC end)\<close>

\<nu>processor set_\<nu>current 100 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  raise Bypass (SOME (meta RS @{thm set_\<nu>current})))\<close>

\<nu>processor choose_AutoExTy 10 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n AutoExTyp T\<close> \<open>fn ctx => fn meta =>
  Parse.list1 Parse.binding >> (fn vars => fn () =>
    raise Process_State_Call' (meta, NuObtain.chooseV vars))\<close>

(* subsubsection \<open>Registers\<close>

\<nu>processor assign_register 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  (fn ctx => fn th => ($$$ "\<rightarrow>" |-- (short_ident >> single || $$$ "(" |-- list1 short_ident --| $$$ ")")) >>
    (fn idts => fn _ => fold_rev (fn idt =>
      NuRegisters.assign_reg ctx idt
        #> NuProcessor.process_no_input (AutoLevel.reduce 1 ctx)) idts th))
end\<close>
\<nu>processor  load_register 110 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  fn ctx => fn th => short_ident >> (fn idt => fn _ => NuRegisters.load_reg ctx idt th
      handle NuRegisters.NoSuchRegister _ => raise Bypass NONE)
end\<close>
\<nu>processor move_register 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  (fn ctx => fn th => (($$$ "\<leftarrow>" || $$$ "$") |-- (short_ident >> single || $$$ "(" |-- list1 short_ident --| $$$ ")")) >>
    (fn idts => fn _ => fold (fn idt => NuRegisters.move_reg ctx idt #> NuProcessor.process_no_input (AutoLevel.reduce 1 ctx)) idts th))
end\<close>
*)
subsubsection \<open>Simplifiers & Resonings\<close>

\<nu>processor \<nu>simplifier 40 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>NuProcessors.simplifier []\<close>
(* \<nu>processor \<nu>simplifier_final 9999 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close> *)

\<nu>processor \<nu>resolver 1000 \<open>PROP P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  NuSys.auto_resolve_rule NONE [] (NuSys.load_specthm meta ctx) meta
    handle NuSys.ReasoningFail _ => raise Bypass NONE)\<close>

subsubsection \<open>Literal operations\<close>

\<nu>processor literal_constructor 9500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.cartouche >> (fn term => fn _ =>
  let val term = Syntax.read_term ctx term |> Thm.cterm_of ctx |> Simplifier.rewrite ctx |> Thm.rhs_of
        val ctx = NuSys.load_specthm meta ctx
  in NuSys.auto_construct ctx term meta end)\<close>

\<nu>processor literal_number 9500\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.number >> (fn num => fn _ =>
  let open NuBasics
    val term = (stack_of_meta meta |> hd |> dest_RepSet |> dest_nuTy |> #2) handle TERM _ => @{term \<open>\<nat>[32]\<close>}
    val term = mk_nuTy (Syntax.parse_term ctx num, term) |> Syntax.check_term ctx |> Thm.cterm_of ctx
    val ctx = NuSys.load_specthm meta ctx
  in NuSys.auto_construct ctx term meta  end)
\<close>

\<nu>cast_overloads E I

end