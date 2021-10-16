(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrime NuLLReps
  keywords
    "proc" "proc'" "rec_proc" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "cast" "requires" "\<Longleftarrow>" "\<Longleftarrow>'" "$" "var" "always" :: quasi_command
  and "\<bullet>" "affirm" "\<nu>have" "\<nu>obtain" "\<nu>choose" "\<nu>choose2" "\<medium_left_bracket>" "\<medium_right_bracket>" "reg" "\<Longrightarrow>" "drop_fact" "\<nu>debug"
          "\<nu>note" "\<nu>choose_quick" :: prf_decl % "proof"
  and "\<nu>processor" "\<nu>processor_resolver" "\<nu>exty_simproc" :: thy_decl % "ML"
  and "\<nu>overloads" "\<nu>cast_overloads" :: thy_decl
  and "finish" :: "qed" % "proof"
abbrevs
  "!!" = "!!"
begin

section \<open>Preliminary constants and settings used in the system\<close>

named_theorems used \<open>theorems that will be inserted in ANY proof environments,
which basically has the same effect as the using command.\<close>
  and final_proc_rewrite \<open>rules used to rewrite the generated procedure theorem in the final stage\<close>
  and final_proc_rewrite2

lemmas [final_proc_rewrite] = Premise_Irew WorkingProtector_def
lemma [final_proc_rewrite2]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<nu>Zero N zr \<equiv> (\<nu>Zero N zr)" unfolding Premise_def .
  
definition  FailedPremise :: "bool \<Rightarrow> bool" where "FailedPremise \<equiv> Premise"
lemma FailedPremise_I: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> FailedPremise P" unfolding FailedPremise_def .
lemma FailedPremise_D: "FailedPremise P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding FailedPremise_def .

section \<open>Syntax\<close>

subsection \<open>Logical image models\<close>

text \<open>A set of models having common meanings, useful for representing logical images\<close>

consts val_of :: " 'a \<Rightarrow> 'b "
consts key_of :: " 'a \<Rightarrow> 'b "

datatype ('a, 'b) object (infixr "\<R_arr_tail>" 60) = object (key_of_obj: 'a) (val_of_obj: 'b) (infixr "\<R_arr_tail>" 60)
adhoc_overloading key_of key_of_obj and val_of val_of_obj

lemma object_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)

datatype ('a, 'b) owning (infixr "\<left_fish_tail>" 60) = owning (resources_of: 'a) (val_of_owning: 'b) (infixr "\<left_fish_tail>" 60)
adhoc_overloading val_of val_of_owning

lemma owning_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<left_fish_tail> x))" by (metis owning.exhaust)
lemma owning_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<left_fish_tail> x))" by (metis owning.exhaust)

section \<open>Mechanisms\<close>

subsection \<open>Register\<close>

definition AndTy :: " 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> ('a \<times> 'b) \<nu>set " (infixr "\<^bold>a\<^bold>n\<^bold>d" 3)  where  "(A \<^bold>a\<^bold>n\<^bold>d B) = (\<lambda>res. A res \<times> B res)"
lemma [simp]: "(a, b) \<in> (A \<^bold>a\<^bold>n\<^bold>d B) res \<longleftrightarrow> a \<in> A res \<and> b \<in> B res" unfolding AndTy_def by simp
lemma [intro]: "a \<in> A res \<Longrightarrow> b \<in> B res \<Longrightarrow> (a, b) \<in> (A \<^bold>a\<^bold>n\<^bold>d B) res" by simp
lemma [elim]: "ab \<in> (A \<^bold>a\<^bold>n\<^bold>d B) res \<Longrightarrow> (\<And>a b. ab = (a, b) \<Longrightarrow> a \<in> A res \<Longrightarrow> b \<in> B res \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding AndTy_def by (cases ab) simp
lemma [elim!,\<nu>elim]: "Inhabited (A \<^bold>a\<^bold>n\<^bold>d B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<nu>Resources_of_set A as \<Longrightarrow> \<nu>Resources_of_set B bs \<Longrightarrow> \<nu>Resources_of_set (A \<^bold>a\<^bold>n\<^bold>d B) (as \<union> bs)"
  unfolding \<nu>Resources_of_set_def  by auto

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A \<^bold>a\<^bold>n\<^bold>d B) \<longmapsto> (A' \<^bold>a\<^bold>n\<^bold>d B') \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<and> Q"
  unfolding Cast_def by auto
lemma StackDelimiter_to_AndTy: " (A\<heavy_comma> B) \<equiv> (B \<^bold>a\<^bold>n\<^bold>d A) " unfolding Stack_Delimiter_def AndTy_def by simp

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


definition AdrGet :: " ('a,'b,'x,'y) index \<Rightarrow> 'x \<nu>set \<Rightarrow> 'a \<nu>set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<blangle> _ \<^bold>@ _ \<brangle>)" [101,4,4] 100)
  where [\<nu>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<blangle> X \<^bold>@ A \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx adr \<blangle> A \<longmapsto> X \<brangle>"
definition AdrMap :: " ('a,'b,'x,'y) index \<Rightarrow> 'x \<nu>set \<Rightarrow> 'a \<nu>set \<Rightarrow> 'y \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<blangle> _ \<^bold>@ _ \<longmapsto> _ \<^bold>@ _ \<brangle>)" [101,4,4,4,4] 100)
  where [\<nu>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx idx \<blangle> A \<longmapsto> X \<brangle> \<and>
    (\<forall>f h. (\<forall>a. a \<in> X h \<longrightarrow> f a \<in> Y h) \<longrightarrow> (\<forall>a. a \<in> A h \<longrightarrow> map_idx idx f  a \<in> B h))"
declare Map_def[\<nu>index_def]

lemma index_here_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>index_def  index_here_def by auto
lemma index_here_mapper[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>index_def  index_here_def by auto
lemma index_left_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left f \<blangle> X \<^bold>@ (A \<^bold>a\<^bold>n\<^bold>d R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases f) auto
lemma index_right_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d A) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto
lemma index_stack_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (A\<heavy_comma> N) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto
lemma index_left_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left f \<blangle> X \<^bold>@ (A \<^bold>a\<^bold>n\<^bold>d R) \<longmapsto> Y \<^bold>@ (B \<^bold>a\<^bold>n\<^bold>d R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases f) auto
lemma index_right_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d A) \<longmapsto> Y \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d B) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto
lemma index_stack_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (A\<heavy_comma> N) \<longmapsto> Y \<^bold>@ (B\<heavy_comma> N) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto

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

subsection \<open>Structural Pairs\<close>

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def .

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

theorem pr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion> B) \<brangle>" unfolding \<nu>def  op_pair_def by auto
theorem dpr_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion> B) \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<brangle>" unfolding \<nu>def  op_depair_def by auto
(*
lemma pr_auto_schema: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c call op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<flower> W \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<flower> W \<brangle>"
  unfolding AutoFusion_def by (rule call) (rule pr_\<nu>proc)
lemma dpr_auto_schema: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c call op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<flower> W \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<flower> W \<brangle>"
  unfolding AutoFusion_def by (rule call) (rule dpr_\<nu>proc)
lemma pr_auto_schema': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<brangle>"
  unfolding AutoFusion_def by (rule pr_\<nu>proc)
lemma dpr_auto_schema': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B \<brangle>"
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


section \<open>Main implementation of the system\<close>

ML_file_debug NuHelp.ML
ML_file "./general/binary_tree.ML"
ML_file "./general/auto_level.ML"
ML_file "./library/path.ML"
ML_file_debug NuBasics.ML
ML_file "./library/general.ML"
ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/procedure.ML"
ML_file "./library/exty.ML"
ML_file NuSys.ML
ML_file "./library/registers.ML"
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
    ((Parse_Spec.opt_thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- requires_statement) >>
        (fn (((((b,arg),ret),fixes),includes),preconds) =>  
            (begin_proc_cmd false b arg ret fixes includes preconds)));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc'\<close> "begin a procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- requires_statement) >>
        (fn (((((b,arg),ret),fixes),includes),preconds) =>  
            (begin_proc_cmd true b arg ret fixes includes preconds)));

val loop_variables = $$$ "var" |-- !!! vars;
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close> "begin a recursive procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- loop_variables -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- requires_opt1) >>
        (fn ((((((b,arg),ret),lvars),fixes),includes),preconds) =>  
            (begin_rec_proc_cmd b arg ret lvars fixes includes preconds)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finish\<close> "Finish the procedure construction"
    (Scan.succeed (Toplevel.end_proof NuToplevel.finish_proc_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>debug\<close> "The \<nu>construction"
    (Scan.succeed (Toplevel.proof (fn stat =>
      stat |> Proof.map_context (NuSys.load_specthm (Proof.the_fact stat)))))

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

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>reg\<close> "declare local registers"
    (Scan.repeat Parse.short_ident >> (fn names => Toplevel.proof (fn stat =>
      Proof.set_facts [Proof.the_fact stat |> NuRegisters.new_regs (Proof.context_of stat) names] stat)))

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

\<nu>processor rule 1000 \<open>PROP P \<Longrightarrow> PROP Q\<close>
  \<open>fn ctx => fn meta => (Parse.$$$ "\<Longleftarrow>" |-- NuProcedure.parser -- Parse.opt_attribs) >> (fn (name,attrs) => fn _ =>
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

subsubsection \<open>Registers\<close>

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

subsubsection \<open>Simplifiers & Resonings\<close>

\<nu>processor \<nu>simplifier 40 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>NuProcessors.simplifier []\<close>
(* \<nu>processor \<nu>simplifier_final 9999 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close> *)

\<nu>processor \<nu>resolver 9000 \<open>PROP P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  NuBasics.elim_SPEC meta |> apfst (fn major =>
  case Seq.pull (NuSys.auto_resolve NONE [] (NuSys.load_specthm meta ctx) major)
    of SOME (major', _) => major' | _ => raise Bypass NONE) |> NuBasics.intro_SPEC)\<close>

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