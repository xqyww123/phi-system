(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrime
  keywords
    "proc" "rec_proc" "\<nu>cast" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "cast" "requires" "\<Longleftarrow>" "\<Longleftarrow>'" "$" "var" "always"  "\<medium_left_bracket>" "\<medium_right_bracket>" "i.e." :: quasi_command
  and "\<bullet>" "affirm" "\<nu>have" "\<nu>obtain" "\<Longrightarrow>" "drop_fact" "\<nu>debug" "\<nu>debug'"
          "\<nu>note" (* "\<nu>choose_quick" *) :: prf_decl % "proof"
  and "\<nu>processor" "\<nu>processor_resolver" "\<nu>reasoner" "setup_\<nu>application_method" :: thy_decl % "ML"
  and "\<nu>overloads" :: thy_decl
  and "finish" :: "qed" % "proof"
abbrevs
  "!!" = "!!"
  and "<implies>" = "\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s"
  and "<argument>" = "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t"
begin

section \<open>Prelude of the Prelude\<close>

subsection \<open>Preliminary constants and settings\<close>

named_theorems used \<open>theorems that will be inserted in ANY proof environments,
which basically has the same effect as the using command.\<close>
  and final_proc_rewrite \<open>rules used to rewrite the generated procedure theorem in the final stage\<close>
  and final_proc_rewrite2

lemmas [final_proc_rewrite] = WorkingProtector_def
lemma [final_proc_rewrite2]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<nu>Zero N zr \<equiv> (\<nu>Zero N zr)" unfolding Premise_def .
  
definition  FailedPremise :: "bool \<Rightarrow> bool" where "FailedPremise \<equiv> Premise"
lemma FailedPremise_I: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> FailedPremise P" unfolding FailedPremise_def .
lemma FailedPremise_D: "FailedPremise P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding FailedPremise_def .

attribute_setup rotated = \<open>Scan.lift (Scan.optional Parse.int 1 -- Scan.optional Parse.int 0) >>
  (fn (k,j) => Thm.rule_attribute [] (fn _ => Thm.permute_prems j k))\<close>
  \<open>Enhanced version of the Pure.rotated\<close>

subsection \<open>Prelude ML programs\<close>

ML_file NuHelp.ML
ML_file \<open>library/NuSimpCongruence.ML\<close>
ML_file \<open>library/cost_net.ML\<close>


subsection \<open>Overload\<close>

ML_file \<open>library/applicant.ML\<close>

attribute_setup \<nu>overload = \<open>Scan.lift (Parse.and_list1 NuApplicant.parser) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuApplicant.overload th) bindings))\<close>

\<nu>overloads D \<open>Destructural cast\<close>


subsection \<open>\<nu> Reasoner\<close>

definition "\<nu>Intro_Rule x = x"
definition "\<nu>Elim_Rule x = x"
definition "\<nu>Application_Rule x = x"

ML_file \<open>library/reasoner.ML\<close>

\<nu>reasoner "Different A B" -1 = \<open>let open NuHelp in
  fn _ => fn th =>
  case try Thm.major_prem_of th
    of SOME prem =>
      (case try (dest_monop @{const_name Trueprop} #> dest_binop @{const_name "Different"}) prem
        of SOME (a,b) =>
          if Term.aconv (a,b) then Seq.empty else Seq.single (@{thm Different_I} RS th)
         | _ => Seq.empty)
     | _ => Seq.empty
end\<close>

attribute_setup \<nu>intro =
\<open>(Scan.lift (Scan.optional (Parse.int >> ~) ~100) >> Nu_Reasoner.attr_add_intro)
  || (Scan.lift (Args.add |-- (Parse.int >> ~)) >> Nu_Reasoner.attr_add_intro)
  || (Scan.lift Args.del >> K Nu_Reasoner.attr_del_intro)\<close>
  \<open>Set introduction rules in \<nu> reasonser.
  Syntax: \<nu>intro [add] <spur-of-the-rule> || \<nu>intro del\<close>

attribute_setup \<nu>reasoner_elim =
\<open>(Scan.lift (Parse.int >> ~) >> Nu_Reasoner.attr_add_elim)
  || (Scan.lift (Args.add |-- (Parse.int >> ~)) >> Nu_Reasoner.attr_add_elim)
  || (Scan.lift Args.del >> K Nu_Reasoner.attr_del_elim)\<close>
  \<open>Set elimduction rules in \<nu> reasonser.
  Syntax: \<nu>reasoner_elim [add] <spur-of-the-rule> || \<nu>elim del\<close>


declare conjI[\<nu>intro] TrueI[\<nu>intro 300]

(* ML \<open>Nu_Reasoner.reasoners @{context}\<close>

ML \<open>val th = Goal.init @{cprop "Q \<and> True \<and> A"}
  val th2 = Nu_Reasoner.reason @{context} th\<close> *)

section \<open>Syntax\<close>

subsection \<open>Syntax Helper\<close>

ML \<open>
fun parse_typing_ty (Type (\<^type_name>\<open>typing\<close>, [a,b])) = (b, a --> b --> \<^typ>\<open>bool\<close>)
  | parse_typing_ty dummyT = (dummyT, dummyT)
  | parse_typing_ty ty = raise TYPE ("should be a typing type", [ty], [])

fun parse_typing (Free (name, ty)) =
    Const (\<^const_syntax>\<open>typing\<close>, ty) $ Free (name^"\<^sub>x", fst (parse_typing_ty ty))
        $ Free (name^"\<^sub>t\<^sub>y", snd (parse_typing_ty ty))
  | parse_typing (Var ((name,ind), ty)) =
    Const (\<^const_syntax>\<open>typing\<close>, ty) $ Var ((name^"\<^sub>x",ind), fst (parse_typing_ty ty))
        $ Var ((name^"\<^sub>t\<^sub>y", ind), snd (parse_typing_ty ty))
  | parse_typing (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tm $ (Const (\<^type_syntax>\<open>typing\<close>, _) $ tya $ tyb)) =
      let val (const $ tmx $ tmty) = parse_typing tm
      in const $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmx $ tyb)
        $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmty $ (Const (\<^type_syntax>\<open>\<nu>\<close>, dummyT) $ tya $ tyb)) end
  | parse_typing (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tm $ markup) =
      let val (const $ tmx $ tmty) = parse_typing tm
      in const $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmx $ markup)
        $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmty $ markup) end
  | parse_typing (tm as Const (\<^const_syntax>\<open>typing\<close>, _) $ _ $ _) = tm
  | parse_typing tm = raise TERM ("should be a NuPrime.typing term", [@{print} tm])

fun parse_typing_x tm = (case parse_typing tm of _ $ x $ _ => x)
fun parse_typing_ty tm = (case parse_typing tm of _ $ _ $ ty => ty)
\<close>

syntax "_\<nu>typing" :: " logic \<Rightarrow> logic "
  "_\<nu>typing_x" :: " logic \<Rightarrow> logic "
  "_\<nu>typing_ty" :: " logic \<Rightarrow> logic "
parse_translation \<open>[
  (\<^syntax_const>\<open>_\<nu>typing\<close>, (fn _ => fn [tm] => parse_typing tm)),
  (\<^syntax_const>\<open>_\<nu>typing_x\<close>, (fn _ => fn [tm] => parse_typing_x tm)),
  (\<^syntax_const>\<open>_\<nu>typing_ty\<close>, (fn _ => fn [tm] => parse_typing_ty tm))
]\<close>


subsection \<open>Logical image models\<close>

text \<open>A set of models having common meanings, useful for representing logical images\<close>

consts val_of :: " 'a \<Rightarrow> 'b "
consts key_of :: " 'a \<Rightarrow> 'b "

datatype ('a, 'b) object (infixr "\<R_arr_tail>" 60) = object (key_of_obj: 'a) (val_of_obj: 'b) (infixr "\<R_arr_tail>" 60)
adhoc_overloading key_of key_of_obj and val_of val_of_obj
declare object.split[split]

lemma object_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_All[lrep_exps]: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a \<R_arr_tail> b))" 
proof fix a b assume "(\<And>x. PROP P x) " then show "PROP P (a \<R_arr_tail> b)" .
next fix x assume "\<And>a b. PROP P (a \<R_arr_tail> b)"
    from \<open>PROP P (key_of x \<R_arr_tail> val_of x)\<close> show "PROP P x" by simp
qed



section \<open>Mechanisms - I\<close>

subsection \<open>Congruence Rule\<close>

(* lemma mk_\<nu>cong1: "\<tort_lbrace>x \<tycolon> T\<tort_rbrace> = \<tort_lbrace>x' \<tycolon> T'\<tort_rbrace> \<equiv> T x = T' x'"
  unfolding atomize_eq RepSet_def unfolding atomize_eq by (auto simp add: atomize_eq)
lemma mk_\<nu>cong2: "(\<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> T'\<tort_rbrace>) \<equiv> (T x \<equiv> T' x')"
  unfolding atomize_eq by rule (simp add: mk_\<nu>cong1)+

attribute_setup \<nu>cong = \<open>let open Simplifier
  fun attrib f = Thm.declaration_attribute (map_ss o f)
  fun mk f th ctx = f (rewrite_rule ctx @{thms mk_\<nu>cong1 mk_\<nu>cong2} th) ctx
  val cong_add = attrib (mk add_cong)
  val cong_del = attrib (mk del_cong)
in Attrib.add_del cong_add cong_del end\<close>
  \<open>declaration of Simplifier congruence rule for the form \<^term>\<open>\<tort_lbrace>x \<tycolon> T\<tort_rbrace> = \<tort_lbrace>x' \<tycolon> T'\<tort_rbrace>\<close>\<close> *)

subsection \<open>Cast\<close>

definition Cast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P)"
consts SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _)" [13,13] 12)
translations "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True)"

definition CastDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13,13] 12)
  where "CastDual A B P A' B' \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P \<and> (\<forall>u. u \<in> A' \<longrightarrow> u \<in> B'))"
  \<comment> \<open>Intuitively, \<^term>\<open>CastDual A B P A' B' \<longleftrightarrow> (\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<and> (Inhabited A \<longrightarrow> (\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> B'))\<close>\<close>

consts SimpCastDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13] 12)
translations
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'"

translations
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l a' \<tycolon> A' \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<tort_lbrace>a' \<tycolon> A'\<tort_rbrace> \<longmapsto> B'"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> b' \<tycolon> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> \<tort_lbrace>b' \<tycolon> B'\<tort_rbrace>"

lemma cast_id[\<nu>intro 2000]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" unfolding Cast_def by fast
lemma cast_dual_id[\<nu>intro 2000]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B"
  unfolding CastDual_def Intro_def Dest_def by (simp add: cast_id)


text \<open>There are 3 kinds of the Cast, corresponding 3 usages where the prefix `some_`
means the variable *can* be schematic (which is unknown in the reasoning) while other variables
are decided (non-schematic),
  \<^item> \<^term>\<open>\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t some_x \<tycolon> T \<longmapsto> some_y \<tycolon> some_U\<close>,
  \<^item> \<^term>\<open>\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t some_y \<tycolon> some_U \<longmapsto> some_x \<tycolon> T\<close>,
  \<^item> \<^term>\<open>\<^bold>c\<^bold>a\<^bold>s\<^bold>t some_x \<tycolon> T \<longmapsto> some_y \<tycolon> U\<close>
To illustrate, by @{thm cast_id} the reasoning on `cast x \<tycolon> T \<longmapsto> ?y \<tycolon> ?U` always results in trivial `cast x \<tycolon> T \<longmapsto> x \<tycolon> T`,
  where as that on `dest cast x \<tycolon> T \<longmapsto> ?y \<tycolon> ?U` is meaningful by absence of that self-loop rule,
  e.g. `dest cast x \<tycolon> T <where> P \<longmapsto> x \<tycolon> T with x \<in> P`.
Actually, to prevent reasoning loop all the `dest cast` must constitute a DAG in the direct of destruction,
  while `intro cast` is that of construction.
\<close>

lemma [\<nu>intro 30]: "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t B' \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Intro_def Cast_def by auto
lemma [\<nu>intro 30]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<Longrightarrow> (P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2"
  unfolding Dest_def Cast_def by auto

lemma [\<nu>intro 10]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l C \<longmapsto> C"
  unfolding Cast_def CastDual_def Premise_def Dest_def Intro_def by simp


(* abbreviation SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<equiv> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h True)" *)
(* lemma CastE[elim]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Cast_def Inhabited_def by (auto intro: Inhabited_subset)
lemma CastI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Cast_def Inhabited_def by auto *)

lemma ie_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma as_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> \<tort_lbrace>X'\<tort_rbrace> \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> \<tort_lbrace>X'\<tort_rbrace>" .
lemma [\<nu>intro 300]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N" unfolding Cast_def Premise_def by simp
lemma [\<nu>intro 2000]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x" unfolding Premise_def by simp

lemma cast_trans: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def by auto
lemma cast_dual_trans: 
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>d\<^bold>u\<^bold>a\<^bold>l B' \<longmapsto> A' \<Longrightarrow> (P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l C' \<longmapsto> B')
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l C' \<longmapsto> A'"
  unfolding Cast_def CastDual_def Intro_def Dest_def by auto

(* lemma dual_cast_fallback[\<nu>intro']: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<and> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t C \<longmapsto> C)" unfolding Cast_def by fast *)

subsection \<open>Tags\<close>

subsubsection \<open>Explicit name tag\<close>

definition Labelled :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "Labelled name x = x" \<comment>\<open>name tag\<close>
consts "named_sugar" :: " 'i_am \<Rightarrow> 'merely \<Rightarrow> 'a_sugar " ("\<ltbrak>_\<rtbrak>. _" [10,15] 14)
translations
  "\<ltbrak>name\<rtbrak>. x \<tycolon> T" == "x \<tycolon> (\<ltbrak>name\<rtbrak>. T)"
  "\<ltbrak>name\<rtbrak>. x" == "CONST Labelled (LABEL name) x"

lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..
lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..

subsubsection \<open>Hidden name hint\<close>

definition NameHint :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "NameHint name x = x" \<comment>\<open>name tag\<close>
translations "X" <= "CONST NameHint name X"


subsubsection \<open>Auto tag\<close>

definition Auto :: " 'a \<Rightarrow> 'a " where "Auto x = x"

lemma [\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> x \<tycolon> Auto T" unfolding Auto_def Intro_def using cast_id .

lemma Auto_cong: "\<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> T'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>x \<tycolon> Auto T\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> Auto T'\<tort_rbrace>" unfolding atomize_eq Auto_def .
simproc_setup Auto_cong ("\<tort_lbrace>x \<tycolon> Auto T\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm Auto_cong})\<close>


subsubsection \<open>Argument tag\<close>

definition Argument :: "'a \<Rightarrow> 'a" ("\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _" [11] 10) where "Argument x = x"

lemma Argument_I: "P \<Longrightarrow> Argument P" unfolding Argument_def .

text \<open>Sequent in pattern \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P \<Longrightarrow> PROP Q\<close> hints users to input a theorem \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> P\<close>
  in order to deduce the sequent into \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> PROP Q\<close>, which is achieved by the `rule` processor.
  Argument servers as a protector to prevent the unexpected auto-reasoning, e.g., the case for cast where
  the reasoner always attempts to solve an unprotected case premises and `Argument` tagging the Cast in this case
  prevent this automatic behavior when expecting user to input the cast rule.\<close>



subsection \<open>Case Analysis\<close>

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e A = B x y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e A = case_prod B (x,y)" by simp
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e A = B x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e A = case_named B (tag x)" by simp
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e A = B a x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e A = case_object B (a \<R_arr_tail> x)" by simp

definition CaseSplit :: "bool \<Rightarrow> bool" where "CaseSplit x = x"
lemma [elim!]: "CaseSplit x \<Longrightarrow> (x \<Longrightarrow> C) \<Longrightarrow> C" unfolding CaseSplit_def .

 lemma [elim!]:
  "y = case_prod f x \<Longrightarrow> (\<And>x1 x2. y = f x1 x2 \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of a \<R_arr_tail> b \<Rightarrow> f a b) \<Longrightarrow> (\<And>a b. y = f a b \<Longrightarrow> C (a \<R_arr_tail> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of tag a \<Rightarrow> f a) \<Longrightarrow> (\<And>a. y = f a \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp

(* lemma [\<nu>reasoner_elim 10002]:
  "CaseSplit (y = case_prod f x) \<Longrightarrow> (\<And>x1 x2. CaseSplit (y = f x1 x2) \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [\<nu>reasoner_elim 10002]:
  "CaseSplit (y = (case x of a \<R_arr_tail> b \<Rightarrow> f a b)) \<Longrightarrow> (\<And>a b. CaseSplit (y = f a b) \<Longrightarrow> C (a \<R_arr_tail> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [\<nu>reasoner_elim 10002]:
  "CaseSplit (y = (case x of tag a \<Rightarrow> f a)) \<Longrightarrow> (\<And>a. CaseSplit (y = f a) \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp*)


section \<open>Essential Low Models\<close>

class field = lrep \<comment> \<open>a field in the record tuple\<close>
class field_list = lrep

subsection \<open>Void\<close>

datatype void = void
declare void.split[split]

lemma [simp]: "x = y" for x :: void by (cases x; cases y) fast

subsubsection \<open>Settings\<close>

instantiation void :: stack begin
definition llty_void :: "void itself \<Rightarrow> llty" where "llty_void _ = llty_nil"
definition deepize_void :: "void \<Rightarrow> deep_model" where "deepize_void _ = DM_none"
instance by standard auto 
end

instantiation void :: field begin instance by standard end
instantiation void :: field_list begin instance by standard end

instantiation void :: zero begin
definition zero_void :: "void" where [simp]: "zero_void = void"
instance by standard
end


subsubsection \<open>Abstractor\<close>

definition NuVoid :: "(void, unit) \<nu>" where "NuVoid _ = UNIV"
text \<open>The name `void` coincides that, when a procedure has no input arguments,
  the \<nu>-type for the input would exactly be @{term Void}. \<close>

consts Void_sugar :: " 'a_sugar " ("Void")
translations "Void" == "() \<tycolon> CONST NuVoid"

lemma [nu_exps]: "p \<nuLinkL> NuVoid \<nuLinkR> x" unfolding NuVoid_def Refining_def by simp
lemma [elim!, \<nu>elim]: "Inhabited \<tort_lbrace>Void\<tort_rbrace> \<Longrightarrow> C \<Longrightarrow> C" by simp
(*translations "a" <= "a \<^bold>a\<^bold>n\<^bold>d CONST Void"*)

subsection \<open>Prod & the pair abstract structure\<close>

instantiation prod :: (field, field_list) field_list begin instance by standard end

instantiation prod :: (zero, zero) zero begin
definition zero_prod :: "'a \<times> 'b" where [simp]: "zero_prod = (0,0)"
instance by standard
end
instantiation prod :: (ceq, ceq) ceq begin
definition ceqable_prod :: "heap \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceqable_prod heap = ceqable heap \<times>\<^sub>r ceqable heap"
lemma [simp]: "ceqable heap (a1,b1) (a2,b2) \<longleftrightarrow> ceqable heap a1 a2 \<and> ceqable heap b1 b2" unfolding ceqable_prod_def by auto
definition ceq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceq_prod = ceq \<times>\<^sub>r ceq"
lemma [simp]: "ceq (a1,b1) (a2,b2) \<longleftrightarrow> ceq a1 a2 \<and> ceq b1 b2" unfolding ceq_prod_def by auto
instance by standard (auto intro: ceq_trans)
end


section \<open>Essential \<nu>-abstractor\<close>

subsection \<open>Separation Conjecture\<close>

definition disjoint :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " (infixl "\<perpendicular>" 60) where "disjoint A B \<longleftrightarrow> (A \<inter> B = {})"
lemma disjoint_rewL: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<notin> B)" unfolding disjoint_def by auto
lemma disjoint_rewR: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> B \<longrightarrow> x \<notin> A)" unfolding disjoint_def by auto
lemma [elim]: "A \<perpendicular> B \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False) \<Longrightarrow> C) \<Longrightarrow> C" unfolding disjoint_def by auto

lemma [iff]: "{} \<perpendicular> S" and [iff]: "S \<perpendicular> {}" unfolding disjoint_def by auto

definition Separation :: " (heap, 'a) \<nu> \<Rightarrow> (heap, 'b) \<nu> \<Rightarrow> (heap, 'a \<times> 'b) \<nu>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b) . {h. (\<exists>h2 h1. h = h2 ++ h1 \<and> dom h2 \<perpendicular> dom h1 \<and> (h1 \<nuLinkL> A \<nuLinkR> a) \<and> (h2 \<nuLinkL> B \<nuLinkR> b))})"

lemma Separation_exp[nu_exps]: "h \<nuLinkL> A \<^emph> B \<nuLinkR> (a,b) \<longleftrightarrow>
  (\<exists>h2 h1. h = h2 ++ h1 \<and> dom h2 \<perpendicular> dom h1 \<and> (h1 \<nuLinkL> A \<nuLinkR> a) \<and> (h2 \<nuLinkL> B \<nuLinkR> b))"
  unfolding Separation_def Refining_def by simp

definition Heap_Delimiter :: "(heap,'ax) \<nu> \<Rightarrow> (heap,'bx) \<nu> \<Rightarrow> (heap, 'ax \<times> 'bx) \<nu>" (infixr "<heap-sep>" 70)
  where "A <heap-sep> B = A \<^emph> B"
consts Heap_Delimiter_sugar :: " 'just \<Rightarrow> 'a \<Rightarrow> 'sugar " ( "_/ \<heavy_asterisk> _" [14,15] 14) \<comment> \<open>It is left associative!\<close>

translations " (a \<tycolon> A) \<heavy_asterisk> (b \<tycolon> B) " \<rightleftharpoons> " (CONST Pair b a) \<tycolon> (B <heap-sep> A) "
  " A \<heavy_asterisk> B " => " (CONST Pair (_\<nu>typing_x B) (_\<nu>typing_x A)) \<tycolon> ((_\<nu>typing_ty B) <heap-sep> (_\<nu>typing_ty A)) "

lemma Heap_Delimiter_cong: "\<tort_lbrace>h1 \<tycolon> H1\<tort_rbrace> \<equiv> \<tort_lbrace>h1' \<tycolon> H1'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>h2 \<tycolon> H2\<tort_rbrace> \<equiv> \<tort_lbrace>h2' \<tycolon> H2'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>h1 \<tycolon> H1 \<heavy_asterisk> h2 \<tycolon> H2\<tort_rbrace> \<equiv> \<tort_lbrace>h1' \<tycolon> H1' \<heavy_asterisk> h2' \<tycolon> H2'\<tort_rbrace>"
  unfolding atomize_eq Heap_Delimiter_def by (auto 0 5 simp add: nu_exps)
simproc_setup Heap_Delimiter_cong ("\<tort_lbrace>h1 \<tycolon> H1 \<heavy_asterisk> h2 \<tycolon> H2\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm Heap_Delimiter_cong})\<close>



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




definition SeparationSet :: " heap set \<Rightarrow> heap set \<Rightarrow> heap set" (infixr "<sep-set>" 70)
  where "A <sep-set> B = {h. (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> h1 \<in> A \<and> h2 \<in> B)}"
lemma HeapDivNu_to_SepSet: "\<tort_lbrace> h1 \<tycolon> H1 \<heavy_asterisk> h2 \<tycolon> H2 \<tort_rbrace> = \<tort_lbrace> h1 \<tycolon> H1 \<tort_rbrace> <sep-set> \<tort_lbrace> h2 \<tycolon> H2 \<tort_rbrace>"
  unfolding SeparationSet_def Heap_Delimiter_def by (auto 4 4 simp add: nu_exps)
lemma SepNu_to_SepSet: "\<tort_lbrace> (h2,h1) \<tycolon> H2 \<^emph> H1 \<tort_rbrace> = \<tort_lbrace> h1 \<tycolon> H1 \<tort_rbrace> <sep-set> \<tort_lbrace> h2 \<tycolon> H2 \<tort_rbrace>"
  unfolding SeparationSet_def Heap_Delimiter_def by (auto 4 4 simp add: nu_exps)

lemma SeparationSet_comm: " A <sep-set> B = B <sep-set> A" unfolding SeparationSet_def
  by (auto 4 4 simp add: disjoint_def inf_commute dest: map_add_comm )
lemma Separation_comm: " \<tort_lbrace> A \<heavy_asterisk> B\<tort_rbrace> = \<tort_lbrace> B \<heavy_asterisk> A\<tort_rbrace>"
  unfolding HeapDivNu_to_SepSet using SeparationSet_comm by fast

lemma SeparationSet_assoc: " (A <sep-set> B) <sep-set> C = A <sep-set> B <sep-set> C"
  unfolding SeparationSet_def
  by (auto simp add: disjoint_def) (metis (no_types, lifting) Un_empty dom_map_add inf_sup_distrib1 inf_sup_distrib2 map_add_assoc)+
lemma Separation_assoc: "\<tort_lbrace> A \<heavy_asterisk> (B \<heavy_asterisk> C)\<tort_rbrace> = \<tort_lbrace> A \<heavy_asterisk> B \<heavy_asterisk> C\<tort_rbrace>"
  unfolding HeapDivNu_to_SepSet using SeparationSet_assoc by fast

(* lemma NonSeparation_distrib_L: "h \<in> (A \<heavy_asterisk> (B \<dbl_and> P)) \<Longrightarrow> h \<in> (A \<heavy_asterisk> B \<dbl_and> P)"
  using map_le_map_add map_le_trans by blast
lemma NonSeparation_distrib_R: "h \<in> ((A \<dbl_and> P) \<heavy_asterisk> B) \<Longrightarrow> h \<in> (A \<heavy_asterisk> B \<dbl_and> P)"
  by (metis NonSeparation_distrib_L Separation_comm) *)
  

lemma [elim!,\<nu>elim]: "Inhabited \<tort_lbrace>a \<tycolon> A \<heavy_asterisk> b \<tycolon> B\<tort_rbrace> \<Longrightarrow> (a \<ratio> A \<Longrightarrow> b \<ratio> B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def Heap_Delimiter_def by (simp add: nu_exps) blast
(* lemma [elim!,\<nu>elim]: "Inhabited (A \<dbl_and> B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by auto *)

subsection \<open>Top Context\<close> \<comment> \<open>The pair of heap and stack\<close>

definition NuTopCtx :: " (heap, 'hx) \<nu> \<Rightarrow> ('s :: stack, 'sx) \<nu> \<Rightarrow> (heap \<times> 's, 'hx \<times> 'sx) \<nu> " (infix "<top-ctx>" 59)
  where "(H <top-ctx> S) = (\<lambda>(h,s). {(hp,sp). (hp \<nuLinkL> H \<nuLinkR> h) \<and> (sp \<nuLinkL> S \<nuLinkR> s) \<and> Heap hp})"
consts "NuTopCtx_sugar" :: " 'just \<Rightarrow> 'a \<Rightarrow> 'sugar " ( "_ \<heavy_comma>/ \<^bold>h\<^bold>e\<^bold>a\<^bold>p _" [10,14] 13)
translations "(s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H)" \<rightleftharpoons> "(CONST Pair h s) \<tycolon> CONST NuTopCtx H S"
  "(S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H)" => "(_\<nu>typing_x H, _\<nu>typing_x S) \<tycolon> CONST NuTopCtx (_\<nu>typing_ty H) (_\<nu>typing_ty S)"

lemma [nu_exps]: " ((hp, sp) \<nuLinkL> H <top-ctx> S  \<nuLinkR> (h, s)) \<longleftrightarrow> (hp \<nuLinkL> H  \<nuLinkR> h) \<and> (sp \<nuLinkL> S  \<nuLinkR> s) \<and> Heap hp"
  unfolding NuTopCtx_def Refining_def by simp
lemma [elim!,\<nu>elim]: "Inhabited \<tort_lbrace>s \<tycolon> S \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H\<tort_rbrace> \<Longrightarrow> (s \<ratio> S \<Longrightarrow> h \<ratio> H \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: nu_exps) blast

lemma NuTopCtx_cong: "\<tort_lbrace>h \<tycolon> H\<tort_rbrace> \<equiv> \<tort_lbrace>h' \<tycolon> H'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>s \<tycolon> S\<tort_rbrace> \<equiv> \<tort_lbrace>s' \<tycolon> S'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H\<tort_rbrace> \<equiv> \<tort_lbrace>s' \<tycolon> S'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h' \<tycolon> H'\<tort_rbrace>"
  unfolding atomize_eq by (auto 0 3 simp add: nu_exps)
simproc_setup NuTopCtx_cong ("\<tort_lbrace>s \<tycolon> S \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm NuTopCtx_cong})\<close>

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Ph \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t s \<tycolon> S \<longmapsto> s' \<tycolon> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Ps \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H) \<longmapsto> (s' \<tycolon> S'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h' \<tycolon> H') \<^bold>w\<^bold>i\<^bold>t\<^bold>h Ph \<and> Ps"
  unfolding Cast_def by (simp add: nu_exps) blast

subsection \<open>Fusion and its derivatives\<close>

subsubsection \<open>Fusion\<close>

definition Fusion :: "('a1,'b1) \<nu> \<Rightarrow> ('a2,'b2) \<nu> \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) \<nu>" (infixr "\<cross_product>" 70) 
  where "Fusion N M x = {(p1,p2). case x of (x1,x2) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)}"

lemma [nu_exps]: "(p1,p2) \<nuLinkL> N \<cross_product> M \<nuLinkR> (x1,x2) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)"
  by (simp add: Fusion_def Refining_def)
lemma [elim,\<nu>elim]: "(x1,x2) \<ratio> N1 \<cross_product> N2 \<Longrightarrow> (x1 \<ratio> N1 \<Longrightarrow> x2 \<ratio> N2 \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (simp add: nu_exps)

lemma [\<nu>intro]: "\<nu>Zero N z1 \<Longrightarrow> \<nu>Zero M z2 \<Longrightarrow> \<nu>Zero (N \<cross_product> M) (z1,z2)" unfolding \<nu>Zero_def by (simp add: nu_exps)

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M \<longmapsto> y' \<tycolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (x,y) \<tycolon> N \<cross_product> M \<longmapsto> (x',y') \<tycolon> N' \<cross_product> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2" unfolding Cast_def by (simp add: nu_exps) blast

(* no_notation RepSet ("\<tort_lbrace> _ \<tort_rbrace>" [10] )
syntax "_RepSet" :: "\<nu>typing \<Rightarrow> 'a set"  ("\<tort_lbrace> _ \<tort_rbrace>" [10] )
translations "_RepSet A " \<rightleftharpoons> "CONST RepSet (A)"
term "\<tort_lbrace> a \<tycolon> A\<tort_rbrace> " *)

subsubsection \<open>Stack Delimiter operator\<close>

definition Stack_Delimiter :: "('a::lrep,'ax) \<nu> \<Rightarrow> ('b::lrep,'bx) \<nu> \<Rightarrow> ('a \<times> 'b, 'ax \<times> 'bx) \<nu>" (infixr "<stack-div>" 70)
  where "A <stack-div> B = A \<cross_product> B"
consts "Stack_Delimiter_sugar" :: " 'just \<Rightarrow> 'a \<Rightarrow> 'sugar " ( "_/ \<heavy_comma> _" [14,15] 14) \<comment> \<open>Note it is left associative\<close>
translations " a \<tycolon> A\<heavy_comma> b \<tycolon> B " == " (CONST Pair b a) \<tycolon> (B <stack-div> A) "
  " A \<heavy_comma> B" => " (CONST Pair (_\<nu>typing_x B) (_\<nu>typing_x A)) \<tycolon> ((_\<nu>typing_ty B) <stack-div> (_\<nu>typing_ty A)) "

lemma [nu_exps]: "(pa,pb) \<nuLinkL> A <stack-div> B \<nuLinkR> (xa,xb) \<longleftrightarrow> (pa \<nuLinkL> A \<nuLinkR> xa) \<and> (pb \<nuLinkL> B \<nuLinkR> xb)"
  unfolding Stack_Delimiter_def by (simp add: nu_exps)
lemma [\<nu>elim,elim!]: "(a,b) \<ratio> A <stack-div> B \<Longrightarrow> (a \<ratio> A \<Longrightarrow> b \<ratio> B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Stack_Delimiter_def by blast

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> A \<longmapsto> a' \<tycolon> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<Longrightarrow> (P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t b \<tycolon> B \<longmapsto> b' \<tycolon> B' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2) \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a \<tycolon> A\<heavy_comma> b \<tycolon> B) \<longmapsto> (a' \<tycolon> A'\<heavy_comma> b' \<tycolon> B') \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2"
  unfolding Cast_def by (simp add: nu_exps) blast

lemma Stack_Delimiter_cong: "\<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<equiv> \<tort_lbrace>a' \<tycolon> A'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>b \<tycolon> B\<tort_rbrace> \<equiv> \<tort_lbrace>b' \<tycolon> B'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>b \<tycolon> B\<heavy_comma> a \<tycolon> A\<tort_rbrace> \<equiv> \<tort_lbrace>b' \<tycolon> B'\<heavy_comma> a' \<tycolon> A'\<tort_rbrace>"
  unfolding atomize_eq by (auto 0 3 simp add: nu_exps)
simproc_setup Stack_Delimiter_cong ("\<tort_lbrace>b \<tycolon> B\<heavy_comma> a \<tycolon> A\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm Stack_Delimiter_cong})\<close>

subsubsection \<open>Front Stack\<close>

definition Nu_Front_Stack :: "('a::lrep,'ax) \<nu> \<Rightarrow> (heap \<times> 'stack,'hsx) \<nu> \<Rightarrow> (heap \<times> 'a \<times> 'stack, 'ax \<times> 'hsx) \<nu>"
  where "Nu_Front_Stack A Ctx = (\<lambda>(ax,hsx). {(h,a,s). (a \<nuLinkL> A \<nuLinkR> ax) \<and> ((h,s) \<nuLinkL> Ctx \<nuLinkR> (hsx))} )"

consts "Front_Stack_sugar" :: " 'just \<Rightarrow> 'a \<Rightarrow> 'sugar " ( "_/ \<heavy_comma>^ _" [13,14] 13) \<comment> \<open>Note it is left associative\<close>
translations " c \<tycolon> Ctx \<heavy_comma>^ a \<tycolon> A " == " (CONST Pair a c) \<tycolon> (CONST Nu_Front_Stack A Ctx) "
  " Ctx \<heavy_comma>^ A " => " (CONST Pair (_\<nu>typing_x A) (_\<nu>typing_x Ctx)) \<tycolon> (CONST Nu_Front_Stack (_\<nu>typing_ty A) (_\<nu>typing_ty Ctx)) "

text \<open>Normally the stack elements are written `before` the heap elements, \<^term>\<open>s1 \<tycolon> S1\<heavy_comma> s2 \<tycolon> S2\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H\<close>.
  The \<^term>\<open>Nu_Front_Stack\<close> allows one writes the stack elements `after` the heap, as \<^term>\<open>s1 \<tycolon> S1\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<heavy_comma>^ s2 \<tycolon> S2\<close>.
  Both of the two \<nu>-types specify the same low concretes.
  It is useful when one needs to specify over the whole remaining stack and heap, e.g., theorem `Until` (see later)
    which requires body to return \<^term>\<open>x \<tycolon> X \<heavy_comma>^ loop_condition \<tycolon> Boolean\<close> where the \<^term>\<open>x \<tycolon> X\<close> instantiated by caller
    specifies all the heap and remaining stack except the leading loop_condition.\<close>

lemma [nu_exps]: "(h,a,s) \<nuLinkL> Nu_Front_Stack A Ctx \<nuLinkR> (ax,hsx) \<longleftrightarrow> (a \<nuLinkL> A \<nuLinkR> ax) \<and> ((h,s) \<nuLinkL> Ctx \<nuLinkR> hsx)"
  unfolding Nu_Front_Stack_def Refining_def by simp
lemma [simp]: "\<tort_lbrace> (a,h,s) \<tycolon> Nu_Front_Stack A (NuTopCtx H S) \<tort_rbrace> = \<tort_lbrace> (h,a,s) \<tycolon> NuTopCtx H (A <stack-div> S) \<tort_rbrace>"
  by (auto simp add: nu_exps)

lemma Nu_Front_Stack_cong: "\<tort_lbrace>c \<tycolon> Ctx\<tort_rbrace> \<equiv> \<tort_lbrace>c' \<tycolon> Ctx'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>c \<tycolon> Ctx \<heavy_comma>^ x \<tycolon> T\<tort_rbrace> \<equiv> \<tort_lbrace>c' \<tycolon> Ctx' \<heavy_comma>^ x \<tycolon> T\<tort_rbrace>"
  unfolding atomize_eq by (auto simp add: nu_exps)
simproc_setup Nu_Front_Stack_cong ("\<tort_lbrace>c \<tycolon> Ctx \<heavy_comma>^ x \<tycolon> T\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm Nu_Front_Stack_cong})\<close>

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> c \<tycolon> Ctx \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> c \<tycolon> Ctx \<heavy_comma>^ (x \<tycolon> X)"
  unfolding Intro_def Cast_def by (simp add: nu_exps)
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t c \<tycolon> Ctx \<longmapsto> (R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t c \<tycolon> Ctx \<heavy_comma>^ (x \<tycolon> X) \<longmapsto> (R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Dest_def Cast_def by (simp add: nu_exps) blast
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> x' \<tycolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> c \<tycolon> Ctx \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> c \<tycolon> Ctx \<heavy_comma>^ (x' \<tycolon> X') \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def by (simp add: nu_exps) blast




subsection \<open>Existential Nu-type\<close>

definition ExNu :: " ('c \<Rightarrow> ('a,'b) \<nu>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b) \<nu> "
  where "ExNu N x = {p. (\<exists>c. p \<nuLinkL> N c \<nuLinkR> x c)}"
lemma [simp]: "p \<nuLinkL> ExNu N \<nuLinkR> x \<longleftrightarrow> (\<exists>c. p \<nuLinkL> N c \<nuLinkR> x c)" unfolding ExNu_def Refining_def by simp


abbreviation ExNu_sugar :: " ('c \<Rightarrow> ('a,'b) typing) \<Rightarrow> ('a, 'c \<Rightarrow> 'b) typing " (binder "\<exists>* " 10)
  where "ExNu_sugar P \<equiv> (\<lambda>c. typing_img (P c)) \<tycolon> ExNu (\<lambda>c. typing_nu (P c))"
syntax "_ExNu_print" :: "logic \<Rightarrow> logic \<Rightarrow> logic"

translations "\<exists>* a b. P" \<rightleftharpoons> "\<exists>* a. (\<exists>*b. P)"
  "\<exists>* c. x \<tycolon> T" => "(\<lambda>c. x) \<tycolon> CONST ExNu (\<lambda>c. T)"
(*  "\<exists>* c. x \<tycolon> T" <= "(\<lambda>c. x) \<tycolon> CONST ExNu (\<lambda>c''''''. T)" (*TODO: print translation that alpha-convert the c''''' *)
  "\<exists>* c. x c \<tycolon> T" <= "x \<tycolon> CONST ExNu (\<lambda>c. T)"
  "CONST Pair a b" <= "(CONST Pair a) b"
  "\<exists>* c. x \<tycolon> T c" <= "(\<lambda>c. x) \<tycolon> CONST ExNu T" *)

notation ExNu_sugar (binder "\<exists>\<^sup>\<nu> " 10)

lemma ExNu_cong: "(\<And>c. \<tort_lbrace>x c \<tycolon> T c\<tort_rbrace> \<equiv> \<tort_lbrace>x' c \<tycolon> T' c\<tort_rbrace>) \<Longrightarrow> \<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace> \<equiv> \<tort_lbrace> x' \<tycolon> ExNu T' \<tort_rbrace>"
  unfolding atomize_eq RepSet_def ExNu_def Refining_def by simp

simproc_setup ExNu_cong ("\<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace>") = \<open>K (NuSimpCong.simproc_qualifier @{thm ExNu_cong})\<close>

lemma ExNu_pair: "\<tort_lbrace> x \<tycolon> ExNu T \<tort_rbrace> = \<tort_lbrace>\<exists>*c1 c2. x (c1,c2) \<tycolon> T (c1,c2) \<tort_rbrace>" by (auto simp add: nu_exps)
lemma named_ExNu: "\<tort_lbrace> x \<tycolon> ExNu T \<tort_rbrace> = \<tort_lbrace>\<exists>*c. x (tag c) \<tycolon> T (tag c) \<tort_rbrace>" by (auto simp add: named_exists nu_exps)

lemma [simp]: "p \<in> \<S>  \<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace> \<longleftrightarrow> (\<exists>z. p \<in> \<S>  \<tort_lbrace> x z \<tycolon> T z\<tort_rbrace> )" by (auto 4 3 simp add: nu_exps)
lemma [simp]: "p \<in> \<S_S> \<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace> \<longleftrightarrow> (\<exists>z. p \<in> \<S_S> \<tort_lbrace>x z \<tycolon> T z\<tort_rbrace>)" by (auto 4 3 simp add: nu_exps)
lemma [simp]: "\<tort_lbrace>x \<tycolon> ExNu T \<heavy_comma> y \<tycolon> R\<tort_rbrace> = \<tort_lbrace>\<exists>* c. x c \<tycolon> T c \<heavy_comma> y \<tycolon> R \<tort_rbrace>" unfolding Stack_Delimiter_def by (auto simp add: nu_exps)
lemma [simp]: "\<tort_lbrace>y \<tycolon> L \<heavy_comma> x \<tycolon> ExNu T\<tort_rbrace> = \<tort_lbrace>\<exists>* c. y \<tycolon> L \<heavy_comma> x c \<tycolon> T c \<tort_rbrace>" unfolding Stack_Delimiter_def by (auto simp add: nu_exps)

lemma ExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> ExNu T)) \<equiv> (\<exists>c. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n x c \<tycolon> T c)"
  unfolding CurrentConstruction_def by auto

lemma ExTyp_I_\<nu>app[\<nu>intro 20]:
  "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x c \<tycolon> T c \<longmapsto> (\<exists>*c. x c \<tycolon> T c)" unfolding Intro_def Cast_def by (simp add: nu_exps) blast
lemma [\<nu>intro 200]: "(\<And>c. \<^bold>c\<^bold>a\<^bold>s\<^bold>t x c \<tycolon> T c \<longmapsto> x' \<tycolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P c) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (\<exists>*c. x c \<tycolon> T c) \<longmapsto> x' \<tycolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>c. P c)"
  unfolding Cast_def by (simp add: nu_exps) blast


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

definition NuAddition :: " ('p,'x) \<nu> \<Rightarrow> bool \<Rightarrow> ('p,'x) \<nu> " (infixl "\<and>\<^sup>\<nu>" 50)
  where " (N \<and>\<^sup>\<nu> P) = (\<lambda>x. {p. P \<and> (p \<nuLinkL> N \<nuLinkR> x)})"
translations "(x \<tycolon> T) \<and>\<^sup>\<nu> P" \<rightleftharpoons> "x \<tycolon> T \<and>\<^sup>\<nu> P"
  "(x \<tycolon> T) \<and> P" => "x \<tycolon> (T \<and>\<^sup>\<nu> P)"
lemma [simp]: "p \<nuLinkL> T \<and>\<^sup>\<nu> P \<nuLinkR> x \<longleftrightarrow> P \<and> (p \<nuLinkL> T \<nuLinkR> x)" unfolding NuAddition_def Refining_def by simp

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> (x \<tycolon> T) \<and>\<^sup>\<nu> P"
  unfolding Intro_def Cast_def Premise_def by (simp add: nu_exps)
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> x' \<tycolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (P \<longrightarrow> Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> x' \<tycolon> T' \<and>\<^sup>\<nu> Q \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Premise_def by (simp add: nu_exps)

lemma subj_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> N \<and>\<^sup>\<nu> P"
  unfolding Cast_def Premise_def by simp

(* lemma [simp]: "\<tort_lbrace> x \<tycolon> T \<and>\<^sup>\<nu> True\<tort_rbrace> = \<tort_lbrace> x \<tycolon> T \<tort_rbrace>" by auto
lemma [simp]: "\<tort_lbrace>L \<heavy_comma> (x \<tycolon> T) \<and> P\<tort_rbrace> = \<tort_lbrace>(L \<heavy_comma> x \<tycolon> T) \<and> P\<tort_rbrace>" and [simp]: "\<tort_lbrace>(x \<tycolon> T) \<and> P\<heavy_comma> R\<tort_rbrace> = \<tort_lbrace>(x \<tycolon> T\<heavy_comma> R) \<and> P\<tort_rbrace>"
  unfolding Stack_Delimiter_def by auto
lemma [simp]: "\<tort_lbrace>L \<heavy_asterisk> (x \<tycolon> T) \<and> P\<tort_rbrace> = \<tort_lbrace>(L \<heavy_asterisk> x \<tycolon> T) \<and> P\<tort_rbrace>" and [simp]: "\<tort_lbrace>(x \<tycolon> T) \<and> P\<heavy_asterisk> R\<tort_rbrace> = \<tort_lbrace>(x \<tycolon> T\<heavy_asterisk> R) \<and> P\<tort_rbrace>"
  unfolding Heap_Delimiter_def by auto blast+
lemma [simp]: "\<tort_lbrace> (s \<tycolon> S) \<and> P \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<tort_rbrace> = \<tort_lbrace> (s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H) \<and> P \<tort_rbrace>"
  and [simp]: "\<tort_lbrace> s \<tycolon> S \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (h \<tycolon> H) \<and> P \<tort_rbrace> = \<tort_lbrace> (s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H) \<and> P \<tort_rbrace>" by auto *)

lemma NuAddition_cong: "\<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> T'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>x \<tycolon> T \<and>\<^sup>\<nu> P\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> T' \<and>\<^sup>\<nu> P\<tort_rbrace>" unfolding atomize_eq by (auto simp add: nu_exps)
simproc_setup NuAddition_cong ("\<tort_lbrace>x \<tycolon> T \<and>\<^sup>\<nu> P\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm NuAddition_cong})\<close>

subsubsection \<open>Auto tag\<close>

abbreviation AutoAddition (infixl "\<and>\<^sup>\<nu>''" 50) where "AutoAddition T P \<equiv> Auto (NuAddition T P)"
notation AutoAddition (infixl "\<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o" 50)
translations "(x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P" \<rightleftharpoons> "x \<tycolon> T \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P"

lemma [simp]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> x \<tycolon> T \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<longmapsto> Y \<brangle> = (P \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> x \<tycolon> T \<longmapsto> Y \<brangle>)"
  unfolding Auto_def Procedure_def by (simp add: nu_exps) blast
lemma [simp]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> X \<longmapsto> y \<tycolon> Y \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<brangle> = \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> X \<longmapsto> y \<tycolon> Y \<and>\<^sup>\<nu> P \<brangle>"
  unfolding Auto_def ..
lemma [simp]: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> x \<tycolon> T \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<longmapsto> Y \<brangle> = (P \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> x \<tycolon> T \<longmapsto> Y \<brangle>)"
  unfolding Function_def by simp
lemma [simp]: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> X \<longmapsto> y \<tycolon> Y \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<brangle> = \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> X \<longmapsto> y \<tycolon> Y \<and>\<^sup>\<nu> P \<brangle>"
  unfolding Auto_def ..


lemma [simp]: "\<tort_lbrace> x \<tycolon> T \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o True\<tort_rbrace> = \<tort_lbrace> x \<tycolon> T \<tort_rbrace>" unfolding Auto_def by (auto simp add: nu_exps)
lemma [simp]: "\<tort_lbrace>L \<heavy_comma> (x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace> = \<tort_lbrace>(L \<heavy_comma> x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace>"
    and [simp]: "\<tort_lbrace>(x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<heavy_comma> R\<tort_rbrace> = \<tort_lbrace>(x \<tycolon> T\<heavy_comma> R) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace>"
  unfolding Auto_def Stack_Delimiter_def by (auto simp add: nu_exps)
lemma [simp]: "\<tort_lbrace>L \<heavy_asterisk> (x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace> = \<tort_lbrace>(L \<heavy_asterisk> x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace>"
    and [simp]: "\<tort_lbrace>(x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<heavy_asterisk> R\<tort_rbrace> = \<tort_lbrace>(x \<tycolon> T\<heavy_asterisk> R) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace>"
  unfolding Auto_def Heap_Delimiter_def by (auto simp add: nu_exps) blast+
lemma [simp]: "\<tort_lbrace> (s \<tycolon> S) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<tort_rbrace> = \<tort_lbrace> (s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<tort_rbrace>"
    and [simp]: "\<tort_lbrace> s \<tycolon> S \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (h \<tycolon> H) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<tort_rbrace> = \<tort_lbrace> (s \<tycolon> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<tort_rbrace>"
  unfolding Auto_def by (auto simp add: nu_exps)
lemma [simp]: "\<tort_lbrace>c \<tycolon> Ctx \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<heavy_comma>^ x \<tycolon> T\<tort_rbrace> = \<tort_lbrace> (c \<tycolon> Ctx \<heavy_comma>^ x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<tort_rbrace>"
  unfolding Auto_def by (auto simp add: nu_exps)

lemma AutoAddition_cong: "\<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> T'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>x \<tycolon> T \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> T' \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace>" unfolding Auto_def by simp
simproc_setup AutoAddition_cong ("\<tort_lbrace>x \<tycolon> T \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm AutoAddition_cong})\<close>

lemma t1: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n x \<tycolon> T) \<and> P"
  unfolding CurrentConstruction_def Auto_def by (cases s) (simp add: nu_exps, blast+)
lemma [simp]: "((((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> B) \<and> C) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<equiv> (((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> (B \<and> C)) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)" by simp

lemma move_fact_to_star1[simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o Q) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP NoFact) (PROP L) (PROP I))
    \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n x \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop Q) (PROP L) (PROP I))"
  unfolding t1 SpecTop_imp conj_imp FactCollection_imp
  by (intro equal_intr_rule SpecTop_I FactCollection_I conjI NoFact) (* (unfold SpecTop_imp conj_imp FactCollection_imp) *)
lemma move_fact_to_star2[simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o Q) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop P) (PROP L) (PROP I))
    \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n x \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection  (Trueprop (Q \<and> P)) (PROP L) (PROP I))"
  unfolding t1 SpecTop_imp conj_imp FactCollection_imp
  by (intro equal_intr_rule SpecTop_I FactCollection_I conjI) (* (unfold SpecTop_imp conj_imp FactCollection_imp) *)


subsection \<open>Identity\<close>

definition Identity :: " ('a::lrep, 'a) \<nu> " where "Identity x = {x}"
lemma [simp]: "p \<nuLinkL> Identity \<nuLinkR> x \<longleftrightarrow> p = x" unfolding Refining_def Identity_def by auto

subsection \<open>Refinement\<close>

definition NuRefine :: " ('a, 'b) \<nu> \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) \<nu> " (infixl "\<nuRefine>" 80)
  where "(N \<nuRefine> T) x = {p. (x \<in> T \<and>(p \<nuLinkL> N \<nuLinkR> x))}"

notation NuRefine (infixl "<where>" 80)

lemma [simp]: " p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> ( p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def Refining_def by simp
lemma [elim,\<nu>elim]: " x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (simp add: nu_exps)

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> S \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x \<tycolon> M <where> S"
  unfolding Intro_def Cast_def by (simp add: nu_exps) blast
lemma [\<nu>intro, \<nu>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M <where> S \<longmapsto> x \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h x \<in> S"
  unfolding Dest_def Cast_def by (simp add: nu_exps)
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x' \<tycolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x' \<in> S \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x' \<tycolon> M' <where> S \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def by (simp add: nu_exps) blast
lemma refine_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N <where> P)"
  unfolding Cast_def by (simp add: nu_exps) blast

abbreviation AutoRefine (infixl "<auto-where>" 80)
  where "AutoRefine N P \<equiv> Auto (NuRefine N P)"
lemma [simp]:"\<tort_lbrace>x \<tycolon> T <auto-where> P \<tort_rbrace> = \<tort_lbrace> (x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P) \<tort_rbrace>"
  unfolding Auto_def Premise_def by (auto simp add: nu_exps)

lemma NuRefine_to_auto:"\<tort_lbrace>x \<tycolon> T <where> P \<tort_rbrace> = \<tort_lbrace>x \<tycolon> T <auto-where> P \<tort_rbrace>" unfolding Auto_def ..

(* lemma [\<nu>intro]: "(x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<and>x \<in> P" unfolding Cast_def by auto
lemma [\<nu>intro]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where> P \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q" unfolding Cast_def by auto
(* lemma [\<nu>cast_overload E]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P) \<longmapsto> x \<tycolon> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h x \<in> P" unfolding Cast_def by auto *)
*)
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e z \<in> S \<Longrightarrow> \<nu>Zero N z \<Longrightarrow> \<nu>Zero (N <where> S) z"
  unfolding \<nu>Zero_def Premise_def by (simp add: nu_exps)
lemma "\<nu>Equal (N <where> P) can_eq eq \<longleftrightarrow> \<nu>Equal N (\<lambda>x y. x \<in> P \<and> y \<in> P \<and> can_eq x y) eq"
  unfolding \<nu>Equal_def by (simp add: nu_exps) blast

(* definition SchemaCondition (infixl "<where''>" 80) where "SchemaCondition = NuRefine"
abbreviation WorkingSchemaCondition (infixl "<where''''>" 80) where "WorkingSchemaCondition \<equiv> WorkingProtector SchemaCondition"

lemma [simp]: "\<tort_lbrace>x \<tycolon> N <where'> P\<tort_rbrace> = (\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<addition> (x \<in> P))" unfolding SchemaCondition_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where> P \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where'> P \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q" unfolding SchemaCondition_def . 
lemma SchemaCondition_simp: "\<tort_lbrace> x \<tycolon> N <where'> P\<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P\<tort_rbrace>" unfolding SchemaCondition_def by auto
lemma refine'_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N <where''> P)" unfolding WorkingProtector_def Cast_def by auto
*)

subsection \<open>Down Lifting\<close>

definition DownLift :: "('a, 'b) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<nu>" (infixl "<down-lift>" 80)
  where "DownLift N g x = {p. ( p \<nuLinkL> N \<nuLinkR> g x)}"

lemma [simp]: " p \<nuLinkL> N <down-lift> g \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> N \<nuLinkR> g x"
  unfolding DownLift_def Refining_def by simp
lemma [elim,\<nu>elim]: " x \<ratio> N <down-lift> g \<Longrightarrow> ( g x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (simp add: nu_exps)

(* lemma [\<nu>cast_overload E]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> g x \<tycolon> N" unfolding Cast_def by simp *)
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> x' \<tycolon> N" unfolding Cast_def by (simp add: nu_exps) blast

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (g y = x) \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M <down-lift> g"
  unfolding Intro_def Cast_def by (simp add: nu_exps) blast
lemma [\<nu>intro, \<nu>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <down-lift> g \<longmapsto> g y \<tycolon> M"
  unfolding Dest_def Cast_def by (simp add: nu_exps)

lemma [\<nu>intro]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <down-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast
lemma "\<down>lift_\<nu>app": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <down-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast


abbreviation AutoDownLift (infixl "<auto-down-lift>" 80) where "AutoDownLift T f \<equiv> Auto (DownLift T f)"

lemma [simp]:"\<tort_lbrace>x \<tycolon> T <auto-down-lift> f \<tort_rbrace> = \<tort_lbrace> f x \<tycolon> T \<tort_rbrace>" unfolding Auto_def by (auto simp add: nu_exps)

(* term image
lemma "\<nu>Equal (N <down-lift> g) can_eq eq \<longleftrightarrow> \<nu>Equal N (inv_imagep can_eq g) (inv_imagep eq g)"
  unfolding \<nu>Equal_def by auto *)

(* definition Schema (infixl "<schema>" 80) where "Schema = DownLift"
lemma i_schema_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <schema> g" unfolding Cast_def Schema_def by auto
lemma [simp]: "\<tort_lbrace> x \<tycolon> N <schema> id \<tort_rbrace> = \<tort_lbrace> x \<tycolon> N \<tort_rbrace>" and [simp]: "\<tort_lbrace> (a,b) \<tycolon> N <schema> f \<tort_rbrace> = \<tort_lbrace> f (a,b) \<tycolon> N \<tort_rbrace>" unfolding Schema_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> <Structural> g y = y1  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <schema> g"
  unfolding Schema_def Cast_def StructuralTag_def by auto *)

subsection \<open>Up Lifting\<close>

definition UpLift :: "('a, 'c) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<nu>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> ( p \<nuLinkL> N \<nuLinkR> y))}"

lemma [simp]: " p \<nuLinkL> N <up-lift> f \<nuLinkR> x \<longleftrightarrow> (\<exists>y. (f y = x) \<and> (p \<nuLinkL> N \<nuLinkR> y))"
  unfolding UpLift_def Refining_def by auto
lemma [elim,\<nu>elim]: " x \<ratio> N <up-lift> f \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> y \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: nu_exps) blast

lemma "\<up>lift_\<nu>app": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M <up-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast
(* lemma [\<nu>overload D]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M <up-lift> g \<longmapsto> (\<exists> \<tycolon> M) "
  unfolding Cast_def by (simp add: nu_exps) blast *)

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M <up-lift> g"
  unfolding Intro_def Cast_def by (simp add: nu_exps) blast
lemma [\<nu>intro 130]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x' \<tycolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M' <up-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast
(*lemma [\<nu>intro -30]: "(\<And> x. CaseSplit (y = g x) \<Longrightarrow> \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<Longrightarrow> \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Dest_def Cast_def CaseSplit_def by auto *)
lemma [\<nu>intro 20]: "(\<And> x. y = g x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P x) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>x. y = g x \<and> P x)"
  unfolding Dest_def Cast_def CaseSplit_def by (simp add: nu_exps) blast
lemma [\<nu>intro 150]: "(\<And> x. y = g x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y' x \<tycolon> M' x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P x) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto>( \<exists>*x. y' x \<tycolon> M' x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>x. y = g x \<and> P x)"
  unfolding Dest_def Cast_def CaseSplit_def by (simp add: nu_exps) blast

(*term case_prod
definition Splited_And :: "'y \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> prop) \<Rightarrow> prop"
  where "Splited_And y pattern prop \<equiv> (\<And>x. y = pattern x \<Longrightarrow> PROP prop x)"

lemma A: "y = case_prod f x \<Longrightarrow> (\<And>x1 x2. x = (x1,x2) \<Longrightarrow> y = f x1 x2 \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x" by (cases x) fast

declare [ [ML_print_depth = 200] ]
ML \<open>Splitter.split_tac\<close>
ML \<open>
val th1 = @{thm conjE}
val th = Goal.init @{cterm "(\<And>x. QQ \<Longrightarrow> y = (case x of (a,b,c) \<Rightarrow> f a b c) \<Longrightarrow> JJ \<Longrightarrow> C x)"}
val th'2 = REPEAT (eresolve0_tac @{thms A} 1
  ) th
  |> Seq.pull
\<close>

thm if_split
thm prod.split_asm
*)
lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> (\<exists>* x. x \<tycolon> M \<and>\<^sup>\<nu> (g x = y))"
  unfolding Dest_def Cast_def by (simp add: nu_exps)

lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> f x \<tycolon> N <up-lift> f" unfolding Cast_def by (simp add: nu_exps) blast
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> f x \<tycolon> N <up-lift> f" unfolding Cast_def by (simp add: nu_exps) blast

lemma "\<nu>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<nu>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<nu>Equal_def by (auto 0 6)


subsubsection \<open>Operator Some\<close>

definition NuSome :: " ('a :: lrep, 'b) \<nu> \<Rightarrow> ('a :: lrep, 'b set) \<nu> " ("<some>")
  where "NuSome T S = {p. (\<exists>x. x \<in> S \<and> (p \<nuLinkL> T \<nuLinkR> x)) }"
notation NuSome ("\<^bold>s\<^bold>o\<^bold>m\<^bold>e")

lemma [simp]: "p \<nuLinkL> \<^bold>s\<^bold>o\<^bold>m\<^bold>e T \<nuLinkR> X \<longleftrightarrow> (\<exists>x. x \<in> X \<and> (p \<nuLinkL>T \<nuLinkR> x))" unfolding NuSome_def Refining_def by simp
lemma [elim,\<nu>elim]: "X \<ratio> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e T) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<ratio> T \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by simp blast
(* lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X \<subseteq> X' \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> X' \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by (auto 2 3) *)
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> Y \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e M) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Cast_def by auto
(*lemma someI_\<nu>cast: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> X \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by auto
lemma someE_\<nu>cast[\<nu>cast_overload E]: "[h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> (\<exists>*some. \<tort_lbrace>some \<tycolon> N \<tort_rbrace> \<addition> (some \<in> X))" unfolding Cast_def by auto *)


section \<open>Mechanisms - II\<close>

subsection \<open>Heap\<close>

definition NuNothing :: "(heap, unit) \<nu>" where  "NuNothing x = {h. h = Map.empty}"
consts Nothing_sugar :: " 'a_sugar " ("Nothing")
translations "Nothing" \<rightleftharpoons> "() \<tycolon> CONST NuNothing"
lemma [nu_exps]: "h \<nuLinkL> NuNothing \<nuLinkR> x \<longleftrightarrow> h = Map.empty" unfolding Refining_def NuNothing_def by simp

lemma Separation_emptyL: "\<tort_lbrace>Nothing \<heavy_asterisk> h \<tycolon> H\<tort_rbrace> = \<tort_lbrace>h \<tycolon> H\<tort_rbrace>" and Separation_emptyR: "\<tort_lbrace>h \<tycolon> H \<heavy_asterisk> Nothing\<tort_rbrace> = \<tort_lbrace>h \<tycolon> H\<tort_rbrace>"
  unfolding Heap_Delimiter_def by (auto simp add: nu_exps)

subsubsection \<open>Syntax & Auxiliary\<close>

consts ResourceState :: " heap \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> bool" ("_ \<^bold>a\<^bold>t _ \<^bold>i\<^bold>s _ " [16,16,12] 11)
consts allocated :: " heap \<Rightarrow> 'a \<Rightarrow> bool"

translations "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s x \<tycolon> T" \<rightleftharpoons> "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"

term "ofs + length xs \<le> segment_len base \<and> segment_llty base = LLTY('a::lrep)"
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
  unfolding MemAddrState_def Inhabited_def by blast
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


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<in> S \<Longrightarrow> h |` S \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<notin> S \<Longrightarrow> h |` (- S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)


subsubsection \<open>Cast\<close>

definition Heap_Cast_Goal :: " 'a \<Rightarrow> 'a "  ("\<medium_left_bracket>\<medium_left_bracket> _ \<medium_right_bracket>\<medium_right_bracket>") where "Heap_Cast_Goal x = x"
  \<comment> \<open>The protector marks the goal to be gained\<close>

lemma [\<nu>intro 1000]: "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<^bold>d\<^bold>u\<^bold>a\<^bold>l h\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket>" unfolding Heap_Cast_Goal_def using cast_dual_id .

lemma context_cast[\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t k \<tycolon> K \<longmapsto> k' \<tycolon> K' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H' \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<medium_right_bracket>\<medium_right_bracket> \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t (k \<tycolon> K\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H) \<longmapsto> (k' \<tycolon> K'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h' \<tycolon> H') \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def Heap_Cast_Goal_def by (simp add: pair_forall nu_exps) blast

lemma context_cast_dual[\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t k \<tycolon> K \<longmapsto> k' \<tycolon> K' \<^bold>w\<^bold>i\<^bold>t\<^bold>h PK
    \<Longrightarrow> (PK \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H' \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h PH \<^bold>d\<^bold>u\<^bold>a\<^bold>l h2 \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H2 \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h2' \<tycolon> H2' \<medium_right_bracket>\<medium_right_bracket>)
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (k \<tycolon> K\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H) \<longmapsto> (k' \<tycolon> K'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h' \<tycolon> H') \<^bold>w\<^bold>i\<^bold>t\<^bold>h PK \<and> PH \<^bold>d\<^bold>u\<^bold>a\<^bold>l (k2 \<tycolon> K2\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h2 \<tycolon> H2) \<longmapsto> (k2 \<tycolon> K2\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h2' \<tycolon> H2')"
  unfolding CastDual_def Cast_def Heap_Cast_Goal_def Intro_def Dest_def by (simp add: pair_forall nu_exps) blast

(* lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> H' \<heavy_asterisk> y \<tycolon> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> y\<^sub>m \<tycolon> Y \<longmapsto> x\<^sub>m \<tycolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> H' \<heavy_asterisk> \<medium_left_bracket> y \<tycolon> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> y\<^sub>m \<tycolon> Y \<medium_right_bracket> \<longmapsto> x\<^sub>m \<tycolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Heap_Cast_Goal_def . *)
(* lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B" unfolding CastDual_def  by (simp add: cast_id) *)

lemma [\<nu>intro 1000]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> h \<tycolon> H \<longmapsto> L \<heavy_asterisk> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<^bold>d\<^bold>u\<^bold>a\<^bold>l L \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> L \<heavy_asterisk> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Heap_Cast_Goal_def using cast_dual_id .

lemma [\<nu>intro 1000]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Heap_Cast_Goal_def using cast_id .

(* lemma [\<nu>intro 10]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
  \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H' \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Heap_Cast_Goal_def  . *)

lemma heap_idx_this_dual[\<nu>intro 1000]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> Nothing \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>d\<^bold>u\<^bold>a\<^bold>l Nothing \<heavy_asterisk> x\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def Separation_emptyL Heap_Cast_Goal_def CastDual_def Intro_def Dest_def by simp

lemma heap_idx_L_dual[\<nu>intro 130]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l h'\<^sub>m \<tycolon> H'\<^sub>m \<heavy_asterisk> x\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket>
    \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t l \<tycolon> L \<heavy_asterisk> h \<tycolon> H \<longmapsto> l \<tycolon> L \<heavy_asterisk> h' \<tycolon> H' \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l l \<tycolon> L \<heavy_asterisk> h'\<^sub>m \<tycolon> H'\<^sub>m \<heavy_asterisk> x\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> l \<tycolon> L \<heavy_asterisk> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma heap_idx_L'[\<nu>intro 110]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>\<medium_right_bracket>
    \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t l \<tycolon> L \<heavy_asterisk> h \<tycolon> H \<longmapsto> l \<tycolon> L \<heavy_asterisk> h' \<tycolon> H' \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma heap_idx_L[\<nu>intro 130]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t l \<tycolon> L \<heavy_asterisk> h \<tycolon> H \<longmapsto> l \<tycolon> L \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma heap_idx_R_dual[\<nu>intro]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
      \<^bold>d\<^bold>u\<^bold>a\<^bold>l h'\<^sub>m \<tycolon> H'\<^sub>m \<heavy_asterisk> x\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<heavy_asterisk> r \<tycolon> R \<longmapsto> h' \<tycolon> H' \<heavy_asterisk> r \<tycolon> R \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
      \<^bold>d\<^bold>u\<^bold>a\<^bold>l h'\<^sub>m \<tycolon> H'\<^sub>m \<heavy_asterisk> r \<tycolon> R \<heavy_asterisk> x\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h\<^sub>m \<tycolon> H\<^sub>m \<heavy_asterisk> r \<tycolon> R \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma heap_idx_R[\<nu>intro]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>\<medium_right_bracket>
    \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<heavy_asterisk> r \<tycolon> R \<longmapsto> h' \<tycolon> H' \<heavy_asterisk> r \<tycolon> R \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma [\<nu>intro 200]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h1 \<tycolon> H1 \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>d\<^bold>u\<^bold>a\<^bold>l h1\<^sub>m \<tycolon> H1\<^sub>m \<heavy_asterisk> x\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h\<^sub>m \<tycolon> H\<^sub>m  \<medium_right_bracket>\<medium_right_bracket>
    \<Longrightarrow> (P1 \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h1 \<tycolon> H1 \<longmapsto> h2 \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H2 \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l h2\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H2\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h1\<^sub>m \<tycolon> H1\<^sub>m \<medium_right_bracket>\<medium_right_bracket>)
    \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> (x, h2) \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X <heap-sep> H2 \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l (x\<^sub>m, h2\<^sub>m) \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m <heap-sep> H2\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma [\<nu>intro 200]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h1 \<tycolon> H1 \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>\<medium_right_bracket>
    \<Longrightarrow> (P1 \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h1 \<tycolon> H1 \<longmapsto> h2 \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H2 \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket>\<medium_right_bracket>)
    \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> (x, h2) \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X <heap-sep> H2 \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma [\<nu>intro 120]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h1 \<tycolon> H1 \<heavy_asterisk> x \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>\<medium_right_bracket>
    \<Longrightarrow> (P1 \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h1 \<tycolon> H1 \<longmapsto> h\<^sub>r \<tycolon> H\<^sub>r \<heavy_asterisk> h2 \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H2 \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket>\<medium_right_bracket>)
    \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h\<^sub>r \<tycolon> H\<^sub>r \<heavy_asterisk> (x, h2) \<tycolon> \<medium_left_bracket>\<medium_left_bracket> X \<^emph> H2 \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet SepNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)

lemma [ \<nu>intro -50 ]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d \<tycolon> D \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> (P \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t d \<tycolon> D \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<tycolon> I'\<^sub>m \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> i \<tycolon> I \<medium_right_bracket>\<medium_right_bracket>)
  \<Longrightarrow> (P \<Longrightarrow> P2 \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t i \<tycolon> I \<longmapsto> x\<^sub>m \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Anyway)
  \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<tycolon> I'\<^sub>m \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> x\<^sub>m \<tycolon> T \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Dest_def Intro_def CastDual_def Different_def Heap_Cast_Goal_def Cast_def
  by (auto simp add: Premise_def)

(* lemma [ \<nu>intro 50 ]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d \<tycolon> D \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> (P \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t d \<tycolon> D \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<tycolon> I'\<^sub>m \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> i \<tycolon> I \<medium_right_bracket>\<medium_right_bracket>)
  \<Longrightarrow> (P \<Longrightarrow> P2 \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t i \<tycolon> I \<longmapsto> x\<^sub>m \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Anyway)
  \<Longrightarrow> \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> P2 \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Dest_def Intro_def CastDual_def Different_def Heap_Cast_Goal_def Cast_def
  by (auto simp add: Premise_def) *)



lemma heap_put_this: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t Nothing \<heavy_asterisk> x \<tycolon> X \<longmapsto> x \<tycolon> X" unfolding Cast_def Separation_emptyL by simp
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t s \<tycolon> S \<heavy_asterisk> x \<tycolon> X \<longmapsto> s' \<tycolon> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t l \<tycolon> L \<heavy_asterisk> s \<tycolon> S \<heavy_asterisk> x \<tycolon> X \<longmapsto> l \<tycolon> L \<heavy_asterisk> s' \<tycolon> S' "
  unfolding Cast_def HeapDivNu_to_SepSet
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t s \<tycolon> S \<heavy_asterisk> x \<tycolon> X \<longmapsto> s' \<tycolon> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (s \<tycolon> S \<heavy_asterisk> r \<tycolon> R) \<heavy_asterisk> x \<tycolon> X \<longmapsto> s' \<tycolon> S' \<heavy_asterisk> r \<tycolon> R "
  unfolding Cast_def HeapDivNu_to_SepSet
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)



(* lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> S \<longmapsto> L \<heavy_asterisk> S'"
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<heavy_asterisk> R \<longmapsto> S' \<heavy_asterisk> R"
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq *)





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


lemma apply_cast: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H)) \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> y \<tycolon> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> y \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<and> P)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Cast_def by (auto 4 6 simp add: nu_exps)
lemma "cast": "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  for T' :: "(heap \<times> 'a::lrep) set" unfolding Cast_def CurrentConstruction_def by auto

lemma cast_\<nu>app: "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> x' \<tycolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> x' \<tycolon> X'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Argument_def by (simp add: nu_exps) blast

lemma cast_heap_\<nu>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> x' \<tycolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> x \<tycolon> X \<longmapsto> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> x' \<tycolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Argument_def Heap_Delimiter_def by (simp add: nu_exps) blast

lemma cast_whole_heap_\<nu>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<longmapsto> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h' \<tycolon> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Argument_def by (simp add: nu_exps) blast

lemma cast_heap_conversion:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h\<^sub>x \<tycolon> H\<^sub>x \<longmapsto> h\<^sub>r \<tycolon> H\<^sub>r \<heavy_asterisk> h \<tycolon> \<medium_left_bracket>\<medium_left_bracket> H \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<medium_right_bracket>\<medium_right_bracket>
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> h' \<tycolon> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h\<^sub>x \<tycolon> H\<^sub>x \<longmapsto> h\<^sub>r \<tycolon> H\<^sub>r \<heavy_asterisk> h' \<tycolon> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Heap_Cast_Goal_def Heap_Delimiter_def by (simp add: nu_exps) blast

(* theorem proc_cast': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> A \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A' \<longmapsto> B' \<brangle>"
  unfolding Procedure_def Cast_def by (auto 0 4) *)


subsection \<open>Conversion\<close>

(* definition AutoTag :: "bool \<Rightarrow> bool" ("\<^bold>a\<^bold>u\<^bold>t\<^bold>o _" [100] 99) where [\<nu>def]: "\<^bold>a\<^bold>u\<^bold>t\<^bold>o P \<longleftrightarrow> P"
lemma [\<nu>intro]: "[heap] \<^bold>c\<^bold>a\<^bold>s\<^bold>t U \<longmapsto> U' \<Longrightarrow> \<^bold>a\<^bold>u\<^bold>t\<^bold>o \<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> U \<longmapsto> U' \<brangle>"
  unfolding AutoTag_def Cast_def Procedure_def nop_def by auto *)
  
definition Conversion :: "('a::lrep \<longmapsto> 'b::lrep) \<Rightarrow> (heap\<times>'a) set \<Rightarrow> (heap\<times>'b) set \<Rightarrow> ( ('c::lrep) \<longmapsto> ('d::lrep)) \<Rightarrow> (heap\<times>'c) set \<Rightarrow> (heap\<times>'d) set \<Rightarrow> bool"
    ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)/ \<long_dobule_mapsto> _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)" [101,2,2,101,2,2] 100)
    where [\<nu>def]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> g \<blangle> U' \<longmapsto> V' \<brangle> \<longleftrightarrow>( \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> V' \<brangle> )"

lemma conversion: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f' \<blangle> U' \<longmapsto> V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U' \<longmapsto> V' \<brangle>"
  for f :: " ('a::lrep) \<longmapsto> ('b::lrep)" and f' :: " ('c::lrep) \<longmapsto> ('d::lrep)" unfolding Conversion_def by fast

lemma [\<nu>intro 2000]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U \<longmapsto> V \<brangle>" unfolding Conversion_def by fast

lemma conversion_cast[\<nu>intro 30]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U' \<longmapsto> V'\<brangle>"
  unfolding Conversion_def Procedure_def Cast_def CastDual_def Intro_def Dest_def
  by (metis LooseStateTy_introByStrict LooseStateTy_upgrade StrictStateTy_elim StrictStateTy_intro)

(* lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> U \<brangle> \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> (g \<nuInstrComp> f) \<blangle> U' \<longmapsto> V\<brangle>"
  unfolding Conversion_def using instr_comp by fast *)

theorem apply_proc_conv: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> S' \<longmapsto> T' \<brangle> \<long_dobule_mapsto> g \<blangle> S \<longmapsto> T\<brangle>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S' \<longmapsto> T' \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Conversion_def by auto

lemma conversion_trans: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n g \<blangle> Xg \<longmapsto> Yg \<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf \<brangle> \<long_dobule_mapsto> g \<blangle> Xg \<longmapsto> Yg \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf\<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>"
  unfolding Conversion_def by blast

subsection \<open>Function\<close>

datatype ('a,'b) argument_types = argument_type (assemble_arg: "'a \<Rightarrow> 'b") (dissemble_arg: "'b \<Rightarrow> 'a")
definition no_argument :: "('r, void \<times> 'r) argument_types"
  where "no_argument = argument_type (\<lambda>r. (void, r)) (\<lambda>(_,r). r)"
definition and_argument :: "('a, 'b \<times> 'r) argument_types \<Rightarrow> 'x itself \<Rightarrow> ('x \<times> 'a, ('x \<times> 'b) \<times> 'r) argument_types"
  where "and_argument args _ =
    argument_type (\<lambda>(x,r). case assemble_arg args r of (b,r') \<Rightarrow> ((x,b),r'))
      (\<lambda>((x,b),r). (x, dissemble_arg args (b,r)))"

definition Arguments :: " (heap \<times> 'a) set \<Rightarrow> (heap \<times> 'b) set \<Rightarrow> 'r set \<Rightarrow> ('a,'b \<times> 'r) argument_types \<Rightarrow> bool " where
  "Arguments A B R args \<longleftrightarrow> (\<forall>h a. (h,a) \<in> A \<longrightarrow> (h, fst (assemble_arg args a)) \<in> B \<and> snd (assemble_arg args a) \<in> R)
    \<and> (\<forall>h b r. (h,b) \<in> B \<and> r \<in> R \<longrightarrow> (h, dissemble_arg args (b,r)) \<in> A)"

lemma [\<nu>intro]: "Arguments \<tort_lbrace>r \<tycolon> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<tort_rbrace> \<tort_lbrace>Void\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<tort_rbrace> \<tort_lbrace>r \<tycolon> R\<tort_rbrace> no_argument"
  unfolding no_argument_def Arguments_def by (simp add: nu_exps)
lemma [\<nu>intro]: "Arguments \<tort_lbrace>a \<tycolon> A\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<tort_rbrace> \<tort_lbrace>b \<tycolon> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<tort_rbrace> R args
  \<Longrightarrow> Arguments \<tort_lbrace>a \<tycolon> A\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<tort_rbrace> \<tort_lbrace>b \<tycolon> B\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<tort_rbrace> R (and_argument args TYPE('xp))"
  for X :: "('xp::lrep, 'x) \<nu>" unfolding and_argument_def Arguments_def by (cases args) (auto 0 3 split: prod.split simp add: nu_exps) 
lemma [\<nu>intro]: "(\<And>c. Arguments \<tort_lbrace>x c \<tycolon> T c\<tort_rbrace> \<tort_lbrace>x' c \<tycolon> T' c\<tort_rbrace> R arg) \<Longrightarrow> Arguments \<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace> \<tort_lbrace>x' \<tycolon> ExNu T'\<tort_rbrace> R arg"
  unfolding Arguments_def by (simp add: nu_exps) blast

definition op_call :: " ('r1, 'a \<times> 'r2) argument_types \<Rightarrow> ('r3, 'b \<times> 'r2) argument_types \<Rightarrow> ('a \<longmapsto> 'b) \<Rightarrow> ('r1 \<longmapsto> 'r3)"
  where "op_call args rets f = (\<lambda>(h,r1). case assemble_arg args r1 of (a,r2) \<Rightarrow>
    (case f (h,a) of Success (h2,b) \<Rightarrow> Success (h2, dissemble_arg rets (b,r2))
        | PartialCorrect \<Rightarrow> PartialCorrect | Fail \<Rightarrow> Fail))"

lemma op_call:
  "Arguments \<tort_lbrace>sh \<tycolon> SH\<tort_rbrace> \<tort_lbrace>a \<tycolon> A\<tort_rbrace> R args \<Longrightarrow>
   Arguments \<tort_lbrace>sh' \<tycolon> SH'\<tort_rbrace> \<tort_lbrace>b \<tycolon> B\<tort_rbrace> R rets \<Longrightarrow>
   \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> a \<tycolon> A \<longmapsto> b \<tycolon> B \<brangle> \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_call args rets f \<blangle> sh \<tycolon> SH \<longmapsto> sh' \<tycolon> SH' \<brangle>"
  unfolding Procedure_def Function_def op_call_def Arguments_def
  by (cases args, cases rets) (auto 0 5 simp add: pair_forall split: state.split prod.split)

lemma rename_func: "f \<equiv> f' \<Longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<blangle> U \<longmapsto> \<R> \<brangle> \<Longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> U \<longmapsto> \<R> \<brangle>" by blast

subsubsection \<open>Recursive Function\<close>

lemma NuAddition_auto_func_no_prems: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> x \<tycolon> T \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<longmapsto> Y \<brangle> \<equiv> (P \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> x \<tycolon> T \<longmapsto> Y \<brangle>)"
  unfolding Auto_def Procedure_def Function_def atomize_eq by (simp add: nu_exps) blast

lemma NuAddition_anti_auto: "(P \<Longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> a \<tycolon> A \<longmapsto> B \<brangle>) \<equiv> Trueprop(\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> a \<tycolon> A \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<longmapsto> B \<brangle>)"
  by (simp add: Premise_def atomize_imp)
lemma recursive_func_help_1: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> x \<tycolon> A \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P \<longmapsto> B\<brangle> \<Longrightarrow> P \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> x \<tycolon> A \<longmapsto> B \<brangle>"
  by (simp add: Premise_def)

subsection \<open>Auto construct & destruct\<close>

definition AutoConstruct :: " 'exp \<Rightarrow> ('a::lrep \<longmapsto> 'b::lrep) \<Rightarrow> (heap \<times> 'a) set \<Rightarrow> (heap \<times> 'b) set \<Rightarrow> bool "("\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t _/ \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<blangle>_/ \<longmapsto> _ \<brangle>)" [20,101,10,10] 100)
  where [\<nu>def]:"AutoConstruct exp f S T \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>"
lemma AutoConstruct: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> AutoConstruct exp f S T \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)" for exp :: "'exp"
  unfolding AutoConstruct_def using apply_proc .

translations "CONST AutoConstruct exp f (s \<tycolon> S) T" \<rightleftharpoons> "CONST AutoConstruct exp f \<tort_lbrace>s \<tycolon> S\<tort_rbrace> T"
  "CONST AutoConstruct exp f S (t \<tycolon> T)" \<rightleftharpoons> "CONST AutoConstruct exp f S \<tort_lbrace>t \<tycolon> T\<tort_rbrace>"

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

translations "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> x \<tycolon> X \<^bold>@ A \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>@ A \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ \<tort_lbrace> a \<tycolon> A\<tort_rbrace> \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ \<tort_lbrace> a \<tycolon> A\<tort_rbrace>  \<longmapsto> Y \<^bold>@ B \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> x \<tycolon> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>@ A  \<longmapsto> Y \<^bold>@ B \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> y \<tycolon> Y \<^bold>@ B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A  \<longmapsto> \<tort_lbrace>y \<tycolon> Y\<tort_rbrace> \<^bold>@ B \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A  \<longmapsto> Y \<^bold>@ \<tort_lbrace>b  \<tycolon> B\<tort_rbrace> \<brangle>"


lemma index_here_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>index_def  index_here_def by auto
lemma index_here_mapper[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>index_def  index_here_def by auto
(* lemma index_left_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left f \<blangle> X \<^bold>@ (A \<^bold>a\<^bold>n\<^bold>d R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases f) auto
lemma index_right_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d A) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto *)
lemma index_stack_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (a \<tycolon> A\<heavy_comma> x \<tycolon> N) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) (simp add: nu_exps)
(* lemma index_left_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left f \<blangle> X \<^bold>@ (A \<^bold>a\<^bold>n\<^bold>d R) \<longmapsto> Y \<^bold>@ (B \<^bold>a\<^bold>n\<^bold>d R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases f) auto
lemma index_right_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d A) \<longmapsto> Y \<^bold>@ (L \<^bold>a\<^bold>n\<^bold>d B) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) auto *)
lemma index_stack_mapper[\<nu>intro]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (a \<tycolon> A\<heavy_comma> N) \<longmapsto> Y \<^bold>@ (b \<tycolon> B\<heavy_comma> N) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) (simp add: nu_exps)

(*
subsection \<open>Register\<close>

definition RegisterCollection :: " 'a \<Rightarrow> 'a " where "RegisterCollection x = x"

lemma RegisterCollection_rew[final_proc_rewrite]: "RegisterCollection x \<equiv> x" unfolding RegisterCollection_def .
lemma Labelled_rew[final_proc_rewrite]: "Labelled name x \<equiv> x" unfolding Labelled_def .

lemma index_reg_getter[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ RegisterCollection A \<brangle>"
  unfolding RegisterCollection_def .
lemma index_reg_mapper[\<nu>intro]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ A  \<longmapsto> Y \<^bold>@ B \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ RegisterCollection A \<longmapsto> Y \<^bold>@ RegisterCollection B \<brangle>"
  unfolding RegisterCollection_def .

(* definition new_reg_0 :: "(('x::lrep) \<times> ('R::lrep) \<flower> void) \<Rightarrow> ('R \<flower> 'x register) state"
  where "new_reg_0 s = (case s of Proc_Ctx (x,R) void \<Rightarrow> StatOn (Proc_Ctx R (Register (LABEL _) x)))"
definition new_reg_L :: "('G, 'G2, 't, 'x register \<times> 't) index \<Rightarrow> (('x::lrep) \<times> ('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg_L adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (Register (LABEL _) x,t)) G)))"
definition new_reg_R :: "('G, 'G2, 't, 't \<times> 'x register) index \<Rightarrow> (('x::lrep) \<times> ('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg_R adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (t, Register (LABEL _) x)) G)))" *)

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

lemma store_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> Labelled name X \<^bold>@ G \<longmapsto> Labelled name Y \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c store_reg idx \<blangle> G\<heavy_comma> Y \<longmapsto> G2 \<brangle>"
  unfolding \<nu>index_def \<nu>def store_reg_def by (cases idx) auto

lemma load_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> Labelled name  \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>@ R \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c load_reg idx \<blangle> R \<longmapsto> R \<heavy_comma> x \<tycolon> X \<brangle>"
  unfolding \<nu>index_def \<nu>def load_reg_def by auto

lemma move_reg: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> Labelled name X \<^bold>@ R \<longmapsto> Labelled name Void \<^bold>@ R' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c move_reg idx \<blangle> R \<longmapsto> R' \<heavy_comma> X \<brangle>"
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

ML_file NuBasics.ML
ML_file "./general/binary_tree.ML"
ML_file "./general/auto_level.ML"
(* ML_file "./library/path.ML" *)
ML \<open>Syntax.parse_term @{context} "xxx"\<close>
ML_file \<open>library/application.ML\<close>
ML_file "./library/general.ML"
ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/procedure.ML"
(* ML_file "./library/exty.ML" *)

ML_file NuSys.ML
ML_file "./library/processors.ML"
ML_file "./library/obtain.ML"
ML_file "./library/QuantExpansion.ML"
ML_file NuToplevel.ML

section \<open>Attributes and Commands\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<nu>instr"}, NuInstructions.list_definitions #> map snd))  \<close>
attribute_setup \<nu>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<nu>-system\<close>

attribute_setup \<nu>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (NuProcessor.get_attr ctx name) (ctx,toks))
  || Scan.lift NuProcessor.process_attr\<close>
  \<open>Evaluate the \<nu>-system process or the process of the given processor on the target theorem\<close>

method_setup \<nu>reason = \<open>let open Scan Parse in
  (succeed [] || Scan.repeat (Attrib.thms -- Scan.lift Parse.int)) >> (fn ths => fn ctx =>
  Method.SIMPLE_METHOD (Nu_Reasoner.reason_tac (Nu_Reasoner.add_intro_rules ths ctx)))
end\<close>

ML \<open>

local open Scan NuToplevel NuSys Parse 
val nustatement = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- opt_attribs -- Scan.repeat1 Parse.propp);
val structured_statement =
  nustatement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));
in

(* val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>exty_simproc\<close> "setup the pecific simproc for \<^const>\<open>ExTy\<close>"
  (Parse.binding >> NuExTyp.set_simproc_cmd) *)

val statement1 = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.propp);
val requires_statement = Scan.optional (Parse.$$$ "requires" |-- Parse.!!! statement1) [];
val premises_statement = Scan.optional (Parse.$$$ "premises" |-- Parse.!!! statement1) [];
val requires_opt1 = Scan.option (Parse.$$$ "requires" |-- Parse.term);
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- (requires_statement -- premises_statement)) >>
        (fn (((((b,arg),ret),fixes),includes),preconds) =>  
            (begin_proc_cmd b arg ret fixes includes preconds)));

val loop_variables = $$$ "var" |-- !!! vars;
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close> "begin a recursive procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- loop_variables -- Parse.for_fixes
            -- Scan.optional Parse_Spec.includes [] -- (requires_statement -- premises_statement)) >>
        (fn ((((((b,arg),ret),vars),fixes),includes),preconds) =>  
            (begin_rec_proc_cmd b arg ret (vars,fixes) includes preconds)));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>\<nu>cast\<close> "begin a procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- option ($$$ "and" |-- Parse.term)
            -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- (requires_statement -- premises_statement)) >>
        (fn ((((((b,arg),ret),addtional_prop),fixes),includes),preconds) =>  
            (begin_cast_cmd b arg ret addtional_prop fixes includes preconds)));

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
    (fn toks => (Toplevel.proof (NuProcessor.powerful_process (toks @ [Token.eof])),
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
  Outer_Syntax.command \<^command_keyword>\<open>\<Longrightarrow>\<close> "name the star fact"
    (Parse.binding -- Parse.opt_attribs >> (Toplevel.proof o NuToplevel.name_star_fact_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>drop_fact\<close> "drop a fact"
    (Parse.list Parse.binding >> (fn names => Toplevel.proof (fold NuToplevel.drop_fact_cmd names)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor\<close> "define \<nu>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword || Parse.string)
          -- Parse.nat -- Parse.term -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
        >> NuProcessor.setup_cmd)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor_resolver\<close> "define \<nu>processor resolver"
      (Parse.binding -- Parse.nat -- (Parse.term -- Parse.for_fixes) -- Parse.name_position -- Scan.optional Parse.text ""
        >> (fn ((((b,precedence),pattern),facts),comment) => NuProcessors.setup_resolver b precedence pattern facts comment))

end
\<close>

attribute_setup intro_forall = \<open>Scan.lift (Scan.repeat Args.var) >> (fn tms =>
  Thm.rule_attribute [] (fn ctx => fn th => 
    let open Thm
    val vs = add_vars th []
    val foralls = map (fn tm => case find_first (fn v => #1 (dest_Var (term_of v)) = tm) vs
                  of SOME y => y | _ => error (#1 tm ^ " is not a var ")) tms
    in Drule.forall_intr_list foralls th end)) \<close>

subsection \<open>Application method\<close>

attribute_setup \<nu>application_method = \<open>Scan.lift (Parse.int -- (Parse.int >> ~)) >> (fn (idx,cost) =>
  Thm.declaration_attribute (fn th => NuApply.update (cost,{thm=th, applicant_idx = idx})))\<close>

declare
  apply_proc[\<nu>application_method 1 100]
  apply_proc_conv[\<nu>application_method 2 -1000]
  "cast"[\<nu>application_method 1 90]
  "cast"[OF _ cast_\<nu>app[OF Argument_I], \<nu>application_method 1 80]
  "cast"[OF _ cast_heap_\<nu>app[OF Argument_I], \<nu>application_method 1 80]
  "cast"[OF _ cast_whole_heap_\<nu>app[OF Argument_I], \<nu>application_method 1 70]
  "cast"[OF _ cast_whole_heap_\<nu>app[OF Argument_I, OF cast_heap_conversion],
      \<nu>application_method 2 20]

(*lemmas apply_func[\<nu>application_method 3 70] = apply_proc[OF _ op_call]*)
lemmas apply_func_conv[\<nu>application_method 3 100] = apply_proc_conv[OF _ _ op_call, rotated 1 1]

(* consts \<nu>Application_Rewrite :: bool
setup_\<nu>application_method \<open>\<nu>Application_Rewrite\<close> 1000 \<open>PROP P &&& A = B\<close> | \<open>PROP P &&& (A \<equiv> B)\<close> = \<open>
  fn ctx => fn applicants => fn major =>
    let
      fun is_simprule (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _)) = true
          | is_simprule (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _) = true
          | is_simprule _ = false
      val applicants = List.filter (is_simprule o Thm.concl_of) applicants
    in
      if null applicants then Seq.empty else Seq.make (fn () =>
        SOME (Simplifier.simplify (Raw_Simplifier.clear_simpset ctx addsimps applicants) major, Seq.empty))
    end
\<close>*)

subsection \<open>Quantification Expansion\<close>

simproc_setup named_forall_expansion ("All (P :: 'a named 'names \<Rightarrow> bool)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.forall_expansion)\<close>

simproc_setup named_exNu_expansion ("\<tort_lbrace>x \<tycolon> ExNu (P :: 'a named 'names \<Rightarrow> ('b,'c)\<nu>)\<tort_rbrace>") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.ExNu_expansion)\<close>

simproc_setup named_pureAll_expansion ("Pure.all (P :: 'a named 'names \<Rightarrow> prop)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.pure_All_expansion)\<close>

section \<open>Processors\<close>

subsection \<open>Controls\<close>

\<nu>processor set_auto_level 10 \<open>PROP P\<close> \<open>(fn ctx => fn th => NuParse.auto_level_force #->
  (fn auto_level' => NuProcessor.internal_process (AutoLevel.reduce auto_level' ctx) th #> (fn x => raise ProcessTerminated x)))\<close>

\<nu>processor repeat 12 \<open>PROP P\<close> \<open>let
    fun repeat n f x = if n <= 0 then x else ((repeat (n-1) f (f x)) handle _ => x)
  in fn ctx => fn th => Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*")
    >> (fn (tok,n) => fn _ => (case Int.fromString n of SOME n => funpow n | _ => repeat 32)
        (NuProcessor.simple_process ctx #> (fn p => p [tok,Token.eof] |> #1)) th)
  end\<close>

subsection \<open>Constructive\<close>

\<nu>processor accept_proc 300 \<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn th => Scan.succeed (fn _ => NuSys.accept_proc ctx th)\<close>

\<nu>processor move_fact 50 \<open>(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> T) \<and>\<^sup>\<nu>\<^sub>a\<^sub>u\<^sub>t\<^sub>o P)\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta RS @{thm move_fact_to_star1} handle THM _ => meta RS @{thm move_fact_to_star2})\<close>

\<nu>processor "apply" 9000 \<open>P\<close> \<open> fn ctx => fn meta => NuApplicant.parser >> (fn binding => fn _ =>
    let open NuBasics NuSys
  val procs = NuApplicant.applicant_thms ctx binding
  (* val xa = hd procs |> Thm.concl_of |> auto_fusion_arity |> @{print}
  val meta =funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema} #> accept_proc ctx) meta
    handle THM _ => funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema'} #> accept_proc ctx) meta *)
val ctx = NuSys.load_specthm meta ctx in NuSys.apply ctx procs meta end)\<close>

(* \<nu>processor cast 8900 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
  \<open> fn ctx => fn meta => (Parse.$$$ "cast" |-- (Parse.$$$ "(" |-- Parse.list NuProcedure.parser --| Parse.$$$ ")" || (NuProcedure.parser >> single)))
    >> (fn bindings => fn _ =>
      let val ctx = NuSys.load_specthm meta ctx
      in fold (NuSys.apply_casts ctx o NuProcedure.cast_thm ctx) bindings meta end)\<close> *)

\<nu>processor set_param 5000 \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Parse.term >> (fn term => fn _ =>
    NuSys.set_param_cmd ctx term meta)\<close>

\<nu>processor rule 7100 \<open>P \<Longrightarrow> PROP Q\<close>
  \<open>fn ctx => fn meta => (NuApplicant.parser -- Parse.opt_attribs) >> (fn (name,attrs) => fn _ =>
    let open NuBasics
    val ctx = NuSys.load_specthm meta ctx
    val attrs = map (Attrib.attribute_cmd ctx o Attrib.check_src ctx) attrs
    val ths = case try (Proof_Context.get_fact ctx) (Facts.Named (name, NONE)) of SOME x => x
         | NONE => Proof_Context.get_fact ctx (Facts.Named (name |> apfst (fn s => s ^ "_\<nu>proc"), NONE))
    val (ths,ctx) = fold_map (Thm.proof_attributes attrs) ths ctx
    in elim_SPEC meta |> apfst (perhaps (try (fn th => @{thm Argument_I} RS th)))
            |> apfst (fn major =>
    case Thm.biresolution NONE false (ths |> map (pair false) |> @{print}) 1 major |> Seq.pull
      of SOME (th, _) => th | _ => raise THM ("RSN: no unifiers", 1, major::ths)) |> intro_SPEC end)\<close>

(* \<nu>processor rule_by_COMP 1000 \<open>PROP P \<Longrightarrow> PROP Q\<close>
  \<open>fn ctx => fn meta => (Parse.$$$ "\<Longleftarrow>'" |-- NuProcedure.parser -- Parse.opt_attribs) >> (fn (name,attrs) => fn _ =>
    let open NuBasics
    val ctx = NuSys.load_specthm meta ctx
    val attrs = map (Attrib.attribute_cmd ctx o Attrib.check_src ctx) attrs
    val [th] = Proof_Context.get_fact ctx (Facts.Labelled (name, NONE)) 
    val ([th],ctx) = fold_map (Thm.proof_attributes attrs) [th] ctx
    in elim_SPEC meta |> apfst (fn major => th COMP major) |> intro_SPEC end)\<close>
*)

\<nu>processor set_\<nu>current 100 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  raise Bypass (SOME (meta RS @{thm set_\<nu>current})))\<close>

subsubsection \<open>Sub-procedure\<close>

\<nu>processor begin_sub_procedure 7000 \<open>PROP Q\<close> \<open>let open Parse Scan in fn ctx => fn meta =>
  $$$ "\<medium_left_bracket>" |-- optional ($$$ "premises" |-- and_list (binding -- opt_attribs)) [] >> (fn prems => fn () =>
  raise Process_State_Call' (meta, NuToplevel.begin_block_cmd prems true)
) end\<close>

\<nu>processor end_sub_procedure 7000 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>let open Parse Scan in fn ctx => fn meta =>
  $$$ "\<medium_right_bracket>" >> (fn x => fn () =>
  raise Process_State_Call' (meta, NuToplevel.end_block_cmd true)
) end\<close>

(*
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "construct nested sub-procedure"
    (optional ($$$ "(" |-- and_list (binding -- opt_attribs) --| $$$ ")") [] >> (Toplevel.proof' o NuToplevel.begin_block_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "finish the nested sub-procedure construction"
    (Scan.succeed (Toplevel.proof' NuToplevel.end_block_cmd));

*)

subsubsection \<open>Existential elimination\<close>

\<nu>processor auto_existential_elimination 50 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n \<tort_lbrace>x \<tycolon> ExNu T\<tort_rbrace>\<close>
  \<open>fn ctx => fn meta => Scan.succeed (fn () =>
    raise Process_State_Call' (meta, NuObtain.auto_choose))\<close>

subsection \<open>Simplifiers & Resonings\<close>

\<nu>processor \<nu>simplifier 40 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>NuProcessors.simplifier []\<close>
(* \<nu>processor \<nu>simplifier_final 9999 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close> *)

\<nu>processor \<nu>reason 1000 \<open>PROP P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  let open NuBasics
    val meta' = elim_SPEC meta
      |> apfst (Nu_Reasoner.reason (NuSys.load_specthm meta ctx))
      |> intro_SPEC
  in if Thm.prop_of meta = Thm.prop_of meta' then raise Bypass (SOME meta') else meta' end)\<close>

subsection \<open>Literal operations\<close>

\<nu>processor literal_constructor 9500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.cartouche >> (fn term => fn _ =>
  let val term = Syntax.read_term ctx term |> Thm.cterm_of ctx |> Simplifier.rewrite ctx |> Thm.rhs_of
        val ctx = NuSys.load_specthm meta ctx
  in NuSys.auto_construct ctx term meta end)\<close>

section \<open>Mechanism III\<close>

subsection \<open>Variant Cast\<close>

definition Variant_Cast :: " ('stack_low, 'stack) typing \<Rightarrow> ('heap_low, 'heap) typing
    \<Rightarrow> 'vars \<Rightarrow> ('stack_low, 'vars) \<nu> \<Rightarrow> ('heap_low, 'vars) \<nu> \<Rightarrow> bool "
      ("\<^bold>v\<^bold>a\<^bold>r\<^bold>i\<^bold>a\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<^bold>h\<^bold>e\<^bold>a\<^bold>p _/ \<longmapsto> _/ \<tycolon> _/ \<^bold>a\<^bold>n\<^bold>d _" )
  where "Variant_Cast stack heap insts stackTy' heapTy' \<longleftrightarrow>
    \<tort_lbrace>stack\<tort_rbrace> = \<tort_lbrace>insts \<tycolon> stackTy'\<tort_rbrace> \<and> \<tort_lbrace>heap\<tort_rbrace> = \<tort_lbrace>insts \<tycolon> heapTy'\<tort_rbrace>"

lemma Variant_Cast_I:
  "s = pattern\<^sub>s vars \<Longrightarrow> h = pattern\<^sub>h vars \<Longrightarrow>
  Variant_Cast (s \<tycolon> S) (h \<tycolon> H) vars (S <auto-down-lift> pattern\<^sub>s) (H <auto-down-lift> pattern\<^sub>h)"
  unfolding Variant_Cast_def by auto

lemma Variant_Cast_I_always:
  "s = pattern\<^sub>s vars \<Longrightarrow> h = pattern\<^sub>h vars \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e always vars \<Longrightarrow>
  Variant_Cast (s \<tycolon> S) (h \<tycolon> H) vars (S <auto-down-lift> pattern\<^sub>s <auto-where> Collect always) (H <auto-down-lift> pattern\<^sub>h)"
  unfolding Variant_Cast_def Auto_def by (auto simp add: nu_exps)

definition Variants_Quant_Tag :: " ('vars \<Rightarrow> unit) \<Rightarrow> 'a \<Rightarrow> 'a" ("<expand'_vars>")
  where "Variants_Quant_Tag vars a = a"
translations " <expand_vars> tag (x \<tycolon> T)" \<rightleftharpoons> "x \<tycolon> <expand_vars> tag T"

(* definition Variants_Subj :: " ('vars \<Rightarrow> unit) \<Rightarrow> ('vars \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>v\<^bold>a\<^bold>r\<^bold>i\<^bold>a\<^bold>n\<^bold>t\<^bold>s _ \<^bold>s\<^bold>u\<^bold>b\<^bold>j _")
  where "Variants_Subj vars subj \<longleftrightarrow> True"
lemma Variants_Subj_I: "Variants_Subj vars subj" unfolding Variants_Subj_def .. *)

lemma case_prod_expn_I: "A = B x y \<Longrightarrow> A = case_prod B (x,y)" by simp
lemma case_named_expn_I: "A = B x \<Longrightarrow> A = case_named B (tag x)" by simp

ML_file_debug \<open>library/variables_tag.ML\<close>

\<nu>processor vars_by_pattern 110 \<open>Variant_Cast (s \<tycolon> S) (h \<tycolon> H) vars S' H' \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn meta => 
let open Parse Scan NuHelp NuBasics in
  ($$$ "var" |-- list1 params -- option ($$$ "in" |-- list1 term) -- option ($$$ "heap" |-- list1 term) -- Scan.option ($$$ "always" |-- term))
    >> (fn ((((vars, stack_schema), heap_schema)), always) => fn _ =>
      NuVariablesTag.variables_tag_pattern_match (flat vars) stack_schema heap_schema always ctx meta |> @{print})
||
  (list1 term -- Scan.option ($$$ "always" |-- term) >> (fn (vars, always) => fn _ =>
      NuVariablesTag.variables_tag_terms vars always ctx meta) )
end\<close>

subsection \<open>Auto Reasoners\<close>

ML_file "library/reasoners.ML"

\<nu>reasoner \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P\<close> 10 = \<open>Nu_Reasoners.premise_tac\<close>

end