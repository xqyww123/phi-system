theory NuSys
  imports NuPrime "./Phi_Logic_Programming_Reasoner/Phi_Logic_Programming_Reasoner"
    "HOL-Library.Adhoc_Overloading" BI_for_Phi
  keywords
    "proc" "rec_proc" (*"\<phi>cast"*) :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "\<Longleftarrow>" "\<Longleftarrow>'" "$" "subj"
    "var" "invar" "\<Longrightarrow>" "goal" "\<exists>" "heap" "stack" "throws"
    "argument" "return" "on" "affirm" :: quasi_command
  and ";;" "\<medium_left_bracket>" "\<medium_right_bracket>" "\<medium_right_bracket>." :: prf_decl % "proof"
  and "\<phi>processor" :: thy_decl % "ML"
  and (* "\<phi>interface" "\<phi>export_llvm" *) "\<phi>overloads" :: thy_decl
abbrevs
  "!!" = "!!"
  and "<argument>" = "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t"
  and "<param>" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
  and "<label>" = "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l"
      and "<subty>" = "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e"
      and "<by>" = "\<^bold>b\<^bold>y"
      and "<simplify>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y"
      and "<when>" = "\<^bold>w\<^bold>h\<^bold>e\<^bold>n"
      and "<try>" = "\<^bold>t\<^bold>r\<^bold>y"
  and "<obligation>" = "\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n"
  and ">->" = "\<Zinj>"
  and "<;>" = "\<Zcomp>"
  and "<@GOAL>" = "\<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L"
  and "<val>" = "\<^bold>v\<^bold>a\<^bold>l"
  and "<ret>" = "\<^bold>r\<^bold>e\<^bold>t"
begin

declare [ [ML_debugger, ML_exception_debugger] ]

chapter \<open>An Interactive Programming Language embedded in Isar\<close>

section \<open>\<phi>-Type\<close>

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete set "


subsubsection \<open>Definitions\<close>

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a set" (infix "\<Ztypecolon>" 20) where " (x \<Ztypecolon> T) = (T x)"

lemma typing_inhabited: "p \<in> (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (x \<Ztypecolon> T)"
  unfolding Inhabited_def \<phi>Type_def by blast

lemma \<phi>Type_eqI:
  \<open>(\<forall>x p. p \<in> (x \<Ztypecolon> a) \<longleftrightarrow> p \<in> (x \<Ztypecolon> b)) \<Longrightarrow> a = b\<close>
  unfolding \<phi>Type_def by blast



paragraph \<open>Syntax\<close>

abbreviation (in \<phi>fiction) COMMA
  :: \<open>('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn\<close> (infixl "\<heavy_comma>" 13)
  where \<open>COMMA \<equiv> (*)\<close>

(*
setup \<open>(Sign.add_trrules (let open Ast 
      fun nuty x y = Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable x, Variable y]
      fun wrap_ele tm = Appl [Constant \<^const_syntax>\<open>Ele\<close>, tm]
      fun wrap_nuty x y = wrap_ele (nuty x y)
    in [
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.COMMA", nuty "x" "T", Variable "U"],
        Appl [Constant "\<^const>local.COMMA", wrap_nuty "x" "T", Variable "U"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.COMMA", Variable "U", nuty "x" "T"],
        Appl [Constant "\<^const>local.COMMA", Variable "U", wrap_nuty "x" "T"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", nuty "x" "T", Variable "U"],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", wrap_nuty "x" "T", Variable "U"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", nuty "x" "T"],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", wrap_nuty "x" "T"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", nuty "x" "T", Variable "U"],
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", wrap_nuty "x" "T", Variable "U"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", Variable "U", nuty "x" "T"],
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", Variable "U", wrap_nuty "x" "T"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.CurrentConstruction", Variable "s", Variable "R", nuty "x" "T"],
        Appl [Constant "\<^const>local.CurrentConstruction", Variable "s", Variable "R", wrap_nuty "x" "T"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.PendingConstruction", Variable "f", Variable "s", Variable "R", nuty "x" "T"],
        Appl [Constant "\<^const>local.PendingConstruction", Variable "f", Variable "s", Variable "R", wrap_nuty "x" "T"])
  ] end))\<close>
*)

subsubsection \<open>Properties\<close>

context \<phi>empty_sem begin

paragraph \<open>Semantic Type\<close>

definition \<phi>SemType :: "'VAL set \<Rightarrow> 'TY \<Rightarrow> bool"
  where [\<phi>def]: \<open>\<phi>SemType S TY \<longleftrightarrow> S \<subseteq> Well_Type TY\<close>

abbreviation \<phi>\<phi>SemType :: "('VAL, 'a) \<phi> \<Rightarrow> 'TY \<Rightarrow> bool"
  where \<open>\<phi>\<phi>SemType T TY \<equiv> (\<forall>x. \<phi>SemType (x \<Ztypecolon> T) TY)\<close>

lemma \<phi>SemType_unique:
  \<open> S \<noteq> {}
\<Longrightarrow> \<phi>SemType S T1
\<Longrightarrow> \<phi>SemType S T2
\<Longrightarrow> T1 = T2\<close>
  unfolding \<phi>SemType_def subset_iff
  using Well_Type_unique by blast

definition SemTyp_Of :: \<open>'VAL set \<Rightarrow> 'TY\<close>
  where \<open>SemTyp_Of S = (@TY. \<phi>SemType S TY)\<close>

lemma SemTyp_Of_I[intro!, simp]:
  \<open>S \<noteq> {} \<Longrightarrow> \<phi>SemType S TY \<Longrightarrow> SemTyp_Of S = TY\<close>
  unfolding SemTyp_Of_def
  using \<phi>SemType_unique by blast 

paragraph \<open>Zero Value\<close>

definition \<phi>Zero :: "'TY \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool"
  where [\<phi>def]: "\<phi>Zero ty T x \<longleftrightarrow> Zero ty \<in> (x \<Ztypecolon> T)"

paragraph \<open>Equality\<close>

definition \<phi>Equal :: "('VAL,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<phi>def]: "\<phi>Equal T can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 res.
    can_eq x1 x2 \<and> p1 \<in> (x1 \<Ztypecolon> T) \<and> p2 \<in> (x2 \<Ztypecolon> T)
      \<longrightarrow> Can_EqCompare res p1 p2 \<and> (EqCompare p1 p2 = eq x1 x2))"

end



(* declare split_paired_All[simp del] split_paired_Ex[simp del] *)



(* ML \<open>Theory.setup (Sign.add_trrules (let open Ast 
      fun nuty x y = Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable x, Variable y]
      fun wrap_ele tm = Appl [Constant \<^const_syntax>\<open>Ele\<close>, tm]
      fun wrap_nuty x y = wrap_ele (nuty x y)
      fun subj x = Appl [Constant \<^const_syntax>\<open>Subjection\<close>, x, Variable "P"]
    in [
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", subj (nuty "x" "T"), Variable "U"],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", subj (wrap_nuty "x" "T"), Variable "U"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", subj (nuty "x" "T")],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", subj (wrap_nuty "x" "T")]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", subj (nuty "x" "T"), Variable "U"],
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", subj (wrap_nuty "x" "T"), Variable "U"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", Variable "U", subj (nuty "x" "T")],
        Appl [Constant "\<^const>local.\<phi>Procedure_no_exception", Variable "f", Variable "U", subj (wrap_nuty "x" "T")])
  ] end))\<close>
*)


section \<open>Basic Constructions of the Deductive Programming\<close>

subsection \<open>Preliminary\<close>

declare Product_Type.prod.case[\<phi>def]

named_theorems \<phi>programming_simps \<open>Simplification rules used in the interactive programming\<close>
and \<phi>lemmata \<open>Contextual facts during the programming. They are automatically
       aggregated from every attached \<^prop>\<open>P\<close> in \<^prop>\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk in [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Sth \<^bold>s\<^bold>u\<^bold>b\<^bold>j P\<close>
       during the programming. Do not modify it manually because it is managed automatically and
       cleared frequently\<close> 

ML_file NuHelp.ML
ML_file \<open>library/NuSimpCongruence.ML\<close>

subsubsection \<open>Reasoning Tags\<close>

definition \<open>Filter_Out_Values (T::'a set) (T'::'a set) \<equiv> Trueprop (T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T')\<close>
definition \<open>View_Shift_Reasoning T \<equiv> Trueprop T\<close>

subsubsection \<open>Construction Mode\<close>

consts programming_mode :: mode
       view_shift_mode  :: mode

subsection \<open>Current Construction & Pending Construction\<close>

(* syntax "_codeblock_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> bool"  ("(2\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _/  \<^bold>a\<^bold>s '\<open>_'\<close>/ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>)" [100,0,0] 3)
syntax "_codeblock_" :: "idt \<Rightarrow> logic \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>" [100,0] 3) *)

definition (in \<phi>empty)
  CurrentConstruction :: " mode
                        \<Rightarrow> ('RES_N \<Rightarrow> 'RES)
                        \<Rightarrow> ('FIC_N,'FIC) assn
                        \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> bool "
  where "CurrentConstruction mode s R S \<longleftrightarrow> s \<in> (INTERP_COM (R * S))"

abbreviation (in \<phi>empty) Programming_CurrentConstruction ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_]/ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _" [1000,1000,11] 10)
  where \<open>Programming_CurrentConstruction \<equiv> CurrentConstruction programming_mode\<close>

abbreviation (in \<phi>empty) View_Shift_CurrentConstruction ("\<^bold>v\<^bold>i\<^bold>e\<^bold>w _ [_]/ \<^bold>i\<^bold>s _" [1000,1000,11] 10)
  where \<open>View_Shift_CurrentConstruction \<equiv> CurrentConstruction view_shift_mode\<close>

definition (in \<phi>empty)
  PendingConstruction :: " ('ret,'RES_N,'RES) proc
                        \<Rightarrow> ('RES_N \<Rightarrow> 'RES)
                        \<Rightarrow> ('FIC_N,'FIC) assn
                        \<Rightarrow> ('ret sem_value \<Rightarrow> ('FIC_N,'FIC) assn)
                        \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> bool "
    ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ [_]/ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _/ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _" [1000,1000,1000,11,11] 10)
    where "PendingConstruction f s R S E \<longleftrightarrow> f s \<subseteq> \<S> (\<lambda>ret. INTERP_COM (R * S ret)) (INTERP_COM (R * E))"

lemma (in \<phi>empty) CurrentConstruction_D: "CurrentConstruction mode s H T \<Longrightarrow> Inhabited T"
  unfolding CurrentConstruction_def Inhabited_def by (clarsimp simp add: \<phi>expns; blast)

lemma (in \<phi>empty) CurrentConstruction_mk_elim_rule:
  "CurrentConstruction mode s H T \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  using CurrentConstruction_D by blast



subsubsection \<open>Rules for Constructing Programs\<close>

context \<phi>empty begin

paragraph \<open>Construct Procedure\<close>

lemma \<phi>apply_proc:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow>(\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E)"
  unfolding \<phi>Procedure_def CurrentConstruction_def PendingConstruction_def bind_def by (auto 0 5)

lemma \<phi>accept_proc:
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1
\<Longrightarrow> (\<And>s' ret. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T ret \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (g ret) \<^bold>o\<^bold>n s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<bind> g) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 + E2"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .

lemma \<phi>return_when_unreachable:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>_. T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<ggreater> Return (sem_value undefined)) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>_. T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  for f :: \<open>(unreachable, 'RES_N, 'RES) proc\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .

lemma \<phi>return_additional_unit:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<bind> (\<lambda>v. Return (\<phi>V_pair v \<phi>V_none))) \<^bold>o\<^bold>n s [R]
        \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>ret. T (\<phi>V_fst ret)) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def \<phi>V_pair_def
    \<phi>V_fst_def \<phi>V_snd_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .

lemma \<phi>return:
  " \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T'
\<Longrightarrow> T' = T ret
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (Return ret) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s 0"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff
  by simp+

lemma \<phi>reassemble_proc_final:
  "(\<And>s H. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> S \<longmapsto> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>"
  unfolding CurrentConstruction_def PendingConstruction_def \<phi>Procedure_def bind_def pair_All
  by blast

paragraph \<open>Construct View Shift\<close>

lemma \<phi>make_view_shift:
  \<open> (\<And>s R. \<^bold>v\<^bold>i\<^bold>e\<^bold>w s [R] \<^bold>i\<^bold>s S \<Longrightarrow> (\<^bold>v\<^bold>i\<^bold>e\<^bold>w s [R] \<^bold>i\<^bold>s S') \<and> P)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding CurrentConstruction_def View_Shift_def by blast

paragraph \<open>Rename Procedure\<close>

lemma \<phi>rename_proc: "f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>" by fast

lemma \<phi>rename_proc_with_goal:
  \<open>f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding GOAL_CTXT_def using \<phi>rename_proc .

paragraph \<open>View Shift & Subtyping\<close>

lemma (in \<phi>empty) \<phi>apply_view_shift_P:
  "CurrentConstruction mode blk R S \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (CurrentConstruction mode blk R S') \<and> P"
  unfolding CurrentConstruction_def View_Shift_def
  by (simp_all add: pair_All \<phi>expns)

lemma (in \<phi>empty) \<phi>apply_view_shift:
  "CurrentConstruction mode blk R S \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> CurrentConstruction mode blk R S'"
  unfolding CurrentConstruction_def View_Shift_def
  by (simp_all add: pair_All \<phi>expns)

lemma (in \<phi>empty) "\<phi>cast":
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T'"
  unfolding CurrentConstruction_def Imply_def
  by (simp_all add: pair_All \<phi>expns) blast

lemma (in \<phi>empty) "\<phi>cast_P":
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T') \<and> P"
  unfolding CurrentConstruction_def Imply_def
  by (simp_all add: pair_All \<phi>expns) blast

end

paragraph \<open>Simplification in the Programming\<close>


lemma (in \<phi>empty) [simp]:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P"
  unfolding CurrentConstruction_def by (simp_all add: \<phi>expns pair_All)

lemma (in \<phi>empty) [simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> B) \<and> C \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> (B \<and> C)"
  by simp

lemma (in \<phi>empty) \<phi>ExTyp_strip:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (ExSet T)) \<equiv> (\<exists>c. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T c)"
  unfolding CurrentConstruction_def atomize_eq by (simp_all add: \<phi>expns pair_All)

lemma (in \<phi>empty) Subjection_simp_proc_arg'[simp]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> = (P \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)"
  (* and Subjection_simp_func_arg[simp]: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<lbrace> T \<and>\<^sup>s P \<longmapsto> Y \<rbrace> = (P \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<lbrace> T \<longmapsto> Y \<rbrace>)" *)
  unfolding \<phi>Procedure_def by (simp add: \<phi>expns) blast

lemmas (in \<phi>empty) Subjection_simp_proc_arg[unfolded atomize_eq[symmetric]] = Subjection_simp_proc_arg'



subsection \<open>Antecedents of Reasoning - Part I\<close>


subsubsection \<open>Mode\<close>

consts MODE_\<phi>EXPN :: mode \<comment> \<open>relating to named_theorems \<open>\<phi>expn\<close>\<close>

abbreviation \<phi>expn_Premise ("<\<phi>expn> _" [26] 26) where \<open>\<phi>expn_Premise \<equiv> Premise MODE_\<phi>EXPN\<close>


subsubsection \<open>Label tag\<close> (*depreciated*)

datatype label = LABEL_TAG "unit \<Rightarrow> unit"

lemma [cong]: "LABEL_TAG x \<equiv> LABEL_TAG x"  using reflexive .
lemma label_eq: "x = y" for x :: label by (cases x, cases y) auto

syntax "_LABEL_" :: "idt \<Rightarrow> label" ("LABEL _" [0] 1000)
translations "LABEL name" == "CONST LABEL_TAG (\<lambda>name. ())"



subsubsection \<open>Parameter Input\<close>

definition ParamTag :: " 'a \<Rightarrow> bool" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 26) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> True"

text (in \<phi>empty)
 \<open>The \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> represents \<^term>\<open>x\<close> is a parameter that should be given by user, e.g.,
  \<^prop>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_size \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int value bit_size \<lbrace> A \<longmapsto> B \<rbrace>\<close>.
  The \<phi>-processor `set_param` processes the \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> antecedent.\<close>

lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
lemma [elim!,\<phi>reason_elim!]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto
lemma [cong]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<longleftrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" ..



subsubsection \<open>Label Input\<close> (*depreciated*)

definition LabelTag :: " label \<Rightarrow> bool" ("\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l _" [1000] 26) where "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<equiv> True"

text \<open>The \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> indicate \<^term>\<open>x\<close> is a \<^typ>\<open>label\<close> that should be set by user, e.g.,
  \<^prop>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l name \<Longrightarrow> do_something_relating name\<close>.
  The \<phi>-processor `set_label` processes the \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> antecedent.\<close>

lemma LabelTag: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x" unfolding LabelTag_def ..
lemma [elim!,\<phi>reason_elim!]: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<Longrightarrow> C \<Longrightarrow> C" by auto



subsubsection \<open>Explicit name tag\<close> (*depreciated*)

definition Labelled :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "Labelled name x = x" \<comment>\<open>name tag\<close>

(* consts "named_sugar" :: " 'i_am \<Rightarrow> 'merely \<Rightarrow> 'a_sugar " ("\<ltbrak>_\<rtbrak>. _" [10,15] 14)
translations
  "\<ltbrak>name\<rtbrak>. x \<Ztypecolon> T" == "x \<Ztypecolon> (\<ltbrak>name\<rtbrak>. T)"
  "\<ltbrak>name\<rtbrak>. x" == "CONST Labelled (LABEL name) x" *)

lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..
lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..



subsubsection \<open>Hidden name hint\<close> (*depreciated*)

definition NameHint :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "NameHint name x = x" \<comment>\<open>name tag\<close>
translations "X" <= "CONST NameHint name X"



subsubsection \<open>Argument tag\<close>

definition Argument :: "'a \<Rightarrow> 'a" ("\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _" [11] 10) where "Argument x = x"

lemma Argument_I: "P \<Longrightarrow> Argument P" unfolding Argument_def .

text \<open>Sequent in pattern \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P \<Longrightarrow> PROP Q\<close> hints users to input a theorem \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> P\<close>
  in order to deduce the sequent into \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> PROP Q\<close>, which is processed by the `rule` processor.
  Argument servers as a protector to prevent the unexpected auto-reasoning, e.g., the case for cast where
  the reasoner always attempts to solve an unprotected case premises and `Argument` tagging the Subty premise
  in this case prevent this automatic behavior when expecting user to input the cast rule.\<close>



subsubsection \<open>Technical Tags\<close>

datatype uniq_id = UNIQ_ID
  \<comment> \<open>A technical tag that is during the exporting translated to a unique ID.
    It is useful to generate unique name of anonymous functions.\<close>




subsubsection \<open>Name tag by type\<close>

datatype ('x, 'name) named (infix "<named>" 30) = tag 'x

syntax "__named__" :: \<open>logic \<Rightarrow> tuple_args \<Rightarrow> logic\<close> (infix "<<named>>" 25)


ML_file \<open>library/name_by_type.ML\<close>

text (in \<phi>empty) \<open>It is a tool to annotate names on a term, e.g. \<^term>\<open>x <<named>> a, b\<close>.
  The name tag is useful in lambda abstraction (including quantification) because the
  name of an abstraction variable is not preserved in many transformation especially
  simplifications. The name can be useful in the deductive programming, e.g. universally
  quantified variables in a sub-procedure like
      \<forall>x y. proc f \<lbrace> VAL x \<Ztypecolon> T\<heavy_comma> VAL y \<Ztypecolon> U \<longmapsto> any \<rbrace> \<Longrightarrow> any'.
  When starting to write the sub-procedure f by command `\<medium_left_bracket>', \<phi>-system fixes variables x and y
    with the name of x and y. The name of x and y then are significant for programming.
  To preserve the name, we use \<^typ>\<open>'any <named> '\<phi>name_x \<times> '\<phi>name_y\<close>,
    \<^prop>\<open>\<forall>(x :: 'any <named> '\<phi>name_x). sth\<close>.
  We use free type variable to annotate it because it is most stable. No transformation
    changes the name of a free type variable.

  This feature is mostly used in Variable Extraction (see ???).\<close>


lemma named_forall: "All P \<longleftrightarrow> (\<forall>x. P (tag x))" by (metis named.exhaust)
lemma named_exists: "Ex P \<longleftrightarrow> (\<exists>x. P (tag x))" by (metis named.exhaust)
lemma [simp]: "tag (case x of tag x \<Rightarrow> x) = x" by (cases x) simp
lemma named_All: "(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (tag x))"
proof fix x assume "(\<And>x. PROP P x)" then show "PROP P (tag x)" .
next fix x :: "'a <named> 'b" assume "(\<And>x. PROP P (tag x))" from \<open>PROP P (tag (case x of tag x \<Rightarrow> x))\<close> show "PROP P x" by simp
qed

lemma named_ExSet: "(ExSet T) = (\<exists>*c. T (tag c) )" by (auto simp add: named_exists \<phi>expns)

subsubsection \<open>Rename \<lambda>-Abstraction\<close>

definition rename_abstraction :: \<open>'\<phi>name_name itself \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>rename_abstraction name origin_abs named_abs \<longleftrightarrow> (origin_abs = named_abs)\<close>

lemma rename_abstraction:
  \<open>rename_abstraction name X X\<close>
  unfolding rename_abstraction_def ..

\<phi>reasoner_ML rename_abstraction 1100 (conclusion "rename_abstraction TYPE(?'name) ?Y ?Y'") =
\<open>fn (ctxt, sequent) =>
  case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>rename_abstraction\<close>, _)
                $ (Const (\<^const_name>\<open>Pure.type\<close>, Type(\<^type_name>\<open>itself\<close>, [name'])))
                $ Abs(_,ty,body)
                $ Var Y'') =>
      let
        val name = case PhiSyntax.dest_name_tylabels name'
                     of [x] => x
                      | _ => raise TYPE ("only one name is expected", [name'], [])
        val Y' = Abs(name, ty, body) |> Thm.cterm_of ctxt
        val sequent = @{thm rename_abstraction} RS Thm.instantiate (TVars.empty, Vars.make [(Y'',Y')]) sequent
      in
        Seq.single (ctxt, sequent)
      end
     | term => raise THM ("Bad shape of rename_abstraction antecedent", 0, [sequent])
\<close>


subsubsection \<open>\<lambda>-Abstraction Tag\<close>

definition "lambda_abstraction" :: " 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool "
  where "lambda_abstraction x Y Y' \<longleftrightarrow> Y' x = Y"

lemma lambda_abstraction: "lambda_abstraction x (Y' x) Y'"
  unfolding lambda_abstraction_def ..

lemma [\<phi>reason 1200 on \<open>lambda_abstraction (?x,?y) ?fx ?f\<close>]:
  \<open> lambda_abstraction y fx f1
\<Longrightarrow> lambda_abstraction x f1 f2
\<Longrightarrow> lambda_abstraction (x,y) fx (case_prod f2)\<close>
  unfolding lambda_abstraction_def by simp

\<phi>reasoner_ML lambda_abstraction 1100 (conclusion "lambda_abstraction ?x ?Y ?Y'") = \<open>fn (ctxt, sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>lambda_abstraction\<close>, _) $ x $ Y $ _)
      = Thm.major_prem_of sequent
    val Y' = Abs("", fastype_of x, abstract_over (x, Y))
    val rule = Drule.infer_instantiate ctxt
          (map (apsnd (Thm.cterm_of ctxt)) [(("x",0),x), (("Y'",0),Y')]) @{thm lambda_abstraction}
  in
    Seq.single (ctxt, rule RS sequent)
  end
\<close>

lemma [\<phi>reason 1200 on \<open>lambda_abstraction (tag ?x) ?fx ?f\<close>]:
  \<open> lambda_abstraction x fx f
\<Longrightarrow> rename_abstraction TYPE('name) f f'
\<Longrightarrow> lambda_abstraction (tag x :: 'any <named> 'name) fx (case_named f')\<close>
  unfolding lambda_abstraction_def rename_abstraction_def by simp


subsubsection \<open>Extract Proof Obligation\<close>

lemma contract_obligations:
  "(Premise mode P \<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n Q \<Longrightarrow> PROP C) \<equiv> (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n P \<and> Q \<Longrightarrow> PROP C)"
  unfolding Premise_def atomize_imp conj_imp .

ML_file "library/reasoners.ML"

\<phi>reasoner_ML Normal_Premise 10 (conclusion \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ?P\<close> | conclusion \<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n ?P\<close>)
  = \<open>Nu_Reasoners.wrap Nu_Reasoners.premise_tac\<close>
\<phi>reasoner  Simp_Premise 10 (conclusion \<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m ?P\<close>)
  = (rule Premise_I; simp; fail)
\<phi>reasoner \<phi>expn_Premise 10 (conclusion \<open><\<phi>expn> ?P\<close>)
  = (rule Premise_I; simp add: \<phi>expns)



section \<open>More Features of the Deductive Programming\<close>

subsection \<open>Preliminary\<close>

subsubsection \<open>Syntax\<close>

ML_file PhiSyntax.ML
ML_file NuBasics.ML

consts val_of :: " 'a \<Rightarrow> 'b "
consts key_of :: " 'a \<Rightarrow> 'b "

datatype ('a, 'b) object (infixr "\<Zinj>" 60) = object (key_of_obj: 'a) (val_of_obj: 'b) (infixr "\<Zinj>" 60)
adhoc_overloading key_of key_of_obj and val_of val_of_obj
declare object.split[split]


lemma object_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<Zinj> x))" by (metis object.exhaust)
lemma object_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<Zinj> x))" by (metis object.exhaust)
lemma object_All[lrep_exps]: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a \<Zinj> b))" 
proof fix a b assume "(\<And>x. PROP P x) " then show "PROP P (a \<Zinj> b)" .
next fix x assume "\<And>a b. PROP P (a \<Zinj> b)"
    from \<open>PROP P (key_of x \<Zinj> val_of x)\<close> show "PROP P x" by simp
  qed



subsubsection \<open>Reasoning Rules & Settings\<close>

declare set_mult_inhabited[\<phi>reason_elim!]
  Premise_def[\<phi>def, \<phi>expns]

lemma (in \<phi>empty) [\<phi>reason]:
  \<open> (\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY)
\<Longrightarrow> \<phi>\<phi>SemType T TY\<close>
  ..

lemma (in \<phi>empty) [\<phi>reason_elim!, elim!]:
  \<open>Inhabited Void \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsubsection \<open>Finalization Rewrites\<close>

consts procedure_simplification :: mode
named_theorems procedure_simps

declare proc_bind_SKIP[procedure_simps]
  proc_bind_SKIP'[procedure_simps]
  proc_bind_assoc[procedure_simps]

\<phi>reasoner procedure_equivalent 1200 (conclusion \<open>Premise procedure_simplification ?P\<close>)
  = (rule Premise_I; simp only: procedure_simps; fail)

\<phi>reasoner procedure_simplification 1200
    (conclusion \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[procedure_simplification] ?Q = ?P\<close>)
  = ((simp only: procedure_simps)?, rule Conv_I; fail)

lemma (in \<phi>empty) "\<phi>__final_proc_rewrite__":
  \<open> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[procedure_simplification] f = f'
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f  \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>\<close>
  unfolding Conv_def by simp

lemma (in \<phi>empty) "\<phi>__final_proc_rewrite__'":
  \<open> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[procedure_simplification] f = f'
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f  \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Conv_def by simp

subsubsection \<open>Misc\<close>

lemma (in \<phi>empty) "\<phi>__Return_rule__":
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_::unit sem_value. Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def Return_def View_Shift_def subset_iff det_lift_def
  by clarsimp


subsection \<open>Ad-hoc Overload\<close>

ML_file \<open>library/applicant.ML\<close>

attribute_setup \<phi>overload = \<open>Scan.lift (Parse.and_list1 NuApplicant.name_position) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuApplicant.overload th) bindings))\<close>

\<phi>overloads D \<open>Destructive subtyping rules\<close>
\<phi>overloads cast \<open>Invoke subtyping on the internal content\<close>



subsection \<open>Subtype\<close>

lemma subty_0[\<phi>reason 2000 on \<open>0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X\<close>
  unfolding Imply_def zero_set_def by simp

lemma cast_id[\<phi>reason 2000 on \<open>?A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?B \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A" unfolding Imply_def by fast

lemma cast_id_ty[\<phi>reason 30 on \<open>?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?T \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> T" unfolding Imply_def by fast

lemma subty_union[\<phi>reason 800]:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X + Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X + Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by simp_all

(* abbreviation SimpleSubty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _)" [2,14] 13)
  where "(A \<longmapsto> B) \<equiv> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d True)" *)
(* lemma SubtyE[elim]: "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Imply_def Inhabited_def by (auto intro: Inhabited_subset)
lemma SubtyI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P" unfolding Imply_def Inhabited_def by auto *)

lemma \<phi>cast_trans:
  "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
    \<Longrightarrow> (P \<Longrightarrow> B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s C \<^bold>a\<^bold>n\<^bold>d Q)
    \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s C \<^bold>a\<^bold>n\<^bold>d P \<and> Q"
  unfolding Imply_def by auto


lemma \<phi>cast_intro_frame:
  "U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> R * U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * U \<^bold>a\<^bold>n\<^bold>d P "
  unfolding Imply_def pair_forall times_set_def by blast

lemma \<phi>cast_intro_frame_R:
  "U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> U' * R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U * R \<^bold>a\<^bold>n\<^bold>d P "
  unfolding Imply_def pair_forall times_set_def by blast

lemma cast_whole_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Argument_def .


subsection \<open>View Shift\<close>

context \<phi>empty begin

lemma View_Shift_by_Subtyp[intro?]:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Imply_def View_Shift_def INTERP_COM_def
  by (clarsimp, metis set_mult_expn)

lemma view_shift_0[\<phi>reason 2000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> X\<close>
  by (blast intro: View_Shift_by_Subtyp subty_0)
  
lemma view_shift_id[\<phi>reason 2000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<longmapsto> ?B \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> A"
  by (blast intro: View_Shift_by_Subtyp cast_id)

lemma view_shift_id_ty[\<phi>reason 30 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?x \<Ztypecolon> ?T \<longmapsto> ?y \<Ztypecolon> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> T \<longmapsto> y \<Ztypecolon> T"
  by (blast intro: View_Shift_by_Subtyp cast_id_ty)

lemma view_shift_union[\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X + Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X + Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  by (simp add: View_Shift_def distrib_left)+

(* abbreviation SimpleSubty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _)" [2,14] 13)
  where "(A \<longmapsto> B) \<equiv> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d True)" *)
(* lemma SubtyE[elim]: "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Imply_def Inhabited_def by (auto intro: Inhabited_subset)
lemma SubtyI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P" unfolding Imply_def Inhabited_def by auto *)

lemma is_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> x' \<Ztypecolon> N" using view_shift_id by force
lemma as_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> X' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> X'"  by blast 

lemma \<phi>view_shift_trans:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> (P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q)
    \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding View_Shift_def by blast


lemma \<phi>view_shift_intro_frame:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R * U' \<longmapsto> R * U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  by (simp add: \<phi>frame_view)

lemma \<phi>view_shift_intro_frame_R:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w U' * R \<longmapsto> U * R \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  by (simp add: \<phi>frame_view mult.commute)

lemma (in \<phi>empty) "\<phi>view_shift":
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T'"
  unfolding CurrentConstruction_def View_Shift_def
  by blast

lemma (in \<phi>empty) "\<phi>view_shift_P":
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T') \<and> P"
  unfolding CurrentConstruction_def View_Shift_def
  by blast

lemma view_shift_whole_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Argument_def .


lemma \<phi>CONSEQ'E:
   "\<^bold>v\<^bold>i\<^bold>e\<^bold>w E \<longmapsto> E' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P3
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A  \<longmapsto> B  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>"
  using \<phi>CONSEQ view_shift_id by blast

end


subsection \<open>Antecedents of Reasoning - Part II\<close>

subsubsection \<open>Introduce Frame Variable\<close>

named_theorems frame_var_rewrs \<open>Rewriting rules to normalize after inserting the frame variable\<close>

declare mult.assoc[symmetric, frame_var_rewrs]
  Subjection_times[frame_var_rewrs]
  ExSet_times[frame_var_rewrs]

consts frame_var_rewrs :: mode

\<phi>reasoner Subty_Simplify 2000 (conclusion \<open>Simplify frame_var_rewrs ?x ?y\<close>)
  = ((simp only: frame_var_rewrs)?, rule Simplify_I)


context \<phi>empty begin

definition \<phi>IntroFrameVar ::
  "('FIC_N,'FIC) assn
\<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn
\<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn
\<Rightarrow> bool"
  where "\<phi>IntroFrameVar R S' S T' T \<longleftrightarrow> S' = (R * S) \<and> T' = R * T "

definition \<phi>IntroFrameVar' ::
  "('FIC_N,'FIC) assn
\<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn
\<Rightarrow> ('ret \<Rightarrow> ('FIC_N,'FIC) assn) \<Rightarrow> ('ret \<Rightarrow> ('FIC_N,'FIC) assn)
\<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn
\<Rightarrow> bool"
  where "\<phi>IntroFrameVar' R S' S T' T E' E \<longleftrightarrow> S' = (R * S) \<and> T' = (\<lambda>ret. R * T ret) \<and> E' = (R * E) "


lemma \<phi>IntroFrameVar_No:
  "\<phi>IntroFrameVar Void S S T T"
  unfolding \<phi>IntroFrameVar_def by simp

lemma \<phi>IntroFrameVar'_No:
  "\<phi>IntroFrameVar' Void S S T T E E"
  unfolding \<phi>IntroFrameVar'_def by simp

lemma \<phi>IntroFrameVar_Yes:
  " Simplify frame_var_rewrs S' (R * S)
\<Longrightarrow> Simplify frame_var_rewrs T' (R * T)
\<Longrightarrow> \<phi>IntroFrameVar R S' S T' T"
  unfolding \<phi>IntroFrameVar_def by blast

lemma \<phi>IntroFrameVar'_Yes:
  " Simplify frame_var_rewrs S' (R * S)
\<Longrightarrow> Simplify frame_var_rewrs T' (\<lambda>ret. R * T ret)
\<Longrightarrow> Simplify frame_var_rewrs E' (R * E)
\<Longrightarrow> \<phi>IntroFrameVar' R S' S T' T E' E"
  unfolding \<phi>IntroFrameVar'_def by blast


\<phi>reasoner_ML \<phi>IntroFrameVar 1000 (conclusion "\<phi>IntroFrameVar ?R ?S' ?S ?T' ?T") =
\<open>fn (ctxt, sequent) =>
  let
    val (Const (\<^const_name>\<open>\<phi>empty.\<phi>IntroFrameVar\<close>, _) $ _ $ _ $ S $ _ $ _) =
        Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val tail = PhiSyntax.strip_separations S |> NuHelp.last
  in
    if is_Var tail andalso fastype_of tail = PhiSyntax.get_assn_typ ctxt
    then Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar_No"  RS sequent)
    else Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar_Yes" RS sequent)
  end\<close>

\<phi>reasoner_ML \<phi>IntroFrameVar' 1000 (conclusion "\<phi>IntroFrameVar' ?R ?S' ?S ?T' ?T ?E' ?E") =
\<open>fn (ctxt, sequent) =>
  let
    val (Const (\<^const_name>\<open>\<phi>empty.\<phi>IntroFrameVar'\<close>, _) $ _ $ _ $ S $ _ $ _ $ _ $ _) =
        Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val tail = PhiSyntax.strip_separations S |> NuHelp.last
  in
    if is_Var tail andalso fastype_of tail = PhiSyntax.get_assn_typ ctxt
    then Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar'_No" RS sequent)
    else Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar'_Yes" RS sequent)
  end\<close>


end


subsubsection \<open>Fix\<close>

definition Fix :: \<open>'a set \<Rightarrow> 'a set\<close> ("FIX _" [16] 15) where [iff]: \<open>Fix S = S\<close>

text (in \<phi>empty) \<open>During the subtyping reasoning, \<^term>\<open>FIX OBJ S\<close> annotates the reasoner
  do not attempt to permute objects to solve the subtyping. It means the order is sensitive
  and fixed. For example, a cast may apply only on the first object,
  after user rotates the target to the first.\<close>

lemma [\<phi>reason 2000]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s FIX Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Fix_def .

lemma (in \<phi>empty) [\<phi>reason 2000]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> FIX Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Fix_def .

(* lemma (in \<phi>empty) cast_obj_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t Y \<longmapsto> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e (FIX OBJ Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ Y' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Imply_def Argument_def Fix_def
  by (simp_all add: \<phi>expns, blast) *)



subsubsection \<open>Matches\<close>

text \<open>The tag restricts in sub-type reasoning the original type must match certain pattern.\<close>

definition TyMatches :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixl "<matches>" 18)
  where \<open>(S <matches> pattern) = S\<close>

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (Y <matches> A) \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding TyMatches_def .

lemma (in \<phi>empty) [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> (Y <matches> A) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding TyMatches_def .


subsubsection \<open>Expansion of Quantification\<close>

ML_file "./library/QuantExpansion.ML"

named_theorems named_expansion \<open>Rewriting rules expanding named quantification.\<close>



(*
subsubsection \<open>Constrain at Most One Solution when Reasoning A Proposition\<close>

definition Unique_Solution :: \<open>bool \<Rightarrow> bool\<close>
  where [iff]: \<open>Unique_Solution P \<longleftrightarrow> P\<close>

definition Meet_A_Solution :: bool
  where [iff]: \<open>Meet_A_Solution \<longleftrightarrow> True\<close>

lemma start_unique_solution_reasoning:
  \<open> P
\<Longrightarrow> Meet_A_Solution
\<Longrightarrow> Unique_Solution P\<close>
  unfolding Unique_Solution_def . *)



subsection \<open>Synthesis\<close>

text \<open>The section presents a generic synthesis framework.
  It is called generic because it supports different semantics of synthesis on different kinds of
    sequent. For example, on Programming_CurrentConstruction, the behavior is to reason
    a procedure to generate an output satisfying the desired specification;
    on View_Shift_CurrentConstruction, it is to reason a view shift;
    on a form of \<open>P \<Longrightarrow> Q\<close>, it is to reason a proposition P according to the given term.\<close>

definition DoSynthesis :: \<open>'a \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>DoSynthesis term sequent result \<equiv> (PROP sequent \<Longrightarrow> PROP result)\<close>

definition Synthesis_Parse :: \<open>'a \<Rightarrow> 'b \<Rightarrow> prop\<close>
  where \<open>Synthesis_Parse input parsed \<equiv> Trueprop True\<close>

lemma \<phi>synthesis:
  \<open> PROP sequent
\<Longrightarrow> PROP DoSynthesis X sequent result
\<Longrightarrow> PROP result\<close>
  unfolding DoSynthesis_def .

text \<open>
  Overall, the synthesis procedure consists of 2 phases. The first phase as a pre-processor,
    parses the input from user and then the second phase triggers the reasoning process
    on the parsed input.

  The reason why we parse the input is because, inputting always complete assertions
    can be verbose.
  For example, user may input just an abstract object \<^term>\<open>x\<close> to mean to
    synthesis \<^term>\<open>x \<Ztypecolon> T\<close> for some unspecified \<^term>\<open>T\<close>;
    user may also input \<^term>\<open>0::nat\<close> to mean to synthesis \<^term>\<open>0 \<Ztypecolon> Natural_Number\<close>.

  Antecedent \<^schematic_term>\<open>Synthesis_Parse input ?parsed\<close> provides this function to parse the user
    input \<^term>\<open>input\<close> before the synthesis. Configured by several rules, the reasoner instantiates
    \<^schematic_term>\<open>?parsed\<close> and solves this antecedent.

  By disabling \<phi>_synthesis_parsing to disable this feature.\<close>


subsubsection \<open>Parse the Term to be Synthesised\<close>

context \<phi>empty begin

lemma [\<phi>reason 9999 on
  \<open>PROP Synthesis_Parse (?X'::?'ret \<Rightarrow> ('FIC_N,'FIC)assn) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse X X\<close> for X :: \<open>'ret \<Rightarrow> ('FIC_N,'FIC)assn\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 9999 on
  \<open>PROP Synthesis_Parse (?X'::('FIC_N,'FIC)assn) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse X (\<lambda>_. X)\<close> for X :: \<open>('FIC_N,'FIC)assn\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 30 
    on \<open>PROP Synthesis_Parse ?x (?Y::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
    if no \<open>PROP Synthesis_Parse (?x \<Ztypecolon> ?T) ?Y\<close>
          \<open>PROP Synthesis_Parse (?x::('FIC_N,'FIC) assn) ?Y\<close>
          \<open>PROP Synthesis_Parse (?x::?'ret \<Rightarrow> ('FIC_N,'FIC) assn) ?Y\<close>
]:
  \<open>PROP Synthesis_Parse x (\<lambda>ret. (x \<Ztypecolon> X ret :: ('FIC_N,'FIC)assn))\<close>
  unfolding Synthesis_Parse_def ..


lemma (in \<phi>empty) [\<phi>reason 10
    on \<open>PROP Synthesis_Parse (numeral ?n::?'bb::numeral) ?X\<close>
       \<open>PROP Synthesis_Parse (0::?'cc::zero) ?X\<close>
       \<open>PROP Synthesis_Parse (1::?'dd::one) ?X\<close>
 if no \<open>PROP Synthesis_Parse (?n::nat) ?X\<close>
]:
  \<open> PROP Synthesis_Parse (n :: nat) X
\<Longrightarrow> PROP Synthesis_Parse n X\<close>
 \<comment> \<open>This rule specifies: when input any 0, 1, or \<^schematic_term>\<open>numeral ?sth\<close>, of unspecified type,
      they should be treated as of natural number type.\<close>
  unfolding Synthesis_Parse_def
  ..

end


subsubsection \<open>Tagging the part a construction can synthesis\<close>

definition Synthesis :: \<open>'a set \<Rightarrow> 'a set\<close> ("SYNTHESIS _" [15] 14) where [iff]: \<open>Synthesis S = S\<close>

text (in \<phi>empty) \<open>
  Occurring in a rule, SYNTHESIS tags a part of the post \<phi>-type of a triple or a view shifting,
    representing this part can be synthesised by this construction.
  For example, \<^prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> SYNTHESIS Z \<rbrace>\<close> represents the procedure f generates
    something that meets Z.

  Occurring during reasoning, like \<^schematic_prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> SYNTHESIS Z \<rbrace> \<Longrightarrow> C\<close>,
    it represents the reasoner needs to find some construction (here it specifies it must be a
    procedure) ?f that generates something meeting Z.
\<close>

subsubsection \<open>Synthesis Operations\<close>

paragraph \<open>Construction on Programming\<close>

lemma (in \<phi>empty) [\<phi>reason 1200
  on \<open>PROP DoSynthesis ?X (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S1)) ?RET\<close>
]:
  " PROP Synthesis_Parse X X'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S1 \<longmapsto> \<lambda>v. S2\<heavy_comma> SYNTHESIS X' v \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S1))
      (Trueprop (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>v. S2\<heavy_comma> X' v) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))"
  unfolding Synthesis_def GOAL_CTXT_def DoSynthesis_def
  using \<phi>apply_proc .

text \<open>On programming mode, the synthesis operation always tries to find a procedure.
  View shifts have to be wrapped in a procedure. (TODO: an automatic wrapper)\<close>

paragraph \<open>Construction on View Shifting\<close>

lemma (in \<phi>empty) [\<phi>reason 1200
  on \<open>PROP DoSynthesis ?X (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?blk [?H] \<^bold>i\<^bold>s ?S1)) ?RET\<close>
]:
  " PROP Synthesis_Parse X X'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> SYNTHESIS X' \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w blk [H] \<^bold>i\<^bold>s S1))
      (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w blk [H] \<^bold>i\<^bold>s S2\<heavy_comma> X'))"
  unfolding Synthesis_def GOAL_CTXT_def DoSynthesis_def
  using \<phi>apply_view_shift .

text \<open>On view shifting mode, the synthesis operation tries to find a view shifting.\<close>

paragraph \<open>Solving an antecedent by Synthesis\<close>

definition Synthesis_by :: \<open>'a \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Synthesis_by X Q = Q\<close>

text \<open>User should configure how to in detail solve an antecedent \<^prop>\<open>P\<close> by a
  given input \<^term>\<open>X\<close>, by giving rules like \<^prop>\<open>Synthesis_by X P\<close>.\<close>

definition Synthesis_by_internal :: \<open>'a \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>Synthesis_by_internal X Q \<equiv> Q\<close>

lemma [\<phi>reason 1200
  on \<open>PROP DoSynthesis ?X (PROP ?P \<Longrightarrow> PROP ?Q) ?RET\<close>
]:
  " PROP Synthesis_by_internal X (PROP P)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X (PROP P \<Longrightarrow> PROP Q) (PROP Q)"
  unfolding DoSynthesis_def Synthesis_by_internal_def .

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. PROP Synthesis_by_internal X (PROP P x))
\<Longrightarrow> PROP Synthesis_by_internal X (\<And>x. PROP P x)\<close>
  unfolding Synthesis_by_internal_def .

lemma [\<phi>reason 1200]:
  \<open>(PROP P \<Longrightarrow> PROP Synthesis_by_internal X (PROP Q))
\<Longrightarrow> PROP Synthesis_by_internal X (PROP P \<Longrightarrow> PROP Q)\<close>
  unfolding Synthesis_by_internal_def .

lemma [\<phi>reason 1200]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> Synthesis_by X P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> PROP Synthesis_by_internal X (Trueprop P)\<close>
  unfolding Synthesis_by_internal_def Synthesis_by_def GOAL_CTXT_def .

lemma (in \<phi>empty) [\<phi>reason 1400]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Synthesis_by X (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def .

lemma (in \<phi>empty) [\<phi>reason 1200]:
  \<open> PROP Synthesis_Parse X X'
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X' ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Synthesis_by X (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> X' ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def Synthesis_def .

lemma (in \<phi>empty) [\<phi>reason 1200]:
  \<open> (\<And>x. Synthesis_by X (P x) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G)
\<Longrightarrow> Synthesis_by X (All P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def GOAL_CTXT_def ..

lemma (in \<phi>empty) [\<phi>reason 1200]:
  \<open> (P \<Longrightarrow> Synthesis_by X Q \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G)
\<Longrightarrow> Synthesis_by X (P \<longrightarrow> Q) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def GOAL_CTXT_def ..


subsubsection \<open>General Synthesis Rules\<close>

lemma (in \<phi>empty) [\<phi>reason 1200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS f x \<Ztypecolon> T ret \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS (case_named f (tag x)) \<Ztypecolon> T ret \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P\<close>
  by simp


subsection \<open>Application\<close> \<comment> \<open>of procedures, subtypings, and any other things\<close>

definition \<phi>Application :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close> ("_/ \<^bold>a\<^bold>p\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _/ \<^bold>\<Rightarrow> _")
  where \<open>\<phi>Application Applicants State Result \<equiv> (PROP State \<Longrightarrow> PROP Applicants \<Longrightarrow> PROP Result)\<close>

definition \<phi>Application_Method :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application_Method \<equiv> \<phi>Application\<close>

definition \<phi>Application_Success :: "prop"
  where \<open>\<phi>Application_Success \<equiv> Trueprop True\<close>

(* lemma \<phi>Application_Method_cong[cong]:
  \<open> App1 \<equiv> App2 \<Longrightarrow> Stat1 \<equiv> Stat2 \<Longrightarrow> Res1 \<equiv> Res2
\<Longrightarrow> \<phi>Application_Method App1 Stat1 Res1 \<equiv> \<phi>Application_Method App2 Stat2 Res2\<close>
  unfolding \<phi>Application_Method *)


lemma \<phi>Application_normalize:
  \<open>(P \<Longrightarrow> ((PROP Apps) \<^bold>a\<^bold>p\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (PROP State) \<^bold>\<Rightarrow> (PROP Result)))
 \<equiv> ((PROP Apps) \<^bold>a\<^bold>p\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (PROP State) \<^bold>\<Rightarrow> (P \<Longrightarrow> PROP Result))\<close>
  unfolding \<phi>Application_def ..

lemma \<phi>application_start_reasoning:
  \<open> PROP \<phi>Application_Method (PROP Apps) (PROP State) (PROP Result)
\<Longrightarrow> ((PROP Apps) \<^bold>a\<^bold>p\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (PROP State) \<^bold>\<Rightarrow> (PROP Result))\<close>
  unfolding \<phi>Application_def \<phi>Application_Method_def .

lemma \<phi>application:
  \<open>PROP Apps \<Longrightarrow> (PROP State) \<Longrightarrow> ((PROP Apps) \<^bold>a\<^bold>p\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (PROP State) \<^bold>\<Rightarrow> (PROP Result)) \<Longrightarrow> PROP Pure.prop Result\<close>
  unfolding \<phi>Application_def Pure.prop_def .

lemma \<phi>application_success:
  \<open>PROP \<phi>Application_Success\<close>
  unfolding \<phi>Application_Success_def ..


definition \<phi>Application_Conv :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application_Conv P Q \<equiv> (PROP P \<Longrightarrow> PROP Q)\<close>

lemma \<phi>Application_Conv:
  \<open> PROP P
\<Longrightarrow> PROP \<phi>Application_Conv P Q
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP Q\<close>
  unfolding \<phi>Application_Conv_def .


ML_file \<open>library/application.ML\<close>

\<phi>reasoner_ML \<phi>Application 2000 (conclusion \<open>(PROP ?App) \<^bold>a\<^bold>p\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?State \<^bold>\<Rightarrow> (PROP ?Result)\<close>) =
  \<open>NuApply.start_reasoning\<close>

\<phi>reasoner_ML \<phi>Application_Success 2000 (conclusion \<open>PROP \<phi>Application_Success\<close>) =
  \<open>NuApply.success_application\<close>


subsubsection \<open>Rules of Application Methods\<close>

paragraph \<open>Common Rules\<close>

lemma [\<phi>reason on \<open>
  PROP \<phi>Application_Method (PROP ?App &&& PROP ?Apps) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (PROP App &&& PROP Apps) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def conjunction_imp .

lemma [\<phi>reason on \<open>
  PROP \<phi>Application_Method (PROP ?App &&& PROP ?Apps) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP Apps) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (PROP App &&& PROP Apps) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def conjunction_imp .

lemma [\<phi>reason 1100 on \<open>
  PROP \<phi>Application_Method (PROP ?Prem \<Longrightarrow> PROP ?App) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (PROP Prem \<Longrightarrow> PROP App) State (PROP Prem \<Longrightarrow> PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def imp_implication
  subgoal premises prems using prems(1)[OF  prems(2) prems(3)[OF prems(4)]] . .

lemma [\<phi>reason 1100 on \<open>
  PROP \<phi>Application_Method (Trueprop (?Prem \<longrightarrow> ?App)) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (Prem \<longrightarrow> App)) State (Prem \<Longrightarrow> PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def imp_implication
  subgoal premises prems using prems(1)[OF prems(2) prems(3)[OF prems(4)]] . .


lemma [\<phi>reason 1200 on \<open>
  PROP \<phi>Application_Method (Pure.all ?App) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP (App x)) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (Pure.all App) State (PROP Result)\<close>
  unfolding \<phi>Application_def \<phi>Application_Method_def
  subgoal premises prems
    apply (tactic \<open>Tactic.resolve_tac \<^context>
      [((Thm.forall_elim \<^cterm>\<open>x\<close> @{thm prems(3)}) RS @{thm prems(1)[OF prems(2)]})] 1\<close>) . .


lemma [\<phi>reason 1200 on \<open>
  PROP \<phi>Application_Method (Trueprop (All ?App)) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop (App x)) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (All App)) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def imp_implication
  subgoal premises prems using prems(1)[OF prems(2) prems(3)[THEN spec[where x=x]]] . .


lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Method (Trueprop App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (App \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def GOAL_CTXT_def
  subgoal premises prems using prems(1)[OF prems(2) prems(3)] . .


lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv X' X
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method X' (PROP X \<Longrightarrow> PROP Y) Y\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def \<phi>Application_Conv_def
  subgoal premises prems using prems(3)[OF prems(1)[OF prems(4)]] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (Trueprop X') (Trueprop X)
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop X') (Trueprop (X \<longrightarrow> Y)) (Trueprop Y)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def \<phi>Application_Conv_def by blast

lemma [\<phi>reason 2000]:
  \<open>PROP \<phi>Application_Conv (PROP X) (PROP X)\<close>
  unfolding \<phi>Application_Conv_def .

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. PROP \<phi>Application_Conv (Trueprop (X' x)) (Trueprop (X x)))
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (All X')) (Trueprop (All X))\<close>
  unfolding \<phi>Application_Conv_def by blast

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (Trueprop X)  (Trueprop X')
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop Y') (Trueprop Y)
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (X' \<longrightarrow> Y')) (Trueprop (X \<longrightarrow> Y))\<close>
  unfolding \<phi>Application_Conv_def by blast

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. PROP \<phi>Application_Conv (X' x) (X x))
\<Longrightarrow> PROP \<phi>Application_Conv (\<And>x. PROP X' x) (\<And>x. PROP X x)\<close>
  unfolding \<phi>Application_Conv_def
proof -
  assume A: \<open>(\<And>x. PROP X' x \<Longrightarrow> PROP X x)\<close>
    and  B: \<open>\<And>x. PROP X' x\<close>
  show \<open>\<And>x. PROP X x\<close> proof -
    fix x show \<open>PROP X x\<close> using B[where x=x, THEN A] .
  qed
qed

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (PROP X)  (PROP X')
\<Longrightarrow> PROP \<phi>Application_Conv (PROP Y') (PROP Y)
\<Longrightarrow> PROP \<phi>Application_Conv (PROP X' \<Longrightarrow> PROP Y') (PROP X \<Longrightarrow> PROP Y)\<close>
  unfolding \<phi>Application_Conv_def
  subgoal premises prems using prems(4)[THEN prems(1), THEN prems(3), THEN prems(2)] . .


paragraph \<open>Applying on Current Construction\<close>

context \<phi>empty begin

subparagraph \<open>Subtyping methods\<close>

lemma [\<phi>reason 3000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?x' \<Ztypecolon> ?X')) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Void\<heavy_comma> x' \<Ztypecolon> X'))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T') \<and> P'))
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n x' \<Ztypecolon> X'))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T') \<and> P'))\<close>
  by simp

lemma \<phi>apply_subtyping_fast[\<phi>reason 1800 on \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" .

lemma [\<phi>reason 1500 on \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" \<phi>cast_intro_frame by blast

lemma \<phi>apply_subtyping_fully[\<phi>reason on \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T' \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any)
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def
    GOAL_CTXT_def FOCUS_TAG_def View_Shift_Reasoning_def
  by (meson \<phi>cast_P \<phi>cast_intro_frame \<phi>view_shift_P)
  


subparagraph \<open>View Shift methods\<close>

lemma [\<phi>reason 3000 on \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?x \<Ztypecolon> ?X \<longmapsto> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?x' \<Ztypecolon> ?X')) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> X \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Void\<heavy_comma> x' \<Ztypecolon> X'))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T') \<and> P'))
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> X \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n x' \<Ztypecolon> X'))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T') \<and> P'))\<close>
  by simp

lemma \<phi>apply_view_shift_fast[\<phi>reason 1800 on \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S \<longmapsto> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>view_shift_P" .

lemma [\<phi>reason 1500 on \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S \<longmapsto> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>view_shift_P" \<phi>view_shift_intro_frame by blast

lemma \<phi>apply_view_shift_fully[\<phi>reason on \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any)
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S' \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def
    GOAL_CTXT_def FOCUS_TAG_def View_Shift_Reasoning_def
  using "\<phi>view_shift_P" \<phi>view_shift_intro_frame
  by (metis (no_types, lifting))



(*
lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n VAL ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n VAL S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n VAL T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" cast_val_\<phi>app[unfolded Argument_def] by blast

lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n VAL ?S)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n VAL S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n VAL T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" cast_val_\<phi>app[unfolded Argument_def] by blast


lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> VAL ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> VAL S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> VAL T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" cast_val_\<phi>app[unfolded Argument_def] \<phi>cast_intro_frame by blast

lemma [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> VAL ?S)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> VAL S))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> VAL T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" cast_val_\<phi>app[unfolded Argument_def] \<phi>cast_intro_frame by metis
*)

subparagraph \<open>Procedure methods\<close>

lemma apply_proc_fast[\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S \<longmapsto> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
      (Trueprop (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using \<phi>apply_proc .


lemma \<phi>apply_proc_fully[\<phi>reason on
    \<open>PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S' \<longmapsto> ?T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>))
            (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result\<close>
]:
  \<open> \<phi>IntroFrameVar' R S'' S' T T' E'' E'
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)
\<Longrightarrow> PROP Filter_Out_Values E'' E
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S' \<longmapsto> T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>))
    (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
    (Trueprop (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def \<phi>IntroFrameVar'_def
    GOAL_CTXT_def FOCUS_TAG_def Simplify_def View_Shift_Reasoning_def
    Filter_Out_Values_def
  subgoal premises prems
    apply (simp only: prems(1))
    using \<phi>apply_proc[OF \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _\<close>,
          OF \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c _ \<lbrace> _ \<longmapsto> _ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _ \<rbrace>\<close>[THEN \<phi>frame[where R=R],
              THEN \<phi>CONSEQ[rotated 1, OF \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>,
                OF view_shift_id, OF View_Shift_by_Subtyp[OF \<open>E'' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s E\<close>],
                simplified prems(1)]]] . .
end


paragraph \<open>Applying on a Block / End a Block\<close>

definition \<open>Exhaustive_Abstract f f' \<longleftrightarrow> (f = f')\<close>

lemma Exhaustive_Abstract_I:
  \<open> Premise procedure_simplification (f = f')
\<Longrightarrow> Exhaustive_Abstract f f'\<close>
  unfolding Exhaustive_Abstract_def Premise_def by simp

\<phi>reasoner_ML Exhaustive_Abstract 1200 (conclusion \<open>Exhaustive_Abstract ?f ?f'\<close>) = \<open>
let
fun abstract_bound_over (j, body) =
  let
    fun abs i lev tm =
      if Bound i aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (i+1) (lev + 1) t)
        | t $ u =>
            (abs i lev t $ (abs i lev u handle Same.SAME => u)
              handle Same.SAME => t $ abs i lev u)
        | _ => raise Same.SAME)
  in abs j 0 body handle Same.SAME => body end

fun my_abstract_over _ (v as Free (name,ty)) body =
      Abs (name, ty, abstract_over (v,body))
  | my_abstract_over btys (Bound i) body =
      Abs ("", nth btys i, abstract_bound_over (i,body))
  | my_abstract_over _ v body =
      Abs ("", fastype_of v, abstract_over (v,body))

fun strip btys (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, ty, x)) = strip (ty::btys) x
  | strip btys (\<^const>\<open>Pure.imp\<close> $ _ $ x) = strip btys x
  | strip btys (\<^const>\<open>Trueprop\<close> $ x) = (btys, x)
  | strip _ x = raise TERM ("Exhaustive_Abstract/strip", [x])

in
  fn (ctxt,sequent) =>
    let
      val (btys, Const (\<^const_name>\<open>Exhaustive_Abstract\<close>, _) $ f $ f')
        = strip [] (hd (Thm.prems_of sequent))
    in (case Term.strip_comb (Envir.beta_eta_contract f') of (Var v, args) =>
         Thm.instantiate (TVars.empty, Vars.make [
              (v, Thm.cterm_of ctxt (fold_rev (my_abstract_over btys) args f))]) sequent
        | _ => sequent)
       |> (fn seq => Seq.single (ctxt, @{thm Exhaustive_Abstract_I} RS seq))
    end
end
\<close>

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>
  PROP \<phi>Application_Conv (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X \<longmapsto> ?Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>)) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f' \<lbrace> ?X' \<longmapsto> ?Y' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E' \<rbrace>))
\<close>]:
  \<open> Exhaustive_Abstract f f'
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1)
\<Longrightarrow> (\<And>ret. PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w Y ret \<longmapsto> Y' ret \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2))
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w E  \<longmapsto> E' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any3)
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> X' \<longmapsto> Y' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>))\<close>
  unfolding \<phi>Application_Conv_def Exhaustive_Abstract_def GOAL_CTXT_def FOCUS_TAG_def
    View_Shift_Reasoning_def
  using \<phi>CONSEQ by blast


subsection \<open>Action\<close>

text \<open>Action is a kind of meta calling mechanism.
  When user inputs some action name to call, initially the system does not know what
    the user intends to do, to construct a procedure or to cast by a view shift or to
      synthesis something or even to call a combination of these features.
  The construction going to happen on the sequent is decided by reasoning.
  The action name is encoded into an antecedent, and then the reasoner starts to
    try to solve the antecedent, causing the system starts to construct the sequent
    according to the given action name and configured reasoning rules relating to
    this action name.\<close>

typedecl action

text \<open>The action name is encoded to be a fixed free variable or a constant of \<^typ>\<open>action\<close>.
  Therefore the pattern matching can be native and fast.
  Note an action can be parameterized like, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> action\<close> parameterized
    by a nat and a boolean. Other parameters can come from the sequent.

  The name encoding is by prefixing "\<A>\<c>\<t>\<i>\<o>\<n>_"\<close>

definition DoAction :: \<open>action \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>DoAction action sequent result \<equiv> (PROP sequent \<Longrightarrow> PROP result)\<close>

text \<open>\<^prop>\<open>PROP DoAction action sequent result\<close> is the antecedent to be reasoned
  to return the construction result of the sequent by the action.\<close>

definition ACTION :: \<open>action \<Rightarrow> prop\<close> where \<open>ACTION \<equiv> Pure.term\<close>

lemma ACTION_I: \<open>PROP ACTION XX\<close> unfolding ACTION_def term_def .

subsubsection \<open>Methods of Applying Action\<close>

text \<open>There are two way to activate the construction of an action.
  One is by application mechanism where user inputs a theorem of shape \<^prop>\<open>PROP ACTION action\<close>;
  another is by synthesis, where user inputs a cartouche of \<^term>\<open>action\<close>.\<close>

paragraph \<open>First way, by Application\<close>

lemma [\<phi>reason 2000]:
  \<open> PROP DoAction action sequent result
\<Longrightarrow> PROP \<phi>Application_Method (ACTION action) sequent result\<close>
  unfolding \<phi>Application_Method_def DoAction_def \<phi>Application_def .

paragraph \<open>Second way, by Synthesis\<close>

lemma [\<phi>reason 1400]:
  \<open> PROP Synthesis_Parse action action'
\<Longrightarrow> PROP DoAction action' sequent result
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis (action::action) sequent result\<close>
  unfolding DoSynthesis_def DoAction_def .


subsubsection \<open>Snippets of Action\<close>

paragraph \<open>Action by View Shift\<close>

consts Action_VS :: \<open>action \<Rightarrow> action\<close>

definition View_Shift_Action :: \<open>action \<Rightarrow> bool \<Rightarrow> prop\<close>
  where \<open>View_Shift_Action action VS \<equiv> Trueprop VS\<close>

text \<open>Antecedent \<^prop>\<open>PROP View_Shift_Action action VS\<close> intends to find a view shift \<^prop>\<open>VS\<close>
  giving the purpose assigned to \<^term>\<open>action\<close>.\<close>

lemma (in \<phi>empty) [\<phi>reason ]:
  \<open> PROP View_Shift_Action action (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X1 \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2)
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R1\<heavy_comma> X1 \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any)
\<Longrightarrow> PROP DoAction (Action_VS action)
      (Trueprop (CurrentConstruction mode s R X))
      (Trueprop (CurrentConstruction mode s R (R1\<heavy_comma> Y) \<and> Any \<and> Any2))\<close>
  unfolding DoAction_def View_Shift_Reasoning_def View_Shift_Action_def
  using \<phi>apply_view_shift_P \<phi>frame_view by blast




section \<open>Elementary \<phi>-Types\<close>

subsection \<open>Type Level Subjection\<close>

definition SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j" 25)
  where \<open> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (\<lambda>x. x \<Ztypecolon> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<close>

lemma SubjectionTY_expn[\<phi>programming_simps, \<phi>expns]:
  \<open>(x \<Ztypecolon> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (x \<Ztypecolon> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding set_eq_iff SubjectionTY_def \<phi>Type_def by simp

lemma SubjectionTY_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<Longrightarrow> (P \<Longrightarrow> Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding SubjectionTY_expn using Subjection_inhabited .

lemma SubjectionTY_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited (x \<Ztypecolon> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> Inhabited (x \<Ztypecolon> T) \<and> P\<close>
  unfolding SubjectionTY_expn by (simp add: \<phi>inhabited)


subsection \<open>Type Level Existential Quantification\<close>

definition ExTyp :: \<open>('c \<Rightarrow> ('a, 'b) \<phi>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b)\<phi>\<close> (binder "\<exists>\<phi>" 10)
  where \<open>ExTyp T = (\<lambda>x. (\<exists>*c. x c \<Ztypecolon> T c))\<close>

syntax
  "_SetcomprPhiTy" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j/ _./ _ " [2,0,2] 2)
  "_SetcomprPhiTy'" :: "logic \<Rightarrow> idts \<Rightarrow> logic \<Rightarrow> logic"

parse_ast_translation \<open>
  let open Ast
    fun idts_to_abs x (Appl [Constant "_idts", a, b]) = Appl [Constant "_abs", a, idts_to_abs x b]
      | idts_to_abs x c = Appl [Constant "_abs", c, x]
    fun parse_SetcomprPhiTy ctxt [Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, x, T],idts,P] =
          Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>,
                idts_to_abs x idts,
                Appl [Constant "\<^const>NuSys.ExTyp_binder", idts,
                      (case P of (Appl [Constant "_constrain", Variable "True", _]) => T
                               | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, T, P])]]
      | parse_SetcomprPhiTy ctxt [X,idts,P] =
          Appl [Constant "\<^const>NuSys.ExTyp_binder", idts,
                (case P of (Appl [Constant "_constrain", Variable "True", _]) => X
                         | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, X, P])]
  in [(\<^syntax_const>\<open>_SetcomprPhiTy\<close>, parse_SetcomprPhiTy)] end
\<close>

(* TODO
term \<open>x \<Ztypecolon> (X a) \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j a b c. P a\<close>

translations
  " _SetcomprPhiTy' x idts X" <= "x \<Ztypecolon> (\<exists>\<phi> idts. X)"

print_ast_translation \<open>
  [(\<^syntax_const>\<open>_SetcomprPhiTy'\<close>, (fn _ => fn x => hd (@{print} x)))]
\<close>

term \<open>x \<Ztypecolon> (X a) \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j a b c. P a\<close>

*)

lemma ExTyp_expn[\<phi>expns,\<phi>programming_simps]:
  \<open>(x \<Ztypecolon> ExTyp T) = (\<exists>*a. x a \<Ztypecolon> T a)\<close>
  unfolding set_eq_iff ExTyp_def \<phi>Type_def by (simp add: \<phi>expns)

lemma ExTyp_inhabited[elim!, \<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> ExTyp T) \<Longrightarrow> (Inhabited (\<exists>*a. x a \<Ztypecolon> T a) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding ExTyp_expn .

lemma ExTyp_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited (x \<Ztypecolon> ExTyp T) \<longleftrightarrow> (\<exists>c. Inhabited (x c \<Ztypecolon> T c))\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)



subsection \<open>Identity\<close>

definition Identity :: " ('a,'a) \<phi> " where "Identity x = {x}"

lemma Identity_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> Identity) \<longleftrightarrow> p = x"
  unfolding \<phi>Type_def Identity_def by auto

lemma Identity_inhabited[elim!,\<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> Identity) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma Identity_E[\<phi>reason on \<open>?v \<Ztypecolon> Identity \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?x \<Ztypecolon> ?T \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> (x \<Ztypecolon> T) \<Longrightarrow> v \<Ztypecolon> Identity \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

lemma (in \<phi>empty) Identity_E_vs[\<phi>reason on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?v \<Ztypecolon> Identity \<longmapsto> ?x \<Ztypecolon> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w v \<Ztypecolon> Identity \<longmapsto> x \<Ztypecolon> T\<close>
  by (simp add: Identity_E View_Shift_by_Subtyp)

lemma to_Identity_\<phi>app:
  \<open>x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (v \<Ztypecolon> Identity \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j v. v \<in> (x \<Ztypecolon> T))\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

lemma from_Identity_\<phi>app:
  \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> X \<Longrightarrow> v \<Ztypecolon> Identity \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X\<close>
  unfolding Imply_def Premise_def by (simp add: \<phi>expns)



subsection \<open>Prod\<close>

definition \<phi>Prod :: " ('concrete::times, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixl "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b). A a * B b)"

lemma \<phi>Prod_expn[\<phi>expns]:
  "concrete \<in> ((a,b) \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>ca cb. concrete = ca * cb \<and> ca \<in> (a \<Ztypecolon> A) \<and> cb \<in> (b \<Ztypecolon> B))"
  unfolding \<phi>Prod_def \<phi>Type_def times_set_def by simp

lemma \<phi>Prod_expn':
  \<open>((a,b) \<Ztypecolon> A \<^emph> B) = (a \<Ztypecolon> A) * (b \<Ztypecolon> B)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma \<phi>Prod_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<Longrightarrow> (Inhabited (x1 \<Ztypecolon> T1) \<Longrightarrow> Inhabited (x2 \<Ztypecolon> T2) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Prod_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<longleftrightarrow> Inhabited (x1 \<Ztypecolon> T1) \<and> Inhabited (x2 \<Ztypecolon> T2)\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Prod_split: "((a,b) \<Ztypecolon> A \<^emph> B) = (a \<Ztypecolon> A) * (b \<Ztypecolon> B)"
  by (simp add: \<phi>expns set_eq_iff)

(*lemma (in \<phi>empty) SepNu_to_SepSet: "(OBJ (a,b) \<Ztypecolon> A \<^emph> B) = (OBJ a \<Ztypecolon> A) * (OBJ b \<Ztypecolon> B)"
  by (simp add: \<phi>expns set_eq_iff times_list_def) *)

lemma [\<phi>reason on \<open>(?x,?y) \<Ztypecolon> ?N \<^emph> ?M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (?x',?y') \<Ztypecolon> ?N' \<^emph> ?M' \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  " x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> N' \<^bold>a\<^bold>n\<^bold>d P1
\<Longrightarrow> y \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y' \<Ztypecolon> M' \<^bold>a\<^bold>n\<^bold>d P2
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (x',y') \<Ztypecolon> N' \<^emph> M' \<^bold>a\<^bold>n\<^bold>d P1 \<and> P2"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma (in \<phi>empty) [\<phi>reason on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w (?x,?y) \<Ztypecolon> ?N \<^emph> ?M \<longmapsto> (?x',?y') \<Ztypecolon> ?N' \<^emph> ?M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> x' \<Ztypecolon> N' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w y \<Ztypecolon> M \<longmapsto> y' \<Ztypecolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w (x,y) \<Ztypecolon> N \<^emph> M \<longmapsto> (x',y') \<Ztypecolon> N' \<^emph> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2"
  unfolding View_Shift_def \<phi>Prod_expn'
  by (smt (verit, best) mult.commute mult.left_commute) 


(*lemma [simp]: "A \<inter> S \<perpendicular> A \<inter> -S"
  unfolding disjoint_def by auto
lemma heap_split_id: "P h1' h2' \<Longrightarrow> \<exists>h1 h2. h1' ++ h2' = h1 ++ h2 \<and> P h1 h2" by auto
lemma heap_split_by_set: "P (h |` S) (h |` (- S)) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  by (rule exI[of _ "h |` S"], rule exI[of _ "h |` (- S)"])
    (auto simp add: map_add_def option.case_eq_if restrict_map_def disjoint_def disjoint_iff domIff)
lemma heap_split_by_addr_set: "P (h |` (MemAddress ` S)) (h |` (- (MemAddress ` S))) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  using heap_split_by_set .*)


subsection \<open>List Item & Empty List\<close>

subsubsection \<open>List Item\<close>

definition List_Item :: \<open>('v, 'a) \<phi> \<Rightarrow> ('v list, 'a) \<phi>\<close>
  where \<open>List_Item T = (\<lambda>x. { [v] |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma List_Item_expn[\<phi>expns]:
 \<open>p \<in> (x \<Ztypecolon> List_Item T) \<longleftrightarrow> (\<exists>v. p = [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding List_Item_def \<phi>Type_def by simp

lemma List_Item_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> List_Item T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<comment> \<open>A example for how to represent multi-elements list\<close>
  \<open> v1 \<in> (x1 \<Ztypecolon> T1)
\<Longrightarrow> v2 \<in> (x2 \<Ztypecolon> T2)
\<Longrightarrow> [v2,v1] \<in> ((x1, x2) \<Ztypecolon> (List_Item T1 \<^emph> List_Item T2))\<close>
  by (simp add: \<phi>expns times_list_def, rule exI[where x=\<open>[v1]\<close>], rule exI[where x=\<open>[v2]\<close>], simp)

subsubsection \<open>Empty List\<close>

definition Empty_List :: \<open>('v list, unit) \<phi>\<close>
  where \<open>Empty_List = (\<lambda>x. { [] })\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Empty_List) \<longleftrightarrow> p = []\<close>
  unfolding Empty_List_def \<phi>Type_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Empty_List) \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsection \<open>Stepwise Abstraction\<close>

definition \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 75)
  where \<open>\<phi>Composition T U = (\<lambda>x. (y \<Ztypecolon> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j y. y \<in> U x))\<close>

lemma \<phi>Composition_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T \<Zcomp> U) \<longleftrightarrow> (\<exists>y. p \<in> (y \<Ztypecolon> T) \<and> y \<in> (x \<Ztypecolon> U))\<close>
  unfolding \<phi>Composition_def \<phi>Type_def by (simp add: \<phi>expns)

lemma \<phi>Composition_inhabited[elim,\<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> T \<Zcomp> U) \<Longrightarrow> (\<And>y. Inhabited (x \<Ztypecolon> U) \<Longrightarrow> Inhabited (y \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast



subsection \<open>Refinement\<close>

definition NuRefine :: " ('a, 'b) \<phi> \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) \<phi> " (infixl "<where>" 80)
  where "(N <where> T) x = {p. (x \<in> T \<and>p \<in> (x \<Ztypecolon> N))}"

lemma NuRefine_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <where> P) \<longleftrightarrow> x \<in> P \<and> p \<in> (x \<Ztypecolon> N)"
  unfolding NuRefine_def \<phi>Type_def by simp

lemma NuRefine_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> N <where> P) \<Longrightarrow> (x \<in> P \<Longrightarrow> Inhabited (x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  " x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> M' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x' \<in> S
\<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> M' <where> S \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 30 on \<open>?x \<Ztypecolon> ?T <where> ?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P''\<close>, \<phi>overload D]:
  "x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
    \<Longrightarrow> x \<Ztypecolon> T <where> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<and> x \<in> S"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma refine_\<phi>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> (N <where> P)"
  unfolding Imply_def by (simp add: \<phi>expns)


subsection \<open>Forward Simulation\<close>

definition \<phi>F_simulation :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> (('av \<times> 'bv) set, ('a \<times> 'b) set) \<phi>\<close> (infixr "\<Rrightarrow>\<^sub>r" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow>\<^sub>r U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>u y. (v,u) \<in> g \<and> (x,y) \<in> f \<and> u \<in> (y \<Ztypecolon> U)) })\<close>


subsection \<open>Mapping\<close>

definition \<phi>Mapping :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> ('av \<Rightarrow> 'bv, 'a \<Rightarrow> 'b) \<phi>\<close> (infixr "\<Rrightarrow>" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow> U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U) })\<close>

lemma \<phi>Mapping_expn[\<phi>expns]:
  \<open>g \<in> (f \<Ztypecolon> T \<Rrightarrow> U) \<longleftrightarrow> (\<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U))\<close>
  unfolding \<phi>Mapping_def \<phi>Type_def by simp

lemma \<phi>Mapping_inhabited[\<phi>expns]:
  \<open>Inhabited (f \<Ztypecolon> T \<Rrightarrow> U) \<Longrightarrow> ((\<And>x. Inhabited (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (f x \<Ztypecolon> U)) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

subsection \<open>Point on a Mapping\<close>

definition \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<dash_tri_R_arrow>" 25)
  where \<open>\<phi>MapAt key T x = { 1(key := v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>MapAt_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>MapAt key T) \<longleftrightarrow> (\<exists>v. p = 1(key := v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>MapAt_def \<phi>Type_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>MapAt field T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)



subsection \<open>Down Lifting\<close> (*depreciated*)

definition DownLift :: "('a, 'b) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<phi>" (infixl "<down-lift>" 80)
  where "DownLift N g x = (g x \<Ztypecolon> N)"

lemma DownLift_expn[simp]: " p \<in> (x \<Ztypecolon> N <down-lift> g) \<longleftrightarrow> p \<in> (g x \<Ztypecolon> N) "
  unfolding DownLift_def \<phi>Type_def by simp

lemma [elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> N <down-lift> g) \<Longrightarrow> (Inhabited (g x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

(* lemma [\<phi>cast_overload E]: " x \<Ztypecolon> N <down-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s g x \<Ztypecolon> N" unfolding Imply_def by simp *)
lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> x \<Ztypecolon> N <down-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> N" unfolding Imply_def by (simp add: \<phi>expns)

(* lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (g y = x) \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <down-lift> g"
  unfolding Intro_def Imply_def by (simp add: \<phi>expns) blast
lemma [\<phi>reason, \<phi>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <down-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s g y \<Ztypecolon> M"
  unfolding Dest_def Imply_def by (simp add: \<phi>expns) *)

lemma [\<phi>reason]: " x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y1 \<Ztypecolon> M \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <down-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns)
lemma "\<down>lift_\<phi>app": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> N <down-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns)



subsection \<open>Up Lifting\<close> (*depreciated*)

definition UpLift :: "('a, 'c) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<phi>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> p \<in> (y \<Ztypecolon> N))}"

lemma UpLift_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <up-lift> f) \<longleftrightarrow> (\<exists>y. (f y = x) \<and> p \<in> (y \<Ztypecolon> N))"
  unfolding UpLift_def \<phi>Type_def by auto

lemma UpLift_inhabited[elim,\<phi>reason_elim]:
  "Inhabited (x \<Ztypecolon> N <up-lift> f) \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> Inhabited (y \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma "\<up>lift_\<phi>app":
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <up-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns) blast
(* lemma [\<phi>overload D]: "x \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists> \<Ztypecolon> M) "
  unfolding Imply_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <up-lift> g"
  unfolding Intro_def Imply_def by (simp add: \<phi>expns) blast *)

lemma [\<phi>reason 130]:
  "x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> M' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x' \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M' <up-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 20]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s N \<^bold>a\<^bold>n\<^bold>d P x)
\<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s N \<^bold>a\<^bold>n\<^bold>d (\<exists>x. y = g x \<and> P x)"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 150]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y' x \<Ztypecolon> M' x \<^bold>a\<^bold>n\<^bold>d P x)
    \<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*x. y' x \<Ztypecolon> M' x) \<^bold>a\<^bold>n\<^bold>d (\<exists>x. y = g x \<and> P x)"
  unfolding Imply_def by (simp add: \<phi>expns) blast

(* lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. (x \<Ztypecolon> M) \<and>\<^sup>s g x = y)"
  unfolding Dest_def Imply_def by (simp add: \<phi>expns) blast *)

lemma "x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f x \<Ztypecolon> N <up-lift> f" unfolding Imply_def by (simp add: \<phi>expns) blast
lemma "x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f x \<Ztypecolon> N <up-lift> f" unfolding Imply_def by (simp add: \<phi>expns) blast

(* lemma "\<phi>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<phi>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<phi>Equal_def by (auto 0 6) *)

subsection \<open>Any\<close>

definition \<phi>Any :: \<open>('x, unit) \<phi>\<close>
  where \<open>\<phi>Any = (\<lambda>_. UNIV)\<close>

lemma \<phi>Any_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Any)\<close>
  unfolding \<phi>Any_def \<phi>Type_def by simp

lemma \<phi>Any_inhabited[\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Any) \<Longrightarrow> C \<Longrightarrow> C\<close>
  .

lemma \<phi>Any_cast [\<phi>reason 1200 on \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?x \<Ztypecolon> \<phi>Any \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<phi>Any\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

lemma (in \<phi>empty) \<phi>Any_vs [\<phi>reason 1200 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?x \<Ztypecolon> \<phi>Any \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> x \<Ztypecolon> \<phi>Any\<close>
  by (simp add: View_Shift_by_Subtyp \<phi>Any_cast)
  

subsection \<open>Value\<close>

definition (in \<phi>empty) Val :: \<open>'v sem_value \<Rightarrow> ('v, 'a) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'a) \<phi>\<close>
  where \<open>Val val T = (\<lambda>x. Void \<^bold>s\<^bold>u\<^bold>b\<^bold>j dest_sem_value val \<in> (x \<Ztypecolon> T))\<close>

lemma (in \<phi>empty) Val_expn [\<phi>expns]:
  \<open>(x \<Ztypecolon> Val val T) = (Void \<^bold>s\<^bold>u\<^bold>b\<^bold>j dest_sem_value val \<in> (x \<Ztypecolon> T))\<close>
  unfolding Val_def \<phi>Type_def by (simp add: \<phi>expns)

lemma (in \<phi>empty) Val_inhabited [\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Val val T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma (in \<phi>empty) Val_cast [\<phi>reason]:
  \<open> y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> y \<Ztypecolon> Val v U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> Val v T \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)


subsubsection \<open>Syntax\<close>

consts anonymous_val :: \<open>'a sem_value\<close>
  \<comment> \<open>Any anonymous_val will be translated into a unique value during the parsing\<close>

syntax val_syntax :: "logic \<Rightarrow> logic" ("\<^bold>v\<^bold>a\<^bold>l _" [18] 17)

setup \<open>(Sign.add_trrules (let open Ast 
    in [
      Syntax.Parse_Rule (
        Appl [Constant \<^syntax_const>\<open>val_syntax\<close>,
                Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable "x", Variable "T"]],
        Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable "x",
                Appl [Constant "\<^const>local.Val", Constant \<^const_name>\<open>anonymous_val\<close>, Variable "T"]])
  ] end))\<close>

ML_file \<open>library/procedure_syntax.ML\<close>

lemma (in \<phi>empty) [\<phi>reason 1100 on
  \<open>PROP Synthesis_Parse (?x \<Ztypecolon> (?T::?'a \<Rightarrow> 'VAL set)) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse (x \<Ztypecolon> T) (\<lambda>v. x \<Ztypecolon> Val v T)\<close>
  unfolding Synthesis_Parse_def ..

subsubsection \<open>Simplification Rules\<close>

lemma (in \<phi>empty) [\<phi>programming_simps]:
    \<open>Val raw (ExTyp T) = (\<exists>\<phi> c. Val raw (T c))\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)

lemma (in \<phi>empty) [\<phi>programming_simps]:
    \<open>Val raw (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (Val raw T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)


subsubsection \<open>Application Methods for Subtyping\<close>

lemma (in \<phi>empty) [\<phi>reason 2100 on \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> if no \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Val_cast \<phi>cast_intro_frame by metis


lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>
  PROP \<phi>Application_Method (Trueprop (?x' \<Ztypecolon> ?T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> if no \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x' \<Ztypecolon> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Val_cast \<phi>cast_intro_frame by metis

subsubsection \<open>Simplification\<close>

lemma (in \<phi>empty) \<phi>Val_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Val v T) = (x' \<Ztypecolon> Val v T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup (in \<phi>empty) Val_simp_cong ("x \<Ztypecolon> Val v T") = \<open>
  K (fn ctxt => NuSimpCong.simproc (Proof_Context.get_thm ctxt "local.\<phi>Val_simp_cong") ctxt)
\<close>

subsubsection \<open>Synthesis\<close>

lemma (in \<phi>empty) [\<phi>reason 2000 on
  \<open>PROP Synthesis_Parse (?raw::'VAL sem_value) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse raw (\<lambda>_. x \<Ztypecolon> Val raw T)\<close>
  unfolding Synthesis_Parse_def ..

lemma (in \<phi>empty) [\<phi>reason 1200
    on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> Val ?raw ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> PROP View_Shift_Reasoning
      (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> SYNTHESIS x \<Ztypecolon> Val raw T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_. R\<heavy_comma> SYNTHESIS x \<Ztypecolon> Val raw T \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_Reasoning_def GOAL_CTXT_def
  by (rule "\<phi>__Return_rule__")


subsubsection \<open>Auto unfolding for value list\<close>

lemma (in \<phi>empty)[simp]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv Empty_List) = (Void \<^bold>s\<^bold>u\<^bold>b\<^bold>j USELESS (rawv = \<phi>V_nil))\<close>
  unfolding set_eq_iff USELESS_def
  by (cases rawv; simp add: \<phi>expns)

lemma (in \<phi>empty)[simp]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv (List_Item T)) = (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T \<^bold>s\<^bold>u\<^bold>b\<^bold>j USELESS (\<exists>v. rawv = \<phi>V_cons v \<phi>V_nil))\<close>
  unfolding set_eq_iff \<phi>V_cons_def USELESS_def
  apply (cases rawv; clarsimp simp add: \<phi>expns \<phi>V_tl_def \<phi>V_hd_def times_list_def; rule;
          clarsimp simp add: sem_value_All sem_value_exists)
  by blast+

lemma (in \<phi>empty)[simp]:
  \<open> [] \<notin> (\<exists>*x. x \<Ztypecolon> L)
\<Longrightarrow> (\<exists>*x. x \<Ztypecolon> Val rawv (L \<^emph> List_Item T)) = ((\<exists>*x. x \<Ztypecolon> Val (\<phi>V_tl rawv) L)\<heavy_comma> (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T))\<close>
  unfolding set_eq_iff
  apply (cases rawv; clarsimp simp add: \<phi>expns \<phi>V_tl_def \<phi>V_hd_def times_list_def)
  by (metis (no_types, opaque_lifting) append_Cons append_self_conv2 list.distinct(1) list.exhaust_sel list.sel(1) tl_Nil tl_append2)

lemma [simp]:
  \<open>[] \<notin> (\<exists>*x. x \<Ztypecolon> (L \<^emph> List_Item T))\<close>
  by (rule; clarsimp simp add: \<phi>expns times_list_def)

lemma [simp]:
  \<open>[] \<notin> (\<exists>*x. x \<Ztypecolon> List_Item T)\<close>
  by (rule; clarsimp simp add: \<phi>expns times_list_def)



subsection \<open>Semantic Type Tagging\<close>

paragraph \<open>Annotation for Single One\<close>

definition (in \<phi>empty_sem) Of_Type :: \<open>('VAL,'a) \<phi> \<Rightarrow> 'TY \<Rightarrow> ('VAL,'a) \<phi>\<close> (infix "<of-type>" 23)
  where \<open>(T <of-type> TY) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> Well_Type TY)\<close>

lemma (in \<phi>empty_sem) [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-type> TY) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> p \<in> Well_Type TY\<close>
  unfolding Of_Type_def \<phi>Type_def by (simp add: \<phi>expns)

lemma (in \<phi>empty_sem) [\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-type> TY) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma (in \<phi>empty_sem) [\<phi>reason 1200 on \<open>\<phi>SemType (?x \<Ztypecolon> ?T <of-type> ?TY) ?TY'\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> T <of-type> TY) TY\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

lemma (in \<phi>empty_sem) [\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U <of-type> TY \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def \<phi>SemType_def by (simp add: \<phi>expns) blast



paragraph \<open>Annotation for a List\<close>

definition (in \<phi>empty_sem) Of_Types :: \<open>('VAL list,'a) \<phi> \<Rightarrow> 'TY list \<Rightarrow> ('VAL list,'a) \<phi>\<close> (infix "<of-types>" 23)
  where \<open>(T <of-types> TYs) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> {p. list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs})\<close>

lemma (in \<phi>empty_sem) [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-types> TYs) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs\<close>
  unfolding Of_Types_def \<phi>Type_def by (simp add: \<phi>expns)

lemma (in \<phi>empty_sem) [\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-types> TYs) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast



subsection \<open>Share\<close>

definition (in perm_transformer) \<phi> :: \<open>rat \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi> n T = (\<lambda>x. { share n (\<psi> v) |v. v \<in> (x \<Ztypecolon> T) \<and> can_share (\<psi> v) } \<^bold>s\<^bold>u\<^bold>b\<^bold>j 0 < n \<and> n \<le> 1)\<close>

lemma (in perm_transformer) [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> n T) \<longleftrightarrow> (\<exists>v. p = share n (\<psi> v) \<and> v \<in> (x \<Ztypecolon> T) \<and> can_share (\<psi> v) \<and> 0 < n \<and> n \<le> 1)\<close>
  unfolding \<phi>_def \<phi>Type_def by (simp add: \<phi>expns, blast)

(*
definition \<phi>Share :: \<open>rat \<Rightarrow> ('v,'x) \<phi> \<Rightarrow> ('v share option, 'x) \<phi>\<close> (infix "\<Znrres>\<phi>" 61)
  where \<open>\<phi>Share n T x = { Some (Share n v) |v. v \<in> (x \<Ztypecolon> T) \<and> 0 < n \<and> n \<le> 1 } \<close>

lemma \<phi>Share_expn[\<phi>expns]:
  \<open> p \<in> (x \<Ztypecolon> n \<Znrres>\<phi> T) \<longleftrightarrow> (\<exists>v. p = Some (Share n v) \<and> v \<in> (x \<Ztypecolon> T) \<and> 0 < n \<and> n \<le> 1) \<close>
  unfolding \<phi>Type_def \<phi>Share_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> n \<Znrres>\<phi> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) *)


definition \<phi>Some :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<circled_bullet> _" [91] 90)
  where \<open>\<phi>Some T = (\<lambda>x. { Some v |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma \<phi>Some_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Some T) \<longleftrightarrow> (\<exists>v. p = Some v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>Some_def by simp

lemma \<phi>Some_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Some T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)



definition \<phi>None :: \<open>('v::one, unit) \<phi>\<close> ("\<circled_white_bullet>")
  where \<open>\<phi>None T = { 1 } \<close>

lemma \<phi>None_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>None) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>None_def \<phi>Type_def by simp

lemma \<phi>None_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>None) \<Longrightarrow> C \<Longrightarrow> C\<close> .




subsection \<open>Agreement\<close>

definition Agreement :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T agree option, 'x) \<phi>\<close>
  where \<open>Agreement T x = { Some (agree v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma Agreement_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Agreement T) \<longleftrightarrow> (\<exists>v. p = Some (agree v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Agreement_def by simp

lemma Agreement_inhabited[simp]:
  \<open>Inhabited (x \<Ztypecolon> Agreement T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

subsection \<open>Nonsepable\<close>

definition Nonsepable :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T nonsepable, 'x) \<phi>\<close>
  where \<open>Nonsepable T x = nonsepable ` (x \<Ztypecolon> T)\<close>

lemma Nonsepable_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Nonsepable T) \<longleftrightarrow> (\<exists>v. p = nonsepable v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Nonsepable_def by blast

lemma Nonsepable_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Nonsepable T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

subsection \<open>Black Hole\<close>

text \<open>Essentially, the system is a Classical Separation Logic.
  For some situation like garbage collection, Intuitionistic Separation Logic can be more convenient.
  Therefore, we employ a `Black Hole' which can contain arbitrary resources to simulate the
    Intuitionistic Separation Logic\<close>

abbreviation (in \<phi>empty) Black_Hole :: \<open>('FIC_N \<Rightarrow> 'FIC) set\<close>
  where \<open>Black_Hole \<equiv> UNIV\<close>

lemma UNIV_subty [\<phi>reason on \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s UNIV \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s UNIV\<close>
  unfolding Imply_def by simp

lemma (in \<phi>empty) UNIV_view_shift [\<phi>reason on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> UNIV \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> UNIV\<close>
  using UNIV_subty View_Shift_by_Subtyp by blast


subsection \<open>Misc.\<close>

definition Function_over :: \<open>('a,'b) \<phi> \<Rightarrow> 'c \<Rightarrow> ('a, 'c \<Rightarrow> 'b) \<phi>\<close> (infix "<func-over>" 40)
  where \<open>(T <func-over> x) = (\<lambda>f. f x \<Ztypecolon> T)\<close>

text \<open>\<^term>\<open>f \<Ztypecolon> T <func-over> x\<close> constrains the abstract object f is a function about x.
  It seems redundant considering \<^term>\<open>f x \<Ztypecolon> T\<close>. Nonetheless, it is useful when given some
    pattern \<^schematic_term>\<open>?f x \<Ztypecolon> T\<close> and trying to match it by some \<^term>\<open>g x \<Ztypecolon> T\<close>.
  Note such match has multiple solutions (e.g. \<^term>\<open>f = g\<close> or \<^term>\<open>f = (\<lambda>_. g x)\<close>), so
    the usual reasoning cannot determine which solution should be chosen.
  By contrast, \<^term>\<open>f \<Ztypecolon> T <func-over> x\<close> has specially designed sub-typing rule converting
    from \<^term>\<open>fx \<Ztypecolon> T\<close>,

\<^prop>\<open> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s fx \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f \<Ztypecolon> T <func-over> x \<^bold>a\<^bold>n\<^bold>d P\<close>,

    which using \<^term>\<open>lambda_abstraction\<close>, always abstracts any occurrences of x in fx exhaustively, e.g.
    always resulting in \<^term>\<open>f = g\<close> instead of \<^term>\<open>f = (\<lambda>_. g x)\<close>\<close>

lemma Function_over_expn[\<phi>expns]:
  \<open>(f \<Ztypecolon> T <func-over> x) = (f x \<Ztypecolon> T)\<close>
  unfolding Function_over_def \<phi>Type_def by simp

lemma Function_over_case_named[simp]:
  \<open>(case_named f \<Ztypecolon> T <func-over> tag x) = (f \<Ztypecolon> T <func-over> x)\<close>
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s fx \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f \<Ztypecolon> T <func-over> x \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def lambda_abstraction_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> f x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> f \<Ztypecolon> T <func-over> x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

lemma (in \<phi>empty) [\<phi>reason 2000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> fx \<Ztypecolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> f \<Ztypecolon> T <func-over> x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)

lemma (in \<phi>empty) [\<phi>reason 2000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w f x \<Ztypecolon> T \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w f \<Ztypecolon> T <func-over> x \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)


lemma (in \<phi>empty) [\<phi>reason 1200 on
  \<open>PROP Synthesis_Parse ?input (\<lambda>v. ?f \<Ztypecolon> ?T v <func-over> ?x :: ('FIC_N,'FIC)assn)\<close>
]:
  \<open> PROP Synthesis_Parse input (\<lambda>v. fx \<Ztypecolon> T v)
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> PROP Synthesis_Parse input (\<lambda>v. f \<Ztypecolon> T v <func-over> x :: ('FIC_N,'FIC)assn)\<close>
  unfolding Synthesis_Parse_def ..


lemma (in \<phi>empty) [\<phi>reason 1200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> SYNTHESIS f x \<Ztypecolon> T v \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> SYNTHESIS f \<Ztypecolon> T v <func-over> x \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P\<close>
  unfolding Synthesis_def lambda_abstraction_def by (simp add: \<phi>expns)


section \<open>Interactive Programming & Proving Environment\<close>

subsection \<open>ML codes\<close>


ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/procedure.ML"


ML_file NuSys.ML
ML_file "./library/processors.ML"
ML_file "./library/obtain.ML"
ML_file "./library/generalization.ML"
(* ML_file "./codegen/compilation.ML" *)
ML_file NuToplevel.ML


subsection \<open>Isar Commands & Attributes\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<phi>instr"}, NuInstructions.list_definitions #> map snd))  \<close>

attribute_setup \<phi>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<phi>-system\<close>

attribute_setup \<phi>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (NuProcessor.get_attr ctx name) (ctx,toks))
  || Scan.lift NuProcessor.process_attr\<close>
  \<open>Evaluate the \<phi>-system process or the process of the given processor on the target theorem\<close>


ML \<open>

local open Scan NuToplevel NuSys Parse 
val nustatement = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- opt_attribs -- Scan.repeat1 Parse.propp);
val structured_statement =
  nustatement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));
val statement1 = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.propp);
val requires_statement = \<^keyword>\<open>assumes\<close> |-- Parse.!!! statement1;
val premises_statement = \<^keyword>\<open>premises\<close> |-- Parse.!!! statement1;
val precond_statement = Scan.repeat ((premises_statement >> map (pair NuToplevel.Premise))
                || (requires_statement >> map (pair NuToplevel.Requirement))) >> flat;
val requires_opt1 = Scan.option (\<^keyword>\<open>assumes\<close> |-- Parse.term);
val where_statement = Scan.optional (\<^keyword>\<open>where\<close> |--
        Parse.and_list1 (Scan.repeat Args.var --| Parse.$$$ "=" -- Parse.term)) [];
val defines_statement = Scan.optional ($$$ "defines" |-- Parse.!!! statement1) [];
val goal = Scan.option (\<^keyword>\<open>goal\<close> |-- Parse.term)
val nu_statements = Parse.for_fixes -- Scan.optional Parse_Spec.includes [] --
           where_statement -- defines_statement  -- precond_statement -- goal;

val arg = Parse.term
val arg_ret = (\<^keyword>\<open>argument\<close> |-- arg --| \<^keyword>\<open>return\<close> -- arg -- option (\<^keyword>\<open>throws\<close> |-- arg))

in

(* val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>exty_simproc\<close> "setup the pecific simproc for \<^const>\<open>ExTy\<close>"
  (Parse.binding >> NuExTyp.set_simproc_cmd) *)

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- nu_statements -- arg_ret) >>
        (fn ((b,(((((fixes,includes),lets),defs),preconds),G)), ((arg,ret),throws)) =>  
            (begin_proc_cmd b arg ret throws fixes includes lets defs preconds G)));

val loop_variables = $$$ "var" |-- !!! vars;
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close> "begin a recursive procedure construction"
    ((Parse_Spec.opt_thm_name ":" -- loop_variables -- nu_statements -- arg_ret) >>
        (fn (((b,vars),(((((fixes,includes),lets),defs),preconds),G)), ((arg,ret),throws)) =>  
            (begin_rec_proc_cmd b arg ret throws (vars,fixes) includes lets defs preconds G)));

(* val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>\<phi>cast\<close> "begin a procedure construction"
    ((Parse_Spec.thm_name ":" -- option ($$$ "and" |-- Parse.term) -- nu_statements - arg_ret) >>
        (fn ((b,(((((fixes,includes),lets),defs),preconds),G)), (arg,ret)) =>
            (begin_cast_cmd b arg ret fixes includes lets defs preconds G))); *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>;;\<close> "Lead statements of \<phi> programs"
    (NuProcessor.powerful_process_p >> Toplevel.proof)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "Begin a \<phi> program block"
   (((optional (\<^keyword>\<open>premises\<close> |--
            and_list (binding -- opt_attribs || Parse.attribs >> pair Binding.empty)) []
      >> NuToplevel.begin_block_cmd)
   -- NuProcessor.powerful_process_p_inert)
   >> (fn (blk,prcs) => Toplevel.proof' (prcs oo blk)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "End a \<phi> program block"
    (Phi_Generalization.syntax >> (Toplevel.proof' o NuToplevel.end_block_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>.\<close> "End a \<phi> program block using default tactic"
    (((Phi_Generalization.syntax >> (fn genric => fn int =>
        NuToplevel.end_block_cmd genric int
    #> (fn s => Proof.using_facts (Proof_Context.get_thms (Proof.context_of s) "\<phi>") s)
    #> Proof.local_future_terminal_proof
          ((Method.Basic (SIMPLE_METHOD o CHANGED_PROP o auto_tac), Position.no_range)
          ,NONE)))
   -- NuProcessor.powerful_process_p_inert)
   >> (fn (blk,prcs) => Toplevel.proof' (prcs oo blk)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>processor\<close> "define \<phi>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword || Parse.string)
          -- Parse.nat -- (\<^keyword>\<open>(\<close> |-- Parse.enum "|" Parse.term --| \<^keyword>\<open>)\<close> )
          -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
        >> NuProcessor.setup_cmd)

(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>interface\<close> "declare \<phi>interface"
      (Parse.binding --| $$$ "=" -- Parse.const -- option ($$$ ":" |-- Parse.typ --| $$$ "\<longmapsto>" -- Parse.typ)
        >> (Toplevel.theory o NuProcedure.add_interface_command))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>export_llvm\<close> "export LLVM target"
      (Scan.succeed (Toplevel.theory (NuToplevel.export_LLVM))) *)

end
\<close>

attribute_setup intro_forall = \<open>Scan.lift (Scan.repeat Args.var) >> (fn tms =>
  Thm.rule_attribute [] (fn ctx => fn th => 
    let open Thm
    val vs = add_vars th Vars.empty |> Vars.dest
    val foralls = map (fn tm => case find_first (fn (_,v) => #1 (dest_Var (term_of v)) = tm) vs
                  of SOME (_,y) => y | _ => error (#1 tm ^ " is not a var ")) tms
    in Drule.forall_intr_list foralls th end)) \<close>


subsection \<open>Elements of the Language\<close>

text \<open>Convention of priorities:
  \<^item> Simplifications and Conversions for canonical forms < 1000
  \<^item> Reasoning Antecedents = 1000
  \<^item> General Application not bound on specific pattern or keyword : 9000~9999
\<close>

context \<phi>empty begin

subsubsection \<open>Controls\<close>

\<phi>processor set_auto_level 10 (\<open>PROP ?P\<close>) \<open>(fn (ctxt, sequent) => NuParse.auto_level_force >>
  (fn auto_level' => fn _ => (Config.put Nu_Reasoner.auto_level auto_level' ctxt, sequent)))\<close>
  \<open>Note the declared auto-level is only valid during the current statement.
   In the next statement, the auto-level will be reset to the default fully-automated level.\<close>

\<phi>processor repeat 12 (\<open>PROP ?P\<close>) \<open>let
  in fn (ctxt, sequent) =>
    Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*") >> (fn (tok,n) => fn () =>
        (case Int.fromString n of SOME n => funpow n | _ => error ("should be a number: "^n))
          (NuProcessor.process_by_input [tok]) (ctxt, sequent)
    )
  end\<close>


subsubsection \<open>Constructive\<close>

\<phi>processor accept_call 500 (\<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g ?f \<^bold>o\<^bold>n ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E\<close>) \<open>fn stat =>
  Scan.succeed (fn _ => NuSys.accept_proc stat)\<close>

\<phi>processor "apply" 9000 (\<open>?P\<close>) \<open> fn (ctxt,sequent) => NuApplicant.parser >> (fn xnames => fn _ =>
  (NuApply.apply (NuApplicant.applicant_thms ctxt xnames) (ctxt, sequent)))\<close>

\<phi>processor set_param 5000 (\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ?P \<Longrightarrow> PROP ?Q\<close>) \<open>fn stat => Parse.term >> (fn term => fn _ =>
  NuSys.set_param_cmd term stat)\<close>

\<phi>processor set_label 5000 (\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l ?P \<Longrightarrow> PROP ?Q\<close>) \<open>fn stat => Parse.name >> (fn name => fn _ =>
  NuSys.set_label name stat)\<close>

\<phi>processor rule 9000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
  \<open>fn (ctxt, sequent) => NuApplicant.parser >> (fn thms => fn _ =>
    let open NuBasics
    val apps = NuApplicant.applicant_thms ctxt thms
    val sequent = perhaps (try (fn th => @{thm Argument_I} RS th)) sequent
    in case Seq.pull (Thm.biresolution (SOME ctxt) false (map (pair false) apps) 1 sequent)
         of SOME (th, _) => (ctxt,th)
          | _ => raise THM ("RSN: no unifiers", 1, sequent::apps) end)\<close>

ML \<open>val phi_synthesis_parsing = Config.declare_bool ("\<phi>_synthesis_parsing", \<^here>) (K false)\<close>

\<phi>processor synthesis 8800 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S\<close> | \<open>PROP ?P \<Longrightarrow> PROP ?RM\<close>)
  \<open>fn (ctxt, sequent) => Parse.group (fn () => "term") (Parse.inner_syntax (Parse.cartouche || Parse.number))
>> (fn raw_term => fn () =>
  let
    val ctxt_parser = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
                        |> Config.put phi_synthesis_parsing true
    val term = Syntax.parse_term ctxt_parser raw_term
                  |> Syntax.check_term ctxt_parser
                  |> Thm.cterm_of ctxt
   in
    NuSys.synthesis term (ctxt, sequent)
  end)\<close>

\<phi>processor existential_elimination 50 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ExSet ?T\<close>)
  \<open>fn stat => (\<^keyword>\<open>\<exists>\<close> |-- Parse.list1 Parse.binding) #> (fn (insts,toks) => (fn () =>
      raise Process_State_Call' (toks, stat, NuObtain.choose insts), []))\<close>

\<phi>processor implicit_existential_elimination 800 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ExSet ?T\<close>)
  \<open>fn stat => Scan.succeed (fn () =>
      if Config.get (#1 stat) Nu_Reasoner.auto_level >= 2
      then raise Process_State_Call (stat, NuObtain.auto_choose)
      else raise Bypass NONE)\<close>

subsubsection \<open>Simplifiers & Reasoners\<close>

\<phi>processor enter_proof 5000 (\<open>Premise ?mode ?P \<Longrightarrow> PROP ?Any\<close>)
  \<open>fn stat => \<^keyword>\<open>affirm\<close> >> (fn _ => fn () =>
      raise Terminate_Process (stat, snd o NuToplevel.prove_prem false))\<close>

\<phi>processor \<phi>simplifier 100 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close>)  \<open>NuProcessors.simplifier []\<close>
(* \<phi>processor \<phi>simplifier_final 9999 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close> *)

\<phi>processor move_fact 200 (\<open>(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T) \<and> ?P\<close>)
\<open>fn (ctxt, sequent) => Scan.succeed (fn _ =>
  let
    fun filter_lemma th =
      case Thm.prop_of th
        of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>USELESS\<close> $ _) => NONE
         | \<^const>\<open>Trueprop\<close> $ \<^const>\<open>True\<close> => NONE
         | _ => SOME th
    val lemmas = (sequent RS @{thm conjunct2})
                  |> HOLogic.conj_elims ctxt
                  |> map_filter filter_lemma
    val (_,ctxt') = Proof_Context.note_thms ""
                      ((Binding.empty, [Named_Theorems.add \<^named_theorems>\<open>\<phi>lemmata\<close>]),
                       [(lemmas,[])]) ctxt
  in
    (ctxt', sequent RS @{thm conjunct1})
  end)\<close>

(* Any simplification should finish before priority 999, or else
 *  this processor will be triggered unnecessarily frequently.*)
\<phi>processor set_\<phi>this 999 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close>)
\<open>fn (ctxt, sequent) => Scan.succeed (fn _ =>
  let
    val ctxt' = NuBasics.set_programming_sequent' sequent ctxt
  in
    raise Bypass (SOME(ctxt', sequent))
  end)\<close>

\<phi>processor \<phi>reason 1000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
\<open>fn stat => Scan.succeed (fn _ =>
  let open NuBasics
    fun reason i (ctxt,sequent) =
      if Thm.no_prems sequent
      then (ctxt,sequent)
      else case Nu_Reasoner.reason (ctxt, Goal.protect 1 sequent)
             of SOME (ctxt',sequent') => reason (1+i) (ctxt', Goal.conclude sequent')
              | NONE => if i = 0 then raise Bypass (SOME (ctxt,sequent))
                                 else (ctxt,sequent)
  in reason 0 stat
  end)\<close>

\<phi>processor naive_obligation_solver 8000 (\<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n ?P \<Longrightarrow> PROP ?Q\<close> | \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ?P \<Longrightarrow> PROP ?Q\<close>)
  \<open>fn (ctxt,sequent) => Scan.succeed (fn () =>
    if Config.get ctxt Nu_Reasoner.auto_level >= 2
    then case Seq.pull (Nu_Reasoners.naive_obligation_solver ctxt sequent)
           of SOME (ret, _) => (ctxt, ret)
            | NONE => raise Bypass NONE
    else raise Bypass NONE)\<close>

\<phi>processor fold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => NuParse.$$$ "fold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.fold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>

\<phi>processor unfold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => NuParse.$$$ "unfold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.unfold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>

(* \<phi>processor goal 1300 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close> \<open>
  fn (ctxt, sequent) => Parse.$$$ "goal" >> (fn _ => fn _ =>
    let
      val goal = Proof_Context.get_thm ctxt "\<phi>thesis" |> Drule.dest_term
      val (_,_,desired_nu) = PhiSyntax.dest_procedure_c goal
      val ty = Thm.typ_of_cterm desired_nu
      val prot = Const (\<^const_name>\<open>Implicit_Protector\<close>, ty --> ty) |> Thm.cterm_of ctxt
      val ctxt = Config.put Nu_Reasoner.auto_level 1 ctxt
    in NuSys.cast (Thm.apply prot desired_nu) (ctxt,sequent) end
)\<close> *)

end

paragraph \<open>Quantification Expansion\<close>

simproc_setup named_forall_expansion ("All (P :: 'a <named> 'names \<Rightarrow> bool)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.forall_expansion)\<close>

simproc_setup named_exSet_expansion ("ExSet (P :: 'a <named> 'names \<Rightarrow> 'b set)") =
  \<open>K (fn ctx => fn cterms => QuantExpansion.simproc_of QuantExpansion.ExNu_expansion ctx cterms)\<close>

simproc_setup named_pureAll_expansion ("Pure.all (P :: 'a <named> 'names \<Rightarrow> prop)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.pure_All_expansion)\<close>

lemmas [unfolded atomize_eq[symmetric], named_expansion] =
  Product_Type.prod.case NuSys.named.case Function_over_case_named



section \<open>Reasoning & Programming\<close>



(*subsubsection \<open>Syntax & Auxiliary\<close>

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
  unfolding MemAddrState_def addr_allocated_def by auto (metis \<phi>set_mono domI map_le_def option.sel) *)

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
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<phi>Independent S claim
    \<Longrightarrow> Alive k \<in> claim \<Longrightarrow> MemAddrState (h(k:=None)) addr S"
  unfolding MemAddrState_def \<phi>Independent_def by auto
lemma MemAddrState_retained_S[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<phi>Independent S claim
    \<Longrightarrow> Write k \<in> claim \<Longrightarrow> MemAddrState (h(k \<mapsto> v)) addr S"
  unfolding MemAddrState_def \<phi>Independent_def by auto

*)


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<in> S \<Longrightarrow> h |` S \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<notin> S \<Longrightarrow> h |` (- S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)

*)

subsection \<open>General Rules & Tools\<close>

lemma (in \<phi>empty) "_\<phi>cast_internal_rule_":
  " \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T'"
  unfolding CurrentConstruction_def GOAL_CTXT_def Imply_def FOCUS_TAG_def
    View_Shift_Reasoning_def View_Shift_def
  by blast

lemma (in \<phi>empty) "_\<phi>cast_internal_rule_'":
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> (\<And>v. PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w T v \<longmapsto> T' v \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E"
  unfolding FOCUS_TAG_def Imply_def PendingConstruction_def bind_def GOAL_CTXT_def
    View_Shift_Reasoning_def View_Shift_def
  apply (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff)
  subgoal for x by (cases x; simp; fastforce) .


(* subsubsection \<open>General Rules\<close>

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>VAL ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s VAL ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> VAL X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s VAL Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>OBJ ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> OBJ X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast) *)


subsubsection \<open>General Simplification for Assertions\<close>

named_theorems assertion_simps

consts assertion_simplification :: mode

\<phi>reasoner assertion_simplification 1200
  (conclusion \<open>Simplify assertion_simplification ?X' ?X\<close>)
  = ((simp only: assertion_simps)?, rule Simplify_I)

lemmas [assertion_simps] =
  mult_zero_right mult_zero_left mult_1_right mult_1_left add_0_right add_0_left



subsubsection \<open>Case Analysis\<close>


lemma [\<phi>reason 1000]: "Premise mode (A = B x y) \<Longrightarrow> Premise mode (A = case_prod B (x,y))" by simp
lemma [\<phi>reason 1000]: "Premise mode (A = B x) \<Longrightarrow> Premise mode (A = case_named B (tag x))" by simp
lemma [\<phi>reason 1000]: "Premise mode (A = B a x) \<Longrightarrow> Premise mode (A = case_object B (a \<Zinj> x))" by simp

definition CaseSplit :: "bool \<Rightarrow> bool" where "CaseSplit x = x"
lemma [elim!]: "CaseSplit x \<Longrightarrow> (x \<Longrightarrow> C) \<Longrightarrow> C" unfolding CaseSplit_def .

 lemma [elim!]:
  "y = case_prod f x \<Longrightarrow> (\<And>x1 x2. y = f x1 x2 \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of a \<Zinj> b \<Rightarrow> f a b) \<Longrightarrow> (\<And>a b. y = f a b \<Longrightarrow> C (a \<Zinj> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of tag a \<Rightarrow> f a) \<Longrightarrow> (\<And>a. y = f a \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp



subsubsection \<open>Same \<phi>-Type\<close>

definition SameNuTy :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " where "SameNuTy A B = True"
text \<open>Technical tag for reasoner converges \<phi>-types of two typings.\<close>

lemma [\<phi>reason 2000]: "SameNuTy (x \<Ztypecolon> T) (x' \<Ztypecolon> T) "
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy B B' \<Longrightarrow> SameNuTy (A * B) (A' * B')"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "(\<And>x. SameNuTy (A x) (A' x)) \<Longrightarrow> SameNuTy (ExSet A) (ExSet A')"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 1000]: "SameNuTy A A" \<comment> \<open>The fallback\<close>
  unfolding SameNuTy_def ..


subsection \<open>Assertion Level View Shift Reasoning\<close>

text \<open>This is a decision procedure reasoning the entailment between assertions.
  It recognizes \<phi>-Types specifying the same object and reduce the goal of assertion entailment
    to subtyping problems of \<phi>-Types. \<close>

lemmas cast_def = GOAL_CTXT_def FOCUS_TAG_def Imply_def

(* lemma [\<phi>intro0]: "x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * y \<Ztypecolon> Y \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * y\<^sub>m \<Ztypecolon> Y \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * \<blangle> y \<Ztypecolon> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * \<blangle> y\<^sub>m \<Ztypecolon> Y \<brangle> \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Heap_Subty_Goal_def . *)
(* lemma [\<phi>intro0]: "A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B" unfolding SubtyDual_def  by (simp add: cast_id) *)

(* lemma [\<phi>intro 1000]:
  "L * H \<longmapsto> L * H \<^bold>d\<^bold>u\<^bold>a\<^bold>l L * h\<^sub>m \<Ztypecolon> \<blangle> H\<^sub>m \<brangle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s L * h\<^sub>m \<Ztypecolon> H\<^sub>m \<brangle>"
  unfolding Heap_Subty_Goal_def using cast_dual_id . *)

text \<open>Priority Convention:
\<^item> 4000: Termination
\<^item> 3000: Normalization
\<^item> 2000: The framework of step-by-step searching
\<^item> 2100: Prior rules for specific patterns in the step-by-step searching
\<^item> 2300: Termination of the step-by-step searching
\<^item> \<le> 1999: Rules for search specific object like value, variable, etc.
\<close>

subsubsection \<open>Initialization\<close>

lemma (in \<phi>empty) [\<phi>reason 2000]:
  \<open> Simplify assertion_simplification X' X
\<Longrightarrow> Simplify assertion_simplification Y' Y
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> \<blangle> Y' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)\<close>
  unfolding View_Shift_Reasoning_def Simplify_def FOCUS_TAG_def
  by simp

lemma (in \<phi>empty) [\<phi>reason 2100 on \<open>PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?var_Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P)\<close>]:
  \<open>PROP View_Shift_Reasoning (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X)\<close>
  unfolding View_Shift_Reasoning_def using view_shift_id .

subsubsection \<open>Termination\<close>

lemma (in \<phi>empty) [\<phi>reason 4000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?H2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
      "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> H \<brangle>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  and [\<phi>reason 4000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> ?R * \<blangle> ?H2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
      "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> 1 * \<blangle> H \<brangle>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_left FOCUS_TAG_def GOAL_CTXT_def using view_shift_id by this+


context \<phi>empty begin

subsubsection \<open>Void Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 2500 ]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<heavy_comma> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_right .

lemma [\<phi>reason 2500]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> Void \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_right .

subsubsection \<open>Pad Void Holes at left\<close> \<comment> \<open>to standardize\<close>

lemma [\<phi>reason 2500
  if no \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> (?X1 \<heavy_comma> ?X2) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?X1 + ?X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> 1 \<heavy_comma> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_left .

lemma [\<phi>reason 2500
    if no \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?Y1 \<heavy_comma> ?Y2 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?Y1 + ?Y2 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 1 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?X1 + ?X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> 0 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w 1 \<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_left .

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 3000]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3000]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3000]:
  "(Q \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def by (simp add: \<phi>expns) blast


subsubsection \<open>Existential\<close>

lemma [\<phi>reason 3000]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U c \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> ExSet U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def by (simp add: \<phi>expns, metis)

lemma [\<phi>reason 3000]:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w T x \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w ExSet T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def GOAL_CTXT_def
  apply (simp add: \<phi>expns)
  by fastforce

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> VAL x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3100 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?var_X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
                       \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?var_Y \<longmapsto> 0 \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> 0 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def by simp


lemma [\<phi>reason 3000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
                       \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?var_Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def by simp

lemma [\<phi>reason 3000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> 0 \<longmapsto> X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def by simp

lemma [\<phi>reason 3000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0\<heavy_comma> ?R \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0\<heavy_comma> R \<longmapsto> X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def by simp

lemma [\<phi>reason 3000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y + 0 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def by simp

lemma [\<phi>reason 3000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 + Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def by simp

subsubsection \<open>Divergence of Union\<close>

paragraph \<open>Divide Schematic Variable\<close>

definition \<open>ALSTR_Divide_Assertion_U X A B \<equiv> Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w A + B \<longmapsto> X)\<close>

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>PROP ALSTR_Divide_Assertion_U (?var_Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U (A + B) A B\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_id) 

lemma (in \<phi>empty) [\<phi>reason on \<open>PROP ALSTR_Divide_Assertion_U (?Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U A A A\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_id)

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>PROP ALSTR_Divide_Assertion_U (?ZR \<heavy_comma> ?Z1) ?A ?B\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U Z1 A1 B1
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U ZR AR BR
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (ZR \<heavy_comma> Z1) (AR \<heavy_comma> A1) (BR \<heavy_comma> B1)\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (smt (z3) INTERP_COM_plus View_Shift_def distrib_left mult.commute mult.left_commute plus_set_in_iff)

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>PROP ALSTR_Divide_Assertion_U (0::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U 0 0 (0::('FIC_N,'FIC) assn)\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_0)

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>PROP ALSTR_Divide_Assertion_U (ExSet ?Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>(\<And>c. PROP ALSTR_Divide_Assertion_U (Z c) (A c) (B c))
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (ExSet Z) (ExSet A) (ExSet B)\<close>
  for A :: \<open>'c \<Rightarrow> ('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def Imply_def plus_set_def View_Shift_def
  apply (clarsimp simp add: \<phi>expns)
  by (smt (z3) Fic_Space_Un) 

lemma (in \<phi>empty) [\<phi>reason 1200
    on \<open>PROP ALSTR_Divide_Assertion_U (?Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P :: ('FIC_N,'FIC) assn) ?A ?B\<close>
]:
  \<open> PROP ALSTR_Divide_Assertion_U Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (B \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def plus_set_def View_Shift_def
  by (simp add: \<phi>expns) blast

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>PROP ALSTR_Divide_Assertion_U \<blangle> ?Z \<brangle> ?A (?B::('FIC_N,'FIC) assn)\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U \<blangle> Z \<brangle>  \<blangle> A \<brangle>  \<blangle> B \<brangle>\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def plus_set_def by (simp add: \<phi>expns)


paragraph \<open>Main Rules\<close>

lemma [\<phi>reason 3000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A + ?B \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U X XA XB
\<Longrightarrow> SUBGOAL G G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> XB \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> XA \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A + B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<or> P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: View_Shift_def distrib_left)

lemma [\<phi>reason 3000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> (?A + ?B) \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U X XA XB
\<Longrightarrow> SUBGOAL G G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> B \<longmapsto> XB \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> A \<longmapsto> XA \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> A + B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<or> P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: View_Shift_def distrib_left)

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding plus_set_def apply simp
  by (metis plus_set_def view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding plus_set_def apply simp
  by (metis plus_set_def sup_commute view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding cast_def
  by (simp add: distrib_left view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding cast_def
  by (simp add: distrib_left view_shift_union(2)) 

subsubsection \<open>Step-by-Step Searching Procedure\<close>

lemma [\<phi>reason 2000
    on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> \<blangle> ?R2 \<heavy_comma> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
 if no \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> \<blangle> ?R2 \<heavy_comma> FIX ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R  \<longmapsto> R1 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R1 \<longmapsto> \<blangle> R2 \<brangle>     \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R  \<longmapsto> \<blangle> R2 \<heavy_comma> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>view_shift_intro_frame_R \<phi>view_shift_trans) 

lemma [\<phi>reason 2000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?Y \<longmapsto> \<blangle> ?R2 \<heavy_comma> (FIX ?X) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> \<blangle> R2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> \<blangle> R2 \<heavy_comma> FIX X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def pair_forall Fix_def
  by (metis \<phi>view_shift_intro_frame_R \<phi>view_shift_trans mult.commute)

lemma [\<phi>reason 2000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> FIX ?Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> FIX Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def pair_forall Fix_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> ?R2 \<heavy_comma> \<blangle> SYNTHESIS ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> SYNTHESIS X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Synthesis_def .

lemma [\<phi>reason 2000 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> SYNTHESIS ?Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> SYNTHESIS Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2300 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?V \<longmapsto> ?R' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> X \<longmapsto> R \<heavy_comma> \<blangle> X \<brangle> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
      \<comment> \<open>successful termination of the step-by-step search\<close>
  unfolding cast_def pair_forall
  by (simp add: view_shift_id)


subsubsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1500 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?y \<Ztypecolon> Val ?v ?U \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?x \<Ztypecolon> Val ?v' ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> y \<Ztypecolon> Val v U \<longmapsto> R \<heavy_comma> \<blangle> x \<Ztypecolon> Val v T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def pair_forall View_Shift_def
  by (simp add: \<phi>expns times_list_def) metis

lemma [\<phi>reason 1300 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?X \<longmapsto> ?R'''\<heavy_comma> \<blangle> ?x \<Ztypecolon> Val ?v ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R'\<heavy_comma> \<blangle> x \<Ztypecolon> Val v T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> X \<longmapsto> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> Val v T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def pair_forall
  by (smt (verit) \<phi>view_shift_intro_frame_R mult.assoc mult.commute)

subsubsection \<open>General Search\<close>

lemma [\<phi>reason 100 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> H'\<heavy_comma> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> H \<longmapsto> R\<heavy_comma> H'\<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def
  by (simp add: \<phi>view_shift_intro_frame mult.assoc)
  

lemma [\<phi>reason 70 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> H \<longmapsto> R' \<heavy_comma> H \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G "
  unfolding cast_def
  by (simp add: \<phi>view_shift_intro_frame mult.commute mult.left_commute)

lemma [\<phi>reason 10 on \<open>?a \<Zinj> ?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R''' \<heavy_comma> ?a' \<Zinj> ?x' \<Ztypecolon> ?T' \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
   a \<Zinj> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s a' \<Zinj> x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow>
   a \<Zinj> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> a' \<Zinj> x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding cast_def pair_forall by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?x \<Ztypecolon> Val ?v ?V \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    if no \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> Void \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> x \<Ztypecolon> Val v V \<longmapsto> R' \<heavy_comma> x \<Ztypecolon> Val v V \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def
  by (smt (verit, best) \<phi>view_shift_intro_frame_R mult.assoc mult.commute)


(* lemma [\<phi>reason 1200
    on \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "CHK_SUBGOAL G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])
*)

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>

subsubsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> T1 \<heavy_comma> T2 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> (T1 \<heavy_comma> T2) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> X1 \<heavy_comma> X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> (X1 \<heavy_comma> X2) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult.assoc[symmetric] .

end


(*
subsubsection \<open>Other Reasoning Settings\<close>

lemma [\<phi>intro 14000]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a \<Zinj> x' " unfolding Premise_def by simp
(* lemma [\<phi>intro 13500]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a' \<Zinj> x' " unfolding Premise_def by simp *)

(*TODO: this rule is too aggressive. Maybe a assumption based flag switch?*)
lemma [\<phi>intro 13000]: "False \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a' \<Zinj> x' " unfolding Premise_def by simp
  \<comment> \<open>For any other situation (when a is not alpha equivalent to a'), reasoning is pruned early.
  The proof for \<^term>\<open>a = a'\<close> is always assigned to users, because maintaining the consistency of object identities
    is so essential that users should always keep.\<close>
*)


subsection \<open>Structural Pairs\<close> (*depreciated*)

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def .


subsection \<open>Convergence of Branches\<close>

consts branch_convergence :: mode

definition "Merge \<equiv> If"
(*definition "MergeNeg \<equiv> Not"*)

text \<open>This merging procedure always retain the order of the left side.\<close>

subsubsection \<open>Identity\<close>

lemma [\<phi>reason 3000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If ?P ?A ?A'' = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P A A = A"
  unfolding Conv_def using if_cancel ..

lemma [\<phi>reason 3000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P ?A ?A'' = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P A A = A"
  unfolding Conv_def Merge_def using if_cancel ..

subsubsection \<open>Fallback\<close>

lemma [\<phi>reason 10 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If ?P ?A ?B = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P A B = If P A B"
  unfolding Conv_def ..

text \<open>There is no fallback for \<^const>\<open>Merge\<close>. The Merge is not allowed to be fallback.
  If the convergence for Merge fails, the reasoning fails.\<close>

subsubsection \<open>Ad-hoc rules\<close>

lemma [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P ?X ?Y = (?Z::?'a sem_value \<Rightarrow> ?'b)\<close>]:
  \<open> (\<And>ret::'a sem_value. \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (X ret) (Y ret) = Z ret)
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P X Y = Z\<close>
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P x y = z
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (x \<Ztypecolon> T) (y \<Ztypecolon> T) = (z \<Ztypecolon> T) "
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If ?P (?a \<Zinj> ?x) (?b \<Zinj> ?y) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P a b = aa
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P x y = z
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P (a \<Zinj> x) (b \<Zinj> y) = (aa \<Zinj> z)"
  unfolding Conv_def Merge_def by force

lemma (in \<phi>empty) branch_convergence_skip:
  " \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (R1 \<heavy_comma> X) (N \<heavy_comma> Y \<heavy_comma> \<blangle> R2 \<brangle>) = R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (R1 \<heavy_comma> X) (N \<heavy_comma> \<blangle> R2 \<heavy_comma> Y \<brangle>) = R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def Merge_def
  by (simp add: mult.commute mult.left_commute)

(*
lemma [\<phi>reason 3000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P A B = X
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge (MergeNeg (MergeNeg P)) A B = X"
  unfolding MergeNeg_def by simp

lemma [\<phi>reason 2800]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P B A = X
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If (MergeNeg P) A B = X"
  unfolding MergeNeg_def by force
*)

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QL) (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QR) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] If P QL QR = Q
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j QL) (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j QR) = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q)"
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) ?R = ?X\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) R = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longrightarrow> Q)"
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P ?L (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) = ?X\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not>P \<longrightarrow> Q)"
  unfolding Conv_def Merge_def by force

subsubsection \<open>Existential\<close>

lemma Conv_Merge_Ex_both:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L x) (R x) = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (\<exists>* x. L x) (\<exists>* x. R x) = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff \<phi>expns)

lemma Conv_Merge_Ex_R[\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P ?L (\<exists>* x. ?R x) = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (R x) = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P  L (\<exists>* x. R x) = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff \<phi>expns)

lemma [\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (\<exists>* x. ?L x) ?R = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L x) R = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (\<exists>* x. L x) R = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff \<phi>expns)

text \<open>The merging recognize two existential quantifier are identical if their type and variable name
  are the same. If so it uses @{thm Conv_Merge_Ex_both} to merge the quantification,
  or else the right side is expanded first.\<close>

\<phi>reasoner_ML Merge_Existential 2000 (conclusion \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) = ?X\<close>) =
\<open>fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Conv\<close>, _) $
        (Const (\<^const_name>\<open>Merge\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exa,tya,_))
                                          $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exb,tyb,_))))
        = Thm.major_prem_of sequent
    val sequent' = if exa = exb andalso tya = tyb
                   then @{thm Conv_Merge_Ex_both} RS sequent
                   else @{thm Conv_Merge_Ex_R} RS sequent
  in Seq.single (ctxt, sequent')
  end\<close>


subsubsection \<open>Separations Initialization\<close>

lemma (in \<phi>empty) [\<phi>reason 1200
    on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?L1 * ?L2) ?R = ?X\<close>
  if no \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P ?L (?R1\<heavy_comma> \<blangle> ?R2 \<brangle>) = ?X\<close>
]:
  " SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L1\<heavy_comma> L2) (1\<heavy_comma> \<blangle> R \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L1\<heavy_comma> L2) R = X"
  unfolding Conv_def cast_def mult_1_left .

(*TODO*)

subsubsection \<open>Value\<close>

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?x \<Ztypecolon> Val ?v ?T) (?y \<Ztypecolon> Val ?v' ?U) = ?X\<close>]: 
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (x \<Ztypecolon> T) (y \<Ztypecolon> U) = (z \<Ztypecolon> Z)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (x \<Ztypecolon> Val v T) (y \<Ztypecolon> Val v U) = (z \<Ztypecolon> Val v Z)"
  unfolding Conv_def cast_def Merge_def set_eq_iff by (simp add: \<phi>expns)

lemma (in \<phi>empty) [\<phi>reason 1200 on
  \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?R1 \<heavy_comma> ?x \<Ztypecolon> Val ?v ?T) (?N \<heavy_comma> \<blangle> ?R2 \<heavy_comma> ?y \<Ztypecolon> Val ?v' ?U \<brangle>) = ?X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (x \<Ztypecolon> T) (y \<Ztypecolon> U) = (z \<Ztypecolon> Z)
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P R1 (1 \<heavy_comma> \<blangle> N \<heavy_comma> R2 \<brangle>) = R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (R1 \<heavy_comma> x \<Ztypecolon> Val v T) (N \<heavy_comma> \<blangle> R2 \<heavy_comma> y \<Ztypecolon> Val v U \<brangle>) = (R \<heavy_comma> z \<Ztypecolon> Val v Z) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def Merge_def by (simp add: \<phi>expns)

declare (in \<phi>empty) branch_convergence_skip[\<phi>reason 1200
     on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?R1 \<heavy_comma> ?x \<Ztypecolon> Val ?v ?T) (?N \<heavy_comma> \<blangle> ?R2 \<heavy_comma> ?Y \<brangle>) = ?R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  if no \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P (?R1 \<heavy_comma> ?x \<Ztypecolon> Val ?v ?T) (?N \<heavy_comma> \<blangle> ?R2 \<heavy_comma> ?y \<Ztypecolon> Val ?v' ?U \<brangle>) = ?R \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?rG\<close>
]

subsubsection \<open>Object\<close>

definition EqualAddress :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool "
  where "EqualAddress _ _ = True"

lemma [\<phi>reason]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a1 = a2
   \<Longrightarrow> EqualAddress (a1 \<Zinj> x1 \<Ztypecolon> T1) (a2 \<Zinj> x2 \<Ztypecolon> T2) "
  unfolding EqualAddress_def ..

subsubsection \<open>Unfold\<close>

lemma (in \<phi>empty) [\<phi>reason 2000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> R \<heavy_comma> R1 \<heavy_comma> R2 \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> R \<heavy_comma> (R1 \<heavy_comma> R2) \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def by (metis mult.assoc)

lemma (in \<phi>empty) [\<phi>reason 2000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L1 \<heavy_comma> L2 \<heavy_comma> L3) R = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L1 \<heavy_comma> (L2 \<heavy_comma> L3)) R = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def by (metis mult.assoc)

lemma (in \<phi>empty) [\<phi>reason 2200]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> R1 \<heavy_comma> R2 \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> 1 \<heavy_comma> (R1 \<heavy_comma> R2) \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def by force


subsubsection \<open>Padding Void\<close>

lemma (in \<phi>empty) [\<phi>reason 2000]:
  " \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (1 \<heavy_comma> x \<Ztypecolon> T) R = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (x \<Ztypecolon> T) R = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def by force

lemma (in \<phi>empty) [\<phi>reason 2000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> 1 \<heavy_comma> y \<Ztypecolon> U \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> y \<Ztypecolon> U \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def by force


subsubsection \<open>Eliminate Void Hole\<close>

lemma (in \<phi>empty) [\<phi>reason 2000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> R \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L (N \<heavy_comma> \<blangle> R \<heavy_comma> 1 \<brangle>) = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def by force

lemma (in \<phi>empty) [\<phi>reason 2000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P L R = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P (L \<heavy_comma> 1) R = X \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def by force

subsubsection \<open>Termination\<close>

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge ?P 1 (1 \<heavy_comma> \<blangle> 1 \<brangle>) = ?X'' \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v[branch_convergence] Merge P 1 (1 \<heavy_comma> \<blangle> 1 \<brangle>) = 1 \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Conv_def cast_def Merge_def by force
  



(* subsection \<open>Program Interface\<close> \<comment> \<open>Interfaces exported to target LLVM module\<close>

definition Prog_Interface :: " label \<Rightarrow> 'a itself \<Rightarrow> 'b itself \<Rightarrow> ('a::lrep  \<longmapsto> 'b::lrep) \<Rightarrow> bool"
  where "Prog_Interface _ args rets proc \<longleftrightarrow> True"

lemma Prog_Interface_proc: "TERM proc \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) proc" 
  unfolding Prog_Interface_def ..

lemma Prog_Interface_func:
  "TERM f \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) f" 
  unfolding Prog_Interface_def ..
*)

subsection \<open>Filter Out Values\<close>

text (in \<phi>empty) \<open>Given an assertion X, antecedent \<^term>\<open>Filter_Out_Values X X'\<close> returns X' where
  all value assertions \<^term>\<open>x \<Ztypecolon> Val raw T\<close> are filtered out.

  It is typically used in exception. When a computation triggers an exception at state X,
    the state recorded in the exception is exactly X' where value assertions are filtered out.\<close>

definition \<open>Filter_Out_Values'' \<equiv> Filter_Out_Values\<close>
definition \<open>Filter_Out_Values' (remain::'a::times set) (keep::'a set) (check::'a set) (ret::'a set)
              \<equiv> Trueprop (keep = check \<longrightarrow> (remain * keep \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ret))\<close>

lemma [\<phi>reason on \<open>PROP Filter_Out_Values ?X ?Z\<close>]:
  \<open> Simplify assertion_simplification X' X
\<Longrightarrow> PROP Filter_Out_Values'' X' Z
\<Longrightarrow> PROP Filter_Out_Values X Z\<close>
  unfolding Filter_Out_Values''_def Simplify_def by simp

lemma [\<phi>reason on \<open>PROP Filter_Out_Values ?var_X ?Z\<close>]:
  \<open>PROP Filter_Out_Values X X\<close>
  unfolding Filter_Out_Values_def using cast_id .

lemma [\<phi>reason 1200 on \<open>PROP Filter_Out_Values'' (ExSet ?T) ?T'\<close>]:
  \<open>(\<And>c. PROP Filter_Out_Values'' (T c) (T' c))
\<Longrightarrow> PROP Filter_Out_Values'' (ExSet T) (ExSet T')\<close>
  unfolding Filter_Out_Values_def Filter_Out_Values''_def Imply_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200 on \<open>PROP Filter_Out_Values'' (?T \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P) ?T'\<close>]:
  \<open> PROP Filter_Out_Values'' T T'
\<Longrightarrow> PROP Filter_Out_Values'' (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding Filter_Out_Values_def Imply_def Filter_Out_Values''_def
  by (simp add: \<phi>expns)

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>PROP Filter_Out_Values'' (?R\<heavy_comma> ?X) ?Z\<close>]:
  \<open> PROP Filter_Out_Values'' R R'
\<Longrightarrow> PROP Filter_Out_Values' R' X X Z
\<Longrightarrow> PROP Filter_Out_Values'' (R\<heavy_comma> X) Z\<close>
  unfolding Filter_Out_Values_def Imply_def Filter_Out_Values'_def Filter_Out_Values''_def
  by (simp add: \<phi>expns) blast

lemma (in \<phi>empty) [\<phi>reason 1100 on \<open>PROP Filter_Out_Values'' ?R ?Z\<close>]:
  \<open> PROP Filter_Out_Values' Void R R Z
\<Longrightarrow> PROP Filter_Out_Values'' R Z\<close>
  unfolding Filter_Out_Values_def Filter_Out_Values'_def Imply_def Filter_Out_Values''_def
  by simp

lemma [\<phi>reason 1200 on \<open>PROP Filter_Out_Values' ?R ?Y (SYNTHESIS ?X) ?Z\<close>]:
  \<open> PROP Filter_Out_Values' R Y X Z
\<Longrightarrow> PROP Filter_Out_Values' R Y (SYNTHESIS X) Z\<close>
  unfolding Filter_Out_Values'_def Synthesis_def .

lemma [\<phi>reason 1200 on \<open>PROP Filter_Out_Values' ?R ?Y (FIX ?X) ?Z\<close>]:
  \<open> PROP Filter_Out_Values' R Y X Z
\<Longrightarrow> PROP Filter_Out_Values' R Y (FIX X) Z\<close>
  unfolding Filter_Out_Values'_def Fix_def .

lemma (in \<phi>empty) [\<phi>reason 1200 on \<open>PROP Filter_Out_Values' ?R ?Y (?x \<Ztypecolon> Val ?raw ?T) ?Z\<close>]:
  \<open>PROP Filter_Out_Values' R Y (x \<Ztypecolon> Val raw T) R\<close>
  unfolding Filter_Out_Values'_def Imply_def by (simp add: \<phi>expns)

lemma (in \<phi>empty) [\<phi>reason 1100 on \<open>PROP Filter_Out_Values' Void ?Y ?X ?Z\<close>]:
  \<open>PROP Filter_Out_Values' Void Y X Y\<close>
  unfolding Filter_Out_Values'_def Imply_def by simp

lemma (in \<phi>empty) [\<phi>reason 1080 on \<open>PROP Filter_Out_Values' ?R ?Y ?X ?Z\<close>]:
  \<open>PROP Filter_Out_Values' R Y X (R\<heavy_comma> Y)\<close>
  unfolding Filter_Out_Values'_def Imply_def by simp



subsection \<open>Variable Extraction\<close>

definition Variant_Cast :: "'vars \<Rightarrow> 'a set \<Rightarrow> ('vars \<Rightarrow> 'a set) \<Rightarrow> bool" ("\<^bold>v\<^bold>a\<^bold>r\<^bold>y _ \<^bold>i\<^bold>n _/ \<longmapsto> _" )
  where "Variant_Cast insts X X' \<longleftrightarrow> X = X' insts"

text \<open>The main usage of this reasoning is for loop and recursion.
  Given an assertion X, \<^prop>\<open>Variant_Cast vars X X'\<close> tries under instruction from user to
    extract the variable part \<^term>\<open>vars\<close> in the assertion. This part typically will be
    universally quantified inside loop bodies.

  There are two syntax for instructing this extraction.
  One is 'v1 v2 ...' instructing all occurrence of free variables v1 v2... in X will be such generalized.
  Another is 'v1 v2 in pattern' instructing to first pattern match X and then v1 v2 in the matched
    pattern will be generalized.\<close>

lemma Variant_Cast_I: "X = X' vars \<Longrightarrow> Variant_Cast vars X X' "
  unfolding Variant_Cast_def by auto

lemma Variant_Cast_I_always:
  "X = X' vars \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e always vars \<Longrightarrow>
  Variant_Cast vars X (\<lambda>vars. X' vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j always vars)"
  unfolding Variant_Cast_def by (auto simp add: \<phi>expns)

lemma case_prod_expn_I: "A = B x y \<Longrightarrow> A = case_prod B (x,y)" by simp
lemma case_named_expn_I: "A = B x \<Longrightarrow> A = case_named B (tag x)" by simp

ML_file_debug \<open>library/variables_tag.ML\<close>

\<phi>processor vars_by_pattern 3000 (\<open>Variant_Cast ?vars ?X ?X' \<Longrightarrow> PROP ?P\<close>)
\<open>fn (ctxt, sequent) => 
let open Parse Scan NuHelp NuBasics
  fun pattern_match ((vars, pattern), always) _ =
    (ctxt, Nu_Variable_Factor.vary_by_pattern vars pattern always ctxt sequent)
  fun var_term (vars, always) _ =
    (ctxt, Nu_Variable_Factor.vary_by_parts vars always ctxt sequent)
  val none = Scan.succeed []
  val params = (list Parse.params) >> flat
  val syn_pattern_match =
    (params --| \<^keyword>\<open>in\<close> -- term -- option (\<^keyword>\<open>invar\<close> |-- term))
    >> pattern_match
  val syn_var_term = (list1 term -- Scan.option (\<^keyword>\<open>invar\<close> |-- term)) >> var_term
in syn_pattern_match || syn_var_term end\<close>

(*  \<open>Nu_Reasoners.wrap (fn ctxt => Nu_Reasoners.asm_simp_tac (ctxt addsimps Proof_Context.get_thms ctxt "\<phi>expns"))\<close> *)


subsection \<open>Share\<close>

definition \<Phi>Share :: \<open>(rat \<Rightarrow> 'a::share set) \<Rightarrow> bool\<close>
  where \<open>\<Phi>Share S \<longleftrightarrow> (\<forall>v m n. v \<in> S m \<longrightarrow> 0 < n \<longrightarrow> share n v \<in> S (n * m))\<close>




subsection \<open>Actions\<close>

subsubsection \<open>Share\<close>

consts \<A>\<c>\<t>\<i>\<o>\<n>_share :: action

lemma share_\<phi>app:
  \<open>PROP ACTION (Action_VS \<A>\<c>\<t>\<i>\<o>\<n>_share)\<close>
  using ACTION_I . 





section \<open>Tools for Constructing Semantic Instructions and for Reasoning them\<close>

subsection \<open>Definitions of Elementary Constructions\<close>

context \<phi>empty_sem begin

definition \<phi>M_assert :: \<open>bool \<Rightarrow> (unit,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_assert P = (\<lambda>s. if P then Return \<phi>V_none s else {Invalid})\<close>

definition \<phi>M_assume :: \<open>bool \<Rightarrow> (unit,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_assume P = (\<lambda>s. if P then Return \<phi>V_none s else {PartialCorrect})\<close>

definition \<phi>M_getV :: \<open>'TY \<Rightarrow> ('VAL \<Rightarrow> 'v) \<Rightarrow> 'VAL sem_value \<Rightarrow> ('v \<Rightarrow> ('y,'RES_N,'RES) proc) \<Rightarrow> ('y,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV TY VDT_dest v F =
    (\<phi>M_assert (dest_sem_value v \<in> Well_Type TY) \<ggreater> F (VDT_dest (dest_sem_value v)))\<close>

definition \<phi>M_caseV :: \<open>('VAL sem_value \<Rightarrow> ('vr,'ret,'RES_N,'RES) proc') \<Rightarrow> ('VAL \<times> 'vr,'ret,'RES_N,'RES) proc'\<close>
  where \<open>\<phi>M_caseV F = (\<lambda>arg. case arg of sem_value (a1,a2) \<Rightarrow> F (sem_value a1) (sem_value a2))\<close>

end

subsection \<open>Reasoning for Elementary Constructions\<close>

context \<phi>empty begin

declare \<phi>SEQ[\<phi>reason!]

lemma \<phi>M_assert[\<phi>reason! on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_assert ?P \<lbrace> ?A \<longmapsto> ?B \<rbrace>\<close>]:
  \<open>(Inhabited X \<Longrightarrow> P) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_assert P \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_assert_def Return_def det_lift_def
  by (clarsimp simp add: \<phi>expns Inhabited_def, blast)

lemma \<phi>M_assert_True[simp]:
  \<open>\<phi>M_assert True = Return \<phi>V_none\<close>
  unfolding \<phi>M_assert_def by simp

lemma \<phi>M_assert':
  \<open>P \<Longrightarrow> Q (F args) \<Longrightarrow> Q ((\<phi>M_assert P \<ggreater> F) args)\<close>
  unfolding \<phi>M_assert_def bind_def Return_def det_lift_def by simp

lemma \<phi>M_assume[\<phi>reason!]:
  \<open>(P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (\<phi>M_assume P \<ggreater> F) \<lbrace> X \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_assume_def bind_def Return_def det_lift_def
  by clarsimp

lemma throw_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c det_lift Exception \<lbrace> X \<longmapsto> \<lambda>_. 0 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s X \<rbrace>\<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def
  by clarsimp

lemma \<phi>M_tail_left:  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_tail_right: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. 1 \<heavy_comma> Y v \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_tail_right_right: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. Y v\<heavy_comma> 1 \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_detail_left[\<phi>reason 2200000]:  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_detail_right[\<phi>reason 2200000]: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. 1\<heavy_comma> Y v \<rbrace>\<close> by simp


lemma \<phi>M_getV[\<phi>reason!]:
   \<open>(v \<in> (x \<Ztypecolon> A) \<Longrightarrow> <\<phi>expn> v \<in> Well_Type TY)
\<Longrightarrow> \<r>Cut
\<Longrightarrow> (v \<in> (x \<Ztypecolon> A) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV TY VDT_dest (sem_value v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (sem_value v) A \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_def Premise_def
  by (clarsimp simp add: \<phi>expns)

declare \<phi>M_getV[where X=1, simplified, \<phi>reason!]

lemma \<phi>M_caseV[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F va vb \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_caseV F (\<phi>V_pair va vb) \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_caseV_def \<phi>V_pair_def by simp

lemma \<phi>M_Success[\<phi>reason!]:
  \<open> <\<phi>expn> v \<in> (y \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return (sem_value v) \<lbrace> X \<longmapsto> \<lambda>u. X\<heavy_comma> y \<Ztypecolon> Val u T \<rbrace> \<close>
  unfolding \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: \<phi>expns)

declare \<phi>M_Success[where X=1, simplified, \<phi>reason!]

lemma \<phi>M_Success'[\<phi>reason 1100000 on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> ?X \<longmapsto> ?X' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace> \<close>
  unfolding Return_def \<phi>Procedure_def det_lift_def by (clarsimp simp add: \<phi>expns)

end


subsection \<open>Elementary Constructions for Reasoning underlying Fictional Separation Logic\<close>

definition (in \<phi>resource_sem) \<phi>Res_Spec :: \<open>('RES_N, 'RES) assn \<Rightarrow> ('RES_N, 'RES) assn\<close>
  where \<open>\<phi>Res_Spec P = (Valid_Resource \<inter> P)\<close>

lemma (in \<phi>resource_sem)[simp]:
  \<open>\<phi>Res_Spec {} = {}\<close>
  \<open>\<phi>Res_Spec 0 = {}\<close>
  unfolding \<phi>Res_Spec_def by (simp add: zero_set_def)+

lemma (in \<phi>fiction) \<phi>INTERP_RES_\<phi>Res_Spec:
  \<open>res \<in> INTERP_RES fic \<longleftrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP fic) \<and> Fic_Space fic\<close>
  unfolding INTERP_RES_def \<phi>Res_Spec_def by (simp, blast)

lemma (in \<phi>fiction) \<phi>Procedure_\<phi>Res_Spec:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<longleftrightarrow> (\<forall>r res. res \<in> \<phi>Res_Spec (\<I> INTERP (r * p) \<^bold>s\<^bold>u\<^bold>b\<^bold>j p. p \<in> P \<and> Fic_Space (r * p))
      \<longrightarrow> f res \<subseteq> \<S> (\<lambda>v. \<phi>Res_Spec (\<I> INTERP (r * q) \<^bold>s\<^bold>u\<^bold>b\<^bold>j q. q \<in> Q v \<and> Fic_Space (r * q)))
                    (\<phi>Res_Spec (\<I> INTERP (r * e) \<^bold>s\<^bold>u\<^bold>b\<^bold>j e. e \<in> E \<and> Fic_Space (r * e))))\<close>
  apply rule
   apply (unfold \<phi>Procedure_alt INTERP_COM \<phi>Res_Spec_def subset_iff)
   apply (clarsimp simp add: times_set_def \<phi>expns INTERP_RES_def)
  subgoal premises prems for r res s c proof-
    have t1: \<open>(\<exists>fic. (\<exists>y. fic = r * y \<and> y \<in> P) \<and> res \<in> Valid_Resource \<and> Fic_Space fic \<and> res \<in> \<I> INTERP fic)\<close>
      using Fic_Space_Un prems by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=res], THEN spec[where x=r], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> f res\<close>])
      apply (cases s; clarsimp simp add: \<phi>expns INTERP_RES_def)
      apply force
      using Fic_Space_Un by blast
  qed
  apply (clarsimp simp add: times_set_def \<phi>expns INTERP_RES_def)
  subgoal premises prems for res r s c proof-
    have t1: \<open>res \<in> Valid_Resource \<and> (\<exists>c. res \<in> \<I> INTERP (r * c) \<and> c \<in> P \<and> Fic_Space r \<and> Fic_Space c)\<close>
      using prems by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=r], THEN spec[where x=res], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> _\<close>])
      apply (cases s; simp add: \<phi>expns INTERP_RES_def)
      using Fic_Space_Un apply blast
      using Fic_Space_Un by blast
  qed .


lemma (in \<phi>resource_sem) \<phi>Res_Spec_subj[iff]:
  \<open> \<phi>Res_Spec (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (\<phi>Res_Spec S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<close>
  unfolding \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma (in \<phi>resource_sem) \<phi>Res_Spec_subj_\<S>:
  \<open> P
\<Longrightarrow> res \<subseteq> \<S> S E
\<Longrightarrow> res \<subseteq> (\<S> (\<lambda>v. S v \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) E)\<close>
  by (clarsimp simp add: \<phi>expns set_eq_iff)

lemma (in \<phi>resource_sem) \<phi>Res_Spec_ex[iff]:
  \<open> \<phi>Res_Spec (ExSet S) = (\<exists>*x. \<phi>Res_Spec (S x))\<close>
  unfolding \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma (in \<phi>resource_sem) \<phi>Res_Spec_ex_\<S>:
  \<open> res \<subseteq> \<S> (S x) E
\<Longrightarrow> res \<subseteq> (\<S> (\<lambda>v. (\<exists>*x. S x v)) E)\<close>
  apply (clarsimp simp add: \<phi>expns set_eq_iff subset_iff)
  subgoal for x by (cases x; clarsimp simp add: \<phi>expns set_eq_iff subset_iff; blast) .


paragraph \<open>Weakest Precondition Transformer for \<phi>Res_Spec\<close>

lemma (in \<phi>resource_sem) \<phi>M_RS_WP_SEQ[\<phi>reason!]:
  \<open> F res \<subseteq> \<S> P E
\<Longrightarrow> (\<And>ret res. res \<in> P ret \<Longrightarrow> G ret res \<subseteq> \<S> Q E)
\<Longrightarrow> (F \<bind> G) res \<subseteq> \<S> Q E\<close>
  unfolding bind_def subset_iff
  apply clarsimp subgoal for s s'
    by (cases s'; simp; cases s; clarsimp ; blast) .


section \<open>Predefined Resource Snippet\<close>

subsection \<open>Minimal Resource\<close>

locale resource =
  Fictional_Algebra.project_inject entry
+ \<phi>resource_sem Resource_Validator
for entry :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, 'T::comm_monoid_mult) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
+ fixes Valid :: \<open>'T set\<close>
  assumes Valid_1: \<open>1 \<in> Valid\<close>
  assumes Resource_Validator[simp]: \<open>Resource_Validator name = inject ` Valid\<close>
begin

lemma \<r>_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    clean res \<in> Valid_Resource \<and> (\<exists>m. res name = inject m \<and> m \<in> Valid)\<close>
  by (subst split, simp add: Valid_Resource_def times_fun_def image_iff Valid_1 one_fine_def, blast)

lemma \<r>_valid_split': \<open>NO_MATCH (clean res') res \<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow>
    clean res \<in> Valid_Resource \<and> (\<exists>m. res name = inject m \<and> m \<in> Valid)\<close>
  using \<r>_valid_split .

lemma get_res_valid:
  \<open> res \<in> Valid_Resource
\<Longrightarrow> get res \<in> Valid\<close>
  unfolding Valid_Resource_def
  apply simp
  subgoal premises prems
    using prems(1)[THEN spec[where x=name], simplified Resource_Validator]
    by fastforce .

definition \<open>raw_fiction I = Fiction (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x })\<close>
lemma raw_fiction_\<I>:
  "\<I> (raw_fiction I) = (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x})"
  unfolding raw_fiction_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def one_fine_def)

lemma raw_fiction_itself_expn[\<phi>expns]:
  \<open>\<phi>Res_Spec (R * \<I> (raw_fiction fiction.it) x)
 = \<phi>Res_Spec (R * {mk x})\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  by (clarsimp simp add: \<phi>expns raw_fiction_\<I>)

lemma get_res_Valid:
  \<open> res \<in> \<phi>Res_Spec S
\<Longrightarrow> (get res) \<in> Valid\<close>
  unfolding \<phi>Res_Spec_def by (clarsimp simp add: \<r>_valid_split')


definition \<open>raw_basic_fiction I = Fiction (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x })\<close>
lemma raw_basic_fiction_\<I>:
  "\<I> (raw_basic_fiction I) = (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x})"
  unfolding raw_basic_fiction_def
  by (rule Fiction_inverse) (clarsimp simp add: Fictional_def one_set_def one_fine_def)


end


subsection \<open>Resources using Fine\<close>

subsubsection \<open>Locale for Resource\<close>

locale fine_resource =
  Fictional_Algebra.project_inject entry
+ \<phi>resource_sem Resource_Validator
for entry :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, 'T::sep_algebra ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
+ fixes Valid :: \<open>'T set\<close>
  assumes Valid_1[simp]: \<open>1 \<in> Valid\<close>
  assumes Resource_Validator[simp]: \<open>Resource_Validator name = inject ` Fine ` Valid\<close>
begin

sublocale resource entry Resource_Validator \<open>Fine ` Valid\<close>
  by (standard; simp add: image_iff one_fine_def)

lemma get_res_Valid:
  \<open> res \<in> \<phi>Res_Spec S
\<Longrightarrow> !!(get res) \<in> Valid\<close>
  unfolding \<phi>Res_Spec_def by (clarsimp simp add: \<r>_valid_split')

subsubsection \<open>Basic Fine Fiction\<close>

definition \<open>basic_fine_fiction I = Fiction (\<lambda>x. { 1(entry #= Fine y) |y. y \<in> \<I> I x })\<close>
lemma basic_fine_fiction_\<I>:
  "\<I> (basic_fine_fiction I) = (\<lambda>x. { 1(entry #= Fine y) |y. y \<in> \<I> I x})"
  unfolding basic_fine_fiction_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def one_fine_def)

subsubsection \<open>Identity Fiction\<close>

lemma fine_fiction_itself_expn[\<phi>expns]:
  \<open>\<phi>Res_Spec (R * \<I> (basic_fine_fiction (fiction.fine fiction.it)) (R2 * Fine x))
 = \<phi>Res_Spec (R * \<I> (basic_fine_fiction (fiction.fine fiction.it)) R2 * {mk (Fine x)})\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: \<phi>expns basic_fine_fiction_\<I> mult_strip_fine_011 )
  apply (rule; clarify)
  apply (metis fun_mult_norm mk_homo_mult times_fine')
  by (smt (verit, del_insts) fun_mult_norm fun_upd_same get_homo_mult get_res_valid image_iff mk_homo_mult mult_strip_fine_111 proj_inj times_fine(1) times_fine(3))

end

subsubsection \<open>Basic Locale for Fiction of Fine Resource\<close>

locale basic_fiction_for_fine_resource =
  \<phi>fiction Resource_Validator INTERPRET
+  R: fine_resource Res Resource_Validator Valid
+  fictional_project_inject INTERPRET Fic \<open>R.basic_fine_fiction (fiction.fine I)\<close>
for Valid :: "'T::sep_algebra set"
and I :: "('U::sep_algebra, 'T) fiction"
and Res :: "('RES_N, 'RES::{comm_monoid_mult,no_inverse}, 'T ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
and Fic :: "('FIC_N,'FIC::{no_inverse,comm_monoid_mult},'U ?) Fictional_Algebra.Entry"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{no_inverse,comm_monoid_mult},'RES_N \<Rightarrow> 'RES) fiction"
begin

lemma fiction_undef_bottom[simp]:
  \<open>INTERP_RES (u * mk Undef) = {}\<close>
  unfolding set_eq_iff INTERP_RES_def
  by (simp add: interp_split' R.basic_fine_fiction_\<I> times_fine)

paragraph \<open>\<phi>-Type\<close>

definition \<phi> :: \<open>('U, 'x) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'x) \<phi>\<close>
    \<comment> \<open>\<phi>Type for level-1 mapping\<close>
  where \<open>\<phi> T x = { mk (Fine f) |f. f \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>f. p = mk (Fine f) \<and> f \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>_def by simp

lemma \<phi>_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)


end


subsubsection \<open>Permission Fiction\<close>

locale permission_fiction =
  \<phi>fiction Resource_Validator INTERPRET
+  R: fine_resource Res Resource_Validator Valid
+  share: perm_transformer perm_transformer
+  fictional_project_inject INTERPRET Fic
      \<open>R.basic_fine_fiction (fiction.fine (fic_functional perm_transformer))\<close>
for Valid :: "'T::sep_algebra set"
and perm_transformer :: \<open>'T \<Rightarrow> 'U::{share_sep_disj,share_module_sep,sep_algebra}\<close>
and Res :: "('RES_N, 'RES::{comm_monoid_mult,no_inverse}, 'T ?) Fictional_Algebra.Entry"
and Resource_Validator :: "'RES_N \<Rightarrow> 'RES set"
and Fic :: "('FIC_N, 'FIC::{comm_monoid_mult,no_inverse}, 'U ?) Fictional_Algebra.Entry"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC, 'RES_N \<Rightarrow> 'RES) fiction"
begin

sublocale basic_fiction_for_fine_resource Valid \<open>fic_functional perm_transformer\<close> ..

lemma expand_raw:
  \<open>Fic_Space r
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine (perm_transformer x))))
  = \<phi>Res_Spec (\<I> INTERP r * { R.mk (Fine x)})\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: R.basic_fine_fiction_\<I> \<phi>expns
            share.sep_mult_strip_011 \<phi>Res_Spec_def R.\<r>_valid_split'
            R.mult_strip_inject_011 interp_split' mult_strip_fine_011)

  subgoal for res_r a r
    apply (rule exI[where x=\<open>res_r * R.mk (Fine a)\<close>])
    by (metis R.mk_homo_mult fun_mult_norm times_fine(1))

  subgoal premises prems for res_r y a proof -
    have t1[simp]: \<open>y ## x\<close>
      by (metis prems(7) prems(8) sep_disj_commute sep_disj_multD1 sep_mult_ac(2))
    show ?thesis
      apply (rule exI[where x=\<open>res_r\<close>], rule exI[where x=\<open>R.mk (Fine (y * x))\<close>])
      by (metis R.mk_homo_mult share.homo_mult fun_mult_norm prems(4) t1 times_fine')
  qed .

lemma partial_implies_raw:
  \<open> Fic_Space r
\<Longrightarrow> 0 < n \<and> n \<le> 1
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine (share n (perm_transformer x)))))
\<Longrightarrow> \<exists>objs. R.get res = Fine objs \<and> x \<preceq>\<^sub>S\<^sub>L objs\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: R.basic_fine_fiction_\<I> \<phi>expns
            mult_strip_fine_011 \<phi>Res_Spec_def R.\<r>_valid_split' R.mult_strip_inject_011
            R.proj_homo_mult interp_split')
  by (metis join_sub_def join_sub_ext_left share.join_sub_share_join_sub_whole)



lemma VS_merge_ownership:
  \<open> (\<forall>ua ub. ua \<in> (x \<Ztypecolon> T) \<and> ub \<in> (x \<Ztypecolon> T) \<and>
             can_share (perm_transformer ua) \<and> can_share (perm_transformer ub) \<and>
             share na (perm_transformer ua) ## share nb (perm_transformer ub) \<longrightarrow> ua = ub)
\<Longrightarrow> na + nb \<le> 1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> na T) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb T) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> (na + nb) T)\<close>
  unfolding View_Shift_def Premise_def
  apply (clarsimp simp add: \<phi>expns mult.assoc mk_homo_mult[symmetric] times_fine)
  subgoal for res R res_r res_xa res_xb
    apply (cases \<open>share na (perm_transformer res_xa) ## share nb (perm_transformer res_xb)\<close>;
           clarsimp simp add: fun_1upd_homo \<phi>INTERP_RES_\<phi>Res_Spec share_left_distrib)
    apply (rule exI[where x=\<open>res_r * mk (Fine (share (na + nb) (perm_transformer res_xb)))\<close>], simp)
    by (metis share_sep_left_distrib_0) .

lemma VS_split_ownership:
  \<open> (\<forall>u. u \<in> (x \<Ztypecolon> T) \<and> can_share (perm_transformer u) \<and> 0 < n \<and> na + nb \<le> 1
     \<longrightarrow> share na (perm_transformer u) ## share nb (perm_transformer u))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (0 < n \<longrightarrow> na + nb = n \<and> 0 < na \<and> 0 < nb)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> n T) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> na T) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb T)\<close>
  unfolding View_Shift_def Premise_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for res R res_r res_x
    apply (rule exI[where x=\<open>res_r * (mk (Fine (share na (perm_transformer res_x)))
                                    * mk (Fine (share nb (perm_transformer res_x))))\<close>],
           rule conjI, blast)
    by (clarsimp simp add: mk_homo_mult[symmetric] times_fine fun_1upd_homo share_sep_left_distrib_0) .
end

(* locale permission_fiction =
  \<phi>fiction Resource_Validator INTERPRET
+  R: resource Res Resource_Validator Valid
+  fictional_project_inject INTERPRET Fic \<open>R.raw_basic_fiction I\<close>
for Valid :: "'T::comm_monoid_mult set"
and I :: "('U::{share,comm_monoid_mult}, 'T) fiction"
and Res :: "('RES_N, 'RES::{comm_monoid_mult,no_inverse}, 'T) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
and Fic :: "('FIC_N,'FIC::{no_inverse,comm_monoid_mult},'U) Fictional_Algebra.Entry"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{no_inverse,comm_monoid_mult},'RES_N \<Rightarrow> 'RES) fiction"
+
fixes perm_transformer :: \<open>'T \<Rightarrow> 'U\<close>
  and R_dom :: \<open>'T set\<close>
assumes \<open>Fic_Space r
\<Longrightarrow> x \<in> R_dom
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_transformer x)))
  = \<phi>Res_Spec (\<I> INTERP r * { R.mk x})\<close>

begin


end *)




subsubsection \<open>Identity Fiction\<close>

locale identity_fiction_for_fine_resource =
   \<phi>fiction Resource_Validator INTERPRET
+  R: fine_resource Res Resource_Validator
+  fictional_project_inject INTERPRET Fic \<open>R.basic_fine_fiction (fiction.fine fiction.it)\<close>
for Res :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, ('T::sep_algebra) ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{no_inverse,comm_monoid_mult},'RES_N \<Rightarrow> 'RES) fiction"
and Fic :: "('FIC_N,'FIC,'T ?) Fictional_Algebra.Entry"
begin

sublocale basic_fiction_for_fine_resource where I = \<open>fiction.it\<close> ..

lemma expand:
  \<open> Fic_Space r
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine x))) = \<phi>Res_Spec (\<I> INTERP r * {R.mk (Fine x)})\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify; rule; clarsimp simp add: \<phi>expns R.basic_fine_fiction_\<I> mult_strip_fine_011
          interp_split')
  apply (metis R.inj_homo_mult fun_1upd_homo_left1 fun_mult_norm times_fine')
  apply (clarsimp simp add: R.mk_homo_mult[symmetric] mult.assoc)
  subgoal premises prems for ua y proof -
    have t1: \<open>y ## x\<close>
      by (smt (verit) R.get_homo_mult R.get_res_valid R.project_inject_axioms fun_upd_same image_iff mult_strip_fine_111 prems(2) project_inject.proj_inj times_fine(1) times_fine(3))
    show ?thesis
      by (metis prems(3) t1 times_fine(1))
  qed .

end


subsection \<open>Nonsepable Mono-Resource\<close>
  \<comment> \<open>The resource non-sepable and having type shape \<^typ>\<open>'a::nonsepable_semigroup option ?\<close>\<close>

locale nonsepable_mono_resource =
  fine_resource entry Resource_Validator \<open>{None} \<union> Some ` nonsepable ` Valid\<close>
for entry :: "('RES_N, 'RES::{comm_monoid_mult,no_inverse}, 'T nonsepable option ?) Fictional_Algebra.Entry"
and Resource_Validator :: "'RES_N \<Rightarrow> 'RES set"
and Valid :: "'T set"
begin

definition fiction_agree
  where \<open>fiction_agree = basic_fine_fiction (fiction.fine (fiction.optionwise Fictional_Algebra.fiction_agree))\<close>

end


subsubsection \<open>Fiction Agreement\<close>

locale agreement_fiction_for_nosepable_mono_resource =
   \<phi>fiction Resource_Validator INTERPRET
+  R: nonsepable_mono_resource Res Resource_Validator Valid
+  fictional_project_inject INTERPRET Fic \<open>R.fiction_agree\<close>
for Valid :: "'T set"
and Res :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, 'T nonsepable option ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{no_inverse,comm_monoid_mult},'RES_N \<Rightarrow> 'RES) fiction"
and Fic :: "('FIC_N,'FIC, 'T nonsepable agree option ?) Fictional_Algebra.Entry"
begin

sublocale basic_fiction_for_fine_resource \<open>{None} \<union> Some ` nonsepable ` Valid\<close>
  \<open>fiction.optionwise Fictional_Algebra.fiction_agree\<close>
  by (standard; simp add: R.fiction_agree_def)
                       
lemma partial_implies:
  \<open> Fic_Space r
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine (Some (agree (nonsepable x))))))
\<Longrightarrow> R.get res = Fine (Some (nonsepable x))\<close>
  unfolding \<phi>Res_Spec_def apply (clarsimp simp add: interp_split'
     R.fiction_agree_def R.basic_fine_fiction_\<I> \<phi>expns mult_strip_fine_011 R.\<r>_valid_split'
     R.mult_strip_inject_011 R.proj_homo_mult fiction.optionwise_\<I> image_iff Bex_def
     fiction_agree_def)
  subgoal for u y a aa
    by (cases a; clarsimp simp add: image_iff Bex_def) .

lemma VS_double:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w {mk x |x. P x} \<longmapsto> {mk x |x. P x} * {mk x |x. P x}\<close>
  unfolding View_Shift_def
  apply (clarsimp simp add: \<phi>expns mk_homo_mult[symmetric] times_fine)
  subgoal for x R u x'
    apply (cases x'; simp)
    subgoal for x'' apply (cases x''; simp)
       apply (metis fun_1upd1 inj_homo_one mult_1_class.mult_1_right one_fine_def one_option_def)
      subgoal for a by (rule exI[where x=\<open>u * mk (Fine (Some a))\<close>]; simp
                ; rule exI[where x=u]; rule exI[where x=\<open>mk (Fine (Some a))\<close>]; simp
                ; rule exI[where x=\<open>mk (Fine (Some a))\<close>]; rule exI[where x=\<open>mk (Fine (Some a))\<close>]
                ; simp add: mk_homo_mult[symmetric] times_fine) . . .

lemma VS_contract:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w {mk x |x. P x} * {mk x |x. P x} \<longmapsto> {mk x |x. P x} \<close>
  unfolding View_Shift_def
  apply (clarsimp simp add: \<phi>expns mk_homo_mult[symmetric])
  subgoal for x R u xa xb
    apply (cases xa; cases xb; simp add: times_fine)
    subgoal for a b
      apply (cases \<open>a ## b\<close>; simp; cases a; cases b; simp)
      by blast+ . .

paragraph \<open>\<phi>-Type\<close>

abbreviation \<open>\<phi>_ag T \<equiv> \<phi> (Agreement (Nonsepable T))\<close>

lemma \<phi>_double_\<phi>app:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi>_ag T \<longmapsto> x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Fine (Some (agree (nonsepable v))) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: VS_double)
qed

lemma \<phi>_contract_\<phi>app:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T \<longmapsto> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Fine (Some (agree (nonsepable v))) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: VS_contract)
qed

end



subsection \<open>Resources based on Mapping\<close>

locale mapping_resource =
  fine_resource entry Resource_Validator
for entry :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, ('key \<Rightarrow> 'val::sep_algebra) ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
begin

lemma "__new_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> k \<notin> dom1 !!(get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> updt (map_fine (\<lambda>f. f(k := u))) res
       \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := u)))})\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd)
  subgoal premises prems for m proof -
    {
      assume A: \<open>k \<notin> dom1 m\<close>
      have t2: \<open>m ## 1(k := u)\<close>
        using A dom1_def sep_disj_fun_def by fastforce
      have t3: \<open>res(name := inject (Fine m)) = res\<close>
        by (simp add: fun_upd_idem prems(5))
      have t1: \<open>res(name := inject (Fine (m(k := u)))) = res * mk (Fine (1(k := u)))\<close>
        thm fun_split_1_not_dom1[where f=m]
        apply (subst fun_split_1_not_dom1[where k=k]) using A apply this
        apply (simp add: times_fine'[symmetric] t2 inj.homo_mult split)
        by (metis fun_1upd_homo_left1 mult.commute t3)
    }
    then show ?thesis
      by (meson domD prems(2) prems(4))
  qed .

end

subsection \<open>One Level Parital Mapping\<close>

subsubsection \<open>Locale for Resource\<close>

locale partial_map_resource =
  mapping_resource Valid entry Resource_Validator
for Valid :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) set"
and entry :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, ('key \<Rightarrow> 'val::nonsepable_semigroup option) ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> P (!!(get res))
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k \<mapsto> any)))})
\<Longrightarrow> updt (map_fine (\<lambda>f. f(k := u))) res
       \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := u)))})\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd )
  apply (clarsimp simp add: mult_strip_fine_011 sep_disj_partial_map_upd
          nonsepable_semigroup_sepdisj_fun times_fine'[symmetric] mk_homo_mult
          mult.assoc[symmetric])
  subgoal premises prems for x aa proof -
    have [simp]: \<open>clean x * mk (Fine aa) = x\<close>
      by (metis fun_split_1 prems(7))
    show ?thesis
      apply simp
      using prems(5) by blast
  qed .


lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> P (!!(get res))
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k \<mapsto> any)))})
\<Longrightarrow> updt (map_fine (\<lambda>f. f(k := None))) res \<in> \<phi>Res_Spec R\<close>
  using "__updt_rule__"[where u=None, simplified, simplified one_fine_def[symmetric],
            simplified, simplified one_set_def[symmetric], simplified] .

abbreviation perm_transformer :: \<open>('key \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'val share option)\<close>
  where \<open>perm_transformer \<equiv> (o) to_share\<close>
abbreviation \<open>share_fiction \<equiv> basic_fine_fiction (fiction.fine (fic_functional perm_transformer))\<close>

(* lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> 1 \<Znrres> v))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k \<mapsto> v)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011)
  subgoal premises prems for res_r y a r
    apply (insert \<open>a * _ = _\<close>[unfolded to_share_strip_011[where b=\<open>1(k \<mapsto> v)\<close>, simplified, OF \<open>a ## _\<close>]])
    apply (clarsimp simp add: times_fine'[symmetric] mk_homo_mult mult.assoc[symmetric])
    using prems(3) by blast
  subgoal premises prems for res_r a r proof -
    have t1[simp]: \<open>a ## 1(k \<mapsto> v)\<close>
      by (metis prems(6) prems(7) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
    show ?thesis
    apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine')
      apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k \<mapsto> v)))"], simp add: prems)
      by (metis (no_types, lifting) map_option_o_map_upd t1 to_share_funcomp_1 to_share_funcomp_sep_disj_I to_share_strip_011)
  qed .


lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> n \<Znrres> v))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011
            proj_homo_mult)
  subgoal premises prems for res_r y a r proof -
    from \<open>a * _ = _\<close>[THEN fun_cong[where x=k], simplified times_fun, simplified]
    have t1: \<open>y k = Some v\<close>
      using prems(6) prems(7) strip_share_fun_mult by force
    then show ?thesis apply (simp add: t1 times_fun)
      using prems(9) sep_disj_partial_map_some_none t1 by fastforce
  qed .

lemma
  assumes A: \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> n \<Znrres> v))))\<close>
  shows share_fiction_partially_implies'[simp]: \<open>!!( get res) k = Some v\<close>
proof -
  from A[THEN share_fiction_partially_implies]
  show ?thesis by fastforce
qed
*)
lemma raw_unit_assertion_implies[simp]:
  \<open>res \<in> \<phi>Res_Spec (R * { mk (Fine (1(k \<mapsto> v)))})
\<Longrightarrow> !!(get res) k = Some v\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011
      proj_homo_mult mult_strip_fine_011 sep_disj_fun_def times_fun)
  by (metis (mono_tags, opaque_lifting) sep_disj_option_nonsepable(2) sep_mult_ac(4) sep_mult_commute times_option(2))


end


subsubsection \<open>Sharing Fiction\<close>

locale share_fiction_for_partial_mapping_resource =
   \<phi>resource_sem Resource_Validator
+  R: partial_map_resource Valid Res Resource_Validator
+  fictional_project_inject INTERPRET Fic \<open>R.share_fiction\<close>
+  \<phi>fiction Resource_Validator INTERPRET
for Valid :: "('key \<Rightarrow> 'val::share_resistence_nonsepable_semigroup option) set"
and Res :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, ('key \<Rightarrow> 'val option) ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{no_inverse,comm_monoid_mult},'RES_N \<Rightarrow> 'RES) fiction"
and Fic :: "('FIC_N,'FIC, ('key \<Rightarrow> 'val share option) ?) Fictional_Algebra.Entry"
begin

sublocale permission_fiction Valid \<open>R.perm_transformer\<close> by standard blast

lemmas expand = expand_raw

lemma partial_implies:
  \<open> Fic_Space r
\<Longrightarrow> 0 < n \<and> n \<le> 1
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine (1(k \<mapsto> n \<Znrres> v)))))
\<Longrightarrow> \<exists>objs. R.get res = Fine objs \<and> objs k = Some v\<close>
  subgoal premises prems proof -
    obtain objs where t1: \<open>R.get res = Fine objs \<and> 1(k \<mapsto> v) \<preceq>\<^sub>S\<^sub>L objs\<close>
      using partial_implies_raw[where x=\<open>1(k \<mapsto> v)\<close> and n=n, simplified] prems by blast
    show ?thesis apply (rule exI[where x=objs], insert t1, simp add: nonsepable_partial_map_subsumption)
      by (smt (verit, best) fun_split_1 fun_upd_same join_sub_def one_option_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fun)
  qed .

lemma partial_implies'[simp]:
  assumes FS: \<open>Fic_Space r\<close>
    and N: \<open>0 < n \<and> n \<le> 1\<close>
    and A: \<open>res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine (1(k \<mapsto> n \<Znrres> v)))))\<close>
  shows \<open>!!(R.get res) k = Some v\<close>
proof -
  from partial_implies[OF FS, OF N, OF A]
  show ?thesis by fastforce
qed

lemma VS_merge_ownership_identity:
  \<open> na + nb \<le> 1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> (na + nb) Identity)\<close>
  by (rule VS_merge_ownership; simp add: \<phi>expns)

lemma VS_split_ownership_identity:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (0 < n \<longrightarrow> na + nb = n \<and> 0 < na \<and> 0 < nb)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity)\<close>
  apply (rule VS_split_ownership; simp add: \<phi>expns sep_disj_fun_def share_fun_def; clarify)
  subgoal premises prems for a
    by (insert \<open>\<forall>_. _\<close>[THEN spec[where x=a]], cases \<open>x a\<close>; simp add: share_All prems) .

lemma VS_divide_ownership:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w FIX x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity)\<close>
  unfolding Fix_def
  by (rule VS_split_ownership_identity; simp add: Premise_def)

end

locale share_fiction_for_partial_mapping_resource_nonsepable =
  share_fiction_for_partial_mapping_resource
    Valid Res Resource_Validator INTERPRET Fic
for Valid :: "('key \<Rightarrow> 'val nonsepable option) set"
and Res :: "('RES_N, 'RES::{comm_monoid_mult,no_inverse}, ('key \<Rightarrow> 'val nonsepable option) ?) Fictional_Algebra.Entry"
and Resource_Validator :: "'RES_N \<Rightarrow> 'RES set"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{comm_monoid_mult,no_inverse}, 'RES_N \<Rightarrow> 'RES) fiction"
and Fic :: "('FIC_N, 'FIC, ('key \<Rightarrow> 'val nonsepable share option) ?) Fictional_Algebra.Entry"
begin

lemma \<phi>nonsepable_normalize:
  \<open>(x \<Ztypecolon> \<phi> (share.\<phi> n (\<phi>MapAt addr (\<phi>Some (Nonsepable Identity)))))
 = (nonsepable x \<Ztypecolon> \<phi> (share.\<phi> n (\<phi>MapAt addr (\<phi>Some Identity))))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

end


subsection \<open>Two Level Parital Mapping\<close>

definition \<open>map_fun_at g k f = (\<lambda>x. if x = k then g (f x) else f x)\<close>

lemma map_fun_at_1[simp]: \<open>map_fun_at g k 1 = 1(k := g 1)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp

lemma map_fun_at_const[simp]:
  \<open>map_fun_at (\<lambda>_. u) k f = f(k := u)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp


subsubsection \<open>Locale of Resources\<close>

locale partial_map_resource2 =
  mapping_resource Valid entry Resource_Validator
for Valid :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) set"
and entry :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, ('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in> Valid)
\<Longrightarrow> P (!!(get res))
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := 1(k2 \<mapsto> any))))})
\<Longrightarrow> updt (map_fine (map_fun_at (map_fun_at (\<lambda>_. u) k2) k)) res
       \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := 1(k2 := u))))})\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd )
  apply (clarsimp simp add: mult_strip_fine_011)
  subgoal premises prems for x aa proof -
    have [simp]: \<open>aa k k2 = None\<close>
      using prems(8) sep_disj_fun sep_disj_partial_map_some_none by fastforce
    then have [simp]: \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (aa * 1(k := 1(k2 \<mapsto> any)))
            = aa * 1(k := 1(k2 := u))\<close>
      unfolding map_fun_at_def fun_eq_iff times_fun_def by auto
    have [simp]: \<open>clean x * mk (Fine aa) = x\<close>
      by (metis fun_split_1 prems(7))
    have [simp]: \<open>aa ## 1(k := 1(k2 := u))\<close>
      by (simp add: sep_disj_fun_def)

    show ?thesis
      apply (simp add: prems times_fine'[symmetric] mk_homo_mult mult.assoc[symmetric])
      using prems(5) by blast
  qed .


lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in> Valid)
\<Longrightarrow> dom (!!(get res) k) = dom any
\<Longrightarrow> P (!!(get res))
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := any)))})
\<Longrightarrow> updt (map_fine (\<lambda>f. f(k := 1))) res \<in> \<phi>Res_Spec R\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd )
  apply (clarsimp simp add: mult_strip_fine_011 times_fun)
  subgoal premises prems for x aa proof -
    have \<open>dom (aa k) = {}\<close>
      by (metis Un_Int_eq(3) dom_mult fun_upd_same prems(2) prems(9) sep_disj_fun sep_disj_partial_map_disjoint)
    then have [simp]: \<open>(aa * 1(k := any))(k := 1) = aa\<close>
      by (smt (verit, del_insts) Diff_iff dom1_upd dom_1 dom_eq_empty_conv fun_split_1_not_dom1 fun_upd_triv fun_upd_upd insertCI)
    have [simp]: \<open>clean x * mk (Fine aa) = x\<close>
      by (metis fun_split_1 prems(8))
    show ?thesis by (simp add: prems)
  qed .

abbreviation perm_transformer :: \<open>('key \<Rightarrow> 'key2 \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option)\<close>
  where \<open>perm_transformer \<equiv> (o) ((o) to_share)\<close>
abbreviation \<open>share_fiction \<equiv> basic_fine_fiction (fiction.fine (fic_functional perm_transformer))\<close>

(*depreciated!*)
(*lemma share_fiction_expn_full':
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := to_share o f))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := f)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011 times_fun)
  subgoal premises prems for res_r y a r
    apply (insert \<open>\<forall>x. a x * _ = _\<close>[THEN spec[where x=k], simplified,
          unfolded to_share_strip_011[where b=f, simplified,
                      OF sep_disj_fun[where x=k, OF \<open>a ## _\<close>, simplified]]])
      apply (clarify)
      subgoal premises prems2 for a' proof -
        have t1: \<open>y = y(k := a') * 1(k := f)\<close>
          unfolding fun_eq_iff times_fun
          apply simp
          by (metis fun_upd_apply mult_1_class.mult_1_right prems2(2) times_fun_def)
        have t2: \<open>y(k := a') ## 1(k := f)\<close>
          using prems2(3) sep_disj_fun_def by fastforce
        show ?thesis
          apply (subst t1)
          apply (clarsimp simp add: times_fine'[OF t2, symmetric] mk_homo_mult mult.assoc[symmetric])
          apply (rule exI[where x="res_r * mk (Fine (y(k := a')))"], simp)
          apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (y(k := a')))"], simp add: prems)
          by (smt (verit, del_insts) mult_1_class.mult_1_right one_fun prems(4) prems2(1))
      qed .
    subgoal premises prems for res_r a fic_r r proof -
      have t1: \<open>a ## 1(k := f)\<close>
        by (metis prems(7) prems(8) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
      have t2: \<open>fic_r ## 1(k := to_share o f)\<close>
        unfolding sep_disj_fun_def
        apply (clarsimp)
        by (metis comp_apply fun_upd_same prems(4) sep_disj_fun_def t1 to_share_funcomp_sep_disj_I)

      show ?thesis
        apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine'[OF t1])
        apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k := f))) "],
                simp add: prems t2)
        by (smt (verit, best) fun_split_1 fun_upd_def fun_upd_same map_option_o_map_upd prems(4) sep_disj_fun t1 t2 times_fun to_share_funcomp_1 to_share_strip_011)
    qed .

lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> 1 \<Znrres> v)))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := 1(k2 \<mapsto> v))))})\<close>
  using share_fiction_expn_full'[where f=\<open>1(k2 \<mapsto> v)\<close>, simplified] .

(*depreciated!*)
lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k k2 = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011
            proj_homo_mult)
  subgoal premises prems for res_r y a r proof -
    note t1 = \<open>a ## _\<close>[THEN sep_disj_fun[where x=k], simplified,
                 THEN sep_disj_fun[where x=k2], simplified]
    from \<open>\<forall>_. (a * _) _ = _\<close>[THEN spec[where x=k], simplified times_fun, simplified,
          THEN fun_cong[where x=k2],
          simplified times_fun, simplified]
    have t2: \<open>y k k2 = Some v\<close>
      using t1 apply (cases \<open>a k k2\<close>; cases \<open>y k k2\<close>; simp)
      by (metis sep_disj_share share.collapse share.inject times_share)

    then show ?thesis apply (simp add: t2 times_fun)
      by (metis mult_1_class.mult_1_left one_option_def prems(9) sep_disj_fun sep_disj_option_nonsepable(1) t2)
  qed .

lemma
  assumes A: \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))\<close>
  shows share_fiction_partially_implies'[simp]: \<open>!!( get res) k k2 = Some v\<close>
proof -
  from A[THEN share_fiction_partially_implies]
  show ?thesis by fastforce
qed
*)

lemma raw_unit_assertion_implies[simp]:
  \<open>res \<in> \<phi>Res_Spec (R * { mk (Fine (1(k := 1(k2 \<mapsto> v))))})
\<Longrightarrow> !!(get res) k k2 = Some v\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011
      proj_homo_mult mult_strip_fine_011 sep_disj_fun_def times_fun)
  by (metis (full_types) fun_upd_same sep_disj_option_nonsepable(1) times_option(3))

lemma raw_unit_assertion_implies':
  \<open>res \<in> \<phi>Res_Spec (R * { mk (Fine (1(k := f)))})
\<Longrightarrow> f \<subseteq>\<^sub>m !!(get res) k\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011
      proj_homo_mult mult_strip_fine_011 sep_disj_fun_def times_fun map_le_def)
  by (smt (verit, del_insts) sep_disj_option_nonsepable(1) times_option(3))

lemma raw_unit_assertion_implies''[simp]:
  \<open>res \<in> \<phi>Res_Spec (R * { mk (Fine (1(k := f)))})
\<Longrightarrow> k2 \<in> dom f
\<Longrightarrow> !!(get res) k k2 = f k2\<close>
  using raw_unit_assertion_implies'[unfolded map_le_def]
  by simp 


end

subsubsection \<open>Locale For Sharing Fiction\<close>

locale share_fiction_for_partial_mapping_resource2 =
   \<phi>resource_sem Resource_Validator
+  R: partial_map_resource2 Valid Res Resource_Validator
+  fictional_project_inject INTERPRET Fic \<open>R.share_fiction\<close>
for Valid :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::share_resistence_nonsepable_semigroup option) set"
and Res :: "('RES_N, 'RES::{no_inverse,comm_monoid_mult}, ('key \<Rightarrow> 'key2 \<Rightarrow> 'val option) ?) Fictional_Algebra.Entry"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{no_inverse,comm_monoid_mult},'RES_N \<Rightarrow> 'RES) fiction"
and Fic :: "('FIC_N,'FIC, ('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option) ?) Fictional_Algebra.Entry"
begin

sublocale permission_fiction Valid \<open>R.perm_transformer\<close> by standard  blast

lemmas expand = expand_raw

lemma [simp]:
  \<open>R.perm_transformer (1(k := f)) = 1(k := to_share o f)\<close>
  unfolding fun_eq_iff by simp

lemmas partial_implies = partial_implies_raw

lemma partial_implies':
  \<open> Fic_Space r
\<Longrightarrow> 0 < n \<and> n \<le> 1
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v))))))
\<Longrightarrow> \<exists>objs. R.get res = Fine objs \<and> objs k k2 = Some v\<close>
  subgoal premises prems proof -
    obtain objs where t1: \<open>R.get res = Fine objs \<and> 1(k := 1(k2 \<mapsto> v)) \<preceq>\<^sub>S\<^sub>L objs\<close>
      using partial_implies_raw[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close> and n=n, simplified] prems by blast
    show ?thesis
      apply (rule exI[where x=objs])
      by (smt (verit, del_insts) fun_upd_same join_sub_def mult_1_class.mult_1_right one_option_def sep_disj_fun_def sep_disj_option_nonsepable(1) sep_mult_commute t1 times_fun_def)
  qed .

lemma partial_implies'':
  assumes FS: \<open>Fic_Space r\<close>
    and N: \<open>0 < n \<and> n \<le> 1\<close>
    and A: \<open> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v))))))\<close>
  shows [simp]: \<open>!!(R.get res) k k2 = Some v\<close>
proof -
  from partial_implies'[OF FS, OF N, OF A]
  show ?thesis by fastforce
qed

end

end