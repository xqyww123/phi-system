theory NuStd_Base
  imports NuSys NuInstructions NuLLReps
  keywords
     "\<up>:" "\<Up>:" "\<down>:" "\<Down>:" "always" "--" "\<rightarrow>" "\<lambda>" "\<lambda>'" "$" :: quasi_command
  abbrevs "|^" = "\<up>"
    and "||^" = "\<Up>"
    and "|v" = "\<down>"
    and "||v" = "\<Down>"
    and "<up>" = "\<up>"
    and "<down>" = "\<down>"
    and "<Up>" = "\<Up>"
    and "<Down>" = "\<Down>"
    and "<some>" = "\<^bold>s\<^bold>o\<^bold>m\<^bold>e"
begin

chapter \<open>Standard Base Library\<close>

section \<open>Preliminary\<close>

\<phi>overloads singular and plural
\<phi>overloads split and split_cast and merge and pop and pop_cast and push

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]


section \<open>Basic Operations\<close>

subsection \<open>Variable\<close>

subsubsection \<open>Syntax\<close>

syntax "__var__" :: "idt \<Rightarrow> logic" ("\<^bold>v\<^bold>a\<^bold>r _" [1000] 999)

parse_ast_translation \<open>
  let open Ast
    fun mk_Var name =
      Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>,
        Appl [Variable "Var", name, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>]]
   in [(\<^syntax_const>\<open>__var__\<close>, fn ctxt => fn [name] => mk_Var name)]
  end
\<close>

syntax "__get_var__" :: "idt \<Rightarrow> logic" ("$_" [1000] 999)
consts "get_var____\<phi>" :: "varname \<Rightarrow> 'b"

translations "$x" => "CONST get_var____\<phi> x"

definition Variable_of :: \<open>'a \<Rightarrow> varname \<Rightarrow> 'a\<close> (infix "<val-of-var>" 22)
  where [iff]: \<open>(S <val-of-var> V) = S\<close>

definition Set_Variable :: \<open>varname \<Rightarrow> 'a \<Rightarrow> 'a\<close> ("$_ := _" [1000, 51] 50)
  where [iff]: \<open>($x := y) = y\<close>

lemma (in std) [\<phi>reason 2000 on \<open>Synthesis_Parse (?var::varname) ?Y\<close>]:
  \<open>Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T)\<close>
  unfolding Synthesis_Parse_def ..


\<phi>processor (in std) get_variable 5000 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close>)  \<open>
  fn (ctxt,sequent) => \<^keyword>\<open>$\<close> |-- Parse.term >> (fn var => fn () =>
    let
      val ctxt_parse = Config.put phi_synthesis_parsing true ctxt
      val term = Const(\<^const_name>\<open>get_var____\<phi>\<close>, dummyT) $ Syntax.parse_term ctxt_parse var
                  |> Syntax.check_term ctxt_parse
                  |> Thm.cterm_of ctxt
    in
      NuToplevel.synthesis term (ctxt,sequent)
    end)
\<close>


subsubsection \<open>Operations\<close>

ML_file_debug "library/local_value.ML"

context std begin

paragraph \<open>Get Variable\<close>

declare [ [\<phi>not_define_new_const] ]

proc op_get_var:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  argument \<open>x \<Ztypecolon> Var vname T\<close>
  return   \<open>x \<Ztypecolon> Var vname T\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close>
  \<medium_left_bracket>
    to_Identity op_get_var''
  \<medium_right_bracket>. .

lemma [\<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> ?R'\<heavy_comma> SYNTHESIS ?x <val-of-var> ?var \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> SUBGOAL G G2
\<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> Y\<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G2
\<Longrightarrow> SOLVE_SUBGOAL G2
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var var TY \<lbrace> X \<longmapsto> Y\<heavy_comma> x \<Ztypecolon> Var var T \<heavy_comma> SYNTHESIS x <val-of-var> var \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  \<medium_left_bracket> premises _ and GetVar and _ and [\<phi>reason on \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]
    GetVar op_get_var \<medium_right_bracket>. .


paragraph \<open>Set Variable\<close>

declare [ [\<phi>trace_reasoning]]

proc op_set_var:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  argument \<open>x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l U\<close>
  return   \<open>y \<Ztypecolon> Var var U\<close>
  \<medium_left_bracket> to_Identity \<open>var\<close> to_Identity op_set_var'' \<medium_right_bracket>. .

proc op_set_var__synthesis[
  \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> ?R'\<heavy_comma> SYNTHESIS ($?var := ?y) \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l ?U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> X \<longmapsto> X1\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<close>
  and      \<open>SUBGOAL G G2\<close>
  and S[unfolded GOAL_CTXT_def FOCUS_TAG_def]:
        \<open>\<And>vy. \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X1\<heavy_comma> y \<Ztypecolon> Val vy U \<longmapsto> \<blangle> Y\<heavy_comma> x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> Val vy U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G2\<close>
  and   \<open>SOLVE_SUBGOAL G2\<close>
  and [\<phi>reason on \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  and [\<phi>reason on \<open>\<phi>SemType (y \<Ztypecolon> U) ?TY\<close>]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
 goal G
argument \<open>X\<close>
return   \<open>Y\<heavy_comma> y \<Ztypecolon> Var var U \<heavy_comma> SYNTHESIS ($var := y) \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l U\<close>
throws   E
  \<medium_left_bracket> G S op_set_var op_get_var \<medium_right_bracket>. .

declare [ [\<phi>not_define_new_const = false] ]

paragraph \<open>Declare New Variables\<close>

proc (in std) op_var_scope:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and BLK: \<open>\<forall>var. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> X\<heavy_comma> x \<Ztypecolon> Var var T \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> y \<Ztypecolon> Var var (U <of-type> TY) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<heavy_comma> y \<Ztypecolon> Var var (U <of-type> TY) \<rbrace>\<close>
  argument \<open>X\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close>
  return   \<open>Y\<close>
  throws   E
  \<medium_left_bracket> to_Identity op_var_scope';;
    try'' \<medium_left_bracket> BLK to_Identity op_free_var \<medium_right_bracket>. \<medium_left_bracket> to_Identity op_free_var;; throw \<medium_right_bracket>. \<medium_right_bracket>.
  ML_val \<open>@{Isar.goal}\<close>
  .

thm op_var_scope_\<phi>compilation
thm op_var_scope'_def
term op_var_scope'

lemma "__\<phi>op_var_scope__":
  \<open> (\<And>var. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> R\<heavy_comma> x \<Ztypecolon> Var var T\<heavy_comma>  X \<longmapsto> Y \<heavy_comma> y \<Ztypecolon> Var var (U <of-type> TY) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<heavy_comma> y \<Ztypecolon> Var var (U <of-type> TY) \<rbrace>)
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TY F [raw] \<lbrace> R\<heavy_comma> (X\<heavy_comma> x \<Ztypecolon> Val raw T) \<longmapsto> \<lambda>_::'VAL list. Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding mult.assoc[symmetric]
  using op_var_scope_\<phi>app[where X=\<open>R\<heavy_comma> X\<close> and x = x and T = T and TY = TY and F=F and y=y, of Y U E raw]
  by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) mult.commute)

lemma "__\<phi>op_set_var__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R\<heavy_comma> y \<Ztypecolon> Var var U\<heavy_comma> X \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (op_set_var var TY [raw] \<ggreater> g) \<lbrace> R\<heavy_comma> (X\<heavy_comma> x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> Val raw U) \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  \<medium_left_bracket> premises G and [\<phi>reason on \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>] and [\<phi>reason on \<open>\<phi>SemType (y \<Ztypecolon> U) ?TY\<close>]
    op_set_var G \<medium_right_bracket>. .



lemma "__\<phi>op_var_scope__0":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R\<heavy_comma> Void \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  by fastforce

\<phi>processor assign_variable 7500 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S\<close>) \<open>
  fn (ctxt,sequent) => ((\<^keyword>\<open>\<rightarrow>\<close> |-- Parse.list1 Parse.binding)
>> (fn vars => fn () =>
  raise NuProcessor.Terminate_Process (Local_Value.mk_var_scope vars (ctxt,sequent), I)))
\<close>

declare [ [\<phi>not_define_new_const = false] ]


subsection \<open>Arithmetic Operations\<close>

\<phi>overloads "+" and "-" and "*" and "/" and "<" and "\<le>" and ">" and "\<ge>" and "=" and "\<not>"
  and "\<and>" and "\<or>"

subsubsection \<open>Boolean Arithmetic\<close>

paragraph \<open>Not\<close>

lemma (in std) op_not[\<phi>overload \<not>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_not raw \<lbrace> x \<Ztypecolon> Val raw \<bool> \<longmapsto> \<not> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<rbrace>\<close>
  unfolding op_not_def
  by \<phi>reason

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R1\<heavy_comma> SYNTHESIS \<not>?b \<Ztypecolon> Val ?v ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R1\<heavy_comma> SYNTHESIS \<not>b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool>\<close>
  \<medium_left_bracket> F1 \<not> \<medium_right_bracket>. .

paragraph \<open>And\<close>

lemma (in std) op_and[\<phi>overload \<and>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_and vb va \<lbrace> a \<Ztypecolon> Val va \<bool>\<heavy_comma> b \<Ztypecolon> Val vb \<bool> \<longmapsto> a \<and> b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<rbrace>\<close>
  unfolding op_and_def
  by \<phi>reason

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS (?x \<and> ?y) \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS (x \<and> y) \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool>\<close>
  throws   \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> yy ;; F2 $y \<and> ;; \<medium_right_bracket>. .

paragraph \<open>Or\<close>

lemma (in std) op_or[\<phi>overload \<or>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_or vb va \<lbrace> a \<Ztypecolon> Val va \<bool>\<heavy_comma> b \<Ztypecolon> Val vb \<bool> \<longmapsto> a \<or> b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<rbrace>\<close>
  unfolding op_or_def
  by \<phi>reason

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x \<or> ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool>\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x \<or> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x, y;; F2 $y \<or> \<medium_right_bracket>. .


subsubsection \<open>Constant Integer\<close>

lemma (in std) op_const_int_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2^b \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int b n \<lbrace> Void \<longmapsto> n \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<nat>[b] \<rbrace>\<close>
  unfolding op_const_int_def Premise_def Synthesis_def
  by \<phi>reason

lemma (in std) [\<phi>reason 1200
    on \<open>Synthesis_Parse (numeral ?n::nat) ?X\<close>
       \<open>Synthesis_Parse (0::nat) ?X\<close>
]:
  \<open> Synthesis_Parse (n \<Ztypecolon> \<nat>[32]) X
\<Longrightarrow> Synthesis_Parse n X\<close>
  unfolding Synthesis_Parse_def ..

lemma (in std) [\<phi>reason
    on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS numeral ?n \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS 1 \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS 0 \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int b n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS n \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_def GOAL_CTXT_def
  using op_const_int_\<phi>app[THEN \<phi>frame, simplified] .

lemma (in std) op_const_size_t:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> Void \<longmapsto> n \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l Size \<rbrace>\<close>
  unfolding op_const_size_t_def Premise_def
  by \<phi>reason

lemma (in std) [\<phi>reason 1200
    on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS (numeral ?n) \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS 0 \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS 1 \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS n \<Ztypecolon> Size \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_def GOAL_CTXT_def
  using op_const_size_t[THEN \<phi>frame, simplified] .


subsubsection \<open>Integer Arithmetic\<close>

paragraph \<open>Addition\<close>

lemma (in std) op_add[\<phi>overload +]:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^b \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b vy vx \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> x + y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def Premise_def
  by \<phi>reason

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x + ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b]  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>x + y < 2 ^ b\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x + y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x;; F2 \<rightarrow> y;; $x $y + \<medium_right_bracket>. .


paragraph \<open>Subtraction\<close>

lemma (in std) op_sub[\<phi>overload -]:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub b vy vx \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> x - y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<nat>[b] \<rbrace>\<close>
  unfolding op_sub_def Premise_def
  apply \<phi>reason
  apply (simp add: \<phi>expns)
  by (metis Nat.add_diff_assoc2 add.commute less_imp_diff_less mod_add_self2 mod_less)

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x - ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>y \<le> x\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x - y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x;; F2 \<rightarrow> y;; $x $y - \<medium_right_bracket>. .


paragraph \<open>Division\<close>

lemma (in std) op_udiv[\<phi>overload /]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_udiv b vy vx \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> x div y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<nat>[b] \<rbrace>\<close>
  unfolding op_udiv_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>expns)
  using div_le_dividend le_less_trans by blast

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x div ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x div y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x;; F2 \<rightarrow> y;; $x $y / \<medium_right_bracket>. .


paragraph \<open>Less Than\<close>

lemma (in std) op_lt[\<phi>overload <]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt b \<lbrace> x \<Ztypecolon> \<nat>[b]\<heavy_comma> y \<Ztypecolon> \<nat>[b] \<longmapsto> x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_lt_def
  by \<phi>reason

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x < ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x < y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x;; F2 \<rightarrow> y ;; $x $y < \<medium_right_bracket>. .

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x > ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x > y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> y;; F2 $y < \<medium_right_bracket>. .

paragraph \<open>Less Equal\<close>

lemma (in std) op_le[\<phi>overload \<le>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le b \<lbrace> x \<Ztypecolon> \<nat>[b]\<heavy_comma> y \<Ztypecolon> \<nat>[b] \<longmapsto> x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_le_def
  by \<phi>reason

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x \<le> ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b]  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x \<le> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x;; F2 \<rightarrow> y;; $x $y \<le> \<medium_right_bracket>. .

proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x \<ge> ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x \<ge> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x;; F2 $x \<le> \<medium_right_bracket>. .


subsubsection \<open>General Arithmetic\<close>

paragraph \<open>Equal\<close>

lemma (in std) op_equal_\<phi>app[\<phi>overload =]:
  \<open> \<phi>SemType (a \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Equal T can_eq eq
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e can_eq a b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal TY \<lbrace> a \<Ztypecolon> T\<heavy_comma> b \<Ztypecolon> T \<longmapsto> eq a b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_equal_def
  apply \<phi>reason
    apply (simp add: \<phi>SemType_def subset_iff)
   apply \<phi>reason
    apply (simp add: \<phi>SemType_def subset_iff)
apply (unfold \<phi>Equal_def Premise_def, simp)
  by \<phi>reason


proc [
    \<phi>reason on \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> ?R2\<heavy_comma> SYNTHESIS VAL (?x = ?y) \<Ztypecolon> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS VAL x \<Ztypecolon> T  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS VAL y \<Ztypecolon> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  assumes [\<phi>reason on \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason on \<open>\<phi>SemType (y \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (y \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason on \<open>\<phi>Equal T ?can_eq ?eq\<close>]: \<open>\<phi>Equal T can_eq (=)\<close>
  premises \<open>can_eq x y\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS VAL (x = y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 \<rightarrow> x;; F2 \<rightarrow> y;; $x $y = \<medium_right_bracket>. .



end


subsection \<open>Branches & Loops\<close>

context std begin

lemma op_sel_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sel \<lbrace> VAL A\<heavy_comma> VAL B\<heavy_comma> c \<Ztypecolon> \<bool> \<longmapsto> VAL (if c then A else B) \<rbrace>\<close>
  unfolding op_sel_def
  by \<phi>reason

lemma branch_\<phi>app:
  \<open> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>T \<lbrace> X \<longmapsto> Y\<^sub>T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>)
\<Longrightarrow> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>F \<lbrace> X \<longmapsto> Y\<^sub>F \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>)
\<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge C Y\<^sub>T Y\<^sub>F = Y
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if br\<^sub>T br\<^sub>F \<lbrace> X\<heavy_comma> C \<Ztypecolon> \<bool> \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T + E\<^sub>F \<rbrace>\<close>
  unfolding op_if_def Premise_def Conv_def Merge_def
  apply \<phi>reason apply (simp add: \<phi>expns)+
  by (meson \<phi>CONSEQ plus_set_in_iff subsetI)

proc "if":
  assumes C: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c cond \<lbrace> X \<longmapsto> X1\<heavy_comma> C \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
      and brT: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brT \<lbrace> X1 \<longmapsto> Y\<^sub>T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>\<close>
      and brF: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brF \<lbrace> X1 \<longmapsto> Y\<^sub>F \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>\<close>
      and [\<phi>reason on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge C Y\<^sub>T Y\<^sub>F = ?Y\<close>]: \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge C Y\<^sub>T Y\<^sub>F = Y\<close>
  argument \<open>X\<close>
  return \<open>Y\<close>
  throws \<open>E + E\<^sub>T + E\<^sub>F\<close>
  \<medium_left_bracket> C branch brT brF \<medium_right_bracket>. .

end


section \<open>Procedures and Operations\<close>

context std begin

subsection \<open>Control Flow\<close>

subsubsection \<open>Loops\<close>

lemma (in std) "__DoWhile__rule_\<phi>app":
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> (\<exists>*x'. X x' \<heavy_comma> P x' \<Ztypecolon> \<bool>) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding op_do_while_def \<phi>Procedure_def
  apply (simp add: SemDoWhile_deterministic2 \<phi>expns LooseStateTy_expn')
  apply (rule allI impI conjI)+
  apply (elim exE)
  apply (simp add: SemDoWhile_deterministic2)
  subgoal for comp R s
  apply (rotate_tac 2)
    apply (induct body comp s rule: SemDoWhile.induct)
apply (simp add: \<phi>expns times_list_def)
    apply fastforce
    subgoal premises prems for f s val res s''
      apply (rule \<open>_ \<Longrightarrow> _ \<Longrightarrow> _\<close>[OF \<open>\<forall>_. _\<close>])
      apply (simp add: \<phi>expns times_list_def)
      apply (insert \<open>\<forall>_. _\<close>[THEN spec[where x=s], THEN spec[where x=R], simplified prems, simplified])
      apply (clarsimp simp add: \<phi>expns times_list_def)
      by (metis zero_neq_one)
    apply force
     apply force
  apply (simp add: \<phi>expns times_list_def)
    subgoal premises prems for f s
      using \<open>\<forall>_. _\<close>[THEN spec[where x=s], THEN spec[where x=R], simplified prems, simplified] . . .


text \<open>Note the While rule we mentioned in the paper is just a special case of the above
      __DoWhile__rule_\<phi>app\<close>

lemma (in std)
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<heavy_comma> P x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x'\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<and> \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<rbrace>"
  using "__DoWhile__rule_\<phi>app"[where X=\<open>\<lambda>x. X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j I x\<close> and P=P,
            simplified Subjection_times, simplified] .


declare [[\<phi>not_define_new_const]]

declare [ [\<phi>trace_reasoning] ]

proc (in std) do_while:
assumes V: \<open>Variant_Cast vars X X'\<close>
    and \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m cond\<close>
premises X[useful]: \<open>cond vars\<close>
assumes B: \<open>\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X' x \<longmapsto> \<exists>*x'. X' x'\<heavy_comma> cond x' \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
argument \<open>X\<close>
return   \<open>X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. \<not> cond x'\<close>
throws E
  \<medium_left_bracket> unfold V[unfolded Variant_Cast_def]
    "__DoWhile__rule"[where P=cond, simplified] \<medium_left_bracket> B \<medium_right_bracket>.
  \<medium_right_bracket> by simp .

declare [[\<phi>not_define_new_const=false]]


proc while:
  assumes V: "Variant_Cast vars X' X"
    and C: "\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<lbrace> X x \<longmapsto> X x\<heavy_comma> cond \<Ztypecolon> Predicate_About x \<rbrace>"
    and B: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<lbrace> X x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. True \<rbrace>"
  argument \<open>X'\<close>
  return \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. \<not> cond x\<close>
  \<medium_left_bracket> unfold V[unfolded Variant_Cast_def]
    C
    branch \<medium_left_bracket> do_while  vars \<open>cond vars\<close> \<medium_left_bracket> B \<exists>vars' C \<medium_right_bracket>. \<medium_right_bracket>.
           \<medium_left_bracket> \<medium_right_bracket> var vars subj \<open>\<not> cond vars\<close> using \<phi> by simp
  \<medium_right_bracket>. .


(*Example*)

proc
  argument \<open>x \<Ztypecolon> \<nat>[32]\<close>
  return \<open>x - 1 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket>  \<rightarrow> varx
  ;; (*assign the value x to a variable named varx*)
               (* command `;;` leads a statement, or ends the previous statement. *)
     if \<open>0 < $varx\<close> \<medium_left_bracket> \<open>$varx - 1\<close> \<medium_right_bracket>.
                    \<medium_left_bracket> \<open>0::nat\<close> \<medium_right_bracket>.
    (* the cartouche like \<open>0 < $varx\<close> invokes a synthesis process
       to make that value automatically *)
  \<medium_right_bracket>. .



proc
  premises \<open>x < 10\<close>
  argument \<open>x \<Ztypecolon> \<nat>[20]\<close>
  return \<open>10 \<Ztypecolon> \<nat>[20]\<close>
  \<medium_left_bracket> \<rightarrow> v ;;
    while x invar \<open>x \<le> 10\<close> (* x is variable during the loop and it meets an invariant x \<le> 10  *)
    \<medium_left_bracket> \<open>$v < 10\<close> \<medium_right_bracket>.
    \<medium_left_bracket> \<open>$v+1\<close> \<rightarrow> v \<medium_right_bracket>. ;; (* this ;; leads an empty statement which does nothing except simplification *)
    have [simp]: \<open>x = 10\<close> using \<phi> by simp ;;
    $v
  \<medium_right_bracket>. .


subsubsection \<open>recursion\<close>

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



definition \<phi>SemTypes :: \<open>('VAL,'FIC_N,'FIC) assn \<Rightarrow> 'TY list \<Rightarrow> bool\<close>
  where \<open>\<phi>SemTypes S TYs \<longleftrightarrow> (fst ` S) \<subseteq> Collect (list_all2 (\<lambda>t x. x \<in> Well_Type t) TYs)\<close>

lemma [\<phi>reason 1200 on \<open>\<phi>SemTypes (OBJ ?X) ?TYs\<close>]:
  \<open>\<phi>SemTypes (OBJ X) []\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemTypes R TYs
\<Longrightarrow> \<phi>SemTypes (R\<heavy_comma> OBJ X) TYs\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200 on \<open>\<phi>SemTypes (VAL ?X) ?TYs\<close>]:
  \<open> \<phi>SemType X TY
\<Longrightarrow> \<phi>SemTypes (VAL X) [TY]\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemType X TY
\<Longrightarrow> \<phi>SemTypes R TYs
\<Longrightarrow> \<phi>SemTypes (R\<heavy_comma> VAL X) (TY # TYs)\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. \<phi>SemTypes (S x) TYs)
\<Longrightarrow> \<phi>SemTypes (ExSet S) TYs\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemTypes S TYs
\<Longrightarrow> \<phi>SemTypes (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) TYs\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma "__op_recursion__":
  " (\<And>x. \<phi>SemTypes (X x) TXs)
\<Longrightarrow> (\<And>x. \<phi>SemTypes (Y x) TYs)
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<forall>g x'. (\<forall>x''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> X x'' \<longmapsto> Y x'' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x'' \<rbrace>) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g \<lbrace> X x' \<longmapsto> Y x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x' \<rbrace>)
\<Longrightarrow> \<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion TXs TYs F \<lbrace> X x \<longmapsto> Y x \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x \<rbrace>"
  unfolding op_recursion_def \<phi>Procedure_def atomize_all
  apply (auto simp add: SemRec_deterministic2)
  subgoal for x a b xa R
    apply (rotate_tac 3) apply (induct rule:  SemRec.induct) by (auto 0 6) .


rec_proc dec:
  var i
  premises A: \<open>0 \<le> i\<close>
  argument \<open>i \<Ztypecolon> \<nat>[b]\<close>
  return \<open>0 \<Ztypecolon> \<nat>[b]\<close>
  \<medium_left_bracket> \<rightarrow> vi ;;
    if \<open>0 < $vi\<close> \<medium_left_bracket> \<open>$vi - 1\<close> dec \<medium_right_bracket>.
                 \<medium_left_bracket> $vi is 0 \<medium_right_bracket>.
  \<medium_right_bracket>. .



subsection \<open>Field Index\<close>

subsubsection \<open>Abstraction\<close>

definition FieldIndex :: " ('a,'a,'ax,'ax) index \<Rightarrow> ('ax::lrep,'bx) \<phi> \<Rightarrow> ('a::lrep,'b) \<phi> \<Rightarrow> ('b \<Rightarrow> 'bx) \<Rightarrow> (('bx \<Rightarrow> 'bx) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>bool"
  where "FieldIndex adr X A gt mp \<longleftrightarrow> (\<forall>a f. \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<lbrace> gt a \<tycolon> X \<^bold>@ a \<tycolon> A \<longmapsto> f (gt a) \<tycolon> X \<^bold>@ mp f a \<tycolon> A \<rbrace>)"

lemma FieldIndex_here: "FieldIndex index_here X X id id"
  unfolding FieldIndex_def \<phi>index_def index_here_def by auto
lemma FieldIndex_left: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_left f) X (A \<cross_product> R) (gt o fst) (apfst o mp)"
  unfolding FieldIndex_def \<phi>index_def index_left_def by (auto simp add: nu_exps)
lemma FieldIndex_right: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_right f) X (R \<cross_product> A) (gt o snd) (apsnd o mp)"
  unfolding FieldIndex_def \<phi>index_def index_right_def by (auto simp add: nu_exps)

lemma FieldIndex_tupl: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_tuple f) X \<lbrace> A \<rbrace> gt mp"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def by (auto simp add: tuple_forall nu_exps)

\<phi>processor field_index 5000 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn major => Parse.nat >> (fn i => fn _ =>
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



(*  WORK IN PROGRESS
subsection \<open>Field Index\<close>

lemma [\<phi>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ \<lbrace> A \<rbrace> \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ \<lbrace> A \<rbrace> \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ \<lbrace> A \<rbrace> \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

subsubsection \<open>Abstraction\<close>


\<phi>processor field_index 110 \<open>\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<lbrace> X \<^bold>@ A \<rbrace> \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn sequent =>
  Parse.nat >> (fn i => fn _ =>
  let open NuBasics NuHelp
    val A = Thm.major_prem_of sequent |> dest_Trueprop |> dest_triop \<^const_name>\<open>AdrGet\<close> |> #3
    val A = repeat (dest_monop \<^const_name>\<open>NuTuple\<close>)
    val arity = 1
val _ =
Logic.dest_implies (prop_of sequent) |> #1
        |> dest_Trueprop |> dest_quinop \<^const_name>\<open>FieldIndex\<close> |> #3
        |> dest_monop \<^const_name>\<open>NuTuple\<close> |> strip_binop_r \<^const_name>\<open>Fusion\<close> |> length
    val path1 = funpow (i-1) (fn th => th RS @{thm FieldIndex_right})
        (@{thm FieldIndex_here}
              |> (fn th => if arity = i then th else th RS @{thm FieldIndex_left}))
  in 
    (path1 RS (@{thm FieldIndex_tupl} RS major), ctx)
  end)\<close>

\<phi>processor field_index_getter 110 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn major => Parse.nat >> (fn i => fn _ =>
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

*)
subsection \<open>Tuple Operations\<close>

subsubsection \<open>Construction & Destruction\<close>

theorem tup_\<phi>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup TYPE('a::field_list) \<lbrace> x \<tycolon> X \<longmapsto> x \<tycolon> \<lbrace> X \<rbrace>  \<rbrace>"
  for X :: "('a::field_list, 'ax) \<phi>"
  unfolding cons_tup_def Procedure_def by (simp add: pair_forall nu_exps)

theorem det_\<phi>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup TYPE('a::field_list) \<lbrace> x \<tycolon> \<lbrace> X \<rbrace> \<longmapsto> x \<tycolon> X \<rbrace>"
  for X :: "('a::field_list, 'ax) \<phi>"
  unfolding Procedure_def op_dest_tup_def by (simp add: tuple_forall pair_forall nu_exps)

subsubsection \<open>Field Accessing\<close>

lemma
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<Longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_tuple idx TYPE('a::field_list) \<lbrace> VAL A \<longmapsto> VAL X \<rbrace> "
  for A :: " 'a::field_list tuple set"
  unfolding \<phi>index_def \<phi>def pair_forall op_get_tuple_def tuple_forall
  by (simp add: nu_exps)

lemma "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<rbrace> \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_tuple idx TYPE('a::field_list) TYPE('y::lrep) \<lbrace> VAL A \<heavy_comma> VAL Y \<longmapsto> VAL B \<rbrace> "
  for A :: "'a::field_list tuple set" and Y :: "'y::lrep set"
  unfolding \<phi>index_def \<phi>def pair_forall op_set_tuple_def
  by (simp add: nu_exps)


subsection \<open>Memory & Pointer Operations\<close>

subsubsection \<open>Pointer Arithmetic\<close>


theorem op_shift_pointer[\<phi>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e address_llty addr = LLTY('a::lrep) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e offset_of addr + delta \<le> address_len addr \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer TYPE('a::lrep) \<lbrace> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> delta \<tycolon> \<nat>[size_t] \<longmapsto>
      R\<heavy_comma> addr ||+ delta \<tycolon> Pointer \<rbrace>"
  unfolding \<phi>def op_shift_pointer_def by (cases addr) (auto simp add: lrep_exps same_addr_offset_def nu_exps)


theorem op_shift_pointer_slice[ unfolded SepNu_to_SepSet, \<phi>overload split ]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < length xs \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer TYPE('p) \<lbrace> addr \<R_arr_tail> xs \<tycolon> Array T \<heavy_comma> addr \<tycolon> Pointer \<heavy_comma> n \<tycolon> \<nat>[size_t]
      \<longmapsto> (addr \<R_arr_tail> take n xs, shift_addr addr n \<R_arr_tail> drop n xs) \<tycolon> (Array T \<^emph> Array T) \<heavy_comma> addr ||+ n \<tycolon> Pointer \<rbrace>"
  for T :: "('p::field, 'x) \<phi>"
  unfolding \<phi>def op_shift_pointer_def Array_def Separation_expn_R pair_forall
  apply (cases addr)
  apply (auto simp add: lrep_exps same_addr_offset_def raw_offset_of_def distrib_right nu_exps
        add.commute add.left_commute pair_forall Shallowize'_expn intro: heap_split_id)
  subgoal for x1 x2 aa b H h1 h2
    apply (rule heap_split_id, simp)
    apply (rule heap_split_by_addr_set[of _ _ "- {(x1 |+ x2 + i) | i. i < n}"])
    apply (auto simp add: nu_exps) done
  done


subsubsection \<open>Allocation\<close>

lemma malloc_split: "Heap h \<Longrightarrow> P (heap_assignN n v (malloc h) Map.empty) h \<Longrightarrow>
    \<exists>h1 h2. heap_assignN n v (malloc h) h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  apply (rule exI[of _ "heap_assignN n v (malloc h) Map.empty"], rule exI[of _ h], simp)
  subgoal premises prems
    unfolding heap_assignN_def using prems(1)
    by (simp add: map_add_def fun_eq_iff resource_key_forall disjoint_rewL memaddr_forall dom_def
          malloc option.case_eq_if) done

lemma [intro]: "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" proof -
  have "AvailableSegments h \<subseteq> {seg} \<union> AvailableSegments (heap_assignN n v seg h)"
    unfolding AvailableSegments_def heap_assignN_def by auto 
  then show "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" 
    unfolding Heap_def using infinite_super by auto
qed

lemma heap_assignN_eval: "v \<in> T \<Longrightarrow> i < n \<Longrightarrow> heap_assignN n (Some (deepize v)) seg h \<^bold>a\<^bold>t (seg |+ i) \<^bold>i\<^bold>s T"
  unfolding MemAddrState_def addr_allocated_def heap_assignN_def by auto



      
theorem alloc_array_\<phi>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N \<Longrightarrow> \<phi>Zero N zero \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc TYPE('x)
      \<lbrace> n \<tycolon> \<nat>[size_t] 
        \<longmapsto> ptr \<R_arr_tail> replicate n zero \<tycolon> Array N \<heavy_comma> ptr \<tycolon> Pointer \<^bold>s\<^bold>u\<^bold>b\<^bold>j ptr. addr_cap ptr n \<rbrace>"
  for N :: "('x::{zero,field},'b)\<phi>"
  unfolding \<phi>def op_alloc_def Array_def
  apply (auto simp add: lrep_exps list_all2_conv_all_nth Let_def same_addr_offset_def nu_exps
      Separation_expn)
  subgoal for aa b M h2
  apply (rule malloc_split, simp add: heap_assignN_eval)
    apply (auto simp add: heap_assignN_eval nu_exps) done
  done


proc alloc : \<open>Void\<close> \<longmapsto> \<open>ptr \<R_arr_tail> zero \<tycolon> Ref T \<heavy_comma> ptr \<tycolon> Pointer \<^bold>s\<^bold>u\<^bold>b\<^bold>j ptr. addr_cap ptr 1\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m T" and [\<phi>reason on ?any]: "\<phi>Zero T zero"
  have A[simp]: "replicate 1 zero = [zero]" by (simp add: One_nat_def)
  \<bullet>\<open>1 \<tycolon> \<nat>[size_t]\<close> alloc_array T
  finish


subsubsection \<open>Load & Store\<close>

\<phi>overloads \<up> and "\<up>:" and \<Up> and "\<Up>:" and \<down> and "\<down>:" and \<Down> and "\<Down>:" and free

abbreviation "list_map_at f i l \<equiv> list_update l i (f (l ! i))"

lemma op_load[ \<phi>overload "\<up>:" ]:
  "FieldIndex field_index Y X gt mp \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load TYPE('y::field) TYPE('x) field_index
    \<lbrace> addr \<R_arr_tail> x \<tycolon> Ref X \<heavy_comma> addr \<tycolon> Pointer \<longmapsto> addr \<R_arr_tail> x \<tycolon> Ref X \<heavy_comma> gt x \<tycolon> Y\<rbrace> "
  for X :: "('x::field, 'a) \<phi>" and Y :: "('y::field, 'b) \<phi>"
  unfolding op_load_def Procedure_def \<phi>index_def Protector_def FieldIndex_def
  by (cases field_index, cases addr)
    (auto simp add: lrep_exps MemAddrState_def nu_exps disjoint_rewR split: option.split iff: addr_allocated_def)


lemmas [ \<phi>overload "\<up>" ] = op_load[THEN mp, OF FieldIndex_here, simplified]

proc i_load_n[\<phi>overload "\<up>:"]:
  \<open>a \<R_arr_tail> xs \<tycolon> Array X \<heavy_comma> a \<tycolon> Pointer \<heavy_comma> i \<tycolon> \<nat>[size_t]\<close> \<longmapsto> \<open>a \<R_arr_tail> xs \<tycolon> Array X \<heavy_comma> gt (xs ! i) \<tycolon> Y\<close>
  for Y :: "('y::field, 'd) \<phi>"
  premises "i < length xs"
  requires idx: "FieldIndex field_index Y X gt mp"
  obtain a' j where a: "a = (a' |+ j)" by (cases a)
  \<bullet> unfold a + \<up>: idx fold a
  finish

lemmas [ \<phi>overload "\<up>" ] = i_load_n_\<phi>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]

lemma op_store[ \<phi>overload "\<down>:" ]:
  "FieldIndex field_index Y X gt mp \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store TYPE('y::field) TYPE('x) field_index
    \<lbrace> addr \<R_arr_tail> x \<tycolon> Ref X \<heavy_comma> addr \<tycolon> Pointer \<heavy_comma> y \<tycolon> Y \<longmapsto> addr \<R_arr_tail> mp (\<lambda>_. y) x \<tycolon> Ref X\<rbrace> "
  for X :: "('x::field, 'c) \<phi>"
  unfolding op_store_def Procedure_def FieldIndex_def \<phi>index_def
  apply (cases field_index, cases addr)
  apply (auto simp add: lrep_exps Let_def nu_exps split: option.split iff: addr_allocated_def)
  apply (meson MemAddrState_E addr_allocated_def disjoint_rewR domI)
  subgoal premises prems for x1 x2 x1a x2a aa ofs b x2b M h1 h2 proof -
    have t1: "\<And>v. (h1 ++ h2)(MemAddress (x1a |+ x2a) \<mapsto> v) = (h1(MemAddress (x1a |+ x2a) \<mapsto> v)) ++ h2"
      using prems by (simp add: domIff map_add_upd_left)
    have t2: "\<And>v.  dom (h1(MemAddress (x1a |+ x2a) \<mapsto> v)) = dom h1"
      using prems by auto
    show ?thesis apply (unfold t1, rule heap_split_id, unfold t2, simp add: prems)
      using prems by (auto simp add: nu_exps MemAddrState_def)
  qed done

lemmas [ \<phi>overload "\<down>" ] = op_store[THEN mp, OF FieldIndex_here, simplified]

proc i_store_n[\<phi>overload "\<down>:"]:
  \<open>a \<R_arr_tail> xs \<tycolon> Array X \<heavy_comma> a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> y \<tycolon> Y\<close> \<longmapsto> \<open>ELE a \<R_arr_tail> xs[i := mp (\<lambda>_. y) (xs ! i)] \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<phi>"
  premises "i < length xs"
  requires idx: "FieldIndex field_index Y X gt mp"
  obtain a' j where a: "a = (a' |+ j)" by (cases a) 
  \<bullet> unfold a \<rightarrow> y + y \<down>: idx fold a
  finish

lemmas [ \<phi>overload "\<down>" ] = i_store_n_\<phi>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]


section \<open>Misc\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp] split_paired_All[simp]

proc times: \<open>R' \<heavy_comma> n \<tycolon> \<nat>['b::len]\<close> \<longmapsto> \<open>R x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x n\<close>
  requires [unfolded Variant_Cast_def, simp]: "Variant_Cast vars R' R"
  requires \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P\<close>
  premises \<open>P vars 0\<close>
  requires Body: \<open>\<forall>x i. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < n \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x i \<longrightarrow>
      \<^bold>p\<^bold>r\<^bold>o\<^bold>c (body :: 'b word \<times> '\<RR>::stack \<longmapsto> '\<RR>) \<lbrace> R x \<heavy_comma> i \<tycolon> \<nat>['b] \<longmapsto> R x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. P x' (Suc i)\<rbrace>\<close>
  \<bullet> \<rightarrow> n \<open>0 \<tycolon> \<nat>['b]\<close>
  \<bullet> while var vars i in \<open>R vars\<close>, i always \<open>i \<le> n \<and> P vars i\<close>
  \<bullet> \<medium_left_bracket> dup n < \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> -- i Body i 1 + cast ie \<open>Suc i\<close> \<medium_right_bracket> drop
  finish

proc split_array[\<phi>overload split]:
  argument \<open>ptr \<R_arr_tail> l \<tycolon> Array T \<heavy_comma> ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<close>
  return \<open>ptr \<R_arr_tail> take n l \<tycolon> Array T \<heavy_comma> (ptr ||+ n) \<R_arr_tail> drop n l \<tycolon> Array T \<heavy_comma> ptr ||+ n \<tycolon> Pointer\<close>
  premises [useful]: "n \<le> length l"
  \<bullet> + split_cast n
  finish

proc pop_array[\<phi>overload pop]: \<open>ptr \<R_arr_tail> l \<tycolon> Array T \<heavy_comma> ptr \<tycolon> Pointer\<close>
  \<longmapsto> \<open>(ptr ||+ 1) \<R_arr_tail> tl l \<tycolon> Array T \<heavy_comma> ptr \<R_arr_tail> hd l \<tycolon> Ref T \<heavy_comma> ptr ||+ 1 \<tycolon> Pointer\<close>
  premises A: "l \<noteq> []"
  have [useful]: "1 \<le> length l" by (meson Premise_def length_0_conv less_one not_le A)
  \<bullet> \<open>1 \<tycolon> \<nat>[size_t]\<close> + pop_cast
  finish


section \<open>Codegen\<close>

ML_file \<open>codegen/codegen.ML\<close>
ML_file \<open>codegen/NuSys.ML\<close>
ML_file \<open>codegen/NuPrime.ML\<close>
ML_file \<open>codegen/NuLLReps.ML\<close>
ML_file \<open>codegen/misc.ML\<close>
ML_file \<open>codegen/Instructions.ML\<close>


\<phi>export_llvm

end