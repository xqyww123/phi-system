theory PhiSem_Min_Lib
  imports PhiSem_Min
begin

chapter \<open>Program Library for Minimal Semantics\<close>

section \<open>Preliminary\<close>

\<phi>overloads singular and plural
\<phi>overloads split and split_cast and merge and pop and pop_cast and push

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

abbreviation LshR (infixl "LSHR" 70) where \<open>x LSHR y \<equiv> x div 2 ^ Big y\<close>
abbreviation LshL (infixl "LSHL" 70) where \<open>x LSHL y \<equiv> x  *  2 ^ Big y\<close>

definition Bits_Tag :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix "<bits>" 25) where [iff]: \<open>(x <bits> n) = x\<close>

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

lemma (in \<phi>min) [\<phi>reason 2000 for
  \<open>PROP Synthesis_Parse (?var::varname) (?Y::?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
]:
  \<open>PROP Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T :: ('FIC_N,'FIC) assn)\<close>
  unfolding Synthesis_Parse_def ..


\<phi>processor (in \<phi>min) get_variable 5000 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close>)  \<open>
  fn (ctxt,sequent) => \<^keyword>\<open>$\<close> |-- Parse.term >> (fn var => fn () =>
    let
      val ctxt_parse = Config.put phi_synthesis_parsing true ctxt
      val term = Const(\<^const_name>\<open>get_var____\<phi>\<close>, dummyT) $ Syntax.parse_term ctxt_parse var
                  |> Syntax.check_term ctxt_parse
                  |> Thm.cterm_of ctxt
    in
      NuSys.synthesis term (ctxt,sequent)
    end)
\<close>


subsubsection \<open>Operations\<close>

ML_file_debug "library/local_value.ML"

context \<phi>min begin

paragraph \<open>Get Variable\<close>

proc (nodef) op_get_var:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  argument \<open>x \<Ztypecolon> Var vname T\<close>
  return   \<open>x \<Ztypecolon> Var vname T\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T\<close>
  \<medium_left_bracket> to_Identity op_get_var'' \<medium_right_bracket> using \<phi> by simp .

lemma [\<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> SYNTHESIS ?x <val-of-var> ?var \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> SUBGOAL G G2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y\<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G2
\<Longrightarrow> SOLVE_SUBGOAL G2
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var var TY \<lbrace> X \<longmapsto> Y\<heavy_comma> x \<Ztypecolon> Var var T \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x <val-of-var> var \<Ztypecolon> T \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Action_Tag_def
  \<medium_left_bracket> premises _ and GetVar and _ and [\<phi>reason for \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]
    GetVar op_get_var \<medium_right_bracket>. .



paragraph \<open>Set Variable\<close>

proc (nodef) op_set_var:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  argument \<open>x \<Ztypecolon> Var var T\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> U\<close>
  return   \<open>y \<Ztypecolon> Var var U\<close>
  \<medium_left_bracket> to_Identity \<open>var\<close> to_Identity op_set_var'' \<medium_right_bracket>. .

proc (nodef) op_set_var__synthesis[
  \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> SYNTHESIS ($?var := ?y) \<Ztypecolon> ?U ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> X \<longmapsto> X1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<close>
  and S[unfolded Action_Tag_def]:
        \<open>\<And>vy. \<^bold>v\<^bold>i\<^bold>e\<^bold>w X1\<heavy_comma> y \<Ztypecolon> Val vy U \<longmapsto> Y\<heavy_comma> x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> Val vy U \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA\<close>
  and [\<phi>reason for \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  and [\<phi>reason for \<open>\<phi>SemType (y \<Ztypecolon> U) ?TY\<close>]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
 goal G
argument \<open>X\<close>
return   \<open>Y\<heavy_comma> y \<Ztypecolon> Var var U \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l ($var := y) \<Ztypecolon> U\<close>
throws   E
  \<medium_left_bracket> G S op_set_var op_get_var \<medium_right_bracket>. .


paragraph \<open>Declare New Variables\<close>

proc (in \<phi>min) op_var_scope:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and BLK: \<open>\<forall>var. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> X\<heavy_comma> x \<Ztypecolon> Var var T \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> y \<Ztypecolon> Var var (U <of-type> TY)
                        \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var (\<phi>Any <of-type> TY) \<rbrace>\<close>
  argument \<open>X\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T\<close>
  return   \<open>Y\<close>
  throws   E
  \<medium_left_bracket> to_Identity op_var_scope'
    try'' \<medium_left_bracket> BLK to_Identity op_free_var \<medium_right_bracket>. \<medium_left_bracket> to_Identity op_free_var throw \<medium_right_bracket>. \<medium_right_bracket>. .

lemma "__\<phi>op_var_scope__":
  \<open> (\<And>var. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> R\<heavy_comma> x \<Ztypecolon> Var var T\<heavy_comma>  X \<longmapsto> Y (ret::'aa sem_value) \<heavy_comma> y \<Ztypecolon> Var var (U <of-type> TY)
                \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var (\<phi>Any <of-type> TY) \<rbrace>)
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TYPE('a) TY F raw \<lbrace> R\<heavy_comma> (X\<heavy_comma> x \<Ztypecolon> Val raw T) \<longmapsto> Y (ret::'aa sem_value) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding mult.assoc[symmetric]
  using op_var_scope_\<phi>app[where X=\<open>R\<heavy_comma> X\<close> and x = x and T = T and TY = TY and F=F and y=y,
            of Y U E \<open>raw\<close>, simplified]
  by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) mult.commute)

lemma "__\<phi>op_set_var__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R\<heavy_comma> y \<Ztypecolon> Var var U\<heavy_comma> X \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (op_set_var var TY raw \<ggreater> g) \<lbrace> R\<heavy_comma> (X\<heavy_comma> x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> Val raw U) \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  \<medium_left_bracket> premises G and [\<phi>reason for \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>] and [\<phi>reason for \<open>\<phi>SemType (y \<Ztypecolon> U) ?TY\<close>]
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


subsection \<open>Arithmetic Operations\<close>

\<phi>overloads "+" and "-" and "*" and "/" and "<" and "\<le>" and ">" and "\<ge>" and "=" and "\<not>"
  and "\<and>" and "\<or>"

subsubsection \<open>Boolean Arithmetic\<close>

paragraph \<open>Not\<close>

bundle unfold_Big = Big_def[iff]

lemma (in \<phi>min) op_not[\<phi>overload \<not>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_not raw \<lbrace> x \<Ztypecolon> Val raw \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l \<not> x \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_not_def
  including unfold_Big
  by (cases raw, simp, \<phi>reason)


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R1\<heavy_comma> SYNTHESIS \<not>?b \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l b \<Ztypecolon> \<bool> \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l \<not>b \<Ztypecolon> \<bool>\<close>
  \<medium_left_bracket> F1 \<not> \<medium_right_bracket> .. .

paragraph \<open>And\<close>

lemma op_and[\<phi>overload \<and>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_and (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> Val va \<bool>\<heavy_comma> b \<Ztypecolon> Val vb \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l a \<and> b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_and_def including unfold_Big
  by (cases va; cases vb; simp, \<phi>reason)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<and> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<and> y) \<Ztypecolon> \<bool>\<close>
  throws   \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 \<and> \<medium_right_bracket>. .

paragraph \<open>Or\<close>

lemma op_or[\<phi>overload \<or>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_or (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> Val va \<bool>\<heavy_comma> b \<Ztypecolon> Val vb \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l a \<or> b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_or_def including unfold_Big
  by (cases va; cases vb, simp, \<phi>reason)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<or> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<or> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 \<or> \<medium_right_bracket>. .


subsubsection \<open>Constant Integer\<close>

lemma op_const_int_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2 ^ Big b \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int b n \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_const_int_def Premise_def Synthesis_def
  by \<phi>reason

lemma [\<phi>reason 1200
    for \<open>PROP Synthesis_Parse (numeral ?n::nat) (?X :: ?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
       \<open>PROP Synthesis_Parse (1::nat) (?X :: ?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
       \<open>PROP Synthesis_Parse (0::nat) (?X :: ?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
]:
  \<open> PROP Synthesis_Parse (n \<Ztypecolon> \<nat>[32]) X
\<Longrightarrow> PROP Synthesis_Parse n X\<close>
  for X :: \<open>'ret \<Rightarrow> ('FIC_N,'FIC) assn\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200
    for \<open>PROP Synthesis_Parse ((numeral ?n::nat) <bits> ?b) (?X :: ?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
       \<open>PROP Synthesis_Parse ((1::nat) <bits> ?b) (?X :: ?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
       \<open>PROP Synthesis_Parse ((0::nat) <bits> ?b) (?X :: ?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
]:
  \<open> PROP Synthesis_Parse (n \<Ztypecolon> \<nat>[b]) X
\<Longrightarrow> PROP Synthesis_Parse (n <bits> b) X\<close>
  for X :: \<open>'ret \<Rightarrow> ('FIC_N,'FIC) assn\<close>
  unfolding Synthesis_Parse_def ..


lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l numeral ?n \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 0 \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < 2 ^ Big b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int b n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_def GOAL_CTXT_def
  using op_const_int_\<phi>app[THEN \<phi>frame, simplified] .


lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> ?R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (?n <bits> ?b') \<Ztypecolon> \<nat>[?b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R' \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (n <bits> b) \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Bits_Tag_def .


(* lemma op_const_size_t:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> Size \<rbrace>\<close>
  unfolding op_const_size_t_def Premise_def
  by (\<phi>reason, simp add: \<phi>expns Big_def) *)


(* lemma [\<phi>reason 1200
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (numeral ?n) \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 0 \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
       \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X' \<longmapsto> ?X\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> Size \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t n \<lbrace> R \<longmapsto> R\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> Size \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_def GOAL_CTXT_def
  using op_const_size_t[THEN \<phi>frame, simplified] . *)


subsubsection \<open>Integer Arithmetic\<close>

paragraph \<open>Addition\<close>

lemma op_add[\<phi>overload +]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2 ^ Big b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x + y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def Premise_def including unfold_Big
  by (cases vx; cases vy; simp, \<phi>reason)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x + ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b]  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>x + y < 2 ^ Big b\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x + y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 + \<medium_right_bracket>. .


lemma op_add_mod:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l (x + y) mod 2 ^ Big b \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_add_def including unfold_Big
  by (cases vx; cases vy; simp, \<phi>reason)



paragraph \<open>Subtraction\<close>

lemma (in \<phi>min) op_sub[\<phi>overload -]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x - y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_sub_def Premise_def including unfold_Big
  apply (cases vx; cases vy; simp, \<phi>reason)
  apply (simp add: \<phi>expns)
  by (metis Nat.add_diff_assoc2 add.commute less_imp_diff_less mod_add_self2 mod_less)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x - ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>y \<le> x\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x - y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 - \<medium_right_bracket>. .


paragraph \<open>Times\<close>

lemma op_omul[\<phi>overload *]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x * y < 2^b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_umul b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x * y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_umul_def Premise_def including unfold_Big
  by (cases vx; cases vy; simp, \<phi>reason)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x * ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  premises \<open>x*y < 2^b\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x * y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 * \<medium_right_bracket>. .



paragraph \<open>Division\<close>

lemma op_udiv[\<phi>overload /]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_udiv b (\<phi>V_pair vy vx) \<lbrace> x \<Ztypecolon> Val vx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val vy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x div y \<Ztypecolon> \<nat>[b] \<rbrace>\<close>
  unfolding op_udiv_def Premise_def
  apply (cases vx; cases vy; simp, \<phi>reason) apply (simp add: \<phi>expns)
  using div_le_dividend le_less_trans by blast

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x div ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x div y) \<Ztypecolon> \<nat>[b]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 / \<medium_right_bracket>. .

paragraph \<open>Shift\<close>

lemma op_lshr_nat_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lshr b1 b2 (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> Val raw1 \<nat>[b1] \<heavy_comma> y \<Ztypecolon> Val raw2 \<nat>[b2] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x div 2 ^ Big y \<Ztypecolon> \<nat>[b1] \<rbrace>\<close>
  unfolding op_lshr_def
  apply (cases raw1; cases raw2; simp; \<phi>reason; simp add: \<phi>expns Big_def)
  using div_le_dividend le_less_trans by blast

lemma op_lshl_nat_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x * 2 ^ Big y < 2 ^ Big b1
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lshl b1 b2 (\<phi>V_pair raw2 raw1) \<lbrace> x \<Ztypecolon> Val raw1 \<nat>[b1] \<heavy_comma> y \<Ztypecolon> Val raw2 \<nat>[b2] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x * 2 ^ Big y \<Ztypecolon> \<nat>[b1] \<rbrace>\<close>
  unfolding op_lshl_def
  by (cases raw1; cases raw2; simp; \<phi>reason; simp add: \<phi>expns Big_def)

proc [
    \<phi>reason 1300 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x LSHR ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b1] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b2] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHR y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 op_lshr_nat \<medium_right_bracket>. .

proc [
    \<phi>reason 1300 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x LSHL ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  premises \<open>x * 2 ^ Big y < 2 ^ Big b1\<close>
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b1] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b2] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x LSHL y) \<Ztypecolon> \<nat>[b1]\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 op_lshl_nat \<medium_right_bracket>. .


paragraph \<open>Less Than\<close>

lemma op_lt[\<phi>overload <]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt b (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> Val rawx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val rawy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x < y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_lt_def
  by (cases rawx; cases rawy; simp, \<phi>reason)


proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x < ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x < y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 < \<medium_right_bracket>. .

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x > ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x > y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2
    \<open>\<v>\<a>\<l>1\<close> \<open>\<v>\<a>\<l>0\<close> <
  \<medium_right_bracket>. .

(* Service Obligation !!!!! Last Day!!!! *)

paragraph \<open>Less Equal\<close>

lemma op_le[\<phi>overload \<le>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le b (\<phi>V_pair rawy rawx) \<lbrace> x \<Ztypecolon> Val rawx \<nat>[b]\<heavy_comma> y \<Ztypecolon> Val rawy \<nat>[b] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l x \<le> y \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_le_def
  by (cases rawx; cases rawy; simp, \<phi>reason)

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<le> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b]  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<le> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2 \<le> \<medium_right_bracket>. .

proc [
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<ge> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[b] \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<ge> y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1
    F2
    \<open>\<v>\<a>\<l>1\<close> \<open>\<v>\<a>\<l>0\<close> \<le> \<medium_right_bracket>. .


subsubsection \<open>General Arithmetic\<close>

paragraph \<open>Equal\<close>

lemma op_equal_\<phi>app[\<phi>overload =]:
  \<open> \<phi>SemType (a \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Equal T can_eq eq
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e can_eq a b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal TY (\<phi>V_pair rawb rawa) \<lbrace> a \<Ztypecolon> Val rawa T\<heavy_comma> b \<Ztypecolon> Val rawb T \<longmapsto> \<^bold>v\<^bold>a\<^bold>l eq a b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_equal_def
  apply (cases rawa; cases rawb; simp, \<phi>reason)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, \<phi>reason)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, \<phi>reason)
   apply (unfold \<phi>Equal_def Premise_def, simp)
  apply (rule \<phi>M_Success')
  by (\<phi>reason)

proc \<phi>__synthesis_eq[
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x = ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  assumes [\<phi>reason for \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason for \<open>\<phi>SemType (y \<Ztypecolon> T) ?TY\<close>]: \<open>\<phi>SemType (y \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason for \<open>\<phi>Equal T ?can_eq ?eq\<close>]: \<open>\<phi>Equal T can_eq (=)\<close>
  premises \<open>can_eq x y\<close>
  goal G
  argument \<open>R\<close>
  return   \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x = y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> F1 F2
  note [[\<phi>trace_reasoning]]
  ;; = \<medium_right_bracket>. .



end


subsection \<open>Branches & Loops\<close>

context \<phi>min begin


lemma op_sel_\<phi>app:
  \<open> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> B) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sel TY (\<phi>V_pair rawc (\<phi>V_pair rawb rawa))
      \<lbrace> a \<Ztypecolon> Val rawa A\<heavy_comma> b \<Ztypecolon> Val rawb B\<heavy_comma> c \<Ztypecolon> Val rawc \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l (if c then a else b) \<Ztypecolon> (if c then A else B) \<rbrace>\<close>
  unfolding op_sel_def including unfold_Big
  by (cases rawc; cases rawb; cases rawa; cases c; simp add: \<phi>SemType_def subset_iff, \<phi>reason)

lemma branch_\<phi>app:
  \<open> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>T \<lbrace> X \<longmapsto> Y\<^sub>T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>)
\<Longrightarrow> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c br\<^sub>F \<lbrace> X \<longmapsto> Y\<^sub>F \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>)
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T v) (Y\<^sub>F v) \<longmapsto> Y v \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if br\<^sub>T br\<^sub>F rawc \<lbrace> X\<heavy_comma> C \<Ztypecolon> Val rawc \<bool> \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. (E\<^sub>T e \<^bold>s\<^bold>u\<^bold>b\<^bold>j C) + (E\<^sub>F e \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> C) \<rbrace>\<close>
  unfolding op_if_def Premise_def Action_Tag_def including unfold_Big
  apply (cases rawc; cases C; simp; \<phi>reason; simp add: \<phi>expns plus_fun_def)
  using \<phi>CONSEQ view_shift_id by blast+


proc "if":
  assumes C: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c cond \<lbrace> X \<longmapsto> X1\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l C \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
      and brT: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e   C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brT \<lbrace> X1 \<longmapsto> Y\<^sub>T (ret::'a sem_value) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>T \<rbrace>\<close>
      and brF: \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e \<not> C \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c brF \<lbrace> X1 \<longmapsto> Y\<^sub>F (ret::'a sem_value) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<^sub>F \<rbrace>\<close>
      and [\<phi>reason 9999 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T ?v) (Y\<^sub>F ?v) \<longmapsto> ?Y \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
              \<open>(\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If C (Y\<^sub>T v) (Y\<^sub>F v) \<longmapsto> Y v \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)\<close>
  argument \<open>X\<close>
  return \<open>Y (ret::'a sem_value)\<close>
  throws \<open>\<lambda>e. E e + (E\<^sub>T e \<^bold>s\<^bold>u\<^bold>b\<^bold>j C) + (E\<^sub>F e \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> C)\<close>
  \<medium_left_bracket> C branch brT brF \<medium_right_bracket>. .

end


section \<open>Procedures and Operations\<close>

context \<phi>min begin

subsection \<open>Control Flow\<close>

subsubsection \<open>Loops\<close>

lemma (in \<phi>min) "__DoWhile__rule_\<phi>app":
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> (\<exists>*x'. X x' \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l P x' \<Ztypecolon> \<bool>) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding op_do_while_def \<phi>Procedure_def
  apply (simp add: subset_iff LooseStateTy_expn')
  apply (rule allI impI conjI)+
  subgoal for comp R s
  apply (rotate_tac 2)
    apply (induct body comp s rule: SemDoWhile.induct; clarsimp simp add: \<phi>expns times_list_def)
    apply fastforce
    subgoal premises prems for res f s s'' c u v proof -
      have t1: \<open>\<exists>c. (\<exists>fic. (\<exists>u v. fic = u * v \<and> u \<in> R \<and> v \<in> X c \<and> u ## v) \<and> s \<in> INTERP_RES fic) \<and> P c\<close>
        using prems(5) prems(6) prems(7) prems(8) prems(9) by blast
      show ?thesis
        apply (insert \<open>\<forall>_ _. (\<exists>_. _) \<longrightarrow> _\<close>[THEN spec[where x=s], THEN spec[where x=R], THEN mp, OF t1])
        using prems(1) prems(3) by fastforce
    qed
    apply fastforce
    by blast .

text \<open>Note the While rule we mentioned in the paper is just a special case of the above
      __DoWhile__rule_\<phi>app\<close>



lemma (in \<phi>min)
  " \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l P x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x'\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<and> \<not> P x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<rbrace>"
  using "__DoWhile__rule_\<phi>app"[where X=\<open>\<lambda>x. X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j I x\<close> and P=P,
            simplified Subjection_times, simplified] .


proc (in \<phi>min) (nodef) do_while:
assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> cond x)\<close>
    and V: \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> ( X' x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> cond x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA\<close>
    and    \<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True\<close>
assumes B: \<open>\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X' x \<longmapsto> (X' x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x') \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
argument \<open>X\<close>
return   \<open>X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> \<not> cond x'\<close>
throws E
  \<medium_left_bracket> 
  V[unfolded Action_Tag_def]
  thm "__DoWhile__rule_\<phi>app"[where P=cond and X=\<open>\<lambda>x'. X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j invariant x'\<close>, simplified]
  ;;
    "__DoWhile__rule_\<phi>app"[where P=cond and X=\<open>\<lambda>x'. X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j invariant x'\<close>, simplified]
  thm \<phi>
  \<medium_left_bracket>
  ;; B \<medium_right_bracket>.
  \<medium_right_bracket> by simp .

proc while:
  assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ( X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x)\<close>
  assumes V[unfolded Action_Tag_def]:
           "\<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA"
    and    \<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True\<close>
    and C: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<lbrace> X x \<longmapsto> X x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond \<Ztypecolon> Predicate_About x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace>"
    and B: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<lbrace> X x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace>"
  argument \<open>X'\<close>
  return \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. \<not> cond x\<close>
  \<medium_left_bracket> V \<exists>x C \<exists>x1 branch \<medium_left_bracket>
    do_while \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. invariant vars \<and> cond vars\<close>
      \<medium_left_bracket> B \<exists>x2 C \<medium_right_bracket>.
    \<medium_right_bracket>.
    \<medium_left_bracket> \<medium_right_bracket> for \<open>X vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j vars. invariant vars \<and> \<not> cond vars\<close> ..
  \<medium_right_bracket> using \<phi> by simp .


(*Example*)


proc AA:
  argument \<open>\<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 2 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 3 \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l 6 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 4 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 2 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket> + + 4 2 1 - 1 + 30000 * 30000 /  \<medium_right_bracket>. .

thm op_const_int_\<phi>app
thm AA_\<phi>compilation


(*
int XX(int x) { if 0 < x then x - 1 else 0 }
*)
proc XX:
  argument \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l x - 1 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket>  \<rightarrow> varx
  ;; (*assign the value x to a variable named varx*)
     (* command `;;` leads a statement, or ends the previous statement. *)
    if \<medium_left_bracket> \<open>0 < $varx\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>$varx - 1\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>0::nat\<close> \<medium_right_bracket>.
    (* the cartouche like \<open>0 < $varx\<close> invokes a synthesis process
       to make that value automatically *)
  \<medium_right_bracket> using \<phi> by simp .

proc
  premises \<open>x < 10\<close>
  argument \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l 10 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket> \<rightarrow> v ;;
    while
  note [[\<phi>trace_reasoning]]
  ;; \<open>x \<Ztypecolon> _ \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. x \<le> 10\<close> (* x is variable during the loop and it meets an invariant x \<le> 10  *)
  ;;
    \<medium_left_bracket> \<open>$v < 10\<close> \<medium_right_bracket>. (*condition body of the loop*)
    \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v \<medium_right_bracket>. (*loop body*) ;; (* this ;; leads an empty statement which does nothing but simplification *)
    $v
  \<medium_right_bracket>. .

end

end
