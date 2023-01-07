theory PhiSem_Variable_Lib
  imports PhiSem_Variable
begin

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

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (?var::varname) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..


\<phi>processor get_variable 5000 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close>)  \<open>
  fn (ctxt,sequent) => \<^keyword>\<open>$\<close> |-- Parse.term >> (fn var => fn () =>
    let
      val ctxt_parse = Config.put phi_synthesis_parsing true ctxt
      val term = Const(\<^const_name>\<open>get_var____\<phi>\<close>, dummyT) $ Syntax.parse_term ctxt_parse var
                  |> Syntax.check_term ctxt_parse
                  |> Thm.cterm_of ctxt
    in
      Phi_Sys.synthesis term (ctxt,sequent)
    end)
\<close>


subsubsection \<open>Operations\<close>

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


declare [[ML_print_depth=1000, eta_contract=false]]

proc op_var_scope:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and BLK: \<open>\<forall>var. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> X\<heavy_comma> x \<Ztypecolon> Var var T \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> () \<Ztypecolon> Var var (\<phi>Any <of-type> TY)
                    \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var (\<phi>Any <of-type> TY) \<rbrace>\<close>
  argument \<open>X\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T\<close>
  return   \<open>Y\<close>
  throws   E
  \<medium_left_bracket> to_Identity op_var_scope'
    try'' \<medium_left_bracket> BLK to_Identity op_free_var \<medium_right_bracket>. \<medium_left_bracket> to_Identity op_free_var throw \<medium_right_bracket>. \<medium_right_bracket>. .

lemma "__\<phi>op_var_scope__":
  \<open> (\<And>var. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> R\<heavy_comma> x \<Ztypecolon> Var var T\<heavy_comma>  X \<longmapsto> \<lambda>ret. Y ret \<heavy_comma> () \<Ztypecolon> Var var (\<phi>Any <of-type> TY)
                \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var (\<phi>Any <of-type> TY) \<rbrace>)
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TYPE('a) TY F raw \<lbrace> R\<heavy_comma> (X\<heavy_comma> x \<Ztypecolon> Val raw T) \<longmapsto> \<lambda>ret. Y ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding mult.assoc[symmetric]
  using op_var_scope_\<phi>app[where X=\<open>R\<heavy_comma> X\<close> and x = x and T = T and TY = TY and F=F,
            of Y E \<open>raw\<close>, simplified]
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

ML_file_debug "library/local_value.ML"

\<phi>processor assign_variable 7500 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S\<close>) \<open>
  fn (ctxt,sequent) => ((\<^keyword>\<open>\<rightarrow>\<close> |-- Parse.list1 Parse.binding)
>> (fn vars => fn () =>
  raise NuProcessor.Terminate_Process (Local_Value.mk_var_scope vars (ctxt,sequent), I)))
\<close>


end
