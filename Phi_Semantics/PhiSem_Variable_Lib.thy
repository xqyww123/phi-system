theory PhiSem_Variable_Lib
  imports PhiSem_Typed_Variable
  keywords "val" :: quasi_command
begin

section \<open>Basic Operations\<close>

subsection \<open>Variable\<close>

(*

 *)

subsubsection \<open>Syntax\<close>

\<phi>processor decl_variable 5000 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close>)  \<open>
  fn (ctxt,sequent) => \<^keyword>\<open>var\<close> |-- Parse.term >> (fn var => fn () =>
    let
      val ctxt_parse = Config.put phi_synthesis_parsing true ctxt
      val term = Const(\<^const_name>\<open>get_var____\<phi>\<close>, dummyT) $ Syntax.parse_term ctxt_parse var
                  |> Syntax.check_term ctxt_parse
                  |> Thm.cterm_of ctxt
    in
      Phi_Sys.synthesis term (ctxt,sequent)
    end)
\<close>


(*
syntax "__var__" :: "idt \<Rightarrow> logic" ("\<^bold>v\<^bold>a\<^bold>r _" [1000] 999)

parse_ast_translation \<open>
  let open Ast
    fun mk_Var name =
      Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>,
        Appl [Variable "Var", name, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>]]
   in [(\<^syntax_const>\<open>__var__\<close>, fn ctxt => fn [name] => mk_Var name)]
  end
\<close> *)

(* syntax "__get_var__" :: "idt \<Rightarrow> logic" ("$_" [1000] 999)
consts "get_var____\<phi>" :: "varname \<Rightarrow> 'b"

translations "$x" => "CONST get_var____\<phi> x"
*)

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (?var::varname) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..



subsubsection \<open>Operations\<close>

paragraph \<open>Get Variable\<close>

proc (nodef) op_get_var:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  argument \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T\<close>
  return   \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close>
  \<medium_left_bracket> to_Identity op_get_var'' \<medium_right_bracket> using \<phi> by simp .

lemma [\<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> SYNTHESIS ?x <val-of> ?var \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> SUBGOAL G G2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y\<heavy_comma> \<blangle> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G2
\<Longrightarrow> SOLVE_SUBGOAL G2
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var var TY \<lbrace> X \<longmapsto> Y\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x <val-of> var \<Ztypecolon> T \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Action_Tag_def
  \<medium_left_bracket> premises _ and GetVar and _ and [\<phi>reason for \<open>\<phi>SemType (x \<Ztypecolon> T) ?TY\<close>]
    GetVar op_get_var \<medium_right_bracket>. .



paragraph \<open>Set Variable\<close>

consts infer_var_type :: \<open>unit action\<close>

lemma [\<phi>reason 1000]:
  \<open> varname.type var \<equiv> TY'
\<Longrightarrow> pred_option ((=) TY) TY' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type
\<Longrightarrow> pred_option ((=) TY) (varname.type var) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type\<close>
  \<comment> \<open>TY is the output. The rule invokes evaluation of the \<open>varname.type var\<close>.\<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open>pred_option ((=) TY) None \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type\<close>
  \<comment> \<open>the output TY can be anything freely\<close>
  by simp

lemma [\<phi>reason 1000 for \<open>pred_option ((=) ?TY') (Some ?TY) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type\<close>]:
  \<open>pred_option ((=) TY) (Some TY) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type\<close>
  \<comment> \<open>the output TY equals to that TY in \<open>Some TY\<close> exactly.\<close>
  by simp

lemma
  \<open>pred_option (\<lambda>TY'. TY = TY') None\<close>
  \<open>pred_option (\<lambda>TY'. TY = TY') (Some TY)\<close>
  by simp+

proc (nodef) op_set_var:
  assumes [unfolded Action_Tag_def, useful]:
      \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type\<close>
  assumes [unfolded \<phi>SemType_def subset_iff, useful]:
      \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  argument \<open>x \<Ztypecolon> Var var T\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> U\<close>
  return   \<open>y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<close>
  \<medium_left_bracket> to_Identity 
    $y to_Identity
    op_set_var'' 
  \<medium_right_bracket>. .

schematic_goal op_set_var__synthesis[
  \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> SYNTHESIS (?y <set-to> ?var) \<Ztypecolon> ?U ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> X \<longmapsto> X1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<close>
  and S[unfolded Action_Tag_def]:
         \<open>\<And>vy. \<^bold>v\<^bold>i\<^bold>e\<^bold>w X1\<heavy_comma> y \<Ztypecolon> Val vy U \<longmapsto> Y\<heavy_comma> x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> Val vy U \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA\<close>
  and P: \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type\<close>
  and [\<phi>reason for \<open>\<phi>SemType (y \<Ztypecolon> U) ?TY\<close>]:
         \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
shows \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?FF \<lbrace> X \<longmapsto> Y\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (y <set-to> var) \<Ztypecolon> U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  \<medium_left_bracket> G S op_set_var P op_get_var \<medium_right_bracket>. .



paragraph \<open>Declare New Variables\<close>

proc op_var_scope:
  assumes BLK: \<open>\<And>var. varname.type var \<equiv> TY
                  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> X\<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[var] \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                      \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>\<close>
  argument \<open>X\<close>
  return   \<open>Y\<close>
  throws   E
  \<medium_left_bracket> op_var_scope'[where TY=TY]
    try''
    \<medium_left_bracket> premises [\<phi>reason]
      BLK to_Identity op_free_var
    \<medium_right_bracket>.
    \<medium_left_bracket> to_Identity op_free_var throw \<medium_right_bracket>.
    \<medium_right_bracket>. .

  thm op_var_scope_\<phi>compilation

lemma "__set_var_rule__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<heavy_comma> X \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> pred_option (\<lambda>TY'. TY = TY') (varname.type var) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> infer_var_type
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (op_set_var var TY raw \<ggreater> g) \<lbrace> R\<heavy_comma> (X\<heavy_comma> x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] U) \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  \<medium_left_bracket> premises G and P and [\<phi>reason for \<open>\<phi>SemType (y \<Ztypecolon> U) ?TY\<close>]
    op_set_var P G \<medium_right_bracket>. .

lemma "__set_new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> Some TY
              \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                         \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>)
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TYPE('a) (Some TY) (\<lambda>var. op_set_var var TY raw \<ggreater> g)
     \<lbrace> R\<heavy_comma> (X \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] U) \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  \<medium_left_bracket> premises G and [\<phi>reason]
    op_var_scope[where TY=\<open>Some TY\<close>] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      $y op_set_var G
    \<medium_right_bracket>.
  \<medium_right_bracket>. .

lemma "__set_new_var_noty_rule__":
  \<open> (\<And>var. varname.type var \<equiv> None
              \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                         \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>)
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TYPE('a) None (\<lambda>var. op_set_var var TY raw \<ggreater> g)
     \<lbrace> R\<heavy_comma> (X \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] U) \<longmapsto> Z \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  \<medium_left_bracket> premises G and [\<phi>reason for \<open>\<phi>SemType (y \<Ztypecolon> U) _\<close>]
    op_var_scope[where TY=None] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      $y op_set_var G
    \<medium_right_bracket>.
  \<medium_right_bracket>. .


lemma "__value_access_0__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R\<heavy_comma> Void \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  by fastforce

lemma
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_. Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s Any \<rbrace>
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y\<close>
  unfolding \<phi>Procedure_def View_Shift_def Return_def det_lift_def
  by (simp add: \<phi>expns)

lemma
  \<open> (sem_value.dest v \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R \<longmapsto> R' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<longmapsto> R' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_def
  by (clarsimp simp add: \<phi>expns)


lemma
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R \<longmapsto> R' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<longmapsto> \<lambda>ret. R' ret \<^bold>s\<^bold>u\<^bold>b\<^bold>j sem_value.dest v \<in> (x \<Ztypecolon> T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_def
  by (clarsimp simp add: \<phi>expns)


thm "__\<phi>op_set_var__"[OF "__\<phi>op_set_var__" [OF "__\<phi>op_var_scope__0"]]

term \<open>x.x.x.x := xx\<close>


ML_file_debug "library/local_value.ML"

\<phi>processor assign_variable 7500 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S\<close>) \<open>
  fn (ctxt,sequent) => ((\<^keyword>\<open>\<rightarrow>\<close> |-- Parse.list1 Parse.binding)
>> (fn vars => fn () =>
  raise NuProcessor.Terminate_Process (Local_Value.mk_var_scope vars (ctxt,sequent), I)))
\<close>

lemma [\<phi>reason 1]:
  \<open>FAIL TEXT(\<open>Fail to reason the semantic type of\<close> X)
\<Longrightarrow> \<phi>SemType X Any\<close>
  by blast

proc
  assumes [\<phi>reason for \<open>\<phi>SemType (x \<Ztypecolon> T) _ \<close>]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  argument \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l U\<close>
  return \<open>xxxx\<close>
  \<medium_left_bracket>
  ;; $x \<rightarrow> xx
  ;;  $\<a>\<r>\<g>1
  ;; \<open>$1\<close> \<open>$(\<a>\<r>\<g>1)\<close>
  ;; \<open>$2 := xx\<close>

end
