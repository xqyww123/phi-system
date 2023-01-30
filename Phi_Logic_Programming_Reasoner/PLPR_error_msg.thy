(*There is still a design under consideration.

It intends to give a rich way with term quotations to represent and report
  error messages in the logic programming based reasoning.
*)

theory PLPR_error_msg
  imports Phi_Logic_Programming_Reasoner
begin

section \<open>Error Reporting\<close>

subsection \<open>Encoding of Text\<close>

typedecl "text"

setup \<open>Sign.mandatory_path "text"\<close>

consts literal :: \<open>(text \<Rightarrow> text) \<Rightarrow> text\<close>
       "term"  :: \<open>'a::{} \<Rightarrow> text\<close>
       type    :: \<open>'a::{} itself \<Rightarrow> text\<close>
       cat     :: \<open>text \<Rightarrow> text \<Rightarrow> text\<close>
       newline :: \<open>text\<close>
      "text"    :: \<open>text \<Rightarrow> text\<close>

setup \<open>Sign.parent_path\<close>

text \<open>We use the name of a lambda variable to encode an arbitrary string text.\<close>

nonterminal "text_"
syntax "_text_" :: \<open>text_ \<Rightarrow> text\<close> ("TEXT'(_')" [1] 1000)
syntax "_text_literal_" :: \<open>cartouche \<Rightarrow> text_\<close> ("_")
syntax "_text_term_" :: \<open>logic \<Rightarrow> text_\<close> ("_" [1000] 999)
syntax "_text_prop_" :: \<open>prop \<Rightarrow> text_\<close> ("_" [1000] 999)
syntax "_text_newline_" :: \<open>text_\<close> ("\<newline>")
syntax "_text_cat_" :: \<open>text_ \<Rightarrow> text_ \<Rightarrow> text_\<close> ("_ _" [1,2] 1)

ML \<open>
structure Text_Encoding = struct

val escape_string   = String.translate (fn #"." => "\001" | x => str x)
val recovery_string = String.translate (fn #"\001" => "." | x => str x)

local open Ast
  fun dest_literal (Appl [Constant \<^syntax_const>\<open>_constrain\<close>, x, _]) = dest_literal x
    | dest_literal (Appl [Constant \<^syntax_const>\<open>_bound\<close>, x]) = dest_literal x
    | dest_literal (Variable x) = recovery_string x

fun decode_text_ast' ret (Appl [Constant \<^const_syntax>\<open>text.literal\<close>,
      Appl [Constant \<^syntax_const>\<open>_abs\<close>, x, _]])
      = Variable (cartouche (dest_literal x))::ret
  | decode_text_ast' ret (Appl [Constant \<^const_syntax>\<open>text.term\<close>, tm])
      = tm::ret
  | decode_text_ast' ret (Appl [Constant \<^const_syntax>\<open>text.type\<close>, tm])
      = tm::ret
  | decode_text_ast' ret (Constant \<^const_syntax>\<open>text.newline\<close>)
      = (Constant \<^syntax_const>\<open>_text_newline_\<close>)::ret
  | decode_text_ast' ret (Appl [Constant \<^const_syntax>\<open>text.cat\<close>, tmA, tmB])
      = decode_text_ast' (decode_text_ast' ret tmB) tmA
  | decode_text_ast' _ ast = raise AST ("decode_text_ast", [ast])

in

fun decode_text _ (\<^const>\<open>text.literal\<close> $ Abs (text, _, _)) = [Pretty.str (recovery_string text)]
  | decode_text ctxt (Const (\<^const_name>\<open>text.term\<close>, _) $ x) = [Syntax.pretty_term ctxt x]
  | decode_text ctxt (Const (\<^const_name>\<open>text.type\<close>, _) $ \<^Const_>\<open>Pure.type T\<close>) =
      [Syntax.pretty_typ ctxt T]
  | decode_text ctxt (\<^const>\<open>text.cat\<close> $ A $ B) =
      decode_text ctxt A @ decode_text ctxt B
  | decode_text _ (\<^const>\<open>text.newline\<close>) = [Pretty.brk 0]
  | decode_text ctxt (\<^const>\<open>text.text\<close> $ X) = decode_text ctxt X
  | decode_text _ tm = raise TERM ("decode_text", [tm])

fun decode_text_pretty ctxt X = Pretty.block (Pretty.separate "" (decode_text ctxt X))
fun decode_text_str ctxt X = Pretty.string_of (decode_text_pretty ctxt X)

fun decode_text_ast ast =
  case decode_text_ast' [] ast
    of [] => Variable ""
     | [x] => x
     | l => Appl l

end
end
\<close>

parse_ast_translation \<open>
let open Ast
  fun dest_literal (Appl [Constant \<^syntax_const>\<open>_constrain\<close>, x, _]) = dest_literal x
    | dest_literal (Appl [Constant \<^syntax_const>\<open>_text_literal_\<close>, x]) = dest_literal x
    | dest_literal (Variable x) = String.substring (x, 7, size x - 15)
        (*7 for size of \ <open> and 15 for size of \ <open> \ <close>*)
  fun encode_literal str =
    Appl [Constant \<^const_syntax>\<open>text.literal\<close>,
    Appl [Constant \<^syntax_const>\<open>_abs\<close>,
      Appl [Constant \<^syntax_const>\<open>_constrain\<close>,
            Variable (Text_Encoding.escape_string str),
            Constant \<^type_syntax>\<open>text\<close>],
      Appl [Constant \<^syntax_const>\<open>_constrain\<close>,
            Constant \<^const_syntax>\<open>undefined\<close>,
            Constant \<^type_syntax>\<open>text\<close>]]]
  fun parse (Appl [Constant \<^syntax_const>\<open>_text_literal_\<close>, tm]) = encode_literal (dest_literal tm)
    | parse (Appl [Constant \<^syntax_const>\<open>_text_prop_\<close>, tm]) =
        parse (Appl [Constant \<^syntax_const>\<open>_text_term_\<close>, tm])
    | parse (Appl [Constant \<^syntax_const>\<open>_text_term_\<close>,
                       (tm as Appl [Constant \<^syntax_const>\<open>_TYPE\<close>, _])]) =
        Appl [Constant \<^const_syntax>\<open>text.type\<close>, tm]
    | parse (Appl [Constant \<^syntax_const>\<open>_text_term_\<close>, tm]) =
        Appl [Constant \<^const_syntax>\<open>text.term\<close>, tm]
    | parse (Constant \<^syntax_const>\<open>_text_newline_\<close>) = Constant \<^const_syntax>\<open>text.newline\<close>
    | parse (Appl [Constant \<^syntax_const>\<open>_text_cat_\<close>, tmA, tmB]) =
        Appl [Constant \<^const_syntax>\<open>text.cat\<close>, parse tmA, parse tmB]
in
  [(\<^syntax_const>\<open>_text_\<close>, (fn ctxt => fn [ast] =>
        Appl [Constant \<^const_syntax>\<open>text.text\<close>, parse ast]))]
end\<close>

print_ast_translation \<open>[(\<^const_syntax>\<open>text.text\<close>, (fn ctxt => fn [ast] =>
  Ast.Appl [Ast.Constant \<^syntax_const>\<open>_text_\<close>, Text_Encoding.decode_text_ast ast]))]\<close>


subsection \<open>Reasoners for Printing Message\<close>

subsubsection \<open>Tracing\<close>

definition TRACING :: \<open>text \<Rightarrow> bool\<close>
  where [iff]: \<open>TRACING x \<longleftrightarrow> True\<close>

lemma TRACING_I: \<open>TRACING x\<close>
  unfolding TRACING_def ..

\<phi>reasoner_ML TRACING 1200 (\<open>TRACING ?x\<close>) = \<open>fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>TRACING\<close> $ text)
          = Thm.major_prem_of sequent
    val str = Text_Encoding.decode_text_str ctxt text
    val _ = tracing str
  in Seq.single (ctxt, @{thm TRACING_I} RS sequent)
  end\<close>

subsubsection \<open>Warning\<close>

definition WARNING :: \<open>text \<Rightarrow> bool\<close>
  where [iff]: \<open>WARNING x \<longleftrightarrow> True\<close>

lemma WARNING_I: \<open>WARNING x\<close>
  unfolding WARNING_def ..

\<phi>reasoner_ML WARNING 1200 (\<open>WARNING ?x\<close>) = \<open>fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>WARNING\<close> $ text)
          = Thm.major_prem_of sequent
    val str = Text_Encoding.decode_text_str ctxt text
    val _ = warning str
  in Seq.single (ctxt, @{thm WARNING_I} RS sequent)
  end\<close>

subsubsection \<open>Fail\<close>

text \<open>Fail ends the current search branch but does not terminate
 the whole reasoning.\<close>

definition FAIL :: \<open>text \<Rightarrow> bool\<close>
  where [iff]: \<open>FAIL x \<longleftrightarrow> False\<close>

definition FAIL' :: \<open>text \<Rightarrow> prop\<close>
  where [iff]: \<open>FAIL' x \<equiv> (\<And>P. PROP P)\<close>

\<phi>reasoner_ML FAIL 1200 (\<open>FAIL ?x\<close> | \<open>PROP FAIL' ?x'\<close>) = \<open>fn (ctxt,sequent) =>
  let
    val text = case Thm.major_prem_of sequent
                 of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>FAIL\<close> $ X) => X
                  | \<^const>\<open>FAIL'\<close> $ X => X
    val str = Text_Encoding.decode_text_str ctxt text
    val _ = warning str
  in Seq.empty
  end\<close>


subsubsection \<open>Error\<close>

text \<open>Fail terminates the whole reasoning.\<close>

definition ERROR :: \<open>text \<Rightarrow> bool\<close>
  where [iff]: \<open>ERROR x \<longleftrightarrow> False\<close>

definition ERROR' :: \<open>text \<Rightarrow> prop\<close>
  where [iff]: \<open>ERROR' x \<equiv> (\<And>P. PROP P)\<close>

\<phi>reasoner_ML ERROR 1200 (\<open>ERROR ?x\<close> | \<open>PROP ERROR' ?x'\<close>) = \<open>fn (ctxt,sequent) =>
  let
    val text = case Thm.major_prem_of sequent
                 of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>ERROR\<close> $ X) => X
                  | \<^const>\<open>ERROR'\<close> $ X => X
    val str = Text_Encoding.decode_text_str ctxt text
    val _ = error str
  in Seq.empty
  end\<close>

end