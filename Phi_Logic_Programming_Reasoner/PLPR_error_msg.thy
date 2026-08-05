(*There is still a design under consideration.

It intends to give a rich way with term quotations to represent and report
  error messages in the logic programming based reasoning.
*)

theory PLPR_error_msg
  imports Main
  abbrevs "<or>" = "\<o>\<r>"
      and "<fail>" = "\<f>\<a>\<i>\<l>"
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
(*Since Isabelle2025 the head constant of an application carrying mixfix syntax is wrapped in a
  constraint recording the source positions of the mixfix delimiters, so ML that pattern-matches
  such a head no longer sees a bare \<^ML>\<open>Const\<close>.  The wrapper appears as a binary \<open>_constrain\<close>
  inside a term-level parse translation, as a unary \<open>_type_constraint_\<close> in the output of
  \<^ML>\<open>Syntax.parse_term\<close>, and as a nested \<open>_constrain\<close> head at ast level.  It is consumed by
  \<^ML>\<open>Syntax.check_term\<close>, so checked terms are unaffected.

  A constraint node carries either positional bookkeeping or a genuine type ascription written by
  the user; the two are told apart not by the wrapper's name but by whether the type slot holds an
  encoded position.  The parse-side operations below are therefore STRICT: they see through
  positional wrappers only, and stop at a genuine ascription, which reproduces the behaviour of
  Isabelle2024.  The print side is different -- there a \<open>_constrain\<close> is always a tool-inserted type
  annotation -- so \<^ML>\<open>Phi_Syntax_Constraint.strip_constraint_ast\<close> is permissive.  Isabelle
  parameterizes exactly this distinction itself, in \<^ML>\<open>Ast.const_match\<close>.*)
structure Phi_Syntax_Constraint = struct

(*peels positional wrappers off the top; peels wrapper-shaped applications only, never a genuine
  application, so a head test built on it cannot fire on an over-applied constant*)
fun strip_pos (t as Const ("_type_constraint_", Type ("fun", [A, B])) $ x) =
      if A = B andalso not (null (Term_Position.decode_positionT A))
      then strip_pos x else t
  | strip_pos (t as Const ("_constrain", _) $ x $ v) =
      if Term_Position.detect_position v then strip_pos x else t
  | strip_pos t = t

(*constraint-aware \<^ML>\<open>Term.strip_comb\<close>: peels wrappers at every level of the spine, so that a
  wrapped head is not torn apart by the decomposition.  It hands the head back TWICE -- peeled, to
  see which constant it is, and unpeeled, so that \<^ML>\<open>Term.list_comb\<close> puts the term back together
  with the wrapper, and the source markup it carries, in place.  Rebuild from the second one; a
  freshly made \<^ML>\<open>Const\<close> would silently drop that markup.*)
fun dest_comb_pos t =
  let fun go t args =
        (case strip_pos t of
           f $ x => go f (x :: args)
         | bare => (bare, t, args))
   in go t [] end

fun strip_comb_pos t = (case dest_comb_pos t of (bare, _, args) => (bare, args))

fun head_const_name t = (case strip_pos t of Const (c, _) => SOME c | _ => NONE)

fun is_head names t =
  (case head_const_name t of SOME c => member (op =) names c | NONE => false)

(*for TYPE COMPUTATION only.  It must never be applied to a term that is stored into, or looked up
  in, a value list: positions are distinct per occurrence, so normalizing a value term would merge
  two occurrences of one name into one and silently change a procedure's arity.*)
fun strip_pos_deep t =
  (case strip_pos t of
     u $ v => strip_pos_deep u $ strip_pos_deep v
   | Abs (x, T, u) => Abs (x, T, strip_pos_deep u)
   | u => u)

(*print side: permissive, as \<^ML>\<open>Ast.const_match\<close> is with \<open>permissive_constraints\<close> set*)
fun strip_constraint_ast (Ast.Appl (Ast.Appl [Ast.Constant "_constrain", c, _] :: args)) =
      strip_constraint_ast (Ast.mk_appl c args)
  | strip_constraint_ast (Ast.Appl [Ast.Constant "_constrain", c, _]) = strip_constraint_ast c
  | strip_constraint_ast ast = ast

end
\<close>

ML \<open>
structure Text_Encoding = struct

val escape_string   = String.translate (fn #"." => "\001" | x => str x)
val recovery_string = String.translate (fn #"\001" => "." | x => str x)

local open Ast
  fun dest_literal (Appl [Constant \<^syntax_const>\<open>_constrain\<close>, x, _]) = dest_literal x
    | dest_literal (Appl [Constant \<^syntax_const>\<open>_bound\<close>, x]) = dest_literal x
    | dest_literal (Variable x) = recovery_string x

  (*this runs on the print side, where a \<open>_constrain\<close> is always a tool-inserted type annotation,
    so the permissive form is the right one*)
  val drop_constraint = Phi_Syntax_Constraint.strip_constraint_ast

fun decode_text_ast' ret ast = decode_text_ast'' ret (drop_constraint ast)

and decode_text_ast'' ret (Appl [Constant \<^const_syntax>\<open>text.literal\<close>,
      Appl [Constant \<^syntax_const>\<open>_abs\<close>, x, _]])
      = Variable (cartouche (dest_literal x))::ret
  | decode_text_ast'' ret (Appl [Constant \<^const_syntax>\<open>text.term\<close>, tm])
      = tm::ret
  | decode_text_ast'' ret (Appl [Constant \<^const_syntax>\<open>text.type\<close>, tm])
      = tm::ret
  | decode_text_ast'' ret (Constant \<^const_syntax>\<open>text.newline\<close>)
      = (Constant \<^syntax_const>\<open>_text_newline_\<close>)::ret
  | decode_text_ast'' ret (Appl [Constant \<^const_syntax>\<open>text.cat\<close>, tmA, tmB])
      = decode_text_ast' (decode_text_ast' ret tmB) tmA
  | decode_text_ast'' _ ast = raise AST ("decode_text_ast", [ast])

in

(*deterministic decoding to plain string*)
fun decode_str _ (\<^const>\<open>text.literal\<close> $ Abs (text, _, _)) = recovery_string text
  | decode_str ctxt (\<^const>\<open>text.cat\<close> $ A $ B) =
      decode_str ctxt A ^ " " ^ decode_str ctxt B
  | decode_str _ (\<^const>\<open>text.newline\<close>) = "\n"
  | decode_str ctxt (\<^const>\<open>text.text\<close> $ X) = decode_str ctxt X
  | decode_str _ tm = raise TERM ("decode_str", [tm])

fun decode_text _ (\<^const>\<open>text.literal\<close> $ Abs (text, _, _)) = (Pretty.text (recovery_string text))
  | decode_text ctxt (Const (\<^const_name>\<open>text.term\<close>, _) $ x) = [Syntax.pretty_term ctxt x]
  | decode_text ctxt (Const (\<^const_name>\<open>text.type\<close>, _) $ \<^Const_>\<open>Pure.type T\<close>) =
      [Syntax.pretty_typ ctxt T]
  | decode_text ctxt (\<^const>\<open>text.cat\<close> $ A $ B) =
      decode_text ctxt A @ [Pretty.brk 1] @ decode_text ctxt B
  | decode_text _ (\<^const>\<open>text.newline\<close>) = [Pretty.fbrk]
  | decode_text ctxt (\<^const>\<open>text.text\<close> $ X) = decode_text ctxt X
  | decode_text _ tm = raise TERM ("decode_text", [tm])

fun decode_text_pretty ctxt X = Pretty.block (decode_text ctxt X)
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

definition TRACING :: \<open>text \<Rightarrow> bool\<close> where \<open>TRACING x \<longleftrightarrow> True\<close>

text \<open>The message is printed only when \<^verbatim>\<open>\<phi>trac_reasoning \<ge> 1\<close>.
      \<^verbatim>\<open>declare [[\<phi>trac_reasoning = 1]]\<close>\<close>

lemma TRACING_I: \<open>TRACING x\<close>
  unfolding TRACING_def ..

subsubsection \<open>Warning\<close>

definition WARNING :: \<open>text \<Rightarrow> bool\<close> where \<open>WARNING x \<longleftrightarrow> True\<close>

lemma WARNING_I: \<open>WARNING x\<close>
  unfolding WARNING_def ..

subsubsection \<open>Fail\<close>

text \<open>Fail ends the current search branch but does not terminate
 the whole reasoning.\<close>

definition FAIL :: \<open>text \<Rightarrow> bool\<close> where \<open>FAIL x \<longleftrightarrow> False\<close>

definition FAIL' :: \<open>text \<Rightarrow> prop\<close> where \<open>FAIL' x \<equiv> (\<And>P. PROP P)\<close>

definition OR_FAIL :: \<open>bool \<Rightarrow> text \<Rightarrow> bool\<close> (infix "\<o>\<r> \<f>\<a>\<i>\<l>" 10)
    where \<open>OR_FAIL P text \<longleftrightarrow> P\<close>

subsubsection \<open>Traced Fail\<close>

text \<open>A debug tracing printed only when \<^verbatim>\<open>\<phi>trac_reasoning \<ge> 1\<close>.\<close>

definition TRACE_FAIL :: \<open>text \<Rightarrow> bool\<close> where \<open>TRACE_FAIL x \<longleftrightarrow> False\<close>

definition TRACE_FAIL' :: \<open>text \<Rightarrow> prop\<close> where \<open>TRACE_FAIL' x \<equiv> (\<And>P. PROP P)\<close>


subsubsection \<open>Error\<close>

text \<open>Fail terminates the whole reasoning.\<close>

definition ERROR :: \<open>text \<Rightarrow> bool\<close> where \<open>ERROR x \<longleftrightarrow> False\<close>

(*TODO: depreciate these*)
definition ERROR' :: \<open>text \<Rightarrow> prop\<close> where \<open>ERROR' x \<equiv> (\<And>P. PROP P)\<close>

subsubsection \<open>Exception\<close>

definition EXCEPTION :: \<open>text \<Rightarrow> bool\<close> where \<open>EXCEPTION x \<longleftrightarrow> False\<close>

end