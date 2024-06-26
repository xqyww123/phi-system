(* FILE: library/syntax/name_by_type.ML
   AUTHOR: Qiyuan Xu

   Syntax tools for named type tag.
*)

signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_name_tylabels : typ -> string list (* 'i \<times> 'j \<times> 'k -> ["i","j","k"] *)
  val mk_name_tylabels : string list -> typ (* ["i","j","k"] -> 'i \<times> 'j \<times> 'k *)
  val mk_name_tag_ast : (Ast.ast * string list) -> Ast.ast

  val mk_namedT : typ -> string list -> typ
  val dest_namedT : typ -> (string * typ) list
  val dest_namedT_only_names : typ -> string list

  val mk_named_tag : term -> typ -> term

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

val tylabel_NAME = "'name_"
val tylabel_name = prefix tylabel_NAME
val tylabel_name_size = String.size tylabel_NAME

fun mk_name_tylabels names =
      HOLogic.mk_tupleT (map (fn x => TFree (tylabel_name x, [\<^class>\<open>type\<close>])) names)
fun trim_tylabel_name name =
  if String.isPrefix tylabel_NAME name
  then String.substring(name, tylabel_name_size, size name - tylabel_name_size)
  else ""

local open Ast in

fun strip_tupargs (Appl [Constant \<^syntax_const>\<open>_tuple_arg\<close>,
                     Appl [Constant \<^syntax_const>\<open>_constrain\<close>, Variable x, _]]) = [x]
  | strip_tupargs (Appl [Constant \<^syntax_const>\<open>_tuple_args\<close>,
                     Appl [Constant \<^syntax_const>\<open>_constrain\<close>, Variable x, _],
                     r]) = x::strip_tupargs r

fun mk_name_tylabels_ast names =
      Appl [Constant \<^type_syntax>\<open>named\<close>,
            Constant \<^type_syntax>\<open>dummy\<close>,
            fold_ast \<^type_syntax>\<open>prod\<close>
              (map (fn x => Variable (tylabel_name x)) names)
           ]

fun mk_name_tag_ast (term,names) =
  Appl [Constant \<^syntax_const>\<open>_constrain\<close>,
        term,
        mk_name_tylabels_ast names]
end

fun mk_namedT T names = Type(\<^type_name>\<open>named\<close>, [T, mk_name_tylabels names])

fun dest_name_tylabel (TFree (name,_)) = trim_tylabel_name name
  | dest_name_tylabel (TVar ((name,_),_)) = trim_tylabel_name name
val dest_name_tylabels = HOLogic.strip_tupleT #> map dest_name_tylabel

fun dest_namedT (Type (@{type_name named}, [tys, names]))
      = dest_name_tylabels names ~~ HOLogic.strip_tupleT tys
  | dest_namedT ty = raise TYPE ("dest_namedT", [ty], [])
fun dest_namedT_only_names (Type (@{type_name named}, [_, names]))
      = dest_name_tylabels names
  | dest_namedT_only_names ty = raise TYPE ("dest_namedT", [ty], [])

fun mk_named_tag X T = \<^Const>\<open>tag \<open>Phi_Help.safe_fastype_of X\<close> T\<close> $ X

val _ = Theory.setup (Sign.parse_ast_translation (
  [(\<^syntax_const>\<open>__named__\<close>, (fn _ =>  fn [term,name] =>
      mk_name_tag_ast (term, strip_tupargs name)))]
))

end
