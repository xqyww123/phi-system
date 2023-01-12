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
  val dest_named : typ -> (string * typ) list
  val dest_named_only_names : typ -> string list

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

val tylabel_name = prefix "'\<phi>name_"
fun mk_name_tylabels names =
      HOLogic.mk_tupleT (map (fn x => TFree (tylabel_name x, [\<^class>\<open>type\<close>])) names)
fun trim_tylabel_name name = String.substring(name, 12, size name - 12)

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

fun dest_named (Type (@{type_name named}, [tys, names]))
      = dest_name_tylabels names ~~ HOLogic.strip_tupleT tys
  | dest_named ty = raise TYPE ("dest_named", [ty], [])
fun dest_named_only_names (Type (@{type_name named}, [_, names]))
      = dest_name_tylabels names
  | dest_named_only_names ty = raise TYPE ("dest_named", [ty], [])

val _ = Theory.setup (Sign.parse_ast_translation (
  [(\<^syntax_const>\<open>__named__\<close>, (fn _ => fn [term,name] =>
      mk_name_tag_ast (term, strip_tupargs name)))]
))

end
