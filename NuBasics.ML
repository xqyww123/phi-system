(*  Title:      NuBasics.ML
    Author:     Qiyuan Xu

Basic supports for the nu-system.

*)

signature NU_BASICS = sig
  val dest_nuTy : term -> term * term
  val dest_named : term -> string option * term (* Named name, x -> (name,x) *)

  val name_tag_ty : typ
  val dest_name_tag : term -> string
  val mk_name_tag : string -> term
end
structure NuBasics = struct
open NuHelp

val name_tag_ty_raw = Term.Type ("NuPrim.name_tag_ty", [])
val name_tag_ty = Term.Type ("fun", [name_tag_ty_raw, name_tag_ty_raw])
val name_tag_const_name = "NuPrim.name_tag_ty.NAME_TAG"
val name_tag_const = Term.Const (name_tag_const_name, name_tag_ty)
fun dest_name_tag (tm as Term.Abs (name,ty,body)) =
      if same_const name_tag_const_name body
          andalso (ty = name_tag_ty orelse ty = Term.dummyT)
        then name else raise Syntax (@{print} tm)
  | dest_name_tag tm = raise Syntax tm
val dest_name_tag = dest_name_tag o Type.strip_constraints
fun mk_name_tag name = Term.Abs (name, name_tag_ty, name_tag_const)

val named_name = "NuPrim.Named"
fun dest_named tm =
      case try (dest_binop named_name) tm of
         SOME (v,tm) => (SOME (dest_name_tag v), tm)
       | NONE => (NONE, tm)
val nuTy_name = "NuPrim.NuTyp"
val dest_nuTy = dest_binop nuTy_name
end
