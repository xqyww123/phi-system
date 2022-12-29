signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_labelled_opt : term -> string option * term (* Labelled name, x -> (name,x) *)
  val label_ty : typ
  val label_cty : ctyp
  val dest_label : term -> string
  val mk_label : string -> term
  val mk_label_c : string -> cterm
  val mk_labelled : string -> term -> term
  val mk_label_thm : string -> thm

end

structure PhiSyntax : PHI_SYNTAX = struct
open PhiSyntax

local open NuHelp in

val unit_const_name = @{const_name "Product_Type.Unity"}
val label_ty = Type (@{type_name "label"}, [])
val label_cty = @{ctyp "label"}
val label_const_name = @{const_name "LABEL_TAG"}
val unit_ty = Type (@{type_name "Product_Type.unit"}, [])
val unit_const = Const("Product_Type.Unity", unit_ty)
val label_const = Const (label_const_name, (unit_ty --> unit_ty) --> label_ty)
val dest_label_raw   = dest_monop label_const_name
val dest_label_raw_c = dest_monop_c label_const_name
fun dest_Abs (Abs x) =  x
  | dest_Abs t = raise TERM("dest_Abs", [t]);
fun dest_label tm =
  tm |> Type.strip_constraints |> dest_label_raw |> dest_Abs |> #1
    handle TERM _ => raise TERM ("dest_label", [tm])
val label_c = @{cterm "LABEL name"}
fun mk_label name = label_const $ Abs (name, unit_ty, unit_const)
fun mk_label_c name = Thm.renamed_term (mk_label name) label_c
fun mk_label_thm name = 
  Thm.instantiate (TVars.empty, Vars.make [((("x",0),\<^typ>\<open>label\<close>), mk_label_c name)]) @{thm LabelTag}
fun mk_labelled name tm = Const(@{const_name Labelled}, dummyT) $ mk_label name $ tm

val labelled_name = @{const_name "Labelled"}
val dest_labelled = dest_binop labelled_name #> apfst dest_label
fun dest_labelled_opt tm =
  case try (dest_binop labelled_name) tm of
     SOME (v,tm) => (SOME (dest_label v), tm)
   | NONE => (NONE, tm)

end

end