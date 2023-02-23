signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_labelled_opt : term -> string option * term (* Labelled name, x -> (name,x) *)
  val label_ty : typ
  val label_cty : ctyp
  val dest_label : term -> string
  val mk_label : string -> term
  val mk_label_c : string -> cterm
  val mk_labelled : string -> term -> term
  val dest_labelled: term -> string * term
  val mk_label_thm : string -> thm
  val intro_labelled : string -> conv
  val elim_labelled : conv
  val labelled_conv : conv -> conv

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

val label_ty = Type (@{type_name "label"}, [])
val label_cty = @{ctyp "label"}
val label_const_name = @{const_name "LABEL_TAG"}
val unit_ty = Type (@{type_name "Product_Type.unit"}, [])
val unit_const = Const("Product_Type.Unity", unit_ty)
val label_const = Const (label_const_name, (unit_ty --> unit_ty) --> label_ty)
val dest_label_raw   = Phi_Help.dest_monop label_const_name
val dest_label_raw_c = Phi_Help.dest_monop_c label_const_name
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
fun dest_labelled X = X
  |> perhaps (try HOLogic.dest_Trueprop)
  |> Phi_Help.dest_binop \<^const_name>\<open>Labelled\<close> |> apfst dest_label
fun dest_labelled_opt tm =
  case try (Phi_Help.dest_binop labelled_name) tm of
     SOME (v,tm) => (SOME (dest_label v), tm)
   | NONE => (NONE, tm)

fun intro_labelled name cterm =
  Thm.instantiate (TVars.make [((("'a",0),[]), Thm.ctyp_of_cterm cterm)],
                   Vars.make  [((("name",0),\<^typ>\<open>label\<close>), mk_label_c name),
                               ((("x",0), Thm.typ_of_cterm cterm), cterm)])
                  @{thm Labelled_def_sym}

val elim_labelled = Conv.rewr_conv @{thm Labelled_def}

fun labelled_conv C ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Labelled\<close>, _) $ _ $ _ => Conv.arg_conv C ctm
     | _ => raise CTERM ("labelled_conv", [ctm])

end