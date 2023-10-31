signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val is_BI_connective : term -> bool
  val fold_items_of_assertion : (term -> 'a -> 'a) -> term -> 'a -> 'a
  val exists_item_of_assertion : (term -> bool) -> term -> bool
  val forall_item_of_assertion : (term -> bool) -> term -> bool
  val forall_item_of_assertion_blv : (int (*level of lambda abstractions*) -> term -> bool)
                                  -> term -> bool

  val strip_separations : term -> term list
  val mk_separations : typ -> term list -> term

  val mk_phi_type_ty : typ (*concrete*) * typ (*abstract*) -> typ
  val mk_phi_type : term * term -> term
  val dest_phi_type_assertion : term -> term (*x*) * term (*T*)
  val dest_phi_type_ty : typ -> typ (*abstract*) * typ (*concrete*)
  val dest_phi_type_ty_c : ctyp -> ctyp (*abstract*) * ctyp (*concrete*)  
  val dest_parameterized_phi_ty : typ -> typ list (*reserved!*) * typ (*x*) * typ (*concrete*)
  val is_Type_Opr : typ -> bool
  val is_non_parameterized_phityp : typ -> bool

  val ExSet_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
  val Subjection_conv : conv -> conv -> conv

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

fun is_BI_connective (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>Subjection\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>ExSet\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>\<phi>Type\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>Additive_Conj\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>REMAINS\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>Mul_Quant\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>AllSet\<close>, _)) = true
  | is_BI_connective (A $ _) = is_BI_connective A
  | is_BI_connective _ = false

(*including all \<phi>-type terms and atomic predicates*)
fun fold_items_of_assertion f =
  let fun fold (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold A (fold B x)
        | fold (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) x = fold X x
        | fold (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) x = fold X x
        | fold (Abs (_, _, X)) x = fold X x
        | fold (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) x = f X x
        | fold (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold A (fold B x)
        | fold (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) x = fold X x
        | fold (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) x = fold A (fold B x)
        | fold (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) x = fold Y (fold X x)
        | fold (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) x = fold X x
        | fold X x = f X x
   in fold
  end

fun exists_item_of_assertion P =
  let fun exists (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = exists B orelse exists A
        | exists (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = exists X
        | exists (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = exists X
        | exists (Abs (_, _, X)) = exists X
        | exists (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P X
        | exists (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = exists B orelse exists A
        | exists (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = exists X
        | exists (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = exists B orelse exists A
        | exists (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) = exists X orelse exists Y
        | exists (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) = exists X
        | exists X = P X
   in exists
  end

fun forall_item_of_assertion P =
  let fun forall (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = forall B andalso forall A
        | forall (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = forall X
        | forall (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = forall X
        | forall (Abs (_, _, X)) = forall X
        | forall (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P X
        | forall (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = forall B andalso forall A
        | forall (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = forall X
        | forall (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = forall B andalso forall A
        | forall (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) = forall X andalso forall Y
        | forall (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) = forall X
        | forall X = P X
   in forall
  end

fun forall_item_of_assertion_blv P =
  let fun forall lv (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = forall lv B andalso forall lv A
        | forall lv (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = forall lv X
        | forall lv (Const(\<^const_name>\<open>ExSet\<close>, _) $ Abs (_, _, X)) = forall (lv + 1) X
        | forall lv (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = forall (lv + 1) (Term.incr_boundvars 1 X $ Bound 0)
        | forall lv (Abs (_, _, X)) = forall (lv+1) X
        | forall lv (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P lv X
        | forall lv (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = forall lv B andalso forall lv A
        | forall _ (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall lv (Const(\<^const_name>\<open>AllSet\<close>, _) $ Abs (_, _, X)) = forall (lv + 1) X
        | forall lv (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = forall (lv + 1) (Term.incr_boundvars 1 X $ Bound 0)
        | forall lv (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = forall lv B andalso forall lv A
        | forall lv (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) = forall lv X andalso forall lv Y
        | forall lv (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) = forall lv X
        | forall lv X = P lv X
   in forall 0
  end


fun strip_separations (Const (@{const_name Subjection}, _) $ T) = strip_separations T
  | strip_separations (Const (@{const_name ExSet}, _) $ T) = strip_separations T
  | strip_separations (Abs (_, _, T)) = strip_separations T
  | strip_separations T = Phi_Help.strip_binop_l @{const_name times} T

fun mk_separations model_ty [] = \<^Const>\<open>one_class.one model_ty\<close>
  | mk_separations model_ty L = foldr1 (fn (A,X) => \<^Const>\<open>times model_ty\<close> $ A $ X) L

fun mk_phi_type (x,T) =
  let val \<^Type>\<open>fun \<open>a\<close> \<open>\<^Type>\<open>set \<open>b\<close>\<close>\<close>\<close> = Phi_Help.safe_fastype_of  T
   in \<^Const>\<open>\<phi>Type a b\<close> $ x $ T end

fun mk_phi_type_ty (tm, tx) = \<^Type>\<open>fun tx \<^Type>\<open>set tm\<close>\<close>

fun dest_phi_type_assertion (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T) = (x, T)
  | dest_phi_type_assertion X = raise TERM ("Not a \<phi>-type assertion", [X])

fun dest_phi_type_ty \<^Type>\<open>fun x \<^Type>\<open>set model\<close>\<close> = (x, model)
  | dest_phi_type_ty T = raise TYPE ("dest_phi_type_ty", [T], [])

fun dest_phi_type_ty_c T =
  (dest_phi_type_ty (Thm.typ_of T) ;
   (Thm.dest_ctyp0 T, Thm.dest_ctyp0 (Thm.dest_ctyp1 T)))

fun dest_parameterized_phi_ty' args \<^Type>\<open>fun x \<open>\<^Type>\<open>set c\<close>\<close>\<close> = (args, x, c)
  | dest_parameterized_phi_ty' args \<^Type>\<open>fun a T\<close> = dest_parameterized_phi_ty' (a::args) T
  | dest_parameterized_phi_ty' _ T = raise TYPE ("not a phi-type",[T],[])

val dest_parameterized_phi_ty = dest_parameterized_phi_ty' []

fun is_Type_Opr ty =
  case dest_parameterized_phi_ty ty
    of ([],_,_) => false
     | (args,_,_) => exists (can dest_parameterized_phi_ty) args

fun is_non_parameterized_phityp typ =
  case try dest_parameterized_phi_ty typ
    of SOME ([],_,_) => true
     | _ => false

val ExSet_conv = Phi_Conv.quant_conv \<^const_name>\<open>ExSet\<close>
fun Subjection_conv CX CP ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Subjection\<close>, _) $ _ $ _ =>
       (Conv.arg1_conv CX then_conv
        Conv.arg_conv CP) ctm
     | _ => raise CTERM ("Subjection_conv", [ctm])

end

val dest_parameterized_phi_ty = Phi_Syntax.dest_parameterized_phi_ty