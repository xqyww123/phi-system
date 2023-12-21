signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val is_BI_connective : term -> bool
  val fold_items_of_assertion : (PLPR_Pattern.bvs -> term -> 'a -> 'a) -> PLPR_Pattern.bvs -> term -> 'a -> 'a
  val exists_item_of_assertion : (PLPR_Pattern.bvs -> term -> bool) -> PLPR_Pattern.bvs -> term -> bool
  val forall_item_of_assertion : (PLPR_Pattern.bvs -> term -> bool) -> PLPR_Pattern.bvs -> term -> bool
  val forall_item_of_assertion_blv : (PLPR_Pattern.bvs * int (*level of lambda abstractions*) -> term -> bool)
                                  -> PLPR_Pattern.bvs -> term -> bool
  val conv_items_of_assertion : (Proof.context -> conv) -> Proof.context -> conv

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
  | is_BI_connective (Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>)) = true
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
  let fun fold bvs (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold bvs A (fold bvs B x)
        | fold bvs (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Abs (N, ty, X)) x = fold ((N,ty)::bvs) X x
        | fold bvs (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) x = f bvs X x
        | fold bvs (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold bvs A (fold bvs B x)
        | fold _ (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold _ (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold bvs (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold bvs (Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold bvs (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) x = fold bvs A (fold bvs B x)
        | fold bvs (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) x = fold bvs Y (fold bvs X x)
        | fold bvs (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>If\<close>, _) $ _ $ X $ Y) x = fold bvs Y (fold bvs X x)
        | fold bvs X x = f bvs X x
   in fold
  end

fun exists_item_of_assertion P =
  let fun exists bvs (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = exists bvs B orelse exists bvs A
        | exists bvs (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = exists bvs X
        | exists bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = exists bvs X
        | exists bvs (Abs (N, ty, X)) = exists ((N,ty)::bvs) X
        | exists bvs (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P bvs X
        | exists bvs (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = exists bvs B orelse exists bvs A
        | exists _ (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists _ (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists _ (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists _ (Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists bvs (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = exists bvs X
        | exists bvs (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = exists bvs B orelse exists bvs A
        | exists bvs (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) = exists bvs X orelse exists bvs Y
        | exists bvs (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) = exists bvs X
        | exists bvs (Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ X) = exists bvs X
        | exists bvs (Const(\<^const_name>\<open>If\<close>, _) $ _ $ X $ Y) = exists bvs X orelse exists bvs Y
        | exists bvs X = P bvs X
   in exists
  end

fun forall_item_of_assertion P =
  let fun forall bvs (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = forall bvs B andalso forall bvs A
        | forall bvs (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = forall bvs X
        | forall bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = forall bvs X
        | forall bvs (Abs (N, ty, X)) = forall ((N,ty)::bvs) X
        | forall bvs (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P bvs X
        | forall bvs (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = forall bvs B andalso forall bvs A
        | forall _ (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ (Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall bvs (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = forall bvs X
        | forall bvs (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = forall bvs B andalso forall bvs A
        | forall bvs (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) = forall bvs X andalso forall bvs Y
        | forall bvs (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) = forall bvs X
        | forall bvs (Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ X) = forall bvs X
        | forall bvs (Const(\<^const_name>\<open>If\<close>, _) $ _ $ X $ Y) = forall bvs X andalso forall bvs Y
        | forall bvs X = P bvs X
   in forall
  end

fun forall_item_of_assertion_blv P =
  let fun forall lv bvs (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = forall lv bvs B andalso forall lv bvs A
        | forall lv bvs (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = forall lv bvs X
        | forall lv bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ Abs (N, Ty, X)) = forall (lv + 1) ((N,Ty)::bvs) X
        | forall lv bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = forall (lv + 1) bvs (Term.incr_boundvars 1 X $ Bound 0)
        | forall lv bvs (Abs (N, Ty, X)) = forall (lv+1) ((N,Ty)::bvs) X
        | forall lv bvs (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P (bvs,lv) X
        | forall lv bvs (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = forall lv bvs B andalso forall lv bvs A
        | forall _ _ (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ _ (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ _ (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall _ _ (Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall lv bvs (Const(\<^const_name>\<open>AllSet\<close>, _) $ Abs (N, Ty, X)) = forall (lv + 1) ((N,Ty)::bvs) X
        | forall lv bvs (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = forall (lv + 1) bvs (Term.incr_boundvars 1 X $ Bound 0)
        | forall lv bvs (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = forall lv bvs B andalso forall lv bvs A
        | forall lv bvs (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) = forall lv bvs X andalso forall lv bvs Y
        | forall lv bvs (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) = forall lv bvs X
        | forall lv bvs (Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ X) = forall lv bvs X
        | forall lv bvs (Const(\<^const_name>\<open>If\<close>, _) $ _ $ X $ Y) = forall lv bvs X andalso forall lv bvs Y
        | forall lv bvs X = P (bvs,lv) X
   in forall 0
  end

fun conv_items_of_assertion C ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (C ctxt)) (C ctxt) ctm
     | Const(\<^const_name>\<open>Subjection\<close>, _) $ _ $ _ =>
          Conv.arg1_conv (C ctxt) ctm
     | Const(\<^const_name>\<open>ExSet\<close>, _) $ _ =>
          Conv.arg_conv (Phi_Conv.abs_conv_eta (C o snd) ctxt) ctm
     | Const(\<^const_name>\<open>AllSet\<close>, _) $ _ =>
          Conv.arg_conv (Phi_Conv.abs_conv_eta (C o snd) ctxt) ctm
     | Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ _ =>
          Conv.arg_conv (Phi_Conv.abs_conv_eta (C o snd) ctxt) ctm
     | Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (C ctxt)) (C ctxt) ctm
     | Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (C ctxt)) (C ctxt) ctm
     | Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (C ctxt)) (C ctxt) ctm
     | Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
     | Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
     | Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
     | Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
     | Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ _ => Conv.arg_conv (C ctxt) ctm
     | Const(\<^const_name>\<open>If\<close>, _) $ _ $ _ $ _ => (Conv.arg_conv (C ctxt) then_conv Conv.arg1_conv (C ctxt)) ctm
     | _ => C ctxt ctm


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