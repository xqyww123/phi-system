signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val is_BI_connective : term -> bool
  val fold_items_of_assertion : (bvs -> term -> 'a -> 'a) -> bvs -> term -> 'a -> 'a
  val fold_items_of_assertion': (bv_typs -> term -> 'a -> 'a) -> bv_typs -> term -> 'a -> 'a
  val exists_item_of_assertion : (bvs -> term -> bool) -> bvs -> term -> bool
  val exists_item_of_assertion': (bv_typs -> term -> bool) -> bv_typs -> term -> bool
  val forall_item_of_assertion : (bvs -> term -> bool) -> bvs -> term -> bool
  val forall_item_of_assertion': (bv_typs -> term -> bool) -> bv_typs -> term -> bool
  val forall_item_of_assertion_blv : (bvs * int (*level of lambda abstractions*) -> term -> bool)
                                  -> bvs -> term -> bool
  val conv_items_of_assertion : (Proof.context -> conv) -> Proof.context -> conv
  val conv_all_typings : (Proof.context -> conv) -> Proof.context -> conv

  val strip_separations : term -> term list
  val mk_separations : typ -> term list -> term
  val leftmost_sep : term -> term
  val rightmost_sep : term -> term

  val mk_phi_type_ty : typ (*concrete*) * typ (*abstract*) -> typ
  val mk_phi_type : term * term -> term
  val dest_phi_type_assertion : term -> term (*x*) * term (*T*)
  val dest_phi_type_ty : typ -> typ (*abstract*) * typ (*concrete*)
  val dest_phi_type_ty_c : ctyp -> ctyp (*abstract*) * ctyp (*concrete*)  
  val dest_parameterized_phi_ty : typ -> typ list (*reserved!*) * typ (*abstract*) * typ (*concrete*)
  val is_phi_type_ty : typ -> bool
  val typ_parameter_of_phi_ty : bv_typs -> term -> ((typ list (*reserved!*) * typ (*abstract*) * typ (*concrete*)) * term) list
  val is_nonnull_Type_Opr : typ -> bool
  val is_non_parameterized_phityp : typ -> bool

  val number_of_typ_operators : bv_typs -> term -> int
  val number_of_typ_operators_in_assertion : bv_typs -> term -> int

  val exists_parameters_that_are_phi_types : (term -> bool) -> term -> bool
  val forall_parameters_that_are_phi_types : (term -> bool) -> term -> bool


  val ExSet_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
  val Subjection_conv : conv -> conv -> conv


  (* System Control *)

  val register_connective : string * int -> unit

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

val arities_of_connective_locker = Synchronized.var "Phi_Syntax.arities_of_connective" ()
val arities_of_connective = Unsynchronized.ref Symtab.empty

fun register_connective iname_airty =
  Synchronized.change arities_of_connective_locker (fn () => (
      arities_of_connective := Symtab.update iname_airty (!arities_of_connective);
      ()))

fun N_arg_rev ret 0 _ = ret
  | N_arg_rev ret N (X $ a) = N_arg_rev (a::ret) (N-1) X

fun arity_of term =
  case Term.head_of term
    of Const (N, _) => Symtab.lookup (!arities_of_connective) N
     | _ => NONE

fun dest_connective_args term = arity_of term
      |> Option.map (fn arity => N_arg_rev [] arity term)

fun conv_N_args 0 C ctm = Conv.all_conv ctm
  | conv_N_args N C ctm = Conv.combination_conv (conv_N_args (N-1) C) C ctm

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
  | is_BI_connective (Const (N, _)) = Symtab.defined (!arities_of_connective) N
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
        | fold _ (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold _ (Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold bvs (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) x = fold bvs A (fold bvs B x)
        | fold bvs (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) x = fold bvs Y (fold bvs X x)
        | fold bvs (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>If\<close>, _) $ _ $ X $ Y) x = fold bvs Y (fold bvs X x)
        | fold bvs X x = (case dest_connective_args X
                            of SOME args => Basics.fold (fold bvs) args x
                             | _ => f bvs X x)
   in fold
  end

fun fold_items_of_assertion' f =
  let fun fold bvs (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold bvs A (fold bvs B x)
        | fold bvs (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Abs (_, ty, X)) x = fold (ty::bvs) X x
        | fold bvs (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) x = f bvs X x
        | fold bvs (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold bvs A (fold bvs B x)
        | fold _ (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold _ (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold _ (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold _ (Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold bvs (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) x = fold bvs A (fold bvs B x)
        | fold bvs (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ Y) x = fold bvs Y (fold bvs X x)
        | fold bvs (Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ X) x = fold bvs X x
        | fold bvs (Const(\<^const_name>\<open>If\<close>, _) $ _ $ X $ Y) x = fold bvs Y (fold bvs X x)
        | fold bvs X x = (case dest_connective_args X
                            of SOME args => Basics.fold (fold bvs) args x
                             | _ => f bvs X x)
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
        | exists bvs X = (case dest_connective_args X
                            of SOME args => Library.exists (exists bvs) args
                             | _ => P bvs X)
   in exists
  end

fun exists_item_of_assertion' P =
  let fun exists bvs (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = exists bvs B orelse exists bvs A
        | exists bvs (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = exists bvs X
        | exists bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = exists bvs X
        | exists bvs (Abs (_, ty, X)) = exists (ty::bvs) X
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
        | exists bvs X = (case dest_connective_args X
                            of SOME args => Library.exists (exists bvs) args
                             | _ => P bvs X)
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
        | forall bvs X = (case dest_connective_args X
                            of SOME args => Library.forall (forall bvs) args
                             | _ => P bvs X)
   in forall
  end

fun forall_item_of_assertion' P =
  let fun forall bvs (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) = forall bvs B andalso forall bvs A
        | forall bvs (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = forall bvs X
        | forall bvs (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = forall bvs X
        | forall bvs (Abs (_, ty, X)) = forall (ty::bvs) X
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
        | forall bvs X = (case dest_connective_args X
                            of SOME args => Library.forall (forall bvs) args
                             | _ => P bvs X)
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
        | forall lv bvs X = (case dest_connective_args X
                               of SOME args => Library.forall (forall lv bvs) args
                                | _ => P (bvs,lv) X)
   in forall 0
  end

fun conv_items_of_assertion C =
  let fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ _ $ _ =>
                Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) ctm
           | Const(\<^const_name>\<open>Subjection\<close>, _) $ _ $ _ =>
                Conv.arg1_conv (conv ctxt) ctm
           | Const(\<^const_name>\<open>ExSet\<close>, _) $ _ =>
                Conv.arg_conv (Phi_Conv.abs_conv_eta (conv o snd) ctxt) ctm
           | Const(\<^const_name>\<open>AllSet\<close>, _) $ _ =>
                Conv.arg_conv (Phi_Conv.abs_conv_eta (conv o snd) ctxt) ctm
           | Const(\<^const_name>\<open>Mul_Quant\<close>, _) $ _ =>
                Conv.arg_conv (Phi_Conv.abs_conv_eta (conv o snd) ctxt) ctm
           | Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ _ $ _ =>
                Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) ctm
           | Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ _ $ _ =>
                Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) ctm
           | Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _ $ _ =>
                Conv.combination_conv (Conv.arg1_conv (conv ctxt)) (conv ctxt) ctm
           | Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
           | Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
           | Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
           | Const(\<^const_name>\<open>one_class.one\<close>, \<^Type>\<open>set _\<close>) => Conv.all_conv ctm
           | Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ _ => Conv.arg_conv (conv ctxt) ctm
           | Const(\<^const_name>\<open>If\<close>, _) $ _ $ _ $ _ => (Conv.arg_conv (conv ctxt) then_conv Conv.arg1_conv (conv ctxt)) ctm
           | Abs _ => Conv.abs_conv (conv o snd) ctxt ctm
           | X => (case arity_of X
                     of SOME arity => conv_N_args arity (conv ctxt) ctm
                      | _ => C ctxt ctm)
   in conv
  end

fun conv_all_typings C = conv_items_of_assertion (fn ctxt => fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => C ctxt ctm
     | _ => Conv.all_conv ctm)

fun strip_separations (Const (@{const_name Subjection}, _) $ T) = strip_separations T
  | strip_separations (Const (@{const_name ExSet}, _) $ T) = strip_separations T
  | strip_separations (Abs (_, _, T)) = strip_separations T
  | strip_separations T = Phi_Help.strip_binop_r @{const_name times} T

(*the left-most non-branching ending element*)
fun leftmost_sep (Const (\<^const_name>\<open>times\<close>, _) $ X $ _) = leftmost_sep X
  | leftmost_sep (Const (@{const_name Subjection}, _) $ T) = leftmost_sep T
  | leftmost_sep (Const (@{const_name ExSet}, _) $ T) = leftmost_sep T
  | leftmost_sep (Const (@{const_name AllSet}, _) $ T) = leftmost_sep T
  | leftmost_sep (Const (@{const_name REMAINS}, _) $ X $ _ $ _) = leftmost_sep X
  | leftmost_sep (Abs (_, _, T)) = leftmost_sep T
  | leftmost_sep X = X

(*the right-most non-branching ending element*)
fun rightmost_sep (Const (\<^const_name>\<open>times\<close>, _) $ _ $ X) = rightmost_sep X
  | rightmost_sep (Const (@{const_name Subjection}, _) $ T) = rightmost_sep T
  | rightmost_sep (Const (@{const_name ExSet}, _) $ T) = rightmost_sep T
  | rightmost_sep (Const (@{const_name AllSet}, _) $ T) = rightmost_sep T
  | rightmost_sep (Const (@{const_name REMAINS}, _) $ _ $ _ $ X) = rightmost_sep X
  | rightmost_sep (Abs (_, _, T)) = rightmost_sep T
  | rightmost_sep X = X

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

fun is_phi_type_ty \<^Type>\<open>fun _ \<open>\<^Type>\<open>set _\<close>\<close>\<close> = true
  | is_phi_type_ty \<^Type>\<open>fun _ T\<close> = is_phi_type_ty T
  | is_phi_type_ty _ = false

fun typ_parameter_of_phi_ty bvtys T_term =
  let fun collect_params ret (F' $ T') =
           (case try dest_parameterized_phi_ty (Term.fastype_of1 (bvtys,T'))
              of SOME dest => collect_params ((dest,T') :: ret) F'
               | NONE => collect_params ret F')
        | collect_params ret _  = ret
   in collect_params [] T_term
  end

fun is_nonnull_Type_Opr ty =
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

fun number_of_typ_operators bvtys tm =
  if can dest_phi_type_ty (Term.fastype_of1 (bvtys, tm))
  then let val (_, args) = Term.strip_comb tm
        in fold (fn arg => fn ret => ret + number_of_typ_operators bvtys arg) args 1
       end
  else case tm
    of Abs (_, ty, X) => number_of_typ_operators (ty::bvtys) X
     | _ => 0

fun number_of_typ_operators_in_assertion bvtys term =
      fold_items_of_assertion' (fn bvtys =>
        fn (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) =>
            (fn S => S + number_of_typ_operators bvtys T)
          | _ => I) bvtys term 0

local
fun head_is_phi (X $ _) = head_is_phi X
  | head_is_phi (Abs (_, _, X)) = head_is_phi X
  | head_is_phi (Const(_, ty)) = is_phi_type_ty ty
  | head_is_phi (Free (_, ty)) = is_phi_type_ty ty
  | head_is_phi (Var (_, ty))  = is_phi_type_ty ty
  | head_is_phi _ = false
in
(*
fun fold_parameters_that_are_phi_types F =
  let fun fold_s (A $ B) x = fold B (fold_s A x)
        | fold_s (Abs (_, _, X)) x = fold_s X x
        | fold_s X x = F X x
      and fold tm x =
        if head_is_phi tm
        then fold_s tm x
        else x
   in fold
  end *)

fun exists_parameters_that_are_phi_types F =
  let fun fold_s (A $ B) = fold_s A orelse fold B
        | fold_s (Abs (_, _, X)) = fold_s X
        | fold_s X = F X
      and fold tm =
        if head_is_phi tm
        then F tm orelse fold_s tm
        else false
   in fold
  end

fun forall_parameters_that_are_phi_types F =
  let fun fold_s (A $ B) = fold A andalso fold_s B
        | fold_s (Abs (_, _, X)) = fold_s X
        | fold_s X = F X
      and fold tm =
        if head_is_phi tm
        then F tm andalso fold_s tm
        else true
   in fold
  end

end

end

val dest_parameterized_phi_ty = Phi_Syntax.dest_parameterized_phi_ty