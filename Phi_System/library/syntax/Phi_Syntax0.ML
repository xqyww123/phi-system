signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val is_action_of : (term -> bool) -> (term -> bool)
  val dest_tags   :  term ->  term
  val dest_tags_c : cterm -> cterm

  val is_BI_connective : term -> bool
  val fold_items_of_assertion : (term -> 'a -> 'a) -> term -> 'a -> 'a
  val exists_item_of_assertion : (term -> bool) -> term -> bool
  val forall_item_of_assertion : (term -> bool) -> term -> bool

  val dest_transformation_typ : term -> typ
  val dest_transformation   : term  -> term * term * term
  val dest_transformation_c : cterm -> cterm * cterm * cterm
  val transformation_conv : conv -> conv -> conv -> conv

  val is_transformation_intro_rule : thm -> bool
  val is_transformation_elim_rule : thm -> bool
  val pass_ensures_intro_transformation : Phi_Reasoner.rule_pass
  val pass_ensures_elim_transformation : Phi_Reasoner.rule_pass

  val strip_separations : term -> term list
  val mk_separations : typ -> term list -> term


end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

val dest_action_tag   = Phi_Help.dest_binop   \<^const_name>\<open>Action_Tag\<close> #> #1
val dest_action_tag_c = Phi_Help.dest_binop_c \<^const_name>\<open>Action_Tag\<close> #> #1

fun is_action_of P (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ A) = P A
  | is_action_of P (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_action_of P X
  | is_action_of _ _ = false

fun dest_tags (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest_tags X
  | dest_tags (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = dest_tags X
  | dest_tags X = X
fun dest_tags_c X = X
  |> perhaps (try Phi_Help.dest_Trueprop_c)
  |> perhaps (try dest_action_tag_c)


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


val dest_transformation   =
         dest_tags
      #> Phi_Help.dest_triop @{const_name "Transformation"}
val dest_transformation_c =
         dest_tags_c
      #> Phi_Help.dest_triop_c @{const_name "Transformation"}

fun dest_transformation_typ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest_transformation_typ X
  | dest_transformation_typ (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = dest_transformation_typ X
  | dest_transformation_typ (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ X) = dest_transformation_typ X
  | dest_transformation_typ (Const(\<^const_name>\<open>Transformation\<close>, \<^Type>\<open>fun \<^Type>\<open>set a\<close> _\<close>) $ _ $ _ $ _) = a
  | dest_transformation_typ X = raise TERM ("dest_transformation_typ", [X])

fun is_transformation_intro_rule rule =
  let val (prems, concl) = Logic.strip_horn (Thm.prop_of rule)
   in case dest_transformation concl
   of (Var v, _, _) =>
        exists (fn prem => case dest_transformation prem
                             of (Var v', _, _) => v' = v
                              | _ => false) prems
    | _ => false
  end

fun is_transformation_elim_rule rule =
  let val (prems, concl) = Logic.strip_horn (Thm.prop_of rule)
   in case dest_transformation concl
   of (_, Var v, _) =>
        exists (fn prem => case dest_transformation prem
                             of (_, Var v', _) => v' = v
                              | _ => false) prems
    | _ => false
  end

fun pass_ensures_intro_transformation _ (rules, (mode, priority), (pattern, except), guard, ctxt) =
  let fun chk rule = if is_transformation_intro_rule rule then rule
                     else rule RS' (Context.proof_of ctxt, @{thm' mk_intro_transformation})
   in (map chk rules, (mode, priority), (pattern, except), guard, ctxt)
  end

fun pass_ensures_elim_transformation _ (rules, (mode, priority), (pattern, except), guard, ctxt) =
  let fun chk rule = if is_transformation_elim_rule rule then rule
                     else rule RS' (Context.proof_of ctxt, @{thm' mk_elim_transformation})
   in (map chk rules, (mode, priority), (pattern, except), guard, ctxt)
  end


fun transformation_conv C_s C_t C_p ctm = (
  dest_transformation_c ctm;
  Phi_Conv.tag_conv (
    Conv.combination_conv (Conv.combination_conv (Conv.combination_conv Conv.all_conv C_s) C_t) C_p) ctm
)

fun strip_separations (Const (@{const_name Subjection}, _) $ T) = strip_separations T
  | strip_separations (Const (@{const_name ExSet}, _) $ T) = strip_separations T
  | strip_separations (Abs (_, _, T)) = strip_separations T
  | strip_separations T = Phi_Help.strip_binop_l @{const_name times} T

fun mk_separations model_ty [] = \<^Const>\<open>one_class.one model_ty\<close>
  | mk_separations model_ty L = foldr1 (fn (A,X) => \<^Const>\<open>times model_ty\<close> $ A $ X) L



end