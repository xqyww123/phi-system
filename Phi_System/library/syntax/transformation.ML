signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val is_transformation_intro_rule : thm -> bool
  val is_transformation_elim_rule : thm -> bool
  val pass_ensures_intro_transformation : Phi_Reasoner.rule_pass
  val pass_ensures_elim_transformation : Phi_Reasoner.rule_pass

  val dest_transformation_typ : term -> typ
  val dest_transformation   : term  -> term * term * term
  val dest_transformation_c : cterm -> cterm * cterm * cterm
  val transformation_conv : conv -> conv -> conv -> conv


end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

val dest_action_tag   = Phi_Help.dest_binop   \<^const_name>\<open>Action_Tag\<close> #> #1
val dest_action_tag_c = Phi_Help.dest_binop_c \<^const_name>\<open>Action_Tag\<close> #> #1


val dest_transformation   =
         PLPR_Syntax.dest_tags
      #> Phi_Help.dest_triop @{const_name "Transformation"}
val dest_transformation_c =
         PLPR_Syntax.dest_tags_c
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


end