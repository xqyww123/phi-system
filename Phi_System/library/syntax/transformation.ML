signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_BI_ty : typ -> typ (*typ of concrete algebra*)

  val is_intro_transformation : term -> bool
  val is_elim_transformation : term -> bool
  val pass_ensures_intro_transformation : Phi_Reasoner.rule_pass
  val pass_ensures_elim_transformation : Phi_Reasoner.rule_pass

  val dest_transformation_typ : term -> typ
  val dest_transformation   : term  -> term * term * term
  val dest_transformation_c : cterm -> cterm * cterm * cterm
  val transformation_conv : conv -> conv -> conv -> conv

  val conv_ToR_add_tag : conv

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

fun dest_BI_ty (\<^Type>\<open>set ty\<close>) = ty
  | dest_BI_ty ty = raise TYPE ("Not of a type of BI assertion", [ty], [])

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

fun is_intro_transformation rule =
  let val (prems, concl) = Logic.strip_horn rule
   in case dest_transformation concl
   of (Var v, _, _) =>
        exists (fn prem => case try dest_transformation (Logic.strip_assums_concl prem)
                             of SOME (Var v', _, _) => v' = v
                              | _ => false) prems
    | _ => false
  end

fun is_elim_transformation rule =
  let val (prems, concl) = Logic.strip_horn rule
   in case dest_transformation concl
   of (_, Var v, _) =>
        exists (fn prem => case dest_transformation prem
                             of (_, Var v', _) => v' = v
                              | _ => false) prems
    | _ => false
  end

fun pass_ensures_intro_transformation _ (rules, (mode, priority), (pattern, except), guard, ctxt) =
  let fun chk rule = if is_intro_transformation (Thm.prop_of rule) then rule
                     else rule RS' (Context.proof_of ctxt, @{thm' mk_intro_transformation})
   in (map chk rules, (mode, priority), (pattern, except), guard, ctxt)
  end

fun pass_ensures_elim_transformation _ (rules, (mode, priority), (pattern, except), guard, ctxt) =
  let fun chk rule = if is_elim_transformation (Thm.prop_of rule) then rule
                     else rule RS' (Context.proof_of ctxt, @{thm' mk_elim_transformation})
   in (map chk rules, (mode, priority), (pattern, except), guard, ctxt)
  end


fun transformation_conv C_s C_t C_p ctm = (
  dest_transformation_c ctm;
  Phi_Conv.tag_conv (
    Conv.combination_conv (Conv.combination_conv (Conv.combination_conv Conv.all_conv C_s) C_t) C_p) ctm
)

fun is_Var x =
  let val (h,args) = Term.strip_comb x
   in Term.is_Var h andalso forall (fn Bound _ => true | _ => false) args
  end

fun err ctm = raise CTERM("Fail to classify the Transformation rule automatically into \<T>\<P>, \<T>\<P>', \<T>\<P>\<A>", [ctm])

fun conv_ToR_add_tag ctm =
  let datatype kind = ProdTy | Ty | Oth
      fun cond_Ty (Const(\<^const_name>\<open>Cond_\<phi>Prod\<close>, _) $ _ $ _ $ _) = ProdTy
        | cond_Ty _ = Ty
      fun dest_ty (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ U) = cond_Ty U
        | dest_ty _ = Oth
      val (X,Y,_) = dest_transformation (Thm.term_of ctm)
   in case (dest_ty X, dest_ty Y)
   of (ProdTy, ProdTy) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>'\<close>, symmetric]} ctm
    | (Oth, _) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<A>\<close>, symmetric]} ctm
    | (_, Oth) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<A>\<close>, symmetric]} ctm
    | (Ty, Ty)  => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<close>, symmetric]} ctm
    | _ => err ctm
  end

fun conv_ToR_add_tag' ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _ =>
        conv_ToR_add_tag ctm
     | _ => let
        fun chk_all_transformation_is_tagged (Const (\<^const_name>\<open>Action_Tag\<close>, _) $ (Const (\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _) $ _) = true
          | chk_all_transformation_is_tagged (Const (\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _) = false
          | chk_all_transformation_is_tagged (X $ Y) = chk_all_transformation_is_tagged X andalso chk_all_transformation_is_tagged Y
          | chk_all_transformation_is_tagged (Abs (_, _, X)) = chk_all_transformation_is_tagged X
          | chk_all_transformation_is_tagged _ = true
     in if chk_all_transformation_is_tagged (Thm.term_of ctm)
        then Conv.all_conv ctm
        else err ctm
    end

fun ToR_rule_add_tag ctxt th =
  Conv.fconv_rule (Phi_Conv.hhf_conv (Phi_Conv.hhf_concl_conv (K (HOLogic.Trueprop_conv conv_ToR_add_tag')))
                                     (K (HOLogic.Trueprop_conv conv_ToR_add_tag')) ctxt) th
  |> (fn th =>
    let val last = Unsynchronized.ref NONE
        fun set v = case !last of NONE => last := SOME v
                                | SOME v' => if v = v' then ()
                                             else err (Thm.cprop_of th)
        fun scan' (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ Const(\<^const_name>\<open>\<T>\<P>\<close>, _)) = set 2
          | scan' (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ Const(\<^const_name>\<open>\<T>\<P>'\<close>, _)) = set 3
          | scan' (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ Const(\<^const_name>\<open>\<T>\<P>\<A>\<close>, _)) = set 1
          | scan' _ = ()
        fun scan (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = scan' X
          | scan (X $ Y) = (scan X ; scan Y)
          | scan (Abs (_, _, X)) = scan X
          | scan _ = ()
     in scan (Thm.prop_of th) ;
        th
    end)

val _ = Theory.setup (Context.theory_map (
  Phi_Reasoner.add_pass (Free("Add ToR tag auto", dummyT), \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>,
    fn pos => fn (rules, prio, pats, guard, ctxt) =>
                 (map (fn rule =>
                    if Thm.is_dummy rule
                    then rule
                    else ToR_rule_add_tag (Context.proof_of ctxt) rule) rules, prio, pats, guard, ctxt))
))

end