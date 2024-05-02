signature PHI_CONV = sig
include PHI_CONV

(*Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 &&& A2 &&& \<dots> &&& An &&& PURE_TOP \<Longrightarrow> C\<close>*)
val aggregate_imps : conv -> conv
val expand_aggregated_imps : conv -> conv

(*Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 \<and> A2 \<and> \<dots> \<and> An \<and> True \<Longrightarrow> C\<close>*)
(*deprecated, use aggregate_imps_hol instead*)
val aggregate_imps_obj : (Proof.context -> conv) -> Proof.context -> conv
val expand_aggregated_imps_obj : (Proof.context -> conv) -> Proof.context -> conv


(*deprecated
(*for HOL only, no objectize.
Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 \<and> A2 \<and> \<dots> \<and> An \<and> True \<Longrightarrow> C*)
val aggregate_imps_hol : conv -> conv
val expand_aggregated_imps_hol : conv (*for Ai*) -> conv (*for C*) -> conv
*)

(*\<exists>y. x = f y \<and> (\<exists>b. P y b) \<equiv> \<exists>b y. x = f y \<and> P y b*)
val move_Ex_for_set_notation : simproc

end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv Conv

fun aggregate_imps C c =
  (implies_conv C (aggregate_imps C else_conv rewr_conv @{thm PURE_TOP_imp[symmetric]})
   then_conv rewr_conv @{thm conjunction_imp[symmetric]}) c

fun expand_aggregated_imps C ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _)) $ _ =>
          rewr_conv @{thm True_implies_equals} ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ Const(\<^const_name>\<open>PURE_TOP\<close>, _) $ _ =>
          rewr_conv @{thm PURE_TOP_imp} ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Pure.conjunction\<close>, _) $ _ $ _) $ _ =>
          (rewr_conv @{thm conjunction_imp} then_conv
           implies_conv C (expand_aggregated_imps C)) ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _)
          $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>conj\<close>, _) $ _ $ _))
          $ _ =>
          (rewr_conv @{thm conj_imp_eq_imp_imp} then_conv
           implies_conv C (expand_aggregated_imps C)) ctm
     | _ => implies_conv C Conv.all_conv ctm

fun aggregate_imps_obj C ctxt c =
 ((implies_conv (C ctxt then_conv iso_atomize_conv ctxt)
                (aggregate_imps_obj C ctxt)
   then_conv rewr_conv @{thm conj_imp_eq_imp_imp[symmetric]})
  else_conv rewr_conv @{thm True_implies_equals[symmetric]}) c

fun expand_aggregated_imps_obj C ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _)) $ _ =>
          rewr_conv @{thm True_implies_equals} ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
          Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _)) $ _ =>
            (rewr_conv @{thm conj_imp_eq_imp_imp} then_conv
             implies_conv (iso_rulify_conv ctxt then_conv C ctxt)
                          (expand_aggregated_imps_obj C ctxt)) ctm
     | _ => raise CTERM ("expand_aggregated_imps_obj", [ctm])

(*
fun aggregate_imps_hol C ctm =
 ((implies_conv C (aggregate_imps_hol C)
   then_conv rewr_conv @{thm conj_imp_eq_imp_imp[symmetric]})
  else_conv rewr_conv @{thm True_implies_equals[symmetric]}) ctm

fun expand_aggregated_imps_hol Cp Cc ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _)) $ _ =>
          (rewr_conv @{thm True_implies_equals} then_conv Cc) ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
          Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _)) $ _ =>
            (rewr_conv @{thm conj_imp_eq_imp_imp} then_conv
             implies_conv Cp (expand_aggregated_imps_hol Cp Cc)) ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
            (implies_conv Cp Cc) ctm
     | _ => Cc ctm*)

(*\<exists>y. x = f y \<and> (\<exists>b. P y b) \<equiv> \<exists>b y. x = f y \<and> P y b*)
val move_Ex_for_set_notation =
  Simplifier.make_simproc \<^context> "Embed_into_Phi_Type.move_Ex" {
  lhss = [\<^term>\<open>\<exists>y. x = f y \<and> (\<exists>b. P y b)\<close>],
  proc = fn _ => fn _ => fn ctm =>
    case Thm.term_of ctm
      of _ $ Abs (y, _, _ $ _ $ (_ $ Abs (b, _, _))) =>
       (let val ret = Conv.rewr_conv @{lemma \<open>\<exists>y. x = f y \<and> (\<exists>b. P y b) \<equiv> \<exists>b y. x = f y \<and> P y b\<close>
                                          by (unfold atomize_eq, blast)} ctm
            val prop = case Thm.prop_of ret
                         of Eq $ LHS $ (Exb $ Abs (_, Tb, Exy $ Abs (_, Ty, Body))) =>
                            Eq $ LHS $ (Exb $ Abs (b, Tb, Exy $ Abs (y, Ty, Body)))
                          | _ => raise CTERM ("",[])
         in SOME (Thm.renamed_prop prop ret)
        end
        handle CTERM _ => NONE)
       | _ => NONE
}

end