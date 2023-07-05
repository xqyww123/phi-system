signature PHI_CONV = sig
include PHI_CONV

(*Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 &&& A2 &&& \<dots> &&& An &&& PURE_TOP \<Longrightarrow> C\<close>*)
val aggregate_imps : conv -> conv
val expand_aggregated_imps : conv -> conv

(*Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 \<and> A2 \<and> \<dots> \<and> An \<and> True \<Longrightarrow> C\<close>*)
val aggregate_imps_obj : (Proof.context -> conv) -> Proof.context -> conv
val expand_aggregated_imps_obj : (Proof.context -> conv) -> Proof.context -> conv

(*for HOL only, no objectize.
Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 \<and> A2 \<and> \<dots> \<and> An \<and> True \<Longrightarrow> C*)
val aggregate_imps_hol : conv -> conv
val expand_aggregated_imps_hol : conv (*for Ai*) -> conv (*for C*) -> conv

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
 ((implies_conv (C ctxt then_conv atomize_conv ctxt)
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
             implies_conv (rulify_conv ctxt then_conv C ctxt)
                          (expand_aggregated_imps_obj C ctxt)) ctm
     | _ => raise CTERM ("expand_aggregated_imps_obj", [ctm])

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
     | _ => raise CTERM ("expand_aggregated_imps_obj", [ctm])



end