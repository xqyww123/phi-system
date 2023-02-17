signature PHI_HELPER_CONV = sig
include PHI_HELPER_CONV

(* Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 &&& A2 &&& \<dots> &&& An &&& PURE_TOP \<Longrightarrow> C\<close> *)
val aggregate_imps : conv -> conv
val expand_aggregated_imps : conv -> conv

(* Converting \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<dots> \<Longrightarrow> An \<Longrightarrow> C\<close> to \<open>A1 \<and> A2 \<and> \<dots> \<and> An \<and> True \<Longrightarrow> C\<close> *)
val aggregate_imps_obj : (Proof.context -> conv) -> Proof.context -> conv
val expand_aggregated_imps_obj : (Proof.context -> conv) -> Proof.context -> conv

val protect_conv : conv
val unprotect_conv : conv

val foralls_body_conv : (Proof.context -> conv) -> Proof.context -> conv

val leading_antecedent_conv : conv -> conv

end

structure Phi_Helper_Conv : PHI_HELPER_CONV = struct
open Phi_Helper_Conv Conv

fun aggregate_imps C c =
  (implies_conv C (aggregate_imps C else_conv rewr_conv @{thm PURE_TOP_imp[symmetric]})
   then_conv rewr_conv @{thm conjunction_imp[symmetric]}) c

fun expand_aggregated_imps C c =
  (rewr_conv @{thm conjunction_imp} then_conv
   implies_conv C (rewr_conv @{thm PURE_TOP_imp} else_conv expand_aggregated_imps C)) c

fun aggregate_imps_obj C ctxt c =
  (implies_conv (C ctxt then_conv atomize_conv ctxt)
                (aggregate_imps_obj C ctxt else_conv rewr_conv @{thm True_implies_equals[symmetric]})
   then_conv rewr_conv @{thm conj_imp_eq_imp_imp[symmetric]}) c

fun expand_aggregated_imps_obj C ctxt c =
  (rewr_conv @{thm conj_imp_eq_imp_imp} then_conv
   implies_conv (rulify_conv ctxt then_conv C ctxt)
                (rewr_conv @{thm True_implies_equals} else_conv expand_aggregated_imps_obj C ctxt)) c


val protect_conv = rewr_conv @{thm Pure.prop_def[symmetric]}
val unprotect_conv = rewr_conv @{thm Pure.prop_def}

fun foralls_body_conv C ctxt =
  forall_conv (fn (_, ctxt) => foralls_body_conv C ctxt) ctxt
  else_conv C ctxt

fun leading_antecedent_conv C = implies_conv C all_conv

end