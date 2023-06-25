signature PHI_HELPER_CONV = sig
include PHI_HELPER_CONV

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

val protect_conv : conv
val unprotect_conv : conv

val leading_antecedent_conv : conv -> conv
val hhf_concl_conv : (Proof.context -> conv) -> Proof.context -> conv
val hhf_conv : (Proof.context -> conv) (*premise conv*)
            -> (Proof.context -> conv) (*concl conv*)
            -> Proof.context -> conv
(*for any meta premise or HOL premise, meta quantification or HOL quantification*)
val premises_conv : (Proof.context -> conv) (*premise conv*)
                  -> (Proof.context -> conv) (*concl conv*)
                  -> Proof.context -> conv
val recursive_premises_conv : (Proof.context -> conv) -> Proof.context -> conv

val rewrite_leading_antecedent : Proof.context -> thm list -> thm -> thm
val simplify_leading_antecedent : Proof.context -> thm -> thm
val simplify_leading_antecedent_hhf_concl : Proof.context -> thm -> thm

end

structure Phi_Helper_Conv : PHI_HELPER_CONV = struct
open Phi_Helper_Conv Conv

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


val protect_conv = rewr_conv @{thm Pure.prop_def[symmetric]}
val unprotect_conv = rewr_conv @{thm Pure.prop_def}


fun leading_antecedent_conv C = implies_conv C all_conv
fun hhf_concl_conv C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (hhf_concl_conv C o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.arg_conv (hhf_concl_conv C ctxt) ctm
     | _ => C ctxt ctm

fun hhf_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (hhf_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (hhf_conv Cp Cc ctxt) ctm
     | _ => Cc ctxt ctm

fun premises_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (premises_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => HOLogic.Trueprop_conv (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (Cp ctxt)) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.All\<close>, _) $ Abs _ =>
          Conv.arg_conv (Conv.abs_conv (premises_conv Cp Cc o snd) ctxt) ctm
     | _ => Cc ctxt ctm

fun recursive_premises_conv C ctxt ctm =
  premises_conv (fn ctxt => fn ctm =>
      case Thm.term_of ctm
        of Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.All\<close>, _) $ _ ) =>
              recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ ) =>
              recursive_premises_conv C ctxt ctm
         | _ => C ctxt ctm)
    (K Conv.all_conv) ctxt ctm


fun rewrite_leading_antecedent ctxt rules =
  Conv.gconv_rule (Raw_Simplifier.rewrite ctxt true rules) 1

fun simplify_leading_antecedent ctxt =
  Conv.gconv_rule (Simplifier.rewrite ctxt) 1

fun simplify_leading_antecedent_hhf_concl ctxt =
  Conv.gconv_rule (hhf_concl_conv Simplifier.rewrite ctxt) 1


end