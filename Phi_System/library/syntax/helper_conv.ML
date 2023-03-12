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

val quant_conv : string -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val hol_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_all_body_conv : (Proof.context -> conv) -> Proof.context -> conv

val leading_antecedent_conv : conv -> conv
val hhf_concl_conv : (Proof.context -> conv) -> Proof.context -> conv

val may_Trueprop_conv : conv -> conv

val rewrite_leading_antecedent : Proof.context -> thm list -> thm -> thm
val simplify_leading_antecedent : Proof.context -> thm -> thm
val simplify_leading_antecedent_hhf_concl : Proof.context -> thm -> thm

end

structure Phi_Helper_Conv : PHI_HELPER_CONV = struct
open Phi_Helper_Conv Conv

fun aggregate_imps C c =
  (implies_conv C (aggregate_imps C else_conv rewr_conv @{thm PURE_TOP_imp[symmetric]})
   then_conv rewr_conv @{thm conjunction_imp[symmetric]}) c

fun expand_aggregated_imps C c =
  (rewr_conv @{thm PURE_TOP_imp} else_conv
  (rewr_conv @{thm conjunction_imp} then_conv
   implies_conv C (expand_aggregated_imps C))) c

fun aggregate_imps_obj C ctxt c =
 ((implies_conv (C ctxt then_conv atomize_conv ctxt)
                (aggregate_imps_obj C ctxt)
   then_conv rewr_conv @{thm conj_imp_eq_imp_imp[symmetric]})
  else_conv rewr_conv @{thm True_implies_equals[symmetric]}) c

fun expand_aggregated_imps_obj C ctxt c =
  (rewr_conv @{thm True_implies_equals} else_conv
  (rewr_conv @{thm conj_imp_eq_imp_imp} then_conv
   implies_conv (rulify_conv ctxt then_conv C ctxt)
                (expand_aggregated_imps_obj C ctxt))) c


val protect_conv = rewr_conv @{thm Pure.prop_def[symmetric]}
val unprotect_conv = rewr_conv @{thm Pure.prop_def}


fun is_strict_reflexive th = (op =) (Logic.dest_equals (Thm.prop_of th))
  handle TERM _ => false;

fun abs_conv cv ctxt ct =
  (case Thm.term_of ct of
    Abs (a, _, _) =>
      let
        val ((v, ct'), ctxt') = Variable.dest_abs_cterm ct ctxt;
        val eq = cv (v, ctxt') ct';
      in if is_strict_reflexive eq then all_conv ct else Thm.abstract_rule a v eq end
  | _ => raise CTERM ("abs_conv", [ct]));


fun quant_conv head cv ctxt ct =
  (case Thm.term_of ct of Const (N, _) $ Abs _ =>
      if N = head then Conv.arg_conv (abs_conv cv ctxt) ct
                  else raise CTERM ("quant_conv", [ct])
  | _ => raise CTERM ("quant_conv", [ct]))

val hol_all_conv = quant_conv \<^const_name>\<open>All\<close>

fun meta_all_body_conv C ctxt =
  forall_conv (fn (_, ctxt) => meta_all_body_conv C ctxt) ctxt
  else_conv C ctxt

fun leading_antecedent_conv C = implies_conv C all_conv
fun hhf_concl_conv C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => Conv.forall_conv (hhf_concl_conv C o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => raise CTERM ("hhf_concl_conv", [ctm])
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.arg_conv (hhf_concl_conv C ctxt) ctm
     | _ => C ctxt ctm

fun may_Trueprop_conv cv ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv cv ct
  | _ => cv ct)

fun rewrite_leading_antecedent ctxt rules =
  Conv.gconv_rule (Raw_Simplifier.rewrite ctxt true rules) 1

fun simplify_leading_antecedent ctxt =
  Conv.gconv_rule (Simplifier.rewrite ctxt) 1

fun simplify_leading_antecedent_hhf_concl ctxt =
  Conv.gconv_rule (hhf_concl_conv Simplifier.rewrite ctxt) 1

end