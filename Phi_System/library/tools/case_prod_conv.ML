signature PHI_CONV = sig
include PHI_CONV

val prod_case_meta_all_split_conv : (Proof.context -> conv) -> Proof.context -> conv
val meta_ball_conv_all : (Proof.context -> conv) -> Proof.context -> conv

val unfold_meta_ball : conv -> conv
val unfold_meta_ball_default : Proof.context -> conv


end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

fun prod_case_meta_all_split_conv C ctxt ctm =
  let fun has_case_prod (Const (\<^const_name>\<open>meta_case_prod\<close>, _)) = SOME @{thm meta_case_prod_simp}
        | has_case_prod (Const (\<^const_name>\<open>case_prod\<close>, _)) = SOME @{thm prod.case[folded atomize_eq]}
        | has_case_prod (X $ _) = has_case_prod X
        | has_case_prod (Abs (_,_,X)) = has_case_prod X
        | has_case_prod _ = NONE
   in case Thm.term_of ctm
        of Const(\<^const_name>\<open>Pure.all\<close>, _) $ X =>
            (case has_case_prod X
               of SOME rule =>
                    (Conv.rewr_conv @{thm split_paired_all} then_conv
                     meta_all_conv (fn (_,ctxt') =>
                        meta_all_conv (K (Conv.rewr_conv rule)) ctxt' then_conv
                        prod_case_meta_all_split_conv C ctxt') ctxt) ctm
                | NONE => C ctxt ctm)
         | _ => raise CTERM ("prod_case_meta_all_split_conv: not a meta-all quantification", [ctm])
  end

fun meta_ball_conv_all C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
         (Conv.rewr_conv @{thm meta_Ball_def} then_conv
          prod_case_meta_all_split_conv (meta_all_conv (fn (_,ctxt') =>
              Conv.implies_concl_conv (meta_ball_conv_all C ctxt'))) ctxt
         ) ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Ball\<close>, _) $ _ $ _ ) =>
         (Conv.rewr_conv @{thm Ball_for_reason} then_conv
          prod_case_meta_all_split_conv (meta_all_conv (fn (_,ctxt') =>
              Conv.implies_concl_conv (meta_ball_conv_all C ctxt'))) ctxt
         ) ctm
     | _ => C ctxt ctm

(*C: convert the domain set*)
fun unfold_meta_ball C ctm =
  let fun conv ctm =
        case Thm.term_of ctm
          of _ $ (Const(\<^const_name>\<open>Set.insert\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) $ Const(\<^const_name>\<open>bot\<close>, _)) $ _ =>
                  (Conv.rewr_conv @{thm' meta_Ball_pair} then_conv conv) ctm
           | _ $ (Const(\<^const_name>\<open>Set.insert\<close>, _) $ _ $ Const(\<^const_name>\<open>bot\<close>, _)) $ _ =>
                  Conv.rewr_conv @{thm' meta_Ball_sing} ctm
           | _ => Conv.rewr_conv @{thm' meta_Ball_def[unfolded Premise_def]} ctm
   in case Thm.term_of ctm
        of Const(\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
              (Conv.arg1_conv C then_conv conv) ctm
         | _ => raise CTERM ("Phi_Conv.unfold_meta_ball", [ctm])
  end

fun unfold_meta_ball_default ctxt =
  unfold_meta_ball (Simplifier.rewrite (ctxt addsimps @{thms' sing_times_sing sing_if}))

end