signature PHI_CONV = sig
include PHI_CONV

val unfold_meta_ball : conv -> conv
val unfold_meta_ball_default : Proof.context -> conv


end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv




(*C: converts the domain set*)
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