signature PHI_REASONERS = sig
include PHI_REASONERS

val tag_having_bubbling : Proof.context -> conv

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

val tag_having_bubbling = Phi_Syntax.conv_items_of_assertion (fn ctxt => fn ctm =>
      let fun tag ctm =
            let val (_, args) = Term.strip_comb (Thm.term_of ctm)
                fun has_bubbling (Const(\<^const_name>\<open>Has_Bubbling\<close>, _) $ _) = true
                  | has_bubbling (Const(\<^const_name>\<open>Bubbling\<close>, _) $ _) = true
                  | has_bubbling (Abs (_, _, X)) = has_bubbling X
                  | has_bubbling _ = false
             in if exists has_bubbling args
             then Conv.rewr_conv @{thm Has_Bubbling_def[symmetric]} ctm
             else Conv.all_conv ctm
            end
       in case Thm.term_of ctm
       of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ =>
            Conv.arg_conv (Phi_Conv.bottom_conv_by_comb_layers (K tag) ctxt) ctm
        | _ => Conv.all_conv ctm
      end )

end