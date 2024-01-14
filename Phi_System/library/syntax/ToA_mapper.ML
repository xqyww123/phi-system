signature PHI_SYNTAX = sig
include PHI_SYNTAX

val dest_ToA_Extract : term -> term * term
val dest_ToA_Subst : term -> term * term * term * term
val dest_ToA_Mapper : term -> term * term * term * term * term * term * term * term * term

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

val dest_ToA_Extract = PLPR_Syntax.dest_tags
                    #> Phi_Help.dest_binop \<^const_name>\<open>ToA_Extract\<close>
val dest_ToA_Subst = PLPR_Syntax.dest_tags
                  #> Phi_Help.dest_quadop \<^const_name>\<open>ToA_Subst\<close>
val dest_ToA_Mapper = PLPR_Syntax.dest_tags
                   #> (fn Const(\<^const_name>\<open>ToA_Mapper\<close>, _) $ g $ U $ U' $ f $ T $ T' $ h $ s $ D =>
                              (g,U,U',f,T,T',h,s,D)
                        | X => raise TERM("dest_ToA_Mapper", [X]))

end