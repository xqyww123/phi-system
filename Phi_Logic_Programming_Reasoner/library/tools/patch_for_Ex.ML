signature PHI_REASONERS = sig

val existential_obligation : int Config.T

end

structure Phi_Reasoners : PHI_REASONERS = struct

val existential_obligation = Config.declare_int ("Phi_Reasoners.existential_obligation", \<^here>) (K 2)

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>reason_mode_existential_obligation\<close> (
    Scan.lift (\<^keyword>\<open>=\<close> |--
      (Args.$$$ "yes" >> K 1 || Args.$$$ "no" >> K 0 || Args.$$$ "enhanced" >> K 2))
    >> (fn mode => Thm.declaration_attribute (K (Config.put_generic existential_obligation mode)))
  ) "set the mode how \<phi>-LPR generates existential quantificatino in the obligation.\n\
    \0: do not generate existence in obligations, leaving them schematic variables\n\
    \1: generate existence in obligations\n\
    \2: generate existence in obligations and apply a special patch on them to enhance the automation\
    \of Isabelle for solving them (using introduction rules)"
)

end

signature PHI_CONV = sig

include PHI_CONV

val move_Ex_inside_All : Proof.context -> conv
val move_Ex_inside_All_exhausitive : (Proof.context -> conv) -> Proof.context -> conv

val move_sp_Ex_inside_All : Proof.context -> conv
val move_sp_Ex_inside_All_exhausitive : (Proof.context -> conv) -> Proof.context -> conv

val move_Ex_downto_Disj : conv
val move_Ex_downto_Disj_exhaustive : conv -> conv

val move_sp_Ex_downto_Disj : conv
val move_sp_Ex_downto_Disj_exhaustive : conv -> conv

end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

fun gen_move_Ex_inside_All (Ex_name, rule) ctxt ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
    case Thm.term_of ctm
      of Const(Ex_name, _) $ (Abs(_, _, Const(\<^const_name>\<open>All\<close>, _) $ _)) =>
          let val (Ex, ctm1) = Thm.dest_comb ctm
              val ( f, ctm2) = Thm.dest_abs_global ctm1
              val (Al, ctm3) = Thm.dest_comb ctm2
              val ( x, body) = Thm.dest_abs_global ctm3
              val fx = Thm.apply f x
              val Q = Thm.lambda x (Thm.lambda fx body)
              val rule = Drule.infer_instantiate ctxt [(("Q",0),Q)] rule
           in Conv.rewr_conv rule ctm
          end
       | _ => raise CTERM ("move_Ex_inside_All", [])
  ) ctm

val move_Ex_inside_All = gen_move_Ex_inside_All
      (\<^const_name>\<open>Ex\<close>, @{thm' choice_iff[folded atomize_eq, symmetric]})
val move_sp_Ex_inside_All = gen_move_Ex_inside_All
      (\<^const_name>\<open>special_Ex\<close>, @{thm' choice_iff[folded atomize_eq special_Ex_def, symmetric]})

fun move_Ex_inside_All_exhausitive C ctxt ctm =
  (move_Ex_inside_All ctxt then_conv
   hol_all_conv (move_Ex_inside_All_exhausitive C o snd) ctxt) ctm
  handle CTERM _ => C ctxt ctm

fun move_sp_Ex_inside_All_exhausitive C ctxt ctm =
  (move_sp_Ex_inside_All ctxt then_conv
   hol_all_conv (move_sp_Ex_inside_All_exhausitive C o snd) ctxt) ctm
  handle CTERM _ => C ctxt ctm

val move_Ex_downto_Disj = Conv.rewr_conv @{thm' HOL.ex_disj_distrib[folded atomize_eq]}
val move_sp_Ex_downto_Disj = Conv.rewr_conv @{thm' HOL.ex_disj_distrib[folded atomize_eq special_Ex_def]}

fun gen_move_Ex_downto_Disj_exhaustive move_Ex_downto_Disj =
let fun move_Ex_downto_Disj_exhaustive C ctm =
      (move_Ex_downto_Disj then_conv (fn ctm =>
         case Thm.term_of ctm
           of \<^Const>\<open>HOL.disj\<close> $ _ $ _ =>
                Conv.combination_conv (Conv.arg_conv (move_Ex_downto_Disj_exhaustive C))
                                      (move_Ex_downto_Disj_exhaustive C) ctm
            | _ => error "Internal bug"
       )) ctm
      handle CTERM _ => C ctm
 in move_Ex_downto_Disj_exhaustive
end

val move_Ex_downto_Disj_exhaustive = gen_move_Ex_downto_Disj_exhaustive move_Ex_downto_Disj
val move_sp_Ex_downto_Disj_exhaustive = gen_move_Ex_downto_Disj_exhaustive move_sp_Ex_downto_Disj

end
