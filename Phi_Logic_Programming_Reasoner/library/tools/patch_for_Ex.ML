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

(* (P \<longrightarrow> Q1) \<and> (P \<longrightarrow> Q2) \<and> \<dots> \<and> (P --> Qn) *)
val zip_conjs : conv
(*recursively for each nested implication*)
val zip_conjs_recursively : conv

(* (\<forall>x. P1 x) \<and> (\<forall>x. P2 x) \<dots> \<and> (\<forall>x. Pn x) \<longrightarrow> (\<forall>x. P1 x \<and> P2 x \<and> \<dots> Pn x)) *)
val zip_Alls : conv
val zip_Alls_recursively : Proof.context -> conv

val zip_All_conj_recursively : Proof.context -> conv

val move_Ex_inside_All : Proof.context -> conv
val move_Ex_inside_All_recursive : (Proof.context -> conv) -> Proof.context -> conv

val move_sp_Ex_inside_All : Proof.context -> conv
val move_sp_Ex_inside_All_recursive : (Proof.context -> conv) -> Proof.context -> conv

val move_Ex_downto_Disj : conv
val move_Ex_downto_Disj_recursive : conv -> conv

val move_sp_Ex_downto_Disj : conv
val move_sp_Ex_downto_Disj_recursive : conv -> conv

(*move to inside any \<forall> and \<or>, with zip over \<and> and \<forall>, exhaustively*)
val move_Ex_inside_exhaustively : Proof.context -> conv
val move_sp_Ex_inside_exhaustively : Proof.context -> conv

end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

fun zip_conjs ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
        HOLogic.conj_conv zip_conjs zip_conjs ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
        HOLogic.conj_conv Conv.all_conv zip_conjs ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =>
        Conv.rewr_conv @{thm' imp_conjR[folded atomize_eq, symmetric]} ctm
     | _ => raise CTERM ("Phi_Conv.zip_conjs", [ctm])

fun zip_conjs_recursively ctm =
  (zip_conjs then_conv HOLogic.imp_conv Conv.all_conv zip_conjs_recursively) ctm
  handle CTERM _ => Conv.all_conv ctm

fun zip_Alls ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
        HOLogic.conj_conv zip_Alls zip_Alls ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
        HOLogic.conj_conv Conv.all_conv zip_Alls ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ ) =>
        Conv.rewr_conv @{thm' all_conj_distrib[folded atomize_eq, symmetric]} ctm
     | _ => raise CTERM ("Phi_Conv.zip_Alls", [ctm])

fun zip_Alls_recursively ctxt ctm =
  (zip_Alls then_conv HOLogic.All_conv (zip_Alls_recursively o snd) ctxt) ctm
  handle CTERM _ => Conv.all_conv ctm

fun zip_All_conj_recursively ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
        HOLogic.All_conv (zip_All_conj_recursively o snd) ctxt ctm
     | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
        HOLogic.imp_conv Conv.all_conv (zip_All_conj_recursively ctxt) ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ _ => let
            fun parse (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ _) = parse X
              | parse (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =
                  zip_Alls then_conv zip_All_conj_recursively ctxt
              | parse (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =
                  zip_conjs then_conv zip_All_conj_recursively ctxt
              | parse _ = raise CTERM ("Phi_Conv.zip_All_conj_recursively", [ctm])
         in parse X ctm
        end
     | _ => Conv.all_conv ctm



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

fun move_Ex_inside_All_recursive C ctxt ctm =
  (move_Ex_inside_All ctxt then_conv
   hol_all_conv (move_Ex_inside_All_recursive C o snd) ctxt) ctm
  handle CTERM _ => C ctxt ctm

fun move_sp_Ex_inside_All_recursive C ctxt ctm =
  (move_sp_Ex_inside_All ctxt then_conv
   hol_all_conv (move_sp_Ex_inside_All_recursive C o snd) ctxt) ctm
  handle CTERM _ => C ctxt ctm

val move_Ex_downto_Disj = Conv.rewr_conv @{thm' HOL.ex_disj_distrib[folded atomize_eq]}
val move_sp_Ex_downto_Disj = Conv.rewr_conv @{thm' HOL.ex_disj_distrib[folded atomize_eq special_Ex_def]}

fun gen_move_Ex_downto_Disj_recursive move_Ex_downto_Disj =
let fun move_Ex_downto_Disj_recursive C ctm =
      (move_Ex_downto_Disj then_conv (fn ctm =>
         case Thm.term_of ctm
           of \<^Const>\<open>HOL.disj\<close> $ _ $ _ =>
                Conv.combination_conv (Conv.arg_conv (move_Ex_downto_Disj_recursive C))
                                      (move_Ex_downto_Disj_recursive C) ctm
            | _ => error "Internal bug"
       )) ctm
      handle CTERM _ => C ctm
 in move_Ex_downto_Disj_recursive
end

val move_Ex_downto_Disj_recursive = gen_move_Ex_downto_Disj_recursive move_Ex_downto_Disj
val move_sp_Ex_downto_Disj_recursive = gen_move_Ex_downto_Disj_recursive move_sp_Ex_downto_Disj

fun gen_move_Ex_inside_exhaustively (ex_name, mv_disj, mv_all, rule_mv_imp) =
  let fun conv ctxt ctm =
        let val tm = case Thm.term_of ctm
                       of Const(N, _) $ Abs (_, _, X) =>
                            if N = ex_name then X
                            else raise CTERM ("Phi_Conv.move_Ex_inside_exhaustively", [ctm])
                        | _ =>   raise CTERM ("Phi_Conv.move_Ex_inside_exhaustively", [ctm])
         in case tm
         of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _  => mv_all conv ctm
          | Const(\<^const_name>\<open>HOL.disj\<close>, _) $ _ $ _  =>
              move_Ex_downto_Disj_recursive (conv ctxt) ctm 
          | Const(N, _) $ Abs (_, _, Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =>
            ((Conv.rewr_conv rule_mv_imp then_conv
              Conv.arg_conv (conv ctxt)) ctm
             handle CTERM _ => Conv.all_conv ctm )
          | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ _ =>
              Phi_Conv.quant_conv ex_name (zip_All_conj_recursively o snd) ctxt ctm
          | _ => Conv.all_conv ctm
        end
   in conv
  end

end
