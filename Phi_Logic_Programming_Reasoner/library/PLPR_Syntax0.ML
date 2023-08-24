signature PLPR_SYNTAX = sig

val merge_guards (*if the rule contains multiple guards, move them into the beginning and
                   consolidate them into one*) : Proof.context -> thm -> thm

val rulify_antecedent : Proof.context -> conv (*converts an antecedent*)
val unfold_antecedents : Proof.context -> thm -> thm (*unfolding \<and>, \<and>\<^sub>\<r>, \<longrightarrow>, \<forall>, for all antecedents in a rule*)
val unfold_leading_antecedent : Proof.context -> thm -> int * thm
      (*the int: how many new antecedent are introduced.*)

end

structure PLPR_Syntax : PLPR_SYNTAX = struct

val merge_guard_rule = @{lemma \<open>(\<g>\<u>\<a>\<r>\<d> P \<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Q \<Longrightarrow> PROP R) \<equiv> (\<g>\<u>\<a>\<r>\<d> P \<and>\<^sub>\<r> Q \<Longrightarrow> PROP R)\<close>
                            by (unfold \<r>Guard_def Ant_Seq_imp)}

fun merge_guards ctxt rule =
  fold_index (fn (i,prem) => fn (meet, rule) =>
    case Logic.strip_assums_concl prem
      of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _) =>
          if meet = 0
          then (1, Thm.permute_prems 0 i rule)
          else Thm.permute_prems 1 (i-meet) rule
                |> Conv.fconv_rule (Conv.rewr_conv merge_guard_rule)
                |> Thm.permute_prems 1 (~ (i-meet))
                |> pair (meet + 1)
       | _ => (meet, rule)
  ) (Thm.prems_of rule) (0, rule)
  |-> (fn meet =>
    if meet = 0 then I
    else Conv.gconv_rule (Conv.top_rewrs_conv @{thms' Ant_Seq_assoc} ctxt) 1)

fun rulify_antecedent ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
      (case X
         of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
              (Conv.rewr_conv @{thm' atomize_all[symmetric]} then_conv
               Phi_Conv.meta_all_conv (rulify_antecedent o snd) ctxt) ctm
          | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
              (Conv.rewr_conv @{thm' atomize_imp[symmetric]} then_conv
               Conv.arg_conv (rulify_antecedent ctxt)) ctm
          | _ => Conv.all_conv ctm)
     | _ => Conv.all_conv ctm

fun unfold_antecedents ctxt rule =
  let fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _))
                $ _ =>
              (Conv.rewr_conv @{thm' Ant_Seq_imp} then_conv conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _))
                $ _ =>
              (Conv.rewr_conv @{thm' conj_imp_eq_imp_imp} then_conv conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
              (Conv.combination_conv (Conv.arg_conv (rulify_antecedent ctxt))
                                     (conv ctxt)) ctm
           | _ => Conv.all_conv ctm
   in Conv.fconv_rule (conv ctxt) rule
  end

fun unfold_leading_antecedent ctxt rule =
  let val num = Unsynchronized.ref 0
      fun conv N ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _))
                $ _ =>
              (num := !num + 1 ;
              (Conv.rewr_conv @{thm' Ant_Seq_imp} then_conv conv (N+1) ctxt) ctm)
           | Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _))
                $ _ =>
              (num := !num + 1 ;
              (Conv.rewr_conv @{thm' conj_imp_eq_imp_imp} then_conv conv (N+1) ctxt) ctm)
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
              (Conv.combination_conv (Conv.arg_conv (rulify_antecedent ctxt))
                                     (if N = 1 then Conv.all_conv else conv (N-1) ctxt)) ctm
           | _ => Conv.all_conv ctm
      val rule' = Conv.fconv_rule (conv 1 ctxt) rule
   in (!num, rule')
  end

end