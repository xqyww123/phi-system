signature PLPR_SYNTAX = sig

val guardize : Proof.context -> int (*N*) -> thm -> thm
  (*tags leading N antecedents as reasoning guards*)
val merge_guards : Proof.context -> thm -> thm
  (*if the rule contains multiple guards, move them into the beginning and consolidate them into one.
    When moving an antecedent not at the beginning, all the previous antecedents before it are
    also tagged as reasoning guards.*)

val rulify_antecedent : bool (*deep*) -> Proof.context -> conv (*converts an antecedent*)
      (*deep: if true, rulify by Phi_Conv.iso_rulify_conv, pure connectives embedded into HOL*)
val atomize_antecedent : bool (*deep*) -> Proof.context -> conv (*converts an antecedent*)
      (*deep: if true, atomize by Phi_Conv.iso_atomize_conv, pure connectives into HOL*)
val elim_leading_All : Proof.context -> thm -> thm
      (*eliminates the leading Pure.all and meta_Balls to schematic variables*)

val unfold_antecedents : bool (*deep*) -> Proof.context -> thm -> thm (*unfolding \<and>, \<and>\<^sub>\<r>, \<longrightarrow>, \<forall>, for all antecedents in a rule*)
val unfold_leading_antecedent : bool (*deep*) -> Proof.context -> thm -> int * thm
      (*the int: how many new antecedent are introduced.*)

val contract_leading_antecedents : bool (*deep*) -> int -> Proof.context -> thm -> thm
      (*the int: how many leading antecedents are considered.*)

val mk_ant_sequence : term list -> term
val intro_ant_sequence : Proof.context -> thm list -> thm
val elim_ant_sequence : thm -> thm list

end

structure PLPR_Syntax : PLPR_SYNTAX = struct

fun guardize ctxt =
  let fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ P =>
            (case P of Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _ => Conv.all_conv ctm
                     | _ => Conv.arg_conv (Conv.rewr_conv (
                              Thm.transfer' ctxt @{thm' \<r>Guard_def[symmetric]})) ctm)
           | _ => (Phi_Conv.atomize_conv ctxt then_conv conv) ctm
      fun move_and_merge_ants N ctm =
        case N of 0 => Conv.all_conv ctm
                | 1 => Conv.implies_conv conv Conv.all_conv ctm
                | _ =>
         (Conv.implies_conv conv (move_and_merge_ants (N-1)) then_conv
          Conv.rewr_conv @{lemma \<open>(\<g>\<u>\<a>\<r>\<d> P \<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Q \<Longrightarrow> PROP R) \<equiv> (\<g>\<u>\<a>\<r>\<d> P \<and>\<^sub>\<r> Q \<Longrightarrow> PROP R)\<close>
                              by (unfold \<r>Guard_def Ant_Seq_imp)}) ctm
  in fn N => Conv.fconv_rule (move_and_merge_ants N)
 end

fun merge_guards ctxt rule =
  let fun is_guard (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _)) = true
        | is_guard _ = false
      
      val last_ind = find_index is_guard (rev (Thm.prems_of rule))
   in if last_ind = ~1 then rule
      else guardize ctxt (Thm.nprems_of rule - last_ind) rule
  end

(*fun reduce_constant_True ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _)) =>
          Conv.rewr_conv @{lemma' \<open>(PROP P \<Longrightarrow> True) \<equiv> Trueprop True\<close>
                              by (rule, simp) } ctm
     | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _,
          Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _)) =>
          Conv.rewr_conv @{lemma' \<open>(\<And>x. True) \<equiv> Trueprop True\<close>
                              by (rule, simp) } ctm
     | Const(\<^const_name>\<open>meta_case_prod\<close>, _) $ Abs (_, _, Abs (_, _, \<^Const>\<open>True\<close>)) $ _ =>
          Conv.rewr_conv @{lemma' \<open>meta_case_prod (\<lambda>_ _. Trueprop True) x \<equiv> Trueprop True\<close>
                              by (unfold meta_case_prod_def)} ctm
     | Const(\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ Abs (_, _, \<^Const>\<open>True\<close>) =>
          Conv.rewr_conv @{lemma' \<open>meta_Ball S (\<lambda>_. Trueprop True) \<equiv> Trueprop True\<close>
                              by (unfold meta_Ball_def, rule, blast)} ctm
     | _ => Conv.all_conv ctm
*)

fun reduce_constant_True_left ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _)) $ _ =>
          Conv.rewr_conv @{lemma \<open>(True \<Longrightarrow> PROP P) \<equiv> PROP P\<close>
                              by (rule, simp) } ctm
     | _ => Conv.all_conv ctm

fun elim_leading_All ctxt rule =
  let fun rename_all2 NONE rule = rule
        | rename_all2 (SOME (N1, N2)) rule =
            let val (A1 $ Abs (_, T1, A2 $ Abs (_, T2, X))) = Thm.prop_of rule
             in Thm.renamed_prop (A1 $ Abs (N1, T1, A2 $ Abs (N2, T2, X))) rule
            end
      fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
              (Conv.rewr_conv @{thm' meta_Ball_def} then_conv
               Phi_Conv.meta_all_conv (conv o snd) ctxt) ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.all\<close>, _) $ _) =>
              (Conv.rewr_conv Drule.norm_hhf_eq then_conv conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _,
                (Const(\<^const_name>\<open>meta_case_prod\<close>, _) $ B $ _)) =>
              let val names = case B of Abs (N,_,Abs (N',_,_)) => SOME (N,N') | _ => NONE
                  val rule = @{lemma' \<open>(\<And>x. PROP meta_case_prod P x) \<equiv> (\<And>a b. PROP P a b)\<close>
                                  by (simp add: split_paired_all)}
               in rename_all2 names (Conv.rewr_conv rule ctm)
              end
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, Const(\<^const_name>\<open>Trueprop\<close>, _) $ 
                (Const(\<^const_name>\<open>case_prod\<close>, _) $ B $ _)) =>
              let val names = case B of Abs (N,_,Abs (N',_,_)) => SOME (N,N') | _ => NONE
                  val rule = @{lemma' \<open>(\<And>x. case_prod P x) \<equiv> (\<And>a b. P a b)\<close>
                                  by (simp add: split_paired_all)}
               in rename_all2 names (Conv.rewr_conv rule ctm)
              end
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
              Phi_Conv.meta_all_conv (conv o snd) ctxt ctm
           | _ => Conv.all_conv ctm
   in rule
   |> Conv.fconv_rule (conv ctxt)
   |> Thm.forall_elim_vars (Thm.maxidx_of rule)
  end

fun rulify_antecedent deep =
  let fun rulify_case_prods cv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
            (case X
               of Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ _ =>
                    (Conv.rewr_conv @{thm' atomize_case_prod[symmetric]} then_conv
                     Phi_Conv.meta_case_prod_conv (rulify_case_prods cv o snd) Conv.all_conv ctxt then_conv
                     Conv.try_conv (Conv.rewr_conv (Thm.transfer' ctxt
                          @{lemma' \<open>meta_case_prod (\<lambda>_ _. Trueprop True) x \<equiv> Trueprop True\<close>
                               by (unfold meta_case_prod_def)}))) ctm
                | _ => cv ctxt ctm
            )
           | _ => cv ctxt ctm
      fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
            (case X
               of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
                    (Conv.rewr_conv @{thm' atomize_all[symmetric]} then_conv
                     Phi_Conv.meta_all_conv (conv o snd) ctxt then_conv
                     Conv.try_conv (Conv.rewr_conv @{lemma' \<open>(\<And>x. True) \<equiv> Trueprop True\<close>
                                                        by (rule, simp) })) ctm
                | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
                    (Conv.rewr_conv @{thm' atomize_imp[symmetric]} then_conv
                     Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) then_conv
                     Conv.try_conv (Conv.rewr_conv @{lemma' \<open>(PROP P \<Longrightarrow> True) \<equiv> Trueprop True\<close>
                                                        by (rule, simp) })) ctm
                | Const(\<^const_name>\<open>Set.Ball\<close>, _) $ _ $ _ =>
                    (Conv.rewr_conv @{thm' atomize_Ball[symmetric]} then_conv
                     Phi_Conv.meta_ball_conv Conv.all_conv (rulify_case_prods conv o snd) ctxt then_conv
                     Conv.try_conv (Conv.rewr_conv @{lemma' \<open>meta_Ball S (\<lambda>_. Trueprop True) \<equiv> Trueprop True\<close>
                                                        by (unfold meta_Ball_def, rule, blast)})) ctm
                | _ => if deep then Phi_Conv.iso_rulify_conv ctxt ctm
                       else Conv.all_conv ctm)
           | _ => if deep then Phi_Conv.iso_rulify_conv ctxt ctm
                  else Conv.all_conv ctm
   in conv
  end


fun atomize_antecedent deep =
  let fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
              (Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) then_conv
               Conv.rewr_conv @{thm' atomize_imp}) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
              (Phi_Conv.meta_all_conv (conv o snd) ctxt then_conv
               Conv.rewr_conv @{thm' atomize_all}) ctm
           | _ => if deep then Phi_Conv.iso_atomize_conv ctxt ctm
                  else Conv.all_conv ctm
   in conv
  end

fun unfold_antecedents deep ctxt rule =
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
              (Conv.combination_conv (Conv.arg_conv (rulify_antecedent deep ctxt))
                                     (conv ctxt) then_conv
               reduce_constant_True_left) ctm
           | _ => Conv.all_conv ctm
   in Conv.fconv_rule (conv ctxt) rule
  end

fun unfold_leading_antecedent deep ctxt rule =
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
              (Conv.combination_conv (Conv.arg_conv (rulify_antecedent deep ctxt))
                                     (if N = 1 then Conv.all_conv else conv (N-1) ctxt) then_conv
               reduce_constant_True_left) ctm
           | _ => Conv.all_conv ctm
      val rule' = Conv.fconv_rule (conv 1 ctxt) rule
   in (!num, rule')
  end

fun contract_leading_antecedents deep N ctxt rule =
  let fun conv N ctxt ctm =
        case N
          of 0 => Conv.all_conv ctm
           | 1 => Conv.implies_conv (atomize_antecedent deep ctxt) Conv.all_conv ctm
           | _ =>(case Thm.term_of ctm
                    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                        (Conv.combination_conv (Conv.arg_conv (atomize_antecedent deep ctxt))
                                               (conv (N-1) ctxt) then_conv
                         Conv.rewr_conv @{thm' Ant_Seq_imp[symmetric]}) ctm
                     | _ => raise CTERM ("contract_leading_antecedents: insufficient antecedents", []))
   in Conv.fconv_rule (conv N ctxt) rule
  end

val ant_seq = \<^Const>\<open>Ant_Seq\<close>
fun mk_ant_sequence [] = \<^const>\<open>True\<close>
  | mk_ant_sequence L = foldr1 (fn (t1,t2) => ant_seq $ t1 $ t2) L

fun intr_ant_seq ctxt thP thQ =
  let
    val (P, Q) = apply2 (Object_Logic.dest_judgment ctxt o Thm.cprop_of) (thP, thQ)
      handle CTERM (msg, _) => raise THM (msg, 0, [thP, thQ]);
    val rule = \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<Longrightarrow> Q \<Longrightarrow> P \<and>\<^sub>\<r> Q\<close> by (rule Ant_Seq_I)\<close>
  in Drule.implies_elim_list rule [thP, thQ] end;

fun intro_ant_sequence _ [] = @{thm' TrueI}
  | intro_ant_sequence ctxt L = foldr1 (uncurry (intr_ant_seq ctxt)) L

fun elim_ant_seq thPQ =
  let
    val _ = case Thm.prop_of thPQ
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _) => ()
               | _ => raise THM ("elim_ant_seq", 0, [thPQ])
    val (P, Q) = Thm.dest_binop (Thm.dest_arg (Thm.cprop_of thPQ))
      handle CTERM (msg, _) => raise THM (msg, 0, [thPQ]);
    val thP =
      Thm.implies_elim \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<and>\<^sub>\<r> Q \<Longrightarrow> P\<close> by (unfold Ant_Seq_def, rule conjunct1)\<close> thPQ;
    val thQ =
      Thm.implies_elim \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<and>\<^sub>\<r> Q \<Longrightarrow> Q\<close> by (unfold Ant_Seq_def, rule conjunct2)\<close> thPQ;
  in (thP, thQ) end;

fun elim_ant_sequence th =
  case Thm.prop_of th
    of \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> => []
     | _ => let fun elim th =
                  let val (th1, th2) = elim_ant_seq th
                   in elim th1 @ elim th2
                  end handle THM _ => [th]
             in elim th
            end

end