signature PLPR_SYNTAX = sig
include PLPR_SYNTAX

val merge_conditions : thm -> thm

val guardize : {merge_cond: bool} -> Context.generic -> int (*N*) -> thm -> thm
  (*tags leading N antecedents as reasoning guards*)
val merge_guards : {merge_cond: bool} -> Context.generic -> thm -> thm
  (*If the rule contains multiple guards, aggregate them into one guard.
    If there is any non-guard antecedent before a guard, mark the antecedent as a guard.*)

val atomize_antecedent : bool (*deep*) -> Proof.context -> conv (*converts an antecedent*)
      (*deep: if true, atomize by Phi_Conv.iso_atomize_conv, pure connectives into HOL*)
val elim_leading_All : Proof.context -> thm -> thm
      (*eliminates the leading Pure.all and meta_Balls to schematic variables*)

val rulify_antecedents : bool (*deep*) -> int (*number of antecedents to be rulified at most*)
                      -> Proof.context -> thm -> int * thm
      (*unfolds \<and>, \<and>\<^sub>\<r>, \<longrightarrow>, \<forall>, for all antecedents in a rule
        deep: if true, rulify by Phi_Conv.iso_rulify_conv, pure connectives embedded into HOL
        number of antecedents: ~1 for exhaustively all, Thm.nprems_of + 1 means to rulify the conclusion
        returns how many new antecedent are introduced.*)

val contract_leading_antecedents : bool (*deep*) -> int -> Proof.context -> thm -> thm
      (*the int: how many leading antecedents are considered.*)

val mk_ant_sequence : term list -> term
val dest_ant_sequence : term -> term list
val dest_ant_sequence_or_HOL_conj : term -> term list
val intro_ant_sequence : thm list -> thm
val elim_ant_sequence : thm -> thm list
val elim_ant_seq_or_HOL_conj : thm -> thm * thm
val elim_ant_sequence_or_HOL_conj : thm -> thm list

end

structure PLPR_Syntax : PLPR_SYNTAX = struct
open PLPR_Syntax

fun cond_can_merge \<^const_name>\<open>MODE_GUARD\<close> = true
  | cond_can_merge \<^const_name>\<open>default\<close> = true
  | cond_can_merge \<^const_name>\<open>MODE_SAFE\<close> = true
  | cond_can_merge _ = false

val merge_conditions =
  let fun need_merge (Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(m1, _) $ _))
                $ (Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(m2, _) $ _))
                $ _))
            = cond_can_merge m1 andalso m1 = m2
        | need_merge _ = false

      fun qchk tm =
        need_merge tm orelse (case tm of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X => qchk X
                                       | _ => false)

      fun merge ctm =
        if need_merge (Thm.term_of ctm)
        then Conv.rewr_conv @{thm' contract_obligations} ctm
        else Conv.all_conv ctm

      fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => (Conv.arg_conv conv then_conv merge) ctm
           | _ => Conv.all_conv ctm

   in fn th => if qchk (Thm.prop_of th) then Conv.fconv_rule conv th else th
  end

val guard_atomize = [
  @{lemma' \<open>(P \<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Q) \<equiv> Trueprop (\<g>\<u>\<a>\<r>\<d> (P \<longrightarrow> Q))\<close>
       by (simp add: \<r>Guard_def atomize_imp)},
  @{lemma' \<open>(\<And>x. \<g>\<u>\<a>\<r>\<d> Q x) \<equiv> Trueprop (\<g>\<u>\<a>\<r>\<d> (\<forall>x. Q x))\<close>
       by (simp add: \<r>Guard_def atomize_all)}
]

fun guardize {merge_cond} ctxt =
  let fun conv guard_unfold ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ P =>
            (case P of Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _ => Conv.all_conv ctm
                     | _ => Conv.arg_conv (Conv.rewr_conv (
                              Thm.transfer'' ctxt @{thm' \<r>Guard_def[symmetric]})) ctm)
           | _ =>
             let val ctxt' = Context.proof_of ctxt
              in ((if guard_unfold
                   then Raw_Simplifier.rewrite ctxt' true guard_atomize
                   else Conv.all_conv)
              then_conv Phi_Conv.atomize_conv (Context.proof_of ctxt)
              then_conv conv guard_unfold) ctm
             end

      fun can_merge_cond (Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(m1, _) $ _)))
                $ (Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(m2, _) $ _)))
                $ _))
            = merge_cond andalso cond_can_merge m1 andalso m1 = m2
        | can_merge_cond _ = false

      fun move_and_merge_ants N ctm =
        case N of 0 => Conv.all_conv ctm
                | 1 => Conv.implies_conv (conv true) Conv.all_conv ctm
                | _ =>
         (Conv.implies_conv (conv true) (move_and_merge_ants (N-1)) then_conv
          (fn ctm => Conv.rewr_conv
               (if can_merge_cond (Thm.term_of ctm)
                then @{lemma \<open>(\<g>\<u>\<a>\<r>\<d> (Premise mode' P) \<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (Premise mode Q) \<Longrightarrow> PROP R) \<equiv> (\<g>\<u>\<a>\<r>\<d> (Premise mode (P \<and> Q)) \<Longrightarrow> PROP R)\<close>
                          by (unfold \<r>Guard_def contract_obligations)}
                else @{lemma \<open>(\<g>\<u>\<a>\<r>\<d> P \<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Q \<Longrightarrow> PROP R) \<equiv> (\<g>\<u>\<a>\<r>\<d> P \<and>\<^sub>\<r> Q \<Longrightarrow> PROP R)\<close>
                          by (unfold \<r>Guard_def Ant_Seq_imp)}
               ) ctm)) ctm

  in fn N => fn rule =>
      case N of 0 => rule
              | 1 => Conv.fconv_rule (Conv.implies_conv (conv false) Conv.all_conv) rule
              | _ => Conv.fconv_rule (move_and_merge_ants N) rule
 end


fun merge_guards {merge_cond} ctxt rule =
  let fun is_guard (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _)) = true
        | is_guard (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_guard X
        | is_guard (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = is_guard X
        | is_guard _ = false
      
      val last_ind = find_index is_guard (rev (Thm.prems_of rule))
   in if last_ind = ~1 then rule
      else guardize {merge_cond=merge_cond} ctxt (Thm.nprems_of rule - last_ind) rule
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
  let fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
              (Conv.rewr_conv @{thm' meta_Ball_def} then_conv conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.all\<close>, _) $ _) =>
              (Conv.rewr_conv Drule.norm_hhf_eq then_conv conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _,
                Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>meta_case_prod\<close>, _) $ _ $ _)) =>
              (Phi_Conv.prod_case_split_in_all_conv (K Conv.all_conv) ctxt then_conv
               conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _,
                (Const(\<^const_name>\<open>meta_case_prod\<close>, _) $ _ $ _)) =>
              (Phi_Conv.prod_case_split_in_all_conv (K Conv.all_conv) ctxt then_conv
               conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, Const(\<^const_name>\<open>Trueprop\<close>, _) $ 
                (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ (Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ _))) =>
              (Phi_Conv.prod_case_split_in_all_conv (K Conv.all_conv) ctxt then_conv
               conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, Const(\<^const_name>\<open>Trueprop\<close>, _) $ 
                (Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ _)) =>
              (Phi_Conv.prod_case_split_in_all_conv (K Conv.all_conv) ctxt then_conv
               conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _
                $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ _))) =>
              (Phi_Conv.prod_case_split_in_all_conv (K Conv.all_conv) ctxt then_conv
               conv ctxt) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
              Phi_Conv.meta_all_conv (conv o snd) ctxt ctm
           | _ => Conv.all_conv ctm
   in rule
   |> Conv.fconv_rule (conv ctxt)
   |> Thm.forall_elim_vars (Thm.maxidx_of rule+1)
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

(*N: numbers of leading antecedents to be rulified at most
  returns: numbers of new antecedent extracted*)
fun rulify_antecedents deep N ctxt thm =
  let fun conv N ctxt ctm =
        if N = 0 then Conv.all_conv ctm else
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
            (case X
               of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
                    (Conv.rewr_conv @{thm' atomize_all[symmetric]} then_conv
                     Phi_Conv.meta_all_conv (conv N o snd) ctxt then_conv
                     Conv.try_conv (Conv.rewr_conv @{lemma' \<open>(\<And>x. True) \<equiv> Trueprop True\<close>
                                                        by (rule, simp) })) ctm
                | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
                    (Conv.rewr_conv @{thm' atomize_imp[symmetric]} then_conv
                     Conv.combination_conv (Conv.arg_conv (conv ~1 ctxt)) (conv (N-1) ctxt) then_conv
                     Conv.try_conv (Conv.rewr_conv @{lemma' \<open>(PROP P \<Longrightarrow> True) \<equiv> Trueprop True\<close>
                                                        by (rule, simp) })) ctm
                | Const(\<^const_name>\<open>Set.Ball\<close>, _) $ _ $ _ =>
                    (Phi_Conv.rulify_Ball (conv N) ctxt then_conv
                     Conv.try_conv (Conv.rewr_conv @{lemma' \<open>meta_Ball S (\<lambda>_. Trueprop True) \<equiv> Trueprop True\<close>
                                                        by (unfold meta_Ball_def, rule, blast)})) ctm
                | _ => if deep then Phi_Conv.iso_rulify_conv ctxt ctm
                       else Conv.all_conv ctm)
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ Y $ _ =>
               (Conv.combination_conv (Conv.arg_conv (conv ~1 ctxt))
                                      (conv (N-1) ctxt) then_conv
                reduce_constant_True_left) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                  Phi_Conv.meta_all_conv (conv N o snd) ctxt ctm
           | _ => Conv.all_conv ctm

      val num = Unsynchronized.ref 0

      fun rule_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _))
            = SOME @{thm' Ant_Seq_I}
        | rule_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _))
            = SOME @{thm' HOL.conjI}
        | rule_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const (\<^const_name>\<open>HOL.True\<close>, _))
            = SOME @{thm' TrueI}
        | rule_of _ = NONE
      exception OUT_OF_IDX
      fun pass 0 _ thm = thm
        | pass N i thm =
           (case (rule_of (Logic.strip_assums_concl (Logic.nth_prem (i+1, Thm.prop_of thm)))
                       handle TERM _ => raise OUT_OF_IDX)
              of SOME rule => ( num := !num + 1 ;
                                pass (if N < 0 then N else N+1) i (rule RSN' (ctxt, i+1, thm)) )
               | NONE => thm
                      |> Conv.gconv_rule (conv ~1 ctxt) 1
                      |> pass (N-1) (i+1))
            handle OUT_OF_IDX =>
              let val thm = Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) (conv N ctxt)) thm
               in if i < Thm.nprems_of thm
               then pass N i thm
               else thm
              end
      val thm = pass N 0 thm
   in (!num, thm)
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

fun dest_ant_sequence tm =
  let fun dest ret (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ A $ B) = dest (dest ret B) A
        | dest ret (Const(\<^const_name>\<open>True\<close>, _)) = ret
        | dest ret X = X :: ret
   in dest [] tm
  end
fun dest_ant_sequence_or_HOL_conj tm =
  let fun dest ret (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ A $ B) = dest (dest ret B) A
        | dest ret (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) = dest (dest ret B) A
        | dest ret (Const(\<^const_name>\<open>True\<close>, _)) = ret
        | dest ret X = X :: ret
   in dest [] tm
  end

fun intr_ant_seq thP thQ =
  let
    val (P, Q) = apply2 (Thm.dest_arg o Thm.cprop_of) (thP, thQ)
      handle CTERM (msg, _) => raise THM (msg, 0, [thP, thQ]);
    val rule = \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<Longrightarrow> Q \<Longrightarrow> P \<and>\<^sub>\<r> Q\<close> by (rule Ant_Seq_I)\<close>
  in Drule.implies_elim_list rule [thP, thQ] end;

fun intro_ant_sequence [] = @{thm' TrueI}
  | intro_ant_sequence L = foldr1 (uncurry intr_ant_seq) L

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
  in (thP, thQ) end

fun elim_conj thPQ =
  let
    val _ = case Thm.prop_of thPQ
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) => ()
               | _ => raise THM ("elim_conj", 0, [thPQ])
    val (P, Q) = Thm.dest_binop (Thm.dest_arg (Thm.cprop_of thPQ))
      handle CTERM (msg, _) => raise THM (msg, 0, [thPQ]);
    val thP =
      Thm.implies_elim \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<and> Q \<Longrightarrow> P\<close> by (rule conjunct1)\<close> thPQ;
    val thQ =
      Thm.implies_elim \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<and> Q \<Longrightarrow> Q\<close> by (rule conjunct2)\<close> thPQ;
  in (thP, thQ) end

fun elim_ant_seq_or_HOL_conj thPQ =
  case Thm.prop_of thPQ
    of _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) => elim_conj thPQ
     | _ (*Trueprop*) $ (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _) => elim_ant_seq thPQ
     | _ => raise THM ("elim_ant_seq_or_HOL_conj", 0, [thPQ])

fun elim_ant_sequence th =
  case Thm.prop_of th
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) => []
     | _ => let fun elim th =
                  let val (th1, th2) = elim_ant_seq th
                   in elim th1 @ elim th2
                  end handle THM _ => [th]
             in elim th
            end

fun elim_ant_sequence_or_HOL_conj th =
  case Thm.prop_of th
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) => []
     | _ => let fun elim th =
                  let val (th1, th2) = elim_ant_seq_or_HOL_conj th
                   in elim th1 @ elim th2
                  end handle THM _ => [th]
             in elim th
            end

end