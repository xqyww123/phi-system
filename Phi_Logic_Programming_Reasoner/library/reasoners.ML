signature PHI_REASONERS = sig

  include PHI_REASONERS

  exception Automation_Fail of (Proof.context * thm) option
  val error_message : (Proof.context * thm) option -> string

  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
  val wrap': (Proof.context -> thm -> thm option) -> (context_state -> context_state option)
  val wrap'': (Proof.context -> thm -> thm) -> (context_state -> context_state)

  val auto_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val auto_obligation_solver' : (Proof.context -> thm -> thm) (*failure callback*)
                              -> Proof.context -> thm -> thm
  val auto_obligation_solver1 : Proof.context -> thm -> thm

  val safer_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val safer_obligation_solver': (Proof.context -> thm -> thm) (*failure callback*)
                              -> Proof.context -> thm -> thm
  val safer_obligation_solver1: Proof.context -> thm -> thm

  (*defer the leading antecedent to the nearest obligation and call the contract*)
  val defer_antecedent : (Proof.context -> thm -> thm) (*contract*)
                                 -> Proof.context -> thm -> thm Seq.seq
  val defer_obligation_tac : Proof.context -> thm -> thm Seq.seq

  structure Tactic_Configures : HOOKS (*You can alter auxiliary facts, tactics, and configure the
      context before applying either the automatic solving*)

  structure Is_Premise_of_Obligation : HANDLERS
      (*Tell me what antecedents are considered premise of a proof obligation to be reported,
        and what are not so that to be ignored.*)
  val is_premise_of_obligation : Context.generic -> term -> bool

  structure Local_Premises_of_Obligation : NAMED_THMS
      (*You can add any facts to be reported as premises of a proof obligation*)

end


structure Phi_Reasoners : PHI_REASONERS = struct
open Thm Term Phi_Reasoners

(** Preliminary **)

exception Automation_Fail of (Proof.context * thm) option

fun error_message err =
      Pretty.string_of (Pretty.chunks (
        Pretty.str "Fail to solve the proof obligation automatically" ::
        (case err of SOME (ctxt, sequent) =>
            (case Thm.prems_of sequent
               of (x::_)
                    => [Syntax.pretty_term ctxt x]
                | _ => [])
                   | NONE => [])
      ))



fun wrap tac (ctxt,thm) = tac ctxt thm |> Seq.map (pair ctxt)
fun wrap' tac (ctxt,thm) = tac ctxt thm |> Option.map (pair ctxt)
fun wrap'' tac (ctxt,thm) = tac ctxt thm |> pair ctxt

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty))) *)

val aux_thms = Useful_Thms.get

(** Tactic Configures **)

datatype solver_mode = Agressive_Solver (*the auto method*) | Safe_Solver (*by clarsimp*)

structure Tactic_Configures = Hooks (
  type arg = solver_mode
  type state = thm list (*aux thms*) * tactic * Proof.context
)

fun apply ctxt tactic  mode =
  HEADGOAL (SOLVED' (K
    (#2 (Tactic_Configures.invoke_until_success (Context.Proof ctxt)
          (fn mode => fn (aux,tac,ctxt) =>
              ([], tactic (ctxt,tac,aux,mode), ctxt)) mode (aux_thms ctxt, all_tac, ctxt)))))

(* tac THEN HEADGOAL (Method.insert_tac ctxt aux)
                       THEN tactic ctxt *)

(*
fun apply' protect_head ctxt tactic =
  let val prep = if protect_head
                 then *)

(** Tactics **)

(*** Auxiliaries ***)

(*protects the remaining goals and only attack the first one*)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude

(*Wrap a context tactic of type `Proof.context -> thm -> thm Seq.seq` to the
  transition between states, of type `Proof.context * thm -> Proof.context * thm`.
  *This wrap only adopts the first result of applying the tactic, and drops other alternatives.*
  The original seq-based tactics are not affected by this.

  Because reasoners in the file only attack the first antecedent and solves it totally or fails,
  this short-cut makes differences only when the antecedent to be solved has some schematic variables
  to be instantiated during the tactic application.

  The semantics of schematic variables in auto_obligation_solver and safer_obligation_solver is,
  any possible instantiation is acceptable.

  If the schematic variables are not able to be chosen arbitrarily, additional mechanisms have
  to be applied previously.*)
fun context_tactic_to_state_transition tac fail ctxt sequent =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => th'
     | NONE => fail ctxt sequent

(*fun context_tactic_to_state_transition_opt tac (ctxt, sequent) =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => SOME (ctxt, th')
     | NONE => NONE *)

(*** Defer ***)

structure Is_Premise_of_Obligation = Handlers ( type arg = term; type ret = bool )
structure Local_Premises_of_Obligation = Named_Thms (
  val name = \<^binding>\<open>__local_premise_of_obligation__\<close>
  val description = "Facts inside will be added as premises into proof obligations"
)

fun is_premise_of_obligation ctxt =
  let val ivk = Is_Premise_of_Obligation.invoke ctxt
   in fn tm => case ivk tm
    of SOME ret => ret
     | NONE => (case tm of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>default\<close>, _) $ _) => true
                         | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_SIMP\<close>, _) $ _) => true
                         | _ => false)
  end

fun obligation_collect filter ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
    case Thm.term_of ctm
      of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
            Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
       | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ Pr $ _
           => if filter Pr
              then (Conv.arg_conv (obligation_collect filter) then_conv
                    Conv.rewr_conv (case Pr
                                      of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =>
                                              @{thm' contract_premise_imp}
                                       | _ => @{thm' contract_premise_imp_general})) ctm
              else (Conv.arg_conv (obligation_collect filter) then_conv
                    Conv.rewr_conv @{thm' conjunction_imp[symmetric]}) ctm
       | _ => raise CTERM ("unexpected proof obligation form", [ctm])
  ) ctm

fun obligation_conv_all ctxt ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
        (Phi_Conv.meta_all_conv (obligation_conv_all o snd) ctxt then_conv
          Conv.rewr_conv @{thm contract_premise_all}) ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
          Conv.all_conv ctm
     | _ => raise CTERM ("internal bug 6733574a-42dc-4592-a08e-ddc223bb6b94", [ctm])
  ) ctm

fun obligation_intro_Ex_conv ctxt thm =
  Phi_Help.lambda_normalization_rule (fn thm =>
    let fun dest' (\<^Const>\<open>Pure.imp\<close> $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (
                        Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ P)) $ Q) = (P,Q)
          | dest' tm = raise TERM ("obligation_intro_Ex", [tm])
        fun dest ctm = dest' (Thm.term_of ctm)
        fun dest_c ctm =
              (dest ctm; (Thm.dest_arg (Thm.dest_arg1 ctm), Thm.dest_arg ctm))
  
        val (P,Q) = dest (Thm.cprop_of thm)
        val vars = Term.add_vars Q []
        fun collect_var ret (Var v) = if member (op =) vars v then ret
                                      else insert (op =) v ret
          | collect_var ret (A $ B) = collect_var (collect_var ret A) B
          | collect_var ret (Abs(_,_,X)) = collect_var ret X
          | collect_var ret _ = ret
        val vars' = collect_var [] P
                  |> map (fn (N,T) => Thm.var (N, Thm.ctyp_of ctxt T))
        val mode = Config.get ctxt existential_obligation = 2
        val contract_Ex_rule = if mode then @{thm' contract_intro_sp_Ex}
                                       else @{thm' contract_intro_Ex}
        val mv_Ex_All = if mode then Phi_Conv.move_sp_Ex_inside_All_exhausitive
                                else Phi_Conv.move_Ex_inside_All_exhausitive
        val mv_Ex_Disj = if mode then Phi_Conv.move_sp_Ex_downto_Disj_exhaustive
                                 else Phi_Conv.move_Ex_downto_Disj_exhaustive
        fun intro_Ex v thm =
              Conv.fconv_rule (
                  Conv.rewr_conv contract_Ex_rule then_conv
                  Phi_Conv.leading_antecedent_conv (
                    PLPR_Syntax.premise_tag_conv (mv_Ex_All (fn _ =>
                      mv_Ex_Disj Conv.all_conv
                    ) ctxt)
                  )
              ) (Thm.forall_intr v thm)
     in fold intro_Ex vars' thm
    end
  ) thm

fun collect_obligation_premises ctxt thm = let open Conv
  val filter = is_premise_of_obligation (Context.Proof ctxt)
  val rule1 = gconv_rule (Phi_Conv.meta_alls_conv (K (
                obligation_collect filter then_conv
                rewr_conv @{thm Pure.prop_def[symmetric]})) ctxt
              ) 1 thm
  val rule2 = case Local_Premises_of_Obligation.get ctxt
                of [] => rule1
                 | L => let val fact = map (Conv.fconv_rule (Object_Logic.atomize ctxt)) L
                                    |> foldl1 (uncurry (HOLogic.conj_intr ctxt))
                         in fact RS (@{thm' contract_add_additional_prems} RS rule1)
                        end
   in (@{thm contract_drop_waste} RS rule1)
   |> gconv_rule (obligation_conv_all ctxt) 1
   |> Config.get ctxt existential_obligation > 0 ? obligation_intro_Ex_conv ctxt
  end

fun contract_obligations ctxt thm =
  collect_obligation_premises ctxt thm
    |> Conv.fconv_rule (Conv.rewr_conv @{thm contract_obligations})

fun defer_antecedent contract ctxt thm =
  let
    val idx = tl (Thm.prems_of thm) |> find_index (fn tm =>
          case tm of (_ $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _)) => true
                   | _ => false)
  in
    if idx = ~1
    then error ("Fail to defer a proof obligation: an \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> antecedent is not found.")
    else Thm.permute_prems 1 idx thm
      |> contract ctxt
      |> Thm.permute_prems 0 (~idx)
      |> Seq.single
  end

val defer_obligation_tac = defer_antecedent contract_obligations

(*** Premise tac ***)

fun intro_all_leading_ex i thm =
  if i > Thm.nprems_of thm
  then thm
  else case Logic.concl_of_goal (Thm.prop_of thm) i
         of _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
              intro_all_leading_ex i (@{thm' conjI} RSN (i, thm))
          | _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ _ ) =>
              intro_all_leading_ex i (@{thm' exI} RSN (i, thm))
          | _ => intro_all_leading_ex (i+1) thm

(*Attack antecedents @{term "Premise mode P"} using the classical auto tactic.
It is the default tactic in the system intended to solve simple proof obligations.*)
fun auto_obligation_solver ctxt th =
  case major_prem_of th
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
          Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ Const (\<^const_name>\<open>True\<close>, _)) =>
            Seq.single (@{thm Premise_True} RS th)
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const (\<^const_name>\<open>True\<close>, _) =>
          Seq.single (@{thm TrueI} RS th)
     | _ => head_only (apply ctxt (fn (ctxt,pre,aux,_) =>
                pre THEN HEADGOAL (Method.insert_tac ctxt aux)
                    THEN Clasimp.auto_tac ctxt) Agressive_Solver) th

val auto_obligation_solver' = context_tactic_to_state_transition auto_obligation_solver

fun auto_obligation_solver1 ctxt sequent =  (
        Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>auto\<close> method...",
            Syntax.pretty_term ctxt (Thm.major_prem_of sequent),
            Pretty.block (Pretty.here \<^here>)
        ]);
        auto_obligation_solver' (fn _ =>
          raise Automation_Fail (SOME (ctxt,sequent))
          (*error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt Goal
            ])) *)
        ) ctxt sequent
     )


(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
fun safer_obligation_solver ctxt th0 =
  let val th = collect_obligation_premises ctxt th0
   in case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
        of SOME (_, \<^const>\<open>True\<close>) => Seq.single (@{thm Premise_True} RS th)
         | SOME _ => apply ctxt (fn (ctxt,pre,aux,_) =>
                        pre THEN HEADGOAL (fn s => fn x => Clasimp.clarsimp_tac (ctxt addsimps aux) s x)) Safe_Solver th
         | NONE => Seq.single th
  end

val safer_obligation_solver' = context_tactic_to_state_transition safer_obligation_solver

fun safer_obligation_solver1 ctxt sequent =
  case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ Goal) => (
        Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>clarsimp\<close> method...",
            Syntax.pretty_term ctxt Goal,
            Pretty.block (Pretty.here \<^here>)
        ]);
        safer_obligation_solver' (fn _ =>
          error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt Goal
        ]))) (ctxt addsimps @{thms Premise_def}) sequent
     )
     | _ => raise THM ("auto_obligation_solver1: The leading antecedent of the given sequent \
              \is not a proof obligation.", 1, [sequent])



(*fun declare_local_assume_reasoners sequent i *)

end
