signature PHI_REASONERS = sig

  exception Automation_Fail of (Proof.context * thm) option
  val error_message : (Proof.context * thm) option -> string

  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
  val auto_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val auto_obligation_solver_opt :  Proof.context * thm -> (Proof.context * thm) option
  val auto_obligation_solver' : (Proof.context * thm -> Proof.context * thm) (*failure callback*)
                              -> Proof.context * thm -> Proof.context * thm
  val auto_obligation_solver1 : Proof.context * thm -> Proof.context * thm

  val safer_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val safer_obligation_solver': (Proof.context * thm -> Proof.context * thm) (*failure callback*)
                              -> Proof.context * thm -> Proof.context * thm
  val safer_obligation_solver1: Proof.context * thm -> Proof.context * thm

  (*defer the leading antecedent to the nearest obligation and call the contract*)
  val defer_antecedent : (Proof.context -> thm -> thm) (*contract*)
                                 -> Proof.context -> thm -> thm Seq.seq
  val defer_obligation_tac : Proof.context -> thm -> thm Seq.seq

  structure Tactic_Configures : HOOKS

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Thm Term

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
fun context_tactic_to_state_transition tac fail (ctxt, sequent) =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => (ctxt, th')
     | NONE => fail (ctxt, sequent)

fun context_tactic_to_state_transition_opt tac (ctxt, sequent) =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => SOME (ctxt, th')
     | NONE => NONE

(*** Premise tac ***)

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
val auto_obligation_solver_opt = context_tactic_to_state_transition_opt auto_obligation_solver

fun auto_obligation_solver1 (ctxt,sequent) =  (
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
        ) (ctxt,sequent)
     )


(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
fun safer_obligation_solver ctxt th =
  case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
    of SOME (_, \<^const>\<open>True\<close>) => Seq.single (@{thm Premise_True} RS th)
     | SOME _ => apply ctxt (fn (ctxt,pre,aux,_) =>
                    pre THEN HEADGOAL (Clasimp.clarsimp_tac (ctxt addsimps aux))) Safe_Solver th
     | NONE => Seq.single th

val safer_obligation_solver' = context_tactic_to_state_transition safer_obligation_solver
val safer_obligation_solver_opt = context_tactic_to_state_transition_opt safer_obligation_solver

fun safer_obligation_solver1 (ctxt,sequent) =
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
        ]))) (ctxt addsimps @{thms Premise_def},sequent)
     )
     | _ => raise THM ("auto_obligation_solver1: The leading antecedent of the given sequent \
              \is not a proof obligation.", 1, [sequent])

fun obligation_conv ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
          Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _)
          $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>default\<close>, _) $ _))
          $ _
         => (Conv.arg_conv obligation_conv then_conv
             Conv.rewr_conv @{thm contract_premise_imp}) ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _
         => (Conv.arg_conv obligation_conv then_conv
             Conv.rewr_conv @{thm conjunction_imp[symmetric]}) ctm
     | _ => raise CTERM ("unexpected proof obligation form", [ctm])

fun obligation_conv_all ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
        (Phi_Helper_Conv.meta_all_conv (obligation_conv_all o snd) ctxt then_conv
          Conv.rewr_conv @{thm contract_premise_all}) ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
          Conv.all_conv ctm
     | _ => raise CTERM ("internal bug 6733574a-42dc-4592-a08e-ddc223bb6b94", [ctm])

fun contract_obligations ctxt thm = let open Conv
  val rule1 = gconv_rule (Phi_Helper_Conv.exhaustive_meta_all_conv (K (
                obligation_conv then_conv Conv.rewr_conv @{thm Pure.prop_def[symmetric]})) ctxt
              ) 1 thm
(*val _ $ (_ $ (_ $ X) $ _) = Thm.major_prem_of rule1
  val _ = case X
            of Const(\<^const_name>\<open>True\<close>, _) => ()
             | _ => warning "!!!" *)
  val rule2 = (@{thm contract_drop_waste} RS rule1)
            |> gconv_rule (obligation_conv_all ctxt) 1
            |> fconv_rule (rewr_conv @{thm contract_obligations})
   in rule2
  end

fun defer_antecedent contract ctxt thm =
  let
    val idx = tl (Thm.prems_of thm) |> find_index (fn tm =>
          case tm of (_ $ (@{term Proof_Obligation} $ _)) => true
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


(*fun declare_local_assume_reasoners sequent i *)

end
