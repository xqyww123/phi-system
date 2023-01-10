signature PHI_REASONERS = sig
  exception Attemption_Fail of Proof.context * thm

  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
  val auto_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val auto_obligation_solver' : (Proof.context * thm -> Proof.context * thm) (*failure callback*)
                              -> Proof.context * thm -> Proof.context * thm
  val auto_obligation_solver1 : Proof.context * thm -> Proof.context * thm

  val safer_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val safer_obligation_solver': (Proof.context * thm -> Proof.context * thm) (*failure callback*)
                              -> Proof.context * thm -> Proof.context * thm
  val safer_obligation_solver1: Proof.context * thm -> Proof.context * thm

  val defer_obligation_tac : Proof.context -> thm -> thm Seq.seq

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Thm Term

(** Preliminary **)

exception Attemption_Fail of Proof.context * thm

fun wrap tac (ctxt,thm) = tac ctxt thm |> Seq.map (pair ctxt)

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty))) *)

fun aux_thms ctxt = Named_Theorems.get ctxt \<^named_theorems>\<open>useful\<close>

(** Tactics **)

(*** Auxiliaries ***)

(*protects the remaining goals and only attach the first one*)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude

fun raw_auto' ctxt =
  let
    val imp = Proof_Context.get_thms ctxt "\<phi>implication_GE"
  in Method.insert_tac ctxt (aux_thms ctxt) 1
     THEN (if null imp then all_tac else resolve_tac ctxt imp 1)
     THEN Clasimp.auto_tac ctxt
  end
(*the classical 'auto' method that
  attacks only the first goal and returns only if the goal is solved*)
fun raw_auto ctxt =
  head_only (raw_auto' ctxt
          #> Seq.filter (fn st' => Thm.nprems_of st' = 0 (*check the only goal is solved*)))

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

(*** Premise tac ***)

(*Attack antecedents @{term "Premise mode P"} using the classical auto tactic.
It is the default tactic in the system intended to solve simple proof obligations.*)
fun auto_obligation_solver ctxt th =
  case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
    of SOME (_, \<^const>\<open>True\<close>) => Seq.single (@{thm Premise_True} RS th)
     | SOME _ => raw_auto ctxt th
     | NONE => Seq.empty

val auto_obligation_solver' = context_tactic_to_state_transition auto_obligation_solver

fun auto_obligation_solver1 (ctxt,sequent) =
  case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ Goal) => (
        Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>auto\<close> method...",
            Syntax.pretty_term ctxt Goal
        ]);
        auto_obligation_solver' (fn _ =>
          error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt Goal
        ]))) (ctxt,sequent)
     )
     | _ => raise THM ("auto_obligation_solver1: The leading antecedent of the given sequent \
              \is not a proof obligation.", 1, [sequent])


(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
fun safer_obligation_solver ctxt th =
  case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
    of SOME (_, \<^const>\<open>True\<close>) => Seq.single (@{thm Premise_True} RS th)
     | SOME _ => HEADGOAL (Clasimp.clarsimp_tac ctxt) th
     | NONE => Seq.single th

val safer_obligation_solver' = context_tactic_to_state_transition safer_obligation_solver

fun safer_obligation_solver1 (ctxt,sequent) =
  case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ Goal) => (
        Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>clarsimp\<close> method...",
            Syntax.pretty_term ctxt Goal
        ]);
        safer_obligation_solver' (fn _ =>
          error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt Goal
        ]))) (ctxt,sequent)
     )
     | _ => raise THM ("auto_obligation_solver1: The leading antecedent of the given sequent \
              \is not a proof obligation.", 1, [sequent])

fun contract_obligations ctxt thm = let open Conv in
  gconv_rule (bottom_conv (K (try_conv (rewrs_conv
    @{thms contract_premise_true
           contract_premise_imp contract_premise_all
     }))) ctxt) 1 thm
  |> fconv_rule (rewr_conv @{thm contract_obligations})
end

fun defer_obligation_tac ctxt thm =
  let
    val idx = tl (Thm.prems_of thm) |> find_index (fn tm =>
          case tm of (_ $ (@{term Proof_Obligation} $ _)) => true
                   | _ => false)
    val n = Thm.nprems_of thm
  in
    if idx = ~1
    then error ("Fail to defer a proof obligation: an \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n antecedent is not found.")
    else Thm.permute_prems 1 idx thm
      |> contract_obligations ctxt
      |> Thm.permute_prems 0 (~idx)
      |> (fn thm' => if Thm.nprems_of thm' = n - 1 then thm'
                     else raise Fail "BUG!!!")
      |> Seq.single
  end

end
