signature NU_REASONERS = sig
  val naive_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val premise_tac : Proof.context -> thm -> thm Seq.seq
  val asm_simp_tac : Proof.context -> thm -> thm Seq.seq
  val single_return : tactic -> tactic
  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
end

structure Nu_Reasoners : NU_REASONERS = struct
open Thm NuBasics Term

fun wrap tac (ctxt,thm) = tac ctxt thm |> Seq.map (pair ctxt)

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty)))

fun get_thms ctxt name =
  case Proof_Context.lookup_fact ctxt name of SOME {thms,...} => thms
                                            | NONE => []

fun aux_thms ctxt = Named_Theorems.get ctxt \<^named_theorems>\<open>useful\<close>
                  @ Named_Theorems.get ctxt \<^named_theorems>\<open>\<phi>lemmata\<close>

(** Tactics **)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude

(* TODO: 
*   Because the `auto` tactic tackles those schematic variables badly,
*   in this tactic, we split the conjection into multiple sub-goals,
*   and for each sub-goal, we use HOL.refl to instantiate schematic variabls
*   like ?Y in equities like "X a b = ?Y a b".
*   However, this strategy is rather naive, and it considers equities one by one.
*   A more idea strategy should guess those schematic variables as a whole,
*   and consider situations more than equities. *)
fun prep_prems ctxt =
  REPEAT_DETERM (SOMEGOAL (resolve_tac ctxt @{thms Premise_I conjI HOL.refl}))
    (* THEN print_dbg "222221111"  *)

fun raw_auto ctxt =
    Method.insert_tac ctxt (aux_thms ctxt |> @{print}) 1
    THEN resolve_tac ctxt (Proof_Context.get_thms ctxt "\<phi>implication") 1
THEN print_dbg "22222"
    THEN Clasimp.auto_tac ctxt
 (* THEN print_dbg "22222"  *)


(*** Premise tac ***)
fun naive_obligation_solver ctxt th =
  if Config.get ctxt Nu_Reasoner.auto_level >= 2 andalso
     can (major_prem_of #> HOLogic.dest_Trueprop #> dest_premise_tag) th
  then head_only (HEADGOAL (SOLVED' (K (raw_auto ctxt)))) th
  else Seq.empty

fun contract_obligations ctxt = let open Conv in
  gconv_rule (bottom_conv (K (try_conv (rewrs_conv
    @{thms contract_premise_true
           contract_premise_imp contract_premise_all
     }))) ctxt) 1
  #> fconv_rule (rewr_conv @{thm contract_obligations})
end

fun premise_tac ctxt thm =
  let
    val idx = Thm.prems_of thm |> find_index (fn tm =>
          case tm of (_ $ (@{term Proof_Obligation} $ _)) => true
                   | _ => false)
    val n = Thm.nprems_of thm
  in
    if idx = ~1
    then Seq.empty
    else Thm.permute_prems 1 (idx-1) thm
      |> contract_obligations ctxt
      |> Thm.permute_prems 0 (~(idx-1))
      |> (fn thm' => if Thm.nprems_of thm' = n - 1 then thm'
                     else raise Fail "BUG!!!")
      |> Seq.single
  end


fun asm_simp_tac ctxt =
  REPEAT (HEADGOAL (resolve_tac ctxt @{thms Premise_I})) THEN
  HEADGOAL (SOLVED' (Simplifier.asm_simp_tac (ctxt addsimps aux_thms ctxt)))
  

fun single_return tac s =
  Seq.make (fn () => 
    case Seq.chop 2 (tac s)
      of ([s'], _) => SOME (s', Seq.empty)
       | _ => NONE
  )


end
