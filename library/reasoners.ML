signature NU_REASONERS = sig
  val premise_collect_tac : Proof.context -> thm -> thm Seq.seq
  val premise_tac : Proof.context -> thm -> thm Seq.seq
  val asm_simp_tac : Proof.context -> thm -> thm Seq.seq
  val single_return : tactic -> tactic
end

structure Nu_Reasoners : NU_REASONERS = struct
open Thm NuBasics Term

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty)))

fun aux_thms ctxt = Proof_Context.get_thms ctxt "\<nu>current"
                  @ Named_Theorems.get ctxt "NuSys.useful"
                  @ Proof_Context.get_thms ctxt "\<nu>lemmata"
                  @ Proof_Context.get_thms ctxt "\<nu>local_values"

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
    Method.insert_tac ctxt (aux_thms ctxt) 1
    THEN prep_prems ctxt
    THEN Clasimp.auto_tac ctxt
 (* THEN print_dbg "22222"  *)


(*** Premise tac ***)
fun premise_collect_tac ctxt th =
  if Config.get ctxt Nu_Reasoner.auto_level >= 2 andalso
     can (major_prem_of #> dest_Trueprop #> dest_premise_tag) th
  then head_only (HEADGOAL (SOLVED' (K (raw_auto ctxt)))) th
  else Seq.empty

fun contract_premcollect ctxt = let open Conv in
  gconv_rule (bottom_conv (K (try_conv (rewrs_conv
    @{thms contract_premise_true
           contract_premise_imp contract_premise_all
     }))) ctxt) 1
  #> fconv_rule (rewr_conv @{thm contract_premcollect})
end

fun premise_tac ctxt thm =
  let
    val idx = Thm.prems_of thm |> find_index (fn tm =>
          case tm of (_ $ (@{term Premise_Collect} $ _)) => true
                   | _ => false)
    val n = Thm.nprems_of thm
  in
    if idx = ~1 then premise_collect_tac ctxt thm
    else Thm.permute_prems 1 (idx-1) thm
      |> contract_premcollect ctxt
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
