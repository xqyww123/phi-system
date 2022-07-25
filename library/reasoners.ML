signature NU_REASONERS = sig
  val naive_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val naive_obligation_solver' : Proof.context * thm -> Proof.context * thm
  val premise_tac : Proof.context -> thm -> thm Seq.seq
  val asm_simp_tac : Proof.context -> thm -> thm Seq.seq
  val single_return : tactic -> tactic
  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
end

structure Nu_Reasoners : NU_REASONERS = struct
open Thm Term

fun wrap tac (ctxt,thm) = tac ctxt thm |> Seq.map (pair ctxt)

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty)))

fun aux_thms ctxt = Named_Theorems.get ctxt \<^named_theorems>\<open>useful\<close>
                  @ Named_Theorems.get ctxt \<^named_theorems>\<open>\<phi>lemmata\<close>

(** Tactics **)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude

fun raw_auto ctxt =
  let
    val imp = Proof_Context.get_thms ctxt "\<phi>implication"
  in Method.insert_tac ctxt (aux_thms ctxt |> @{print}) 1
     THEN (if null imp then all_tac else resolve_tac ctxt imp 1)
     THEN Clasimp.auto_tac ctxt
  end


(*** Premise tac ***)
fun naive_obligation_solver ctxt th =
  case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
    of SOME (_, \<^const>\<open>True\<close>) => Seq.single (@{thm Premise_True} RS th)
     | SOME _ => head_only (HEADGOAL (SOLVED' (K (raw_auto ctxt)))) th
     | NONE => Seq.empty

fun naive_obligation_solver' (ctxt,th) =
 (case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
    of SOME (_, \<^const>\<open>True\<close>) => @{thm Premise_True} RS th
     | SOME (_, goal) =>
          (case Seq.pull (head_only (HEADGOAL (SOLVED' (K (raw_auto ctxt)))) th)
             of SOME (th',_) => th'
              | NONE => error ("fail to prove automatically the\n"^Syntax.string_of_term ctxt goal))
     | NONE => th)
   |> pair ctxt

fun contract_obligations ctxt thm = let open Conv in
  gconv_rule (bottom_conv (K (try_conv (rewrs_conv
    @{thms contract_premise_true
           contract_premise_imp contract_premise_all
     }))) ctxt) 1 thm
  |> fconv_rule (rewr_conv @{thm contract_obligations})
end

fun premise_tac ctxt thm =
  let
    val idx = tl (Thm.prems_of thm) |> find_index (fn tm =>
          case tm of (_ $ (@{term Proof_Obligation} $ _)) => true
                   | _ => false)
    val n = Thm.nprems_of thm
  in
    if idx = ~1
    then Seq.empty
    else Thm.permute_prems 1 idx thm
      |> contract_obligations ctxt
      |> Thm.permute_prems 0 (~idx)
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
