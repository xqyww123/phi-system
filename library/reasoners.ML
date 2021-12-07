signature NU_REASONERS = sig
  val premise_tac : Proof.context -> thm -> thm Seq.seq
end

structure Nu_Reasoners : NU_REASONERS = struct
open Thm NuBasics Term

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty)))

(** Tactics **)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude
fun raw_auto ctx =
    Method.insert_tac ctx (Proof_Context.get_thms ctx "\<nu>current"
                         @ Named_Theorems.get ctx "NuSys.useful"
                         @ Proof_Context.get_thms ctx "\<nu>lemmata"
                         @ Proof_Context.get_thms ctx "\<nu>local_values"
                          ) 1
    THEN Clasimp.auto_tac ctx

(*** Premise tac ***)
fun premise_tac ctx th =
  if AutoLevel.get ctx >= 2 andalso
     can (major_prem_of #> dest_Trueprop #> dest_premise_tag) th
  then head_only (HEADGOAL (SOLVED' (K (raw_auto ctx THEN print_dbg "2222")))) th
  else Seq.empty


end
