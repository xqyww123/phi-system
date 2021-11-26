signature NU_REASONERS = sig
  val premise_tac : Proof.context -> thm -> thm Seq.seq
end

structure Nu_Reasoners : NU_REASONERS = struct
open Thm NuBasics Term

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty)))

(** Tactics **)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude
fun raw_auto ctx =
  ((Method.insert_tac ctx (Named_Theorems.get ctx "NuSys.used") 1)
    THEN Method.insert_tac ctx (Proof_Context.get_thms ctx "\<nu>current"
                                  |> map (fn th => th RS @{thm CurrentConstruction_D})) 1
    THEN Method.insert_tac ctx (Proof_Context.get_thms ctx "\<glowing_star>") 1
    THEN print_dbg
    THEN Clasimp.auto_tac ctx
    )

(*** Premise tac ***)
val Premise_I = @{thm NuPrime.Premise_I}
fun mk_premise_tac withdraw ctx th =
  if AutoLevel.get ctx >= 2 andalso can (major_prem_of #> dest_Trueprop #> dest_premise_tag) th
  then (head_only (SOLVED' (K (HEADGOAL (resolve0_tac [Premise_I]) THEN raw_auto
  ctx THEN print_dbg)) 1)
      ORELSE withdraw) th
  else Seq.empty
val FailedPremise_I = @{thm FailedPremise_I} and FailedPremise_D = @{thm FailedPremise_D}
val withdrawable_premise_tac = mk_premise_tac (Seq.succeed o undisch o (fn x => FailedPremise_D RS x))
val dest_failed_premise_tag = dest_Trueprop #> dest_monop @{const_name "FailedPremise"}
val premise_tac = mk_premise_tac Seq.fail
fun fininsh_premise_hyps th =
  fold ((fn x => FailedPremise_I RS x) oo implies_intr)
    (chyps_of th |> filter (can (dest_failed_premise_tag o term_of))) th


end
