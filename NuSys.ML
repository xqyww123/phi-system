signature NU_SYS = sig
  val apply_proc : thm (*spec*) -> thm (*proc*) -> thm (*spec*)
  val accept_proc : Proof.context -> thm -> thm
  val assign_reg : string (*name*) -> thm -> thm

  val process : Proof.state -> int (* auto level *) -> thm -> thm
    (* auto level: 0 - fully auto, 1 - paritally auto, 2 - fully manual *)
end
structure NuSys : NU_SYS = struct
open Thm NuBasics
val apply_proc_thm = @{thm NuPrim.apply_proc}
fun apply_proc spec proc =
  elim_SPEC spec |> apfst (fn focus => apply_proc_thm OF [focus, proc]) |> intro_SPEC
fun assign_reg reg spec =
  apply_proc spec (NuRegisters.assign_reg reg (registers_of_specthm spec |> term_of))

val accept_proc_thm = @{thm NuPrim.accept_proc}
fun accept_proc ctx specthm =
  specthm |> disch_current_codeblock
    |> forall_intr (current_block_var specthm |> cterm_of ctx)
    |> mk_PropBlock 0 
    |> (fn x => x RS accept_proc_thm)
    |> param_set_free_var_name ctx (current_block_var specthm |> dest_Free |> #1)
    |> undisch

fun process stat auto_level = NuProcessor.process auto_level (Proof.context_of stat |> Context.Proof)
end
