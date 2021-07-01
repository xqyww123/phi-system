signature NU_SYS = sig
  val apply_proc : thm (*spec*) -> thm (*proc*) -> thm (*spec*)
  val accept_proc : Proof.context -> thm -> thm
  val assign_reg : string (*name*) -> thm -> thm
  val load_reg : string (*name*) -> thm -> thm

  val process : int (* auto level *) -> Proof.state -> thm -> thm parser
    (* auto level: 2 - fully auto, 1 - paritally auto, 0 - fully manual *)
end
structure NuSys : NU_SYS = struct
open Thm NuBasics
val apply_proc_thm = @{thm NuPrim.apply_proc}
fun apply_proc spec proc =
  elim_SPEC spec |> apfst (fn focus => apply_proc_thm OF [focus, proc]) |> intro_SPEC
fun operate_reg operation reg spec =
  apply_proc spec (operation reg (registers_of_specthm spec |> term_of))
val assign_reg = operate_reg NuRegisters.assign_reg
val load_reg = operate_reg NuRegisters.load_reg

val accept_proc_thm = @{thm NuPrim.accept_proc}
fun accept_proc ctx specthm =
  specthm |> disch_current_codeblock
    |> forall_intr (current_block_var specthm |> cterm_of ctx)
    |> mk_PropBlock 0 
    |> (fn x => x RS accept_proc_thm)
    |> param_set_free_var_name ctx (current_block_var specthm |> dest_Free |> #1)
    |> undisch

fun process auto_level stat = NuProcessor.process auto_level (Proof.context_of stat)
end
