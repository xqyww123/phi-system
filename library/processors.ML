signature NU_PROCESSORS = sig
  type proc = NuProcessor.proc
  val simplifier : thm list (*simp cong*) -> proc
  val focus_rule : proc -> proc
  val premise_prover : (Proof.context -> tactic) -> proc
  val all_premises_prover : (Proof.context -> tactic) -> proc

  val setup_resolver : binding -> int (*precedence*)
        -> (string * (binding * string option * mixfix) list) (* pattern *)
        -> (xstring * Position.T) (*name of facts*) -> string (*comment*)
        -> local_theory -> local_theory
  (* it loads all aux facts and codeblocks in the spec thm *)
  (* val open_spec : proc -> proc *)
end
structure NuProcessors : NU_PROCESSORS = struct
open NuBasics NuHelp NuProcessor
fun simplifier cong = almost_safe (fn ctx => fn meta =>
  Scan.succeed (fn _ => let
    val ctx' = NuSys.load_specthm meta ctx
                |> fold Simplifier.add_cong (@{thm NuPrim.SpecTop_cong_major}::cong)
    val (major,aux) = elim_SPEC meta
    in Simplifier.full_simplify ctx' major
        |> (fn th2 => if Thm.eq_thm_prop (major, th2) then raise Bypass else th2)
        |> rpair aux |> intro_SPEC
    end))
fun focus_rule processor ctx th toks = 
  case elim_SPEC th of (focus,aux) =>
    processor ctx focus toks |> apfst (fn th => fn _ => intro_SPEC (th (),aux))
fun premise_prover_raw n prover ctx th =
  Scan.succeed (fn _ => 
    (if n = ~1 then th RS Drule.protectI else Goal.protect n th)
      |> prover ctx |> Seq.pull |> (fn x =>
          case x of SOME (th,_) => Goal.conclude th | _ => raise Bypass))
val premise_prover = focus_rule o premise_prover_raw 1
val all_premises_prover = focus_rule o premise_prover_raw ~1

fun setup_resolver binding precedence pattern facts comment lthy =
  let
    val facts = Facts.check (Context.Proof lthy) (Proof_Context.facts_of lthy) facts
  in
    setup' binding precedence pattern (
      premise_prover (almost_safe (fn ctx =>
        Tactical.SOLVED' (Tactical.REPEAT o Tactic.resolve_tac ctx
          (Proof_Context.get_thms ctx facts)) 1))
    ) comment lthy
  end
end
