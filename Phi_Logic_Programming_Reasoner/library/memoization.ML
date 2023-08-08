signature PHI_REASONERS = sig
include PHI_REASONERS

(*solve the leading antecedent with memoizing the reasoning.
  The leading antecedent cannot contain schematic variables.
  Else, return NONE.*)
val memoize_safe : context_state -> context_state option
val memoize : context_state -> context_state

(*Internal*)
val tagged_memoize : context_state -> context_state option

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

fun gen_memoize_safe f (ctxt, sequent) =
  let val goal = fst (Thm.dest_implies (Thm.cprop_of sequent))
   in if Thm.maxidx_of_cterm goal <> ~1
   then NONE
   else case Phi_Reasoner.reason NONE false ctxt (Goal.init goal)
     of SOME ret' =>
          let val ret = Goal.conclude ret'
              val save = ret
                      |> Thm.forall_intr_vars
                      |> f
              val num = Thm.nprems_of save
              fun tac (ctxt,sequent) = Seq.make (fn () =>
                  let val sequent' = (save RS' (ctxt, sequent))
                                  |> REPEAT_DETERM_N num (Thm.assumption (SOME ctxt) 1)
                   in Seq.pull sequent'
                   |> Option.map (fn (sequent'', _) => ((ctxt,sequent''), Seq.empty))
                  end
                )
                
           in SOME (Context.proof_map (
                      Phi_Reasoner.add {name = Free("Memoized", \<^typ>\<open>prop \<Rightarrow> prop\<close>) $ Thm.prop_of save,
                                        pos = \<^here>,
                                        mode = Phi_Reasoner.NORMAL_LOCAL_CUT,
                                        pattern = [(Thm.concl_of save, 100000)],
                                        blacklist = [],
                                        tactic = Phi_Reasoner.Tac_ML tac}
                      ) ctxt,
                    Thm.implies_elim sequent ret)
          end
      | NONE => NONE
  end


fun tagged_memoize (ctxt, sequent) =
  let val sequent' = @{thm' Memoize_I} RS sequent
   in gen_memoize_safe (fn th => @{thm' Memoize_D} RS th) (ctxt, sequent')
  end

val memoize_safe = gen_memoize_safe I
fun memoize stat =
  case memoize_safe stat
    of SOME ret => ret
     | NONE => error (let open Pretty in string_of (chunks
          [para "The leading antecedent cannot contain schematic variables for memoization",
           Thm.pretty_thm (fst stat) (snd stat)])
        end)

end