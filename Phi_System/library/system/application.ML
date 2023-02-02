(* FILE: library/system/application.ML
   AUTHOR: Qiyuan Xu

   The module contains reasoning infrastructure for applying application rules.
   An application rule can be a specification theorem for a procedure, a rule of view shift
   or transformation of abstraction, or any arbitrary things whose application methods are
   registered to the \<phi>-LPR reasoner.

   I changed the semantics of application recently: the application now returns
   once the first successful application is found, instead of traversing all possible
   applications and checking there is only one feasible application.
*)

signature NU_APPLICATION = sig

  val apply_proc_naive : thm (*proc*) -> context_state -> context_state

(*Depending on application rules, most of the resulted sequent (except resolution) has
an additional obligation antecedent at the last of the antecedent list,
storing proof obligations generated during ToSA, no matter whether the obligations are trivial.*)
  val try_apply : thm list (*applied rules*) -> context_state (*sequent*) -> context_state option
  val apply : thm list (*applied rules*) -> context_state (*sequent*) -> context_state

(*
  (*Advanced Modus Pones using logic programming about antecedent \<^term>\<open>\<phi>Application_Conv\<close>
    where the inferences relate to various conversions of applied rules.
   *)
  val MPs : Proof.context -> thm list -> thm -> thm
  val MP  : Proof.context -> thm -> thm -> thm *)

end

structure NuApply : NU_APPLICATION = struct
open Phi_Help

val expand_appliant = 
  repeat (fn th => th RS @{thm spec}) #>
  repeat (fn th => th RS @{thm mp}) #>
  repeat (fn th => th RS @{thm spec})

fun apply_proc_naive proc (ctxt,sequent) =
  (ctxt, expand_appliant proc RS (sequent RS @{thm \<phi>apply_proc}))

fun mk_app_reasoning_normal app sequent =
  let val idx = Thm.maxidx_of sequent + 1
      val app = Thm.incr_indexes idx app
      val idx = Thm.maxidx_of app + 1
      val rule = @{thm \<phi>application}
              |> Thm.incr_indexes idx
              |> Thm.instantiate (TVars.empty,
                                  Vars.make [((("Apps",idx),propT),  Thm.cprop_of app),
                                             ((("State",idx),propT), Thm.cprop_of sequent)])
  in Thm.implies_elim (Thm.implies_elim rule app) sequent
  end

fun mk_app_reasoning_RS app sequent =
  (app RS @{thm \<phi>Application_Conv})
    |> Thm.permute_prems 0 (Thm.nprems_of app)
    |> (fn th => th RS sequent)

fun mk_app_reasoning sequent app =
  case Thm.prop_of sequent
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
            mk_app_reasoning_RS app sequent
     | _ => mk_app_reasoning_normal app sequent

fun try_apply [] _ = NONE
  | try_apply apps (ctxt,sequent) = (
      Phi_Reasoner.debug_info ctxt (fn _ =>
            "Reasoning generic applications..." ^ Position.here \<^here>);
      PLPR_Optimum_Solution.best_among (ctxt, map (mk_app_reasoning sequent) apps))

fun apply applications stat =
  case try_apply applications stat
    of SOME stat' => stat'
     | NONE => raise THM ("Application Fail", 0, (snd stat)::applications)


(*
fun comp_no_flatten_matched (th, n) i rule =
  (case distinct Thm.eq_thm (Seq.list_of
      (Thm.bicompose NONE {flatten = false, match = true, incremented = true}
        (false, th, n) i rule)) of
    [th'] => Thm.solve_constraints th'
  | [] => raise THM ("comp_no_flatten", i, [th, rule])
  | _ => raise THM ("comp_no_flatten: unique result expected", i, [th, rule]));

fun MPs ctxt th1s' th2 =
  let
    val th1s = map (Drule.incr_indexes th2) th1s'
    val stats = map (fn th1 =>
          Thm.instantiate (TVars.empty, Vars.make [
              ((("P",0), \<^typ>\<open>prop\<close>), Thm.cprop_of th1),
              ((("Q",0), \<^typ>\<open>prop\<close>), Thm.cprem_of th2 1)
          ]) @{thm \<phi>Application_Conv}
     |> (fn th => comp_no_flatten_matched (Thm.implies_elim th th1, 3) 1 th2)
     |> pair ctxt |> Seq.single
     |> pair 0
     ) th1s
    val _ = Phi_Reasoner.debug_info ctxt (fn _ => "Reasoning modus pones..." ^ Position.here \<^here>)
    fun obligation_fail S = raise Phi_Reasoners.Attemption_Fail S
  in 
    case Seq.pull (Phi_Reasoner.reason_s ctxt stats)
      of SOME (stat, _) => snd (Phi_Reasoners.safer_obligation_solver' obligation_fail stat)
       | NONE => Phi_Reasoner.error "Meta Modus Pones"
  end

fun MP ctxt th1' th2 =
  MPs ctxt [th1'] th2
  *)
end

