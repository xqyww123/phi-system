(* value_access.ML
   AUTHOR: Qiyuan Xu

   Access (get and set) local values or variables.
*)

signature VALUE_ACCESS = sig

val collect_and_clean_value : Proof.context -> thm (*sequent*)
                           -> thm (*sequent*) * thm list (*specs of value*)

val register_value_spec_thms : Position.T -> thm list -> Context.generic -> Context.generic
  (*so that the values can be synthesised*)

val open_value_context  : Position.T -> context_state -> context_state
(*val open_value_context' : Position.T -> Proof.state -> Proof.state *)

end

structure Value_Access : VALUE_ACCESS = struct

fun collect_and_clean_value ctxt sequent =
  let
    val mode = Phi_Working_Mode.working_mode_on1 ctxt (Thm.concl_of sequent)
  in (ctxt, @{thm apply_collect_clean_value} RS (sequent COMP #transform_rule mode))
  |> Phi_Reasoner.reason NONE
  |> (fn SOME (_, sequent') => sequent'
                            |> HOLogic.conj_elim ctxt
                            |> apsnd (fn th => th |> HOLogic.conj_elims ctxt |> rev
                                                  |> tl (*the head is always True*))
       | NONE => Phi_Reasoner.error "Internal bug #vb7iop23")
  end

fun register_value_spec_thms pos rules =
  Phi_Reasoner.add_intro_rules (map (fn rule =>
    let
      val i = maxidx_of_term (Thm.prop_of rule) + 1
      val pattern = 
            (case Thm.prop_of rule
               of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, T1)
                                  $ (Const (\<^const_name>\<open>sem_value.dest\<close>, T2) $ V)
                                  $ TM )
                => \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, T1)
                                   $ (Const (\<^const_name>\<open>sem_value.dest\<close>, T2) $ V)
                                   $ Var (("spec",i), fastype_of TM) )
            | _ => raise THM ("Not a specification theorem of a value!", 0, [rule]))
    in (rule, pos, 1000, [pattern], []) end
  ) rules)

fun open_value_context pos (ctxt,sequent) =
  let
    val mode = Phi_Working_Mode.working_mode_on1 ctxt (Thm.prop_of sequent)
    val (sequent', rules) = collect_and_clean_value ctxt sequent
    val args = rules |> map (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>sem_value.dest\<close>, _) $ V)
                                  $ _)
                 => V
             | _ => error "Internal Bug q34v6 nu89p")
    val binds = rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>sem_value.dest\<close>, _) $ V)
                                  $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ Free (N,_) $ _))
                 => SOME (N, V)
             | _ => NONE)
    val binds'= rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>sem_value.dest\<close>, _) $ (V as Free (N,_)))
                                  $ _)
                 => SOME (N, V)
             | _ => NONE)
  in ctxt
  |> Value_Access_Syntax.open_value_context args
  |> Context.proof_map (register_value_spec_thms pos rules)
  |> Value_Access_Syntax.bind_local_vals (binds' @ binds)
  |> rpair sequent'
  end

(*
fun open_value_context' pos stat =
  Proof.map_context (open_value_context pos (Phi_Basics.the_nu_fact stat)) stat
  *)

end