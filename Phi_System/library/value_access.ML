signature VALUE_ACCESS = sig

val all_value_terms : term (*\<phi>-BI assertion*) -> term list
val all_value_spec_thms : Proof.context -> thm (*sequent*) -> thm list

val register_value_spec_thms : Position.T -> thm list -> Context.generic -> Context.generic
  (*so that the values can be synthesised*)

val open_value_context  : Position.T -> thm -> Proof.context -> Proof.context
val open_value_context' : Position.T -> Proof.state -> Proof.state

end

structure Value_Access : VALUE_ACCESS = struct

fun all_value_terms assertion =
      Phi_Syntax.strip_separations assertion
   |> map_filter (fn (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ V $ _))
                       => SOME V
                   | _ => NONE)

fun all_value_spec_thms ctxt sequent =
     Phi_Basics.reason_programming_implication ctxt
       @{thms ExSet_inhabited Subjection_inhabited Val_inhabited_collect set_mult_inhabited}
       sequent
  |> conv_GE_to_plain_conjunction ctxt
  |> filter (fn th => case Thm.prop_of th
                        of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                                $ (Const (\<^const_name>\<open>sem_value.dest\<close>, _) $ _)
                                                $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _))
                              => true
                          | _ => false)

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

fun open_value_context pos sequent ctxt =
  let
    val mode = Phi_Working_Mode.working_mode_on1 ctxt (Thm.prop_of sequent)
    val args = all_value_terms (#argument_spec mode (Thm.prop_of sequent))
    val rules = all_value_spec_thms ctxt sequent
  in ctxt
  |> Value_Access_Syntax.open_value_context args
  |> Context.proof_map (register_value_spec_thms pos rules)
  end

fun open_value_context' pos stat =
  Proof.map_context (open_value_context pos (Phi_Basics.the_nu_fact stat)) stat
  

end