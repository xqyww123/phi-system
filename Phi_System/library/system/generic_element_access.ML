signature PHI_GENERIC_ELEMENT_ACCESS = sig

val get_element_of_abstract_object : Proof.context -> cterm * cterm * cterm -> cterm

val is_enabled_report_unprocessed_element_index : Proof.context -> bool
val enable_report_unprocessed_element_index : Proof.context -> Proof.context
val stop_reporting_unprocessed_element_index : Proof.context -> Proof.context
val report_unprocessed_element_index : cterm -> Proof.context -> Proof.context
val get_unprocessed_element_index : Proof.context -> cterm

val empty_input : cterm

end

structure Phi_Generic_Element_Access : PHI_GENERIC_ELEMENT_ACCESS = struct

(*** Get Element of Abstract Object ***)

val get_element_of_abstract_object_goal =
      Thm.trivial \<^schematic_cprop>\<open>Get_Abstract_Element ?x ?T ?path ?y\<close>

val _ = get_element_of_abstract_object_goal

fun get_element_of_abstract_object ctxt (x,T,path) =
  let val goal = Drule.infer_instantiate ctxt
                    [(("x",0),x), (("T",0),T), (("path",0),path)]
                    get_element_of_abstract_object_goal
   in case Phi_Reasoner.reason (SOME 1) (ctxt, goal)
        of SOME (_, ret) =>
              (case Thm.prop_of ret
                 of _ $ (Const (\<^const_name>\<open>Get_Abstract_Element\<close>, _) $ _ $ _ $ _ $ _) =>
                         Thm.dest_arg (Thm.dest_arg (Thm.cprop_of ret))
                  | _ => raise THM ("bad return of Get_Abstract_Element reasoning", 0, [ret]))
         | NONE => error "Get_Abstract_Element reasoning fails."
  end

(*** Element Index Process ***)

val empty_input = \<^cterm>\<open>[]::element_index_input\<close>

structure Unprc_EleIdx = Single_Thread_Proof_Data_Opt (type T = cterm)

val enable_report_unprocessed_element_index = Unprc_EleIdx.put empty_input
val stop_reporting_unprocessed_element_index = Unprc_EleIdx.del

fun is_enabled_report_unprocessed_element_index ctxt =
  is_some (Unprc_EleIdx.get ctxt)

fun report_unprocessed_element_index ctm ctxt =
  case Unprc_EleIdx.get ctxt
    of SOME _ => Unprc_EleIdx.put ctm ctxt
     | NONE => ctxt

fun get_unprocessed_element_index ctxt =
  case Unprc_EleIdx.get ctxt
    of SOME ret => ret
     | NONE => error "reporting_unprocessed_element_index is not turned on"

end