signature GENERIC_ELEMENT_ACCESS = sig

val get_element_of_abstract_object : Proof.context -> cterm * cterm * cterm -> cterm

val is_enabled_report_unprocessed_element_index : Proof.context -> bool
val enable_report_unprocessed_element_index : Proof.context -> Proof.context
val stop_reporting_unprocessed_element_index : Proof.context -> Proof.context
val report_unprocessed_element_index : cterm -> Proof.context -> Proof.context
val get_unprocessed_element_index : Proof.context -> cterm
val error_unprocessed_element_index : Proof.context -> cterm -> 'a

val empty_input : cterm
val is_empty_input : term -> bool

end

structure Generic_Element_Access : GENERIC_ELEMENT_ACCESS = struct

(*** Get Element of Abstract Object ***)

val get_element_of_abstract_object_goal =
      Thm.trivial \<^schematic_cprop>\<open>Get_Abstract_Element ?x ?T ?path ?y\<close>

fun get_element_of_abstract_object ctxt (x,T,path) =
  let val idx = Int.max (Thm.maxidx_of_cterm x, Int.max (Thm.maxidx_of_cterm T, Thm.maxidx_of_cterm path)) + 1
      val goal = Thm.incr_indexes idx get_element_of_abstract_object_goal
              |> Drule.infer_instantiate ctxt [(("x",idx),x), (("T",idx),T), (("path",idx),path)]
      val ret = Phi_Reasoner.reason1 (fn _ => error "Get_Abstract_Element reasoning fails.")
                                     NONE (SOME 1) ctxt goal
   in case Thm.prop_of ret
        of _ $ (Const (\<^const_name>\<open>Get_Abstract_Element\<close>, _) $ _ $ _ $ _ $ _) =>
                Thm.dest_arg (Thm.dest_arg (Thm.cprop_of ret))
         | _ => raise THM ("bad return of Get_Abstract_Element reasoning", 0, [ret])
  end

(*** Element Index Process ***)

val empty_input = \<^cterm>\<open>[]::element_index_input\<close>
fun is_empty_input (Const (\<^const_name>\<open>Nil\<close>, _)) = true
  | is_empty_input _ = false

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

fun error_unprocessed_element_index ctxt idx =
  error (Pretty.string_of (Pretty.block (
            Pretty.str "Fail to access element " ::
            flat (Library.separate [Pretty.str "."] (map single (
                HOLogic.dest_list (Thm.term_of idx)
             |> map (
                  (fn term => case Phi_Tool_Symbol.revert_symbol_term term
                                of SOME str => Pretty.str str
                                 | NONE => Syntax.pretty_term ctxt term) o
                  (fn term => case try Phi_Syntax.dest_phi_type_assertion term
                                of SOME (x, _) => x
                                 | _ => term) o
                  snd o HOLogic.dest_prod))))
        )))

end