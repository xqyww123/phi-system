signature GENERIC_ELEMENT_ACCESS = sig

type prohibit_remainig_eleidx = bool
exception Remaining_Eleidx of cterm

val get_element_of_abstract_object : Proof.context -> cterm * cterm * cterm -> cterm

val is_enabled_report_unprocessed_element_index : Proof.context -> bool
val enable_report_unprocessed_element_index : prohibit_remainig_eleidx -> Proof.context -> Proof.context
val stop_reporting_unprocessed_element_index : Proof.context -> Proof.context
val report_unprocessed_element_index : cterm * cterm -> Proof.context -> Proof.context
val get_unprocessed_element_index : Proof.context -> (cterm * cterm) option
val error_unprocessed_element_index : Proof.context -> cterm -> 'a

val empty_input : cterm
val is_empty_input : term -> bool

(*Final hook for parsing operators like 'Address-Of'*)

val EIHook_none : cterm

end

structure Generic_Element_Access : GENERIC_ELEMENT_ACCESS = struct

val EIHook_none = \<^cterm>\<open>\<E>\<I>\<H>\<O>\<O>\<K>_none\<close>
               |> Thm.trim_context_cterm

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

type prohibit_remainig_eleidx = bool
exception Remaining_Eleidx of cterm

val empty_input = \<^cterm>\<open>[]::element_index_input\<close>
fun is_empty_input (Const (\<^const_name>\<open>Nil\<close>, _)) = true
  | is_empty_input _ = false

structure Unprc_EleIdx = Single_Thread_Proof_Data_Opt (type T = prohibit_remainig_eleidx * (cterm * cterm) option)

fun enable_report_unprocessed_element_index flag = Unprc_EleIdx.put (flag, NONE)
val stop_reporting_unprocessed_element_index = Unprc_EleIdx.del

fun is_enabled_report_unprocessed_element_index ctxt =
  is_some (Unprc_EleIdx.get ctxt)

fun report_unprocessed_element_index (ctm,hook) ctxt =
  case Unprc_EleIdx.get ctxt
    of SOME (prohibit_remain, _) =>
        if prohibit_remain andalso not (is_empty_input (Thm.term_of ctm))
        then raise Remaining_Eleidx ctm
        else Unprc_EleIdx.put (false, SOME (ctm,hook)) ctxt
     | NONE => ctxt

fun get_unprocessed_element_index ctxt =
  case Unprc_EleIdx.get ctxt
    of SOME (_, ret) => ret
     | NONE => error "reporting_unprocessed_element_index is not turned on"


fun error_unprocessed_element_index ctxt idx =
  error (let open Pretty in
    string_of (chunks (
      block (
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
        ) :: Phi_Reasoners.failure_reasons_of' ctxt
     ))
  end)

end