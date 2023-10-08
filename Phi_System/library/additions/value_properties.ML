signature PHI_LOCAL_VALUE_PROPERTIES = sig
end

structure Phi_Local_Value_Properties : PHI_LOCAL_VALUE_PROPERTIES = struct

val dest_Zero   = PLPR_Syntax.dest_tags   #> Phi_Help.dest_triop   \<^const_name>\<open>\<phi>Zero\<close>
val dest_Zero_c = PLPR_Syntax.dest_tags_c #> Phi_Help.dest_triop_c \<^const_name>\<open>\<phi>Zero\<close>

(* Zero Value *)

fun make_zero_value ctxt goal =
  let val (TY,T,x) = dest_Zero_c goal
      val idx = Thm.maxidx_of_cterm goal + 1
  in @{thm \<phi>deduce_zero_value}
  |> Thm.incr_indexes idx
  |> Drule.infer_instantiate ctxt [(("TY",idx),TY), (("T",idx),T), (("x",idx),x)]
  |> Phi_Reasoner.reason NONE (SOME 1) ctxt
  |> (fn SOME s => s
       | NONE => error (Pretty.string_of (Pretty.block [
           Pretty.str "The rule of the semantic type of ",
           Syntax.pretty_term ctxt (Thm.term_of T),
           Pretty.str " has not been given, so the proof of its zero value cannot be proceeded."
           ])))
  end

val make_zero_value' =
  Proof.map_context_result (fn c => (make_zero_value c (Phi_Envir.get_thesis c), c))

val zero_value : Phi_Working_Mode.working_mode = {
  name = \<^const_name>\<open>working_mode_\<phi>Zero\<close>,
  domain = can dest_Zero,
  is_on_going_construction = can dest_Zero,
  spec_of = #spec_of Phi_Working_Mode.implication,
  spec_of_c = #spec_of_c Phi_Working_Mode.implication,
  inhabited_rule = #inhabited_rule Phi_Working_Mode.implication,
  initialize_sequent = make_zero_value',
  transformation_rule = #transformation_rule Phi_Working_Mode.implication,
  view_shift_rule = #view_shift_rule Phi_Working_Mode.implication,
  cast = #cast Phi_Working_Mode.implication,
  cast_exception = #cast_exception Phi_Working_Mode.implication,
  vcg_before_assembling = K I,
  introduce_existence = #introduce_existence Phi_Working_Mode.implication,
  introduce_existence_in_assembling = #introduce_existence_in_assembling Phi_Working_Mode.implication
}


val _ = Theory.setup (Context.theory_map (Phi_Working_Mode.register [zero_value]))


end