signature PHI_VALUE_PROPERTIES = sig
end

structure Phi_Value_Properties : PHI_VALUE_PROPERTIES = struct

val dest_SemType = Phi_Syntax.dest_tags #> Phi_Help.dest_binop \<^const_name>\<open>\<phi>SemType\<close>
val dest_SemType_c = Phi_Syntax.dest_tags_c #> Phi_Help.dest_binop_c \<^const_name>\<open>\<phi>SemType\<close>

val dest_Zero = Phi_Syntax.dest_tags #> Phi_Help.dest_triop \<^const_name>\<open>\<phi>Zero\<close>
val dest_Zero_c = Phi_Syntax.dest_tags_c #> Phi_Help.dest_triop_c \<^const_name>\<open>\<phi>Zero\<close>

(* Semantic Type *)

fun finish_sem_type hyp (_,sequent) =
    let val (s,_) = Phi_Syntax.dest_ToA_Construction_c hyp
    in sequent
        |> Thm.implies_intr hyp
        |> Thm.forall_intr s
        |> (fn th => th COMP @{thm \<phi>assemble_SemType})
    end

fun start_implication finish arg ctxt =
    let open Phi_Syntax
      val ([blk_name],ctxt) = Variable.add_fixes ["\<CC>"] ctxt
      val Type (\<^type_name>\<open>set\<close>, [T]) = Thm.typ_of_cterm arg
      val stat_var = Free (blk_name, T)
      val ctxt = Variable.declare_constraints stat_var ctxt
      val init = Const(\<^const_name>\<open>ToA_Construction\<close>, dummyT) $ stat_var
      val init = Thm.cterm_of ctxt (Syntax.check_term ctxt init)
      val init = Thm.apply @{cterm Trueprop} (Thm.apply init arg)
      val ([init],ctxt) = Assumption.add_assms
            (fn _ => fn [hyp] => (finish hyp o pair ctxt, I)) [init] ctxt
    in
      (ctxt,init)
    end

fun vcg_sem_type goal (ctxt,sequent) =
  let
    val S = #2 (Phi_Syntax.dest_ToA_Construction (Thm.prop_of sequent))
    val TY = #2 (dest_SemType_c goal)
    val idx = 1 + Thm.maxidx_of sequent
    val rule = @{thm \<phi>finalization_SemType}
            |> Thm.incr_indexes idx
            |> Thm.instantiate (TVars.empty, Vars.make [((("TY",idx),\<^typ>\<open>TY\<close>),TY)])
  in (ctxt, sequent RS rule)
  |> Phi_Reasoner.reason1 (fn _ => Pretty.string_of (Pretty.chunks [
        Pretty.block [Pretty.str "The value specification does not have semantic type ",
                      Syntax.pretty_term ctxt (Thm.term_of TY)],
        Syntax.pretty_term ctxt S
      ])) NONE
  end

val sem_type : Phi_Working_Mode.working_mode = {
  name = "\<phi>SemType",
  domain = (fn _ => can dest_SemType),
  spec_of = #spec_of Phi_Working_Mode.implication,
  spec_of_c = #spec_of_c Phi_Working_Mode.implication,
  source_spec = #1 o dest_SemType,
  source_spec_c = #1 o dest_SemType_c,
  inhabited_rule = #inhabited_rule Phi_Working_Mode.implication,
  initial_sequent = start_implication finish_sem_type,
  transformation_rule = #transformation_rule Phi_Working_Mode.implication,
  view_shift_rule = #view_shift_rule Phi_Working_Mode.implication,
  cast = #cast Phi_Working_Mode.implication,
  cast_exception = #cast_exception Phi_Working_Mode.implication,
  vcg_before_assembling = vcg_sem_type,
  introduce_existence = #introduce_existence Phi_Working_Mode.implication,
  introduce_existence_in_assembling = #introduce_existence_in_assembling Phi_Working_Mode.implication
}

(* Zero Value *)

fun make_zero_value goal ctxt =
  let val (TY,T,x) = dest_Zero_c goal
      val idx = Thm.maxidx_of_cterm goal + 1
  in @{thm \<phi>make_zero_value}
  |> Thm.incr_indexes idx
  |> Drule.infer_instantiate ctxt [(("TY",idx),TY), (("T",idx),T), (("x",idx),x)]
  |> pair ctxt
  end

val zero_value : Phi_Working_Mode.working_mode = {
  name = "\<phi>Zero",
  domain = (fn _ => can dest_Zero),
  spec_of = #spec_of Phi_Working_Mode.implication,
  spec_of_c = #spec_of_c Phi_Working_Mode.implication,
  source_spec = I,
  source_spec_c = I,
  inhabited_rule = #inhabited_rule Phi_Working_Mode.implication,
  initial_sequent = make_zero_value,
  transformation_rule = #transformation_rule Phi_Working_Mode.implication,
  view_shift_rule = #view_shift_rule Phi_Working_Mode.implication,
  cast = #cast Phi_Working_Mode.implication,
  cast_exception = #cast_exception Phi_Working_Mode.implication,
  vcg_before_assembling = K I,
  introduce_existence = #introduce_existence Phi_Working_Mode.implication,
  introduce_existence_in_assembling = #introduce_existence_in_assembling Phi_Working_Mode.implication
}


val _ = Theory.setup (Context.theory_map (Phi_Working_Mode.register
          [sem_type, zero_value]))


end