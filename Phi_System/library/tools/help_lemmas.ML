signature PHI_HELP_LEMMAS = sig

val local_defs : Proof.context -> thm list

end

structure Phi_Help_Lemmas : PHI_HELP_LEMMAS = struct

fun local_defs ctxt =
  let fun is_local_def (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ X $ _) =
            is_Free (fst (strip_comb X))
        | is_local_def _ = false
   in Assumption.all_assms_of ctxt
       |> filter (is_local_def o Thm.term_of)
       |> map Thm.assume
  end

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>local_defs\<close>, (
  fn Context.Theory _ => []
   | Context.Proof ctxt => local_defs ctxt)))
end