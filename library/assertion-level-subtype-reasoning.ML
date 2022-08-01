signature ASSERTION_LEVEL_SUBTYPE_REASONING = sig
  val branch_envir_schematics : thm -> term list
end

structure Assertion_Level_Subtype_Reasoning : ASSERTION_LEVEL_SUBTYPE_REASONING = struct

fun branch_envir_schematics sequent =
      Thm.prems_of sequent
        |> map_filter (fn Const (\<^const_name>\<open>Assertion_Level_Subtyp_Reasoning_Branch_Envir\<close>, _)
                            $ tm => SOME (HOLogic.strip_tuple tm)
                        | _ => NONE)
        |> flat
        |> distinct (op =)

end