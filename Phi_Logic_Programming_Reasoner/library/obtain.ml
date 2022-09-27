structure PLPR_obtain = struct

fun reason (ctxt, sequent) =
  let
    val obtain_goal = Thm.major_prem_of sequent
    fun to_ex_goal (Const (\<^const_name>\<open>Obtain\<close>, Type ("fun", [_, ty])) $ _ $ P)
          = Const (\<^const_name>\<open>Ex\<close>, ty) $ to_ex_goal P
      | to_ex_goal (\<^const>\<open>Trueprop\<close> $ P) = \<^const>\<open>Trueprop\<close> $ to_ex_goal P
      | to_ex_goal P = P
    val goal = Thm.trivial (Thm.cterm_of ctxt (to_ex_goal obtain_goal))
   in goal RS (sequent COMP @{thm conjunctionI})
  end

end