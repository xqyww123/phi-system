theory MaxidxProbe
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>Root-cause probe for the section 8.3-1 acceptance-formula deviation:
  suite 1 C3 measured maxidx -1 -> 0 on the theorem the recovery chain
  returns; the cslh19 dumps show the NOTED global facts keep maxidx -1.
  Hypothesis: the noting/export pipeline (Goal.norm_result etc.) retightens
  the cached maxidx bound; the flip never reaches the stored fact.\<close>

debt_axiomatization ground: \<open>(1::nat) + 1 = 2\<close>

ML \<open>
  val th_noted = @{thm ground}
  val _ = writeln ("noted maxidx = " ^ string_of_int (Thm.maxidx_of th_noted))
  val ((_, th_chain), _) =
    Debt_Axiom.add_debt_axiom_global (\<^binding>\<open>probe\<close>, \<^prop>\<open>(2::nat) + 2 = 4\<close>) \<^theory>
  val _ = writeln ("chain maxidx = " ^ string_of_int (Thm.maxidx_of th_chain))
\<close>

end
