theory PhiSem_C
  imports PhiSem_Mem_C
          PhiSem_Mem_C_Ag_NT
          PhiSem_Mem_C_Ag_Ar
          PhiSem_CF_Routine
          PhiSem_CF_Breakable
          PhiSem_Variable
          PhiSem_Machine_Integer
          PhiSem_Machine_Integer_Boolean
          PhiSem_Mem_C_Ar_MI
begin

debt_axiomatization
  where \<p>\<t>\<r>_neq_\<i>\<n>\<t>'  [simp]: \<open>\<p>\<t>\<r> \<noteq> sem_int_T n\<close>
    and \<p>\<t>\<r>_neq_\<s>\<t>\<r>\<u>\<c>\<t> [simp]: \<open>\<p>\<t>\<r> \<noteq> semty_ntup f\<close>


lemma TY_neqs[simp]:
  \<open>\<p>\<t>\<r> \<noteq> \<i>\<n>\<t>('n)\<close>         \<open>\<i>\<n>\<t>('n) \<noteq> \<p>\<t>\<r>\<close>
  \<open>\<p>\<t>\<r> \<noteq> \<b>\<o>\<o>\<l>\<close>            \<open>\<b>\<o>\<o>\<l> \<noteq> \<p>\<t>\<r>\<close>
  \<open>semty_ntup f \<noteq> \<p>\<t>\<r>\<close>
  unfolding mk_int_T_def bool_def'
  by simp_all (metis \<p>\<t>\<r>_neq_\<i>\<n>\<t>' \<p>\<t>\<r>_neq_\<s>\<t>\<r>\<u>\<c>\<t>)+



(*declare [[\<phi>infer_requirements]]*)

(*
setup \<open>Context.theory_map (Phi_Hacks.Thy_At_Begin.add 66 (K (
  Simplifier.map_theory_simpset (fn ctxt => ctxt delsimps @{thms' Nat.One_nat_def Num.add_2_eq_Suc'}))))
\<close> 

declare One_nat_def[\<phi>sledgehammer_simps] *)



ML \<open>fun filter_out (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>to\<close>, _) $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>OPEN\<close>, _) $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>MAKE\<close>, _) $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = filter_out X
    | filter_out (Abs (_, _, X)) = filter_out X
    | filter_out (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>Identifier_of\<close>, _) $ _ $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>Semantic_Type\<close>, _) $ _ $ _) = true
    | filter_out _ = false

  fun report_utilization statistic_groups reasoner_groups =
  let open Pretty
      val statistics = Phi_Reasoner.utilization_of_groups_in_all_theories
          (Context.Theory \<^theory>) (map (the o snd) reasoner_groups) statistic_groups
        |> filter (fn (th, i) => i > 0 andalso not (filter_out (Thm.concl_of th)))
      val (R,R') = (length statistics, Integer.sum (map snd statistics))
   in Output.writeln ("R = " ^ string_of_int R ^ ", R' = " ^ string_of_int R')
  end
\<close>


end