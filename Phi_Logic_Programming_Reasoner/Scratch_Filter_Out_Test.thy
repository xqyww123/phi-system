(*TEMPORARY 2026-08-11 -- DELETE AFTER: §7.3b of OBLIGATION_PREMISE_LOSS_PLAN_V2.md.
  The registry of \<phi>filter_out_from_obligation_premise starts empty, so every part of
  it (parser, mk_spattern, does_smatch, iNet insertion and its clash report, the
  trace switch) would otherwise ship without ever having run.
  The last two commands are EXPECTED TO FAIL -- that is what they test.*)
theory Scratch_Filter_Out_Test
  imports PLPR
begin

subsection \<open>The probe goal\<close>

text \<open>Both antecedents are shapes that really occur among the five antecedents
  discarded at \<^file>\<open>../Phi_System/Phi_Types.thy\<close> line 2529.\<close>

ML \<open>
val probe_goal = @{cprop \<open>length xs = n \<Longrightarrow> iv = iv' \<Longrightarrow> g xs iv\<close>}

fun probe ctxt =
  Goal.init probe_goal
    |> (fn th => @{thm' Premise_D[where mode=default]} RS th)
    |> Phi_Reasoners.collect_obligation_premises (true, true, 0) ctxt
    |> apsnd (fn th => Syntax.string_of_term ctxt (Thm.major_prem_of th))
\<close>

subsection \<open>1. Nothing is filtered while the registry is empty\<close>

ML \<open>probe \<^context>\<close>

subsection \<open>2. A registered shape is filtered, and the trace says why\<close>

declare [[\<phi>trace_filter_out_from_obligation_premise = true]]
declare [[\<phi>filter_out_from_obligation_premise \<open>length xs = n\<close>]]

ML \<open>probe \<^context>\<close>

subsection \<open>3. A \<open>var_\<close>-prefixed variable matches only schematic variables\<close>

declare [[\<phi>filter_out_from_obligation_premise \<open>f var_x\<close>]]

ML \<open>
val query = Phi_Reasoners.is_filtered_out_from_obligation_premise (Context.Proof \<^context>)
val matches_a_schematic_variable = query [] \<^prop>\<open>f (?y::nat)\<close>
val matches_a_fixed_variable     = query [] \<^prop>\<open>f (n::nat)\<close>
val _ = \<^assert> (matches_a_schematic_variable andalso not matches_a_fixed_variable)
\<close>

subsection \<open>4. Registering the same shape again clashes readably (EXPECTED ERROR)\<close>

declare [[\<phi>filter_out_from_obligation_premise \<open>length xs = n\<close>]]

end
