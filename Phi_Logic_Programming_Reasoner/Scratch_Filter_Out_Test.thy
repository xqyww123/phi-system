(*TEMPORARY 2026-08-12 -- DELETE AFTER: \<section>7.3b of OBLIGATION_PREMISE_LOSS_PLAN_V2.md.
  The registry of \<phi>filter_out_from_obligation_premise starts empty, so every part of it
  (parser, mk_spattern, does_smatch, iNet insertion and its clash report, the trace
  switch) would otherwise ship without ever having run.
  Every check is an assertion: if this theory loads, it passed.*)
theory Scratch_Filter_Out_Test
  imports PLPR
begin

subsection \<open>The probe goal\<close>

text \<open>Both antecedents are shapes that really occur among the five antecedents
  discarded at \<^file>\<open>../Phi_System/Phi_Types.thy\<close> line 2529.\<close>

ML \<open>
val probe_goal = @{cprop \<open>length xs = n \<Longrightarrow> iv = iv' \<Longrightarrow> g xs iv\<close>}

(*how many antecedents were folded in, and the resulting obligation as plain text*)
fun probe ctxt =
  Goal.init probe_goal
    |> (fn th => @{thm' Premise_D[where mode=default]} RS th)
    |> Phi_Reasoners.collect_obligation_premises (true, true, 0) ctxt
    |> apsnd (fn th => Protocol_Message.clean_output
                         (Syntax.string_of_term ctxt (Thm.major_prem_of th)))
\<close>

subsection \<open>1. Nothing is filtered while the registry is empty\<close>

ML \<open>
val (folded_0, obligation_0) = probe \<^context>
val _ = writeln ("empty registry: " ^ obligation_0)
val _ = \<^assert> (folded_0 = 2)
val _ = \<^assert> (String.isSubstring "length xs = n" obligation_0)
val _ = \<^assert> (String.isSubstring "iv = iv'" obligation_0)
\<close>

subsection \<open>2. A registered shape is filtered out\<close>

text \<open>Turn the trace on as well; its text is read by eye in the prover output,
  since \<^ML>\<open>tracing\<close> cannot be captured from here.\<close>

declare [[\<phi>trace_filter_out_from_obligation_premise = true]]
declare [[\<phi>filter_out_from_obligation_premise \<open>length xs = n\<close>]]

ML \<open>
val (folded_1, obligation_1) = probe \<^context>
val _ = writeln ("one shape registered: " ^ obligation_1)
val _ = \<^assert> (folded_1 = 1)
val _ = \<^assert> (not (String.isSubstring "length xs" obligation_1))
val _ = \<^assert> (String.isSubstring "iv = iv'" obligation_1)
\<close>

subsection \<open>3. A \<open>var_\<close>-prefixed variable matches only schematic variables\<close>

text \<open>This is the check that \<^ML>\<open>PLPR_Pattern.mk_spattern\<close> really was applied at
  registration: without it the negative variable index that carries the convention
  is never created and the pattern below would match a fixed variable too.\<close>

declare [[\<phi>filter_out_from_obligation_premise \<open>f var_x\<close>]]

ML \<open>
val query = Phi_Reasoners.is_filtered_out_from_obligation_premise (Context.Proof \<^context>)
val f = Free ("f", \<^typ>\<open>nat \<Rightarrow> bool\<close>)
val _ = \<^assert> (query [] (HOLogic.mk_Trueprop (f $ Var (("y",0), \<^typ>\<open>nat\<close>))))
val _ = \<^assert> (not (query [] (HOLogic.mk_Trueprop (f $ Free ("n", \<^typ>\<open>nat\<close>)))))
\<close>

subsection \<open>4. Registering the same shape twice reports the clash readably\<close>

ML \<open>
val attribute_name =
      Attrib.check_name \<^context> ("\<phi>filter_out_from_obligation_premise", \<^here>)
val _ = writeln ("attribute resolves to: " ^ attribute_name)
val duplicate_declaration =
      Token.make_src (attribute_name, \<^here>)
        [Token.make_string ("length xs = n", Position.none)]
val clash =
     (case Exn.capture (fn () =>
              Thm.apply_attribute (Attrib.attribute \<^context> duplicate_declaration)
                                  Drule.dummy_thm (Context.Proof \<^context>)) ()
        of Exn.Res _ => "<no error was raised>"
         | Exn.Exn exn => Protocol_Message.clean_output (Runtime.exn_message exn))
val _ = writeln ("clash report: " ^ clash)
val _ = \<^assert> (String.isSubstring "Clash with an existing" clash)
\<close>

text \<open>Step 5 of \<section>7.3b -- withdrawing this theory and confirming the behaviour returns to
  the empty-registry state -- cannot be an assertion inside the theory that does the
  registering. It is discharged by deleting this file: the registrations above live in
  this theory's context only, and no other theory imports this one.\<close>

end
