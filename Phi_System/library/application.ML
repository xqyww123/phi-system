signature NU_APPLICATION = sig

  val apply_proc_naive : thm (*proc*) -> context_state -> context_state

  val start_reasoning: context_state -> context_state Seq.seq
  val success_application : context_state -> context_state Seq.seq

  val try_apply : thm list (*applicants*) -> context_state (*sequent*) -> context_state option
  val apply : thm list (*applicants*) -> context_state (*sequent*) -> context_state

  (*Advanced Modus Pones using logic programming conducted by \<^term>\<open>\<phi>Application_Conv\<close>
    which infers various conversion of applicants.
   *)
  val MPs : Proof.context -> thm list -> thm -> thm
  val MP  : Proof.context -> thm -> thm -> thm

end

structure NuApply : NU_APPLICATION = struct
open NuHelp

val expand_appliant = 
  repeat (fn th => th RS @{thm spec}) #>
  repeat (fn th => th RS @{thm mp}) #>
  repeat (fn th => th RS @{thm spec})

fun apply_proc_naive proc (ctxt,sequent) =
  (ctxt, expand_appliant proc RS (sequent RS (Proof_Context.get_thm ctxt "local.\<phi>apply_proc")))

val empty_var = Synchronized.var "\<phi>applicant_ctxt" [] : thm list Synchronized.var

structure AppContext = Proof_Data (
  type T = thm list (*successful application*) Synchronized.var
  val init = K empty_var
)

val bad_rule_msg =
  "The reasoning of application finishes without invoking \<phi>Application_Success.\n"^
  "Some application rule must be wrong."^
  "A correct application rule should have proposition \<phi>Application_Success in its premises, "^
  "marking the sequent behind this premise is the result of the application."

fun app_equivalent ctxt (thm1, thm2) =
  let
    val goal = Goal.init (Thm.mk_binop \<^cterm>\<open>(\<equiv>)::prop \<Rightarrow> prop \<Rightarrow> prop\<close>
                  (Thm.cprop_of thm1) (Thm.cprop_of thm2))
  in
    is_some (Seq.pull (SOLVED' (Simplifier.simp_tac ctxt) 1 goal))
  end

fun start_reasoning (ctxt,sequent) =
  let
    val (app,state,result) = dest_triop_c \<^const_name>\<open>\<phi>Application\<close> (Thm.cprem_of sequent 1)
    val sequent' = @{thm \<phi>application_start_reasoning}
          |> Drule.infer_instantiate ctxt
                [(("Apps",0), app),
                 (("State",0), state),
                 (("Result",0), result)]
    val successful_app = Synchronized.var "\<phi>applicant_ctxt" []
    val ctxt' = AppContext.put successful_app ctxt
    val _ = case Nu_Reasoner.reason ~1 (ctxt', sequent')
              of SOME _ => error bad_rule_msg
               | NONE => ()
  in
    case Synchronized.value successful_app
          |> distinct (app_equivalent ctxt)
      of thms as (_ :: _ :: _) =>
        (warning ("Failed application in \n"^Thm.string_of_thm ctxt sequent^
          "\nThere are more than one available applications that are not trivially equivalent:\n"^
          String.concatWith "\n" (map (fn t=> "\<bullet> "^Thm.string_of_thm ctxt t) thms)^
          "\nThe system cannot determine which one to be applied. You may modify the code to be more specific.");
         Seq.empty)
       | [result] =>
            let val result' = Raw_Simplifier.rewrite_rule ctxt @{thms \<phi>Application_normalize} result
            in Seq.single (ctxt, result' RS sequent) end
       | [] =>
        (warning ("Failed application in \n"^Thm.string_of_thm ctxt sequent^
          "\nNo available applications are found.");
         Seq.empty)
  end

fun success_application (ctxt,sequent) =
  let
    val sequent' = @{thm \<phi>application_success} RS sequent
    val _ = Synchronized.change (AppContext.get ctxt)
                (fn thms => sequent' :: thms)
  in
    Seq.empty
  end

fun try_apply [] (ctxt,sequent) = NONE
  | try_apply applicants (ctxt,sequent) =
      let
        val apps = applicants
                    |> foldl1 (fn (a,b) =>
                          Drule.comp_no_flatten (b,0) 1 (
                           Drule.comp_no_flatten (a,0) 1 @{thm conjunctionI}))
        val sequent' = sequent RS (Drule.comp_no_flatten (apps,0) 1 @{thm \<phi>application})
        val _ = Nu_Reasoner.debug_info ctxt (fn _ => "Reasoning generic applications...")
      in
        Nu_Reasoner.reason ~1 (ctxt,sequent')
          |> Option.map (apsnd (Goal.conclude))
      end

fun apply applicants stat =
  case try_apply applicants stat
    of SOME stat' => stat'
     | NONE => raise THM ("Application Fail", 0, (snd stat)::applicants)


fun comp_no_flatten_matched (th, n) i rule =
  (case distinct Thm.eq_thm (Seq.list_of
      (Thm.bicompose NONE {flatten = false, match = true, incremented = true}
        (false, th, n) i rule)) of
    [th'] => Thm.solve_constraints th'
  | [] => raise THM ("comp_no_flatten", i, [th, rule])
  | _ => raise THM ("comp_no_flatten: unique result expected", i, [th, rule]));

fun MPs ctxt th1s' th2 =
  let
    val th1s = map (Drule.incr_indexes th2) th1s'
    val stats = map (fn th1 =>
          Thm.instantiate (TVars.empty, Vars.make [
              ((("P",0), \<^typ>\<open>prop\<close>), Thm.cprop_of th1),
              ((("Q",0), \<^typ>\<open>prop\<close>), Thm.cprem_of th2 1)
          ]) @{thm \<phi>Application_Conv}
     |> (fn th => comp_no_flatten_matched (Thm.implies_elim th th1, 3) 1 th2)
     |> pair ctxt |> Seq.single
     |> pair 0
     ) th1s
    val _ = Nu_Reasoner.debug_info ctxt (fn _ => "Reasoning modus pones...")
    fun obligation_fail S = raise Nu_Reasoners.Attemption_Fail S
  in 
    case Seq.pull (Nu_Reasoner.reason_s ctxt stats)
      of SOME (stat, _) => snd (Nu_Reasoners.safer_obligation_solver' obligation_fail stat)
       | NONE => error(
            "Reasoning Fails. You may turn on \<phi>trace_reasoning to debug where the reasoning fails.")
  end

fun MP ctxt th1' th2 =
  MPs ctxt [th1'] th2
  
end

