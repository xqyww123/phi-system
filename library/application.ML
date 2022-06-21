signature NU_APPLICATION = sig

  val apply_proc_naive : thm (*proc*) -> context_state -> context_state

  val start_reasoning: context_state -> context_state Seq.seq
  val success_application : context_state -> context_state Seq.seq

  val try_apply : thm list (*applicants*) -> context_state (*sequent*) -> context_state option
  val apply : thm list (*applicants*) -> context_state (*sequent*) -> context_state

(*   val trace : bool Config.T

  type cost = int
  type application_thm = {
    thm : thm, (* the application theorem *)
    applicant_idx : cost (* index of the applicant (e.g. the procedure to be called)
                         * among premises of the application theorem. *)
  }
  type reasoner = (Proof.context -> thm list -> tactic) Nu_Reasoner.generic_reasoner

  val update : (cost * application_thm) -> Context.generic -> Context.generic
  val update' : (cost * reasoner) -> Context.generic -> Context.generic
  
  val content : Context.generic -> (cost * reasoner) list

  val setup_cmd : ((string (*name term*) * cost) * string list (*pattern terms*)) * Input.source (* tactic source*)
        -> local_theory -> local_theory *)
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
    val _ = case Nu_Reasoner.reason (ctxt', sequent')
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
            in Seq.single (ctxt, Goal.conclude result' RS sequent) end
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

fun try_apply applicants (ctxt,sequent) =
  let
    val apps = applicants
                |> map (Conv.fconv_rule (Object_Logic.atomize ctxt))
                |> foldl1 (fn (a,b) => @{thm conjI} OF [a,b]) 
    val sequent' = @{thm \<phi>application} OF [apps, sequent]
  in
    Nu_Reasoner.reason (ctxt,sequent')
      |> Option.map (apsnd (Goal.conclude))
  end

fun apply applicants stat =
  case try_apply applicants stat
    of SOME stat' => stat'
     | NONE => raise THM ("Application Fail", 0, (snd stat)::applicants)

(*
val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_application\<close> (K false);

type applicant_idx = int
type cost = int
type application_thm = {
  thm : thm,
  applicant_idx : applicant_idx
}
type reasoner = (Proof.context -> thm list -> tactic) Nu_Reasoner.generic_reasoner


fun applicant_pattern ({thm,applicant_idx}:application_thm) =
  let
    val prems = Thm.prems_of thm
  in
    (hd prems, nth prems applicant_idx)
          |> apply2 Logic.strip_assums_concl
          |> Logic.mk_conjunction 
  end

fun RLN_with_ctxt ctxt thas thb i =
  Thm.biresolution (SOME ctxt) false (map (pair false) thas) i thb
    |> Seq.map Thm.solve_constraints

fun application_reasoner (appl as {thm,applicant_idx}:application_thm) = {
  name = @{term \<phi>Application_Rule},
  pattern = [applicant_pattern appl],
  tactic = (fn ctxt => fn applicants => fn major =>
    Seq.make (fn () =>
      let
        val sequent = major RS thm
        val _ = if Config.get ctxt trace
                then tracing ("\<phi>application''\nmethod: "
                  ^ Thm.string_of_thm ctxt thm ^ "\napplicants: "
                  ^ String.concatWith "\n \<bullet>" (map (Thm.string_of_thm ctxt) applicants))
                else ()
      in
        RLN_with_ctxt ctxt applicants sequent applicant_idx
          |> Seq.map (fn th =>
              let
                val _ = if Config.get ctxt trace
                        then tracing ("\<phi>application\nmethod: "
                          ^ Thm.string_of_thm ctxt thm ^ "\nsequent: "
                          ^ Thm.string_of_thm ctxt th)
                        else ()
              in
                Goal.protect (applicant_idx - 1) th
              end)
          |> Seq.pull
        handle THM _ => NONE
      end
    ))
  }


structure ApThms = Generic_Data
(
  type T = reasoner Cost_Net.T;
  val empty: T = Cost_Net.init Nu_Reasoner.reasoner_eq #pattern;
  val extend = I;
  val merge : T * T -> T = Cost_Net.merge;
);

fun content ctx = Cost_Net.content (ApThms.get ctx)

fun update' (cost,appl) = ApThms.map (Cost_Net.update (cost,appl))
fun update  (cost,appl) = update' (cost, application_reasoner appl)

fun apply ctx applicants major =
  let
    val apthms = ApThms.get (Context.Proof ctx)
    val applicants = map expand_appliant applicants
    val major_pat = (Thm.major_prem_of major handle THM _ => Thm.concl_of major)
    val patterns = map (fn applicant =>
          Logic.mk_conjunction (major_pat, Thm.concl_of applicant)) applicants
    (* val _ = List.app (tracing o Syntax.string_of_term ctx) patterns *)
  in
    fold (fn pat => fn l => (Cost_Net.retrieve apthms pat) @ l) patterns []
      |> distinct (fn ((_,a),(_,b)) => Nu_Reasoner.reasoner_eq (a,b))
      |> map (apsnd (fn r => #tactic r ctx applicants major))
  end


fun setup_cmd (((name,cost),patterns),tactic_src) lthy =
  let
    val patterns = if null patterns then [name] else patterns
    val name = Syntax.read_term lthy name
    val patterns = Syntax.read_props lthy patterns |> map free_to_var
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of tactic_src)
        (ML_Lex.read
          ("Theory.local_setup (Local_Theory.background_theory (Context.theory_map (NuApply.update' (" ^
          ML_Syntax.print_int cost ^ ", {name=(" ^
          ML_Syntax.print_term name ^ "), pattern=(" ^
          ML_Syntax.print_list ML_Syntax.print_term patterns
          ^ "), tactic=(let in ") @
          ML_Lex.read_source tactic_src @
          ML_Lex.read (" end)}) )))"))
    )
  end

val _ =
  Outer_Syntax.local_theory @{command_keyword setup_\<phi>application_method}
    "define \<phi>application_method"
    (Parse.term -- (Parse.int >> ~) -- Parse.enum "|" Parse.term --| @{keyword =} -- Parse.ML_source
      >> setup_cmd)
*)
end

