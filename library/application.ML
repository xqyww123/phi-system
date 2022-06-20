signature NU_APPLICATION = sig

  val trace : bool Config.T

  val apply_proc_naive : Proof.context -> thm (*proc*) -> thm (*meta or major*) -> thm

  type cost = int
  type application_thm = {
    thm : thm, (* the application theorem *)
    applicant_idx : cost (* index of the applicant (e.g. the procedure to be called)
                         * among premises of the application theorem. *)
  }
  type reasoner = (Proof.context -> thm list -> tactic) Nu_Reasoner.generic_reasoner

  val update : (cost * application_thm) -> Context.generic -> Context.generic
  val update' : (cost * reasoner) -> Context.generic -> Context.generic
  val apply : Proof.context -> thm list (*applicant*) -> thm (*sequent*)
        -> (cost * thm Seq.seq) list
  val content : Context.generic -> (cost * reasoner) list

  val setup_cmd : ((string (*name term*) * cost) * string list (*pattern terms*)) * Input.source (* tactic source*)
        -> local_theory -> local_theory
end

structure NuApply : NU_APPLICATION = struct
open NuHelp

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_application\<close> (K false);

val expand_appliant = 
  repeat (fn th => th RS @{thm spec}) #>
  repeat (fn th => th RS @{thm mp}) #>
  repeat (fn th => th RS @{thm spec})

fun apply_proc_naive ctxt proc sequent =
  expand_appliant proc RS (sequent RS (Proof_Context.get_thm ctxt "local.\<phi>apply_proc"))

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

end

