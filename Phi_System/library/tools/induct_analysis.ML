signature IDECP_INDUCT_ANALYSIS = sig

val case_analysis : bool * (term option list list * thm option) -> Proof.context * thm -> thm
val case_analysis_processor : Phi_Opr_Stack.context -> (Phi_CP_IDE.eval_cfg -> Phi_Opr_Stack.context) parser

end

structure IDECP_Induct_Analysis : IDECP_INDUCT_ANALYSIS = struct

(*Syntax Parser stolen from ISABELLE/src/Tools/induct.ML*)

local
val arbitraryN = "arbitrary";
val takingN = "taking";
val ruleN = "rule";
val typeN = "type";
val predN = "pred";
val setN = "set";

fun unless_more_args scan = Scan.unless (Scan.lift
      ((Args.$$$ arbitraryN || Args.$$$ takingN || Args.$$$ typeN ||
        Args.$$$ predN || Args.$$$ setN || Args.$$$ ruleN) -- Args.colon)) scan;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :|--
    (fn names => Scan.peek (fn context => Scan.succeed (names |> map (fn name =>
      (case get (Context.proof_of context) name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name))))));

fun rule get_type get_pred =
  named_rule typeN (Args.type_name {proper = false, strict = false}) get_type ||
  named_rule predN (Args.const {proper = false, strict = false}) get_pred ||
  named_rule setN (Args.const {proper = false, strict = false}) get_pred ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thms;

fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

val cases_rule = rule Induct.lookup_casesT Induct.lookup_casesP >> single_rule;
val induct_rule = rule Induct.lookup_inductT Induct.lookup_inductP;

in

val case_synt = Scan.lift (Args.mode Induct.no_simpN) --
      (Parse.and_list' (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule)

end

fun case_analysis_phityp (ctxt,sequent) =
      Phi_Apply.apply1 [@{thm' "_cases_app_rule_"}] ctxt sequent

fun case_analysis_system (no_simp, (insts, opt_rule)) (ctxt,sequent) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val sequent' = (sequent RS' (ctxt, #transformation_rule mode))
                  |> Goal.protect 1
   in case Seq.pull (Induct.cases_tac ctxt (not no_simp) insts opt_rule [] 1 sequent')
        of SOME (ret, _) => ret
                         |> Conv.fconv_rule (Phi_Conv.hhf_conv
                              (fn ctxt =>
                                Simplifier.asm_rewrite (Simplifier.clear_simpset ctxt) then_conv
                                Phi_Conv.hhf_conv
                                  (fn _ => HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' Premise_def[where mode=default, folded atomize_eq, symmetric]}))
                                  (fn _ => HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' Argument_def[symmetric]})) ctxt)
                              (fn _ => Conv.rewr_conv @{thm' Pure.prop_def})
                              ctxt)
         | NONE => error "Fail to apply the case analysis"
  end

fun case_analysis (no_simp, (insts, opt_rule)) stat =
  case insts
    of [[]] => case_analysis_phityp stat
     | [] => case_analysis_phityp stat
     | [[NONE]] => case_analysis_phityp stat
     | _ => case_analysis_system (no_simp, (insts, opt_rule)) stat

fun case_analysis_processor (oprs,(ctxt,sequent)) =
  Args.$$$ "case_analysis" |-- Scan.pass (Context.Proof ctxt) case_synt >> (fn data => fn _ =>
    (oprs, (ctxt, case_analysis data (ctxt,sequent))))

end