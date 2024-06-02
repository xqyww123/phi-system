(* FILE: library/system/toplevel.ML
   AUTHOR: Qiyuan Xu

   Definition of Isar commands for IDE-CP.
*)

signature PHI_TOPLEVEL = sig

  include PHI_TOPLEVEL

  datatype cond_kind = Premise | Assumption
  datatype ('a,'b) modifier = Mod_by_Rule of 'a | Mod_by_Attr of 'b

  structure Finishing_Modifier_Hooks : HOOKS
  structure Finishing_Construction_Hooks : HOOKS
  structure Begining_Procedures : HOOKS
  structure Infer_Requirements : HOOKS

  (*val is_interactive : bool Config.T
  exception Schematic*)

  val name_of_the_building_procedure : Proof.context -> binding option
  val free_fixed_outside : Proof.context -> Name.context option

  val begin_proc_cmd : bool (*whether to define a new constant*)
        -> Attrib.binding (*name*)
        -> xstring (*input*)
        -> xstring (*output*)
        -> xstring option (*throws*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
        -> (Facts.ref * Token.src list, Token.src list) modifier list
        -> bool -> local_theory -> Proof.state

(*
  val begin_rec_proc_cmd : bool (*whether to define a new constant*)
        -> Attrib.binding
        -> xstring (*input*)
        -> xstring (*output*)
        -> xstring option (*throws*)
        -> ((binding * string option * mixfix) list * (*variants*)
            (binding * string option * mixfix) list   (*for fixes*))
        -> (xstring * Position.T) list (*includes*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
        -> bool -> local_theory -> Proof.state *)

  val statement_clean_values : bool Config.T (*controls whether the statement command \<^bold>;
        cleans all values at its beginning.*)

  val prove_prem : Phi_CP_IDE.eval_cfg * bool -> (Proof.state -> Proof.state) -> Proof.state -> thm list * Proof.state

  (*val export_LLVM : theory -> theory *)

end

structure Phi_Toplevel : PHI_TOPLEVEL = struct

open Phi_Toplevel

val v_proc_var = ("\<p>\<r>\<o>\<c>",0)


(* Library *)

fun print_results int = Proof_Display.print_results
                            {interactive=int, pos=Position.thread_data (), proof_state=false}

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt'
  in ((vars, xs), ctxt'') end

datatype cond_kind = Premise | Assumption



(** Programming Block **)

(** Statement **)

fun prove_prem (cfg,int) after_qed'' stat =
  let
    val sequent = Phi_Envir.the_state_sequent stat
    fun after_qed sequent stat =
          stat |> Phi_Envir.set_state_sequent sequent
               |> Phi_CP_IDE.call_of_state_sequent (fn s => s
                    |> apfst (Config.put Phi_Reasoner.auto_level 1)
                    |> Phi_CP_IDE.Post_App.invoke (Context.Proof (fst s)) cfg
                    |> apfst ( Config.restore Phi_Reasoner.auto_level (fst s) )
                  )
               |> after_qed''
  in stat
  |> Phi_Sys.obligation_proof (print_results int) Proof_Context.mode_schematic ""
        NONE after_qed [] [] sequent
  end
 (*let open Proof
    val sequent = Phi_Envir.the_state_sequent stat
    val goal = Thm.prop_of sequent
                |> Logic.dest_implies |> #1 (* |> dest_premise_tag |> mk_Trueprop *)
    fun after_qed (ctxt',[[th]]) stat =
      let
        val [th] = Proof_Context.export ctxt' (context_of stat) [th]
        val original_auto_level = Config.get (Proof.context_of stat) Phi_Reasoner.auto_level
      in
        stat |> Proof.map_context_result
                  (Config.put Phi_Reasoner.auto_level 0
                    #> (fn ctxt => Phi_Processor.process_no_input (ctxt, th RS specthm))
                    #> apfst (Config.put Phi_Reasoner.auto_level original_auto_level)
                    #> swap)
             |-> Phi_Envir.set_state_sequent
      end
  in
    stat |> Phi_Sys.setup_proof (print_results int) Proof_Context.mode_schematic ""
              NONE after_qed [] [] [[(goal,[])]]
         |> apsnd (
              Proof.map_context (Proof_Context.set_mode Proof_Context.mode_default)
           #> Proof.refine (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (
                HEADGOAL (resolve_tac ctxt @{thms Premise_I})
              ))) #> Seq.the_result "should never fail"
            )
  end*)


(** Header of Procedure **)

datatype ('a,'b) modifier = Mod_by_Rule of 'a | Mod_by_Attr of 'b

structure Finishing_Modifier_Hooks = Hooks (type arg = unit
                                            type state = context_state)
structure Finishing_Construction_Hooks = Hooks (type arg = unit
                                                type state = context_state)
structure Begining_Procedures = Hooks (
  type arg = unit
  type state = {
    includes: string list,
    assms: (typ, term, thm list) Element.ctxt list,
    concls: (typ, term) Element.stmt,
    after_qed: thm list list -> Proof.context -> Proof.context,
    lthy: local_theory
  }
)

structure Infer_Requirements = Hooks (
  type arg = {
      arg: term,
      ret: term,
      throw: term,
      existing_requirements: ((binding * Token.src list) * (term * term list)) list
    }
  type state = {
    parse_ctxt: Proof.context,
    new_requirements: ((binding * Token.src list) * (term * term list)) list (*inferred premises / requirements*)
  }
)

val enable_infer_requirements = Attrib.setup_config_bool \<^binding>\<open>\<phi>infer_requirements\<close> (K false)

structure Procedure_Envir = Proof_Data (
  type T = { binding: binding,
             free_fixed_outside: Name.context } option
  val init = (K NONE)
)

val name_of_the_building_procedure = Option.map #binding o Procedure_Envir.get
val free_fixed_outside = Option.map #free_fixed_outside o Procedure_Envir.get

fun infer_requirements ctxt arg =
  if Config.get ctxt enable_infer_requirements
  then case Infer_Requirements.invoke (Context.Proof ctxt) arg {
                parse_ctxt = ctxt,
                new_requirements = []
              }
         of {new_requirements=[], ...} => (ctxt, #existing_requirements arg)
          | {new_requirements, parse_ctxt} => (
              Phi_Reasoner.warn_pretty (Context.Proof parse_ctxt) 1 (fn () => let open Pretty in
                  chunks ([block (text "Several comonly useful premises are inferred and added to the specification")] @
                    map (fn (_,(prem,_)) =>
                      item [Syntax.pretty_term parse_ctxt prem]) new_requirements @
                    [block (text "If they are too aggressive, you may disable this automation by \<open>declare [[\<phi>infer_requirements = false]]\<close>")])
                end) ;
              (parse_ctxt, #existing_requirements arg @ new_requirements))
  else (ctxt, #existing_requirements arg)

fun gen_begin_proc prep_term prep_prop prep_var prep_attr def_const
      binding arg ret throws rawfixes includes raw_defines raw_preconds action raw_modifiers
      int lthy =
  let
    val free_fixed_outside = Variable.names_of lthy

    val includes = includes |> map (Bundle.check lthy)
    val ((fixes,var_names), ctxt_parse) = lthy
                                       |> not (null includes) ? Bundle.includes includes
                                       |> prep_decls prep_var rawfixes
                                       |> apsnd (Proof_Context.set_mode Proof_Context.mode_schematic)
    val binding = binding |> apsnd (map (Attrib.check_src lthy))
    val ctxt_parse = Context.proof_map (Procedure_Syntax.set_proc_parse_mode
                        (Procedure_Syntax.HOL_Quantify, Procedure_Syntax.Lambda_Apps))
                        ctxt_parse
    val parse_term = prep_term ctxt_parse
    val parse_prop = prep_prop ctxt_parse

    fun apply_modifier (ctxt,sequent) = (ctxt,sequent)
         |> fold (fn Mod_by_Rule rule =>
                          Phi_Modifier.by_rule (singleton (Attrib.eval_thms ctxt) rule)
                 | Mod_by_Attr attr =>
                          fold (Phi_Modifier.apply_wrapped_attribute o prep_attr ctxt) attr
               ) raw_modifiers
         |> Finishing_Modifier_Hooks.invoke (Context.Proof ctxt) ()

    fun prep_attrterm prep ((b,attrs),(prop, pats)) =
          ((b, map (Attrib.check_src lthy) attrs), (prep prop, map parse_term pats))

    fun prep_precond (Premise, c) =
          prep_attrterm (parse_prop #>
                  (fn (Const (@{const_name Trueprop}, _) $ tm)
                        => \<^const>\<open>Trueprop\<close> $ (@{term Normal_Premise} $ tm)
                    | _ => error "Premise must be atomic HOL assertion (meaning you cannot use \
                                 \meta connectivities like \<open>\<Longrightarrow>\<close> or \<open>\<And>\<close>). You may want to \
                                 \use keyword \<open>assume\<close> for introducing advanced arbitrary \
                                 \antecedents.")) c
      | prep_precond (Assumption, c) = prep_attrterm parse_prop c
    val preconds0 = map prep_precond raw_preconds

    val arg = Procedure_Syntax.translate_arg (parse_term arg)
    val ret = Procedure_Syntax.translate_ret (parse_term ret)
    val v_proc = Var (v_proc_var, dummyT)
    val throws = (case throws
                    of SOME thr => parse_term thr
                     | NONE => Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, dummyT))
    val goal0 = Const (@{const_name \<phi>Procedure}, dummyT) $ v_proc $ arg $ ret $ throws
    val goal0 = case action of NONE => HOLogic.Trueprop $ goal0
                   | SOME A => HOLogic.Trueprop $ (\<^Const>\<open>Action_Tag\<close> $ goal0 $ parse_term A)

    val preconds0'1 = map (fn (_,(P,_)) => P) preconds0
    val (preconds0'1, ctxt_parse) = fold_map Phi_Typeclass.complete preconds0'1 ctxt_parse
    val (arg::ret::throws::goal0::preconds0'1) =
            Syntax.check_terms ctxt_parse (arg::ret::throws::goal0::preconds0'1)
    val preconds0 = map2 (fn (a,(_,b)) => fn c => (a,(c,b))) preconds0 preconds0'1

    val (ctxt_parse, preconds) = infer_requirements ctxt_parse
                        {arg=arg, ret=ret, throw=throws, existing_requirements=preconds0}
    val goal = goal0
            |> fold_rev (fn (_,(P,_)) => fn X => \<^const>\<open>Pure.imp\<close> $ P $ X) preconds

    fun post_process' binding int lthy th =
      (lthy,th)
        |> Finishing_Construction_Hooks.invoke (Context.Proof lthy) ()
        |> Phi_Procedure.define def_const binding
        |> (fn (lthy, th) =>
              (Proof_Display.print_results {interactive = int,
                                            pos = Binding.pos_of (fst binding),
                                            proof_state = false} lthy
                (("\<phi>procedure", ""), [("", [th])]); lthy))

    val defines = map (prep_attrterm parse_prop) raw_defines
    val assms = [Element.Fixes fixes, Element.Defines defines]
    val concls = Element.Shows [(Binding.empty_atts,[(goal,[])])]
    fun after_qed [[th]] lthy = post_process' binding int lthy th

    val {includes, assms, concls, after_qed, lthy} =
          Begining_Procedures.invoke (Context.Proof lthy) () {
              includes=includes, assms=assms, concls=concls, after_qed=after_qed, lthy=lthy
            }
  in
    lthy |> Specification.schematic_theorem false "" NONE after_qed Binding.empty_atts
              includes assms concls int
         |> Proof.map_context (fn ctxt =>
              ctxt |> Context_Position.set_visible false
                   |> (fn ctxt => ctxt addsimprocs [Semantic_Type_Tools.unfold_typeof_simproc])
                   |> Context_Position.restore_visible ctxt
                   |> Phi_ID.set_construct (Binding.name_of (fst binding))
                   |> Context.proof_map (Named_Theorems.clear \<^named_theorems>\<open>\<phi>lemmata\<close>)
                   |> Procedure_Envir.put (SOME {binding=fst binding, free_fixed_outside=free_fixed_outside})
                   |> PLPR_Statistics.setup_semantic_operation_recording
            )
         |> Proof.refine (Method.Basic (K (K (fn s => s
              |> Named_Premises.bind_sequent_assms (map (apsnd snd) preconds) 1
              |> apply_modifier
              |> Seq.single o Seq.Result))))
         |> Seq.the_result "should never fail #gn9[q3"
  end

val begin_proc =
      gen_begin_proc (K I) (K I) Proof_Context.cert_var (K I)
val begin_proc_cmd =
      gen_begin_proc Syntax.parse_term Syntax.parse_prop Proof_Context.read_var
                     Attrib.attribute_cmd



(** Statement **)

(*Whether to remove all values at the beginning of the command \<^bold>;*)
val statement_clean_values = Attrib.setup_config_bool \<^binding>\<open>\<phi>statement_clean_values\<close> (K true)

fun clean_values (ctxt,sequent) =
      if can Phi_Syntax.dest_CurrentConstruction (Thm.prop_of sequent)
         andalso Config.get ctxt statement_clean_values
      then snd (Generic_Variable_Access.extract_values (~1,true) (ctxt, sequent))
      else (ctxt, sequent)

(*
fun statement_line_cmd auto_lev = Phi_CP_IDE.eval_line

  Phi_Processor.powerful_process_p auto_lev (fn expr_id =>
                        Phi_Envir.map_state_sequent (fn (ctxt,sequent) =>
                            End_of_Line.invoke (Context.Proof ctxt) expr_id (ctxt,sequent)))
    >> (fn expr_id => fn process =>
              Phi_Envir.map_state_sequent (fn (ctxt,sequent) =>
                    Begin_of_Line.invoke (Context.Proof ctxt) expr_id (ctxt,sequent))
           #> process
     (*the return of the process doesn't mean the end of the construction because the construction
       can be interrupted and suspended by inserted proofs.*)
  )


fun statement_cmd_first_line auto_lev =
  statement_line_cmd auto_lev >> (fn f =>
       Proof.map_context (Config.put previous_statement_completes' false)
    #> f)

fun statement_cmd_tail auto_lev toks =
  (statement_line_cmd auto_lev >> (fn f => fn s =>
      if Phi_Envir.under_programming_environ (Proof.context_of s)
      then f s
      else if null toks orelse Token.is_eof (hd toks)
           then s
           else error "The construction has ended but a statement is given")) toks
*)

val _ = Theory.setup (Context.theory_map (

   Phi_Opr_Stack.Begin_of_Statement.add 50 (K (fn opr_ctxt =>
      if Phi_Opr_Stack.is_the_first_statement (#1 (#1 opr_ctxt))
      then opr_ctxt
      else apsnd clean_values opr_ctxt))

#> Phi_Opr_Stack.End_of_Line.add 100
      (K (apsnd (apfst Phi_Envir.freeze_dynamic_lemmas)))

))


(*val is_interactive = Config.declare_bool ("\<phi>Sys.interactive", \<^here>) (K true)
exception Schematic*)

(* fun export_LLVM thy =
  let
    fun eval code = ML_Context.exec (fn () =>
                      ML_Context.eval_source ML_Compiler.flags (Input.string code))

    val base = Path.expand (Resources.master_directory thy)
    val path = File.full_path base (Path.basic (Context.theory_name thy ^ ".ll"))

    val codegen = eval ("NuCG.codegen NuCG_" ^ Context.theory_name thy ^ ".gen"
                    ^ "(" ^ ML_Syntax.print_path path ^ ")" )
    val _ = tracing("generating LLVM IR: " ^ Path.print path)
  in
    thy |> Context.theory_map (eval (NuCompilation.compile thy(* |> (fn s => (tracing s; s))*)))
        |> Context.theory_map codegen
  end *)



local open Scan Phi_Sys Parse

val is_props = Scan.repeat1 ($$$ "is" |-- prop);
val ppats = Scan.optional ($$$ "(" |-- !!! (is_props --| $$$ ")")) [];

val attrib = token liberal_name ::: !!! args;
val attribs = (\<^keyword>\<open>[\<close> -- \<^keyword>\<open>]\<close>) >> K [Attrib.internal Position.none (K (K (NONE,NONE)))]
           || ($$$ "[" |-- list attrib --| $$$ "]")
val opt_attribs = Scan.optional attribs [];
fun opt_thm_name s =
  Scan.optional
    ((Parse.binding -- opt_attribs || attribs >> pair Binding.empty) --| Parse.$$$ s)
    Binding.empty_atts;

val statement1 = Parse.and_list1 (opt_thm_name ":" -- Parse.propp);
val requires_statement = (\<^keyword>\<open>assumes\<close> || \<^keyword>\<open>requires\<close>) |-- Parse.!!! statement1;
val premises_statement = \<^keyword>\<open>premises\<close> |-- Parse.!!! statement1;
val precond_statements =
      Scan.repeat ((premises_statement >> map (pair Premise))
                || (requires_statement >> map (pair Assumption))) >> flat;
(* val requires_opt1 = Scan.option (\<^keyword>\<open>assumes\<close> |-- Parse.term); *)
val where_statement = Scan.optional (\<^keyword>\<open>where\<close> |-- Parse.!!! statement1) [];
val goal = Scan.option (\<^keyword>\<open>@tag\<close> |-- Parse.term)

val includes = Scan.optional Parse_Spec.includes []
val input  = \<^keyword>\<open>input\<close>  |-- Parse.term
val output = \<^keyword>\<open>output\<close> |-- Parse.term
val throws = Scan.option (\<^keyword>\<open>throws\<close> |-- Parse.term)

val rec_vars = \<^keyword>\<open>var\<close> |-- !!! vars;

val def_const_flag =
  Scan.optional ((\<^keyword>\<open>(\<close> |-- Phi_Parse.$$$ "nodef" --| \<^keyword>\<open>)\<close>) >> (K false)) true

val modifier  = (Parse.attribs >> Mod_by_Attr) || (Parse.thm >> Mod_by_Rule)
val modifiers = repeat (\<^keyword>\<open>is\<close> |-- and_list modifier) >> flat

(*
fun phi_proof step_in prf tr =
  let (*val pos = Toplevel.pos_of tr*)
      (*val doc_id = case Position.id_of (Toplevel.pos_of tr)
                     of SOME id => @{print} id
                      | _ => Exn.error "internal bug #vcj4i[10th;ji"*)
   in Toplevel.proof' (fn int => fn stat =>
        stat |> Proof.map_context step_in (*(fn ctxt =>
                  let val ctxt' = step_in ctxt
                   in Phi_Cache_DB.check_cache doc_id ctxt';
                      ctxt'
                  end)*)
             |> prf int ) tr end *)

in

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((def_const_flag -- Parse_Spec.opt_thm_name ":"
      -- includes
      -- precond_statements
      -- input
      -- precond_statements
      -- output
      -- throws
      -- goal
      -- where_statement
      -- Parse.for_fixes
      -- modifiers) >>
      (fn (((((((((((def_const,b),includes),prec1),arg),prec2),ret),throws),G),defs),fixes),mods) =>
        begin_proc_cmd def_const b arg ret throws fixes includes defs (prec1 @ prec2) G mods))

(*
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close>
    "begin a recursive procedure construction"
    ((def_const_flag -- Parse_Spec.opt_thm_name ":"
      -- includes
      -- precond_statements
      -- input
      -- rec_vars
      -- precond_statements
      -- output
      -- throws
      -- goal
      -- where_statement
      -- Parse.for_fixes
     ) >> (
     fn (((((((((((def_const,b),includes),prec1),arg),vars),prec2),ret),throws),G),defs),fixes) =>
        begin_rec_proc_cmd def_const b arg ret throws (vars,fixes) includes defs (prec1 @ prec2) G))
*)

fun is_eof_toks [] = true
  | is_eof_toks (h :: _) = Token.is_eof h

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>;;\<close> "Leading a statement of \<phi> programs"
    (fn toks => Toplevel.proof (Phi_CP_IDE.eval_line (Symtab.empty, SOME 3, SOME 3) (toks @ [Token.eof]))
             |> rpair (if is_eof_toks toks then [Token.eof] else []))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<semicolon>\<close> "Leading a statement of \<phi> programs"
    (fn toks => Toplevel.proof (Phi_CP_IDE.eval_line (Symtab.empty, SOME 3, SOME 3) (toks @ [Token.eof]))
             |> rpair (if is_eof_toks toks then [Token.eof] else []))


fun statement_cmd_no_auto toks = (Phi_CP_IDE.eval_line (Symtab.empty, SOME 3, SOME 1) (toks @ [Token.eof]),
                                  if is_eof_toks toks then [Token.eof] else [])

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "Begin a \<phi> program block"
   (((  optional (\<^keyword>\<open>for\<close> |-- list1 Parse.binding) []
     -- optional (\<^keyword>\<open>premises\<close> |--
            and_list ((binding -- opt_attribs || attribs >> pair Binding.empty) -- ppats)) []
      >> begin_block_cmd)
   -- statement_cmd_no_auto)
   >> (fn (blk,prcs) => Toplevel.proof' (fn int => @{print} o prcs o blk int o Proof.map_context Phi_ID.next)))

datatype end_blk_action = Enter_Proof_Mode | Transparent_Proof of (Proof.state -> Proof.state)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "End a \<phi> program block"
    (option (\<^keyword>\<open>for\<close> |-- term) --
     option (\<^keyword>\<open>subj\<close> |-- term) -- (
        \<^keyword>\<open>certified\<close> >> K Enter_Proof_Mode ||
        statement_cmd_no_auto >> Transparent_Proof
  ) >> (fn (spec_subj,act) => Toplevel.proof' (fn int => fn stat =>
  let val spec = case spec_subj of (SOME _, SOME _) =>
                                      Exn.error "keyword 'for' and 'subj' should not be given simutaneously."
                                 | (SOME s, _) => SOME (Spec_Annot s)
                                 | (_, SOME s) => SOME (Subj_Annot s)
                                 | _ => NONE
   in stat
   |> Proof.map_context Phi_ID.next
   |> (case act
         of Enter_Proof_Mode => end_block_cmd spec int
          | Transparent_Proof tail_statement => end_block_auto_proof_cmd spec int
                                             #> (fn s => s
                                             |> Proof.map_context Phi_ID.next
                                             |> Phi_Envir.under_programming_environ (Proof.context_of s) ? tail_statement))
  end)))
(*
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>.\<close> "End a \<phi> program block using default tactic"
    (((option (\<^keyword>\<open>for\<close> |-- term) >> (fn cast => fn int => fn stat =>
       stat
    |> end_block_auto_proof_cmd cast int ))
   -- statement_cmd_tail (3,1))
   >> (fn (blk,tail_statement) => Toplevel.proof' (fn int =>
        tail_statement o Proof.map_context Phi_ID.next o blk int o Proof.map_context Phi_ID.next)))
*)
(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>interface\<close> "declare \<phi>interface"
      (Parse.binding --| $$$ "=" -- Parse.const -- option ($$$ ":" |-- Parse.typ --| $$$ "\<longmapsto>" -- Parse.typ)
        >> (Toplevel.theory o Phi_Procedure.add_interface_command))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>export_llvm\<close> "export LLVM target"
      (Scan.succeed (Toplevel.theory (Phi_Toplevel.export_LLVM))) *)

end

end
