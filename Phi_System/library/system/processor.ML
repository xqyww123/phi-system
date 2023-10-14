(* FILE: library/system/processor.ML
   AUTHOR: Qiyuan Xu

   Processor of IDE-CP. Processor is the core unit implementing the constructs in the programming
   of IDE-CP.
*)

signature PHI_CP_IDE = sig

include PHI_CP_IDE

(*** Syntax Processors ***)


exception Bypass
exception Terminate_Process of context_state * ((Proof.state -> Proof.state) (*continue*) -> Proof.state -> Proof.state) option
exception ProcessFail of binding * context_state * exn
exception Process_State_Call  of context_state * (Proof.state -> Proof.state)
exception Process_State_Call' of Token.T list * context_state * (Proof.state -> Proof.state)
type proc = (context_state -> (expr_id -> context_state) parser)

val trace : bool Config.T

type processor = {
    name : string,
    pos : Position.T,
    priorirty : int, (*the priority when the processor will be invoked*)
    precedence : int, (*the processor will not be applied until all pending operations in the
                        operator stack and of a higher precedence are processed.*)
    pattern : term list, (*applied only when match the pattern*)
    proc : proc
  }

val add_processor : string list * processor -> theory -> theory
val apply_processors : theory -> Token.T list
                    -> int -> Phi_CP_IDE.expr_id -> context_state
                    -> (context_state * Token.T list) option
val list : theory -> processor Ord_List.T Symtab.table

(*
val internal_process : context_state -> context_state parser
val simple_process   : context_state -> context_state parser
val powerful_process : (Proof.state -> Proof.state) (*continue*)
                    -> Token.T list -> Proof.state -> Proof.state
val powerful_process_p : int (*auto-level*) * int (*auto-level when no user input*)
                     -> (Proof.state -> Proof.state) (*continue*)
                     -> (Proof.state -> Proof.state) parser
                    (*if the input is empty, then powerful_process_p_inert does nothing*)
val process_by_input : int (*auto-level*) option -> Token.T list -> context_state -> context_state
val process_no_input : int (*auto-level*) option -> context_state -> context_state
val process_all_antecedents : int (*auto-level*) option -> context_state -> context_state
val process_attr : attribute parser
*)

(* be activated only when auto level >= 1 *)
val almost_safe : proc -> proc
(* be activated only when auto level >= 2 *)
val not_safe : proc -> proc
val parse_auto_level : proc -> proc

val setup_cmd : (((((string * Position.T) * int (*precedence*)) * string list)
      * (binding * string option * mixfix) list)
      * Input.source (* proc source*)) * string (*comment*) -> local_theory -> local_theory

end

structure Phi_CP_IDE : PHI_CP_IDE = struct
open Phi_CP_IDE

(*** Syntax Processors ***)

exception Bypass

exception Terminate_Process  of context_state * ((Proof.state -> Proof.state) -> Proof.state -> Proof.state) option
exception Terminate_Process' of Token.T list * context_state * ((Proof.state -> Proof.state) -> Proof.state -> Proof.state) option
exception ProcessFail of binding * context_state * exn
exception Process_State_Call' of Token.T list * context_state * (Proof.state -> Proof.state)
exception Process_State_Call of context_state * (Proof.state -> Proof.state)

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_processing\<close> (K false);

type proc = context_state -> (expr_id -> context_state) parser

type processor = {
    name : string,
    pos : Position.T,
    priorirty : int, (*the priority when the processor will be invoked*)
    precedence : int, (*the processor will not be applied until all pending operations in the
                        operator stack and of a higher precedence are processed.*)
    pattern : term list, (*applied only when match the pattern*)
    proc : proc
  }

val proc_eq = (op =) o apply2 #name
fun proc_ord (a,b) = int_ord (#priorirty a, #priorirty b)

structure Processors = Theory_Data
(
  type T = processor Ord_List.T Symtab.table (*indexed by leading keywords*)
  val empty = Symtab.empty
  val merge = Symtab.merge (eq_list proc_eq)
)

val list = Processors.get

fun add_processor (keywords, proc) =
  let val keywords = if null keywords then [""] else keywords
   in Processors.map (fold (fn key => Symtab.map_default (key, []) (Ord_List.insert proc_ord proc)) keywords)
  end

fun apply_processors thy =
  let val processors = Processors.get thy
      fun apply toks =
        let val next = case toks of tok :: _ => Token.content_of tok | _ => ""
            val ps = case Symtab.lookup processors next
                       of SOME ps => ps
                        | NONE => (case Symtab.lookup processors ""
                                     of SOME ps => ps
                                      | NONE => [])
            fun invoke prec expr_id (ctxt,sequent) =
              let fun try_app p =
                    if prec < #precedence p andalso
                       exists (fn pat => PLPR_Pattern.matches (Proof_Context.theory_of ctxt) []
                                                              (pat, Thm.prop_of sequent))
                              (#pattern p)
                    then SOME (((#proc p (ctxt,sequent) || (fn _ => raise Bypass)) >> (fn f => f expr_id)) toks)
                         handle Bypass => NONE
                    else NONE
      
               in get_first try_app ps
              end
         in invoke
        end
   in apply
  end

(*

exception Processed of (context_state * Token.T list)

fun eof_wrap parse [] = (fst (parse [Token.eof]), [])
  | eof_wrap parse toks = parse toks

fun process_impl procs =
  let fun eval toks proc stat = ()
      fun eval toks candidate_procs stat = ()
      fun process stat [] _ = stat
        | process stat toks step_num =
        let val tok = hd toks
            
         in ()
        end
   in ()
  end

fun process_impl procs (stat,toks) step_num =
      let
        val stat' = fold (fn (_, Processor {binding, pattern, proc,...}) => fn (ctxt,sequent) =>
          if exists (fn pat =>
                matches (Proof_Context.theory_of ctxt) pat (Thm.prop_of sequent)
             ) pattern
          then let
            val _ = if step_num > 1000 then error "too deep process" else ();
            val (execute,toks) =
              eof_wrap (proc (ctxt,sequent) || (fn _ => raise Bypass NONE)) toks
            val _ = if Config.get ctxt trace
                    then tracing ("\<phi>process: " ^ Binding.print binding)
                    else ()
            in
            raise Processed (execute step_num, toks)
              handle Process_State_Call (meta,f) => raise Process_State_Call' (toks,meta,f)
                   | Terminate_Process (stat,f) => raise Terminate_Process' (toks,stat,f)
            end handle Bypass NONE => (ctxt,sequent)
              | Bypass (SOME stat') => stat'
              | Processed stat_toks => raise Processed stat_toks
              | Process_State_Call' arg => raise Process_State_Call' arg
          else (ctxt,sequent)) procs stat
      in (stat',toks)
      end
      handle Processed stat_toks => process_impl procs stat_toks (step_num + 1)
        | NDBG sequent => ((fst stat, sequent),[Token.eof])

fun internal_process (ctxt,sequent) toks =
  Runtime.exn_trace (fn _ =>
  process_impl
    (Data.get (Context.Proof ctxt) |> Name_Space.dest_table |> sort (proc_ord o apply2 snd))
    ((ctxt,sequent),toks) 0)

fun simple_process stat toks =
  internal_process stat toks
  handle Process_State_Call' (toks,stat,_) => raise Fail "state call is not supported in simple process"
       | Terminate_Process'  (toks,stat,NONE) => (stat,toks)
       | Terminate_Process'  (toks,stat,SOME _) => raise Fail "state call is not supported in simple process"

fun powerful_process continue toks stat =
  let
    val sequent = Phi_Envir.the_state_sequent stat
  in
    stat
      |> Proof.map_context_result (fn ctxt =>
            (internal_process (ctxt,sequent) --| Scan.catch Parse.eof) toks
              |> (fn ((ctxt,sequent),_) => (sequent,ctxt))
          )
      |-> Phi_Envir.set_state_sequent
      |> continue
    handle Process_State_Call' (toks,(ctxt,sequent),f) =>
              powerful_process continue toks
                  (stat |> Proof.map_context (K ctxt)
                        |> Phi_Envir.set_state_sequent sequent
                        |> f)
         | Terminate_Process' (toks,(ctxt,sequent), f) =>
              (Scan.catch Parse.eof toks;
               stat |> Proof.map_context (K ctxt)
                    |> Phi_Envir.set_state_sequent sequent
                    |> (case f of SOME f' => f' continue | _ => I))
  end


fun powerful_process_p_internal' lev continue toks s =
  if Phi_Envir.under_programming_environ (Proof.context_of s)
  then s |> Proof.map_context (Config.put Phi_Reasoner.auto_level lev)
         |> powerful_process continue (toks @ [Token.eof])
  else if Token.is_eof (hd toks)
       then s
       else error "Not in the \<phi> programming environment"

fun powerful_process_p (lev1,lev2) continue toks =
      (if Token.is_eof (hd toks)
       then (if lev2 < 0 then I else powerful_process_p_internal' lev2 continue toks)
       else powerful_process_p_internal' lev1 continue toks
      ,if Token.is_eof (hd toks) then [Token.eof] else [])


fun process_by_input lev tokens stat =
      let val stat' = case lev of SOME lv => apfst (Config.put Phi_Reasoner.auto_level lv) stat
                                | NONE => stat
       in simple_process stat' (tokens @ [Token.eof]) |> #1 end
fun process_no_input lev = process_by_input lev []

fun process_all_antecedents lev s =
  let val (ctxt',sequent') = process_no_input lev s
   in if #constr_is_ready (Phi_Working_Mode.mode1 (fst s)) (Thm.prop_of sequent')
      then (ctxt',sequent')
      else error (Pretty.string_of (
        let val ant = Phi_Help.leading_antecedent' sequent'
         in case ant
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ G) =>
                  Pretty.chunks [
                    Pretty.str "Fail to solve obligation:",
                    Syntax.pretty_term ctxt' G,
                    Pretty.str "You may need to prove its obligations manually using \<^keyword>\<open>certified\<close>."
                  ]
               | _ =>
                  Pretty.chunks [
                    Pretty.str "Fail to solve reasoner job:",
                    Syntax.pretty_term ctxt' ant,
                    Pretty.str "It usually means you are doing unexpected operation."
                  ]
        end))
  end

*)

val read_prop_pattern = Syntax.read_props o Proof_Context.set_mode Proof_Context.mode_pattern

fun setup_cmd (((((binding,precedence),raw_term),fixes),proc),comment) lthy =
  let
    val (_, lthy') = Proof_Context.add_fixes_cmd fixes lthy
    val prop = read_prop_pattern lthy' raw_term
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of proc)
        (ML_Lex.read
          ("Theory.local_setup (Phi_Processor.setup (" ^
          ML_Syntax.make_binding binding ^ ") (" ^ ML_Syntax.print_int precedence ^ ") ("
          ^ ML_Syntax.print_list ML_Syntax.print_term prop ^ ") (let open Phi_Processor in ") @
          ML_Lex.read_source proc @
          ML_Lex.read (" end) " ^ ML_Syntax.print_string comment ^ ")"))
    )
  end


fun almost_safe f (ctxt,sequent) =
      if Config.get ctxt Phi_Reasoner.auto_level >= 1 then f (ctxt,sequent) else raise Bypass

fun not_safe f (ctxt,sequent) =
      if Config.get ctxt Phi_Reasoner.auto_level >= 2 then f (ctxt,sequent) else raise Bypass

fun parse_auto_level (proc:proc) (ctxt,sequent) =
    proc (Phi_Reasoner.reduce_auto_level (Config.get ctxt Phi_Reasoner.auto_level) ctxt, sequent)


val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>processor\<close> "define \<phi>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword || Parse.string)
          -- Parse.nat -- (\<^keyword>\<open>(\<close> |-- Parse.enum "|" Parse.term --| \<^keyword>\<open>)\<close> )
          -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.embedded ""
        >> setup_cmd)

end
