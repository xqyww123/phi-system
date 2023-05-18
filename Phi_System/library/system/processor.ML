(* FILE: library/system/processor.ML
   AUTHOR: Qiyuan Xu

   Processor of IDE-CP. Processor is the core unit implementing the constructs in the programming
   of IDE-CP.
*)

signature PHI_PROCESSOR = sig

  type binding = Binding.binding
  type processing_id = int (*Unique id of each runtime processing in a statement*)

  exception Bypass of context_state option
  exception Terminate_Process of context_state * ((Proof.state -> Proof.state) (*continue*) -> Proof.state -> Proof.state) option
  exception ProcessFail of binding * context_state * exn
  exception Process_State_Call  of context_state * (Proof.state -> Proof.state)
  exception Process_State_Call' of Token.T list * context_state * (Proof.state -> Proof.state)
  type proc = (context_state -> (processing_id -> context_state) parser)

  val trace : bool Config.T

  datatype 'a pattern = Whole_Prop of 'a | Concl of 'a | Premise of 'a

  val define : binding -> int (*precedence*) -> term pattern list -> proc
            -> Context.generic -> Context.generic
  val define_lthy : binding -> int (*precedence*) -> term pattern list -> proc
            -> local_theory -> local_theory
  (* val get : Proof.context -> string -> T option *)
  val defined : Context.generic -> string -> bool
  val get_attr : Context.generic -> xstring * Position.T -> attribute parser
  val list : Context.generic -> (binding * term pattern list) list
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
  val process_attr : attribute parser

  (* be activated only when auto level >= 1 *)
  val almost_safe : proc -> proc
  (* be activated only when auto level >= 2 *)
  val not_safe : proc -> proc
  val apply_attr : attribute -> context_state -> context_state
  val parse_auto_level : proc -> proc

  val setup : binding -> int (*precedence*) -> term pattern list -> proc ->
        string (*comment*) -> local_theory -> local_theory
  val setup_global : binding -> int (*precedence*) -> term pattern list -> proc ->
        string (*comment*) -> theory -> theory
  val setup' : binding -> int (*precedence*) ->
        (string pattern list * (binding * string option * mixfix) list) -> proc ->
        string (*comment*) -> local_theory -> local_theory
  val setup_cmd : (((((string * Position.T) * int (*precedence*)) * string pattern list)
        * (binding * string option * mixfix) list)
        * Input.source (* proc source*)) * string (*comment*) -> local_theory -> local_theory

  val simplifier : proc
end

structure Phi_Processor : PHI_PROCESSOR = struct
open Thm Phi_Envir

exception Bypass of context_state option

type binding = Binding.binding
type processing_id = int

exception Terminate_Process  of context_state * ((Proof.state -> Proof.state) -> Proof.state -> Proof.state) option
exception Terminate_Process' of Token.T list * context_state * ((Proof.state -> Proof.state) -> Proof.state -> Proof.state) option
exception ProcessFail of binding * context_state * exn
exception Process_State_Call' of Token.T list * context_state * (Proof.state -> Proof.state)
exception Process_State_Call of context_state * (Proof.state -> Proof.state)

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_processing\<close> (K false);

type proc = context_state -> (processing_id -> context_state) parser

datatype 'a pattern = Whole_Prop of 'a | Concl of 'a | Premise of 'a

fun map_pattern f (Whole_Prop x) = Whole_Prop (f x)
  | map_pattern f (Concl x) = Concl (f x)
  | map_pattern f (Premise x) = Premise (f x)

fun pattern_burrow f pats =
  map (fn Whole_Prop x => x | Concl x => x | Premise x => x) pats
    |> f
    |> map2 (fn Whole_Prop _ => Whole_Prop | Concl _ => Concl | Premise _ => Premise) pats

fun pattern_print_ML (Whole_Prop x) = "Phi_Processor.Whole_Prop (" ^ ML_Syntax.print_term x ^ ")"
  | pattern_print_ML (Concl x) = "Phi_Processor.Concl (" ^ ML_Syntax.print_term x ^ ")"
  | pattern_print_ML (Premise x) = "Phi_Processor.Premise (" ^ ML_Syntax.print_term x ^ ")"


datatype processor = Processor of {
              binding : binding,
              precedence : int,
              pattern : term pattern list,
              proc : proc
            }

fun precedence_of (Processor{precedence,...}) = precedence
fun proc_of (Processor{proc,...}) = proc
fun proc_ord (a,b) = int_ord (precedence_of a, precedence_of b)

fun mk_processor (binding, precedence, pat, proc) =
      Processor {binding = binding, precedence = precedence, pattern = pat, proc = proc}


structure Data = Generic_Data
(
  type T = processor Name_Space.table
  val empty: T = Name_Space.empty_table "\<phi>processor"
  fun merge data : T = Name_Space.merge_tables data
);

val ops_processor = {get_data = Data.get, put_data = Data.put}

fun define binding precedence pat proc ctxt =
  let
    val x = mk_processor (binding, precedence, pat, proc)
    val (name, data') = Name_Space.define ctxt true (binding, x) (Data.get ctxt);
  in Data.put data' ctxt end;

fun define_lthy binding precedence pat proc =
  Local_Theory.declaration {syntax=false, pervasive=false} (fn m =>
      define binding precedence (map (map_pattern (Morphism.term m)) pat) proc)

fun define_global binding precedence pat proc thy =
  Context.theory_map (define binding precedence pat proc) thy

val list = Data.get #> Name_Space.dest_table
      #> map (fn (name, Processor {pattern, ...}) => (Binding.name name,pattern))

fun wrap_attr (proc:proc) : attribute parser =
  Parse.args >> (fn toks => fn (ctxt, thm) =>
      (proc (Context.proof_of ctxt, thm) --| Scan.catch Parse.eof) toks
              |> (fn (f,_) => f 0
                           |> apfst (SOME o Context.Proof)
                           |> apsnd SOME))


fun defined ctxt name =
  let
    val tab = Data.get ctxt
    val name = Name_Space.intern (Name_Space.space_of_table tab) name
  in
    Name_Space.defined tab name
  end

fun get_attr ctxt name =
  wrap_attr
    (proc_of (Name_Space.check ctxt (Data.get ctxt) name |> snd))

fun matches thy (Whole_Prop pat) X = Pattern.matches thy (pat,X)
  | matches thy (Premise pat) (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ X $ _)
      = PLPR_Pattern.matches thy (pat, Logic.strip_assums_concl X)
  | matches thy (Premise pat) X = PLPR_Pattern.matches thy (pat,X)
  | matches thy (Concl pat) X = PLPR_Pattern.matches thy (pat, Logic.strip_assums_concl X)

exception Processed of (context_state * Token.T list)

fun eof_wrap parse [] = (fst (parse [Token.eof]), [])
  | eof_wrap parse toks = parse toks

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
    val sequent = the_state_sequent stat
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

val _ = Phi_Envir.under_programming_environ

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


val process_attr = wrap_attr (fn stat => simple_process stat #> apfst K)
fun process_by_input lev tokens stat =
      let val stat' = case lev of SOME lv => apfst (Config.put Phi_Reasoner.auto_level lv) stat
                                | NONE => stat
       in simple_process stat' (tokens @ [Token.eof]) |> #1 end
fun process_no_input lev = process_by_input lev []



val read_prop_pattern = Syntax.read_props o Proof_Context.set_mode Proof_Context.mode_pattern

fun setup binding precedence term proc (comment:string) =
  define_lthy binding precedence term proc

fun setup_global binding precedence term proc (comment:string) =
  define_global binding precedence term proc

fun setup' binding precedence (raw_term,fixes) proc (comment:string) lthy =
  let
    val (_, lthy') = Proof_Context.add_fixes_cmd fixes lthy
    val prop = pattern_burrow (read_prop_pattern lthy') raw_term
  in
    define_lthy binding precedence prop proc lthy
  end

fun setup_cmd (((((binding,precedence),raw_term),fixes),proc),comment) lthy =
  let
    val (_, lthy') = Proof_Context.add_fixes_cmd fixes lthy
    val prop = pattern_burrow (read_prop_pattern lthy') raw_term
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of proc)
        (ML_Lex.read
          ("Theory.local_setup (Phi_Processor.setup (" ^
          ML_Syntax.make_binding binding ^ ") (" ^ ML_Syntax.print_int precedence ^ ") ("
          ^ ML_Syntax.print_list pattern_print_ML prop ^ ") (let open Phi_Processor in ") @
          ML_Lex.read_source proc @
          ML_Lex.read (" end) " ^ ML_Syntax.print_string comment ^ ")"))
    )
  end


fun almost_safe f (ctxt,sequent) =
      if Config.get ctxt Phi_Reasoner.auto_level >= 1 then f (ctxt,sequent) else raise Bypass NONE

fun not_safe f (ctxt,sequent) =
      if Config.get ctxt Phi_Reasoner.auto_level >= 2 then f (ctxt,sequent) else raise Bypass NONE

fun parse_auto_level (proc:proc) (ctxt,sequent) =
    proc (Phi_Reasoner.reduce_auto_level (Config.get ctxt Phi_Reasoner.auto_level) ctxt, sequent)

fun apply_attr (attr:attribute) (ctxt, sequent) =
  attr (Context.Proof ctxt, sequent)
    |> apfst (Context.proof_of o the)
    |> apsnd the

fun simplifier (ctxt, sequent) = Scan.succeed (fn _ =>
  let
    val lev = Config.get ctxt Phi_Reasoner.auto_level
    val sctxt =
      if lev >= 2
      then Phi_Programming_Simp_SS.enhance ctxt
      else if lev >= 1
      then Phi_Programming_Safe_Simp_SS.equip ctxt
      else raise Bypass (SOME (ctxt, sequent))
    val sequent' = Simplifier.full_simplify sctxt sequent
  in raise Bypass (SOME (ctxt, sequent'))
  end)


val pattern_keyword = (\<^keyword>\<open>premises\<close> >> K Premise)
                   || (\<^keyword>\<open>conclusion\<close> >> K Concl)
                   || (Scan.succeed Whole_Prop)
val pattern = (pattern_keyword -- Parse.term) >> (fn (f,x) => f x)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>processor\<close> "define \<phi>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword || Parse.string)
          -- Parse.nat -- (\<^keyword>\<open>(\<close> |-- Parse.enum "|" pattern --| \<^keyword>\<open>)\<close> )
          -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.embedded ""
        >> setup_cmd)

end
