signature NU_PROCESSOR = sig
  type binding = Binding.binding
  exception Bypass of context_state option
  exception ProcessTerminated of context_state * Token.T list
  exception ProcessFail of binding * context_state * exn
  exception Process_State_Call of Token.T list * context_state * (Proof.state -> Proof.state)
  exception Process_State_Call' of context_state * (Proof.state -> Proof.state)
  type proc = (context_state -> (unit -> context_state) parser)

  val trace : bool Config.T

  val define : binding -> int (*precedence*) -> term (*pattern*) list -> proc -> local_theory -> local_theory
  (* val get : Proof.context -> string -> T option *)
  val defined : Context.generic -> string -> bool
  val get_attr : Context.generic -> xstring * Position.T -> attribute parser
  val list : Context.generic -> (binding * term (*pattern*) list) list
  val internal_process : context_state -> context_state parser
  val simple_process   : context_state -> context_state parser
  val powerful_process : Token.T list -> Proof.state -> Proof.state
  val process_by_input : Token.T list -> context_state -> context_state
  val process_no_input : context_state -> context_state
  val process_attr : attribute parser

  (* be activated only when auto level >= 1 *)
  val almost_safe : proc -> proc
  (* be activated only when auto level >= 2 *)
  val not_safe : proc -> proc
  val apply_attr : attribute -> context_state -> context_state
  val parse_auto_level : proc -> proc

  val setup : binding -> int (*precedence*) -> term (*pattern*) list -> proc ->
        string (*comment*) -> local_theory -> local_theory
  val setup' : binding -> int (*precedence*) ->
        (string (*pattern*) list * (binding * string option * mixfix) list) -> proc ->
        string (*comment*) -> local_theory -> local_theory
  val setup_cmd : (((((string * Position.T) * int (*precedence*)) * string (*pattern*) list)
        * (binding * string option * mixfix) list)
        * Input.source (* proc source*)) * string (*comment*) -> local_theory -> local_theory
end

structure NuProcessor : NU_PROCESSOR = struct
open Thm NuBasics

exception Bypass of context_state option
type binding = Binding.binding
exception ProcessTerminated of context_state * Token.T list
exception ProcessFail of binding * context_state * exn
exception Process_State_Call of Token.T list * context_state * (Proof.state -> Proof.state)
exception Process_State_Call' of context_state * (Proof.state -> Proof.state)

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_processing\<close> (K false);

type proc = context_state -> (unit -> context_state) parser

datatype processor = Processor of {
              binding : binding,
              precedence : int,
              pattern : term list,
              proc : proc
            }

fun precedence_of (Processor{precedence,...}) = precedence
fun proc_of (Processor{proc,...}) = proc
fun proc_ord (a,b) = int_ord (precedence_of a, precedence_of b)

fun mk_processor (binding, precedence, pat, proc) =
      Processor {binding = binding, precedence = precedence, pattern = pat, proc = proc}


structure Data = Generic_Data
(
  type T = processor Name_Space.table;
  val empty: T = Name_Space.empty_table "\<phi>processor";
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

val ops_processor = {get_data = Data.get, put_data = Data.put}

fun define binding precedence pat proc =
      Entity.define ops_processor binding (mk_processor (binding, precedence, pat, proc)) #> #2

val list = Data.get #> Name_Space.dest_table
      #> map (fn (name, Processor {binding,pattern, ...}) => (Binding.name name,pattern))

val get = Data.get #> Name_Space.get

fun wrap_attr (proc:proc) : attribute parser =
  Parse.args >> (fn toks => fn (ctxt, thm) =>
      (proc (Context.proof_of ctxt, thm) --| Scan.catch Parse.eof) toks
              |> fst |> (fn f => f () |> apfst (SOME o Context.Proof) |> apsnd SOME))


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


exception Processed of (context_state * Token.T list)

fun eof_wrap parse [] = (fst (parse [Token.eof]), [])
  | eof_wrap parse toks = parse toks

fun process_impl procs (stat,toks) limit =
      let
        val prop = Thm.prop_of (snd stat)
        val stat' = fold (fn (_, Processor {binding, pattern, proc,...}) => fn (ctxt,sequent) =>
          if exists (fn pat => Pattern.matches (Proof_Context.theory_of ctxt) (pat, prop)) pattern
          then let
            val _ = if limit > 100 then error "too deep process" else ();
            val (execute,toks) =
              eof_wrap (proc (ctxt,sequent) || (fn _ => raise Bypass NONE)) toks
            val _ = if Config.get ctxt trace
                    then tracing ("\<phi>process: " ^ Binding.print binding)
                    else ()
            in
            raise Processed (execute(), toks)
              handle Process_State_Call' (meta,f) =>
                  raise Process_State_Call (toks,meta,f)
            end handle Bypass NONE => (ctxt,sequent)
              | Bypass (SOME stat') => stat'
              | Processed stat_toks => raise Processed stat_toks
              | Process_State_Call arg => raise Process_State_Call arg
              | ProcessTerminated stat_toks => raise ProcessTerminated stat_toks
              | ex => (@{print} (ctxt,sequent); @{print} binding; Exn.reraise (@{print} ex))
            (* | ex => Exn.reraise (ProcessFail (binding,th,ex)) *)
          else (ctxt,sequent)) procs stat
      in (stat',toks)
      end
      handle Processed stat_toks => process_impl procs stat_toks (limit + 1)
        | ProcessTerminated stat_toks => stat_toks
        | NDBG sequent => ((fst stat, sequent),[Token.eof])

fun internal_process (ctxt,sequent) toks =
  Runtime.exn_trace (fn _ =>
  process_impl
    (Data.get (Context.Proof ctxt) |> Name_Space.dest_table |> sort (proc_ord o apply2 snd))
    ((ctxt,sequent),toks) 0)

fun simple_process stat toks =
  internal_process stat toks handle Process_State_Call (toks,stat,f) => (stat,toks)

fun powerful_process toks stat =
  let
    val sequent = the_nu_fact stat
  in
    stat
      |> Proof.map_context_result (fn ctxt =>
            (internal_process (ctxt,sequent) --| Scan.catch Parse.eof) toks
              |> (fn ((ctxt,sequent),_) => (sequent,ctxt))
          )
      |-> NuBasics.set_nu_fact
    handle Process_State_Call (toks,(ctxt,sequent),f) =>
      powerful_process toks (stat |> Proof.map_context (K ctxt)
                                  |> NuBasics.set_nu_fact sequent
                                  |> f)
  end

val process_attr = wrap_attr (fn stat => simple_process stat #> apfst K)
fun process_by_input tokens stat = simple_process stat (tokens @ [Token.eof]) |> #1
val process_no_input = process_by_input []



val read_prop_pattern = Syntax.read_props o Proof_Context.set_mode Proof_Context.mode_pattern

fun setup binding precedence term proc (comment:string) =
  define binding precedence term proc

fun setup' binding precedence (raw_term,fixes) proc (comment:string) lthy =
  let
    val (_, lthy') = Proof_Context.add_fixes_cmd fixes lthy
    val prop = read_prop_pattern lthy' raw_term
  in
    define binding precedence prop proc lthy
  end

fun setup_cmd (((((binding,precedence),raw_term),fixes),proc),comment) ctxt =
  let
    val (_, ctxt') = Proof_Context.add_fixes_cmd fixes ctxt
    val prop = read_prop_pattern ctxt' raw_term
  in
    ctxt |> Context.proof_map (
      ML_Context.expression (Input.pos_of proc)
        (ML_Lex.read
          ("Theory.local_setup (NuProcessor.setup (" ^
          ML_Syntax.make_binding binding ^ ") (" ^ ML_Syntax.print_int precedence ^ ") ("
          ^ ML_Syntax.print_list ML_Syntax.print_term prop ^ ") (let open NuProcessor NuProcessors in ") @
          ML_Lex.read_source proc @
          ML_Lex.read (" end) " ^ ML_Syntax.print_string comment ^ ")"))
    )
  end


fun almost_safe f (ctxt,sequent) =
      if Config.get ctxt Nu_Reasoner.auto_level >= 1 then f (ctxt,sequent) else raise Bypass NONE

fun not_safe f (ctxt,sequent) =
      if Config.get ctxt Nu_Reasoner.auto_level >= 2 then f (ctxt,sequent) else raise Bypass NONE

fun parse_auto_level (proc:proc) (ctxt,sequent) =
  NuParse.auto_level #-> (fn auto_level' =>
    proc (Nu_Reasoner.reduce_auto_level auto_level' ctxt, sequent))

fun apply_attr (attr:attribute) (ctxt, sequent) =
  attr (Context.Proof ctxt, sequent)
    |> apfst (Context.proof_of o the)
    |> apsnd the

(* fun processor_parser (ctxt,tokens) =
val processor_attr = Scan.lift (Parse.named_position >> #1) --  *)
  
end
