signature NU_PROCESSOR = sig
  type binding = Binding.binding
  exception Bypass of thm option
  exception ProcessTerminated of thm * Token.T list
  exception ProcessFail of binding * thm * exn
  exception Process_State_Call of Token.T list * thm * (Proof.state -> Proof.state)
  exception Process_State_Call' of thm * (Proof.state -> Proof.state)
  val Process_State_Call'' : thm -> (thm -> Proof.context -> thm * Proof.context) -> exn
  type proc = (Proof.context -> thm -> (unit -> thm) parser)
  val define : binding -> int (*precedence*) -> term (*pattern*) -> proc -> local_theory -> local_theory
  (* val get : Proof.context -> string -> T option *)
  val defined : Context.generic -> string -> bool
  val get_attr : Context.generic -> xstring * Position.T -> attribute parser
  val enable : string -> Context.generic -> Context.generic
  val disable : string -> Context.generic -> Context.generic
  val list : Context.generic -> (binding * term (*pattern*)) list
  val process : Proof.context -> thm -> thm parser
  val process_no_input : Proof.context -> thm -> thm
  val process_attr : attribute parser

  (* be activated only when auto level >= 1 *)
  val almost_safe : (Proof.context -> 'a) -> Proof.context -> 'a
  (* be activated only when auto level >= 2 *)
  val not_safe : (Proof.context -> 'a) -> Proof.context -> 'a
  val apply_attr : Proof.context -> thm -> attribute -> thm
  val parse_auto_level : proc -> proc

  val setup : binding -> int (*precedence*) -> term (*pattern*) -> proc ->
        string (*comment*) -> local_theory -> local_theory
  val setup' : binding -> int (*precedence*) ->
        (string (*pattern*) * (binding * string option * mixfix) list) -> proc ->
        string (*comment*) -> local_theory -> local_theory
  val setup_cmd : (((((string * Position.T) * int (*precedence*)) * string (*pattern*))
        * (binding * string option * mixfix) list)
        * Input.source (* proc source*)) * string (*comment*) -> local_theory -> local_theory
end
structure NuProcessor : NU_PROCESSOR = struct
open Thm NuBasics
exception Bypass of thm option
type binding = Binding.binding
exception ProcessTerminated of thm * Token.T list
exception ProcessFail of binding * thm * exn
type proc = Proof.context -> thm -> (unit -> thm) parser
exception Process_State_Call of Token.T list * thm * (Proof.state -> Proof.state)
exception Process_State_Call' of thm * (Proof.state -> Proof.state)
fun Process_State_Call'' th f = Process_State_Call' (th, (fn stat =>
      Proof.map_context_result (f (Proof.the_fact stat)) stat
        |-> (Proof.set_facts o single)))


datatype processor = Processor of {
              binding : binding,
              precedence : int,
              pattern : term,
              enabled : bool,
              proc : proc
            }
fun precedence_of (Processor{precedence,...}) = precedence
fun proc_of (Processor{proc,...}) = proc
val proc_ord = int_ord o apply2 precedence_of
fun mk_processor (binding, precedence, pat, proc) =
      Processor {binding = binding, precedence = precedence, pattern = pat, enabled = true, proc = proc}
fun set_enabled v (Processor {binding, precedence, pattern, enabled, proc}) =
      Processor {binding = binding, precedence = precedence, pattern = pattern, enabled = v, proc = proc}

structure Data = Generic_Data
(
  type T = processor Name_Space.table; (* key : the constant name, value: the definition *)
  val empty: T = Name_Space.empty_table "\<nu>processor";
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

val ops_processor = {get_data = Data.get, put_data = Data.put}
fun define binding precedence pat proc =
      Entity.define ops_processor binding (mk_processor (binding, precedence, pat, proc)) #> #2
val list = Data.get #> Name_Space.dest_table
      #> map (fn (name, Processor {binding,pattern, ...}) => (Binding.name name,pattern))
val get = Data.get #> Name_Space.get
fun wrap_attr proc =
  Parse.args >> (fn toks =>
    Thm.rule_attribute [] (fn ctx => fn th =>
      fst ((proc (Context.proof_of ctx) th --| Scan.catch Parse.eof) toks) ()))
val wrap_attr = wrap_attr : (Proof.context -> thm -> (unit -> thm) parser) -> attribute parser
fun defined ctx name =
  let
    val tab = Data.get ctx
    val name = Name_Space.intern (Name_Space.space_of_table tab) name
  in
    Name_Space.defined tab name
  end
fun get_attr ctx name =
  wrap_attr
    (proc_of (Name_Space.check ctx (Data.get ctx) name |> snd))

fun enable name =
      Data.map (Name_Space.map_table_entry name (set_enabled true))
fun disable name =
      Data.map (Name_Space.map_table_entry name (set_enabled false))

exception Processed of (thm * Token.T list)
fun eof_wrap parse [] = (fst (parse [Token.eof]), [])
  | eof_wrap parse toks = parse toks
fun process_impl ctx procs (th,toks) limit =
      let
        val focus = prop_of th |> dest_SpecTop |> #1
        val th = fold (fn (_, Processor {binding, pattern, enabled, proc,...}) => fn th =>
          if not enabled then th
          else if can (Pattern.unify ctx (pattern,focus)) Envir.init
          then let
            val _ = if limit > 100 then error "too deep process" else ();
            val (execute,toks) =
              eof_wrap (proc (Context.proof_of ctx) th || (fn _ => raise Bypass NONE)) toks
            val _ = tracing ("process: " ^ Binding.print binding)
            in
            raise Processed (execute(), toks)
              handle Process_State_Call' (meta,f) =>
                        raise Process_State_Call (toks,meta,f)
            end handle Bypass NONE => th
              | Bypass (SOME th') => th'
              | Processed th_toks => raise Processed th_toks
              | ProcessTerminated th_toks => raise ProcessTerminated th_toks
              | Process_State_Call arg => raise Process_State_Call arg
              | ex => (@{print} th; @{print} binding; Exn.reraise (@{print} ex))
            (* | ex => Exn.reraise (ProcessFail (binding,th,ex)) *)
          else th
        ) procs th
      in (th,toks)
      end
      handle Processed th_toks => process_impl ctx procs th_toks (limit + 1)
        | ProcessTerminated th_toks => th_toks
        | NDBG th => (th,[Token.eof])
fun process ctx th toks =
  Runtime.exn_trace (fn _ =>
  process_impl (Context.Proof ctx)
    (Data.get (Context.Proof ctx) |> Name_Space.dest_table |> sort (proc_ord o apply2 snd))
    (th,toks) 0)
val process_attr = wrap_attr (fn ctx => fn th => process ctx th #> apfst K)
fun process_no_input ctx th = process ctx th [Token.eof] |> #1

fun setup binding precedence term proc (comment:string) =
  define binding precedence term proc
fun setup' binding precedence (term,fixes) proc (comment:string) lthy =
  let
    val (_, lthy') = Proof_Context.add_fixes_cmd fixes lthy
    val term = Syntax.read_prop lthy' term |> free_to_var
  in
    define binding precedence term proc lthy
  end

fun setup_cmd (((((binding,precedence),term),fixes),proc),comment) ctx =
  let
    val (_, ctx') = Proof_Context.add_fixes_cmd fixes ctx
    val term = Syntax.read_prop ctx' term |> free_to_var
  in
    ctx |> Context.proof_map (
      ML_Context.expression (Input.pos_of proc)
        (ML_Lex.read
          ("Theory.local_setup (NuProcessor.setup (" ^
          ML_Syntax.make_binding binding ^ ") (" ^ ML_Syntax.print_int precedence ^ ") ("
          ^ ML_Syntax.print_term term ^ ") (let open NuProcessor NuProcessors in ") @
          ML_Lex.read_source proc @
          ML_Lex.read (" end) " ^ ML_Syntax.print_string comment ^ ")"))
    )
  end

fun almost_safe f ctx = if AutoLevel.get ctx >= 1 then f ctx else raise Bypass NONE
fun not_safe f ctx = if AutoLevel.get ctx >= 2 then f ctx else raise Bypass NONE
fun parse_auto_level proc ctx th =
  NuParse.auto_level #-> (fn auto_level' => proc (AutoLevel.reduce auto_level' ctx) th)

fun apply_attr ctx th attr =
  attr (Context.Proof ctx, th) |> #2 |> the

(* fun processor_parser (ctx,tokens) =
val processor_attr = Scan.lift (Parse.named_position >> #1) --  *)
  
end
