signature NU_PROCESSOR = sig
  type binding = Binding.binding
  exception Bypass
  exception ProcessTerminated of thm * Token.T list
  exception ProcessFail of binding * thm * exn
  type auto_level = int
  type proc = (auto_level -> Proof.context -> thm -> thm parser)
  val define : binding -> int (*precedence*) -> term (*pattern*) -> proc -> local_theory -> local_theory
  (* val get : Proof.context -> string -> T option *)
  val defined : Context.generic -> string -> bool
  val get_attr : Context.generic -> xstring * Position.T -> int (*auto level*) -> attribute parser
  val enable : string -> Context.generic -> Context.generic
  val disable : string -> Context.generic -> Context.generic
  val list : Context.generic -> (binding * term (*pattern*)) list
  val process : auto_level -> Proof.context -> thm -> thm parser
  val process_no_input : auto_level -> Proof.context -> thm -> thm
  val process_attr : auto_level -> attribute parser

  (* be activated at any auto level *)
  val safe : 'a -> auto_level -> 'a
  (* be activated only when auto level >= 1 *)
  val almost_safe : 'a -> auto_level -> 'a
  (* be activated only when auto level >= 2 *)
  val not_safe : 'a -> auto_level -> 'a
  val apply_attr : attribute -> Proof.context -> thm -> thm
  val focus_rule : proc -> proc
  val premise_prover : (auto_level -> Proof.context -> tactic) -> proc
  val parse_auto_level : proc -> proc

  val setup : binding -> int (*precedence*) -> term (*pattern*) -> proc
        -> string (*comment*) -> local_theory -> local_theory
  val setup_cmd : (((((string * Position.T) * int (*precedence*)) * string (*pattern*))
        * (binding * string option * mixfix) list)
        * Input.source (* proc source*)) * string (*comment*) -> local_theory -> local_theory
  val setup_resolver : binding -> int (*precedence*)
        -> (string * (binding * string option * mixfix) list) (* pattern *)
        -> (xstring * Position.T) (*name of facts*) -> string (*comment*)
        -> local_theory -> local_theory
end
structure NuProcessor : NU_PROCESSOR = struct
open Thm NuBasics
exception Bypass
type binding = Binding.binding
exception ProcessTerminated of thm * Token.T list
exception ProcessFail of binding * thm * exn
type auto_level = int
type proc = auto_level -> Proof.context -> thm -> thm parser


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
      (proc (Context.proof_of ctx) th --| Scan.catch Parse.eof) toks |> fst))
val wrap_attr = wrap_attr : (Proof.context -> thm -> thm parser) -> attribute parser
fun defined ctx name =
  let
    val tab = Data.get ctx
    val name = Name_Space.intern (Name_Space.space_of_table tab) name
  in
    Name_Space.defined tab name
  end
fun get_attr ctx name auto_level =
  wrap_attr
    (proc_of (Name_Space.check ctx (Data.get ctx) name |> snd) auto_level)

fun enable name =
      Data.map (Name_Space.map_table_entry name (set_enabled true))
fun disable name =
      Data.map (Name_Space.map_table_entry name (set_enabled false))

exception Processed of (thm * Token.T list)
fun process_impl auto_level ctx procs (th,toks) limit =
      let
        val focus = prop_of th |> dest_SpecTop |> #1
      in
        (List.app (fn (_, Processor {binding, pattern, enabled, proc,...}) =>
          if not enabled then ()
          else if can (Pattern.unify ctx (pattern,focus)) Envir.init
          then (@{print} binding;
            if limit > 100 then error "too deep process" else ();
            raise Processed
              ((proc auto_level (Context.proof_of ctx) th
                || (fn _ => raise Bypass)) toks)
          ) handle Bypass => ()
              | Processed th_toks => raise Processed th_toks
              | ProcessTerminated th_toks => raise ProcessTerminated th_toks
              | ex => (@{print} th; @{print} binding; Exn.reraise (@{print} ex))
            (* | ex => Exn.reraise (ProcessFail (binding,th,ex)) *)
          else ()
        ) procs 
        ; (th,toks))
      handle Processed th_toks => process_impl auto_level ctx procs th_toks (limit + 1)
        | ProcessTerminated th_toks => th_toks
      end
fun process auto_level ctx th toks =
  Runtime.exn_trace (fn _ =>
  process_impl auto_level (Context.Proof ctx)
    (Data.get (Context.Proof ctx) |> Name_Space.dest_table |> sort (proc_ord o apply2 snd))
    (th,toks) 0)
val process_attr = wrap_attr o process
fun process_no_input ctx auto_level th = process ctx auto_level th [Token.eof] |> #1

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
          ^ ML_Syntax.print_term term ^ ") (let open NuProcessor in ") @
          ML_Lex.read_source proc @
          ML_Lex.read (" end) " ^ ML_Syntax.print_string comment ^ ")"))
    )
  end

val safe = K
fun almost_safe f auto_level = if auto_level >= 1 then f else raise Bypass
fun not_safe f auto_level = if auto_level >= 2 then f else raise Bypass
fun parse_auto_level proc auto_level ctx th =
  NuParse.auto_level #-> (fn auto_level' => proc (Int.min (auto_level, auto_level')) ctx th)

fun apply_attr attr ctx th =
  attr (Context.Proof ctx, th) |> #2 |> the
fun focus_rule processor auto_level ctx th toks = 
  let
    val (th,ctx) = open_specthm th ctx
    val (th,toks) = processor auto_level ctx th toks
    val (th,_) = close_specthm th ctx
  in
    (th,toks)
  end
fun premise_prover_raw prover auto_level ctx th =
  Scan.succeed
    ((cprem_of th 1 |> Goal.init |> prover auto_level ctx |> Seq.pull |> (fn x =>
      case x of SOME (th,_) => Goal.conclude th | _ => raise Bypass)
    ) RS th)
val premise_prover = focus_rule o premise_prover_raw

fun setup_resolver binding precedence pattern facts comment lthy =
  let
    val facts = Facts.check (Context.Proof lthy) (Proof_Context.facts_of lthy) facts
  in
    setup' binding precedence pattern (
      premise_prover (almost_safe (fn ctx =>
        Tactical.SOLVED' (Tactical.REPEAT o Tactic.resolve_tac ctx
          (Proof_Context.get_thms ctx facts)) 1))
    ) comment lthy
  end
(* fun processor_parser (ctx,tokens) =
val processor_attr = Scan.lift (Parse.named_position >> #1) --  *)
  
end
