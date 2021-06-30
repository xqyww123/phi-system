signature NU_PROCESSOR = sig
  type binding = Binding.binding
  exception Bypass
  exception ProcessFail of binding * thm * exn
  type auto_level = int
  type proc = (auto_level -> Proof.context -> thm -> thm)
  val define : binding -> int (*precedence*) -> term (*pattern*) -> proc -> local_theory -> local_theory
  (* val get : Proof.context -> string -> T option *)
  val get_attr : Context.generic -> xstring * Position.T -> int (*auto level*) -> attribute
  val enable : string -> Context.generic -> Context.generic
  val disable : string -> Context.generic -> Context.generic
  val list : Context.generic -> (binding * term (*pattern*)) list
  val process : auto_level -> Context.generic -> thm -> thm

  (* be activated at any auto level *)
  val safe : 'a -> auto_level -> 'a
  (* be activated only when auto level >= 1 *)
  val almost_safe : 'a -> auto_level -> 'a
  (* be activated only when auto level >= 2 *)
  val not_safe : 'a -> auto_level -> 'a
  val apply_attr : attribute -> Proof.context -> thm -> thm
  val focus_rule : proc -> proc
  val premise_prover : (auto_level -> Proof.context -> tactic) -> proc

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
exception ProcessFail of binding * thm * exn
type auto_level = int
type proc = auto_level -> Proof.context -> thm -> thm


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
(* FIXME *)
fun get_attr ctx name auto_level =
  let
    val tab = Data.get ctx
  in
    Thm.rule_attribute [] (Context.proof_of #>
      proc_of (Name_Space.check ctx tab name |> snd) auto_level)
  end

fun enable name =
      Data.map (Name_Space.map_table_entry name (set_enabled true))
fun disable name =
      Data.map (Name_Space.map_table_entry name (set_enabled false))

exception Processed of thm
fun process_impl auto_level ctx procs th =
      let
        val focus = prop_of th |> dest_SpecTop |> #1
      in
        fold (fn (_, Processor {binding, pattern, enabled, proc,...}) => fn th =>
          if not enabled then th
          else if can (Pattern.unify ctx (pattern,focus)) Envir.init
          then (@{print} binding;
          raise Processed (proc auto_level (Context.proof_of ctx) th))
            handle Bypass => th | Processed th => raise Processed th
              (* | ex => Exn.reraise (ProcessFail (binding,th,ex)) *)
          else th
        ) procs th
      handle Processed th' => process_impl auto_level ctx procs th'
      end
fun process auto_level ctx =
  process_impl auto_level ctx
    (Data.get ctx |> Name_Space.dest_table |> sort (proc_ord o apply2 snd))

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

fun apply_attr attr ctx th =
  attr (Context.Proof ctx, th) |> #2 |> the
fun focus_rule processor auto_level ctx th = 
  let
    val (th,ctx) = open_specthm th ctx
    val th = processor auto_level ctx th
    val (th,_) = close_specthm th ctx
  in
    th
  end
fun premise_prover_raw prover auto_level ctx th =
  (cprem_of th 1  |> Goal.init |> prover auto_level ctx |> Seq.hd |> Goal.conclude) RS th
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
