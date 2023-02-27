(* The old kernel for a programming language on IDE-CP.
 It collects all instructions of a semantic formalization and
  verifies whether a program is built using those instructions only, so
  the the program is valid without using invalid (non-registered) instructions.
*)

signature NU_INSTRUCTIONS = sig
  val list : Context.generic -> string list
  val list_definitions : Context.generic -> (string * thm) list
  val add : thm -> Context.generic -> Context.generic
  val is_instruction : Context.generic -> string -> bool
  val is_instruction_term : Context.generic -> term -> bool
  val is_compilable : Context.generic -> term -> bool (* iff all constants in the term are instructions *)
  (* val definition_of : string -> thm option *)
end
structure NuInstructions : NU_INSTRUCTIONS = struct
open HOLogic Term Thm

structure Instrs = Generic_Data
(
  type T = thm Symtab.table; (* key : the constant name, value: the definition *)
  val empty: T = Symtab.empty;
  val extend = I;
  val merge : T * T -> T = Symtab.join (fn _ => fn _ => raise Symtab.SAME);
);

val list = Instrs.get #> Symtab.keys
val list_definitions = Instrs.get #> Symtab.dest
fun dest_eq_lhs' tm =
      if can dest_Trueprop tm
      then dest_Trueprop tm |> dest_eq |> #1
      else Logic.dest_equals tm |> #1
fun name_of_definition def = Thm.concl_of def |> dest_eq_lhs' |> strip_comb |> #1 |> dest_Const |> #1
fun add def = Instrs.map (Symtab.update_new (name_of_definition def, def))
val is_instruction = Instrs.get #> Symtab.defined
fun is_instruction_term ctx (Const (name, _)) = is_instruction ctx name
  | is_instruction_term _ _ = false
fun is_compilable ctx tm = fold_aterms (fn tm => fn P => P andalso is_instruction_term ctx tm) tm true
(* fun definition_of const_name = Instrs.get lookup *)
end
