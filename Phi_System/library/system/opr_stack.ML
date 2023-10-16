signature PHI_OPR_STACK = sig

type operator_info = (int (*left precedence*) * int (*precedence*) * int (*arity delta*) option)
type arg_name = string option * Position.T
type named_arg = arg_name * thm list (*values*)
type free_param = exn

exception String_Param of string

type names_of_args = (string option * Position.T) list (*The name of the current parameter that the programming is making;
                                                     It enables named parameter like \<open>call (name1: aa, name2: bb)\<close>;
                                                     This feature is used later in constructing named tuple, like \<open>{aa: 1, bb: 2}\<close>,
                                                     where the \<open>aa\<close> and \<open>bb\<close> are actually such named parameters.
                                                     The list is a stack of nested callings, but not calling stack! e.g.,
                                                     when constructing the dd in \<open>{aa: 1, bb: {cc: 2, dd: 3}}\<close>, the stack is [bb,dd],
                                                     and the source is identical to \<open>mk_tup(aa: 1, bb: mk_tup(cc: 2, dd: 3))\<close>,
                                                     so the stack is about the two callings of \<open>mk_tup\<close>, rather than their
                                                     operand stack.*)

datatype opr_frame = Apply of ( (string * Position.T)
                              * Phi_CP_IDE.expr_id
                              * thm list (*app rules*)
                              * thm list (*values before*))
                   | Meta_Apply of ((Phi_CP_IDE.eval_cfg * named_arg list * exn option (*free argument*)
                                          -> (opr_frame list * names_of_args) * context_state
                                          -> (opr_frame list * names_of_args) * context_state)
                                    * thm list (*values before*)
                                    * (string * Position.T) (*name and position of the apply*))
                   | Begin_Block
                   | Comma of named_arg
                   | Opr of ( int (*precedence*) * int option (*arity constraint*)
                            * (string * Position.T)
                            * Phi_CP_IDE.expr_id
                            * thm list)
                   | Meta_Opr of (int (*precedence*) * int option (*arity constraint*)
                               * (string * Position.T)
                               * Phi_CP_IDE.expr_id
                               * free_param option
                               * (Phi_CP_IDE.eval_cfg * (string * Position.T) * free_param option ->
                                    opr_frame list * context_state ->
                                    opr_frame list * context_state))
                   | Left_Parenthesis of thm list (*values before*)

type opr_stack = opr_frame list * names_of_args
type context = opr_stack * context_state

val init_opr_stack : opr_stack
val precedence_of_frame : opr_frame -> int
val precedence_of : opr_frame list -> int


structure Data : PROOF_DATA
val initialize_opr_stack : Proof.context -> Proof.context

(* Operator Database *)

val lookup_operator : theory -> string -> operator_info option

val decl_opr : int * int * string * int option -> theory -> theory
val decl_infix : int * string * int option -> theory -> operator_info * theory
val decl_infixl : int * string * int option -> theory -> operator_info * theory
val decl_infixr : int * string * int option -> theory -> operator_info * theory
val decl_prefix : int * string * int option -> theory -> operator_info * theory
val decl_postfix : int * string * int option -> theory -> operator_info * theory

(* Data Base of Meta Operators *)

type meta_opr = Phi_CP_IDE.eval_cfg * (string * Position.T) * free_param option ->
                opr_frame list * context_state ->
                opr_frame list * context_state

val lookup_meta_opr : theory -> string -> meta_opr option
val set_meta_opr : string * meta_opr -> theory -> theory

(* Control of Lines and Statements *)

val is_the_first_statement : opr_frame list -> bool
val uninitialize : context -> context

val interrupt : context -> context
val is_interrupted : opr_frame list -> bool
val uninterrupted : context -> context

(* Hooks *)

structure Begin_of_Statement : HOOKS
structure End_of_Statement : HOOKS
structure Begin_of_Line : HOOKS
structure End_of_Line : HOOKS

(* Whether a rule can be applied by delay *)

structure Synt_No_Delayed_Apply : GENERIC_DATA
  (*registries of whether a rule can be applied delayed*)

val synt_can_delay_apply  : Context.generic -> Symtab.key -> bool
val synt_can_delay_apply' : Context.generic -> Facts.ref -> bool


end

structure Phi_Opr_Stack : PHI_OPR_STACK = struct

(** Library **)

type arg_name = string option * Position.T
type named_arg = arg_name * thm list (*values*)
type free_param = exn
type names_of_args = (string option * Position.T) list

datatype opr_frame = Apply of ( (string * Position.T)
                              * Phi_CP_IDE.expr_id
                              * thm list (*app rules*)
                              * thm list (*values before*))
                      | Meta_Apply of ( (Phi_CP_IDE.eval_cfg * named_arg list * free_param option
                                              -> (opr_frame list * names_of_args) * context_state
                                              -> (opr_frame list * names_of_args) * context_state)
                                      * thm list (*values before*)
                                      * (string * Position.T) (*name and position of the apply*))
                      | Begin_Block
                      | Comma of named_arg
                      | Opr of ( int (*precedence*) * int option (*arity constraint*)
                               * (string * Position.T)
                               * Phi_CP_IDE.expr_id
                               * thm list)
                      | Meta_Opr of (int (*precedence*) * int option (*arity constraint*)
                                  * (string * Position.T)
                                  * Phi_CP_IDE.expr_id
                                  * free_param option
                                  * (Phi_CP_IDE.eval_cfg * (string * Position.T) * free_param option ->
                                      opr_frame list * context_state ->
                                      opr_frame list * context_state))
                      | Left_Parenthesis of thm list (*values before*)

type meta_opr = Phi_CP_IDE.eval_cfg * (string * Position.T) * free_param option ->
                opr_frame list * context_state ->
                opr_frame list * context_state

type opr_stack = opr_frame list * names_of_args
type context = opr_stack * context_state


fun precedence_of_frame (Apply _) = ~1
  | precedence_of_frame (Meta_Apply _) = ~1
  | precedence_of_frame Begin_Block = ~1
  | precedence_of_frame (Comma _) = ~1
  | precedence_of_frame (Opr (prec, _, _, _, _)) = prec
  | precedence_of_frame (Meta_Opr (prec, _, _, _, _, _)) = prec
  | precedence_of_frame (Left_Parenthesis _) = ~1

fun precedence_of [] = ~1
  | precedence_of (frame :: _) = precedence_of_frame frame

(* Predefined Free Params *)

exception String_Param of string

(** Marks **)

(* Statement Interruption *)

(*An statement can be separated into two Isar commands, particularly due to inserted proof of
  obligations. When a statement is split, a special null-arity meta operator of highest precedence
  is pushed to the operator stack, marking the statement is incomplete.
 *)

val statement_interruptionN = "<interrupt>"
val statement_interruptionO = Meta_Opr (~1, NONE, (statement_interruptionN,Position.none), [], NONE, K I)

fun is_interrupted (Meta_Opr (_, _, ("<interrupt>", _), _, _, _) :: _) = true
  | is_interrupted _ = false

fun interrupt ((opr,anames),s) = ((statement_interruptionO::opr,anames),s)

fun uninterrupted ((opr,anames),s) =
  let val opr' = case opr of (Meta_Opr (_, _, ("<interrupt>", _), _, _, _) :: opr') => opr'
                           | _ => opr
   in ((opr',anames),s)
  end


(* Mark of the First Statement in a Block *)
val initial_statementN = "<initial>"
val initial_statementO = Meta_Opr (1001,NONE,(initial_statementN,Position.none),[],NONE,K I)

fun is_the_first_statement (Meta_Opr (_, _, ("<initial>", _), _, _, _) :: _) = true
  | is_the_first_statement _ = false

fun uninitialize ((opr,anames),s) =
  let val opr' = case opr of (Meta_Opr (_, _, ("<initial>", _), _, _, _) :: opr') => opr'
                           | _ => opr
   in ((opr',anames),s)
  end

val init_opr_stack = ([initial_statementO], [(NONE, Position.none)])


(** Stack Data **)

structure Data = Proof_Data (
  type T = opr_stack
  val init = K init_opr_stack
)

val initialize_opr_stack = Data.put init_opr_stack


(** Operator Database **)

type operator_info = (int (*left precedence*) * int (*precedence*) * int (*arity delta*) option)

structure Operators = Theory_Data (
  type T = operator_info Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (op =)
)

fun chk_precedence p =
  if 0 < p andalso p <= 1000 then p
  else error "precedence of operator should be within [1,1000]"

fun decl_infix' (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (precedence, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_infix (precedence, symbol, arity) thy =
  ( (precedence, precedence, arity),
    decl_infix' (precedence, symbol, SOME arity) thy )

fun decl_opr (left_precedence, precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (chk_precedence left_precedence, chk_precedence precedence, arity)))

fun decl_infixr' (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (precedence + 1, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_infixr (precedence, symbol, arity) thy =
  ( (precedence + 1, precedence, arity),
    decl_infixr' (precedence, symbol, SOME arity) thy )

fun decl_infixl' (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (chk_precedence precedence, precedence+1, the_default (SOME 1) arity)))

fun decl_infixl (precedence, symbol, arity) thy =
  ( (precedence, precedence+1, arity),
    decl_infixl' (precedence, symbol, SOME arity) thy )

fun decl_prefix' (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (1001, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_prefix (precedence, symbol, arity) thy =
  ( (1001, precedence, arity),
    decl_prefix' (precedence, symbol, SOME arity) thy )

fun decl_postfix' (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (chk_precedence precedence, 1001, the_default (SOME 0) arity)))

fun decl_postfix (precedence, symbol, arity) thy =
  ( (precedence, 1001, arity),
    decl_postfix' (precedence, symbol, SOME arity) thy )

fun lookup_operator thy symbol = Symtab.lookup (Operators.get thy) symbol

val symbol = Parse.group (fn () => "symbol") (Parse.sym_ident || Parse.keyword || Parse.string)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>declare_\<phi>operator\<close>
    "declare operators in \<phi>-programming"
    (Scan.repeat1
        (( \<^keyword>\<open>infixl\<close> >> K decl_infixl' || \<^keyword>\<open>infixr\<close> >> K decl_infixr' ||
           \<^keyword>\<open>infix\<close> >> K decl_infix' ||
         Args.$$$ "prefix" >> K decl_prefix' || Args.$$$ "postfix" >> K decl_postfix')
       -- Parse.nat
       -- Parse.position symbol
       -- Scan.option (Parse.int >> SOME || \<^keyword>\<open>var\<close> >> K NONE))
    >> (fn decls => Toplevel.theory (
            fold (fn (((f,prec),(sym,_)),arity) => f (prec, sym, arity)) decls
         #> Named_Target.theory_map (
              fold (fn ((_,sym),_) =>
                Named_Theorems.declare (Binding.suffix_name "_\<phi>app" (Binding.make sym))
                    ("overloads \<phi>-programming operator " ^ fst sym)
                #> snd)
              decls)
       ))
)


(** Hooks **)

structure Begin_of_Statement = Hooks (type arg = Phi_CP_IDE.eval_cfg type state = context)
structure End_of_Statement = Hooks (type arg = Phi_CP_IDE.eval_cfg type state = context)
structure Begin_of_Line = Hooks (type arg = Phi_CP_IDE.eval_cfg type state = context)
structure End_of_Line = Hooks (type arg = Phi_CP_IDE.eval_cfg type state = context)

(** Whether a rule can be applied by delay **)

structure Synt_No_Delayed_Apply = Generic_Data (
  type T = Symtab.set
  val empty = Symtab.empty
  val merge = Symtab.merge (op =)
)

fun synt_can_delay_apply ctxt sym =
  not (Symtab.defined (Synt_No_Delayed_Apply.get ctxt) sym)

fun synt_can_delay_apply' ctxt (Facts.Named ((name,_),_)) = synt_can_delay_apply ctxt name
  | synt_can_delay_apply' _ _ = true

val _ = Theory.setup (Context.theory_map (Synt_No_Delayed_Apply.map (
   Symtab.insert_set "if"
#> Symtab.insert_set "while"
)))


(** Database of Meta Operators **)

structure Meta_Opr = Theory_Data (
  type T = meta_opr Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K false)
)

fun lookup_meta_opr thy = Symtab.lookup (Meta_Opr.get thy)
val set_meta_opr = Meta_Opr.map o Symtab.update


(** Setup of Hooks **)


val _ = Theory.setup (Context.theory_map (

  Begin_of_Line.add 100 (fn cfg => fn s =>
     if is_interrupted (#1 (#1 s))
     then uninterrupted s
     else Begin_of_Statement.invoke (Context.Proof (#1 (#2 s))) cfg s)

#>End_of_Line.add 0 (fn cfg => fn s =>
     if is_interrupted (#1 (#1 s))
     then s
     else End_of_Statement.invoke (Context.Proof (#1 (#2 s))) cfg s)

))



end