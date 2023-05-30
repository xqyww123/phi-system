signature PHI_OPR_STACK = sig

structure Synt_No_Delayed_Apply : GENERIC_DATA
  val synt_can_delay_apply  : Context.generic -> Symtab.key -> bool
  val synt_can_delay_apply' : Context.generic -> Facts.ref -> bool

type operator_info = (int (*left precedence*) * int (*precedence*) * int (*arity delta*) option)
type arg_name = string option * Position.T
type named_arg = arg_name * thm list (*values*)
type free_param = exn option

exception String_Param of string

val do_application : thm list -> context_state -> context_state
val begin_apply : (string * Position.T) * thm list -> context_state -> context_state
val begin_block : Position.T -> Proof.context -> Proof.context
val close_parenthesis : free_param -> (context_state -> context_state)
                     -> context_state -> context_state
val open_parenthesis : arg_name -> context_state -> context_state
val push_operator : operator_info * (string * Position.T) * thm list -> context_state -> context_state
val end_expression : int (*precedence*) -> context_state -> context_state (*evaluate stacked operators
      of precedence higher than the given argument*)
val comma : arg_name -> context_state -> context_state
val lookup_operator : theory -> string -> operator_info option

val is_during_apply : Proof.context -> string -> bool


datatype opr_frame = Apply of ((string * Position.T) * thm list (*app rules*) * thm list (*values before*))
                   | Meta_Apply of ((named_arg list * exn option (*free argument*)
                                          -> opr_frame list * context_state
                                          -> opr_frame list * context_state)
                                    * thm list (*values before*)
                                    * (string * Position.T) (*name and position of the apply*))
                   | Begin_Block
                   | Comma of named_arg
                   | Opr of (int (*precedence*) * int option (*arity constraint*)
                              * (string * Position.T) * thm list)
                   | Meta_Opr of (int (*precedence*)
                               * int option (*arity constraint*)
                               * (string * Position.T)
                               * free_param
                               * ((string * Position.T) * free_param ->
                                    opr_frame list * context_state ->
                                    opr_frame list * context_state))
                   | Left_Parenthesis of thm list (*values before*)

type meta_opr = (string * Position.T) * free_param ->
                opr_frame list * context_state ->
                opr_frame list * context_state

val lookup_current_opstack : Proof.context -> opr_frame list

val eval_opr : Phi_Working_Mode.working_mode * int * (string * Position.T) ->
                  opr_frame list ->
                    Proof.context * thm ->
                      opr_frame list * (Proof.context * thm)

val meta_apply : (string * Position.T) * arg_name ->
                    (named_arg list * free_param -> opr_frame list * context_state -> opr_frame list * context_state) ->
                    context_state -> context_state

val lookup_meta_opr : theory -> string -> meta_opr option
val set_meta_opr : string * meta_opr -> theory -> theory
val push_meta_operator : operator_info * (string * Position.T) * free_param
                       * ( (string * Position.T) * free_param
                              -> opr_frame list * context_state
                              -> opr_frame list * context_state )
                       -> context_state -> context_state


val decl_opr : int * int * string * int option -> theory -> theory
val decl_infix : int * string * int option -> theory -> operator_info * theory
val decl_infixl : int * string * int option -> theory -> operator_info * theory
val decl_infixr : int * string * int option -> theory -> operator_info * theory
val decl_prefix : int * string * int option -> theory -> operator_info * theory
val decl_postfix : int * string * int option -> theory -> operator_info * theory

end

structure Phi_Opr_Stack : PHI_OPR_STACK = struct

type arg_name = string option * Position.T
type named_arg = arg_name * thm list (*values*)
type free_param = exn option

exception String_Param of string

datatype opr_frame = Apply of ((string * Position.T) * thm list (*app rules*) * thm list (*values before*))
                      | Meta_Apply of ((named_arg list * free_param
                                              -> opr_frame list * context_state
                                              -> opr_frame list * context_state)
                                        * thm list (*values before*)
                                        * (string * Position.T) (*name and position of the apply*))
                      | Begin_Block
                      | Comma of named_arg
                      | Opr of (int (*precedence*) * int option (*arity constraint*)
                                  * (string * Position.T) * thm list)
                      | Meta_Opr of (int (*precedence*) * int option (*arity constraint*)
                                  * (string * Position.T)
                                  * free_param
                                  * ((string * Position.T) * free_param ->
                                      opr_frame list * context_state ->
                                      opr_frame list * context_state))
                      | Left_Parenthesis of thm list (*values before*)

type meta_opr = (string * Position.T) * free_param ->
                opr_frame list * context_state ->
                opr_frame list * context_state

structure Opr_Stack = Proof_Data (
  type T = (opr_frame list * (string option * Position.T) list (*current parameter name*))
  val init = K ([], [(NONE, Position.none)])
)

val lookup_current_opstack = fst o Opr_Stack.get

(* fun invoke_delayed_action (Apply (_, rules)) s = Phi_Apply.apply rules s
  | invoke_delayed_action End_Block s =
      raise Phi_Processor.Process_State_Call (s,
             Phi_Toplevel.end_block_auto_proof_cmd NONE false
          #> Proof.map_context (Opr_Stack.map tl)) *)

fun chk_arity_constraint NONE _ _ _ = ()
  | chk_arity_constraint(SOME n) mode (name,pos) (_,sequent)
      = let val actual = Generic_Variable_Access.number_of_values (#spec_of mode (Thm.prop_of sequent))
         in if actual = n
            then ()
            else error (Pretty.string_of (Pretty.block ([
                  Pretty.str (if actual < n then "Less " else "More "),
                  Pretty.str "arguments are given to the operator \"",
                  Pretty.str name,
                  Pretty.str "\" than its expected arity "
                ] @ Pretty.here pos)))
        end

fun chk_no_name vs =
  case get_first (fn ((SOME _, pos),_) => SOME pos | _ => NONE) vs
    of SOME pos => error ("Named arguement is not supported here! " ^ Position.here pos)
     | _ =>  maps snd vs

fun bad_syntax (name, pos) =
      error ("Bad Syntax: " ^ name ^ " " ^ Position.here pos)

fun eval_opr _ (acts as (Apply _ :: _)) s = (acts, s)
  | eval_opr _ (acts as (Begin_Block :: _)) s = (acts, s)
  | eval_opr (mode, limit, name') (acts as (Opr (pr, arity, name, rules) :: aR)) s
      = if pr < limit then (acts, s)
        else if pr = limit then bad_syntax name'
        else (
          chk_arity_constraint arity mode name s;
          eval_opr (mode, limit, name') aR (
            Phi_Processor.process_all_antecedents NONE (Phi_Apply.apply rules s)))
  | eval_opr (mode, limit, name') (acts as (Meta_Opr (pr, arity, name, param, meta) :: aR)) s
      = if pr < limit then (acts, s)
        else if pr = limit then bad_syntax name'
        else let
          val _ = chk_arity_constraint arity mode name s
          val (acts',s') = meta (name,param) (aR,s)
                         |> apsnd (Phi_Processor.process_all_antecedents NONE)
           in eval_opr (mode, limit, name') acts' s' end
  | eval_opr _ (acts as (Left_Parenthesis _ :: _)) s = (acts, s)
  | eval_opr _ (acts as (Meta_Apply _ :: _)) s = (acts, s)
  | eval_opr _ (acts as (Comma _ :: _)) s = (acts, s)
  | eval_opr _ [] s = ([], s)

fun close_parenthesis arg c s0 =
  let fun close c args (Apply (_, rules, vals_before) :: acts) s =
            c acts (Phi_Apply.apply rules (
                      Generic_Variable_Access.push_values (vals_before @ chk_no_name args) s))
        | close c args (Begin_Block :: acts) s =
            raise Phi_Processor.Process_State_Call (
                Generic_Variable_Access.push_values (chk_no_name args) s,
                Phi_Toplevel.end_block_auto_proof_cmd NONE false
             #> Phi_Envir.map_state_sequent (c acts))
        | close _ _ (Opr _ :: _) _ = error "internal bug #91066fd2-8881-422f-bf54-4b3f69879042"
        | close _ _ (Meta_Opr _ :: _) _ = error "internal bug #10cc33ab-de95-48fb-8b8c-103f2c0110fd"
        | close c args (Left_Parenthesis vals_before :: acts) s =
            c acts (Generic_Variable_Access.push_values (vals_before @ chk_no_name args) s)
        | close c args (Meta_Apply (f, vals_before, (_, pos)) :: acts) (ctxt,sequent) =
            uncurry c (f (((NONE, pos), vals_before) :: args, arg) (acts, (ctxt,sequent)))
        | close c args (Comma arg :: acts) s =
            close c (arg :: args) acts s
        | close _ _ [] _ = error "parenthesis is inbalanced!"
      val mode = Phi_Working_Mode.mode1 (fst s0)
      val (actions, arg_name :: arg_names) = Opr_Stack.get (fst s0)
      val (actions', (ctxt,sequent)) = eval_opr (mode, 0, ("<internal bug>", Position.none)) actions s0
      val (vals, (ctxt',sequent')) = Generic_Variable_Access.extract_values (~1, true) (ctxt,sequent)
   in close (fn acts => fn (ctxt, sequent) =>
                  c (Opr_Stack.put (acts, arg_names) ctxt, sequent))
            [(arg_name, vals)] actions' (ctxt', sequent')
  end

fun open_parenthesis arg_name (ctxt,sequent) =
  let val (vals,(ctxt',sequent')) = Generic_Variable_Access.extract_values (~1, true) (ctxt,sequent)
   in (Opr_Stack.map (fn (L, arg_names) =>
          (Left_Parenthesis vals :: L, arg_name :: arg_names)) ctxt',
       sequent')
  end

fun push_operator ((left_prec,prec,arity_delta),name,rule) (ctxt,sequent) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val (actions, arg_names) = Opr_Stack.get ctxt
      val (actions', (ctxt',sequent')) = eval_opr (mode, left_prec, name) actions (ctxt,sequent)
      val arity_constraint =
            Option.map (fn x => x + Generic_Variable_Access.number_of_values
                                      (#spec_of (Phi_Working_Mode.mode1 ctxt') (Thm.prop_of sequent')))
                       arity_delta
   in (ctxt',sequent')
   |> apfst (Opr_Stack.put (Opr (prec,arity_constraint,name,rule) :: actions', arg_names))
  end

fun push_meta_operator ((left_prec,prec,arity_delta),name,param,meta) (ctxt,sequent) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val (actions, arg_names) = Opr_Stack.get ctxt
      val (actions', (ctxt',sequent')) = eval_opr (mode, left_prec, name) actions (ctxt,sequent)
      val arity_constraint =
            Option.map (fn x => x + Generic_Variable_Access.number_of_values (
                                        #spec_of (Phi_Working_Mode.mode1 ctxt') (Thm.prop_of sequent')))
                       arity_delta
   in (ctxt',sequent')
   |> apfst (Opr_Stack.put (Meta_Opr (prec,arity_constraint,name,param,meta) :: actions', arg_names))
  end

fun end_expression precedence s =
  let val mode = Phi_Working_Mode.mode1 (fst s)
      val (actions, arg_names) = Opr_Stack.get (fst s)
      val (actions', s') = eval_opr (mode, precedence, ("", Position.none)) actions s
   in s'
   |> apfst (Opr_Stack.put (actions', arg_names))
  end

fun do_application rules stat =
      stat
   |> end_expression 900
   |> Phi_Apply.apply rules

fun comma next_arg_name s =
  let val mode = Phi_Working_Mode.mode1 (fst s)
      val (actions, arg_name :: arg_names) = Opr_Stack.get (fst s)
      fun chk_actions (Left_Parenthesis _ :: _) = ()
        | chk_actions (Meta_Apply _ :: _) = ()
        | chk_actions (Apply _ :: _) = ()
        | chk_actions (Begin_Block :: _) = bad_syntax (",", snd next_arg_name)
        | chk_actions (Comma _ :: _ ) = ()
        | chk_actions (_ :: L) = chk_actions L
        | chk_actions [] = bad_syntax (",", snd next_arg_name)
      val _ = chk_actions actions
      val (actions', (ctxt,sequent)) = eval_opr (mode, 0, ("",Position.none)) actions s
      val (vals,(ctxt'1,sequent')) = Generic_Variable_Access.extract_values (~1, true) (ctxt,sequent)
      val ctxt' = Opr_Stack.put (Comma (arg_name, vals) :: actions', next_arg_name :: arg_names) ctxt'1
   in (ctxt', sequent')
  end

fun begin_apply (name, rules) (ctxt,sequent) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val (actions, arg_names) = Opr_Stack.get ctxt
      val (actions', (ctxt',sequent')) = eval_opr (mode, 900, name) actions (ctxt,sequent)
      val (vals,(ctxt'',sequent'')) = Generic_Variable_Access.extract_values (~1, true) (ctxt',sequent')
      val ctxt'3 = Opr_Stack.put (Apply (name, rules, vals) :: actions', (NONE, snd name) :: arg_names) ctxt''
   in (ctxt'3, sequent'')
  end

fun meta_apply (pos,arg_name) f (ctxt,sequent) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val (actions, arg_names) = Opr_Stack.get ctxt
      val (actions', (ctxt',sequent')) = eval_opr (mode, 900, pos) actions (ctxt,sequent)
      val (vals,(ctxt'',sequent'')) = Generic_Variable_Access.extract_values (~1, true) (ctxt',sequent')
      val ctxt'3 = Opr_Stack.put (Meta_Apply (f, vals, pos) :: actions', arg_name :: arg_names) ctxt''
   in (ctxt'3, sequent'')
  end

fun begin_block pos = Opr_Stack.map (fn (actions, arg_names) =>
        (Begin_Block :: actions, (NONE, pos) :: arg_names))

fun is_during_apply ctxt name =
  let val (actions, _) = Opr_Stack.get ctxt
      fun is_during (Apply ((s, _), _, _) :: _) = (s = name)
        | is_during (Meta_Apply (_, _, (s, _)) :: _) = s = name
        | is_during (Begin_Block :: _) = false
        | is_during (Comma _ :: L) = is_during L
        | is_during (Opr _ :: L) = is_during L
        | is_during (Meta_Opr _ :: L) = is_during L
        | is_during (Left_Parenthesis _ :: L) = is_during L
        | is_during [] = false
   in is_during actions
  end

val delayed_apps = Opr_Stack.get #> fst

(*** Prefix, Infix, Postfix operators  ***)

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


val _ = Theory.setup (Context.theory_map (

  Phi_Toplevel.End_of_Statement.add ~10 (K (end_expression 0))

#>Phi_Toplevel.End_of_Statement.add 998 (K (fn (ctxt,sequent) => (
    if not (null (delayed_apps ctxt))
    then warning "parenthesis is inbalanced!"
    else () ;
    (ctxt,sequent)
  )))

#>Phi_Toplevel.Begin_of_Next_Statement.add 1 (K (fn (ctxt,sequent) => (
    if not (null (delayed_apps ctxt))
    then error "parenthesis is inbalanced!"
    else () ;
    (ctxt,sequent)
  )))
))





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


structure Meta_Opr = Theory_Data (
  type T = meta_opr Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K false)
)

fun lookup_meta_opr thy = Symtab.lookup (Meta_Opr.get thy)
val set_meta_opr = Meta_Opr.map o Symtab.update


end