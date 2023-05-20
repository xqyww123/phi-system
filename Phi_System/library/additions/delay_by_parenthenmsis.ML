signature PHI_DELAY_APPLICATION = sig

structure Synt_No_Delayed_Apply : GENERIC_DATA
  val synt_can_delay_apply  : Context.generic -> Symtab.key -> bool
  val synt_can_delay_apply' : Context.generic -> Facts.ref -> bool

type operator_info
type arg_name = (string * Position.T) option

val apply : (string * Position.T) * thm list -> context_state -> context_state
val begin_block : Proof.context -> Proof.context
val close_parenthesis : (context_state -> context_state) -> context_state -> context_state
val open_parenthesis : arg_name -> context_state -> context_state
val push_operator : operator_info * (string * Position.T) * thm list -> context_state -> context_state
val end_expression : context_state -> context_state
val comma : arg_name -> context_state -> context_state
val lookup_operator : theory -> Symtab.key -> operator_info option

end

structure Phi_Delay_Application : PHI_DELAY_APPLICATION = struct

type arg_name = (string * Position.T) option
type named_arg = arg_name * thm list (*values*)
datatype delay_action = Apply of ((string * Position.T) * thm list (*app rules*) * thm list (*values before*))
                      | Meta_Apply of ((named_arg list -> context_state -> context_state)
                                        * named_arg)
                      | Begin_Block
                      | Comma of named_arg
                      | Opr of (int (*precedence*) * int option (*arity constraint*)
                                  * (string * Position.T) * thm list)
                      | Left_Parenthesis of thm list (*values before*)

structure Parenthesis_Stack = Proof_Data (
  type T = (delay_action list * (string * Position.T) option list (*current parameter name*))
  val init = K ([], [NONE])
)

(* fun invoke_delayed_action (Apply (_, rules)) s = Phi_Apply.apply rules s
  | invoke_delayed_action End_Block s =
      raise Phi_Processor.Process_State_Call (s,
             Phi_Toplevel.end_block_auto_proof_cmd NONE false
          #> Proof.map_context (Parenthesis_Stack.map tl)) *)

fun values_number ret (Const (@{const_name Subjection}, _) $ T) = values_number ret T
  | values_number ret (Const (@{const_name ExSet}, _) $ T) = values_number ret T
  | values_number ret (Abs (_, _, T)) = values_number ret T
  | values_number ret (Const (\<^const_name>\<open>times\<close>, _) $ L $ (
        Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const(\<^const_name>\<open>Val\<close>, _) $ _ $ _)))
      = values_number (ret+1) L
  | values_number ret (Const (\<^const_name>\<open>times\<close>, _) $ L $ _) = values_number ret L
  | values_number ret (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const(\<^const_name>\<open>Val\<close>, _) $ _ $ _))
      = ret + 1
  | values_number ret _ = ret

fun chk_arity_constraint NONE _ _ _ = ()
  | chk_arity_constraint(SOME n) mode (name,pos) (ctxt,sequent)
      = let val actual = values_number 0 (#spec_of mode (Thm.prop_of sequent))
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
  case get_first fst vs
    of SOME (_,pos) => error ("Named arguement is not supported here! " ^ Position.here pos)
     | _ =>  maps snd vs

fun eval_opr _ _ (acts as (Apply _ :: _)) s = (acts, s)
  | eval_opr _ _ (acts as (Begin_Block :: _)) s = (acts, s)
  | eval_opr mode limit (acts as (Opr (pr, arity, name, rules) :: aR)) s
      = if pr < limit then (acts, s)
        else (
          chk_arity_constraint arity mode name s;
          eval_opr mode limit aR (
            let val (ctxt',sequent') = Phi_Processor.process_no_input NONE (Phi_Apply.apply rules s)
             in if #is_on_going_construction mode (Thm.prop_of sequent')
                then (ctxt',sequent')
                else error ("Fail to solve obligations of operat " ^ fst name ^ " (" ^
                            Position.here (snd name) ^ ")\n\
                            \You may need to prove its obligations manually using \<^keyword>\<open>certified\<close>.")
            end))
  | eval_opr _ _ (acts as (Left_Parenthesis _ :: _)) s = (acts, s)
  | eval_opr _ _ (acts as (Meta_Apply _ :: _)) s = (acts, s)
  | eval_opr _ _ (acts as (Comma _ :: _)) s = (acts, s)
  | eval_opr _ _ [] s = ([], s)

fun close_parenthesis c s0 =
  let fun close c args (Apply (_, rules, vals_before) :: acts) s =
            c acts (Phi_Apply.apply rules (
                      Generic_Variable_Access.push_values (vals_before @ chk_no_name args) s))
        | close c args (Begin_Block :: acts) s =
            raise Phi_Processor.Process_State_Call (
                Generic_Variable_Access.push_values (chk_no_name args) s,
                Phi_Toplevel.end_block_auto_proof_cmd NONE false
             #> Phi_Envir.map_state_sequent (c acts))
        | close _ _ (Opr _ :: _) _ = error "internal bug #91066fd2-8881-422f-bf54-4b3f69879042"
        | close c args (Left_Parenthesis vals_before :: acts) s =
            c acts (Generic_Variable_Access.push_values (vals_before @ chk_no_name args) s)
        | close c args (Meta_Apply (f, arg) :: acts) (ctxt,sequent) =
            c acts (f (arg :: args) (ctxt,sequent))
        | close c args (Comma arg :: acts) s =
            close c (arg :: args) acts s
        | close _ _ [] _ = error "parenthesis is inbalanced!"
      val mode = Phi_Working_Mode.mode1 (fst s0)
      val (actions, arg_name :: arg_names) = Parenthesis_Stack.get (fst s0)
      val (actions', (ctxt,sequent)) = eval_opr mode 0 actions s0
      val (sequent', vals) = Generic_Variable_Access.collect_and_clean_value true ctxt sequent
   in close (fn acts => fn (ctxt, sequent) =>
                  c (Parenthesis_Stack.put (acts, arg_names) ctxt, sequent))
            [(arg_name, vals)] actions' (ctxt, sequent')
  end

fun open_parenthesis arg_name (ctxt,sequent) =
  let val (sequent', vals) = Generic_Variable_Access.collect_and_clean_value true ctxt sequent
   in (Parenthesis_Stack.map (fn (L, arg_names) =>
          (Left_Parenthesis vals :: L, arg_name :: arg_names)) ctxt,
       sequent')
  end

fun push_operator ((left_prec,prec,arity_delta),name,rule) (ctxt,sequent) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val (actions, arg_names) = Parenthesis_Stack.get ctxt
      val (actions', (ctxt',sequent')) = eval_opr mode left_prec actions (ctxt,sequent)
      val arity_constraint =
            Option.map (fn x => x + values_number 0 (#spec_of (Phi_Working_Mode.mode1 ctxt')
                                                              (Thm.prop_of sequent')))
                       arity_delta
   in (ctxt',sequent')
   |> apfst (Parenthesis_Stack.put (Opr (prec,arity_constraint,name,rule) :: actions', arg_names))
  end

fun end_expression s =
  let val mode = Phi_Working_Mode.mode1 (fst s)
      val (actions, arg_name :: arg_names) = Parenthesis_Stack.get (fst s)
      val (actions', s') = eval_opr mode 0 actions s
   in s'
   |> apfst (Parenthesis_Stack.put (actions', NONE :: arg_names))
  end

fun comma next_arg_name s =
  let val mode = Phi_Working_Mode.mode1 (fst s)
      val (actions, arg_name :: arg_names) = Parenthesis_Stack.get (fst s)
      val (actions', (ctxt,sequent)) = eval_opr mode 0 actions s
      val (sequent', vals) = Generic_Variable_Access.collect_and_clean_value true ctxt sequent
      val ctxt' = Parenthesis_Stack.put (Comma (arg_name, vals) :: actions', next_arg_name :: arg_names) ctxt
   in (ctxt', sequent')
  end

fun apply (name, rules) (ctxt,sequent) =
  let val (actions, arg_names) = Parenthesis_Stack.get ctxt
      val (sequent', vals) = Generic_Variable_Access.collect_and_clean_value true ctxt sequent
      val ctxt' = Parenthesis_Stack.put (Apply (name, rules, vals) :: actions, NONE :: arg_names) ctxt
   in (ctxt', sequent')
  end

val begin_block = Parenthesis_Stack.map (fn (actions, arg_names) =>
        (Begin_Block :: actions, NONE :: arg_names))

val delayed_apps = Parenthesis_Stack.get #> fst

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

fun decl_infix (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (precedence, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_infixr (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (precedence + 1, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_infixl (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (chk_precedence precedence, precedence+1, the_default (SOME 1) arity)))

fun decl_prefix (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (1001, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_postfix (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (chk_precedence precedence, 1001, the_default (SOME 0) arity)))

fun lookup_operator thy symbol = Symtab.lookup (Operators.get thy) symbol

val symbol = Parse.group (fn () => "symbol") (Parse.sym_ident || Parse.keyword || Parse.string)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>declare_\<phi>operator\<close>
    "declare operators in \<phi>-programming"
    (Scan.repeat1
        (( \<^keyword>\<open>infixl\<close> >> K decl_infixl || \<^keyword>\<open>infixr\<close> >> K decl_infixr ||
           \<^keyword>\<open>infix\<close> >> K decl_infix ||
         Args.$$$ "prefix" >> K decl_prefix || Args.$$$ "postfix" >> K decl_postfix)
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

  Phi_Toplevel.End_of_Statement.add ~10 (K end_expression)

#>Phi_Toplevel.End_of_Statement.add 998 (K (fn (ctxt,sequent) => (
    if not (null (delayed_apps ctxt))
       andalso Phi_Toplevel.previous_statement_is_finished ctxt
    then warning "parenthesis is inbalanced!"
    else () ;
    (ctxt,sequent)
  )))

#>Phi_Toplevel.Begining_of_Statement.add 1 (K (fn (ctxt,sequent) => (
    if not (null (delayed_apps ctxt))
       andalso Phi_Toplevel.previous_statement_is_finished ctxt
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

end