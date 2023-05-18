signature PHI_DELAY_APPLICATION = sig

structure Synt_No_Delayed_Apply : GENERIC_DATA
  val synt_can_delay_apply  : Context.generic -> Symtab.key -> bool
  val synt_can_delay_apply' : Context.generic -> Facts.ref -> bool

datatype delay_action = Apply of ((string * Position.T) * thm list)
                      | End_Block
                      | Opr of (int (*precedence*) * int option * (string * Position.T) * thm list)
                      | Left_Parenthesis

type operator_info

val delay_app : delay_action -> Proof.context -> Proof.context
val close_parenthesis : (context_state -> context_state) -> context_state -> context_state
val open_parenthesis : Proof.context -> Proof.context
val push_operator : operator_info * (string * Position.T) * thm list -> context_state -> context_state
val delayed_apps : Proof.context -> delay_action list
val end_expression : context_state -> context_state
val comma : context_state -> context_state
val lookup_operator : theory -> Symtab.key -> operator_info option

end

structure Phi_Delay_Application : PHI_DELAY_APPLICATION = struct

datatype delay_action = Apply of ((string * Position.T) * thm list)
                      | End_Block
                      | Opr of (int (*precedence*) * int option (*arity constraint*) * (string * Position.T) * thm list)
                      | Left_Parenthesis

structure Parenthesis_Stack = Proof_Data (
  type T = delay_action list
  val init = K []
)

fun delay_app app = Parenthesis_Stack.map (fn L => app :: L)

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

fun chk_arity_constraint NONE _ _ = ()
  | chk_arity_constraint (SOME n) (name,pos) (ctxt,sequent)
      = let val actual = values_number 0 (#spec_of (Phi_Working_Mode.mode1 ctxt) (Thm.prop_of sequent))
         in if actual = n
            then ()
            else error (Pretty.string_of (Pretty.block ([
                  Pretty.str (if actual < n then "Less " else "More "),
                  Pretty.str "arguments are given to the operator \"",
                  Pretty.str name,
                  Pretty.str "\" than its expected arity "
                ] @ Pretty.here pos)))
        end
      

fun close_parenthesis c s =
  let fun close c (Apply (_, rules) :: acts) s = c acts (Phi_Apply.apply rules s)
        | close c (End_Block :: acts) s =
            raise Phi_Processor.Process_State_Call (s,
                Phi_Toplevel.end_block_auto_proof_cmd NONE false
             #> Phi_Envir.map_state_sequent (c acts))
        | close c (Opr (_, arity,name, rules) :: acts) s = (
            chk_arity_constraint arity name s;
            close c acts (Phi_Apply.apply rules s |> Phi_Processor.process_no_input NONE))
        | close c (Left_Parenthesis :: acts) s = c acts s
        | close _ [] _ = error "parenthesis is inbalanced!"
   in close (fn acts => fn (ctxt, sequent) =>
                  c (Parenthesis_Stack.put acts ctxt, sequent))
            (Parenthesis_Stack.get (fst s))
            s
  end

fun eval_opr _ (acts as (Apply _ :: _)) s = (acts, s)
  | eval_opr _ (acts as (End_Block :: _)) s = (acts, s)
  | eval_opr limit (acts as (Opr (pr, arity, name, rules) :: aR)) s
      = if pr < limit then (acts, s)
        else (
          chk_arity_constraint arity name s;
          eval_opr limit aR (
                Phi_Apply.apply rules s |> Phi_Processor.process_no_input NONE))
  | eval_opr _ (acts as (Left_Parenthesis :: _)) s = (acts, s)
  | eval_opr _ [] s = ([], s)

val open_parenthesis = Parenthesis_Stack.map (fn L => Left_Parenthesis :: L)

fun push_operator ((left_prec,prec,arity_delta),name,rule) (ctxt,sequent) =
  let val actions = Parenthesis_Stack.get ctxt
      val (actions', s') = eval_opr left_prec actions (ctxt,sequent)
      val arity_constraint =
            Option.map (fn x => x + values_number 0 (#spec_of (Phi_Working_Mode.mode1 ctxt)
                                                              (Thm.prop_of sequent)))
                       arity_delta
   in s'
   |> apfst (Parenthesis_Stack.put (Opr (prec,arity_constraint,name,rule) :: actions'))
  end

fun end_expression s =
  let val actions = Parenthesis_Stack.get (fst s)
      val (actions', s') = eval_opr 0 actions s
   in s'
   |> apfst (Parenthesis_Stack.put actions')
  end

val delayed_apps = Parenthesis_Stack.get

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

fun decl_infixr (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (precedence + 1, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_infixl (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (chk_precedence precedence, precedence+1, the_default (SOME 1) arity)))

fun decl_prefix (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (1001, chk_precedence precedence, the_default (SOME 1) arity)))

fun decl_postfix (precedence, symbol, arity) =
      Operators.map (Symtab.update_new (symbol, (chk_precedence precedence, 1001, the_default (SOME 0) arity)))

fun lookup_operator thy symbol = Symtab.lookup (Operators.get thy) symbol

val symbol = Parse.group (fn () => "symbol") (Parse.sym_ident || Parse.keyword)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>declare_\<phi>operator\<close>
    "declare operators in \<phi>-programming"
    (Scan.repeat1
        (( \<^keyword>\<open>infixl\<close> >> K decl_infixl || \<^keyword>\<open>infixr\<close> >> K decl_infixr ||
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

  Phi_Toplevel.End_of_Statement.add 998 (K (fn (ctxt,sequent) => 
    let val (ctxt',sequent') = end_expression (ctxt,sequent)
     in if not (null (delayed_apps ctxt'))
           andalso Phi_Toplevel.previous_statement_is_finished ctxt'
        then warning "parenthesis is inbalanced!"
        else () ;
        (ctxt',sequent')
    end
  ))

#>Phi_Toplevel.Begining_of_Statement.add 1 (K (fn (ctxt,sequent) => (
    if not (null (delayed_apps ctxt))
       andalso Phi_Toplevel.previous_statement_is_finished ctxt
    then error "parenthesis is inbalanced!"
    else () ;
    (ctxt,sequent)
  )))
))

val comma = end_expression (*not implemented yet*)




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