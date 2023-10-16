signature PHI_OPR_STACK = sig

include PHI_OPR_STACK

(* Operator Stack *)


(** Operations **)

(* Function Application *)

val begin_apply : Phi_CP_IDE.eval_cfg -> (string * Position.T) * thm list -> context -> context

val meta_apply : Phi_CP_IDE.eval_cfg
              -> (string * Position.T) * arg_name
              -> (Phi_CP_IDE.eval_cfg * named_arg list * free_param option -> context -> context)
              -> context -> context


(* Block, Parenthesis *)

val begin_block : Position.T -> context -> context

val close_parenthesis : Phi_CP_IDE.eval_cfg * free_param option * bool
                     -> context -> context
val open_parenthesis : arg_name -> context -> context

val comma : Phi_CP_IDE.eval_cfg -> arg_name -> context -> context

(* Operator *)

val push_operator : Phi_CP_IDE.eval_cfg -> operator_info * (string * Position.T) * thm list
                 -> context -> context

val push_meta_operator : Phi_CP_IDE.eval_cfg
                      -> operator_info * (string * Position.T) * free_param option
                       * ( Phi_CP_IDE.eval_cfg * (string * Position.T) * free_param option
                              -> opr_frame list * context_state
                              -> opr_frame list * context_state )
                       -> context -> context

(* End of Expression *)

val end_expression : Phi_CP_IDE.eval_cfg -> int (*precedence*)
                  -> context -> context (*evaluate until the peak precedence in the stacked operators
                                          is less than the given argument*)

(* Misc. *)

val inside_calling_stack : string -> opr_stack -> bool

type operation_name = ( string option (*title of the operation, e.g. operator or function*)
                      * Markup.T (*used in pretty printing*)
                      * (string * Position.T) (*name and position*))

val eval_until : Context.generic -> int * int
              -> Phi_Working_Mode.working_mode
               * bool
               * Phi_CP_IDE.eval_cfg
              -> operation_name
              -> opr_frame list -> context_state
              -> int * operation_name * opr_frame list * context_state

val eval_one_step : Context.generic
                 -> Phi_Working_Mode.working_mode * int * bool * Phi_CP_IDE.eval_cfg
                 -> operation_name * context -> (operation_name * context) option

val end_of_input : unit parser

(*val eval_tokens : context_state -> context_state parser*)

(* declaring operators *)


end

structure Phi_Opr_Stack : PHI_OPR_STACK = struct
open Phi_Opr_Stack

(*** Library * **)

(*** Operator Stack ***)


(** Tools **)

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

type operation_name = (string option * Markup.T * (string * Position.T))

fun bad_syntax (title, m, name) =
  let open Pretty in error (string_of (
    block ( text "Bad Syntax:"
          @ (case title of SOME t => [brk 1, str t] | _ => [])
          @ [brk 1, mark_str (Position.markup (snd name) m, fst name)] )
  )) end

fun chk_complete_eval mode (title, m, name) (ctxt, sequent) =
  if #constr_is_ready mode (Thm.prop_of sequent) then (ctxt, sequent)
  else error (let open Pretty in string_of (
         chunks [block ( text "Evaluation of"
                       @ (case title of SOME t => [brk 1, str t] | _ => [])
                       @ [brk 1, mark_str (Position.markup (snd name) m, fst name)]
                       @ text "fails. There are unsolved antecedents or proof obligations"),
                 Thm.pretty_thm ctxt sequent]
       ) end)

fun end_of_input toks =
  let fun err () = let open Pretty in error (string_of (
                     block (text "End of line expects" @ [brk 1] @ here (Token.pos_of (hd toks)))
                   )) end
   in case toks
   of [] => ((), [])
    | [tok] => if Token.is_eof tok then ((), []) else err ()
    | _ => err ()
  end

(*fun chk_complete_eval' mode (ctxt, sequent) =
  if #constr_is_ready mode (Thm.prop_of sequent) then (ctxt, sequent)
  else error (let open Pretty in string_of (
         chunks [para "Evaluation fails. There are unsolved antecedents or proof obligations",
                 Thm.pretty_thm ctxt sequent]
       ) end)*)

(*num: to be evaluated at most, negative to be unlimited
  returns: number of operations not evaluated yet*)
fun eval_until gen_ctxt (limit, num) (mode, complete_eval, cfg) =
  let val post_app = Phi_CP_IDE.Post_App.invoke gen_ctxt
      fun eval 0 prev_name acts s = (0, prev_name, acts, s)
        | eval num prev_name (acts as (Apply _ :: _)) s = (num, prev_name, acts, s)
        | eval num prev_name (acts as (Begin_Block :: _)) s = (num, prev_name, acts, s)
        | eval num prev_name (acts as (Opr (pr, arity, name, expr_id, rules) :: aR)) (ctxt,sequent)
            = if pr < limit then (num, prev_name, acts, (ctxt,sequent))
              else if pr = limit then bad_syntax prev_name
              else let val name' = (SOME "operator", Markup.operator, name)
                in chk_arity_constraint arity mode name (ctxt,sequent);
                   chk_complete_eval mode prev_name (ctxt,sequent);
                   eval (num-1) name' aR ( (ctxt, Phi_Apply.apply rules ctxt sequent)
                     |> post_app (Phi_CP_IDE.set_expr_id expr_id cfg)
                     |> complete_eval ? chk_complete_eval mode (SOME "operator", Markup.operator, name) )
               end
        | eval num prev_name (acts as (Meta_Opr (pr, arity, name, expr_id, param, meta) :: aR)) s
            = if pr < limit then (num, prev_name, acts, s)
              else if pr = limit then bad_syntax prev_name
              else let val _ = chk_arity_constraint arity mode name (chk_complete_eval mode prev_name s)
                       val name' = (SOME "operator", Markup.operator, name)
                       val (acts',s') = meta (cfg,name,param) (aR,s)
                                     |> apsnd (fn (ctxt,sequent) => (ctxt,sequent)
                                          |> post_app (Phi_CP_IDE.set_expr_id expr_id cfg)
                                          |> complete_eval ? chk_complete_eval mode name'
                                        )
                    in eval (num-1) name' acts' s'
                   end
        | eval num prev_name (acts as (Left_Parenthesis _ :: _)) s = (num, prev_name, acts, s)
        | eval num prev_name (acts as (Meta_Apply _ :: _)) s = (num, prev_name, acts, s)
        | eval num prev_name (acts as (Comma _ :: _)) s = (num, prev_name, acts, s)
        | eval num prev_name [] s = (num, prev_name, [], s)
   in eval num
  end


fun eval_one_step gen_ctxt =
  let val eval_gen = eval_until gen_ctxt
      fun work (mode, precedence, complete_eval, cfg) =
        let val eval = eval_gen (precedence, 1) (mode, complete_eval, cfg)
            fun one_step (prev_name, ((opr,names),s)) =
                  let val (num,prev_name',opr',s') = eval prev_name opr s
                   in if num = 0 then SOME (prev_name', ((opr',names),s')) else NONE
                  end
         in one_step
        end
   in work
  end

(** open \& close parenthesis **)

fun close_parenthesis (cfg, meta_arg, complete_eval) (oprs, s0) =
  let val post_app = Phi_CP_IDE.Post_App.invoke (Context.Proof (fst s0))
      val mode = Phi_Working_Mode.mode1 (fst s0)
      val (actions, arg_name :: arg_names) = oprs

      fun close args (((Apply (name, expr_id, rules, vals_before) :: acts), arg_names), s) =
            s |> Generic_Variable_Access.push_values (vals_before @ chk_no_name args)
              |> Phi_Reasoners.wrap'' (Phi_Apply.apply rules)
              |> post_app (Phi_CP_IDE.set_expr_id expr_id cfg)
              |> complete_eval ? chk_complete_eval mode (SOME "function", Markup.plain_text, name)
              |> pair (acts, arg_names)

        | close args ((Begin_Block :: acts, arg_names), s) =
            s |> Generic_Variable_Access.push_values (chk_no_name args)
              |> Phi_CP_IDE.proof_state_call (Phi_Toplevel.end_block_auto_proof_cmd NONE false)
              |> pair (acts, arg_names)

        | close _ ((Opr _ :: _, _), _) = error "internal bug #91066fd2-8881-422f-bf54-4b3f69879042"
        | close _ ((Meta_Opr _ :: _, _), _) = error "internal bug #10cc33ab-de95-48fb-8b8c-103f2c0110fd"
        | close args ((Left_Parenthesis vals_before :: acts, arg_names), s) =
            ((acts, arg_names), Generic_Variable_Access.push_values (vals_before @ chk_no_name args) s)
        | close args ((Meta_Apply (f, vals_before, (_, pos)) :: acts, arg_names), (ctxt,sequent)) =
            f (cfg, ((NONE, pos), vals_before) :: args, meta_arg) ((acts, arg_names), (ctxt,sequent))
        | close args ((Comma arg :: acts, arg_names), s) =
            close (arg :: args) ((acts, arg_names), s)
        | close _ (([],_), _) = error "parenthesis is inbalanced!"

      val (_, _, actions', (ctxt,sequent)) =
            eval_until (Context.Proof (fst s0)) (0, ~1) (mode, true, cfg)
                       (NONE, Markup.error, ("<internal bug>", Position.none)) actions s0
      val (vals, (ctxt',sequent')) = Generic_Variable_Access.extract_values (~1, true) (ctxt,sequent)
   in close [(arg_name, vals)] ((actions', arg_names), (ctxt', sequent'))
  end

fun open_parenthesis arg_name ((oprs, arg_names), (ctxt,sequent)) =
  let val (vals,(ctxt',sequent')) = Generic_Variable_Access.extract_values (~1, true) (ctxt,sequent)
   in ((Left_Parenthesis vals :: oprs, arg_name :: arg_names), (ctxt', sequent'))
  end

(** Operator **)

fun push_operator cfg ((left_prec,prec,arity_delta),name,rule) ((actions, arg_names), (ctxt,sequent)) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val (_, _, actions', (ctxt',sequent')) =
              eval_until (Context.Proof ctxt) (left_prec, ~1) (mode, true, cfg)
                         (SOME "operator", Markup.operator, name) actions (ctxt,sequent)
      val arity_constraint =
            Option.map (fn x => x + Generic_Variable_Access.number_of_values
                                      (#spec_of mode (Thm.prop_of sequent')))
                       arity_delta
   in ((Opr (prec,arity_constraint,name,#id cfg,rule) :: actions', arg_names), (ctxt',sequent'))
  end

fun push_meta_operator cfg ((left_prec,prec,arity_delta),name,param,meta)
                       ((actions, arg_names), (ctxt,sequent)) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val (_, _, actions', (ctxt',sequent')) =
              eval_until (Context.Proof ctxt) (left_prec, ~1) (mode, true, cfg)
                         (SOME "operator", Markup.operator, name) actions (ctxt,sequent)
      val arity_constraint =
            Option.map (fn x => x + Generic_Variable_Access.number_of_values (
                                        #spec_of (Phi_Working_Mode.mode1 ctxt') (Thm.prop_of sequent')))
                       arity_delta
   in ((Meta_Opr (prec,arity_constraint,name,#id cfg,param,meta) :: actions', arg_names), (ctxt',sequent'))
  end

(** End of Expression **)

fun end_expression cfg precedence ((actions, arg_names), s) =
  let val mode = Phi_Working_Mode.mode1 (fst s)
      val (_, _, actions', s') =
          eval_until (Context.Proof (fst s)) (precedence, ~1) (mode, true, cfg)
                     (NONE, Markup.plain_text, ("<end-of-expr>", Position.none)) actions s
   in ((actions', arg_names), s')
  end

(** Comma **)

fun comma cfg next_arg_name ((actions, arg_name :: arg_names), s) =
  let val mode = Phi_Working_Mode.mode1 (fst s)
      val opr_name = (SOME "operator", Markup.operator, (",", snd next_arg_name))
      fun chk_actions (Left_Parenthesis _ :: _) = ()
        | chk_actions (Meta_Apply _ :: _) = ()
        | chk_actions (Apply _ :: _) = ()
        | chk_actions (Begin_Block :: _) = bad_syntax opr_name
        | chk_actions (Comma _ :: _ ) = ()
        | chk_actions (_ :: L) = chk_actions L
        | chk_actions [] = bad_syntax opr_name
      val _ = chk_actions actions
      val (_, _, actions', (ctxt,sequent)) =
                eval_until (Context.Proof (fst s)) (0, ~1) (mode, true, cfg) opr_name actions s
      val (vals,(ctxt',sequent')) = Generic_Variable_Access.extract_values (~1, true) (ctxt,sequent)
   in ((Comma (arg_name, vals) :: actions', next_arg_name :: arg_names), (ctxt', sequent'))
  end

(** Function Application **)

(*
fun do_application (cfg, complete_eval) rules stat =
      stat
   |> end_expression cfg @{priority %\<phi>lang_app}
   |> apsnd (fn s => s
              |> Phi_Reasoners.wrap'' (Phi_Apply.apply rules)
              |> Phi_CP_IDE.Post_App.invoke (Context.Proof (fst s)) cfg
              |> complete_eval ? chk_complete_eval mode (SOME "function", Markup.plain_text, name))
*)

fun begin_apply cfg (name, rules) ((actions, arg_names), (ctxt,sequent)) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val fun_name = (SOME "function", Markup.plain_text, name)
      val (_, _, actions', (ctxt',sequent')) =
              eval_until (Context.Proof ctxt) (@{priority %\<phi>lang_app}, ~1) (mode, true, cfg) fun_name actions (ctxt,sequent)
      val (vals,(ctxt'',sequent'')) = Generic_Variable_Access.extract_values (~1, true) (ctxt',sequent')
   in ((Apply (name, #id cfg, rules, vals) :: actions', (NONE, snd name) :: arg_names), (ctxt'', sequent''))
  end

fun meta_apply cfg (pos,arg_name) f ((actions, arg_names), (ctxt,sequent)) =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val fun_name = (SOME "function", Markup.plain_text, pos)
      val (_, _, actions', (ctxt',sequent')) =
              eval_until (Context.Proof ctxt) (@{priority %\<phi>lang_app}, ~1) (mode, true, cfg) fun_name actions (ctxt,sequent)
      val (vals,(ctxt'',sequent'')) = Generic_Variable_Access.extract_values (~1, true) (ctxt',sequent')
   in ((Meta_Apply (f, vals, pos) :: actions', arg_name :: arg_names), (ctxt'', sequent''))
  end

fun begin_block pos ((actions, arg_names), s) =
      ((Begin_Block :: actions, (NONE, pos) :: arg_names), s)

(** Misc. Tools **)

fun inside_calling_stack name (actions, _) =
  let fun is_during (Apply ((s, _), _, _, _) :: _) = (s = name)
        | is_during (Meta_Apply (_, _, (s, _)) :: _) = s = name
        | is_during (Begin_Block :: _) = false
        | is_during (Comma _ :: L) = is_during L
        | is_during (Opr _ :: L) = is_during L
        | is_during (Meta_Opr _ :: L) = is_during L
        | is_during (Left_Parenthesis _ :: L) = is_during L
        | is_during [] = false
   in is_during actions
  end





(*** Prefix, Infix, Postfix operators  ***)



(*** Hooks, Control of Lines and Statements ***)









end