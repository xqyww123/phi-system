signature GENERIC_ELEMENT_ACCESS = sig

include GENERIC_ELEMENT_ACCESS

structure Agg_Path_Encoders : HANDLERS
structure Agg_Constructors : HANDLERS

val mk_element_index_input : thm list -> term

val gen_access : string * string -> (string * Position.T) * Phi_Opr_Stack.arg_name -> context_state -> context_state
val gen_constructor : string -> (string * Position.T) * Phi_Opr_Stack.arg_name
                   -> context_state -> context_state

exception Bracket_Opr_Read
exception Bracket_Opr_Write of Position.T

val dot_triangle_opr : (string * Position.T) * Phi_Opr_Stack.free_param
          -> Phi_Opr_Stack.opr_frame list * context_state
          -> Phi_Opr_Stack.opr_frame list * context_state

val dot_triangle_assignment : (string * Position.T) * Phi_Opr_Stack.free_param
          -> Phi_Opr_Stack.opr_frame list * context_state
          -> Phi_Opr_Stack.opr_frame list * context_state

val err_assignment : Position.T -> 'a

end

structure Generic_Element_Access : GENERIC_ELEMENT_ACCESS = struct

open Generic_Element_Access

fun gen_mk_element_index_input f args =
  let val raw_path' = map (fn rule =>
            HOLogic.mk_prod (Phi_Syntax.dest_satisfaction (Thm.prop_of (f rule)))) args
   in HOLogic.mk_list \<^typ>\<open>VAL \<times> VAL set\<close> raw_path'
  end

val mk_element_index_input = gen_mk_element_index_input I

structure Agg_Path_Encoders = Handlers (
  type arg = (Position.T * thm) list * context_state
  type ret = (Proof.context * cterm (*raw index*))
)

exception Bracket_Opr_Read
exception Bracket_Opr_Write of Position.T

fun chk_arg ((SOME _, pos), _) =
      error ("named argument is not supported here " ^ Position.here pos)
  | chk_arg ((_, pos), _ :: _ :: _) =
      error (Position.here pos ^ " the expression returns more than one value")
  | chk_arg ((_, pos), []) =
      error (Position.here pos ^ " the expression returns no value!")
  | chk_arg ((_, pos), [v]) = (pos, v)

fun mk_element_index_input_internal args0 ctxt =
  let val idx_input = gen_mk_element_index_input snd args0
      val args = distinct (fn ((_,rule1),(_,rule2)) =>
            pointer_eq (rule1, rule2) orelse
            Thm.concl_of rule1 aconv Thm.concl_of rule2) args0
      fun pattern_of (Trueprop $ ((H1 as Const (\<^const_name>\<open>Set.member\<close>, _)) $ V $ S))
            = let val i = Int.max (maxidx_of_term H1, maxidx_of_term V) + 1
               in \<^const>\<open>Action_Tag\<close> $ (Trueprop $ (H1 $ V $ Var(("S",i), fastype_of S)))
                                    $ \<^const>\<open>parse_element_index_input\<close>
              end
        | pattern_of X =
            raise TERM ("bad rule #c419df7c-c917-4605-a129-bb914d5716bf", [X])
      val reasoning_rules = map (fn (pos, rule) =>
            ([rule RS @{thm Action_Tag_I[where A=\<open>parse_element_index_input\<close>]}], pos,
             Phi_Reasoner.LOCAL_CUT, 1000, [(pattern_of (Thm.prop_of rule), NONE)], [], NONE)
          ) args
      val thy = Proof_Context.theory_of ctxt
      val pats = map (pattern_of o Thm.prop_of o snd) args
   in ctxt
   |> Context.proof_map (
        Phi_Reasoner.del_reasoners \<^pattern_prop>\<open>(_ :: VAL) \<in> _ @action parse_element_index_input\<close>
          (fn r => exists (fn pat => Pattern.matches thy (pat, #name r)) pats))
   |> Context.proof_map (
        Phi_Reasoner.add_intro_rules reasoning_rules)
   |> pair idx_input
  end

fun gen_access named_thm_of_rules pos_and_first_args stat =
  let fun invoke (args, rules_name) (opstack, (ctxt,sequent)) =
        let val (idx_input, ctxt') = mk_element_index_input_internal args ctxt
            val rules = Named_Theorems.get ctxt' rules_name
                      |> map (Drule.infer_instantiate ctxt' [(("input_index", 0), Thm.cterm_of ctxt' idx_input)])
         in (opstack, Phi_Apply.apply rules (ctxt', sequent))
        end
      fun invoke' (args, SOME Bracket_Opr_Read) (opstack, stat) =
            invoke (map chk_arg args, fst named_thm_of_rules) (opstack, stat)
        | invoke' (args, SOME (Bracket_Opr_Write pos)) (opstack, stat) =
            let val arity = 1 + Generic_Variable_Access.number_of_values
                                    (#spec_of Phi_Working_Mode.programming (Thm.prop_of (snd stat)))
             in (Phi_Opr_Stack.Meta_Opr (50, SOME arity, (":=", pos), NONE,
                      K (invoke (map chk_arg args, snd named_thm_of_rules))
                   ) :: opstack,
                 stat)
            end
        | invoke' _ _ =
            error "Bad free_arg in Generic_Element_Access"
      fun invoke'3 ((_, vals_before) :: args, free_arg) (opstack, stat) =
            if length vals_before = 0
            then error ("Bad Syntax: The operand of aggregate access is absent. " ^
                         Position.here (snd (fst pos_and_first_args)))
            else invoke' (args, free_arg) (opstack, Generic_Variable_Access.push_values vals_before stat)
        | invoke'3 _ _ = error "internal bug #a2a96e04-14d6-4b66-9c2e-053e5c2bfcbe"
   in Phi_Opr_Stack.meta_apply pos_and_first_args invoke'3 stat
  end

structure Agg_Constructors = Handlers (
  type arg = string (*user's source hint, indicating which object to be constructed*)
           * Phi_Opr_Stack.named_arg list * context_state
  type ret = Proof.context * cterm (*constructor*) * term list (*arguments*)
)

fun gen_constructor kind pos_and_first_args stat =
  let fun invoke ((_, vals_before) :: args0, free_arg) (oprs, (ctxt0, sequent0)) =
        let val _ = case free_arg of NONE => ()
                       | _ => error "Bad free_arg: a32d7843-538e-4ddc-af95-ea71514cc0ad"
            val (ctxt,sequent) = Generic_Variable_Access.push_values vals_before (ctxt0,sequent0)
            val kind' = if kind = "" then "structure" else kind
            val (ctxt', ctor, args') = Agg_Constructors.invoke (Context.Proof ctxt)
                                                               (kind, args0, (ctxt,sequent))
                      |> (fn SOME ret => ret
                           | NONE => error ("Don't know how to construct " ^ kind' ^
                                              " using the given arguments."))
            val args = Thm.cterm_of ctxt (HOLogic.mk_list \<^typ>\<open>VAL \<phi>arg\<close> args')
            val reasoning_rules =
                  maps (fn ((_, pos), rules) =>
                    map (fn rule => (rule,pos,Phi_Reasoner.LOCAL_CUT,1000)) rules) args0
            val ctxt'' = Context.proof_map (Phi_Local_Value.add_reasoning_rules reasoning_rules) ctxt'
            val (ctxt'3, rule') =
                @{thm op_construct_aggregate_\<phi>app}
                  |> Thm.instantiate (TVars.empty, Vars.make [
                        ((("constructor", 0), \<^typ>\<open>VAL \<phi>arg list \<Rightarrow> VAL\<close>), ctor),
                        ((("args", 0), \<^typ>\<open>VAL \<phi>arg list\<close>), args)
                      ])
                  |> pair ctxt''
                  |> Phi_Reasoner.reason (SOME 1)
                  |> (fn SOME ret => ret
                       | NONE => error ("Fail to construct " ^ kind'))
         in (oprs, Phi_Apply.apply [rule'] (ctxt'3, sequent))
        end
        | invoke _ _ = error "internal bug #5330d2f8-c5e3-46ae-9b45-5ae9550f037d"
   in Phi_Opr_Stack.meta_apply pos_and_first_args invoke stat
  end


fun is_empty (Const (\<^const_name>\<open>Nil\<close>, _)) = true
  | is_empty _ = false


fun gen_dot_triangle_opr F front_arity ((name, pos), _) (stack, (ctxt0,sequent0)) =
  let val (front_args, (ctxt, sequent)) =
            Generic_Variable_Access.extract_values (front_arity, true) (ctxt0,sequent0)
      fun collect (ret, Phi_Opr_Stack.Meta_Opr (_, _, ("\<tribullet>", pos), _, _) :: L) = collect (pos :: ret, L)
        | collect ret_L = ret_L
      val (poss, stack') = collect ((if name = "\<tribullet>" then [pos] else []), stack)
      val actual = Generic_Variable_Access.number_of_values (
                        #spec_of Phi_Working_Mode.programming (Thm.prop_of sequent))
      val _ = if actual < length poss
              then error ("Unbalanced operator stack " ^ Position.here pos) else ()
      val (args', (ctxt',sequent')) =
              Generic_Variable_Access.extract_values (length poss, true) (ctxt,sequent)
      val args = poss ~~ args'

      val (idx_input'0, ctxt'2) = mk_element_index_input_internal args ctxt'
      val idx_input = Thm.cterm_of ctxt'2 idx_input'0
      val (ctxt'3, sequent'3) = Generic_Variable_Access.push_values front_args (ctxt'2,sequent')
   in F ((name, pos), stack', idx_input, ctxt'3, sequent'3)
  end

fun err_assignment pos =
  error ("Bad Syntax: The assignment does not assign to a (generic) variable." ^
         Position.here pos)

val dot_triangle_assignment =
  gen_dot_triangle_opr (fn ((_, pos), stack, idx_input, ctxt, sequent) =>
    let val (stack', vname, pos) =
          case stack
            of (Phi_Opr_Stack.Meta_Opr (_, _, ("$", pos), SOME (Phi_Opr_Stack.String_Param vname), _) :: stack')
                => (stack', vname, pos)
             | _ => err_assignment pos
     in (stack', Generic_Variable_Access.assignment_cmd [(NONE, (Binding.make (vname, pos), idx_input))] (ctxt, sequent))
    end
  ) 1
 

val dot_triangle_opr =
  gen_dot_triangle_opr (fn (_, stack', idx_input, ctxt'3, sequent'3) =>
    let val (idx_input', ctxt'4, sequent'4, stack'') =
          case stack'
            of (Phi_Opr_Stack.Meta_Opr (_, _, ("$", pos), SOME (Phi_Opr_Stack.String_Param vname), _) :: stack'')
                => let val ctxt'3' = Generic_Element_Access.enable_report_unprocessed_element_index ctxt'3
                       val (ctxt'4, sequent'4) = Generic_Variable_Access.get_value vname idx_input  (ctxt'3', sequent'3)
                                              |> Phi_Processor.process_all_antecedents NONE
                       val idx_input' = Generic_Element_Access.get_unprocessed_element_index ctxt'4
                    in (idx_input', ctxt'4, sequent'4, stack'')
                   end
             | _ => (idx_input, ctxt'3, sequent'3, stack')
  
        val rules = Named_Theorems.get ctxt'4 \<^named_theorems>\<open>\<tribullet>_\<phi>app\<close>
        fun process_index idx s =
          if is_empty (Thm.term_of idx)
          then s |> apfst Generic_Element_Access.stop_reporting_unprocessed_element_index
          else let val rules' = map (Drule.infer_instantiate ctxt'4 [(("input_index", 0), idx)]) rules
                   val s' = s
                          |> apfst Generic_Element_Access.enable_report_unprocessed_element_index
                          |> Phi_Apply.apply rules'
                          |> Phi_Processor.process_all_antecedents NONE
                in process_index (Generic_Element_Access.get_unprocessed_element_index (fst s')) s'
               end
     in (stack'', process_index idx_input' (ctxt'4, sequent'4))
    end
  ) 0


end