signature GENERIC_ELEMENT_ACCESS = sig

include GENERIC_ELEMENT_ACCESS

structure Agg_Path_Encoders : HANDLERS
structure Agg_Constructors : HANDLERS

val mk_element_index_input : thm list -> term

val gen_access : string * string
              -> (string * Position.T) * Phi_Opr_Stack.arg_name
              -> Phi_CP_IDE.eval_cfg -> Phi_Opr_Stack.context -> Phi_Opr_Stack.context

val gen_constructor : string -> (string * Position.T) * Phi_Opr_Stack.arg_name
                   -> Phi_CP_IDE.eval_cfg -> Phi_Opr_Stack.context -> Phi_Opr_Stack.context

exception Bracket_Opr_Read
exception Bracket_Opr_Write of Position.T

val dot_triangle_opr : Phi_CP_IDE.eval_cfg * (string * Position.T) * Phi_Opr_Stack.free_param option
          -> Phi_Opr_Stack.opr_frame list * context_state
          -> Phi_Opr_Stack.opr_frame list * context_state

val dot_triangle_assignment : Phi_CP_IDE.eval_cfg * (string * Position.T) * Phi_Opr_Stack.free_param option
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
      fun pattern_of (Trueprop $ ((H1 as Const (\<^const_name>\<open>Satisfaction\<close>, _)) $ V $ S))
            = let val i = Int.max (maxidx_of_term H1, maxidx_of_term V) + 1
               in Trueprop $ (\<^const>\<open>Action_Tag\<close> $ (H1 $ V $ Var(("S",i), fastype_of S))
                                                $ \<^const>\<open>\<A>parse_eleidx\<close>)
              end
        | pattern_of X =
            raise TERM ("bad rule Y6uYVPRLRYeA3oqKVPXWGQ", [X])
      val reasoning_rules = map (fn (pos, rule) =>
            ([rule RS @{thm Action_Tag_I[where A=\<open>\<A>parse_eleidx\<close>]}], pos,
             Phi_Reasoner.NORMAL_LOCAL_CUT', SOME @{reasoner_group %\<A>parse_eleidx},
             [(pattern_of (Thm.prop_of rule), NONE)], [], NONE)
          ) args
      val thy = Proof_Context.theory_of ctxt
      val pats = map (pattern_of o Thm.prop_of o snd) args
   in ctxt
   |> Context.proof_map (
        Phi_Reasoner.del_reasoners [\<^pattern_prop>\<open>(_ :: VAL) \<Turnstile> _ @action \<A>parse_eleidx\<close>]
          (fn r => exists (fn pat => Pattern.matches thy (pat, #name r)) pats))
   |> Context.proof_map (Phi_Reasoner.add_rules reasoning_rules)
   |> pair idx_input
  end

fun gen_access named_thm_of_rules pos_and_first_args cfg stat =
  let fun invoke (args, rules_name) (oprs, (ctxt,sequent)) =
        let val (idx_input, ctxt') = mk_element_index_input_internal args ctxt
            val rules = Phi_App_Rules.get_overloadings ctxt' rules_name
                      |> map (Drule.infer_instantiate ctxt' [(("input_index", 0), Thm.cterm_of ctxt' idx_input)])
         in (oprs, Phi_Reasoners.wrap'' (Phi_Apply.apply rules) (ctxt', sequent))
        end
      fun invoke' (_, args, SOME Bracket_Opr_Read) opr_ctxt =
            invoke (map chk_arg args, fst named_thm_of_rules) opr_ctxt
        | invoke' (cfg, args, SOME (Bracket_Opr_Write pos)) opr_ctxt=
            Phi_Opr_Stack.push_meta_operator cfg
                ((1001,@{priority %\<phi>lang_assignment_opr},SOME 1), (":=", pos), NONE,
                 K (invoke (map chk_arg args, snd named_thm_of_rules))) opr_ctxt
        | invoke' _ _ =
            error "Bad free_arg in Generic_Element_Access"
      fun invoke'3 (cfg, (_, vals_before) :: args, free_arg) (opstack, stat) =
            if length vals_before = 0
            then error ("Bad Syntax: The operand of aggregate access is absent. " ^
                         Position.here (snd (fst pos_and_first_args)))
            else invoke' (cfg, args, free_arg) (opstack, Generic_Variable_Access.push_values vals_before stat)
        | invoke'3 _ _ = error "BUG qgjNc1ebSHCtqRNU7y9/Cw"
   in Phi_Opr_Stack.meta_apply cfg pos_and_first_args invoke'3 stat
  end

structure Agg_Constructors = Handlers (
  type arg = string (*user's source hint, indicating which object to be constructed*)
           * Phi_Opr_Stack.named_arg list * context_state
  type ret = Proof.context * cterm (*constructor*) * term list (*arguments*)
)

fun gen_constructor kind pos_and_first_args cfg stat =
  let fun invoke (_, (_, vals_before) :: args0, free_arg) (oprs, (ctxt0, sequent0)) =
        let val _ = case free_arg of NONE => ()
                       | _ => error "Bad free_arg 1ibvpcveSdePAKyDJuJefA"
            val (ctxt,sequent) = Generic_Variable_Access.push_values vals_before (ctxt0,sequent0)
            val kind' = if kind = "" then "structure" else kind
            val (ctxt', ctor, args') = Agg_Constructors.invoke (Context.Proof ctxt)
                                                               (kind, args0, (ctxt,sequent))
                      |> (fn SOME ret => ret
                           | NONE => error ("Don't know how to construct " ^ kind' ^
                                              " using the given arguments."))
            val args = Thm.cterm_of ctxt (HOLogic.mk_list \<^typ>\<open>VAL \<phi>arg\<close> args')

            val pos_rules = map_index (fn (i,((name, pos), rules)) =>
                  let val sym = case name
                                  of SOME str =>
                                        \<^Const>\<open>Inl \<^Type>\<open>symbol\<close> \<^Type>\<open>nat\<close>\<close>
                                                $ Phi_Tool_Symbol.mk_symbol str
                                   | NONE =>
                                        \<^Const>\<open>Inr \<^Type>\<open>nat\<close> \<^Type>\<open>symbol\<close>\<close> $ HOLogic.mk_nat i
                      val csym = Thm.cterm_of ctxt (\<^Const>\<open>\<A>ctr_arg\<close> $ sym)
                      val rules' = map (fn rule =>
                            let val tag = Drule.infer_instantiate ctxt
                                              [(("A",0),csym)] @{thm' Action_Tag_I}
                             in rule RS tag
                            end ) rules
                   in (pos, rules')
                  end ) args0

            val ctxt'' = Context.proof_map (
                    Generic_Variable_Access.register_value_spec_thms_no_dup pos_rules
                  ) ctxt'
            val rule' =
                @{thm' op_construct_aggregate_\<phi>app}
                  |> Thm.transfer' ctxt''
                  |> Thm.instantiate (TVars.empty, Vars.make [
                        ((("constructor", 0), \<^typ>\<open>VAL list \<Rightarrow> VAL\<close>), ctor),
                        ((("args", 0), \<^typ>\<open>VAL \<phi>arg list\<close>), args)
                      ])
                  |> Phi_Reasoner.reason1 (fn () => "Fail to construct " ^ kind') NONE (SOME 1) ctxt''
         in (oprs, (ctxt' (*not ctxt''!*), Phi_Apply.apply [rule'] ctxt'' sequent))
        end
        | invoke _ _ = error "BUG 2CG4WNzYQqirWulpFUkQQA"
   in Phi_Opr_Stack.meta_apply cfg pos_and_first_args invoke stat
  end


fun is_empty (Const (\<^const_name>\<open>Nil\<close>, _)) = true
  | is_empty _ = false


fun gen_dot_triangle_opr F front_arity (cfg, (name, pos), _) (stack, (ctxt0,sequent0)) =
  let val (front_args, (ctxt, sequent)) =
            Generic_Variable_Access.extract_values (front_arity, true) (ctxt0,sequent0)
      fun collect (ret, Phi_Opr_Stack.Meta_Opr (_, _, ("\<tribullet>", pos), _, _, _) :: L) = collect (pos :: ret, L)
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
   in F (cfg, (name, pos), stack', idx_input, ctxt'3, sequent'3)
  end

fun err_assignment pos =
  error ("Bad Syntax: The assignment does not assign to a (generic) variable." ^
         Position.here pos)

val dot_triangle_assignment =
  gen_dot_triangle_opr (fn (_, (_, pos), stack, idx_input, ctxt, sequent) =>
    let val (stack', vname, pos) =
          case stack
            of (Phi_Opr_Stack.Meta_Opr (_, _, ("$", pos), _, SOME (Phi_Opr_Stack.String_Param vname), _) :: stack')
                => (stack', vname, pos)
             | _ => err_assignment pos
     in (stack', Generic_Variable_Access.assignment_cmd [(NONE, (Binding.make (vname, pos), idx_input))] (ctxt, sequent))
    end
  ) 1
 

val dot_triangle_opr =
  gen_dot_triangle_opr (fn (cfg, _, stack', idx_input, ctxt'3, sequent'3) =>
    let val post_app = Phi_CP_IDE.Post_App.invoke (Context.Proof ctxt'3)
        val (idx_input', ctxt'4, sequent'4, stack'') =
          case stack'

            of (Phi_Opr_Stack.Meta_Opr (_, _, ("$", _), _, SOME (Phi_Opr_Stack.String_Param vname), _) :: stack'')
                => let val ctxt'3' = Generic_Element_Access.enable_report_unprocessed_element_index ctxt'3
                       val (ctxt'4, sequent'4) = (ctxt'3', sequent'3)
                              |> Phi_Reasoners.wrap'' (Generic_Variable_Access.get_value vname idx_input)
                              |> post_app cfg
                       val idx_input' = Generic_Element_Access.get_unprocessed_element_index ctxt'4
                    in (idx_input', ctxt'4, sequent'4, stack'')
                   end
             | _ => (idx_input, ctxt'3, sequent'3, stack')
  
        val rules = Phi_App_Rules.get_overloadings ctxt'4 @{\<phi>overloading "\<tribullet>"}
        fun process_index idx s =
          if is_empty (Thm.term_of idx)
          then s |> apfst Generic_Element_Access.stop_reporting_unprocessed_element_index
          else let val rules' = map (Drule.infer_instantiate ctxt'4 [(("input_index", 0), idx)]) rules
                   val s' = s
                          |> apfst Generic_Element_Access.enable_report_unprocessed_element_index
                          |> Phi_Reasoners.wrap'' (Phi_Apply.apply rules')
                          |> post_app cfg
                   handle THM ("Application Fail", _, _) =>
                      Generic_Element_Access.error_unprocessed_element_index (fst s) idx
                in process_index (Generic_Element_Access.get_unprocessed_element_index (fst s')) s'
               end
     in (stack'', process_index idx_input' (ctxt'4, sequent'4))
    end
  ) 0


end