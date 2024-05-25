signature GENERIC_ELEMENT_ACCESS = sig

include GENERIC_ELEMENT_ACCESS

structure Agg_Path_Encoders : HANDLERS
structure Agg_Constructors : HANDLERS

val mk_dot_opr : Position.T -> Phi_Opr_Stack.opr_frame list -> Phi_Opr_Stack.meta_operator

val mk_element_index_input : thm list -> term

val gen_access : string * string
              -> (string * Position.T) * Phi_Opr_Stack.arg_name
              -> Phi_CP_IDE.eval_cfg -> Phi_Opr_Stack.context -> Phi_Opr_Stack.context

val gen_constructor : string -> (string * Position.T) * Phi_Opr_Stack.arg_name
                   -> Phi_CP_IDE.eval_cfg -> Phi_Opr_Stack.context -> Phi_Opr_Stack.context

exception Bracket_Opr_Read
exception Bracket_Opr_Write of Position.T

val dot_triangle_opr : Phi_Opr_Stack.meta_opr
val dot_triangle_update_opr : Phi_Opr_Stack.meta_opr
val dot_triangle_assignment : Phi_Opr_Stack.meta_opr

val open_bracket_opr : Position.T -> Phi_CP_IDE.eval_cfg -> Phi_Opr_Stack.context -> Phi_Opr_Stack.context
val close_bracket : Position.T -> Phi_CP_IDE.eval_cfg -> Phi_Opr_Stack.context -> Phi_Opr_Stack.context

val err_assignment : Position.T -> 'a

end

structure Generic_Element_Access : GENERIC_ELEMENT_ACCESS = struct

open Generic_Element_Access

fun gen_mk_element_index_input f args =
  let val raw_path' = map (fn rule =>
            HOLogic.mk_prod (Phi_Syntax.dest_satisfaction (Thm.prop_of (f rule)))) args
   in HOLogic.mk_list \<^typ>\<open>VAL \<times> VAL set\<close> raw_path'
  end

val prod_VAL_VALset = \<^cterm>\<open>Pair :: VAL \<Rightarrow> VAL set \<Rightarrow> VAL \<times> VAL set\<close>
fun mk_list_c ts =
  let
    val Nil = \<^cterm>\<open>Nil :: (VAL \<times> VAL set) list\<close>
    fun Cons t u = Thm.apply
      (Thm.apply \<^cterm>\<open>Cons :: (VAL \<times> VAL set) \<Rightarrow> (VAL \<times> VAL set) list \<Rightarrow> (VAL \<times> VAL set) list\<close> t) u
  in fold_rev Cons ts Nil end;

fun gen_mk_element_index_input_c f args =
  let val raw_path' = map (fn rule =>
            case Phi_Syntax.dest_satisfaction_c (Thm.cprop_of (f rule))
              of (A,B) => Thm.apply (Thm.apply prod_VAL_VALset A) B) args
   in mk_list_c raw_path'
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
  let val idx_input = gen_mk_element_index_input_c snd args0
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
   |> Config.map Phi_Reasoner.trace (fn i => i - 1)
   |> Context.proof_map (
        Phi_Reasoner.del_reasoners [\<^pattern_prop>\<open>(_ :: VAL) \<Turnstile> _ @tag \<A>parse_eleidx\<close>]
          (fn r => exists (fn pat => Pattern.matches thy (pat, #name r)) pats))
   |> Context.proof_map (Phi_Reasoner.add_rules reasoning_rules)
   |> Config.restore Phi_Reasoner.trace ctxt
   |> pair idx_input
  end

fun is_empty (Const (\<^const_name>\<open>Nil\<close>, _)) = true
  | is_empty _ = false

exception RW_RETURN of Phi_Opr_Stack.opr_frame list * context_state
fun rw_access (read_rule_name, write_rule_name) read_or_write idx_input cfg (oprs, (ctxt,sequent)) =
  let val post_app = Phi_CP_IDE.Post_App.invoke (Context.Proof ctxt)
      val (oprs'1, (idx_input', (ctxt'1, sequent'1))) =
        case oprs
          of (Phi_Opr_Stack.Meta_Opr (_, _, ("$", _), _, SOME (Phi_Opr_Stack.String_Param vname), _, _) :: oprs')
              => let
                 fun attempt prohibit_remains_idx idx F (oprs,s) =
                    let val s' = s
                            |> apfst (Generic_Element_Access.enable_report_unprocessed_element_index prohibit_remains_idx)
                            |> F idx
                            |> post_app cfg
                          handle THM ("Application Fail", _, _) =>
                            raise Generic_Element_Access.Remaining_Eleidx idx
                        val (idx', hook) = Generic_Element_Access.get_unprocessed_element_index (fst s')
                                     |> the_default (idx, Generic_Element_Access.EIHook_none)
                        val (oprs',s'') = if is_empty (Thm.term_of idx')
                                          then Generic_Element_Access.evaluate_hook hook read_or_write (oprs,s')
                                          else (oprs, s')
                        val _ = if prohibit_remains_idx andalso not (is_empty (Thm.term_of idx'))
                                then raise Generic_Element_Access.Remaining_Eleidx idx'
                                else ()
                     in (oprs', (idx', s''))
                    end
              in if read_or_write
                 then attempt false idx_input
                            (Phi_Reasoners.wrap'' o Generic_Variable_Access.get_value vname)
                            (oprs', (ctxt,sequent))
                 else attempt false empty_input
                                (Phi_Reasoners.wrap'' o Generic_Variable_Access.get_value vname)
                                (oprs', (ctxt,sequent))
                   |> (fn (oprs',(_, s')) => (oprs', (idx_input, s'))) 
                (*let (*the commented programs allows ":=" to assign / alter a variable *)
                      fun fallback () =
                            attempt false empty_input
                                (Phi_Reasoners.wrap'' o Generic_Variable_Access.get_value vname)
                                (ctxt,sequent)
                              |> (fn (_, s') => (oprs', (idx_input, s')))
                   in attempt true idx_input
                            (fn idx => Generic_Variable_Access.assignment' [(NONE, (Binding.make (vname, pos), idx))])
                            (ctxt,sequent)
                        |> (fn idx_stat => raise RW_RETURN (oprs', snd idx_stat))
                      handle Generic_Element_Access.Remaining_Eleidx _ => fallback()
                           | Generic_Variable_Access.ASSIGN_FAIL _ => fallback()
                  end*)
             end
           | _ => (oprs, (idx_input, (ctxt, sequent)))

      val r_rules = Phi_App_Rules.get_overloadings ctxt'1 read_rule_name
      val w_rules = if read_or_write then []
                    else Phi_App_Rules.get_overloadings ctxt'1 write_rule_name
      fun process_index (oprs, (idx, s)) =
         let val finish = apfst Generic_Element_Access.stop_reporting_unprocessed_element_index
             fun loopback_w (oprs, (idx, s)) =
                if is_empty (Thm.term_of idx)
                then (oprs, finish s)
                else error "Bad configuration of rules: still has unprocess element indexes"
             fun loopback_r (oprs, (idx, s)) =
                if is_empty (Thm.term_of idx)
                then (oprs, finish s)
                else process_index (oprs, (idx, s))
             fun attempt prohibit_remains_idx rules0 (oprs, s) =
                let val rules = map (Drule.infer_instantiate ctxt'1 [(("input_index", 0), idx)]) rules0
                    val s' = s
                         |> apfst (Generic_Element_Access.enable_report_unprocessed_element_index prohibit_remains_idx)
                         |> Phi_Reasoners.wrap'' (Phi_Apply.apply rules)
                         |> post_app cfg
                    handle THM ("Application Fail", _, _) =>
                        raise Generic_Element_Access.Remaining_Eleidx idx
                    val (idx', hook) = Generic_Element_Access.get_unprocessed_element_index (fst s')
                            |> the_default (idx, Generic_Element_Access.EIHook_none)
                    val (oprs',s'') =
                            if is_empty (Thm.term_of idx')
                            then Generic_Element_Access.evaluate_hook hook read_or_write (oprs,s')
                            else (oprs, s')
                    val _ = if prohibit_remains_idx andalso not (is_empty (Thm.term_of idx'))
                            then raise Generic_Element_Access.Remaining_Eleidx idx'
                            else ()
                 in (oprs', (idx', s''))
                end
           (*fun assert_nonempty idx =
                if is_empty (Thm.term_of idx) then idx
                else error "Bad configuration of access rules: the writer cannot process all element index while\
                            \ the reader can..." *)
          in if read_or_write
             then loopback_r (attempt false r_rules (oprs, s))
             else (loopback_w (attempt true w_rules (oprs, s))
                   handle Generic_Element_Access.Remaining_Eleidx _ =>
                      process_index (attempt false r_rules (oprs, s)))
         end
         handle Generic_Element_Access.Remaining_Eleidx idx =>
            Generic_Element_Access.error_unprocessed_element_index (fst s) idx
   in process_index (oprs'1, (idx_input', (ctxt'1, sequent'1)))
  end
  handle RW_RETURN ret => ret

fun gen_access named_thm_of_rules pos_and_first_args cfg stat =
  let fun invoke read_or_write args (oprs, (ctxt,sequent)) =
        let val (idx_input, ctxt') = mk_element_index_input_internal args ctxt
         in rw_access named_thm_of_rules read_or_write idx_input cfg (oprs, (ctxt',sequent))
        end
      fun wrap f ((a,b),c) =
        let val (a',c') = f (a,c)
         in ((a',b),c')
        end
        (*let val (idx_input, ctxt') = mk_element_index_input_internal args ctxt
            val rules = Phi_App_Rules.get_overloadings ctxt'
                            ((if read_or_write then fst else snd) named_thm_of_rules)
                      |> map (Drule.infer_instantiate ctxt' [(("input_index", 0), idx_input)])
         in (oprs, Phi_Reasoners.wrap'' (Phi_Apply.apply1 rules) (ctxt', sequent))
        end*)
      fun invoke' (_, args, SOME Bracket_Opr_Read) vals opr_ctxt = opr_ctxt
            |> apsnd (Generic_Variable_Access.push_values vals)
            |> wrap (invoke true (map chk_arg args))
        | invoke' (cfg, args, SOME (Bracket_Opr_Write pos)) vals opr_ctxt=
            Phi_Opr_Stack.push_meta_operator cfg
                ((1001,@{priority %\<phi>lang_update_opr}, (0,1)), (":=", pos), NONE,
                 K ( apsnd (Generic_Variable_Access.push_values vals)
                  #> invoke false (map chk_arg args) )) opr_ctxt
        | invoke' _ _ _ =
            error "Bad free_arg in Generic_Element_Access"
      fun invoke'3 (cfg, (_, vals) :: args, free_arg) s =
            if length vals = 1
            then invoke' (cfg, args, free_arg) vals s
            else error ("Bad Syntax: There must be one target of aggregate access. " ^
                         Position.here (snd (#1 pos_and_first_args)))
        | invoke'3 _ _ = error "BUG qgjNc1ebSHCtqRNU7y9/Cw"
   in Phi_Opr_Stack.meta_apply cfg pos_and_first_args @{priority %\<phi>lang_app} invoke'3 stat
  end

structure Agg_Constructors = Handlers (
  type arg = string (*user's source hint, indicating which object to be constructed*)
           * Phi_Opr_Stack.named_arg list * context_state
  type ret = Proof.context * cterm (*constructor*) * term list (*arguments*)
)

fun gen_constructor kind settings cfg stat =
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

            val ctxt'' = Generic_Variable_Access.register_value_spec_thms_no_dup (K I) pos_rules ctxt'
            val rule' =
                @{thm' op_construct_aggregate_\<phi>app}
                  |> Thm.transfer' ctxt''
                  |> Thm.instantiate (TVars.empty, Vars.make [
                        ((("constructor", 0), \<^typ>\<open>VAL list \<Rightarrow> VAL\<close>), ctor),
                        ((("args", 0), \<^typ>\<open>VAL \<phi>arg list\<close>), args)
                      ])
                  |> Phi_Reasoner.reason1 (fn () => "Fail to construct " ^ kind') NONE (SOME 1) ctxt''
         in (oprs, (ctxt' (*not ctxt''!*), Phi_Apply.apply1 [rule'] ctxt'' sequent))
        end
        | invoke _ _ = error "BUG 2CG4WNzYQqirWulpFUkQQA"
   in Phi_Opr_Stack.meta_apply cfg settings @{priority %\<phi>lang_push_val} invoke stat
  end



fun gen_dot_triangle_opr F right_arity (cfg, (name, pos), _, vals0) (stack, (ctxt0,sequent0)) =
  let fun chk_vals _ [v] = SOME v
        | chk_vals _ [ ] = NONE
        | chk_vals pos _ = error ("Bad \<tribullet> operation " ^ Position.here pos)

      val (right_operands, (ctxt, sequent)) =
            Generic_Variable_Access.extract_values (~1, true) (ctxt0,sequent0)
      val _ = if length right_operands = right_arity
              then ()
              else Phi_Opr_Stack.error_arity_opr ("right", right_arity, length right_operands) (name, pos)
      val (vals0, right_operands) = if name = "\<tribullet>"
                                then ([chk_vals pos vals0, SOME (hd right_operands)], tl right_operands)
                                else ([chk_vals pos vals0], right_operands)
      fun collect (poss, valss, Phi_Opr_Stack.Meta_Opr (_, _, ("\<tribullet>", pos), _, _, vals, _) :: L) =
            collect (pos :: poss, chk_vals pos vals::valss, L)
        | collect ret_L = ret_L
      val (poss, vals, stack') = collect ((if name = "\<tribullet>" then [pos] else []), vals0, stack)
      (*val (args', (ctxt',sequent')) =
              Generic_Variable_Access.extract_values (length poss, true) (ctxt,sequent)*)
      val args = poss ~~ map the (tl vals)

      val (idx_input'0, ctxt'2) = mk_element_index_input_internal args ctxt
      val idx_input = idx_input'0
      val (ctxt'3, sequent'3) =
              Generic_Variable_Access.push_values (the_list (hd vals) @ right_operands) (ctxt'2,sequent)
   in F (cfg, (name, pos), stack', idx_input, ctxt'3, sequent'3)
  end

fun err_assignment pos =
  error ("Bad Syntax: The assignment does not assign to a (generic) variable." ^
         Position.here pos)

val dot_triangle_assignment =
  gen_dot_triangle_opr (fn (_, (_, pos), stack, idx_input, ctxt, sequent) =>
    let val (stack', vname, pos) =
          case stack
            of (Phi_Opr_Stack.Meta_Opr (_, _, ("$", pos), _, SOME (Phi_Opr_Stack.String_Param vname), [], _) :: stack')
                => (stack', vname, pos)
             | _ => err_assignment pos
     in (stack', Generic_Variable_Access.assignment_cmd [(NONE, (Binding.make (vname, pos), idx_input))] (ctxt, sequent))
    end
  ) 1
 

val dot_triangle_opr =
  gen_dot_triangle_opr (fn (cfg, _, stack', idx_input, ctxt'3, sequent'3) =>
    rw_access (@{\<phi>overloading "\<tribullet>"}, "") true idx_input cfg (stack', (ctxt'3, sequent'3)) ) 1

val dot_triangle_update_opr =
  gen_dot_triangle_opr (fn (cfg, _, stack', idx_input, ctxt'3, sequent'3) =>
    rw_access (@{\<phi>overloading "\<tribullet>"}, @{\<phi>overloading ":="}) false idx_input cfg (stack', (ctxt'3, sequent'3)) ) 1

fun calc_dot_priority oprs =
  let open Phi_Opr_Stack
      fun is_the_first (Meta_Opr (_,_,("\<tribullet>",_),_,_,_,_) :: _) = false
        | is_the_first (Meta_Opr (pr,_,_,_,_,_,_) :: L) =
            if pr > @{priority %\<phi>lang_app} then is_the_first L else true
        | is_the_first (Opr (pr,_,_,_,_,_) :: L) =
            if pr > @{priority %\<phi>lang_app} then is_the_first L else true
        | is_the_first _ = true
   in if is_the_first oprs
      then @{priority loose %\<phi>lang_push_val+1}
      else @{priority loose %\<phi>lang_dot_opr+1}
  end

fun mk_dot_opr pos oprs =
  ((calc_dot_priority oprs, @{priority %\<phi>lang_dot_opr},
        (VAR_ARITY_IN_OPSTACK, 1)), ("\<tribullet>", pos), NONE, dot_triangle_opr)

fun build_dot_opr_stack cfg idxs oprs =
  let (*val mode = Phi_Working_Mode.mode1 (#1 (#2 opr_ctxt))
      val (_, _, oprs, stat) = Phi_Opr_Stack.eval_until
              (Context.Proof (#1 (#2 opr_ctxt)))
              (lprio, ~1)
              (mode, true, cfg)
              (NONE, Markup.operator, ("", Position.none))
              (#1 opr_ctxt) (#2 opr_ctxt)
              *)
      val last = length idxs - 1
   in fold_index (fn (i,((_,pos),vals)) => fn L =>
        Phi_Opr_Stack.Meta_Opr (
            (if i = last
             then @{priority loose %\<phi>lang_push_val}
             else @{priority loose %\<phi>lang_dot_opr}),
            SOME (if i = last then 0 else 1),
            (if i = last then "<val>" else "\<tribullet>", pos),
            #id cfg,
            NONE,
            vals,
            (if i = last then (fn (_, _, _, vals) => apsnd (Generic_Variable_Access.push_values vals))
             else dot_triangle_opr)
          ) :: L) idxs oprs
  end
  

fun open_bracket_opr pos cfg opr_ctxt =
  let fun invoke (cfg, args, _) (stack, stat) =
           (apfst (build_dot_opr_stack cfg args) stack, stat)
   in Phi_Opr_Stack.meta_apply cfg (("[",pos),(NONE,pos))
                               (calc_dot_priority (#1 (#1 opr_ctxt))) invoke opr_ctxt
  end

fun close_bracket pos cfg opr_ctxt = (
  Phi_Opr_Stack.check_meta_apply_balance "[" pos (#1 (#1 opr_ctxt)) ;
  Phi_Opr_Stack.close_parenthesis (cfg, NONE, false) opr_ctxt )


end