signature PHI_GENERIC_ELEMENT_ACCESS = sig

structure Agg_Path_Encoders : HANDLERS
structure Agg_Constructors : HANDLERS

val mk_agg_path_default : Phi_Delayed_App.named_arg list * context_state -> Proof.context * thm
val mk_agg_path_val : Phi_Delayed_App.named_arg list * context_state -> Proof.context * thm

val gen_access : string -> (string * Position.T) * Phi_Delayed_App.arg_name -> context_state -> context_state
val gen_constructor : string -> (string * Position.T) * Phi_Delayed_App.arg_name
                   -> context_state -> context_state

end

structure Phi_Generic_Element_Access : PHI_GENERIC_ELEMENT_ACCESS = struct

fun gen_mk_agg_path idx_val_constr args ctxt =
  let val _ = List.app (
        fn ((SOME _, pos), _) => error ("named argument is not supported here " ^ 
                                         Position.here pos)
         | ((_, pos), _ :: _ :: _) => error (Position.here pos ^ " the expression returns more than\
                                              \ one value")
         | ((_, pos), []) => error (Position.here pos ^ " the expression returns no value!")
         | _ => ()
        ) args
      val raw_path' = map (fn (_, [rule]) =>
            case Phi_Local_Value.get_raw_val_in_rule rule
              of _ (*\<phi>arg*) $ (\<^term>\<open>V_symbol.mk\<close> $ sym) => \<^Const>\<open>AgIdx_S \<^typ>\<open>VAL\<close>\<close> $ sym
               | v => idx_val_constr $ v) args
      val raw_path = HOLogic.mk_list \<^typ>\<open>aggregate_index\<close> raw_path'
      val reasoning_rules =
            map (fn ((_, pos), [rule]) => (rule,pos,Phi_Reasoner.LOCAL_CUT,1000)) args
      val ctxt' = Context.proof_map (Phi_Local_Value.add_reasoning_rules reasoning_rules) ctxt
      val ind = Term.maxidx_term raw_path ~1 + 1
   in Goal.init (Thm.cterm_of ctxt' (
        \<^const>\<open>Trueprop\<close> $ (\<^Const>\<open>unwind_aggregate_path_into_logical_form \<^typ>\<open>aggregate_path\<close>\<close>
                              $ raw_path $ Var (("logical_path", ind), \<^typ>\<open>aggregate_path\<close>))))
    |> pair ctxt'
    |> Phi_Reasoner.reason (SOME 1)
    |> (fn SOME (_, ret) => Goal.conclude ret (*we drop the context here*)
         | NONE => error "Fail to unwind the aggregate path into a logical form.")
  end

fun mk_agg_path_default (args,(ctxt,_)) = (ctxt, gen_mk_agg_path \<^Const>\<open>AgIdx_VN \<^typ>\<open>VAL\<close>\<close> args ctxt)
fun mk_agg_path_val (args,(ctxt,_)) = (ctxt, gen_mk_agg_path \<^Const>\<open>AgIdx_V \<^typ>\<open>VAL\<close>\<close> args ctxt)

structure Agg_Path_Encoders = Handlers (
  type arg = Phi_Delayed_App.named_arg list * context_state
  type ret = (Proof.context * thm (*unwind_aggregate_path_into_logical_form*))
)

fun gen_access named_thm_of_rules pos_and_first_args stat =
  let fun invoke ((_, vals_before) :: args) (ctxt0,sequent0) =
        let val (ctxt,sequent) = Generic_Variable_Access.push_values vals_before (ctxt0,sequent0)
            val (ctxt', unwind) = Agg_Path_Encoders.invoke (Context.Proof ctxt) (args, (ctxt,sequent))
                                |> (fn SOME ret => ret
                                     | NONE => mk_agg_path_default (args, (ctxt,sequent)))
            val rules = Named_Theorems.get ctxt named_thm_of_rules
                      |> map (fn thm => unwind RS thm)
         in Phi_Apply.apply rules (ctxt', sequent)
        end                                      
        | invoke _ _ = error "internal bug #a2a96e04-14d6-4b66-9c2e-053e5c2bfcbe"
   in Phi_Delayed_App.meta_apply pos_and_first_args invoke stat
  end

structure Agg_Constructors = Handlers (
  type arg = string (*user's source hint, indicating which object to be constructed*)
           * Phi_Delayed_App.named_arg list * context_state
  type ret = Proof.context * cterm (*constructor*) * term list (*arguments*)
)

fun gen_constructor kind pos_and_first_args stat =
  let fun invoke ((_, vals_before) :: args0) (ctxt0, sequent0) =
        let val (ctxt,sequent) = Generic_Variable_Access.push_values vals_before (ctxt0,sequent0)
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
         in Phi_Apply.apply [rule'] (ctxt'3, sequent)
        end
        | invoke _ _ = error "internal bug #5330d2f8-c5e3-46ae-9b45-5ae9550f037d"
   in Phi_Delayed_App.meta_apply pos_and_first_args invoke stat
  end

end