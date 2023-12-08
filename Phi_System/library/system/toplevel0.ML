signature PHI_TOPLEVEL = sig

  (* Open \& Close a Block *)
  val begin_block :
        binding list (*names of fixed variables, use the name of the lambda variable if not given*)
      * (Attrib.binding * term list) list (*bindings of conditions, attributes registered by
                                      \<open>\<phi>premise_attribute\<close> will be applied on the conditions *)
        -> bool -> Proof.state -> Proof.state
  val begin_block_cmd :  binding list * (Attrib.binding * string list) list
        -> bool -> Proof.state -> Proof.state

  datatype spec_annot = Spec_Annot of string | Subj_Annot of string
  val end_block_cmd : spec_annot option -> bool -> Proof.state -> Proof.state
  val end_block_auto_proof_cmd : spec_annot option -> bool
                              -> Proof.state -> Proof.state
  val end_block : term option (*a spec that the sequent will be transformed to before assembling*)
               -> bool -> Proof.state -> Proof.state

end

structure Phi_Toplevel : PHI_TOPLEVEL = struct

(** Library **)

fun print_results int = Proof_Display.print_results
                            {interactive=int, pos=Position.thread_data (), proof_state=false}


(** Programming Block **)

(* Begin Block *)

local
fun is_backward_mode s = (Proof.assert_backward s; true)
      handle ERROR _ => false

fun strip_fun_args \<^Type>\<open>fun T T'\<close> = T :: strip_fun_args T'
  | strip_fun_args _ = []
fun strip_fun_ret \<^Type>\<open>fun _ T'\<close> = strip_fun_ret T'
  | strip_fun_ret T' = T'

fun collect_var_red L (Const _) = L
  | collect_var_red L (Free _) = L
  | collect_var_red L (Var _) = L
  | collect_var_red L (Bound _) = L
  | collect_var_red L (Abs (_,_,X)) = collect_var_red L X
  | collect_var_red L (X as _ $ _) =
      case strip_comb X of (Var (N, T), args) =>
            let val n = length args
                val Targs  = strip_fun_args T
                val Targs' = fold2 (fn t => (fn Bound _ => (fn L => t::L)
                                              | _ => I)) (List.take (Targs, n)) args []
                val T' = strip_fun_ret T
                      |> fold_rev (fn t => fn T => t --> T ) (List.drop (Targs, n))
                      |> fold (fn t => fn T => t --> T ) Targs'
            in (N,T')::L
            |> fold (fn arg => fn L => collect_var_red L arg) args
            end
        | (H,args) => collect_var_red L H
                   |> fold (fn arg => fn L => collect_var_red L arg) args

fun red_var tys (Abs (N,T,X)) = Abs (N,T, red_var tys X)
  | red_var tys (X as _ $ _) =
     (case strip_comb X of ((H as Var (N,_)), args) =>
        (case AList.lookup (op =) tys N
           of SOME T' => list_comb (Var (N,T'),
                            filter (fn Bound _ => true | _ => false) (map (red_var tys) args))
            | NONE => list_comb (H, map (red_var tys) args))
        | (H,args) => list_comb (H, map (red_var tys) args))
  | red_var _ X = X

(* Because we fix universally quantified variables during opening a programming context,
   the quantified variables which are parameters of schematic variables are also fixed.
   (\<And>x1 x2. P (?z x1 x2))  becomes   P (?z x1 x2)
   Since it is meaningless for a schematic variables to be parameterized by fixed variables,
   this ML function trims all such fixed variables parameterizing schematic variables.
   The above example will be trimmed to (P ?z). *)
fun reduce_var X =
  let val tys = collect_var_red [] X
      val tys'= filter (fn (N,T) => forall (fn (N',T') => N <> N' orelse T = T') tys) tys
   in if null tys' then X else red_var tys' X end

fun merge_premises_bindings R [] = map (the_default ((Binding.empty, []),[])) R
  | merge_premises_bindings (NONE::R1) (((B,A2),P2)::R2)
      = ((B,A2),P2) :: merge_premises_bindings R1 R2
  | merge_premises_bindings ((SOME ((B1,A1),P1))::R1) (((B2,A2),P2)::R2)
      = if Binding.name_of B1 = "\<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l>"
        then error "Too much premises bindings given"
        else ((B2, A1@A2), P1@P2) :: merge_premises_bindings R1 R2
  | merge_premises_bindings [] (_::_)
      = error "Too much premises bindings given"

exception Internal_Match_Fail of string

in

fun gen_begin_block prep_attr prep_prop (var_bindings,prem_bindings0) int stat =
  let
    val stat = Proof.map_context Phi_ID.next stat
    val is_top = not (Phi_Envir.under_programming_environ (Proof.context_of stat))
                 orelse is_backward_mode stat
    val normalize_tac =
          REPEAT_DETERM (HEADGOAL (Tactic.resolve_tac (Proof.context_of stat)
              @{thms Action_Tag_I Argument_I allI impI Labelled_I Labelled_I'}))
          (*TODO: retain the name of the quantified variables*)
    val stat =
          if is_top
          then stat
                |> Proof.apply (
                      Method.Basic (K (Method.SIMPLE_METHOD normalize_tac)), Position.no_range)
                |> Seq.the_result "impossible"
          else stat
    val sequent =
          if is_top
          then #goal (Proof.raw_goal stat)
          else Phi_Envir.the_state_sequent stat
                  |> Tactic.rule_by_tactic (Proof.context_of stat) normalize_tac

    val ((mode,sequent),stat) = Proof.map_context_result (fn ctxt =>
            Phi_Working_Mode.infer_working_mode_of_sequent (ctxt,sequent)
                |> (fn (m,(c,s)) => ((m,s),c))) stat

    val ((prem_bindings, sequent), stat) = Proof.map_context_result (fn ctxt =>
      let val prem_bindings =
            map (fn ((b,attrs), pats) =>
                  (((if Binding.name_of b = "_" then Binding.empty else b),
                     map (prep_attr ctxt) attrs),
                   map (prep_prop ctxt) pats)
                ) prem_bindings0
           val (pbs,sequent') = Named_Premises.remove_assm_bindings ctxt 1 sequent
      in ((merge_premises_bindings pbs prem_bindings, sequent'),
          Named_Premises.remove_bindings (map_filter
               (Option.map (Binding.name_of o fst o fst)) pbs) ctxt)
      end
    ) stat

    val stat =(if is_top
               then Proof.refine_primitive (K (K sequent)) stat
                    |> Proof.assert_backward
                    |> Proof.enter_forward
               else Phi_Envir.set_state_sequent sequent stat)
               |> Proof.begin_block

    (*Assuming the proof state is in the normal hhf, or else the operation fails.*)
    val (vars0, goal) =
          Phi_Help.strip_binder_raw @{const_name Pure.all} (Phi_Help.leading_antecedent' sequent)
    val vars1 = burrow_fst (Name.variant_list []) vars0
    val vb_N = length var_bindings
    val (var_names, stat) =
          Proof.map_context_result (Proof_Context.add_fixes
            (map2 (fn (_,ty) => fn b => (b, SOME ty, NoSyn)) (List.take (vars1, vb_N)) var_bindings
           @ map  (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) (List.drop (vars1, vb_N)))
          ) stat
    val vars = map2 (fn N => fn (_,T) => Free (N,T)) var_names vars1
    val goal = subst_bounds (rev vars, goal)
            |> reduce_var
    val prems = Logic.strip_imp_prems goal
    val goal'  = Logic.strip_imp_concl goal

    fun after_qed (ctxt',[[th]]) stat0 =
      let val stat = Proof.end_block stat0
          val ctxt'' = Proof.context_of stat
          val th0 = (* Drule.eta_contraction_rule *) th
          val (th1::vars') = (th0::map (Drule.mk_term o Thm.cterm_of ctxt') vars)
                                   |> Proof_Context.export ctxt' ctxt''
          val th2 = Drule.forall_intr_list (map Drule.dest_term vars') th1

          fun gen_sequent (ctxt,sequent) =
            let (*val sequent = Phi_Help.beta_eta_contract_leading_antecedent sequent0*)
                val insts =
                      PLPR_Pattern.match (Proof_Context.theory_of ctxt'') (K false) []
                                    (Phi_Help.leading_antecedent' sequent, Thm.prop_of th2)
                                    (Vartab.empty, Vartab.empty)
                      |> Phi_Help.subst_env
                      |> Phi_Help.certify_vars (Context.Proof ctxt)
                handle Pattern.MATCH =>
                  raise Internal_Match_Fail (
                    Pretty.string_of (Pretty.chunks [
                      Pretty.str "The higher-order pattern match fails",
                      Pretty.block [Pretty.str "from ",
                                    Syntax.pretty_term ctxt'' (Phi_Help.leading_antecedent' sequent)],
                      Pretty.block [Pretty.str "to ",
                                    Syntax.pretty_term ctxt'' (Thm.prop_of th2)],
                      Pretty.str "which usually means some schematic variable is instantiated to\
                        \ some universally quantified variables that it has no access."
                    ]))
                val sequent' = Thm.instantiate insts sequent (*index is considered*)
                val sequent'' = Thm.implies_elim
                                      (Phi_Help.beta_eta_contract_leading_antecedent sequent')
                                      (Phi_Help.beta_eta_contract th2)
                    (*This beta eta contraction may be not good, cuz it may remove names of quantified
                      variables but I cannot find a better and simpler way to do this implication
                      elimination.*)
                val sequent'3 = Phi_Reasoner.reason NONE (SOME 1) ctxt sequent''
                       |> (fn SOME X => X
                            | NONE => Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
                                  Pretty.str "Fail to reason the finalization reasoning tasks:",
                                  Syntax.pretty_term ctxt (Thm.major_prem_of sequent'')
                                ])))
                val sequent'4 = case Thm.major_prem_of sequent'3
                                  of Const (\<^const_name>\<open>Trueprop\<close>, _) $ Const (\<^const_name>\<open>True\<close>, _)
                                      => @{thm TrueI} RS sequent'3
                                   | _ => sequent'3
             in (ctxt, sequent'4)
             end
             handle Internal_Match_Fail msg =>
              (case Phi_Apply.try_apply [th2] ctxt sequent
                 of SOME s' => (ctxt, s')
                  | _ => error msg)
      in if is_top
         then stat
                |> Proof.enter_backward
                |> Proof.apply (Method.Basic (fn _ =>
                        Method.CONTEXT_METHOD (K (Seq.single o Seq.Result o gen_sequent))), Position.no_range)
                |> Seq.the_result "never fail"
         else Phi_Envir.map_state_sequent gen_sequent stat
      end

    val bindings = prem_bindings
          |> map2 (fn P => fn ((b,attrs),pats) =>
              let val attrs' = Premises_Attribute.attribute_of (null attrs) P (Context.Proof (Proof.context_of stat))
              in ((b, attrs' @ map (Attrib.attribute (Proof.context_of stat)) attrs), pats)
              end) prems
  in
    stat
      |> Proof.map_context (Config.put phi_allow_source_object_to_be_not_variable true)
      |> Proof.internal_goal (print_results int) Proof_Context.mode_schematic true
          "" NONE after_qed []
          (map2 (fn (b,pats) => fn prop => (b,[(prop,pats)])) bindings prems)
          [(Binding.empty_atts, [(goal',[])])] |> #2
      |> Proof.map_context (fn ctxt => ctxt
            |> Proof_Context.set_mode Proof_Context.mode_default
            |> Config.restore phi_allow_source_object_to_be_not_variable (Proof.context_of stat)
            |> Phi_ID.step_in
            |> Phi_Opr_Stack.initialize_opr_stack)
      |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
            Context_Tactic.CONTEXT_TACTIC all_tac), Position.no_range))
      |> Seq.the_result "never fail"
      |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)
      |> (fn stat => stat
              |> Proof.map_context (fn ctxt => ctxt
                  |> Phi_Working_Mode.set mode
                  |> Phi_Envir.put_thesis (Thm.cprem_of (@{print} (#goal (Proof.goal stat))) 1
                                              |> Drule.strip_imp_concl)))
      |> Proof.begin_block
      |> #initialize_sequent mode
      |-> Phi_Envir.enter_programming_environ
      |> Proof.map_context Phi_Envir.freeze_dynamic_lemmas
(*      |> Generic_Variable_Access.open_context' Position.none *)
      (* |> NuObtain.obtain_quick_pairs_perhaps_try *)
  end

val begin_block_cmd =
      gen_begin_block Attrib.check_src
                      (Syntax.parse_prop o Proof_Context.set_mode Proof_Context.mode_pattern)
val begin_block = gen_begin_block (K I) (K I)

end


(* End Block *)

local

fun basic_method r = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (r ctxt)))

fun gen_finish_proc prep_term qed spec int stat =
  let
    val ctxt_ = Proof.context_of stat
    val goal = Phi_Envir.get_thesis ctxt_
    val mode = Phi_Working_Mode.mode1 ctxt_
  in stat
  |> Proof.map_context_result (fn ctxt =>
      let
        val sequent_pre1 = Phi_Envir.the_programming_sequent' ctxt
        val sequent =
          if Thm.no_prems sequent_pre1
          then sequent_pre1
          else let
            val _ = Phi_Reasoner.info_print ctxt 2 (fn _ =>
                      "solving pending antecedents before closing the programming block..."
                      ^ Position.here \<^here>)
            fun attack_obligations ctxt sequent =
              case try Thm.major_prem_of sequent
                of SOME (\<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ _)) =>
                    attack_obligations ctxt (Phi_Reasoners.auto_obligation_solver1 ctxt sequent)
                 | _ => sequent
            val sequent_pre2 = attack_obligations ctxt sequent_pre1
            in Phi_Reasoner.reason1 (fn _ => Pretty.string_of (Pretty.chunks [
                    Pretty.str "Fail to solve pending antecedents:",
                    Thm.pretty_thm ctxt sequent_pre2
               ])) NONE NONE ctxt sequent_pre2
            end
        val (ctxt',sequent') = Phi_Sys.move_lemmata (ctxt, sequent)
        val (ctxt'',sequent'') = sequent'
              |> (case spec
                    of NONE => I
                     | SOME term =>
                        let val ctxt'' = Proof_Context.set_mode (Proof_Context.mode_pattern) ctxt'
                            val aim = Thm.cterm_of ctxt'' (prep_term ctxt'' term)
                            val _ = Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.block [
                               Pretty.str "transforming to the given specification ",
                               Syntax.pretty_term ctxt'' (Thm.term_of aim),
                               Pretty.block (Pretty.here \<^here>)
                            ])
                        in Phi_Sys.cast aim ctxt'
                        #> Phi_Reasoners.auto_obligation_solver' (fn ctxt => fn sequent =>
                             error (Pretty.string_of (Pretty.chunks [
                               Pretty.str ("Fail to solve the proof obligation generated during "^
                                           "the cast towards the given specification:"),
                               Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent),
                               Pretty.block [
                                 Pretty.str ("Tailing specification of a programming block is "^
                                 "only sufficient for simple transformations having simple "^
                                 "proof obligations. More complicated transformation should use "),
                                 Pretty.keyword2 "assert", Pretty.str "command instead."
                               ]
                           ]))) ctxt'
                        end)
              |> pair ctxt'
              |> #vcg_before_assembling mode goal
      in (sequent'', ctxt'')
        (*The transformation shall generate a poof obligation*)
      end
    )
        (*and the proof obligation is presented to users here.*)
    |-> Phi_Sys.obligation_proof (print_results int) Proof_Context.mode_schematic "" NONE
          (fn sequent => fn stat =>
      let
        val ctxt = Proof.context_of stat
        val stat' = stat
          |> Proof.set_facts []
          |> Proof.map_context Phi_Envir.exit_programming_environ
          |> Proof.end_block
          
        val ctxt'1 = Proof.context_of stat'
        val sequent'1 = singleton (Proof_Context.export ctxt ctxt'1) sequent
        val end_tac = basic_method (fn ctxt' => fn goal' => (
            let
              val sequent' = singleton (Proof_Context.export ctxt'1 ctxt') sequent'1
              val _ = Phi_Reasoner.info_print ctxt' 2 (fn _ =>
                  Pretty.string_of (Pretty.chunks [
                    Pretty.str "Solving the goal by the resulted sequent from the programming.",
                    Pretty.item [Pretty.str "goal:"],
                    Syntax.pretty_term ctxt' (fst (Logic.dest_implies (Thm.prop_of goal'))),
                    Pretty.item [Pretty.str "resulted sequent:"],
                    Thm.pretty_thm ctxt' sequent',
                    Pretty.block (Pretty.here \<^here>)
                  ]))
                val result = Phi_Apply.apply [sequent'] ctxt' goal'
                          |> Phi_Reasoners.weak_obligation_solver1 {can_inst=true} ctxt'
              in result end
              handle E => raise (@{print} E)
            ))
       in
        stat'
          |> qed (SOME (end_tac, Position.no_range), false)
       end) [] []
     |> snd
  end
in

datatype spec_annot = Spec_Annot of string | Subj_Annot of string

val end_block_cmd = gen_finish_proc (fn ctxt =>
     (fn (Spec_Annot spec) => Syntax.read_term ctxt spec
       | (Subj_Annot subj) =>
            let val term = Syntax.read_term ctxt subj
                val i = Term.maxidx_of_term term + 1
             in \<^Const>\<open>Subjection \<open>TVar(("'x", i), [])\<close>\<close>
                  $ Var(("X",i),\<^Type>\<open>set \<open>TVar(("'x", i), [])\<close>\<close>)
                  $ term
            end
     )) Proof.local_qed

val end_block = gen_finish_proc (K I) Proof.local_qed

fun led_future_proof s =
  if Proof.goal_finished s then s
  else let val s = Proof.map_context Phi_ID.next s
           val id = Option.map Phi_ID.encode (Phi_ID.get_if_is_named (Proof.context_of s))
           val meth = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (fn sequent =>
                Phi_Sledgehammer_Solver.auto id ctxt (@{thm Premise_D[where mode=default]} RS sequent))))
        in Proof.local_future_terminal_proof ((meth, Position.no_range), NONE) s
       end

fun led_future_proof0 s =
  if Proof.goal_finished s
  then Proof.local_done_proof s
  else led_future_proof s

fun end_block_auto_proof_cmd cast int =
       end_block_cmd cast int
    #> led_future_proof0

(* fun gen_finish_proc' prep_specthm qed int stat =
  let val sequent = Proof.the_fact stat
  in if current_block_depth sequent > 1 then
      gen_finish_proc' prep_specthm qed int (end_block_cmd false stat)
    else gen_finish_proc prep_specthm qed int stat end *)


end



end

