(* FILE: library/system/toplevel.ML
   AUTHOR: Qiyuan Xu

   Definition of Isar commands for IDE-CP.
*)

signature PHI_TOPLEVEL = sig

  datatype cond_kind = Premise | Assumption
  datatype ('a,'b) modifier = Mod_by_Rule of 'a | Mod_by_Attr of 'b

  structure Finishing_Modifier_Hooks : HOOKS
  structure Finishing_Construction_Hooks : HOOKS

  val is_interactive : bool Config.T
  exception Schematic

  val name_of_the_building_procedure : Proof.context -> binding option
  val begin_proc_cmd : bool (*whether to define a new constant*)
        -> Attrib.binding (*name*)
        -> xstring (*input*)
        -> xstring (*output*)
        -> xstring option (*throws*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
        -> (Facts.ref * Token.src list, Token.src list) modifier list
        -> bool -> local_theory -> Proof.state

(*
  val begin_rec_proc_cmd : bool (*whether to define a new constant*)
        -> Attrib.binding
        -> xstring (*input*)
        -> xstring (*output*)
        -> xstring option (*throws*)
        -> ((binding * string option * mixfix) list * (*variants*)
            (binding * string option * mixfix) list   (*for fixes*))
        -> (xstring * Position.T) list (*includes*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
        -> bool -> local_theory -> Proof.state *)

  val begin_block :
        binding list (*names of fixed variables, use the name of the lambda variable if not given*)
      * (Attrib.binding * term list) list (*bindings of conditions, attributes registered by
                                      \<open>\<phi>premise_attribute\<close> will be applied on the conditions *)
        -> bool -> Proof.state -> Proof.state
  val begin_block_cmd :   binding list * (Attrib.binding * string list) list
        -> bool -> Proof.state -> Proof.state

  datatype spec_annot = Spec_Annot of string | Subj_Annot of string
  val end_block_cmd : spec_annot option -> bool -> Proof.state -> Proof.state
  val end_block_auto_proof_cmd : spec_annot option -> bool -> Proof.state -> Proof.state
  val end_block : term option (*a spec that the sequent will be transformed to before assembling*)
               -> bool -> Proof.state -> Proof.state

  val statement_clean_values : bool Config.T (*controls whether the statement command \<^bold>;
        cleans all values at its beginning.*)
  val statement_line_cmd : int * int -> (Proof.state -> Proof.state) parser

  structure Begin_of_Line : HOOKS
  structure End_of_Line : HOOKS
  structure Begin_of_Next_Statement : HOOKS
  structure End_of_Statement : HOOKS

  val prove_prem : bool -> (Proof.state -> Proof.state) -> Proof.state -> thm list * Proof.state
  (*val export_LLVM : theory -> theory *)

end

structure Phi_Toplevel : PHI_TOPLEVEL = struct


val v_proc_var = ("\<p>\<r>\<o>\<c>",0)


(* Library *)

fun print_results int = Proof_Display.print_results int (Position.thread_data ())

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt'
  in ((vars, xs), ctxt'') end

datatype cond_kind = Premise | Assumption



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
                      PLPR_Pattern.match (Proof_Context.theory_of ctxt'')
                                    (Phi_Help.leading_antecedent' sequent, Thm.prop_of th2)
                                    (Vartab.empty, Vartab.empty)
                      |> Phi_Help.env_to_table ctxt''
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
                val sequent'3 = Phi_Reasoner.reason (SOME 1) ctxt sequent''
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
              let val attrs' = Premises_Attribute.attribute_of (null attrs) P
                                                        (Context.Proof (Proof.context_of stat))
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
            |> Phi_ID.step_in)
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
(*      |> Generic_Variable_Access.open_value_context' Position.none *)
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
               ])) NONE ctxt sequent_pre2
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
                               Syntax.pretty_term ctxt'' (Phi_Help.leading_antecedent' sequent),
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
                          |> Phi_Reasoners.safer_obligation_solver1 ctxt'
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

fun repeat_future_proof s =
  if Proof.goal_finished s then s
  else let val id = Option.map Phi_ID.encode (Phi_ID.get_if_is_named (Proof.context_of s))
           val meth = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (fn sequent =>
                Phi_Sledgehammer_Solver.auto id (ctxt, @{thm Premise_D[where mode=default]} RS sequent))))
        in Proof.local_future_terminal_proof ((meth, Position.no_range), NONE) s
       end
fun repeat_future_proof0 s =
  if Proof.goal_finished s
  then Proof.local_done_proof s
  else repeat_future_proof s

fun end_block_auto_proof_cmd cast int =
       end_block_cmd cast int
    #> repeat_future_proof0

(* fun gen_finish_proc' prep_specthm qed int stat =
  let val sequent = Proof.the_fact stat
  in if current_block_depth sequent > 1 then
      gen_finish_proc' prep_specthm qed int (end_block_cmd false stat)
    else gen_finish_proc prep_specthm qed int stat end *)


end

val previous_statement_is_finished' =
      Config.declare_bool ("Phi_Toplevel.previous_statement_is_finished", \<^here>) (K false)
(* It is false iff the previous statement is ended by a proof meaning the intended construction
   of the previous statement is interrupted by a pending proof so not finished.
 *)

fun prove_prem int after_qed'' stat =
  let
    val sequent = Phi_Envir.the_state_sequent stat
    fun after_qed sequent stat =
      let
        val original_auto_level = Config.get (Proof.context_of stat) Phi_Reasoner.auto_level
      in
        stat |> Proof.map_context_result
                  (fn ctxt =>
                   Phi_Processor.process_no_input (SOME 1) (ctxt,sequent)
                  |> swap
                  |> apsnd (Config.put Phi_Reasoner.auto_level original_auto_level
                         #> Config.put previous_statement_is_finished' false))
             |-> Phi_Envir.set_state_sequent
             |> after_qed''
      end
  in stat
  |> Phi_Sys.obligation_proof (print_results int) Proof_Context.mode_schematic ""
        NONE after_qed [] [] sequent
  end
 (*let open Proof
    val sequent = Phi_Envir.the_state_sequent stat
    val goal = Thm.prop_of sequent
                |> Logic.dest_implies |> #1 (* |> dest_premise_tag |> mk_Trueprop *)
    fun after_qed (ctxt',[[th]]) stat =
      let
        val [th] = Proof_Context.export ctxt' (context_of stat) [th]
        val original_auto_level = Config.get (Proof.context_of stat) Phi_Reasoner.auto_level
      in
        stat |> Proof.map_context_result
                  (Config.put Phi_Reasoner.auto_level 0
                    #> (fn ctxt => Phi_Processor.process_no_input (ctxt, th RS specthm))
                    #> apfst (Config.put Phi_Reasoner.auto_level original_auto_level)
                    #> swap)
             |-> Phi_Envir.set_state_sequent
      end
  in
    stat |> Phi_Sys.setup_proof (print_results int) Proof_Context.mode_schematic ""
              NONE after_qed [] [] [[(goal,[])]]
         |> apsnd (
              Proof.map_context (Proof_Context.set_mode Proof_Context.mode_default)
           #> Proof.refine (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (
                HEADGOAL (resolve_tac ctxt @{thms Premise_I})
              ))) #> Seq.the_result "should never fail"
            )
  end*)


(** Header of Procedure **)

datatype ('a,'b) modifier = Mod_by_Rule of 'a | Mod_by_Attr of 'b

structure Finishing_Modifier_Hooks = Hooks (type arg = unit
                                            type state = context_state)
structure Finishing_Construction_Hooks = Hooks (type arg = unit
                                                type state = context_state)

structure Procedure_Building_Envir = Proof_Data (
  type T = binding option
  val init = (K NONE)
)

val name_of_the_building_procedure = Procedure_Building_Envir.get


fun gen_begin_proc prep_term prep_prop prep_var prep_attr def_const
      binding arg ret throws rawfixes includes raw_defines raw_preconds action raw_modifiers
      int lthy =
  let
    val includes = includes |> map (Bundle.check lthy)
    val ((fixes,var_names), ctxt_parse) = lthy
                                       |> not (null includes) ? Bundle.includes includes
                                       |> prep_decls prep_var rawfixes
    val binding = binding |> apsnd (map (Attrib.check_src lthy))
    val parse_term = prep_term ctxt_parse
    val parse_prop = prep_prop ctxt_parse

    fun apply_modifier (ctxt,sequent) = (ctxt,sequent)
         |> fold (fn Mod_by_Rule rule =>
                          Phi_Modifier.by_rule (singleton (Attrib.eval_thms ctxt) rule)
                 | Mod_by_Attr attr =>
                          fold (Phi_Modifier.apply_wrapped_attribute o prep_attr ctxt) attr
               ) raw_modifiers
         |> Finishing_Modifier_Hooks.invoke (Context.Proof ctxt) ()

    fun prep_attrterm prep ((b,attrs),(prop, pats)) =
          ((b, map (Attrib.check_src lthy) attrs), (prep prop, map parse_term pats))

    fun prep_precond (Premise, c) =
          prep_attrterm (parse_prop #>
                  (fn (Const (@{const_name Trueprop}, _) $ tm)
                        => \<^const>\<open>Trueprop\<close> $ (@{term Normal_Premise} $ tm)
                    | _ => error "Premise must be atomic HOL assertion (meaning you cannot use \
                                 \meta connectivities like \<open>\<Longrightarrow>\<close> or \<open>\<And>\<close>). You may want to \
                                 \use keyword \<open>assume\<close> for introducing advanced arbitrary \
                                 \antecedents.")) c
      | prep_precond (Assumption, c) = prep_attrterm parse_prop c
    val preconds = map prep_precond raw_preconds

    val arg = Procedure_Syntax.translate_arg (parse_term arg)
    val ret = Procedure_Syntax.translate_ret (parse_term ret)
    val v_proc = Var (v_proc_var, dummyT)
    val throws = (case throws
                    of SOME thr => parse_term thr
                     | NONE => Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, dummyT))
    val goal0 = Const (@{const_name \<phi>Procedure}, dummyT) $ v_proc $ arg $ ret $ throws
    val goal = (case action of NONE => HOLogic.Trueprop $ goal0
                   | SOME A => HOLogic.Trueprop $ (\<^Const>\<open>Action_Tag\<close> $ goal0 $ parse_term A))
            |> fold_rev (fn (_,(P,_)) => fn X => \<^const>\<open>Pure.imp\<close> $ P $ X) preconds

    fun post_process' binding int lthy th =
      (lthy,th)
        |> Finishing_Construction_Hooks.invoke (Context.Proof lthy) ()
        |> Phi_Procedure.define def_const binding
        |> (fn (lthy, th) =>
              (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
                (("\<phi>procedure", ""), [("", [th])]); lthy))

    val defines = map (prep_attrterm parse_prop) raw_defines
    val elems = [Element.Fixes fixes, Element.Defines defines]
    val concls = Element.Shows [(Binding.empty_atts,[(goal,[])])]
    fun after_qed [[th]] lthy = post_process' binding int lthy th
  in
    lthy |> Specification.schematic_theorem false "" NONE after_qed Binding.empty_atts
              includes elems concls int
         |> Proof.map_context (fn ctxt =>
              ctxt |> Phi_ID.set_construct (Binding.name_of (fst binding))
                   |> Context.proof_map (Named_Theorems.clear \<^named_theorems>\<open>\<phi>lemmata\<close>)
                   |> Procedure_Building_Envir.put (SOME (fst binding))
            )
         |> Proof.refine (Method.Basic (K (K (fn s => s
              |> Named_Premises.bind_sequent_assms (map (apsnd snd) preconds) 1
              |> apply_modifier
              |> Seq.single o Seq.Result))))
         |> Seq.the_result "should never fail #gn9[q3"
  end

val begin_proc =
      gen_begin_proc (K I) (K I) Proof_Context.cert_var (K I)
val begin_proc_cmd =
      gen_begin_proc Syntax.parse_term Syntax.parse_prop Proof_Context.read_var
                     Attrib.attribute_cmd



(** Statement **)

structure Begin_of_Next_Statement = Hooks (type arg = unit type state = context_state)
structure End_of_Statement = Hooks (type arg = unit type state = context_state)
structure Begin_of_Line = Hooks (type arg = unit type state = context_state)
structure End_of_Line = Hooks (type arg = unit type state = context_state)

(*Whether to remove all values at the beginning of the command \<^bold>;*)
val statement_clean_values = Attrib.setup_config_bool \<^binding>\<open>\<phi>statement_clean_values\<close> (K true)

fun clean_values (ctxt,sequent) =
      if can Phi_Syntax.dest_CurrentConstruction (Thm.prop_of sequent)
         andalso Config.get ctxt statement_clean_values
      then snd (Generic_Variable_Access.extract_values (~1,true) (ctxt, sequent))
      else (ctxt, sequent)

fun statement_line_cmd auto_lev =
  Phi_Processor.powerful_process_p auto_lev (
                        Phi_Envir.map_state_sequent (fn (ctxt,sequent) =>
                            End_of_Line.invoke (Context.Proof ctxt) () (ctxt,sequent)))
    >> (fn process =>
              Phi_Envir.map_state_sequent (fn (ctxt,sequent) =>
                    Begin_of_Line.invoke (Context.Proof ctxt) () (ctxt,sequent))
           #> process
     (*the return of the process doesn't mean the end of the construction because the construction
       can be interrupted and suspended by inserted proofs.*)
  )

fun statement_cmd_first_line auto_lev =
  statement_line_cmd auto_lev >> (fn f =>
       Proof.map_context (Config.put previous_statement_is_finished' false)
    #> f)

fun statement_cmd_tail auto_lev toks =
  (statement_line_cmd auto_lev >> (fn f => fn s =>
      if Phi_Envir.under_programming_environ (Proof.context_of s)
      then f s
      else if null toks orelse Token.is_eof (hd toks)
           then s
           else error "The construction has ended but a statement is given")) toks


val _ = Theory.setup (Context.theory_map (
   Begin_of_Line.add 0 (K (fn s =>
     if Config.get (fst s) previous_statement_is_finished'
     then Begin_of_Next_Statement.invoke (Context.Proof (fst s)) () s
     else s))
#> End_of_Line.add 0 (K (fn s =>
     if Config.get (fst s) previous_statement_is_finished'
     then End_of_Statement.invoke (Context.Proof (fst s)) () s
     else s))
#> Begin_of_Next_Statement.add 50 (K clean_values)
#> Begin_of_Line.add 1000 (K (apfst (Config.put previous_statement_is_finished' true))) (*reset*)
#> End_of_Line.add 100 (K (apfst Phi_Envir.freeze_dynamic_lemmas))
))

fun previous_statement_is_finished ctxt = Config.get ctxt previous_statement_is_finished'

val is_interactive = Config.declare_bool ("\<phi>Sys.interactive", \<^here>) (K true)
exception Schematic

(* fun export_LLVM thy =
  let
    fun eval code = ML_Context.exec (fn () =>
                      ML_Context.eval_source ML_Compiler.flags (Input.string code))

    val base = Path.expand (Resources.master_directory thy)
    val path = File.full_path base (Path.basic (Context.theory_name thy ^ ".ll"))

    val codegen = eval ("NuCG.codegen NuCG_" ^ Context.theory_name thy ^ ".gen"
                    ^ "(" ^ ML_Syntax.print_path path ^ ")" )
    val _ = tracing("generating LLVM IR: " ^ Path.print path)
  in
    thy |> Context.theory_map (eval (NuCompilation.compile thy(* |> (fn s => (tracing s; s))*)))
        |> Context.theory_map codegen
  end *)



local open Scan Phi_Sys Parse

val is_props = Scan.repeat1 ($$$ "is" |-- prop);
val ppats = Scan.optional ($$$ "(" |-- !!! (is_props --| $$$ ")")) [];

val attrib = token liberal_name ::: !!! args;
val attribs = (\<^keyword>\<open>[\<close> -- \<^keyword>\<open>]\<close>) >> K [Attrib.internal (K (K (NONE,NONE)))]
           || ($$$ "[" |-- list attrib --| $$$ "]")
val opt_attribs = Scan.optional attribs [];
fun opt_thm_name s =
  Scan.optional
    ((Parse.binding -- opt_attribs || attribs >> pair Binding.empty) --| Parse.$$$ s)
    Binding.empty_atts;

val statement1 = Parse.and_list1 (opt_thm_name ":" -- Parse.propp);
val requires_statement = (\<^keyword>\<open>assumes\<close> || \<^keyword>\<open>requires\<close>) |-- Parse.!!! statement1;
val premises_statement = \<^keyword>\<open>premises\<close> |-- Parse.!!! statement1;
val precond_statements =
      Scan.repeat ((premises_statement >> map (pair Premise))
                || (requires_statement >> map (pair Assumption))) >> flat;
(* val requires_opt1 = Scan.option (\<^keyword>\<open>assumes\<close> |-- Parse.term); *)
val where_statement = Scan.optional (\<^keyword>\<open>where\<close> |-- Parse.!!! statement1) [];
val goal = Scan.option (\<^keyword>\<open>@action\<close> |-- Parse.term)

val includes = Scan.optional Parse_Spec.includes []
val input  = \<^keyword>\<open>input\<close>  |-- Parse.term
val output = \<^keyword>\<open>output\<close> |-- Parse.term
val throws = Scan.option (\<^keyword>\<open>throws\<close> |-- Parse.term)

val rec_vars = \<^keyword>\<open>var\<close> |-- !!! vars;

val def_const_flag =
  Scan.optional ((\<^keyword>\<open>(\<close> |-- Phi_Parse.$$$ "nodef" --| \<^keyword>\<open>)\<close>) >> (K false)) true

val modifier  = (Parse.attribs >> Mod_by_Attr) || (Parse.thm >> Mod_by_Rule)
val modifiers = repeat (\<^keyword>\<open>is\<close> |-- modifier)

(*
fun phi_proof step_in prf tr =
  let (*val pos = Toplevel.pos_of tr*)
      (*val doc_id = case Position.id_of (Toplevel.pos_of tr)
                     of SOME id => @{print} id
                      | _ => Exn.error "internal bug #vcj4i[10th;ji"*)
   in Toplevel.proof' (fn int => fn stat =>
        stat |> Proof.map_context step_in (*(fn ctxt =>
                  let val ctxt' = step_in ctxt
                   in Phi_Cache_DB.check_cache doc_id ctxt';
                      ctxt'
                  end)*)
             |> prf int ) tr end *)

in

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((def_const_flag -- Parse_Spec.opt_thm_name ":"
      -- includes
      -- precond_statements
      -- input
      -- precond_statements
      -- output
      -- throws
      -- goal
      -- where_statement
      -- Parse.for_fixes
      -- modifiers) >>
      (fn (((((((((((def_const,b),includes),prec1),arg),prec2),ret),throws),G),defs),fixes),mods) =>
        begin_proc_cmd def_const b arg ret throws fixes includes defs (prec1 @ prec2) G mods))

(*
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close>
    "begin a recursive procedure construction"
    ((def_const_flag -- Parse_Spec.opt_thm_name ":"
      -- includes
      -- precond_statements
      -- input
      -- rec_vars
      -- precond_statements
      -- output
      -- throws
      -- goal
      -- where_statement
      -- Parse.for_fixes
     ) >> (
     fn (((((((((((def_const,b),includes),prec1),arg),vars),prec2),ret),throws),G),defs),fixes) =>
        begin_rec_proc_cmd def_const b arg ret throws (vars,fixes) includes defs (prec1 @ prec2) G))
*)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>;;\<close> "Lead statements of \<phi> programs"
    (statement_line_cmd (3,3) >> (fn f => Toplevel.proof (f o Proof.map_context Phi_ID.next)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "Begin a \<phi> program block"
   (((  optional (\<^keyword>\<open>for\<close> |-- list1 Parse.binding) []
     -- optional (\<^keyword>\<open>premises\<close> |--
            and_list ((binding -- opt_attribs || attribs >> pair Binding.empty) -- ppats)) []
      >> begin_block_cmd)
   -- statement_cmd_first_line (3,1))
   >> (fn (blk,prcs) => Toplevel.proof' (fn int => prcs o blk int o Proof.map_context Phi_ID.next)))

datatype end_blk_action = Enter_Proof_Mode | Transparent_Proof of (Proof.state -> Proof.state)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "End a \<phi> program block"
    (option (\<^keyword>\<open>for\<close> |-- term) --
     option (\<^keyword>\<open>subj\<close> |-- term) -- (
        \<^keyword>\<open>certified\<close> >> K Enter_Proof_Mode ||
        statement_cmd_tail (3,1) >> Transparent_Proof
  ) >> (fn (spec_subj,act) => Toplevel.proof' (fn int => fn stat =>
  let val spec = case spec_subj of (SOME _, SOME _) =>
                                      Exn.error "keyword 'for' and 'subj' should not be given simutaneously."
                                 | (SOME s, _) => SOME (Spec_Annot s)
                                 | (_, SOME s) => SOME (Subj_Annot s)
                                 | _ => NONE
   in stat
   |> Proof.map_context Phi_ID.next
   |> (case act
         of Enter_Proof_Mode => end_block_cmd spec int
          | Transparent_Proof tail_statement => end_block_auto_proof_cmd spec int
                                             #> Proof.map_context Phi_ID.next
                                             #> tail_statement)
  end)))
(*
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>.\<close> "End a \<phi> program block using default tactic"
    (((option (\<^keyword>\<open>for\<close> |-- term) >> (fn cast => fn int => fn stat =>
       stat
    |> end_block_auto_proof_cmd cast int ))
   -- statement_cmd_tail (3,1))
   >> (fn (blk,tail_statement) => Toplevel.proof' (fn int =>
        tail_statement o Proof.map_context Phi_ID.next o blk int o Proof.map_context Phi_ID.next)))
*)
(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>interface\<close> "declare \<phi>interface"
      (Parse.binding --| $$$ "=" -- Parse.const -- option ($$$ ":" |-- Parse.typ --| $$$ "\<longmapsto>" -- Parse.typ)
        >> (Toplevel.theory o Phi_Procedure.add_interface_command))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>export_llvm\<close> "export LLVM target"
      (Scan.succeed (Toplevel.theory (Phi_Toplevel.export_LLVM))) *)

end

end
