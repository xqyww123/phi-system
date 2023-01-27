(* FILE: library/system/toplevel.ML
   AUTHOR: Qiyuan Xu

   Definition of Isar commands for IDE-CP.
*)

signature PHI_TOPLEVEL = sig

  datatype cond_kind = Premise | Assumption

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

  val begin_block :   binding list (*fixed variables*)
                    * (Attrib.binding * term list) list (*bindings of conditions*)
        -> bool -> Proof.state -> Proof.state
  val begin_block_cmd :   binding list (*fixed variables*)
                        * (Attrib.binding * string list) list (*bindings of conditions*)
        -> bool -> Proof.state -> Proof.state
  val end_block_cmd : string option -> bool -> Proof.state -> Proof.state

  val statement_clean_values : bool Config.T (*controls whether the statement command \<^bold>;
        cleans all values at its beginning.*)
  val statement_cmd : (Proof.state -> Proof.state) parser

  val prove_prem : bool -> Proof.state -> thm list * Proof.state
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
  | merge_premises_bindings ((SOME ((_,A1),P1))::R1) (((B,A2),P2)::R2)
      = ((B, A1@A2), P1@P2) :: merge_premises_bindings R1 R2
  | merge_premises_bindings [] (_::_)
      = error "Too much premises bindings given"

in

fun gen_begin_block prep_attr prep_prop (var_bindings,prem_bindings0) int stat =
  let
    val ctxt = Proof.context_of stat

    val is_top = not (Phi_Envir.under_programming_environ ctxt) orelse is_backward_mode stat
    val normalize_tac =
          REPEAT_DETERM (HEADGOAL (Tactic.resolve_tac ctxt
              @{thms Action_Tag_I Argument_I allI impI Labelled_I Labelled_I'}))
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
                  |> Tactic.rule_by_tactic ctxt normalize_tac
    val stat = (if is_top then Proof.enter_forward (Proof.assert_backward stat) else stat)
                  |> Proof.begin_block

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

    val stat = if is_top then Proof.refine_primitive (K (K sequent)) stat else stat


    (*Assuming the proof state is in the normal hhf, or else the operation fails.*)
    val (vars, goal) =
          Phi_Help.strip_binder_raw @{const_name Pure.all} (Phi_Help.leading_antecedent' sequent)
    val vb_N = length var_bindings
    val (var_names, stat) =
          Proof.map_context_result (Proof_Context.add_fixes
            (map2 (fn (_,ty) => fn b => (b, SOME ty, NoSyn)) (List.take (vars, vb_N)) var_bindings
           @ map  (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) (List.drop (vars, vb_N)))
          ) stat
    val vars = map Free (var_names ~~ map snd vars)
    val goal = subst_bounds (rev vars, goal)
            |> reduce_var
    val prems_goal = Phi_Help.strip_binop_r @{const_name Pure.imp} goal
    val (prems, goal') = (Phi_Help.front prems_goal, Phi_Help.last prems_goal)

    val mode = Phi_Working_Mode.working_mode_on1 ctxt goal'
    val goal'c = Thm.cterm_of ctxt goal'
    val arg = #source_spec_c mode goal'c

    fun after_qed (ctxt',[[th]]) stat0 =
      let val stat = Proof.end_block stat0
          val ctxt'' = Proof.context_of stat
          val th0 = Drule.eta_contraction_rule th
          val (th1::vars') = (th0::map (Drule.mk_term o Thm.cterm_of ctxt') vars)
                                   |> Proof_Context.export ctxt' ctxt''
          val th2 = Drule.forall_intr_list (map Drule.dest_term vars') th1

          fun gen_sequent sequent0 =
            let val sequent = Phi_Help.beta_eta_contract_leading_antecedent sequent0
                val insts =
                      Pattern.match (Proof_Context.theory_of ctxt'')
                                    (Phi_Help.leading_antecedent' sequent, Thm.prop_of th2)
                                    (Vartab.empty, Vartab.empty)
                      |> Phi_Help.env_to_table ctxt''
                handle Pattern.MATCH => error (Pretty.string_of (Pretty.chunks [
                      Pretty.str "The higher-order pattern match fails",
                      Pretty.block [Pretty.str "from ",
                                    Syntax.pretty_term ctxt'' (Phi_Help.leading_antecedent' sequent)],
                      Pretty.block [Pretty.str "to ",
                                    Syntax.pretty_term ctxt'' (Thm.prop_of th2)],
                      Pretty.str "which usually means some schematic variable is instantiated to\
                        \ some universally quantified variables that it has no access."
                    ]))
                val sequent' = Thm.instantiate insts sequent (*index is considered*)
             in Thm.implies_elim (Phi_Help.beta_eta_contract_leading_antecedent sequent')
                                 (Phi_Help.beta_eta_contract th2)end
      in if is_top
         then stat
                |> Proof.enter_backward
                |> Proof.apply (Method.Basic (fn _ =>
                        Method.SIMPLE_METHOD (Seq.single o gen_sequent)), Position.no_range)
                |> Seq.the_result "never fail"
         else Phi_Envir.set_state_sequent (gen_sequent sequent) stat
      end

    val delta = length prems - length prem_bindings
    val _ = if delta < 0 then error "too much premise bindings" else  ()
    val bindings = (prem_bindings @ (List.tabulate (delta, K ((Binding.empty, []),[]))))
          |> map2 (fn P => fn ((b,attrs),pats) =>
              let val attrs' = Premises_Attribute.attribute_of (null attrs) P (Context.Proof ctxt)
              in ((b, attrs' @ map (Attrib.attribute ctxt) attrs), pats)
              end) prems
  in
    stat
      |> Proof.internal_goal (print_results int) Proof_Context.mode_schematic true 
          "" NONE after_qed []
          (map2 (fn (b,pats) => fn P => (b,[(P,pats)])) bindings prems)
          [(Binding.empty_atts, [(goal',[])])] |> #2
      |> Proof.map_context (Proof_Context.set_mode Proof_Context.mode_default)
      |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
            Context_Tactic.CONTEXT_TACTIC all_tac), Position.no_range))
      |> Seq.the_result "never fail"
      |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)

      |> Proof.map_context_result (fn ctxt => ctxt
            |> Phi_Working_Mode.set mode
            |> Phi_Envir.put_thesis goal'c
            |> #initial_sequent mode arg
            |> swap)
      |-> Phi_Envir.enter_programming_environ
      |> Proof.begin_block
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
    val mode = Phi_Working_Mode.mode ctxt_
  in stat
  |> Proof.map_context_result (fn ctxt_pre1 =>
      let
        val sequent_pre1 = Phi_Envir.the_programming_sequent' ctxt_pre1
        val (ctxt,sequent) =
          if Thm.no_prems sequent_pre1
          then (ctxt_pre1,sequent_pre1)
          else let
            val _ = Phi_Reasoner.debug_info ctxt_pre1 (fn _ =>
                      "solving pending antecedents before closing the programming block..."
                      ^ Position.here \<^here>)
            fun attack_obligations (ctxt,sequent) =
              case try Thm.major_prem_of sequent
                of SOME (\<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ _)) =>
                    attack_obligations (Phi_Reasoners.auto_obligation_solver1 (ctxt,sequent))
                 | _ => (ctxt,sequent)
            val (ctxt_pre2, sequent_pre2) = attack_obligations (ctxt_pre1, sequent_pre1)
            in Phi_Reasoner.reason1 (fn _ => Pretty.string_of (Pretty.chunks [
                    Pretty.str "Fail to solve pending antecedents:",
                    Thm.pretty_thm ctxt_pre2 sequent_pre2
               ])) NONE (ctxt_pre2,sequent_pre2)
            end
        val (ctxt',sequent') = Phi_Sys.move_lemmata (ctxt, sequent)
        val (ctxt'',sequent'') = (ctxt',sequent')
              |> (case spec
                    of NONE => I
                     | SOME term =>
                        let val ctxt'' = Proof_Context.set_mode (Proof_Context.mode_pattern) ctxt'
                            val aim = Thm.cterm_of ctxt'' (prep_term ctxt'' term)
                            val _ = Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.block [
                               Pretty.str "transforming to the given specification ",
                               Syntax.pretty_term ctxt'' (Thm.term_of aim),
                               Pretty.block (Pretty.here \<^here>)
                            ])
                        in Phi_Sys.cast aim
                        #> Phi_Reasoners.auto_obligation_solver' (fn (ctxt,sequent) =>
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
                           ])))
                        end)
              |> #vcg_before_assembling mode goal
      in (sequent'', Phi_Envir.exit_programming_environ ctxt'')
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
          |> Proof.end_block
        val end_tac = basic_method (fn ctxt' => fn goal' => (
            let
              val sequent' = singleton (Proof_Context.export ctxt ctxt') sequent
              val _ = Phi_Reasoner.debug_info ctxt' (fn _ =>
                  Pretty.string_of (Pretty.chunks [
                    Pretty.str "Solving the goal by the resulted sequent from the programming.",
                    Pretty.item [Pretty.str "goal:"],
                    Syntax.pretty_term ctxt' (fst (Logic.dest_implies (Thm.prop_of goal'))),
                    Pretty.item [Pretty.str "resulted sequent:"],
                    Thm.pretty_thm ctxt' sequent',
                    Pretty.block (Pretty.here \<^here>)
                  ]))
                val (_,result) = NuApply.apply [sequent'] (ctxt',goal')
                              |> Phi_Reasoners.safer_obligation_solver1
              in result end
            ))
       in
        stat'
          |> qed (SOME (end_tac, Position.no_range), false)
       end) [] []
     |> snd
  end
in
val end_block_cmd = gen_finish_proc Syntax.read_term Proof.local_qed

(* fun gen_finish_proc' prep_specthm qed int stat =
  let val sequent = Proof.the_fact stat
  in if current_block_depth sequent > 1 then 
      gen_finish_proc' prep_specthm qed int (end_block_cmd false stat)
    else gen_finish_proc prep_specthm qed int stat end *)
val finish_proc_cmd = gen_finish_proc Syntax.read_term Proof.local_qed
end



fun prove_prem int stat =
  let open Proof
    val specthm = Phi_Envir.the_state_sequent stat
    val goal = Thm.prop_of specthm
                |> Logic.dest_implies |> #1 (* |> dest_premise_tag |> mk_Trueprop *)
    fun after_qed (ctxt',[[th]]) stat =
      let
        val [th] = Proof_Context.export ctxt' (context_of stat) [th]
        val original_auto_level = Config.get (Proof.context_of stat) Phi_Reasoner.auto_level
        (* val th = th RS @{thm NuPrime.Premise_I} *)
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
  end


(** Header of Procedure **)


fun gen_begin_proc prep_term prep_prop prep_var post_process def_const
      binding arg ret throws rawfixes includes raw_defines raw_preconds action
      int lthy =
  let
    val includes = includes |> map (Bundle.check lthy)
    val ((fixes,var_names), ctxt_parse) = lthy
                                       |> not (null includes) ? Bundle.includes includes
                                       |> prep_decls prep_var rawfixes
    val binding = binding |> apsnd (map (Attrib.check_src lthy))
    val parse_term = prep_term ctxt_parse
    val parse_prop = prep_prop ctxt_parse

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
    val goal0 = \<^const>\<open>Trueprop\<close> $
                  (Const (@{const_name \<phi>Procedure}, dummyT) $ v_proc $ arg $ ret $ throws)
    val goal = (case action of NONE => goal0
                   | SOME A => \<^Const>\<open>Action_Tag dummyT\<close> $ goal0 $ parse_term A)
            |> fold_rev (fn (_,(P,_)) => fn X => \<^const>\<open>Pure.imp\<close> $ P $ X) preconds

    fun post_process' binding int lthy th =
      lthy
        |> Phi_Procedure.define def_const binding (
            (lthy, (th RSN (3, @{thm "\<phi>__final_proc_rewrite__"})
                      handle THM _  => (th RSN (3, @{thm "\<phi>__final_proc_rewrite__'"}))))
              |> Phi_Reasoner.reason NONE
              |> (fn SOME (lthy', th) => post_process lthy' th
                   | NONE => error("Fail to simplify finally the procedure.\n"^
                                   "It is a rare error and you may check the simplification "^
                                   "rules of procedure_simps")))
        |-> (fn th => fn lthy =>
              (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
                (("\<phi>procedure", ""), [("", [th])]); lthy))

    val defines = map (prep_attrterm parse_prop) raw_defines
    val elems = [Element.Fixes fixes, Element.Defines defines]
    val concls = Element.Shows [(Binding.empty_atts,[(goal,[])])]
    fun after_qed [[th]] lthy = post_process' binding int lthy th
  in
    lthy |> Specification.schematic_theorem false "" NONE after_qed Binding.empty_atts
              includes elems concls int
         |> Proof.map_context (Context.proof_map (Named_Theorems.clear \<^named_theorems>\<open>\<phi>lemmata\<close>))
         |> (fn stat => stat
              |> Proof.map_context (Phi_Envir.put_thesis (
                    Thm.cprem_of (#goal (Proof.goal stat)) 1
                      |> Drule.strip_imp_concl
                  )))
         |> Proof.refine (Method.Basic (K (K (
              Named_Premises.bind_sequent_assms (map (apsnd snd) preconds) 1
                #> Seq.Result #> Seq.single))))
         |> Seq.the_result "should never fail #gn9[q3"
  end

val begin_proc =
      gen_begin_proc (K I) (K I) Proof_Context.cert_var (K I)
val begin_proc_cmd =
      gen_begin_proc Syntax.parse_term Syntax.parse_prop Proof_Context.read_var (K I)


(* fun gen_begin_rec_proc prep_term prep_prop prep_var
      def_const (binding,attr) raw_arg raw_ret raw_throw (raw_vars, raw_fixes) =
  let open QuantExpansion
    val prep_ctxt = I
    val func_name = Binding.name_of binding
    fun mk_Goal (ctxt,fixes,fixed_names) (raw_arg,raw_ret,raw_throws,conds) = 
      let
        val ([tArg,tRet], ctxt') =
                Variable.variant_fixes ["\<tau>Arg", "\<tau>Ret"]
                  (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)
        val origin_names = map (fn (n,_,_) => (Binding.name_of n)) raw_vars
        val var_names = take (length raw_vars) fixed_names
        val vars = origin_names ~~ (map (rpair dummyT) var_names)

        val arg = Procedure_Syntax.translate_arg raw_arg
        val ret = Procedure_Syntax.translate_ret raw_ret
        val throws = raw_throws

        val conds' = map (snd #> fst #> perhaps (try HOLogic.dest_Trueprop)) conds
        val arg' = arg
              |> fold_rev (fn c => fn Nu =>
                    Phi_Help.mk_binop @{const_name Subjection} (Nu,c)) conds'
              |> Phi_Help.tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)
        val ret' = ret
              |> Phi_Help.tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)
        val throws' = (if throws = Term.dummy
                       then Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, dummyT)
                       else throws)
              |> Phi_Help.tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)

        val goal0 = \<^const>\<open>Trueprop\<close> $ (
              Const (@{const_name All}, dummyT) $ Abs("x", dummyT,
                (Const (@{const_name \<phi>Procedure}, dummyT)
                  $ (Const ("local.op_recursion", dummyT) (*TODO ! ! ! BUG !*)
                      $ Var ((tArg,0), dummyT)
                      $ Var ((tRet,0), dummyT)
                      $ Var ((func_name,0), dummyT))
                  $ arg'
                  $ ret'
                  $ throws')))
        val other_frees = Term.add_frees goal0 []
                       |> filter_out (fn (v,_) => exists (fn u => v = u) fixed_names)
        val (_,ctxt'') = Proof_Context.add_fixes
                            (map (fn (nam,_) => (Binding.name nam, NONE, NoSyn)) other_frees)
                            ctxt'
              

        val All = pure_All_expansion origin_names ctxt''
        val forall = forall_expansion origin_names ctxt''
        val recursion_thm = Proof_Context.get_thm ctxt'' "local.__op_recursion__" (*TODO*)
        val (_,proof0) = goal0
            |> Syntax.check_term ctxt'' |> Thm.cterm_of ctxt''
            |> Goal.init
            |> (HEADGOAL (resolve_tac ctxt'' [recursion_thm])
                THEN (Raw_Simplifier.rewrite_rule ctxt'' (*improve this!*)
                       (All::forall:: @{thm norm_precond_conj_metaeq} ::
                        Named_Theorems.get ctxt'' @{named_theorems named_expansion})
                      #> Seq.single))
            |> Seq.maps (Phi_Reasoner.reason_tac NONE ctxt'' o pair ctxt'')
            |> Seq.the_result "fail to reason sematic type of the procedure."

        val goal' = Thm.cprem_of proof0 1 |> Thm.term_of |> HOLogic.dest_Trueprop
        
        val vars' = Phi_Help.strip_binder_vars @{const_name All} goal'
        val vars'_fix = map (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) vars'
        val (var_names',ctxt''') = Proof_Context.add_fixes (take 1 vars'_fix) ctxt''
                                    |> apfst (fn vn => vn @ map fst (drop 1 vars'))
        val vars'' = map (apsnd snd) (var_names' ~~ vars')

        val prems_goal =
          subst_bounds (rev (map Free vars''),
            Phi_Help.strip_binder_raw_body @{const_name All} goal')
          |> Phi_Help.strip_binop_r @{const_name "HOL.implies"}
          |> map HOLogic.mk_Trueprop
        val (prems, goal) = (Phi_Help.front prems_goal, Phi_Help.last prems_goal)

        val conds' = ((Binding.name func_name,[]),(hd prems,[])) ::
              (map (fn (tm,(b,(_,is))) => (b,(tm,is))) (tl prems ~~ conds))

        fun constr_process stat =
          let
            val goal_proc = Thm.cprem_of (#goal (Proof.goal stat)) 1
                         |> Drule.strip_imp_concl
          in
            stat
              |> Proof.map_context (Phi_Envir.put_thesis goal_proc)

          end
        fun post_process' binding int lthy th =
          lthy
            |> Phi_Procedure.define def_const binding (
                th |> Drule.forall_intr_list
                        (map ( Thm.cterm_of lthy
                             o map_types (map_type_tvar (fn ((name,_),s) => TVar ((name,0),s)))
                             o map_aterms (fn (Var ((name,_),ty)) => Var ((name,0),ty) | x => x)
                             o Morphism.term (Proof_Context.export_morphism ctxt''' lthy)
                             o Free) vars'')
                   |> Conv.fconv_rule (Conv.repeat_changed_conv (Object_Logic.atomize lthy))
                   |> (fn sol => NuApply.MP lthy sol
                                    (singleton (Proof_Context.export ctxt''' lthy) proof0))
                   |> Goal.conclude
                   |> Object_Logic.rulify lthy
                 |> (fn th' => (lthy,
                        (th' RSN (3, @{thm "\<phi>__final_proc_rewrite__"})
                          handle THM _  => (th' RSN (3, @{thm "\<phi>__final_proc_rewrite__'"}))))
                   |> Phi_Reasoner.reason NONE
                   |> (fn SOME (_, th) => th
                        | NONE => error("Fail to simplify finally the procedure.\n"^
                                        "It is a rare error and you may check the simplification "^
                                        "rules of procedure_simps")))
               )
            |-> (fn th => fn lthy =>
                   (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
                      (("\<phi>procedure", ""), [("", [th])]); lthy))
      in
        (goal, constr_process, post_process', vars'_fix @ drop (length raw_vars) fixes, conds')
      end
  in
    gen_constr_envir prep_term prep_prop prep_var prep_ctxt mk_Goal
        (binding,attr) raw_arg raw_ret raw_throw (raw_vars @ raw_fixes)
  end

val begin_rec_proc_cmd =
      gen_begin_rec_proc Syntax.parse_term Syntax.parse_prop Proof_Context.read_var

*)



(** Statement **)

(*Whether to remove all values at the beginning of the command \<^bold>;*)
val statement_clean_values = Attrib.setup_config_bool \<^binding>\<open>\<phi>statement_clean_values\<close> (K true)

fun clean_values (ctxt,sequent) =
      if can Phi_Syntax.dest_CurrentConstruction (Thm.prop_of sequent)
         andalso Config.get ctxt statement_clean_values
      then (ctxt, Generic_Variable_Access.collect_and_clean_value true ctxt sequent |> fst)
      else (ctxt, sequent)

val statement_cmd =
  Phi_Processor.powerful_process_p >> (fn f => fn stat =>
    stat |> Phi_Envir.map_state_sequent clean_values
         |> f
  )




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
val requires_statement = \<^keyword>\<open>assumes\<close> |-- Parse.!!! statement1;
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
      -- Parse.for_fixes) >>
      (fn ((((((((((def_const,b),includes),prec1),arg),prec2),ret),throws),G),defs),fixes) =>
        begin_proc_cmd def_const b arg ret throws fixes includes defs (prec1 @ prec2) G))

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
    (statement_cmd >> Toplevel.proof)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "Begin a \<phi> program block"
   (((  optional (\<^keyword>\<open>for\<close> |-- list1 Parse.binding) []
     -- optional (\<^keyword>\<open>premises\<close> |--
            and_list ((binding -- opt_attribs || attribs >> pair Binding.empty) -- ppats)) []
      >> begin_block_cmd)
   -- Phi_Processor.powerful_process_p_inert)
   >> (fn (blk,prcs) => Toplevel.proof' (prcs oo blk)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "End a \<phi> program block"
    (option (\<^keyword>\<open>for\<close> |-- term) >> (Toplevel.proof' o end_block_cmd))

val _ = let
  fun repeat_future_proof s =
    if Proof.goal_finished s then s
    else s
      |> Proof.using_facts (Proof_Context.get_thms (Proof.context_of s) "\<phi>")
      |> Proof.local_future_terminal_proof
          ((Method.Basic (SIMPLE_METHOD o CHANGED_PROP o auto_tac), Position.no_range), NONE)
  fun repeat_future_proof0 s =
    if Proof.goal_finished s
    then Proof.local_done_proof s
    else repeat_future_proof s
in
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>.\<close> "End a \<phi> program block using default tactic"
    (((option (\<^keyword>\<open>for\<close> |-- term) >> (fn cast => fn int => fn stat =>
       stat
    |> end_block_cmd cast int
    |> repeat_future_proof0))
   -- Phi_Processor.powerful_process_p_inert)
   >> (fn (blk,prcs) => Toplevel.proof' (prcs oo blk)))
end

(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>interface\<close> "declare \<phi>interface"
      (Parse.binding --| $$$ "=" -- Parse.const -- option ($$$ ":" |-- Parse.typ --| $$$ "\<longmapsto>" -- Parse.typ)
        >> (Toplevel.theory o Phi_Procedure.add_interface_command))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>export_llvm\<close> "export LLVM target"
      (Scan.succeed (Toplevel.theory (Phi_Toplevel.export_LLVM))) *)

end

end
