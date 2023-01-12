(* FILE: library/system/toplevel.ML
   AUTHOR: Qiyuan Xu

   Definition of Isar commands for IDE-CP.
*)

signature PHI_TOPLEVEL = sig
  datatype cond_kind = Premise | Assumption

  val begin_proc_cmd : bool (*whether to define a new constant*)
        -> Attrib.binding (*name*)
        -> xstring (*argument*)
        -> xstring (*return*)
        -> xstring option (*throws*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (indexname list * string) list (*let patterns*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
        -> bool -> Proof.context -> Proof.state
  val begin_rec_proc_cmd : bool (*whether to define a new constant*)
        -> Attrib.binding 
        -> xstring (*argument*)
        -> xstring (*return*)
        -> xstring option (*throws*)
        -> ((binding * string option * mixfix) list * (*variants*)
            (binding * string option * mixfix) list   (*for fixes*))
        -> (xstring * Position.T) list (*includes*)
        -> (indexname list * string) list (*let patterns*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
        -> bool -> Proof.context -> Proof.state
  val begin_view_shift_cmd : Attrib.binding
        -> xstring (*domain*)
        -> xstring (*image*)
        -> xstring option (*addtional_prop,   cast domain |--> image with additional_prop*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (indexname list * string) list (*let patterns*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
        -> bool -> Proof.context -> Proof.state
  (* val begin_rec_proc_cmd : Attrib.binding 
        -> xstring (*argument and return*)
        -> (binding * string option * mixfix) list (*loop variables fixes*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> xstring option (*pre-conditions*)
        -> bool -> Proof.context -> Proof.state *)
  val begin_block_cmd : Attrib.binding list (*bindings of conditions*)
        -> bool -> Proof.state -> Proof.state
  val end_block_cmd : string option -> bool -> Proof.state -> Proof.state

  val statement_clean_values : bool Config.T (*controls whether the statement command \<^bold>;
        cleans all values at its beginning.*)
  val statement_cmd : (Proof.state -> Proof.state) parser

  val prove_prem : bool -> Proof.state -> thm list * Proof.state
  (*val export_LLVM : theory -> theory *)
end

structure Phi_Toplevel : PHI_TOPLEVEL = struct
open Phi_Help Phi_Basics Term HOLogic Thm Phi_Sys

(* fun mk_Trueprop (tm as (Const (@{const_name Trueprop}, _) $ _)) = tm
  | mk_Trueprop tm = HOLogic.mk_Trueprop tm *)

type context = Proof.context
type state = Proof.state
val register_label_head = "\<upsilon>"
val delimiter_name = "NuPrime.Stack_Delimiter"
val eof_ctx_stack_name = "NuPrime.End_of_Contextual_Stack"
fun mk_eof_ctx_stack tm = Const(eof_ctx_stack_name, dummyT) $ tm
val mk_register_collection = I
val elim_premise = [Thm.rule_attribute [] (fn _ => fn th =>
      if can PLPR_Syntax.dest_premise_tag (concl_of th) then th RS @{thm Premise_D} else th)]
(* fun mk_register_collection tm = Const(@{const_name RegisterCollection},
* dummyT) $ tm *)

(** proc command **)

val indTy = Type ("Nat.ind", [])
val arg_stat_term_name = "\<ss>"


val v_proc_var = ("\<p>\<r>\<o>\<c>",0)
val v_lrep_var = "\<l>\<r>\<e>\<p>"
val v_goal_name = "\<phi>goal"
val vv_proc_const_name = "?\<p>\<r>\<o>\<c>"
val top_blk_name = "\<t>\<o>\<p>_\<b>\<l>\<o>\<c>\<k>"

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



structure Blk_Level = Proof_Data (
  type T = int
  val init = K 0
)

fun inc_blk_level ctxt =
  let
    val i = Blk_Level.get ctxt
  in (i, Blk_Level.put (i+1) ctxt)
  end

fun dec_blk_level ctxt =
  let
    val i = Blk_Level.get ctxt
  in (i, Blk_Level.put (i-1) ctxt)
  end









fun gen_constr_envir prep_term prep_prop prep_typ prep_var prep_ctx mk_Goal
      binding arg ret throws rawfixes includes raw_lets raw_defines raw_preconds raw_goal_ctxt
      int ctxt =
  let
    val ((fixes,var_names), ctx_parse) = prep_decls prep_var rawfixes (prep_ctx ctxt)
    val binding = binding |> apsnd (map (Attrib.check_src ctxt))
    val pos = Binding.pos_of (fst binding)
    val parse_term = prep_term ctx_parse
    val parse_prop = prep_prop ctx_parse
    val parse_typ = prep_typ ctx_parse

    val lets = maps (fn (vs,t) => map (rpair (parse_term t)) vs) raw_lets
    val parse_term = parse_term #> Term.subst_Vars lets
    val parse_prop = parse_prop #> Term.subst_Vars lets

    fun map_trueprop f (Const (@{const_name Trueprop}, _) $ tm) = mk_Trueprop (f tm)
      | map_trueprop f tm = f tm
    fun prep_attrterm prep =
         (apfst (apsnd (map (Attrib.check_src ctxt))) #>
          apsnd (apfst (parse_prop #> map_trueprop prep)
                  #> apsnd (map parse_term)))
    val defines = map (prep_attrterm I) raw_defines

    fun prep_precond (Premise, c) =
          prep_attrterm (mk_monop @{const_abbrev Normal_Premise}) c
            |> apfst (apsnd (fn attrs =>
                  @{attributes [TRY_THEN Premise_D, useful]} @ attrs))
      | prep_precond (Assumption, c) =
          prep_attrterm I c
    val preconds = map prep_precond raw_preconds

    val (goal', constr_process, post_process, fixes', preconds') =
          mk_Goal (ctx_parse,fixes,var_names)
                  (parse_term arg,
                   parse_term ret,
                   (case throws of SOME thr => parse_term thr | NONE => Term.dummy),
                   preconds)

    val goal = case raw_goal_ctxt of NONE => goal'
                  | SOME G => Const (\<^const_name>\<open>GOAL_CTXT\<close>, dummyT)
                              $ goal'
                              $ parse_term G

    (* val [arg,ret] = Syntax.check_terms ctx_parse [arg,ret]
    val ctx_parse = ctx_parse |> Variable.declare_term arg |> Variable.declare_term ret *)
    val includes = includes |> map (Bundle.check ctxt)
    (* val (goal,th) = begin_proc ctx_parse (arg,ret)  *)
    val elems = [Element.Fixes fixes',
                 Element.Defines defines,
                 Element.Assumes (map (apsnd single) preconds')]
    val concls = Element.Shows [(Binding.empty_atts,[(goal,[])])]
    fun after_qed [[th]] lthy = post_process binding int lthy th
  in
    ctxt |> Specification.schematic_theorem false "" NONE after_qed Binding.empty_atts
              includes elems concls int
         |> Proof.map_context (
             let
               fun fetch names ctxt =
                 map (snd o Proof_Context.get_fact_generic ctxt o Facts.named) names |> flat
               fun bind_lets ctxt =
                 fold Proof_Context.bind_term (map (apsnd (Syntax.check_term ctxt)) lets) ctxt
             in
               bind_lets #>
               Context.proof_map (Named_Theorems.clear \<^named_theorems>\<open>\<phi>lemmata\<close>)
             end)
         |> constr_process
  end

fun gen_begin_proc prep_term prep_prop prep_typ prep_var prep_Nu post_process def_const =
  let
    val prep_ctx = I
    fun mk_Goal (ctxt,fixes,_) arg_ret_throws_conds =
      let
        val (arg, ret, throws', preconds) = prep_Nu ctxt arg_ret_throws_conds
        (*val _ = debug_term ctxt "arg " arg
        val _ = debug_term ctxt "ret " ret*)
        val arg = Procedure_Syntax.translate_arg arg
        val ret = Procedure_Syntax.translate_ret ret
        val v_proc = Var (v_proc_var, dummyT)
        val throws = if throws' = Term.dummy
                     then Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, dummyT)
                     else throws'
        val goal = mk_Trueprop
          (Const (@{const_name \<phi>Procedure}, dummyT) $ v_proc $ arg $ ret $ throws)

        fun constr_process stat =
          let
            val goal_proc = Thm.cprem_of (#goal (Proof.goal stat)) 1
                         |> Drule.strip_imp_concl
          in
            stat
              |> Proof.map_context (put_thesis goal_proc)

          end
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
      in
        (goal, constr_process, post_process', fixes, preconds)
      end
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var prep_ctx mk_Goal
  end
    
val begin_proc =
      gen_begin_proc (K I) (K I) (K I) Proof_Context.cert_var (K I) (K I)
val begin_proc_cmd =
      gen_begin_proc Syntax.parse_term Syntax.parse_prop Syntax.parse_typ Proof_Context.read_var
        (fn ctxt => fn (arg,ret,throws,conds) =>
          (arg, ret, throws, conds)
        ) (K I)

fun gen_begin_rec_proc prep_term prep_prop prep_typ prep_var
      def_const (binding,attr) raw_arg raw_ret raw_throw (raw_vars, raw_fixes) =
  let open QuantExpansion
    val prep_ctx = I
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

        val conds' = map (snd #> fst #> perhaps (try dest_Trueprop)) conds
        val arg' = arg
              |> fold_rev (fn c => fn Nu =>
                    Phi_Help.mk_binop @{const_name Subjection} (Nu,c)) conds'
              |> tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)
        val ret' = ret
              |> tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)
        val throws' = (if throws = Term.dummy
                       then Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, dummyT)
                       else throws)
              |> tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)

        val goal0 = mk_Trueprop (
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
                       (All::forall:: @{thm Subjection_simp_proc_arg_metaeq} ::
                        Named_Theorems.get ctxt'' @{named_theorems named_expansion})
                      #> Seq.single))
            |> Seq.maps (Phi_Reasoner.reason_tac NONE ctxt'' o pair ctxt'')
            |> Seq.the_result "fail to reason sematic type of the procedure."

        val goal' = Thm.cprem_of proof0 1 |> Thm.term_of |> dest_Trueprop
        
        val vars' = strip_binder_vars @{const_name All} goal'
        val vars'_fix = map (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) vars'
        val (var_names',ctxt''') = Proof_Context.add_fixes (take 1 vars'_fix) ctxt''
                                    |> apfst (fn vn => vn @ map fst (drop 1 vars'))
        val vars'' = map (apsnd snd) (var_names' ~~ vars')

        val prems_goal =
          subst_bounds (rev (map Free vars''),
            strip_binder_raw_body @{const_name All} goal')
          |> strip_binop_r @{const_name "HOL.implies"}
          |> map mk_Trueprop
        val (prems, goal) = (front prems_goal, last prems_goal)

        val conds' = ((Binding.name func_name,[]),(hd prems,[])) ::
              (map (fn (tm,(b,(_,is))) => (b,(tm,is))) (tl prems ~~ conds))

        fun constr_process stat =
          let
            val goal_proc = Thm.cprem_of (#goal (Proof.goal stat)) 1
                         |> Drule.strip_imp_concl
          in
            stat
              |> Proof.map_context (put_thesis goal_proc)

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
    gen_constr_envir prep_term prep_prop prep_typ prep_var prep_ctx mk_Goal
        (binding,attr) raw_arg raw_ret raw_throw (raw_vars @ raw_fixes)
  end

val begin_rec_proc_cmd = gen_begin_rec_proc
      Syntax.parse_term Syntax.parse_prop Syntax.parse_typ Proof_Context.read_var

fun gen_begin_view_shift_cmd prep_term prep_prop prep_typ prep_var
      binding arg ret additional_prop =
  let
    fun mk_Goal (ctxt,fixes,_) (arg, ret, _, preconds) =
      let
        val arg = arg
        val ret = ret
        val additional_prop = case additional_prop
                                of SOME x => prep_term ctxt x
                                 | _ => @{term True}
        val goal = mk_Trueprop
          (Const (@{const_name View_Shift}, dummyT) $ arg $ ret $ additional_prop)
        fun constr_process stat =
          let
            val ctxt = Proof.context_of stat
            val arg = Syntax.check_term ctxt arg
            val Type (@{type_name set}, [ty]) = fastype_of arg
            val ([lrep_name],stat) = Proof.map_context_result (Proof_Context.add_fixes
                                        [(Binding.name v_lrep_var, SOME ty, NoSyn)]) stat
            val sequent_term = mk_Trueprop (
                  Const (@{const_name Set.member}, dummyT) $ Free (lrep_name, ty) $ arg)
                    |> Syntax.check_prop ctxt
            val ([(_,[sequent])],stat) = Proof.map_context_result (
                  Proof_Context.add_assms Assumption.assume_export
                      [(Binding.empty_atts, [(sequent_term,[])])]) stat
          in
            (*Phi_Basics.set_state_sequent sequent*)
            stat
          end
        fun post_process binding int lthy th =
          (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
            (("\<phi> view shift", ""), [("", [th])]); lthy)
      in
        (goal, constr_process, post_process, fixes, preconds)
      end
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var I mk_Goal binding arg ret NONE
  end

val begin_view_shift_cmd =
      gen_begin_view_shift_cmd Syntax.parse_term Syntax.parse_prop Syntax.parse_typ
      Proof_Context.read_var



(* structure Statement_Begin_Hook *)
(*
structure Procedure_Begin_Hook = Generic_Data (
  type T = (context_state -> context_state) list
  val init = K []
) *)



local

fun basic_method r = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (r ctxt)))

fun gen_finish_proc prep_term qed spec int stat =
  let
    val ctxt_ = Proof.context_of stat
    val goal = get_thesis ctxt_
    val mode = Phi_Working_Mode.working_mode_on1 ctxt_ (Thm.term_of goal)
  in stat
  |> Proof.map_context (dec_blk_level #> snd)
  |> Proof.map_context_result (fn ctxt_pre1 =>
      let
        val sequent_pre1 = Phi_Basics.the_programming_sequent' ctxt_pre1
        val (ctxt,sequent) =
          if Thm.no_prems sequent_pre1
          then (ctxt_pre1,sequent_pre1)
          else let
            val _ = Phi_Reasoner.debug_info ctxt_pre1 (fn _ =>
                      (\<^here>, "solving pending antecedents before closing the programming block..."))
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
                               Syntax.pretty_term ctxt'' (Thm.term_of aim)
                            ] |> pair \<^here>)
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
              |> #before_finish mode goal
        val desired_nu = #return_spec_c mode ctxt' goal
        val _ = Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.block [
                  Pretty.str "casting to the destined post-condition ",
                  Syntax.pretty_term ctxt'' (Thm.term_of desired_nu)
                ] |> pair \<^here>)
      in
        (ctxt'',sequent'')
          (* |> invoke_Block_End_Hook *)
          |> Phi_Sys.cast desired_nu
          |> swap
        (*The transformation shall generate a poof obligation*)
      end
    )
        (*and the proof obligation is presented to users here.*)
    |-> Phi_Sys.obligation_proof (print_results int) Proof_Context.mode_schematic false "" NONE
          (fn sequent => fn stat =>
      let
        val ctxt = Proof.context_of stat
        val end_tac = basic_method (fn ctxt' => fn goal => (
            let
              val sequent' = singleton (Proof_Context.export ctxt ctxt') sequent
              val _ = Phi_Reasoner.debug_info ctxt' (fn _ =>
                  Pretty.string_of (Pretty.chunks [
                    Pretty.str "Solving the goal by the resulted sequent from the programming.",
                    Pretty.item [Pretty.str "goal:"],
                    Syntax.pretty_term ctxt' (fst (Logic.dest_implies (Thm.prop_of goal))),
                    Pretty.item [Pretty.str "resulted sequent:"],
                    Thm.pretty_thm ctxt' sequent'
                  ]) |> pair \<^here>)
                val result = NuApply.MP ctxt' sequent' goal
              in result end
            ))
       in
        stat
          |> Proof.set_facts [] 
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
    val specthm = the_state_sequent stat
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
             |-> Phi_Basics.set_state_sequent
      end
  in
    stat |> setup_proof (print_results int) Proof_Context.mode_schematic false ""
              NONE after_qed [] [] [[(goal,[])]]
         |> apsnd (
              Proof.map_context (Proof_Context.set_mode Proof_Context.mode_default)
           #> Proof.refine (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (
                HEADGOAL (resolve_tac ctxt @{thms Premise_I})
              ))) #> Seq.the_result "should never fail"
            )
  end


local
val attr_useful = map (Attrib.attribute @{context}) @{attributes [useful]}
fun is_backward_mode s = (Proof.assert_backward s; true)
      handle ERROR _ => false
in

fun gen_begin_block prep_attr bindings int stat =
  let open Proof
    val ctxt = context_of stat

    val is_top = not (Phi_Basics.under_programming_environ ctxt) orelse is_backward_mode stat
    val normalize_tac =
          REPEAT_DETERM (HEADGOAL (Tactic.resolve_tac ctxt @{thms GOAL_CTXT_I Argument_I allI impI}))
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
          else the_state_sequent stat
                  |> Tactic.rule_by_tactic ctxt normalize_tac
    val stat = (if is_top then enter_forward (assert_backward stat) else stat)
                  |> begin_block

    (*Assuming the proof state is in the normal hhf, or else the operation fails.*)
    val (vars, goal) =
          strip_binder_raw @{const_name Pure.all} (leading_antecedent' sequent)
    val (var_names, stat) =
          Proof.map_context_result (Proof_Context.add_fixes
            (map (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) vars)) stat
    val vars = map Free (var_names ~~ map snd vars)
    val goal = subst_bounds (rev vars, goal)
    val prems_goal = strip_binop_r @{const_name Pure.imp} goal
    val (prems, goal) = (front prems_goal, last prems_goal)

    val mode = Phi_Working_Mode.working_mode_on1 ctxt goal

    val arg = #argument_spec mode goal
    val blk_name = #block_name_of mode goal
    val (level, stat) = Proof.map_context_result inc_blk_level stat
    val blk_name = "\<L>" ^ (Int.toString level) ^ "_" ^ blk_name

    fun after_qed (ctxt',[[th]]) stat0 =
      let val stat = end_block stat0
          val ctxt'' = context_of stat
          val th0 = Drule.eta_contraction_rule th
          val (th1::vars') = (th0::map (Drule.mk_term o cterm_of ctxt') vars)
                                   |> Proof_Context.export ctxt' ctxt''
          val th2 = Drule.forall_intr_list (map Drule.dest_term vars') th1

          fun gen_sequent sequent =
            let val insts =
                      Pattern.match (Proof_Context.theory_of ctxt'')
                                    (Phi_Help.leading_antecedent' sequent, Thm.prop_of th2)
                                    (Vartab.empty, Vartab.empty)
                      |> Phi_Help.env_to_table ctxt''
                handle Pattern.Pattern => error (Pretty.string_of (Pretty.chunks [
                      Pretty.str "The higher-order pattern match fails",
                      Pretty.block [Pretty.str "from ",
                                    Syntax.pretty_term ctxt'' (Phi_Help.leading_antecedent' sequent)],
                      Pretty.block [Pretty.str "to ",
                                    Syntax.pretty_term ctxt'' (Thm.prop_of th2)],
                      Pretty.str "which usually means some schematic variable is instantiated to\
                        \some universally quantified variables that it has no access."
                    ]))
                val sequent' = Thm.instantiate insts sequent
             in Thm.implies_elim (Phi_Help.beta_eta_contract sequent')
                                 (Phi_Help.beta_eta_contract th2) end
      in if is_top
         then stat
                |> enter_backward
                |> apply (Method.Basic (fn _ => Method.SIMPLE_METHOD (Seq.single o gen_sequent)),
                          Position.no_range)
                |> Seq.the_result "never fail"
         else Phi_Basics.set_state_sequent (gen_sequent sequent) stat
      end

    val delta = length prems - length bindings
    val _ = if delta < 0 then error "too much premise bindings" else  ()
    val bindings =
      ((map (apsnd (map (prep_attr ctxt))
          #> apfst (fn x => if Binding.name_of x = "_" then Binding.empty else x)
            ) bindings)
          @ (List.tabulate (delta, K (Binding.empty, attr_useful))))
        |> map (apsnd (fn x => elim_premise @ x))
  in
    stat
      |> internal_goal (print_results int) Proof_Context.mode_schematic false 
          "" NONE after_qed []
          (bindings ~~ (map (single o rpair []) prems))
          [(Binding.empty_atts, [(goal,[])])] |> #2
      |> Proof.map_context (Proof_Context.set_mode Proof_Context.mode_default)
      |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
            Context_Tactic.CONTEXT_TACTIC all_tac), Position.no_range))
      |> Seq.the_result "never fail"
      |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)

      |> Proof.map_context_result (fn ctxt => ctxt
            |> Phi_Working_Mode.set mode
            |> Proof_Context.put_thms false ("\<phi>thesis",
                          SOME [Drule.mk_term (cterm_of ctxt goal)])
            |> #initial_sequent mode blk_name (cterm_of ctxt arg)
            |> Generic_Variable_Access.open_value_context' Position.none
            |> swap)
      |-> (if is_top then Phi_Basics.enter_programming_environ else Phi_Basics.set_state_sequent)
(*      |> Generic_Variable_Access.open_value_context' Position.none *)
      (* |> NuObtain.obtain_quick_pairs_perhaps_try *)
  end
val begin_block_cmd = gen_begin_block Attrib.attribute_cmd
val begin_block = gen_begin_block (K I)
end


(*Whether to remove all values at the beginning of the command \<^bold>;*)
val statement_clean_values = Attrib.setup_config_bool \<^binding>\<open>\<phi>statement_clean_values\<close> (K true)

fun clean_values (ctxt,sequent) =
      if can Phi_Syntax.dest_CurrentConstruction (Thm.prop_of sequent)
         andalso Config.get ctxt statement_clean_values
      then (ctxt, Generic_Variable_Access.collect_and_clean_value true ctxt sequent |> fst)
      else (ctxt, sequent)

val statement_cmd =
  Phi_Processor.powerful_process_p >> (fn f => fn stat =>
    stat |> Phi_Basics.map_state_sequent clean_values
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

end
