(*  Title:      NuToplevel.ML
    Author:     Qiyuan Xu

The toplevel structure of the ν-system.

`begin_proc (argument-statement, for-fixes, including bundles)`
    starts the block for procedure construction. The block is based on `notepad`. 

*)

signature NU_TOPLEVEL = sig
  datatype cond_kind = Premise | Requirement
    (* Premise is automatically prefixed by @{term Premise} and added to
     * @{named_theorems useful}; Requirement is not. *)
  val begin_proc_cmd : Attrib.binding 
        -> xstring (*argument*)
        -> xstring (*return*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (indexname list * string) list (*let patterns*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> bool -> Proof.context -> Proof.state
  val begin_rec_proc_cmd : Attrib.binding 
        -> xstring (*argument*)
        -> xstring (*return*)
        -> ((binding * string option * mixfix) list * (*variants*)
            (binding * string option * mixfix) list   (*for fixes*))
        -> (xstring * Position.T) list (*includes*)
        -> (indexname list * string) list (*let patterns*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> bool -> Proof.context -> Proof.state
  val begin_cast_cmd : Attrib.binding
        -> xstring (*domain*)
        -> xstring (*image*)
        -> xstring option (*addtional_prop,   cast domain |--> image with additional_prop*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (indexname list * string) list (*let patterns*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> bool -> Proof.context -> Proof.state
  (* val begin_rec_proc_cmd : Attrib.binding 
        -> xstring (*argument and return*)
        -> (binding * string option * mixfix) list (*loop variables fixes*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> xstring option (*pre-conditions*)
        -> bool -> Proof.context -> Proof.state *)
  val finish_proc_cmd : bool -> Proof.state -> Proof.context
  val begin_block_cmd : Attrib.binding list (*bindings of conditions*)
        -> bool -> Proof.state -> Proof.state
  val end_block_cmd : bool -> Proof.state -> Proof.state
  
  val prove_prem : bool -> Proof.state -> thm list * Proof.state

  val export_LLVM : (string * Position.T) option -> theory -> theory
end

structure NuToplevel : NU_TOPLEVEL = struct
open NuHelp NuBasics Term HOLogic Thm NuSys

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
      if can dest_premise_tag (concl_of th |> @{print}) then th RS @{thm Premise_E} else th)]
(* fun mk_register_collection tm = Const(@{const_name RegisterCollection},
* dummyT) $ tm *)

(** proc command **)

val indTy = Type ("Nat.ind", [])
val stack_R = Free ("\<R>", @{typ "'\<R>::stack set"})
val arg_stat_term_name = "\<ss>"


val default_name = "v"
val auto_name = dest_nuTy #> fst #> Type.strip_constraints #> dest_Free #> fst


val v_proc_var = ("\<p>\<r>\<o>\<c>",0)
val v_lrep_var = "\<l>\<r>\<e>\<p>"
val v_goal_name = "\<nu>goal"
val vv_proc_const_name = "?\<p>\<r>\<o>\<c>"
fun mk_raw_prod (a,b) = Const ("Product_Type.Pair", dummyT) $ a $ b

val top_blk_name = "\<t>\<o>\<p>_\<b>\<l>\<o>\<c>\<k>"

fun print_results int = Proof_Display.print_results int (Position.thread_data ())

(* fun begin_proc ctxt (arg,ret) =
  let
    (* val (arg,ret) = mk_raw_prod (arg,ret) |> Syntax.check_term ctxt |> dest_prod *)
    val (argT,retT) = apply2 (type_of #> dest_Type #> #2 #> hd) (arg,ret)
    val procT = argT --> mk_stateT retT
    val goal = HOLogic.mk_Trueprop (
          Const ("NuPrime.Procedure",
                    (argT --> mk_stateT retT) --> mk_setT argT --> mk_setT retT --> boolT)
          $ Var (v_proc_var, procT) $ arg $ ret)
    val th = arg |> Thm.cterm_of ctxt |> start_proc ctxt top_blk_name
  in
    (goal,th)
  end *)

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt'
  in ((vars, xs), ctxt'') end

datatype cond_kind = Premise | Requirement

fun gen_constr_envir prep_term prep_prop prep_typ prep_var mk_Goal post_process
      binding arg ret rawfixes includes raw_lets raw_defines raw_preconds int ctxt =
  let
    val ((fixes,var_names), ctx_parse) = prep_decls prep_var rawfixes ctxt
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
                  @{attributes [TRY_THEN Premise_E, useful]} @ attrs))
      | prep_precond (Requirement, c) =
          prep_attrterm I c
    val preconds = map prep_precond raw_preconds

    val (goal, constr_process, preconds) =
          mk_Goal (ctx_parse,(fixes,var_names))
                  (parse_term arg, parse_term ret, preconds)

    (* val [arg,ret] = Syntax.check_terms ctx_parse [arg,ret]
    val ctx_parse = ctx_parse |> Variable.declare_term arg |> Variable.declare_term ret *)
    val includes = includes |> map (Bundle.check ctxt)
    (* val (goal,th) = begin_proc ctx_parse (arg,ret)  *)
    val elems = [Element.Fixes fixes,
                 Element.Defines defines,
                 Element.Assumes (map (apsnd single) preconds)]
    val concls = Element.Shows [(Binding.empty_atts,[(goal,[])])]
    fun after_qed [[th]] lthy = post_process binding int lthy th
  in
    ctxt |> Specification.schematic_theorem false "" NONE after_qed Binding.empty_atts
              includes elems concls int
         |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
               Context_Tactic.CONTEXT_TACTIC Tactical.all_tac), Position.no_range))
         |> Seq.the_result "never fail"
         |> Proof.map_context (
             let
               fun fetch names ctxt =
                 map (snd o Proof_Context.get_fact_generic ctxt o Facts.named) names |> flat
               fun bind_lets ctxt =
                 fold Proof_Context.bind_term (map (apsnd (Syntax.check_term ctxt)) lets) ctxt
             in
               bind_lets #>
               Proof_Context.put_thms false ("\<nu>current", SOME []) #>
               Proof_Context.put_thms false ("\<nu>local_values", SOME []) #>
               Proof_Context.put_thms false ("\<nu>lemmata", SOME []) #>
               Proof_Context.add_thms_dynamic (Binding.make ("\<nu>'",pos), (
                 fetch ["\<nu>current", "\<nu>local_values", "\<nu>lemmata", "useful"]
               )) #> snd #>
               Proof_Context.add_thms_dynamic (Binding.make ("\<nu>",pos), (
                 fetch ["\<nu>lemmata", "useful"]
               )) #> snd
             end)
         |> constr_process
  end

fun gen_begin_proc prep_term prep_prop prep_typ prep_var prep_Nu post_process binding =
  let
    fun mk_Goal ctx_fixes arg_ret_conds =
      let
        val (arg, ret, preconds) = prep_Nu ctx_fixes arg_ret_conds
        val ctxt = fst ctx_fixes
        val _ = debug_term ctxt "aaa " arg
        val _ = debug_term ctxt "ret " ret
        val goal = mk_Trueprop
          (Const (@{const_name "Procedure"}, dummyT) $ Var (v_proc_var, dummyT) $ arg $ ret)

        fun constr_process stat =
          let
            val ctxt = Proof.context_of stat
            val goal_proc = Thm.cprem_of (#goal (Proof.goal stat)) 1 |> Drule.strip_imp_concl
            val (_,Arg,_) = dest_procedure_c goal_proc
          in
            stat
              |> Proof.map_context (
                  Proof_Context.put_thms false ("\<nu>thesis",
                    SOME [Drule.mk_term goal_proc]))
              |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)
              |> Proof.map_context_result (start_proc (Binding.name_of (fst binding)) Arg)
              |-> NuBasics.set_nu_fact
          end
      in
        (goal, constr_process, preconds)
      end

    fun post_process' binding int lthy th =
      lthy
        |> NuProcedure.define binding (post_process lthy th)
        |-> (fn th => fn lthy =>
              (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
                  (("\<nu>procedure", ""), [("", [th])]); lthy))
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var mk_Goal post_process' binding
  end
    
val begin_proc =
      gen_begin_proc (K I) (K I) (K I) Proof_Context.cert_var (K I) (K I)
val begin_proc_cmd =
      gen_begin_proc Syntax.parse_term Syntax.parse_prop Syntax.parse_typ Proof_Context.read_var
        (fn (ctxt,_) => fn (arg,ret,conds) =>
          (NuBasics.parse_arg_list false arg,
           NuBasics.parse_arg_list false ret,
           conds)
        ) (K I)

fun gen_begin_rec_proc prep_term prep_prop prep_typ prep_var
        (binding,attr) raw_arg raw_ret (raw_vars, raw_fixes) =
  let open QuantExpansion
    val func_name = Binding.name_of binding
    fun mk_Goal (ctxt,(fixes,fixed_names)) (arg,ret,conds) = 
      let
        val origin_names = map (fn (n,_,_) => (Binding.name_of n)) raw_vars
        val var_names = take (length raw_vars) fixed_names
        val var_tys = take (length raw_vars) fixes
                        |> map (fn (_,ty,_) => the_default dummyT ty)
        val vars = origin_names ~~ (map (rpair dummyT) var_names)

        val arg = NuBasics.parse_arg_list true arg
        val ret = NuBasics.parse_arg_list true ret
        val x = Const (@{const_name tag}, dummyT) $
                  list_mk_binop_r @{const_name Pair} (map Free (var_names ~~ var_tys))

        val conds' = map (snd #> fst #> perhaps (try dest_Trueprop)) conds
        val arg' = arg
              |> fold_rev (fn c => fn Nu =>
                    NuBasics.mk_binop @{const_name Subjection} (Nu,c)) conds'
              |> tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)
        val ret' = ret
              |> tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)

        val goal = mk_Trueprop (
              Const (@{const_name All}, dummyT) $ Abs("x", dummyT,
                (Const (@{const_name Function}, dummyT)
                  $ (Const ("NuInstructions.op_recursion", dummyT)
                      $ @{term UNIQ_ID} $ Const ("Pure.type", dummyT) $ Const ("Pure.type", dummyT)
                      $ Var ((func_name,0), dummyT))
                  $ arg'
                  $ ret')))

        val recursion_thm = Proof_Context.get_thm ctxt "NuStd_Base.op_recursion"
        fun constr_process stat =
          let
            (* simplify the proof goal, to expand all the auto Nu *)
            val ctxt = Proof.context_of stat
            val simctx = Raw_Simplifier.clear_simpset ctxt
                  addsimps @{thms Subjection_simp_proc_arg Subjection_simp_func_arg}

            val stat = stat
              |> Proof.using_facts [] |> Proof.enter_backward (*|> Proof.begin_block*)
              |> Proof.refine (Method.Basic (fn ctxt =>
                  Method.SIMPLE_METHOD (
                    HEADGOAL (resolve_tac ctxt [recursion_thm]) THEN
                    HEADGOAL (Simplifier.simp_tac ctxt)
                  )))
              |> Seq.the_result "should never fail"

            val sequent = #goal (Proof.goal stat) |> @{print}
            val goal = Thm.prems_of sequent |> hd

            val vars = strip_binder_vars @{const_name Pure.all} goal
            val (var_names,stat) = stat
              |> Proof.map_context_result (Proof_Context.add_fixes
                  (map (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) vars))
            val vars = map (Free o apsnd snd) (var_names ~~ vars)

            val goal =
              subst_bounds (rev vars,
                strip_binder_raw_body @{const_name Pure.all} goal)
              |> dest_Trueprop
              |> strip_binop_r @{const_name "HOL.implies"}
              |> map mk_Trueprop |> map (debug_term ctxt "1231 ")
            val (prems, goal) = (front goal, last goal)

            (* intro assumptions *)
            fun imp_export prems sequent =
              sequent
                |> fold_rev (fn prem => fn th =>
                      (Thm.implies_intr prem th RS @{thm impI})
                          |> Thm.assumption NONE 1
                          |> Seq.make_results |> Seq.the_result "should never fail"
                  ) prems
            val assms = map (fn (tm,((b,attr),(_,pats))) =>
                                  ((b, elim_premise @ map (Attrib.attribute ctxt) attr),
                                   [(tm,pats)]))
                  (prems ~~ (((Binding.name func_name,[]),(dummy,[]))::conds)) |> @{print}
            val (_,stat) = stat |> Proof.map_context_result (
                  Proof_Context.add_assms (fn _ => fn prems => (imp_export prems, I)) assms)

            val (_,Arg,_) = dest_procedure goal
            val Arg = Thm.cterm_of ctxt Arg
          in
            stat
              |> Proof.map_context (
                  Proof_Context.put_thms false ("\<nu>thesis",
                    SOME [Drule.mk_term (cterm_of ctxt goal)]))
              |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)
              |> Proof.map_context_result (start_proc func_name Arg)
              |-> NuBasics.set_nu_fact
          end
            (* |> *)
      in
        (goal, constr_process, [])
      end

    fun post_process' binding int lthy th =
      lthy
        |> NuProcedure.define binding (
            th |> normlize_thm_of_names
               |> Simplifier.simplify lthy
               |> repeat QuantExpansion.spec_retaining_name
               |> repeat (fn th => th RS @{thm mp})
            )
        |-> (fn th => fn lthy =>
              (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
                  (("\<nu>procedure", ""), [("", [th])]); lthy))
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var mk_Goal post_process'
        (binding,attr) raw_arg raw_ret (raw_vars @ raw_fixes)
  end

val begin_rec_proc_cmd = gen_begin_rec_proc
      Syntax.parse_term Syntax.parse_prop Syntax.parse_typ Proof_Context.read_var

fun gen_begin_cast_cmd prep_term prep_prop prep_typ prep_var
      binding arg ret additional_prop =
  let
    fun mk_Goal (ctxt,_) (arg, ret, preconds) =
      let
        val arg = mk_repset arg
        val ret = mk_repset ret
        val additional_prop = case additional_prop
                                of SOME x => prep_term ctxt x
                                 | _ => @{term True}
        val goal = mk_Trueprop
          (Const (@{const_name "Cast"}, dummyT) $ arg $ ret $ additional_prop)
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
            NuBasics.set_nu_fact sequent stat
          end
      in
        (goal, constr_process, preconds)
      end
    fun post_process binding int lthy th =
          (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
            (("\<nu>cast", ""), [("", [th])]); lthy)
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var mk_Goal post_process
      binding arg ret
  end

val begin_cast_cmd =
      gen_begin_cast_cmd Syntax.parse_term Syntax.parse_prop Syntax.parse_typ
      Proof_Context.read_var




fun RSNXX ctxt tha (i, thb) =
  (case Seq.pull (biresolution (SOME (Config.put Pattern.unify_trace_failure true ctxt)) false [(false, tha)] i thb) of
    SOME (th, _) => solve_constraints th
  | _ => raise THM ("RSNXX: no unifiers", i, [tha, thb]));
fun RSXX ctxt tha thb = RSNXX ctxt tha (1,thb);

local
fun basic_method r = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (r ctxt)))
fun gen_finish_proc qed int stat =
  let
    val sequent = NuBasics.the_nu_fact stat
    val ctxt = Proof.context_of stat
    val goal = Proof_Context.get_thm ctxt "\<nu>thesis" |> Drule.dest_term
    val (_,_,desired_nu) = dest_procedure_c goal |> @{print}
    (* quick fix:
    val xa = term_of desired_nu |> auto_fusion_arity
     val sequent = funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema} #> accept_proc ctxt) sequent
      handle THM _ => funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema'}
      #> accept_proc ctxt) sequent *)
    val sequent = sequent
          |> Local_Defs.unfold ctxt @{thms Implicit_Protector_def}
          (* |> Raw_Simplifier.rewrite_rule ctxt @{thms RegisterCollection_rew}
          * *)
    val sequent = NuSys.cast_completely ctxt desired_nu sequent RS @{thm reassemble_proc_0}
    val end_tac = basic_method (fn ctxt' => fn prooof_stat => 
      Runtime.exn_trace (fn () =>
      RSXX ctxt' (
        singleton (Proof_Context.export ctxt ctxt') sequent
          (* |> conversion_completely ctxt' goal *)
      ) prooof_stat)
      handle e => (Runtime.exn_system_message e; Exn.reraise (@{print} e)))
  in
    stat |> Proof.set_facts [] 
      |> qed (SOME (end_tac, Position.no_range), false)
  end
in
val end_block_cmd = gen_finish_proc Proof.local_qed

(* fun gen_finish_proc' prep_specthm qed int stat =
  let val sequent = Proof.the_fact stat
  in if current_block_depth sequent > 1 then 
      gen_finish_proc' prep_specthm qed int (end_block_cmd false stat)
    else gen_finish_proc prep_specthm qed int stat end *)
val finish_proc_cmd = gen_finish_proc Proof.global_qed
end


fun prove_prem int stat =
  let open Proof
    val specthm = the_nu_fact stat
    val goal = Thm.prop_of specthm
                |> Logic.dest_implies |> #1 (* |> dest_premise_tag |> mk_Trueprop *)
    fun after_qed (ctxt',[[th]]) stat =
      let
        val [th] = Proof_Context.export ctxt' (context_of stat) [th]
        (* val th = th RS @{thm NuPrime.Premise_I} *)
      in
        stat |> Proof.map_context_result
                  (Config.put Nu_Reasoner.auto_level 0
                    #> NuProcessor.process_no_input (th RS specthm))
             |-> NuBasics.set_nu_fact
      end
  in
    stat |> setup_proof (print_results int) Proof_Context.mode_schematic false ""
              NONE after_qed [] [] [[(goal,[])]]
         |> apsnd (
              Proof.refine (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (
                HEADGOAL (resolve_tac ctxt @{thms Premise_I})
              ))) #> Seq.the_result "should never fail"
            )
  end

local
fun block_name_of (Var ((x,_),_)) = x
  | block_name_of _ = "block"
val attr_useful = map (Attrib.attribute @{context}) @{attributes [useful]}
in

fun gen_begin_block prep_attr bindings int stat =
  let open Proof
    val specthm = the_nu_fact stat
    val stat = stat |> begin_block
    val ctxt = context_of stat
    val (vars, goal) = prop_of specthm
                          |> Logic.dest_implies |> #1
                          |> dest_Trueprop |> strip_binder_raw @{const_name All}
    val (var_names, stat) = stat
          |> Proof.map_context_result (Proof_Context.add_fixes
              (map (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) vars))
    val vars = map (Free o apsnd snd) (var_names ~~ vars)
    val goal = subst_bounds (rev vars, goal)
    val prems_goal = strip_binop_r @{const_name implies} goal
    val (prems, goal) = (front prems_goal, last prems_goal)
    val (proc,arg,ret) = dest_procedure goal
    val blk_name = block_name_of proc
    val level = current_block_depth specthm
    val blk_name = "L\<nu>'" ^ (Int.toString level) ^ "_" ^ blk_name
    val (prems, goal) = (map mk_Trueprop prems, mk_Trueprop goal)
    val _ = debug_term ctxt "aaaa " goal
    fun after_qed (ctxt',[[th]]) stat =
      end_block stat |> (fn stat =>
        stat |> NuBasics.set_nu_fact (
                  let val ctxt'' = context_of stat
                    val vars' = Variable.export_terms ctxt' ctxt'' vars
                  in ((singleton (Proof_Context.export ctxt' ctxt'') th
                        |> Drule.forall_intr_list (map (cterm_of ctxt'') vars')
                        |> Raw_Simplifier.rewrite_rule ctxt'' @{thms atomize_imp atomize_all}
                      ) COMP specthm)
                  end
          ))
    val delta = length prems - length bindings |> @{print}
    val _ = if delta < 0 then error "too much premise bindings" else  ()
    val bindings =
      ((map (apsnd (map (prep_attr ctxt))) bindings)
          @ (List.tabulate (delta, K (Binding.empty, attr_useful))))
        |> map (apsnd (fn x => elim_premise @ x))
  in
    stat
      |> internal_goal (print_results int) Proof_Context.mode_schematic false 
          "" NONE after_qed []
          (bindings ~~ (map (single o rpair []) prems))
          [(Binding.empty_atts, [(goal,[])])] |> #2
      |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
            Context_Tactic.CONTEXT_TACTIC Tactical.all_tac), Position.no_range))
      |> Seq.the_result "never fail"
      |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)
      |> Proof.map_context_result (start_proc blk_name (cterm_of ctxt arg))
      |-> NuBasics.set_nu_fact
      |> Proof.map_context (fn ctxt => 
            Proof_Context.put_thms false ("\<nu>thesis",
              SOME [Drule.mk_term (cterm_of ctxt goal)]) ctxt
          )
      (* |> NuObtain.obtain_quick_pairs_perhaps_try *)
  end
val begin_block_cmd = gen_begin_block Attrib.attribute_cmd
val begin_block = gen_begin_block (K I)
end

fun export_LLVM path thy =
  let
    fun eval code = ML_Context.exec (fn () =>
                      ML_Context.eval_source ML_Compiler.flags (Input.string code))

    fun prep_path (path,pos) =
      let
        val base = Path.expand (Resources.master_directory thy)
        val path = File.full_path base (Path.explode path)
        val _ = Position.report pos (Markup.path (Path.implode path));
      in path end

    val codegen =
      case path of SOME P =>
          eval ("NuCG.codegen NuCG_" ^ Context.theory_name thy ^ ".gen"
                    ^ "(" ^ ML_Syntax.print_path (prep_path P) ^ ")" )
        | _ => I
  in 
    thy |> Context.theory_map (eval (NuCompilation.compile thy |> (fn s => (tracing s; s))))
        |> Context.theory_map codegen
  end

end
