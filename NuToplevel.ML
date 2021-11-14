(*  Title:      NuToplevel.ML
    Author:     Qiyuan Xu

The toplevel structure of the ν-system.

`begin_proc (argument-statement, for-fixes, including bundles)`
    starts the block for procedure construction. The block is based on `notepad`. 

*)

signature NU_TOPLEVEL = sig
  val begin_proc_cmd : bool (*raw*) -> Attrib.binding 
        -> xstring (*argument*)
        -> xstring (*return*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (Attrib.binding * (string * string list)) list (*pre-conditions*)
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
  val have_aux : ((Thm.binding * attribute list) * (term * term list) list) list
        -> bool -> Proof.state -> thm list * Proof.state
  val have_aux_cmd : ((Attrib.binding * Token.src list) * (string * string list) list) list
        -> bool -> Proof.state -> thm list * Proof.state
  val name_star_fact_cmd : Attrib.binding -> Proof.state -> Proof.state
  val drop_fact_cmd : Binding.binding -> Proof.state -> Proof.state
end

structure NuToplevel : NU_TOPLEVEL = struct
open NuHelp NuBasics Term HOLogic Thm NuSys
type context = Proof.context
type state = Proof.state
val register_label_head = "\<upsilon>"
val delimiter_name = "NuPrime.Stack_Delimiter"
val eof_ctx_stack_name = "NuPrime.End_of_Contextual_Stack"
fun mk_eof_ctx_stack tm = Const(eof_ctx_stack_name, dummyT) $ tm
val mk_register_collection = I
(* fun mk_register_collection tm = Const(@{const_name RegisterCollection},
* dummyT) $ tm *)

(** proc command **)

val indTy = Type ("Nat.ind", [])
val stack_R = Free ("\<R>", @{typ "'\<R>::stack set"})
val arg_stat_term_name = "\<ss>"


val default_name = "v"
val auto_name = dest_nuTy #> fst #> Type.strip_constraints #> dest_Free #> fst


val v_proc_var = ("\<p>\<r>\<o>\<c>",0)
val v_goal_name = "\<nu>goalaa"
val vv_proc_const_name = "?\<p>\<r>\<o>\<c>"
fun mk_raw_prod (a,b) = Const ("Product_Type.Pair", dummyT) $ a $ b

val top_blk_name = "\<t>\<o>\<p>_\<b>\<l>\<o>\<c>\<k>"

fun print_results int = Proof_Display.print_results int (Position.thread_data ())

(* fun begin_proc ctx (arg,ret) =
  let
    (* val (arg,ret) = mk_raw_prod (arg,ret) |> Syntax.check_term ctx |> dest_prod *)
    val (argT,retT) = apply2 (type_of #> dest_Type #> #2 #> hd) (arg,ret)
    val procT = argT --> mk_stateT retT
    val goal = HOLogic.mk_Trueprop (
          Const ("NuPrime.Procedure",
                    (argT --> mk_stateT retT) --> mk_setT argT --> mk_setT retT --> boolT)
          $ Var (v_proc_var, procT) $ arg $ ret)
    val th = arg |> Thm.cterm_of ctx |> start_proc ctx top_blk_name
  in
    (goal,th)
  end *)

fun init_registers ctx meta = meta
  (* apply_proc_naive (
      funpow (length (stack_of_meta meta) - 1) (fn th => th RS @{thm index_right_mapper})
        @{thm index_here_mapper}
      RS @{thm op_init_register})
      (Raw_Simplifier.rewrite_rule ctx @{thms StackDelimiter_to_AndTy} meta |> @{print})
    |> NuSys.accept_proc ctx *)
val empty_facts_thm = @{thm NuPrime.empty_facts}

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt'
  in ((vars, xs), ctxt'') end

fun gen_begin_proc prep_prop prep_term prep_typ prep_var
      raw binding arg ret rawfixes includes preconds int ctx =
  let
    val ((fixes,var_names), ctx_parse) = prep_decls prep_var rawfixes ctx
    val binding = binding |> apsnd (map (Attrib.check_src ctx))
    val parse_term = prep_term ctx_parse
    val parse_prop = prep_prop ctx_parse
    val parse_typ = prep_typ ctx_parse
    val preconds = preconds |> map (
      apfst (apsnd (map (Attrib.check_src ctx))) #>
      apsnd (apfst parse_prop #> apsnd (map parse_term) #> single))
    val arg = prep_term ctx_parse arg |> NuBasics.parse_arg_list |> mk_repset
    val ret = prep_term ctx_parse ret |> NuBasics.parse_arg_list |> mk_repset
    (* val [arg,ret] = Syntax.check_terms ctx_parse [arg,ret]
    val ctx_parse = ctx_parse |> Variable.declare_term arg |> Variable.declare_term ret *)
    val includes = includes |> map (Bundle.check ctx)
    (* val (goal,th) = begin_proc ctx_parse (arg,ret)  *)
    val goal = mk_Trueprop
      (Const (@{const_name "Procedure"}, dummyT) $ Var (v_proc_var, dummyT) $ arg $ ret)
    val elems = [Element.Fixes fixes, Element.Assumes preconds]
    val concls = Element.Shows [(Binding.empty_atts,[(goal,[])])]
    fun after_qed [[th]] lthy =
      lthy
        |> NuProcedure.define binding th 
        |-> (fn th => fn lthy =>
              (Proof_Display.print_results int Position.none ctx
                  (("\<nu>procedure", ""), [("", [th])]); lthy))
  in
    ctx |> Specification.schematic_theorem false "" NONE after_qed Binding.empty_atts
              includes elems concls int
      |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
            Context_Tactic.CONTEXT_TACTIC Tactical.all_tac), Position.no_range))
      |> Seq.the_result "impossible"
      |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)
      |> (fn stat =>
          let val ctx = Proof.context_of stat
          val th = arg |> Syntax.check_term ctx
            |> Thm.cterm_of ctx |> start_proc ctx top_blk_name
            |> rpair empty_facts_thm |> intro_SPEC
            |> (if raw then I else init_registers ctx)
            |> Simplifier.simplify ctx
          in Proof.set_facts [th] stat end)
      |> Proof.map_context (fn ctx => 
          ctx |> Proof_Context.put_thms false ("\<nu>thesis",
            SOME [Drule.mk_term (cterm_of ctx (Syntax.check_term
              (Proof_Context.set_mode Proof_Context.mode_schematic ctx) goal))]))
  end

val begin_proc_cmd = gen_begin_proc Syntax.parse_prop Syntax.parse_term
                        Syntax.parse_typ Proof_Context.read_var
val begin_proc = gen_begin_proc (K I) (K I) (K I) Proof_Context.cert_var



fun RSNXX tha (i, thb) =
  (case Seq.pull (biresolution NONE false [(false, tha)] i thb) of
    SOME (th, _) => solve_constraints th
  | _ => raise THM ("RSN: no unifiers", i, [tha, thb]));
fun RSXX tha  thb = RSNXX tha (1,thb);

local
fun basic_method r = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (r ctxt)))
fun gen_finish_proc prep_specthm qed int stat =
  let
    val meta = Proof.the_fact stat
    val ctx = Proof.context_of stat
    val goal = Proof_Context.get_thm ctx "\<nu>thesis" |> Drule.dest_term
    val (_,_,desired_nu) = dest_procedure_c goal
    (* quick fix:
    val xa = term_of desired_nu |> auto_fusion_arity
     val meta = funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema} #> accept_proc ctx) meta
      handle THM _ => funpow (xa - 1) (apply_proc_naive @{thm pr_auto_schema'}
      #> accept_proc ctx) meta *)
    val meta = meta |> prep_specthm ctx
          (* |> Raw_Simplifier.rewrite_rule ctx @{thms RegisterCollection_rew}
          * *)
    val meta = meta |> elim_SPEC
          |> apfst (NuSys.cast (NuSys.load_specthm meta ctx) desired_nu)
          |> intro_SPEC
    val end_tac = basic_method (fn ctx' => fn t => 
      RSXX (
        finish_proc (singleton (Proof_Context.export ctx ctx') (elim_SPEC meta |> fst))
          |> conversion ctx' goal
      ) t
      handle e => raise @{print} e)
  in
    stat |> Proof.set_facts [] 
      |> qed (SOME (end_tac, Position.no_range), false)
  end
in
val end_block_cmd = gen_finish_proc (K I) (*NuRegisters.delete_locale*) Proof.local_qed

fun gen_finish_proc' prep_specthm qed int stat =
  let val meta = Proof.the_fact stat
  in if current_block_depth meta > 1 then 
      gen_finish_proc' prep_specthm qed int (end_block_cmd false stat)
    else gen_finish_proc prep_specthm qed int stat end
val finish_proc_cmd = gen_finish_proc' (K I) (*NuRegisters.delete_locale*) Proof.global_qed
end


fun prove_prem int stat =
  let open Proof
    val specthm = the_fact stat
    val (focus,aux) = elim_SPEC specthm
    val goal = Thm.prop_of specthm |> dest_SpecTop |> #1
          |> Logic.dest_implies |> #1 |> dest_premise_tag |> mk_Trueprop
    fun after_qed (ctx',[[th]]) stat =
      let
        val [th] = Proof_Context.export ctx' (context_of stat) [th]
        val th = th RS @{thm NuPrime.Premise_I}
      in
        set_facts [(NuProcessor.process_no_input
          (Proof.context_of stat |> AutoLevel.put 0)
            (intro_SPEC (th RS focus, aux)))] stat
      end
  in
    stat |> setup_proof (print_results int) Proof_Context.mode_schematic false ""
      NONE after_qed [] [] [[(goal,[])]]
  end

local
fun gen_have_aux prep_attr prep_prop goals int stat =
  let open Proof
    val ctx = context_of stat
    fun prep1 ((a,b),c) = ((a, map (prep_attr ctx) b), map (prep_attr ctx) c)
    val ctx' = Proof_Context.set_mode Proof_Context.mode_schematic ctx
    fun prep2 (a,b) = (prep_prop ctx a, map (prep_prop ctx') b)
    val goals = map (fn (a,b) => (prep1 a, map prep2 b)) goals
    val specthm = the_fact stat
    val binds = map (fst #> fst) goals
    val attrs = map (fst #> snd) goals
    fun apply_attr ctx attr = map (fn th => (proof_attributes attr th ctx |> #1))
    fun after_qed (ctx',thes) stat =
      let
        val ctx = context_of stat
        val thes = thes |> map (Proof_Context.export ctx' (context_of stat))
                        |> map2 (apply_attr ctx') attrs
      in
        stat |> map_context_result (declare_facts (binds ~~ thes) specthm)
          |-> set_facts o single
      end
  in
    stat |> setup_proof (print_results int) Proof_Context.mode_default false "\<nu>lemma"
      NONE after_qed [] [] (map snd goals)
  end
in
val have_aux = gen_have_aux (K I) Syntax.check_prop
val have_aux_cmd = gen_have_aux Attrib.attribute_cmd Syntax.read_prop
end

fun process (meta,stat) =
  (NuProcessor.process_no_input (Proof.context_of stat) meta, stat)
fun name_star_fact_cmd binding stat =
  let
    val ctx = Proof.context_of stat
    val meta = Proof.the_fact stat
  in
    stat 
      |> Proof.map_context_result
            (NuSys.name_star_fact (apsnd (map (Attrib.attribute_cmd ctx)) binding) meta)
      |> process
      |-> Proof.set_facts o single
  end
fun drop_fact_cmd binding stat =
  let
    val ctx = Proof.context_of stat
    val meta = Proof.the_fact stat
  in
    stat 
      |> Proof.map_context_result
            (NuSys.delete_fact (Binding.name_of binding) meta)
      |-> Proof.set_facts o single
  end

local
fun block_name_of (Var ((x,_),_)) = x
  | block_name_of _ = "block"
val Premise_I = @{thm NuPrime.Premise_I}
val premise_export = K (K ((fn th => th COMP Premise_I), I))
val elim_premise = [Thm.rule_attribute [] (fn _ => fn th =>
      if can dest_premise_tag (prop_of th) then th COMP @{thm Premise_E} else th)]
val attr_used = map (Attrib.attribute @{context}) @{attributes [used]}
val elim_premise_tag = perhaps (mk_Trueprop o dest_premise_tag)
in
fun gen_begin_block prep_attr bindings int stat =
  let open Proof
    val specthm = the_fact stat
    val stat = stat |> begin_block
                |> map_context (open_meta specthm)
    val ctx = context_of stat
    val (vars, goal) = specthm |> prop_of |> dest_SpecTop |> #1
          |> Logic.dest_implies |> #1
          |> dest_Trueprop |> strip_binder @{const_name All}
    val (inst, stat) = stat
          |> Proof.map_context_result (fix_frees Position.none vars)
    val (vars, goal) = (map inst vars, inst goal)
    val prems_goal = strip_binop_r @{const_name implies} goal
    val (prems, goal) = (front prems_goal, last prems_goal)
    val (proc,arg,ret) = dest_procedure goal
    val blk_name = block_name_of proc
    val level = current_block_depth specthm
    val level_prefix = "L\<nu>'"^(Int.toString level)^"_"^blk_name
    val (prems, goal) = (map mk_Trueprop prems, mk_Trueprop goal)
    fun after_qed (ctx',[[th]]) stat =
      end_block stat |> (fn stat => stat
          |> set_facts[
            specthm
              |> elim_SPEC
              |> apfst (fn focus =>
                let val ctx'' = context_of stat
                  val vars' = Variable.export_terms ctx' ctx'' vars
                in ((singleton (Proof_Context.export ctx' ctx'') th
                      |> Drule.forall_intr_list (map (cterm_of ctx'') vars')
                      |> Raw_Simplifier.rewrite_rule ctx'' @{thms atomize_imp atomize_all}
                    ) COMP focus)
                end)
              |> intro_SPEC
          ])
    val delta = length prems - length bindings
    val _ = if delta < 0 then error "too much premise bindings" else  ()
    val bindings =
      ((map (apsnd (map (prep_attr ctx))) bindings)
          @ (List.tabulate (delta, K (Binding.empty, attr_used))))
        |> map (apsnd (fn x => elim_premise @ x))
  in
    stat
      |> internal_goal (print_results int) Proof_Context.mode_schematic false 
          "\<nu>block" NONE after_qed []
          (bindings ~~ (map (single o rpair []) prems))
          [(Binding.empty_atts, [(goal,[])])] |> #2
      |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
            Context_Tactic.CONTEXT_TACTIC Tactical.all_tac), Position.no_range))
      |> Seq.the_result "unreachable"
      |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)
      |> (fn stat => let val ctx = Proof.context_of stat
            val next_specthm = start_proc ctx level_prefix (cterm_of ctx arg)
              |> rpair (elim_SPEC specthm |> #2) |> intro_SPEC
              (* |> NuRegisters.new_locale ctx *)
          in Proof.set_facts [next_specthm] stat end)
      |> Proof.map_context (fn ctx => 
            Proof_Context.put_thms false ("\<nu>thesis",
              SOME [Drule.mk_term (cterm_of ctx goal)]) ctx
          )
      (* |> NuObtain.obtain_quick_pairs_perhaps *)
  end
val begin_block_cmd = gen_begin_block Attrib.attribute_cmd
val begin_block = gen_begin_block (K I)
end


(* fun gen_begin_rec_proc prep_term prep_var
  binding arg_ret raw_loop_vars rawfixes includes precond int ctx =
  let
    (* val pr_proc = @{thm pr_auto_schema'}
    val dpr_proc = @{thm dpr_auto_schema'} *)
    val i_rec_proc = Proof_Context.get_thm ctx "NuInstructions.i_recursion_\<nu>proc"

    val ((fixes,_), ctx_parse) = prep_decls prep_var rawfixes ctx
    val ((loop_vars, loop_vars_names'), ctx_parse) =
          prep_decls prep_var raw_loop_vars ctx_parse
    val precond = Option.map (prep_term ctx_parse) precond

    val arg_ret = prep_term ctx_parse arg_ret
    val (arg, ret) = NuHelp.dest_binop @{const_name Arg_Ret_Pair_sugar} arg_ret
    val (_,args) = arg
      |> strip_binop_l "NuPrime.Stack_Delimiter" |> map pass_name |> split_list
    val rets = ret |> strip_binop_l "NuPrime.Stack_Delimiter"
    val arg_arity = length args
    val arg = parse_arg false arg
    val ret = parse_ret ret
    val ret_nu = map (perhaps dest_RepSet #> dest_nuTy #> #2) rets
          |> list_mk_binop_r @{const_name AutoFusion}


    val precond' = case precond of SOME x =>
          [((Binding.name "precondition",[]),(mk_Trueprop x,[]))] | _ => []
    val stat = begin_proc true binding arg_ret (loop_vars @ fixes)
                  includes precond' int ctx
    val ctx = Proof.context_of stat

    val vars = (map (fn (x,_,_) => Binding.name_of x) loop_vars) ~~ loop_vars_names'
    val schema = map (perhaps dest_RepSet #> dest_nuTy #> #1) args |> rev
          |> list_mk_binop_r "Product_Type.Pair"
          |> tuple_abs vars
    val cond = case precond of SOME c =>
            tuple_abs vars c |> mk_monop @{const_name Set.Collect}
                | NONE => Const (@{const_name Orderings.top_class.top}, dummyT) (* it's term UNIV *)
    val rec_func = map (perhaps dest_RepSet #> dest_nuTy #> #1) rets |> rev
          |> list_mk_binop_r "Product_Type.Pair"
          |> tuple_abs vars
    val meta = Proof.the_fact stat
          (* |> funpow (arg_arity-1)
              (NuBasics.apply_proc_naive pr_proc #> NuSys.accept_proc ctx) *)
          |> NuBasics.apply_proc_naive i_rec_proc
          |> NuSys.set_param ctx ret_nu
          |> NuSys.set_param ctx schema
          |> NuSys.set_param ctx cond
          |> NuSys.set_param ctx rec_func
          |> NuSys.auto_resolve_rule NONE [] ctx
          |> (fn meta =>
              case precond of SOME _ =>
                elim_SPEC meta |> apfst (fn major =>
                    (Proof_Context.get_thm ctx "precondition" RS @{thm StructuralTag_I}) RS major)
                  |> intro_SPEC
              | NONE => meta)
  in
    stat |> Proof.set_facts[meta]
      |> begin_block [(#1 binding |> Binding.suffix_name "_\<nu>proc", [])] false 
  end

val begin_rec_proc_cmd = gen_begin_rec_proc Syntax.parse_term
Proof_Context.read_var *)
end
