(*  Title:      NuToplevel.ML
    Author:     Qiyuan Xu

The toplevel structure of the ν-system.

`begin_proc (argument-statement, for-fixes, including bundles)`
    starts the block for procedure construction. The block is based on `notepad`. 

*)

signature NU_TOPLEVEL = sig
  val begin_proc_cmd : Attrib.binding 
        -> xstring (*argument*)
        -> xstring (*return value*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (Attrib.binding * (string * string list) list) list (*pre-conditions*)
        -> bool -> Proof.context -> Proof.state
  val finish_proc_cmd : bool -> Proof.state -> Proof.context
  val begin_block_cmd : Attrib.binding list (*bindings of conditions*)
        -> bool -> Proof.state -> Proof.state
  val end_block_cmd : bool -> Proof.state -> Proof.state
  
  val setup_proof : (Proof.context -> (string * string) * (string * thm list) list -> unit)
        -> Proof_Context.mode -> bool -> string -> Method.text option
        -> (Proof.context * thm list list -> Proof.state -> Proof.state)
        -> (binding * typ option * mixfix) list (*fixes*)
        -> (Thm.binding * (term * term list) list) list (*premis*)
        -> (term * term list) list list (*no binding is allowed*)
        -> Proof.state -> thm list * Proof.state
  val prove_prem : bool -> Proof.state -> thm list * Proof.state
  val have_aux : ((Thm.binding * attribute list) * (term * term list) list) list
        -> bool -> Proof.state -> thm list * Proof.state
  val have_aux_cmd : ((Attrib.binding * Token.src list) * (string * string list) list) list
        -> bool -> Proof.state -> thm list * Proof.state
  val name_star_fact_cmd : Attrib.binding -> Proof.state -> Proof.state
  val drop_fact_cmd : Binding.binding -> Proof.state -> Proof.state

  val process_cmd : Token.T list -> Proof.state -> Proof.state
end

structure NuToplevel : NU_TOPLEVEL = struct
open NuHelp NuBasics Term HOLogic Thm NuSys
type context = Proof.context
type state = Proof.state
val register_label_head = "\<upsilon>"
val delimiter_name = "NuPrim.Stack_Delimiter"
val eof_ctx_stack_name = "NuPrim.End_of_Contextual_Stack"
fun mk_eof_ctx_stack tm = Const(eof_ctx_stack_name, dummyT) $ tm

(** proc command **)

val indTy = Type ("Nat.ind", [])
val stack_R = Free ("\<R>", Type ("Set.set", [TFree ("'\<R>", ["NuPrim.stack"])]))
val arg_stat_term_name = "\<ss>"


val default_name = "v"
val auto_name = dest_nuTy #> fst #> Type.strip_constraints #> dest_Free #> fst
fun pass_name tm = 
      case dest_named tm of
         (SOME name, tm) => (name, tm)
       | (NONE, tm) => (tm |> try auto_name |> the_default default_name, tm)

(* "(a1 ⦂ N1 named n1, ⋯ ,ak ⦂ Nk named nk)" -->
    ("(a1 ⦂ N1) × ⋯ × (ak ⦂ Nk) × ℛ ", [n1,...,nk]) with automatical naming for the anonymous *)
fun parse_arg arg =
  let
    val (names,args) = arg
      |> strip_binop_l "NuPrim.Stack_Delimiter" |> map pass_name |> split_list
    val names = names |> Name.variant_list []
    val arg = list_mk_binop_l0 delimiter_name (mk_eof_ctx_stack stack_R)
                (map mk_repset args)
  in
    (arg, names)
  end
fun parse_ret ret =
  ret |> strip_binop_l "NuPrim.Stack_Delimiter" |> map mk_repset
    |> list_mk_binop_l0 delimiter_name (mk_eof_ctx_stack stack_R)

val v_proc_var = ("\<p>\<r>\<o>\<c>",0)
val v_goal_name = "\<nu>goalaa"
val vv_proc_const_name = "?\<p>\<r>\<o>\<c>"
val final_proc_rewrite_rules = @{thms final_proc_rewrite}
fun mk_raw_prod (a,b) = Const ("Product_Type.Pair", dummyT) $ a $ b

val top_blk_name = "\<t>\<o>\<p>_\<p>\<r>\<o>\<c>"
fun begin_proc ctx (arg,ret) =
  let
    val (arg,ret) = mk_raw_prod (arg,ret) |> Syntax.check_term ctx |> dest_prod
    val (argT,retT) = apply2 (type_of #> dest_Type #> #2 #> hd) (arg,ret)
    val procT = argT --> mk_stateT retT
    val goal = HOLogic.mk_Trueprop (
          Const ("NuPrim.Procedure",
                    (argT --> mk_stateT retT) --> mk_setT argT --> mk_setT retT --> boolT)
          $ Var (v_proc_var, procT) $ arg $ ret)
    val th = arg |> Thm.cterm_of ctx |> start_proc ctx top_blk_name
  in
    (goal,th)
  end

fun mk_regctx ctx meta =
  if can (dest_current_nu #> dest_Proc_CtxTy) meta then meta
  else apply_proc_naive @{thm NuPrim.begin_proc_ctx} meta |> accept_proc ctx
val empty_facts_thm = @{thm NuPrim.empty_facts}

fun prep_decls raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map Proof_Context.read_var raw_vars ctxt
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt'
  in ((vars, xs), ctxt'') end

fun begin_proc_cmd binding arg ret rawfixes includes preconds int ctx =
  let
    val ((fixes,_), ctx_parse) = prep_decls rawfixes ctx
    val binding = binding |> apsnd (map (Attrib.check_src ctx))
    val preconds = preconds |> map (apfst (apsnd (map (Attrib.check_src ctx))))
    val (arg, reg_names) = arg |> Syntax.parse_term ctx_parse |> parse_arg
    val ret = ret |> Syntax.parse_term ctx_parse |> parse_ret

    val includes = includes |> map (Bundle.check ctx)
    val parse_term = Syntax.read_term ctx_parse
    val parse_prop = Syntax.read_prop ctx_parse
    val parse_typ = Syntax.read_typ ctx_parse
    val (goal,th) = begin_proc ctx_parse (arg,ret) 
    val elems = [Element.Fixes fixes,
                 Element.Assumes (preconds
                    |> map (apsnd (map (apfst parse_prop #> apsnd (map parse_term)))))]
    val concls = Element.Shows [(Binding.empty_atts,[(goal,[])])]
    fun after_qed [[th]] lthy =
      lthy
        |> NuProcedure.define binding
              (Raw_Simplifier.rewrite_rule lthy final_proc_rewrite_rules th)
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
          val th = th |> rpair empty_facts_thm |> intro_SPEC
            |> mk_regctx ctx
            |> fold (fn name =>
                NuRegisters.assign_reg ctx name #> accept_proc ctx) reg_names
            |> Simplifier.simplify ctx
          in Proof.set_facts [th] stat end)
      |> Proof.map_context
          (Proof_Context.put_thms false ("\<nu>thesis", SOME [Drule.mk_term (cterm_of ctx goal)]))
  end


fun RSNXX tha (i, thb) =
  (case Seq.pull (biresolution NONE false [(false, tha)] i thb) of
    SOME (th, _) => solve_constraints th
  | _ => raise THM ("RSN: no unifiers", i, [tha, thb]));
fun RSXX tha  thb = RSNXX tha (1,thb);

local
fun basic_method r = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (r ctxt)))
val end_proc_ctx_thm = @{thm NuPrim.end_proc_ctx}
fun gen_finish_proc prep_specthm qed int stat =
  let
    val meta = Proof.the_fact stat
    val ctx = Proof.context_of stat
    val goal = Proof_Context.get_thm ctx "\<nu>thesis" |> Drule.dest_term
    val (_,_,desired_nu) = dest_procedure_c goal
    val meta = meta |> prep_specthm ctx
    val meta = if not (can dest_Proc_CtxTy (term_of desired_nu))
                  andalso can dest_Proc_CtxTy (dest_current_nu meta)
               then apply_proc_naive end_proc_ctx_thm meta |> accept_proc ctx
               else meta
    val meta = meta |> elim_SPEC
          |> apfst (NuSys.cast (NuSys.load_specthm meta ctx) desired_nu)
          |> intro_SPEC
    val end_tac = basic_method (fn ctx' => fn t => 
      RSXX (finish_proc ctx' goal
        (singleton (Proof_Context.export ctx ctx') (elim_SPEC meta |> fst))) t
        handle e => raise @{print} e)
  in
    stat |> Proof.set_facts [] 
      |> qed (SOME (end_tac, Position.no_range), false)
  end
in
val finish_proc_cmd = gen_finish_proc (K I) Proof.global_qed
val end_block_cmd = gen_finish_proc NuRegisters.delete_locale Proof.local_qed
end

fun process_cmd toks stat =
  stat |> Proof.set_facts
    [(NuSys.process stat (Proof.the_fact stat) --| Scan.catch Parse.eof ) toks |> fst]

fun print_results int = Proof_Display.print_results int (Position.thread_data ())
fun setup_proof print_results mode strict_asm kind before_qed after_qed' fixes assumes gl stat =
  let open Proof
    val specthm = the_fact stat
    fun after_qed ctxthms stat =
      stat |> end_block 
           |> after_qed' ctxthms
  in
    stat |> begin_block
      |> map_context (load_specthm specthm)
      |> internal_goal print_results mode strict_asm kind before_qed after_qed fixes assumes
            (map (pair Binding.empty_atts) gl)
      |> apsnd (fn stat => using_facts (Named_Theorems.get (context_of stat) "NuSys.used") stat)
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
        val th = th RS @{thm NuPrim.Premise_I}
      in
        set_facts [(NuProcessor.process_no_input
          (Proof.context_of stat |> AutoLevel.put 0)
            (intro_SPEC (th RS focus, aux)))] stat
      end
  in
    stat |> setup_proof (print_results int) Proof_Context.mode_default false ""
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
val Premise_I = @{thm NuPrim.Premise_I}
val premise_export = K (K ((fn th => th COMP Premise_I), I))
val elim_premise = [Thm.rule_attribute [] (fn _ => fn th =>
      if can dest_premise_tag (prop_of th) then th COMP @{thm Premise_E} else th)]
val attr_used = map (Attrib.attribute @{context}) @{attributes [used]}
val elim_premise_tag = perhaps (mk_Trueprop o dest_premise_tag)
in
fun begin_block_cmd bindings int stat =
  let open Proof
    val specthm = the_fact stat
    val stat = stat |> begin_block
                |> map_context (open_meta specthm)
    val ctx = context_of stat
    val (vars, goal) = specthm |> prop_of |> dest_SpecTop |> #1
          |> Logic.dest_implies |> #1 |> strip_binder "Pure.all"
    val (inst, stat) = stat
          |> Proof.map_context_result (fix_frees Position.none vars)
    val goal = inst goal
    val (prems, goal) = (Logic.strip_imp_prems goal, Logic.strip_imp_concl goal)
    val (proc,arg,ret) = dest_procedure goal 
    val blk_name = block_name_of proc
    val level = current_block_depth specthm
    val level_prefix = "L\<nu>'"^(Int.toString level)^"_"^blk_name
    fun after_qed (ctx',[[th]]) stat =
      stat |> end_block |> (fn stat => stat
          |> set_facts[
            specthm
              |> elim_SPEC
              |> apfst (fn focus =>
                let val ctx'' = context_of stat
                  val vars' = map inst vars |> Variable.export_terms ctx' ctx''
                in ((singleton (Proof_Context.export ctx' ctx'') th
                      |> Drule.forall_intr_list (map (cterm_of ctx'') vars')
                    ) COMP focus)
                end)
              |> intro_SPEC
              |> NuProcessor.process_no_input (Proof.context_of stat)
          ])
    val delta = length prems - length bindings
    val _ = if delta < 0 then error "too much premise bindings" else  ()
    val bindings =
      ((map (apsnd (map (Attrib.attribute_cmd ctx))) bindings)
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
              |> rpair (elim_SPEC specthm |> #2)
              |> intro_SPEC |> mk_regctx ctx |> NuRegisters.new_locale ctx
          in Proof.set_facts [next_specthm] stat end)
      |> Proof.map_context (fn ctx => 
            Proof_Context.put_thms false ("\<nu>thesis",
              SOME [Drule.mk_term (cterm_of ctx goal)]) ctx
          )
  end
end

end
