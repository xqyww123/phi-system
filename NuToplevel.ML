(*  Title:      NuToplevel.ML

The toplevel structure of the ν-system.

`begin_proc (argument-statement, for-fixes, including bundles)`
    starts the block for procedure construction. The block is based on `notepad`. 

*)

signature NU_TOPLEVEL = sig
  datatype cond_kind = Premise | Requirement
    (* Premise is automatically prefixed by @{term Premise} and added to
     * @{named_theorems useful}; Requirement is not. *)
  val register_Block_End_Hook : (context_state -> context_state) -> Proof.context -> Proof.context

  val put_thesis : cterm -> Proof.context -> Proof.context
  val get_thesis : Proof.context -> cterm

  val begin_proc_cmd : Attrib.binding 
        -> xstring (*argument*)
        -> xstring (*return*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (indexname list * string) list (*let patterns*)
        -> (Attrib.binding * (string * string list)) list (*local definitions*)
        -> (cond_kind * (Attrib.binding * (string * string list))) list (*preconditions*)
        -> string option
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
        -> string option
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
  val end_block_cmd : Phi_Generalization.generic -> bool -> Proof.state -> Proof.state
  
  val prove_prem : bool -> Proof.state -> thm list * Proof.state
  val synthesis : cterm -> context_state -> context_state
  (*val export_LLVM : theory -> theory *)
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
      if can dest_premise_tag (concl_of th) then th RS @{thm Premise_D} else th)]
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

fun parse_arg (X as (Const (@{const_name "\<phi>Type"}, _) $ _ $ _)) =
      X |> mk_monop @{const_name "Ele"}
  | parse_arg (Abs (a,ty, X)) = Abs (a,ty, parse_arg X)
  | parse_arg ((C as Const ("_type_constraint_", _)) $ X) = (C $ parse_arg X)
  | parse_arg ((C as Const (@{const_name "ExSet"}, _)) $ X) = (C $ parse_arg X)
  | parse_arg ((C as Const (@{const_name "Subjection"}, _)) $ X $ P) =
      (C $ parse_arg X $ P)
  | parse_arg X = X


fun put_thesis thesis = 
      Proof_Context.put_thms false ("\<phi>thesis", SOME [Drule.mk_term thesis])
fun get_thesis ctxt =
      Proof_Context.get_thm ctxt "\<phi>thesis" |> Drule.dest_term


fun print_results int = Proof_Display.print_results int (Position.thread_data ())

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt'
  in ((vars, xs), ctxt'') end

datatype cond_kind = Premise | Requirement






type working_mode = {
  domain: Proof.context -> term -> bool,
  desired_phi: term (*term of the current sequent*) -> term,
  desired_phi_c: cterm (*term of the current sequent*) -> cterm,
  end_block: (Proof.context * Proof.context) -> thm (*solution*) -> thm (*goal*) -> thm (*goal'*),
  end_proof: Proof.context -> thm (*solution*) -> thm (*goal*) -> thm (*goal'*)
}

structure Working_Modes = Generic_Data(
  type T = working_mode Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K false)
)

fun working_mode_on ctxt goal =
      Symtab.get_first (fn (_,mode) => if #domain mode ctxt goal then SOME mode else NONE)
        (Working_Modes.get (Context.Proof ctxt))
fun working_mode_on1 ctxt goal =
      case working_mode_on ctxt goal of SOME x => x
         | NONE => error ("Do not know how to handle goal " ^ Syntax.string_of_term ctxt goal)

fun orelse_opt f1 f2 x = case f1 x of SOME y => y | NONE => f2 x

fun strip_forall_implies btys (\<^const>\<open>Trueprop\<close> $ x) = strip_forall_implies btys x
  | strip_forall_implies btys (Const (\<^const_name>\<open>All\<close>, _) $ Abs (_,ty,x))
      = strip_forall_implies (ty::btys) x
  | strip_forall_implies btys (Const (\<^const_name>\<open>implies\<close>, _) $ _ $ x)
      = strip_forall_implies btys x
  | strip_forall_implies btys x = (btys,x)

fun abstract_bound_over (j, body) =
  let
    fun abs i lev tm =
      if Bound i aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (i+1) (lev + 1) t)
        | t $ u =>
            (abs i lev t $ (abs i lev u handle Same.SAME => u)
              handle Same.SAME => t $ abs i lev u)
        | _ => raise Same.SAME);
  in abs j 0 body handle Same.SAME => body end;



val procedure : working_mode = 
  let
    val desired_phi = orelse_opt (try (#3 o PhiSyntax.dest_CurrentConstruction))
           (#3 o PhiSyntax.dest_procedure)
    val desired_phi_c = orelse_opt (try (#3 o PhiSyntax.dest_CurrentConstruction_c))
           (#3 o PhiSyntax.dest_procedure_c)
    fun my_abstract_over _ (v as Free (name,ty)) body =
          Abs (name, ty, abstract_over (v,body))
      | my_abstract_over btys (Bound i) body =
          Abs ("", nth btys i, abstract_bound_over (i,body))
      | my_abstract_over _ v body =
          Abs ("", fastype_of v, abstract_over (v,body))
    fun exaustive_abst solution goal =
      let
        val thy = Thm.theory_of_thm solution
        val (_, (fg,_,_)) = Thm.major_prem_of goal
              |> strip_forall_implies []
              |> apsnd PhiSyntax.dest_procedure
        val (btys, (fs,_,_)) = Thm.concl_of solution
              |> strip_forall_implies []
              |> apsnd PhiSyntax.dest_procedure
      in case Term.strip_comb fg of (Var v, args) =>
           Thm.instantiate (TVars.empty,
                             Vars.make [(v, Thm.global_cterm_of thy
                                                    (fold (my_abstract_over btys) args fs))]) goal
           | _ => goal
      end
    fun initial_reassemble ctxt sequent =
          if can (PhiSyntax.dest_CurrentConstruction) (Thm.prop_of sequent)
          then sequent RS Proof_Context.get_thm ctxt "local.\<phi>reassemble_proc_0"
          else sequent
  in {
    domain = (K (can PhiSyntax.dest_procedure)),
    desired_phi = desired_phi,
    desired_phi_c = desired_phi_c,
    end_proof = (fn _ => fn solution => fn goal => solution RS exaustive_abst solution goal),
    end_block = (fn (ctxt,ctxt') => fn solution => fn goal =>
        let
          val solution' = singleton (Proof_Context.export ctxt ctxt') (initial_reassemble ctxt solution)
        in
          solution' RS exaustive_abst solution' goal
        end
        handle e => (Runtime.exn_system_message e; Exn.reraise (@{print} e)))
} end

val _ = Theory.setup (Context.theory_map
            (Working_Modes.map (Symtab.update_new ("procedure", procedure))))









fun gen_constr_envir prep_term prep_prop prep_typ prep_var prep_ctx mk_Goal
      binding arg ret rawfixes includes raw_lets raw_defines raw_preconds raw_goal_ctxt int ctxt =
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
      | prep_precond (Requirement, c) =
          prep_attrterm I c
    val preconds = map prep_precond raw_preconds

    val (goal', constr_process, post_process, fixes', preconds') =
          mk_Goal (ctx_parse,fixes,var_names)
                  (parse_term arg, parse_term ret, preconds)

    val goal = case raw_goal_ctxt of NONE => goal'
                 | SOME G => Const (\<^const_name>\<open>GOAL_CTXT\<close>, dummyT)
                              $ HOLogic.dest_Trueprop goal'
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

fun gen_begin_proc prep_term prep_prop prep_typ prep_var prep_Nu post_process binding =
  let
    val prep_ctx = I
    fun mk_Goal (ctxt,fixes,_) arg_ret_conds =
      let
        val (arg, ret, preconds) = prep_Nu ctxt arg_ret_conds
        (*val _ = debug_term ctxt "arg " arg
        val _ = debug_term ctxt "ret " ret*)
        val v_proc = Var (v_proc_var, PhiSyntax.mk_procT ctxt)
        val goal = mk_Trueprop
          (Const ("local.\<phi>Procedure", dummyT) $ v_proc $ arg $ ret)

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
            |> NuProcedure.define binding (post_process lthy
                (Raw_Simplifier.rewrite_rule lthy @{thms final_proc_rewrite} th))
            |-> (fn th => fn lthy =>
                  (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
                    (("\<phi>procedure", ""), [("", [th])]); lthy))
      in
        (goal, constr_process, post_process', fixes, preconds)
      end
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var prep_ctx mk_Goal binding
  end
    
val begin_proc =
      gen_begin_proc (K I) (K I) (K I) Proof_Context.cert_var (K I) (K I)
val begin_proc_cmd =
      gen_begin_proc Syntax.parse_term Syntax.parse_prop Syntax.parse_typ Proof_Context.read_var
        (fn ctxt => fn (arg,ret,conds) =>
          (parse_arg arg, parse_arg ret, conds)
        ) (K I)

fun gen_begin_rec_proc prep_term prep_prop prep_typ prep_var
        (binding,attr) raw_arg raw_ret (raw_vars, raw_fixes) =
  let open QuantExpansion
    val prep_ctx = I
    val func_name = Binding.name_of binding
    fun mk_Goal (ctxt,fixes,fixed_names) (arg,ret,conds) = 
      let
        val ([tArg,tRet], ctxt') =
                Variable.variant_fixes ["\<tau>Arg", "\<tau>Ret"]
                  (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)
        val origin_names = map (fn (n,_,_) => (Binding.name_of n)) raw_vars
        val var_names = take (length raw_vars) fixed_names
        val vars = origin_names ~~ (map (rpair dummyT) var_names)

        val arg = parse_arg arg
        val ret = parse_arg ret

        val conds' = map (snd #> fst #> perhaps (try dest_Trueprop)) conds
        val arg' = arg
              |> fold_rev (fn c => fn Nu =>
                    NuHelp.mk_binop @{const_name Subjection} (Nu,c)) conds'
              |> tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)
        val ret' = ret
              |> tuple_abs vars
              |> mk_cases_named origin_names
              |> (fn tm => tm $ Bound 0)

        val goal0 = mk_Trueprop (
              Const (@{const_name All}, dummyT) $ Abs("x", dummyT,
                (Const ("local.\<phi>Procedure", dummyT)
                  $ (Const ("local.op_recursion", dummyT)
                      $ Var ((tArg,0), dummyT)
                      $ Var ((tRet,0), dummyT)
                      $ Var ((func_name,0), dummyT))
                  $ arg'
                  $ ret')))
        val other_frees = Term.add_frees goal0 []
                       |> filter_out (fn (v,_) => exists (fn u => v = u) fixed_names)
        val (_,ctxt'') = Proof_Context.add_fixes
                            (map (fn (nam,_) => (Binding.name nam, NONE, NoSyn)) other_frees)
                            ctxt'
              

        val All = pure_All_expansion origin_names ctxt''
        val forall = forall_expansion origin_names ctxt''
        val recursion_thm = Proof_Context.get_thm ctxt'' "local.__op_recursion__"
        val Subjection_simp_proc_arg =
              Proof_Context.get_thm ctxt'' "local.Subjection_simp_proc_arg"
        val (_,proof0) = goal0
            |> Syntax.check_term ctxt'' |> Thm.cterm_of ctxt''
            |> Goal.init
            |> (HEADGOAL (resolve_tac ctxt'' [recursion_thm])
                THEN (Raw_Simplifier.rewrite_rule ctxt'' (*it is very ugly here!*)
                       (All::forall::Subjection_simp_proc_arg::
                        Named_Theorems.get ctxt'' @{named_theorems named_expansion})
                      #> Seq.single))
            |> Seq.maps (Nu_Reasoner.reason_tac ctxt'' o pair ctxt'')
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
            |> NuProcedure.define binding (
                th |> Drule.forall_intr_list
                        (map ( Thm.cterm_of lthy
                             o map_types (map_type_tvar (fn ((name,_),s) => TVar ((name,0),s)))
                             o map_aterms (fn (Var ((name,_),ty)) => Var ((name,0),ty) | x => x)
                             o Morphism.term (Proof_Context.export_morphism ctxt''' lthy)
                             o Free) vars'')
                   |> Conv.fconv_rule (Conv.repeat_changed_conv (Object_Logic.atomize lthy))
                   |> (fn sol => #end_proof procedure lthy sol
                                    (singleton (Proof_Context.export ctxt''' lthy) proof0))
                   |> Goal.conclude
                   |> Object_Logic.rulify lthy
               )
            |-> (fn th => fn lthy =>
                   (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
                      (("\<phi>procedure", ""), [("", [th])]); lthy))
      in
        (goal, constr_process, post_process', vars'_fix @ drop (length raw_vars) fixes, conds')
      end
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var prep_ctx mk_Goal
        (binding,attr) raw_arg raw_ret (raw_vars @ raw_fixes)
  end

val begin_rec_proc_cmd = gen_begin_rec_proc
      Syntax.parse_term Syntax.parse_prop Syntax.parse_typ Proof_Context.read_var

fun gen_begin_cast_cmd prep_term prep_prop prep_typ prep_var
      binding arg ret additional_prop =
  let
    fun mk_Goal (ctxt,fixes,_) (arg, ret, preconds) =
      let
        val arg = parse_arg arg
        val ret = parse_arg ret
        val additional_prop = case additional_prop
                                of SOME x => prep_term ctxt x
                                 | _ => @{term True}
        val goal = mk_Trueprop
          (Const ("local.\<phi>Subty", dummyT) $ arg $ ret $ additional_prop)
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
            (*NuBasics.set_nu_fact sequent*)
            stat
          end
        fun post_process binding int lthy th =
          (Proof_Display.print_results int (Binding.pos_of (fst binding)) lthy
            (("\<phi>cast", ""), [("", [th])]); lthy)
      in
        (goal, constr_process, post_process, fixes, preconds)
      end
  in
    gen_constr_envir prep_term prep_prop prep_typ prep_var I mk_Goal binding arg ret
  end

val begin_cast_cmd =
      gen_begin_cast_cmd Syntax.parse_term Syntax.parse_prop Syntax.parse_typ
      Proof_Context.read_var



structure Block_End_Hook = Proof_Data (
  type T = (context_state -> context_state) list
  val init = K []
)

fun register_Block_End_Hook hook = Block_End_Hook.map (fn L => hook::L)
fun invoke_Block_End_Hook (ctxt,sequent) =
  fold (fn hook => fn stat => hook stat) (Block_End_Hook.get ctxt) (ctxt,sequent)


fun RSNXX ctxt tha (i, thb) =
  (case Seq.pull (biresolution (SOME ctxt) false [(false, tha)] i thb) of
    SOME (th, _) => solve_constraints th
  | _ => raise THM ("RSNXX: no unifiers", i, [tha, thb]));
fun RSXX ctxt tha thb = RSNXX ctxt tha (1,thb);







local

fun basic_method r = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (r ctxt)))

fun gen_finish_proc qed genz int stat =
  let
    val ctxt_ = Proof.context_of stat
    val goal = get_thesis ctxt_
    val mode = working_mode_on1 ctxt_ (Thm.term_of goal)
  in stat |>
    Proof.map_context_result (fn ctxt =>
      let
        val sequent = NuBasics.the_programming_sequent' ctxt
        val desired_nu = #desired_phi_c mode goal
      in
        (ctxt,sequent)
          |> invoke_Block_End_Hook
          |> (case genz
                of Phi_Generalization.None => I
              | _ => NuSys.cast (#desired_phi mode (Thm.prop_of sequent)
                                  |> Phi_Generalization.generalize_cmd genz ctxt
                                  |> Syntax.check_term ctxt
                                  |> Thm.cterm_of ctxt))
          |> NuSys.cast desired_nu
          |> swap
      end
    )
    |-> NuSys.obligation_proof (print_results int) Proof_Context.mode_default false "" NONE
          (fn sequent => fn stat =>
      let
        val ctxt = Proof.context_of stat
        val end_tac = basic_method (fn ctxt' => #end_block mode (ctxt,ctxt') sequent)
       in
        stat
          |> Proof.set_facts [] 
          |> qed (SOME (end_tac, Position.no_range), false)
       end) [] []
     |> snd
  end
in
val end_block_cmd = gen_finish_proc Proof.local_qed

(* fun gen_finish_proc' prep_specthm qed int stat =
  let val sequent = Proof.the_fact stat
  in if current_block_depth sequent > 1 then 
      gen_finish_proc' prep_specthm qed int (end_block_cmd false stat)
    else gen_finish_proc prep_specthm qed int stat end *)
val finish_proc_cmd = gen_finish_proc Proof.local_qed
end


fun prove_prem int stat =
  let open Proof
    val specthm = the_nu_fact stat
    val goal = Thm.prop_of specthm
                |> Logic.dest_implies |> #1 (* |> dest_premise_tag |> mk_Trueprop *)
    fun after_qed (ctxt',[[th]]) stat =
      let
        val [th] = Proof_Context.export ctxt' (context_of stat) [th]
        val original_auto_level = Config.get (Proof.context_of stat) Nu_Reasoner.auto_level
        (* val th = th RS @{thm NuPrime.Premise_I} *)
      in
        stat |> Proof.map_context_result
                  (Config.put Nu_Reasoner.auto_level 0
                    #> (fn ctxt => NuProcessor.process_no_input (ctxt, th RS specthm))
                    #> apfst (Config.put Nu_Reasoner.auto_level original_auto_level)
                    #> swap)
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

fun synthesis term (ctxt, sequent) =
  let
    val mode_constr = can (PhiSyntax.dest_CurrentConstruction) (Thm.prop_of sequent)
    val synthesis = Proof_Context.get_thm ctxt  (if mode_constr then "local.__\<phi>synthesis__"
                                                                else "local.__\<phi>synthesis__antecedent")
                  |> Drule.infer_instantiate ctxt [(("X",0), term)]
                  |> (fn rule => if mode_constr then sequent RS rule
                                                else rule RS sequent)
  in
    case Nu_Reasoner.reason (ctxt, synthesis)
      of SOME ret => ret
       | NONE => error ("fail to synthesis "^Syntax.string_of_term ctxt (Thm.term_of term))
  end




local
val attr_useful = map (Attrib.attribute @{context}) @{attributes [useful]}
in

fun gen_begin_block prep_attr bindings int stat =
  let open Proof
    val ctxt = context_of stat

    val is_top = not (NuBasics.under_programming_environ ctxt)
    val stat =
          if is_top
          then stat
                |> Proof.apply (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (
                                    TRY (HEADGOAL (Raw_Simplifier.rewrite_goal_tac ctxt @{thms GOAL_CTXT_def}))
                                    THEN HEADGOAL (Object_Logic.full_atomize_tac ctxt)
                               )), Position.no_range)
                |> Seq.the_result "cannot atomize the first subgoal"
          else stat
    val sequent =
          if is_top
          then #goal (Proof.raw_goal stat)
          else the_nu_fact stat
                  |> Conv.fconv_rule (Conv.prems_conv 1 (Conv.repeat_changed_conv
                          (Object_Logic.atomize ctxt)))
    val stat = (if is_top then enter_forward (assert_backward stat) else stat)
                  |> begin_block

    val (vars, goal) = prop_of sequent
                        |> Logic.dest_implies |> #1
                        |> dest_Trueprop |> strip_binder_raw @{const_name All}
    val (var_names, stat) = stat
          |> Proof.map_context_result (Proof_Context.add_fixes
              (map (fn (nam,ty) => (Binding.name nam, SOME ty, NoSyn)) vars))
    val vars = map (Free o apsnd snd) (var_names ~~ vars)
    val goal = subst_bounds (rev vars, goal)
    val prems_goal = strip_binop_r @{const_name implies} goal
    val (prems, goal) = (front prems_goal, last prems_goal)
    val (proc,arg,ret) = PhiSyntax.dest_procedure goal

    val mode = working_mode_on1 ctxt goal
    
    val blk_name = case proc of (Var ((x,_),_)) => x
                      | _ => "block"
    val level = PhiSyntax.current_block_depth sequent
    val blk_name = "L\<phi>'" ^ (Int.toString level) ^ "_" ^ blk_name
    
    val (prems, goal) = (map mk_Trueprop prems, mk_Trueprop goal)
    
    fun after_qed (ctxt',[[th]]) stat =
      end_block stat |> (fn stat =>
          let val ctxt'' = context_of stat
              val vars' = Variable.export_terms ctxt' ctxt'' vars
              fun gen_sequent sequent =
                    #end_proof mode ctxt''
                      (singleton (Proof_Context.export ctxt' ctxt'') th
                        |> Drule.forall_intr_list (map (cterm_of ctxt'') vars')
                        |> Raw_Simplifier.rewrite_rule ctxt'' @{thms atomize_imp atomize_all})
                      sequent
          in if is_top
             then stat
                    |> enter_backward
                    |> apply (Method.Basic (fn _ => Method.SIMPLE_METHOD (Seq.single o gen_sequent)),
                              Position.no_range)
                    |> Seq.the_result "never fail"
             else NuBasics.set_nu_fact (gen_sequent sequent) stat
          end)

    val delta = length prems - length bindings
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

      |> Proof.map_context_result (start_proc blk_name (cterm_of ctxt arg) #> swap)
      |-> NuBasics.set_nu_fact
      |> Proof.map_context (fn ctxt => 
            Proof_Context.put_thms false ("\<phi>thesis",
              SOME [Drule.mk_term (cterm_of ctxt goal)]) ctxt
          )
      (* |> NuObtain.obtain_quick_pairs_perhaps_try *)
  end
val begin_block_cmd = gen_begin_block Attrib.attribute_cmd
val begin_block = gen_begin_block (K I)
end

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
