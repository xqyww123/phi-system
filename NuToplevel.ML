(*  Title:      NuToplevel.ML
    Author:     Qiyuan Xu

The toplevel structure of the ν-system.

`begin_proc (argument-statement, for-fixes, including bundles)`
    starts the block for procedure construction. The block is based on `notepad`. 

*)

signature NU_TOPLEVEL = sig
  val register_label_head : string
  val show_proc_expression_attr : attribute context_parser

  val begin_proc_cmd : Attrib.binding 
        -> xstring (*argument*)
        -> xstring (*return value*)
        -> (binding * string option * mixfix) list (*for fixes*)
        -> (xstring * Position.T) list (*includes*)
        -> (Attrib.binding * (string * string list) list) list (*pre-conditions*)
        -> bool -> Proof.context -> Proof.state
  val finish_proc_cmd : Toplevel.transition -> Toplevel.transition
  
  val setup_proof : bool -> Method.text option
        -> (Proof.context * thm list list -> Proof.state -> Proof.state)
        -> (binding * typ option * mixfix) list (*fixes*)
        -> (Thm.binding * (term * term list) list) list (*premis*)
        -> (term * term list) list list (*no binding is allowed*)
        -> bool -> Proof.state -> thm list * Proof.state
  val prove_prem : bool -> Proof.state -> thm list * Proof.state
  val have_aux : ((Thm.binding * attribute list) * (term * term list) list) list
        -> bool -> Proof.state -> thm list * Proof.state
  val have_aux_cmd : ((Attrib.binding * Token.src list) * (string * string list) list) list
        -> bool -> Proof.state -> thm list * Proof.state

  val process_cmd : Token.T list -> Proof.state -> Proof.state
  (* val have_cmd :
        Proof.state -> Proof.state *)

  (* val transition_cmd : ('a -> thm -> thm) -> 'a list parser -> (Toplevel.transition -> Toplevel.transition) parser
  val transition : ('a -> thm -> thm) -> int (* auto level *) -> 'a list -> Proof.state ->
  Proof.state *)
  (* val end_proc : state -> state *)
end

structure NuToplevel : NU_TOPLEVEL = struct
open NuHelp NuBasics Term HOLogic Thm NuSys
type context = Proof.context
type state = Proof.state
val register_label_head = "\<upsilon>"
val delimiter_name = "NuPrim.Stack_Delimiter"
val eof_ctx_stack_name = "NuPrim.End_of_Contextual_Stack"
fun mk_eof_ctx_stack tm = Const(eof_ctx_stack_name, dummyT) $ tm

val bool_opt_parser = Scan.lift
      (Parse.$$$ "=" |-- ((Args.$$$ "false" >> K false) || (Args.$$$ "true" >> K true)))

fun map_theory_total f = Context.mapping f (Proof_Context.background_theory f)

(* val show_proc_expression = Config.declare_bool ("show_proc_expression", \<^here>) (K false) *)
local
val omitted = [Syntax.Print_Rule (("logic", "_codeblock_ x"),
      ("logic", "CONST CodeBlock x exp"))]
val detailed = [Syntax.Print_Rule (("logic", "_codeblock_exp_ x exp"),
      ("logic", "CONST CodeBlock x exp"))]
in
val show_proc_expression_attr = let
  fun attr opt _ ctx = ctx |> map_theory_total
    (Isar_Cmd.no_translations (if opt then omitted else detailed)
    #> Isar_Cmd.translations  (if opt then detailed else omitted))
  in bool_opt_parser >> (Thm.declaration_attribute o attr) end
end

(** proc command **)

val indTy = Type ("Nat.ind", [])
val stack_R = Free ("\<R>", Type ("Set.set", [TFree ("'\<R>", ["NuPrim.lrep"])]))
val arg_stat_term_name = "\<ss>"

(** proc command **)

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
    val (names,args) = arg |> HOLogic.strip_tuple |> map pass_name |> split_list
    val names = names |> Name.variant_list []
    val arg = list_mk_binop_r0 delimiter_name (mk_eof_ctx_stack stack_R) args
  in
    (arg, names)
  end
fun parse_ret ret =
  ret |> HOLogic.strip_tuple
    |> list_mk_binop_r0 delimiter_name (mk_eof_ctx_stack stack_R)

structure ProcConstructionData = Generic_Data
(
  type T = proc_conctx
  val empty: T = {proc_const = dummy_c, binding = Binding.empty, goal = dummy_c}
  val extend = I
  val merge : T * T -> T = #1
)

val v_proc_var = ("\<p>\<r>\<o>\<c>",0)
val v_goal_name = "\<nu>goalaa"
val vv_proc_const_name = "?\<p>\<r>\<o>\<c>"
val final_proc_rewrite_rules = @{thms final_proc_rewrite}
fun begin_proc_cmd binding arg ret fixes includes preconds int ctx =
  let
    val binding = binding |> apsnd (map (Attrib.check_src ctx))
    val preconds = preconds |> map (apfst (apsnd (map (Attrib.check_src ctx))))
    val (arg, reg_names) = arg |> Syntax.parse_term ctx |> parse_arg

    val ret = ret |> Syntax.parse_term ctx |> parse_ret
    val includes = includes |> map (Bundle.check ctx)
    val parse_term = Syntax.parse_term ctx
    val parse_prop = Syntax.parse_prop ctx
    val (goal,th) = begin_proc ctx (arg,ret) [] (*reg_names*)
    val elems = [Element.Fixes (fixes |> map (fn (b,ty,f) => (b, Option.map (Syntax.parse_typ ctx) ty, f))),
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
      (* |> Proof.map_context (Context.proof_map (ProcConstructionData.map
          (K {proc_const = cterm_of ctx proc, binding = fst binding, goal = cterm_of ctx goal}))) *)
      |> Proof.proof (SOME (Method.Basic (fn _ => fn _ =>
            Context_Tactic.CONTEXT_TACTIC Tactical.all_tac), Position.no_range))
      |> Seq.the_result "impossible"
      |> Proof.using_facts [] |> Proof.enter_forward (*|> Proof.begin_block*)
      |> Proof.set_facts [th]
  end

fun basic_method r = Method.Basic (fn ctxt => fn _ => CONTEXT_TACTIC (PRIMITIVE (r ctxt)))
val finish_proc_cmd = Toplevel.end_proof (fn int => fn stat =>
  let
    val ctx = Proof.context_of stat
    val conctx = ProcConstructionData.get (Context.Proof ctx)
    val goal = Proof_Context.read_term_schematic ctx "?thesis"
                |> open_schematic_term
    val th = Proof.the_fact stat
    (* val (proc,_,_) = prop_of th |> dest_procedure *)
(* Assumption.all_assms_of ctx' |> @{print}; *)
    val end_tac = basic_method (fn ctx' => fn t => 
      (finish_proc ctx (cterm_of ctx goal)
        (singleton (Proof_Context.export ctx ctx') (elim_SPEC th |> fst))) RS t
        handle e => raise @{print} e)
  in
    stat |> Proof.set_facts [th] 
      |> Proof.global_qed (SOME (end_tac, Position.no_range), false)
  end
  )
  (* #> Isar_Cmd.qed NONE *)

(* fun begin_proc_cmd (statement, pos) fixes assumes ctx =
  let
    val (arg, labels) = statement |> Syntax.parse_term lthy |> parse_argument lthy
    val stat = ctx
          |> Proof.theorem NONE TODO 
          |> Proof.begin_block
          |> NuHelp.fix_frees pos [stack_R]
          |> Proof.fix_cmd fixes
    val lthy = Proof.context_of stat
    val (arg, labels) = statement |> Syntax.parse_term lthy |> parse_argument lthy
    val stat = stat |> NuHelp.fix_frees pos (Variable.add_frees lthy arg [] |> map Free)
    val lthy = Proof.context_of stat
    val _ = statement |> Syntax.parse_term lthy (* a dirty hack to fix the displayed color *)
    val arg = arg |> free_to_fix lthy |> Thm.cterm_of lthy
    val (th, to_fix) = arg |> start_construction lthy "\<t>\<o>\<p>_\<p>\<r>\<o>\<c>"
    val _ = @{print} th
    val stat = stat |> Proof.set_facts [th]
  in
    stat
  end *)

(* fun fold_last_flag f [] x = x
  | fold_last_flag f [v] x = f true v x
  | fold_last_flag f (v::r) x = fold_last_flag f r (f false v x)
fun transition tr auto_level xs stat =
      Proof.the_fact stat |> fold_last_flag (fn last => fn x =>
        tr x #> NuSys.process stat (if last then auto_level else 0)) xs
      |> (fn specthm => Proof.set_facts [specthm] stat)
fun transition_cmd tr arg_parser =
      (arg_parser -- NuParse.auto_level) >> (fn (arg, auto_level) =>
        Toplevel.proof (transition tr auto_level arg)) *)
fun process_cmd toks stat =
  stat |> Proof.set_facts
    [(NuSys.process stat (Proof.the_fact stat) --| Scan.catch Parse.eof ) toks |> fst]

val codeblock_attrs = [] (* map (Attrib.attribute @{context}) @{attributes
[in_using]} *)
fun hyp_export is_goal asms = (I,I)
fun setup_proof strict_asm before_qed after_qed' fixes assumes gl int stat =
  let open Proof
    val specthm = the_fact stat
    val codeblocks = codeblocks_of specthm
    fun after_qed ctxthms stat =
      stat |> end_block 
           |> after_qed' ctxthms
  in
    stat |> begin_block
      |> assm hyp_export [] [] (map (fn cb =>
          ((Binding.name (codeblock_name cb),codeblock_attrs), [(cb,[])])) codeblocks)
      |> map_context (load_specthm specthm)
      |> have strict_asm before_qed after_qed fixes assumes (map (pair Binding.empty_atts) gl) int
      |> apsnd (fn stat => using_facts (Named_Theorems.get (context_of stat) "NuSys.in_using") stat)
  end

fun prove_prem int stat =
  let open Proof
    val specthm = the_fact stat
    val (focus,aux) = elim_SPEC specthm
    val goal = Thm.prop_of specthm |> dest_SpecTop |> #1 |> Logic.dest_implies |> #1
    fun after_qed (ctx',[[th]]) stat =
      let
        val [th] = Proof_Context.export ctx' (context_of stat) [th]
      in
        set_facts [(NuProcessor.process_no_input
          (Proof.context_of stat |> AutoLevel.put 0)
            (intro_SPEC (th RS focus, aux)))] stat
      end
  in
    stat |> setup_proof false NONE after_qed [] [] [[(goal,[])]] int
  end

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
        stat |> map_context_result (declare_auxes (binds ~~ thes) specthm)
          |-> set_facts o single
      end

           
  in
    stat |> setup_proof false NONE after_qed [] [] (map snd goals) int
  end

val have_aux = gen_have_aux (K I) Syntax.check_prop
val have_aux_cmd = gen_have_aux Attrib.attribute_cmd Syntax.read_prop

(* fun have_cmd stat =
  stat |> Proof.have_cmd 
      Proof.state -> Proof.state *)

end
