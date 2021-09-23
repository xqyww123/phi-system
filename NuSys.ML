(* The Signature *)
signature NU_SYS = sig
  (** Tactics **)
  exception CastFail of thm
  type proc_conctx = {proc_const: cterm, binding: Binding.binding, goal: cterm}
  val raw_auto : Proof.context -> tactic
  val premise_tac : Proof.context -> tactic
  val auto_resolve : (thm list (*major*) * thm list option (*minor*)) option ->
    thm list (*addtional major*) -> Proof.context -> tactic
  val auto_resolve_rule : (thm list (*major*) * thm list option (*minor*)) option ->
    thm list (*addtional major*) -> Proof.context -> thm -> thm


  (** Basic Operations **)

  (*
    `conversion` tries to convert the procedure theorem to the given form.
      By @{thm NuPrim.conversion}, it generates a @{term Conversion} premise intended to be solved
      by `cast` operation.
    `cast` operations solves the first premise by `auto_resolve0`. Several proof obligation that cannot
      be solved automatically will be charged as premises in the result theorem.
          Γ |- cast_premise ==> P
      ---------------------------------
          Γ |- Premise Q1 ==> Premise Q2 ==> ... ==> P
      where @{term "Premise Q1, Premise Q2"} are proof obligations of the cast.

    In the cast proving, the unsolved premise marked with @{term Premise} tag is considered as
    accecptable proof obligations intented to be solved by users (or by automatic provers if it
    succeeds),
    while any other unsolved premises are considered as failures of the casting or conversion, which
    raise a CastFail exception.

    Also note, in the `auto_resolve0` and also `premise_tac`, only premises tagged with @{term
    Premise} will be tried to be solved automatically, while any other permises will not
    be touched by automatic provers.
  *)
  val conversion : Proof.context -> cterm (*to*) -> thm (*from*) -> thm
  val cast : Proof.context -> thm -> thm

  (*
    `apply_procs ctx procs whole_meta` applies the first appliable procedure in the `procs`
    on the `whole_meta`, by exact (schematical) matching first and then converted calling second
    (see @{thm NuPrim.apply_proc_conv}) with automatic cast proof by cast_tag.

    About `accept_proc`, see @{thm NuPrim.accept_proc}
  *)
  val apply_procs_major : Proof.context -> thm list (*procs*) -> thm (*whole*) -> thm
  val apply_proc : Proof.context -> thm (*proc*) -> thm (*whole*) -> thm (*whole*)
  val apply_procs : Proof.context -> thm list -> thm -> thm
  val accept_proc : Proof.context -> thm -> thm

  val process : Proof.state -> thm -> thm parser

  val start_proc : Proof.context -> string (*blk name*) -> cterm -> thm (* see @{thm NuPrim.start_proc} *)
  val finish_proc : Proof.context -> cterm (*goal*) -> thm -> thm (* see @{thm NuPrim.finish_proc} *)

  (*
    `declare_facts` declares ν-facts embedded in the specification theorem.
    `load_specthm` activates all embedded ν-facts in a specification theorem.

    There are two situation in the ν-system, the one for deductive construction
    and the other one for normal Isar proof (e.g. νhave and νobtain).

    In the deductive construction, all ν-facts are embedded in the specification
    theorem, and the specification theorem has several codeblock assumptions
    as undeclared hypothesises that are undeclared in the `Assumption`
    structure. Codeblock assumption stores the constructed program and represents
    the partial correctness hypothesises under the current symbolic execution
    (the assertion that the execution so far is normal).
    The codeblock assumption is updated by every `accept_proc` operation.

    The operation `load_specthm` convert current construction context into a normal
    Isar context by loading all embedded ν-facts with attribute evaluation and
    declaring the codeblock assumptions. Therefore the codeblock assumptions are
    fixed and procedure construction cannot be proceeded.

    Attributes sent to `declare_facts` are not activated immediately, but stored
    and activated until `load_specthm`, in the context loading the ν-facts.
    Therefore, declarative attributes do not touch the deductive context,
    but only the loading context.
  *)
  val declare_fact  : Thm.binding * thm list -> thm -> Proof.context -> thm * Proof.context
  val declare_facts : (Thm.binding * thm list) list -> thm -> Proof.context -> thm * Proof.context
  (* `load_specthm (ctx,specthm)` puts auxiliary facts into the context by the name `\<nu>aux` *)
  val load_specthm  : thm -> Proof.context -> Proof.context

end

(* The Structure *)
structure NuSys : NU_SYS = struct
open Thm NuBasics Term
exception CastFail of thm
type proc_conctx = {proc_const: cterm, binding: Binding.binding, goal: cterm}

structure NuFacts = Generic_Data
(
  (*key : name of the auxiliary fact, value: the attribute to be evaluated*)
  type T = (Position.T * attribute list) Symtab.table; 
  val empty: T = Symtab.empty
  val extend = I
  val merge : T * T -> T = Symtab.join (fn _ => fn _ => raise Symtab.SAME);
)
fun get_aux_attrs ctx (name,auxth) =
  case the_default (Position.none,[]) (Symtab.lookup (NuFacts.get (Context.Proof ctx)) name)
    of (pos,attrs) =>
      ((Binding.make (name,pos), attrs), [(Conjunction.elim_conjunctions auxth,[])])
fun note_auxes auxes ctx =
  Proof_Context.note_thmss "" (map (get_aux_attrs ctx) auxes) ctx
fun fold1 f (h::r) = fold f r h
  | fold1 f [] = raise Fail "fold1"
fun declare_fact ((binding,attrs),auxes) th ctx =
  let
    val name = Binding.name_of binding
    val _ = if name = "\<glowing_star>" then error "reserved keyword: \<glowing_star>" else ()
  in
  ctx |> Context.proof_map (NuFacts.map (Symtab.update_new (name, (Binding.pos_of binding, attrs))))
    |> pair (@{thm NuPrim.declare_fact} OF [intro_param_name name, fold1 Conjunction.intr auxes, th])
  end
fun declare_facts auxes th ctx =
  fold (fn a => fn (th,ctx) => declare_fact a th ctx) auxes (th,ctx)


val aux_name = "that" and aux_name_raw = "\<nu>aux'raw"
fun hyp_export is_goal asms = (I,I)
val codeblock_attrs = [] (* map (Attrib.attribute @{context}) @{attributes [used]} *)
fun load_specthm specthm ctx =
  (case elim_SPEC specthm of (focus,aux) =>
  let
    val auxes = user_facts_in_collection aux
    val codeblocks = codeblocks_of specthm
  in
    ctx
      |> Proof_Context.add_assms hyp_export (map (fn cb =>
          ((Binding.name (codeblock_name cb),codeblock_attrs), [(cb,[])])) codeblocks) |> #2
      |> note_auxes auxes
      |-> (fn ths => Proof_Context.put_thms false (aux_name_raw, SOME (flat (map snd ths))))
  end)
fun aux_facts ctx = Proof_Context.get_thms ctx aux_name
fun aux_facts_raw ctx = Proof_Context.get_thm ctx aux_name_raw






(** Tactics **)
fun head_only tac th =
  if nprems_of th = 1
  then tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude
fun raw_auto ctx =
  (ALLGOALS (Method.insert_tac ctx (Named_Theorems.get ctx "NuSys.used"))
    THEN Simpdata.auto_tac ctx)

(*** Premise tac ***)
val Premise_I = @{thm NuPrim.Premise_I}
fun mk_premise_tac withdraw ctx th =
  if AutoLevel.get ctx >= 2 andalso can (major_prem_of #> dest_premise_tag) th
  then (head_only (SOLVED' (K (HEADGOAL (resolve0_tac [Premise_I]) THEN raw_auto ctx)) 1)
      ORELSE withdraw) th
  else Seq.empty
val FailedPremise_I = @{thm FailedPremise_I} and FailedPremise_D = @{thm FailedPremise_D}
val withdrawable_premise_tac = mk_premise_tac (Seq.succeed o undisch o @{print} o (fn x => FailedPremise_D RS x))
val dest_failed_premise_tag = dest_monop "NuSys.FailedPremise"
val premise_tac = mk_premise_tac Seq.fail
fun fininsh_premise_hyps th =
  fold ((fn x => FailedPremise_I RS x) oo implies_intr)
    (chyps_of th |> filter (can (dest_failed_premise_tag o term_of))) th

(*** Simplify tag tac ***)
fun simp_tag_tac ctx th =
  case try (fn th => cprem_of th 1 |> dest_simplify_tag_c) th
    of SOME (_,y) => ((Simplifier.rewrite ctx y RS @{thm Simplify_I}) RS th) |> Seq.single
     | NONE => Seq.empty

(*** auto resolve tac ***)
fun auto_resolve thms addtion ctx  =
  let 
    val (thms,minor_thms) = case thms of SOME (major, SOME minor) => (major, minor)
                              | SOME (major, NONE) => (major, [])
                              | NONE => (Named_Theorems.get ctx "NuPrim.\<nu>intro",
                                         Named_Theorems.get ctx "NuPrim.\<nu>intro'")
    val thms = addtion @ thms
  in HEADGOAL (SOLVED' (REPEAT_DETERM_N 100 o (fn i =>
      simp_tag_tac ctx
      ORELSE resolve_tac ctx thms i
        ORELSE premise_tac ctx
        ORELSE resolve_tac ctx minor_thms i
    ))) #> Seq.map fininsh_premise_hyps
  end
val auto_resolve0 = auto_resolve NONE []

fun auto_resolve_rule' major_minor addition ctx =
  Tactic.rule_by_tactic ctx (REPEAT (auto_resolve major_minor addition ctx))
fun auto_resolve_rule major_minor addition ctx th =
  if can dest_SpecTop (prop_of th)
  then elim_SPEC th
    |> apfst (auto_resolve_rule' major_minor addition (load_specthm th ctx))
    |> intro_SPEC
  else auto_resolve_rule' major_minor addition ctx th
val auto_resolve_rule0 = auto_resolve_rule NONE []



  (** Basic Operations **)

fun conclude fail x =
  case Seq.pull x
    of SOME (th, other) => Goal.conclude th
     | NONE => fail ()

fun cast ctx th = 
  Goal.protect 1 th |> head_only (auto_resolve0 ctx)
        |> conclude (fn _ => raise CastFail th)
val conversion_thm = @{thm conversion}
fun conversion ctx to from =
  let
    val (f ,U ,V ) = dest_procedure_c (cconcl_of from)
    val (f',U',V') = dest_procedure_c to
    val a = dest_ctyp0 (ctyp_of_cterm f)
    val b = dest_ctyp0 (dest_ctyp1 (ctyp_of_cterm f))
    val c = dest_ctyp0 (ctyp_of_cterm f')
    val d = dest_ctyp0 (dest_ctyp1 (ctyp_of_cterm f'))
    val rule = Thm.instantiate
      ([((("'a",0),["NuPrim.lrep"]), a),
        ((("'b",0),["NuPrim.lrep"]), b),
        ((("'c",0),["NuPrim.lrep"]), c),
        ((("'d",0),["NuPrim.lrep"]), d)
       ],[
        ((("f",0),  typ_of_cterm f),  f),
        ((("U",0),  typ_of_cterm U),  U),
        ((("V",0),  typ_of_cterm V),  V),
        ((("f'",0), typ_of_cterm f'), f'),
        ((("U'",0), typ_of_cterm U'), U'),
        ((("V'",0), typ_of_cterm V'), V')])
      conversion_thm
  in
    (from RSN (2,rule)) |> cast ctx
  end

local open Tactical Tactic
val apply_proc_thm = @{thm NuPrim.apply_proc} and apply_proc_conv_thm = @{thm NuPrim.apply_proc_conv}
val vA = (("'a",0),["NuPrim.lrep"])
fun v_blk t = (("blk",0), mk_stateT t)
fun vS t = (("S",0), HOLogic.mk_setT t)
fun mk_apply_thms apply_thm focus =
  let
    val (blk,nuSet) = cprop_of focus |> dest_Trueprop_c |> dest_CurrentConstruction_c
    val aT = ctyp_of_cterm blk |> dest_ctyp0
    val at = typ_of aT
  in
    Thm.implies_elim
      (Thm.instantiate ([(vA,aT)],[(v_blk at, blk),(vS at, nuSet)]) apply_thm) focus
  end
fun resolve_N thas thb i =
  biresolution NONE false (map (pair false) thas) i thb |> Seq.map solve_constraints
in
fun apply_procs_major ctx procs major  =
  resolve_N procs (mk_apply_thms apply_proc_conv_thm major) 2 |> Seq.map (Goal.protect 1)
    |> Seq.append (resolve_N procs (mk_apply_thms apply_proc_thm major) 1
                    |> Seq.map (Goal.protect 0))
    |> Seq.maps (auto_resolve0 ctx)
    |> Seq.pull |> (fn x => case x of SOME (th,_) => Goal.conclude th
                             | NONE => raise THM ("fail to make the call", 0, major::procs))
end
fun apply_procs ctx procs whole =
  elim_SPEC whole |> apfst (apply_procs_major ctx procs) |> intro_SPEC
fun apply_proc ctx = apply_procs ctx o single

val accept_proc_thm = @{thm NuPrim.accept_proc}
fun accept_proc0 ctx wmeta =
  wmeta |> disch_current_codeblock
    |> mk_PropBlock 0 
    |> (fn x => x RS accept_proc_thm)
    |> (fn th => 
        let val (vname,vty) = prems_of th |> hd |> dest_codeblock |> #1 |> dest_Var
          val (name,_) = current_block_var wmeta |> dest_Free
        in Thm.instantiate ([],
            [((vname,vty), Thm.cterm_of ctx (Free (name,vty)))]) th end)
    |> undisch
fun accept_proc ctx meta = 
  (if can (prop_of #> dest_SpecTop #> #1 #> block_var_of_Constuction) meta
  then meta else auto_resolve_rule0 ctx meta) |> accept_proc0 ctx

val process = NuProcessor.process o Proof.context_of


val start_proc_thm = @{thm NuPrim.start_proc}
fun start_proc ctx blk_name arg_nuTy =
  let
    val argTy = (case dest_Type (typ_of_cterm arg_nuTy) of ("Set.set", [ty]) => ty
                   | _ => raise Fail "start_proc - argTy - not a set")
    val stat_var = Free (blk_name, mk_stateT argTy) |> cterm_of ctx
    val arg_var = Free (blk_name^"_arg", argTy) |> cterm_of ctx
    val init_thm = Drule.instantiate'_normalize [SOME (ctyp_of ctx argTy)]
                      [SOME stat_var, SOME arg_var, SOME arg_nuTy] start_proc_thm
    val init_thm = init_thm |> undisch
  in
    init_thm
  end

fun meta_eq_to_hol_eq th =
  let
    val (L,R) = cprop_of th |> Thm.dest_equals
    val rule = Thm.instantiate
          ([((("'a",0),["HOL.type"]),ctyp_of_cterm L)],
           [((("A",0),typ_of_cterm L),L), ((("B",0),typ_of_cterm R),R)])
              @{thm HOL.meta_eq_to_obj_eq}
  in
    Thm.implies_elim rule th
  end

val finish_proc_thm = @{thm NuPrim.finish_proc}
fun finish_proc ctx goal th =
  let
    val codeblock = current_codeblock th
    val (s,a,_,_) = dest_codeblock_c codeblock
  in
    th |> implies_intr codeblock
       |> forall_intr s |> forall_intr a
       |> (fn x => x COMP finish_proc_thm)
       |> conversion ctx goal 
  end




end
