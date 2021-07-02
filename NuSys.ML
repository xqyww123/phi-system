signature NU_SYS = sig
  exception CastFail of term list
  type proc_conctx = {proc_const: cterm, binding: Binding.binding, goal: cterm}
  val conversion_goal : cterm (*to*) -> thm (*from*) -> thm
  val cast_tac : Proof.context -> tactic
  val cast : Proof.context -> thm -> thm

  val apply_proc : Proof.context -> thm (*proc*) -> thm (*spec*) -> thm (*spec*)
  val apply_procs : Proof.context -> thm list -> thm -> thm
  val accept_proc : Proof.context -> thm -> thm
  val assign_reg : Proof.context -> string (*name*) -> thm -> thm
  val load_reg : Proof.context -> string (*name*) -> thm -> thm

  val process : Proof.state -> thm -> thm parser

  val begin_proc : Proof.context -> binding -> term * term -> term * thm
  val finish_proc : Proof.context -> cterm (*goal*) -> thm -> thm

end
structure NuSys : NU_SYS = struct
open Thm NuBasics Term
exception CastFail of term list
type proc_conctx = {proc_const: cterm, binding: Binding.binding, goal: cterm}

fun conversion_goal to from =
  let
    val (f ,U ,V ) = dest_procedure_c (cconcl_of from)
    val (f',U',V') = dest_procedure_c to
    val a = dest_ctyp0 (ctyp_of_cterm f)
    val b = dest_ctyp0 (dest_ctyp1 (ctyp_of_cterm f))
    val c = dest_ctyp0 (ctyp_of_cterm f')
    val d = dest_ctyp0 (dest_ctyp1 (ctyp_of_cterm f'))
    val rule = Thm.instantiate
      ([((("'a",0),["HOL.type"]), a),
        ((("'b",0),["HOL.type"]), b),
        ((("'c",0),["HOL.type"]), c),
        ((("'d",0),["HOL.type"]), d)
       ],[
        ((("f",0),  typ_of_cterm f),  f),
        ((("U",0),  typ_of_cterm U),  U),
        ((("V",0),  typ_of_cterm V),  V),
        ((("f'",0), typ_of_cterm f'), f'),
        ((("U'",0), typ_of_cterm U'), U'),
        ((("V'",0), typ_of_cterm V'), V')])
      @{thm conversion_goal}
  in
    (from RSN (2,rule)) |> Goal.protect 1
  end

fun head_tac tac th =
  if nprems_of th = 1
  then tac th
  else Goal.init (cprem_of th 1) |> tac
        |> Seq.filter (fn th => nprems_of th = 0)
        |> Seq.map (Thm.implies_elim th o Goal.conclude)
fun obligation_auto_tac ctx th =
  if can (major_prem_of #> dest_obligation) th
  then if nprems_of th = 1
    then Simpdata.auto_tac ctx th
    else head_tac (obligation_auto_tac ctx) th
  else Seq.empty
fun cast_tac ctx =
  HEADGOAL (SOLVED' (REPEAT_DETERM_N 100 o (fn i =>
    resolve_tac ctx (Named_Theorems.get ctx "NuPrim.\<nu>cast") i
      ORELSE obligation_auto_tac ctx
  )))
fun cast_tac2 ctx =
   (REPEAT (HEADGOAL (resolve_tac ctx (Named_Theorems.get ctx "NuPrim.\<nu>cast"))
      ORELSE obligation_auto_tac ctx))
fun cast ctx goal = cast_tac2 ctx goal |> Seq.pull |> (fn x =>
      case x of SOME (th,other) => Goal.conclude th
              | NONE => raise TERM ("Cast fail", prems_of goal)
                  (* raise CastFail ((prems_of goal)) *)
              )

local open Tactical Tactic
val apply_proc_thm = @{thm NuPrim.apply_proc} and apply_proc_conv_thm = @{thm NuPrim.apply_proc_conv}
val vA = (("'a",0),["HOL.type"])
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
fun apply_procs ctx procs spec  =
  elim_SPEC spec |> apfst (fn focus =>
    resolve_N procs (mk_apply_thms apply_proc_conv_thm focus) 2 |> Seq.map (Goal.protect 1)
      |> Seq.append (resolve_N procs (mk_apply_thms apply_proc_thm focus) 1
                      |> Seq.map (Goal.protect 0))
      |> Seq.maps (cast_tac ctx)
      |> Seq.pull |> (fn x => case x of SOME (th,_) => Goal.conclude th
                                 | NONE => raise THM ("fail to make the call", 0, focus::procs))
    ) |> intro_SPEC
end
fun apply_proc ctx = apply_procs ctx o single
fun operate_reg operation ctx reg spec =
  apply_proc ctx (operation reg (registers_of_specthm spec |> term_of)) spec
val assign_reg = operate_reg NuRegisters.assign_reg
val load_reg = operate_reg NuRegisters.load_reg

val accept_proc_thm = @{thm NuPrim.accept_proc}
fun accept_proc ctx specthm =
  specthm |> disch_current_codeblock
    |> forall_intr (current_block_var specthm |> cterm_of ctx)
    |> mk_PropBlock 0 
    |> (fn x => x RS accept_proc_thm)
    |> param_set_free_var_name ctx (current_block_var specthm |> dest_Free |> #1)
    |> undisch

val process = NuProcessor.process o Proof.context_of

val top_blk_name = "\<t>\<o>\<p>_\<p>\<r>\<o>\<c>"
val argument_name = "\<a>\<r>\<g>\<u>\<m>\<e>\<n>\<t>"
val v_proc_var = ("\<p>\<r>\<o>\<c>",0)
fun starting_construction ctx arg_nuTy =
  let
    val argTy = (case dest_Type (typ_of_cterm arg_nuTy) of ("Set.set", [ty]) => ty
                   | _ => raise Fail "start_construction - argTy - not a set")
    val stat_var = Free (top_blk_name, mk_stateT (proc_ctx_ty (argTy, void_ty))) |> cterm_of ctx
    val arg_var = Free (argument_name, argTy) |> cterm_of ctx
    val init_thm = Drule.instantiate'_normalize [SOME (ctyp_of ctx argTy)]
                      [SOME stat_var, SOME arg_var, SOME arg_nuTy] start_construction_thm
    val init_thm = init_thm |> undisch
  in
    init_thm
  end

fun begin_proc ctx name (arg,ret) =
  let
    val (arg,ret) = apply2 (Syntax.check_term ctx) (arg,ret)
    val (argT,retT) = apply2 (type_of #> dest_Type #> #2 #> hd) (arg,ret)
    val procT = argT --> mk_stateT retT
    (*val (proc,ctx) = Proof_Context.background_theory_result (
          Sign.declare_const ctx ((name, argT --> mk_stateT retT), NoSyn)) ctx*)
    val goal = HOLogic.mk_Trueprop (
          Const ("NuPrim.Procedure",
                    (argT --> mk_stateT retT) --> mk_setT argT --> mk_setT retT --> boolT)
          $ Var (v_proc_var, procT) $ arg $ ret)
    val th = arg |> Thm.cterm_of ctx
              |> starting_construction ctx
  in
    (goal,th)
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

fun finish_proc ctx goal th =
  let
    val (tm,L) = cprop_of th |> dest_SpecTop_c
    val (T,R) = dest_Trueprop_c tm |> dest_CurrentConstruction_c |> #2 |> dest_Proc_CtxTy_c
    val codeblock = case codeblocks_of_c th of [cb] => cb
                       | _ => error "unfinished sub-block"
    val (s,a,S,f) = dest_codeblock_c codeblock
    val aT = ctyp_of_cterm a
    val bT = dest_ctyp0 (dest_ctyp0 (ctyp_of_cterm s))
    val cT = dest_ctyp1 (dest_ctyp0 (ctyp_of_cterm s))
    val finish_thm = Thm.instantiate (
          [((("'a",0),["HOL.type"]),aT),
           ((("'b",0),["NuPrim.lrep"]),bT),
           ((("'c",0),["NuPrim.register_collection"]),cT)
          ], [
           ((("S",0), typ_of_cterm S),S),
           ((("f",0), typ_of_cterm f),f),
           ((("T",0), typ_of_cterm T),T),
           ((("R",0), typ_of_cterm R),R),
           ((("L",0), typ_of_cterm L),L)
          ]) @{thm NuPrim.finish_construction}
    (* val def_term = prems_of th |> hd |> dest_Trueprop |> HOLogic.dest_eq |> Logic.mk_equals *)
  in
    th |> implies_intr codeblock
       |> forall_intr s |> forall_intr a
       |> implies_elim finish_thm
       |> conversion_goal goal |> cast ctx
    (* ctx |> Proof_Context.background_theory_result
            (Thm.add_def (Proof_Context.defs_context ctx) false true
                (Binding.suffix_name "_def" binding, def_term))
        >> (Thm.implies_elim th o meta_eq_to_hol_eq o snd)
        |> (fn (th,ctx) =>
          th |> conversion_goal goal |> cast ctx |> rpair ctx) *)
  end
end
