(* The Signature *)
signature NU_SYS = sig
  (** Tactics **)
  exception CastFail of thm
  exception ReasoningFail of thm
  val raw_auto : Proof.context -> tactic

  (** Basic Operations **)

  (*
    `conversion` tries to convert the procedure theorem to the given form.
      By @{thm NuPrime.conversion}, it generates a @{term Conversion} premise intended to be solved
      by `auto_resolve`
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
  val conversion : cterm (*to*) -> context_state (*from*) -> context_state
  val conversion_completely : cterm (*to*) -> context_state (*from*) -> context_state
        (* solve all the premises by Nu_Resonser, raising CastFail if failed *)
  val cast : cterm (*desired nu*) -> context_state (*sequent*) -> context_state
  val cast_completely : cterm (*desired nu*) -> context_state (*major*) -> context_state
        (* solve all the premises by Nu_Resonser, raising CastFail if failed *)

  val apply : thm list -> context_state -> context_state
  val apply_proc_naive : thm (*proc*) -> context_state (*meta or major*) -> context_state
  val accept_proc : context_state -> context_state

  val set_param : term -> context_state -> context_state
  val set_param_cmd : string -> context_state -> context_state
  val set_label : string -> context_state -> context_state

  val start_proc : string (*blk name*) -> cterm -> Proof.context -> context_state
  val rename_blk_var : string -> context_state -> cterm (*renamed block*) * context_state
        (* current old_name reulst in ...
        * ---------------------------------
        *  current new_name reulst in *)

  val auto_construct : cterm -> context_state -> context_state

  val setup_proof : (Proof.context -> (string * string) * (string * thm list) list -> unit)
        -> Proof_Context.mode -> bool -> string -> Method.text option
        -> (Proof.context * thm list list -> Proof.state -> Proof.state)
        -> (binding * typ option * mixfix) list (*fixes*)
        -> (Thm.binding * (term * term list) list) list (*premis*)
        -> (term * term list) list list (*no binding is allowed*)
        -> Proof.state -> thm list * Proof.state
end

(* The Structure *)
structure NuSys : NU_SYS = struct
open Thm NuBasics Term
exception CastFail of thm
exception ReasoningFail of thm

val aux_name = "that" and aux_name_raw = "\<phi>aux'raw"
fun hyp_export is_goal asms = (I,I)
val curr_const_attrs = [Thm.declaration_attribute (Named_Theorems.add_thm "NuSys.useful")]
fun aux_facts ctxt = Proof_Context.get_thms ctxt aux_name
fun aux_facts_raw ctxt = Proof_Context.get_thm ctxt aux_name_raw


fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg'' th = Seq.make (fn () => (@{print} th; raise NDBG th))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty)))

(** Tactics **)
fun head_only tac th =
  if nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude
fun raw_auto ctxt =
  ((Method.insert_tac ctxt (Named_Theorems.get ctxt "NuSys.useful") 1)
    THEN Clasimp.auto_tac ctxt)



(*** auto resolve tac ***)
fun SOLVED tac st =
  if Thm.nprems_of st = 0 then all_tac st
  else (tac st |> Seq.filter (fn st' => Thm.nprems_of st' < Thm.nprems_of st));

fun SOLVED_RULE rule fail (ctxt,thm) =
  if Thm.nprems_of thm = 0 then (ctxt,thm)
  else (case rule (ctxt,thm) of SOME (ctxt',thm') =>
          if Thm.nprems_of thm' < Thm.nprems_of thm
          then (ctxt',thm')
          else fail (ctxt',thm')
        | NONE => fail (ctxt,thm))

fun REPEATX tac =
  let
    fun rep qs st = if length qs > 100 then raise Fail "too deep tac" else
      (case Seq.pull (tac st) of
        NONE => SOME (st, Seq.make (fn () => repq qs))
      | SOME (st', q) => rep (q :: qs) st')
    and repq [] = NONE
      | repq (q :: qs) = if length qs > 100 then raise Fail "too deep tac" else
          (case Seq.pull q of
            NONE => repq qs
          | SOME (st, q) => rep (q :: qs) st);
  in fn st => Seq.make (fn () => rep [] st) end;


(** Basic Operations **)

fun cast desired_nu (ctxt,sequent) =
  let
    val cast = Proof_Context.get_thm ctxt "local.\<phi>cast"
    val cast' = Proof_Context.get_thm ctxt "local.\<phi>cast'"
    val cast  = Drule.infer_instantiate ctxt [(("T'",0),desired_nu)] cast
    val cast' = Drule.infer_instantiate ctxt [(("T'",0),desired_nu)] cast'
  in
    (ctxt, (sequent RS cast' handle THM _ => sequent RS cast))
  end

fun cast_completely desired_nu stat =
  cast desired_nu stat
    |> SOLVED_RULE Nu_Reasoner.reason (fn (_,thm) => raise CastFail thm)

fun conversion to (ctxt,from) =
  let open PhiSyntax
    val conversion_thm = Proof_Context.get_thm ctxt "local.\<phi>conversion"
    val (f ,U ,V ) = dest_procedure_c (cconcl_of from)
    val (f',U',V') = dest_procedure_c to
    val rule = Thm.instantiate
      (TVars.empty, Vars.make[
        ((("f",0),  typ_of_cterm f),  f),
        ((("U",0),  typ_of_cterm U),  U),
        ((("V",0),  typ_of_cterm V),  V),
        ((("f'",0), typ_of_cterm f'), f'),
        ((("U'",0), typ_of_cterm U'), U'),
        ((("V'",0), typ_of_cterm V'), V')])
      conversion_thm
  in
    (ctxt, from RSN (2,rule))
  end
fun conversion_completely to from =
  conversion to from
    |> apsnd (Goal.protect 1)
    |> SOLVED_RULE Nu_Reasoner.reason (fn (_,thm) => raise CastFail thm)
    |> apsnd (Goal.conclude)

fun export_codeblock ctxt cb sequent =
  let open PhiSyntax
    val reassemble_proc = Proof_Context.get_thm ctxt "local.\<phi>reassemble_proc"
    val (s',_,_) = dest_codeblock_c cb
  in
    sequent
      |> Thm.implies_intr cb
      |> Thm.forall_intr s'
      |> (fn th => th COMP reassemble_proc)
      (* |> Thm.assumption NONE 1
      |> Seq.make_results |> Seq.the_result "export_codeblock" *)
  end

fun accept_proc (ctxt,sequent) =
  let open PhiSyntax
    val (f,s,_,_) = dest_PendingConstruction (Thm.prop_of sequent)
    val tyb = range_type (fastype_of f)
    val name = term_name s |> Variable.revert_fixed ctxt
    val ([name],ctxt) = Variable.add_fixes [name] ctxt
    val s' = Free (name, tyb)
    val ctxt = Variable.declare_constraints s' ctxt
    val s' = Thm.cterm_of ctxt s'
    val accept_proc_thm = Proof_Context.get_thm ctxt "local.\<phi>accept_proc"
    val accept_proc_thm = Drule.infer_instantiate ctxt [(("s'",0),s')] accept_proc_thm
    val sequent = sequent RS accept_proc_thm
    val assm = Thm.cprem_of sequent 1
    val ([cb],ctxt) = Assumption.add_assms
          (fn _ => fn [cb] => (export_codeblock ctxt cb, I)) [assm] ctxt
    val sequent = cb RS sequent
  in
    (ctxt,sequent)
  end


fun apply appliants (ctxt,sequent) =
  NuApply.apply ctxt appliants sequent
    |> map (apsnd (Seq.map (pair ctxt)))
    |> Nu_Reasoner.reason_s ctxt
    |> (fn x => case Seq.pull x
                  of SOME ((ctxt',thm),_) => (ctxt', perhaps (try Goal.conclude) thm)
                   | NONE => raise THM ("fail to apply", 0, sequent::appliants))

fun apply_proc_naive appliants (ctxt,sequent)
  = (ctxt,NuApply.apply_proc_naive ctxt appliants sequent)


(*Param & Label*)
fun param_type sequent =
  NuBasics.param_type sequent
    |> map_atyps (fn ty => case ty of TVar _ => dummyT | _ => ty)
  (* TODO: how to parse (check) the term of a desired type pattern
  * (schematic type variable)? *)

fun set_param term (ctxt,sequent) =
  (ctxt,
    (term |> Type.constraint (param_type sequent)
          |> Syntax.check_term ctxt |> Thm.cterm_of ctxt |> NuBasics.intro_param)
      RS sequent)

fun set_param_cmd term (ctxt,sequent) =
  case try (dest_funT #> apfst dest_named) (param_type sequent)
    of SOME (name_and_tys, rng) =>
        let
          val fixes = map (fn (name,ty) =>
                (Binding.name name, (if ty = dummyT then NONE else SOME ty), NoSyn)) name_and_tys
          val (fixed_names, ctxt) = Proof_Context.add_fixes fixes ctxt
          val term = Syntax.parse_term ctxt term
                      |> NuHelp.tuple_abs (map fst name_and_tys ~~ map (rpair dummyT) fixed_names)
                      |> NuHelp.mk_monop @{const_name case_named}
        in
          set_param term (ctxt,sequent)
        end
     | NONE => set_param (Syntax.parse_term ctxt term) (ctxt,sequent)

fun set_label name (ctxt,sequent) = (ctxt, mk_label_thm name RS sequent)

fun finish_proc cc (ctxt,sequent) =
  let open PhiSyntax
    val reassemble_proc_final = Proof_Context.get_thm ctxt "local.\<phi>reassemble_proc_final"
    val (s',H',_) = dest_CurrentConstruction_c cc
  in
    sequent
      |> Thm.implies_intr cc
      |> Thm.forall_intr H'
      |> Thm.forall_intr s'
      |> (fn th => th COMP reassemble_proc_final)
      |> pair ctxt
  end


fun start_proc blk_name arg_nuTy ctxt =
  let open PhiSyntax
    val ([blk_name, RR],ctxt) = Variable.add_fixes [blk_name, "\<RR>"] ctxt
    val stat_var = Free (blk_name, mk_stateT ctxt)
    val ctxt = Variable.declare_constraints stat_var ctxt
    val init = Const("local.CurrentConstruction",
                  fastype_of stat_var --> dummyT
                                      --> typ_of_cterm arg_nuTy
                                      --> \<^typ>\<open>bool\<close>)
               $ stat_var $ Free (RR, dummyT)
    val init = Thm.cterm_of ctxt (Syntax.check_term ctxt init)
    val init = Thm.apply @{cterm Trueprop} (Thm.apply init arg_nuTy)
    val ([init],ctxt) = Assumption.add_assms
          (fn _ => fn [cc] => (snd o finish_proc cc o pair ctxt, I)) [init] ctxt
  in
    (ctxt,init)
  end

fun rename_blk_var name (ctxt,meta) =
  let open PhiSyntax
    val codeblock = current_codeblock meta
    val (s,_,_) = dest_codeblock_c codeblock
    val thy = Thm.theory_of_thm meta
    val s' = Thm.global_cterm_of thy (Free (name, typ_of_cterm s))
    val meta = meta |> implies_intr codeblock
                |> forall_intr s |> forall_elim s'
                (* |> forall_intr a |> forall_elim a' *)
  in
    (cprem_of meta 1, (ctxt, NuHelp.undisch meta))
  end


fun auto_construct target (ctxt,sequent) =
  let
    val Make_by_proc = Proof_Context.get_thm ctxt "local.\<phi>Make_by_proc"
    val stat = 
      (sequent RS Drule.infer_instantiate ctxt [(("exp",0),target)] Make_by_proc)
          |> Goal.protect 1
          |> pair ctxt
          |> Nu_Reasoner.reason
  in case stat of SOME (ctxt,sequent) =>
        if Thm.no_prems sequent
        then (ctxt, Goal.conclude sequent)
        else raise CTERM ("fail to construct", [target])
      | NONE => raise CTERM ("fail to construct", [target])
  end


fun setup_proof print_results mode strict_asm kind before_qed after_qed' fixes assumes gl stat =
  let open Proof
    val specthm = the_nu_fact stat
    fun after_qed ctxthms stat =
      stat |> end_block 
           |> after_qed' ctxthms
  in
    stat |> begin_block
      |> internal_goal print_results mode strict_asm kind before_qed after_qed fixes assumes
            (map (pair Binding.empty_atts) gl)
      (* |> apsnd (fn stat => using_facts (Named_Theorems.get (context_of stat)
      * "NuSys.useful") stat) *)
  end
end
