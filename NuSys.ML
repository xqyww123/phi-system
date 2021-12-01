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
  val conversion : Proof.context -> cterm (*to*) -> thm (*from*) -> thm
  val conversion_completely : Proof.context -> cterm (*to*) -> thm (*from*) -> thm
        (* solve all the premises by Nu_Resonser, raising CastFail if failed *)
  val cast : Proof.context -> cterm (*desired nu*) -> thm (*major*) -> thm
  val cast_completely : Proof.context -> cterm (*desired nu*) -> thm (*major*) -> thm
        (* solve all the premises by Nu_Resonser, raising CastFail if failed *)

  val apply : Proof.context -> thm list -> thm -> thm
  val apply_proc_naive : thm (*proc*) -> thm (*meta or major*) -> thm
  val accept_proc : thm -> Proof.context -> thm * Proof.context
  val set_param : Proof.context -> term -> thm -> thm
  val set_param_cmd : Proof.context -> string -> thm -> thm

  val start_proc : string (*blk name*) -> cterm -> Proof.context -> thm * Proof.context
  val rename_blk_var : string -> thm -> cterm (*renamed block*) * thm
        (* current old_name reulst in ...
        * ---------------------------------
        *  current new_name reulst in *)

  val auto_construct : Proof.context -> cterm -> thm -> thm

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

val aux_name = "that" and aux_name_raw = "\<nu>aux'raw"
fun hyp_export is_goal asms = (I,I)
val curr_const_attrs = [Thm.declaration_attribute (Named_Theorems.add_thm "NuSys.used")]
fun aux_facts ctx = Proof_Context.get_thms ctx aux_name
fun aux_facts_raw ctx = Proof_Context.get_thm ctx aux_name_raw


fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg'' th = Seq.make (fn () => (@{print} th; raise NDBG th))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty)))

(** Tactics **)
fun head_only tac th =
  if nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude
fun raw_auto ctx =
  ((Method.insert_tac ctx (Named_Theorems.get ctx "NuSys.used") 1)
    THEN Clasimp.auto_tac ctx)

(*** Premise tac ***)
val Premise_I = @{thm NuPrime.Premise_I}
fun mk_premise_tac withdraw ctx th =
  if AutoLevel.get ctx >= 2 andalso can (major_prem_of #> dest_Trueprop #> dest_premise_tag) th
  then (head_only (SOLVED' (K (HEADGOAL (resolve0_tac [Premise_I]) THEN raw_auto ctx)) 1)
      ORELSE withdraw) th
  else Seq.empty
val FailedPremise_I = @{thm FailedPremise_I} and FailedPremise_D = @{thm FailedPremise_D}
val withdrawable_premise_tac = mk_premise_tac (Seq.succeed o undisch o (fn x => FailedPremise_D RS x))
val dest_failed_premise_tag = dest_Trueprop #> dest_monop @{const_name "FailedPremise"}
val premise_tac = mk_premise_tac Seq.fail
fun fininsh_premise_hyps th =
  fold ((fn x => FailedPremise_I RS x) oo implies_intr)
    (chyps_of th |> filter (can (dest_failed_premise_tag o term_of))) th

(*** Different tag tac ***)
fun different_tag th =
  case try Thm.major_prem_of th
    of SOME prem =>
      (case try (dest_Trueprop #> dest_binop @{const_name "Different"}) prem
        of SOME (a,b) =>
          if Term.aconv (a,b) then Seq.empty else Seq.single (@{thm Different_I} RS th)
         | _ => Seq.empty)
     | _ => Seq.empty



(*** auto resolve tac ***)
fun SOLVED tac st =
  if Thm.nprems_of st = 0 then all_tac st
  else (tac st |> Seq.filter (fn st' => Thm.nprems_of st' < Thm.nprems_of st));
fun SOLVED_RULE rule fail th =
  if Thm.nprems_of th = 0 then th
  else (case rule th of SOME th' =>
          if Thm.nprems_of th' < Thm.nprems_of th then th'
          else fail th'
        | NONE => fail th)

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
fun cast ctx desired_nu sequent =
  let
    val cast  = Drule.infer_instantiate ctx [(("T'",0),desired_nu)] @{thm "cast"}
    val cast' = Drule.infer_instantiate ctx [(("T'",0),desired_nu)] @{thm "cast'"}
  in
    sequent RS cast' handle THM _ => sequent RS cast
  end
fun cast_completely ctx desired_nu major =
  cast ctx desired_nu major
    |> SOLVED_RULE (Nu_Reasoner.reason ctx) (fn th => raise CastFail th)

val conversion_thm = @{thm conversion}
fun conversion ctx to from =
  let
    val (f ,U ,V ) = dest_procedure_c (cconcl_of from) |> @{print}
    val (f',U',V') = dest_procedure_c to
    val (a,b) = dest_typroc_c (ctyp_of_cterm f) 
    val (c,d) = dest_typroc_c (ctyp_of_cterm f')
    val rule = Thm.instantiate
      ([((("'a",0),["NuPrime.lrep"]), a),
        ((("'b",0),["NuPrime.lrep"]), b),
        ((("'c",0),["NuPrime.lrep"]), c),
        ((("'d",0),["NuPrime.lrep"]), d)
       ],[
        ((("f",0),  typ_of_cterm f),  f),
        ((("U",0),  typ_of_cterm U),  U),
        ((("V",0),  typ_of_cterm V),  V),
        ((("f'",0), typ_of_cterm f'), f'),
        ((("U'",0), typ_of_cterm U'), U'),
        ((("V'",0), typ_of_cterm V'), V')])
      conversion_thm
  in
    from RSN (2,rule)
  end
fun conversion_completely ctx to from =
  conversion ctx to from
    |> Goal.protect 1
    |> SOLVED_RULE (Nu_Reasoner.reason ctx) (fn th => raise CastFail th)
    |> Goal.conclude

fun export_codeblock cb sequent =
  let
    val (s',_,_) = dest_codeblock_c cb
  in
    sequent
      |> Thm.implies_intr cb
      |> Thm.forall_intr s'
      |> (fn th => th COMP @{thm reassemble_proc})
      (* |> Thm.assumption NONE 1
      |> Seq.make_results |> Seq.the_result "export_codeblock" *)
  end

fun accept_proc sequent ctx =
  let
    val (f,s,_,_) = dest_PendingConstruction (Thm.prop_of sequent)
    val tyb = range_type (fastype_of f)
    val name = term_name s |> Variable.revert_fixed ctx
    val ([name],ctx) = Variable.add_fixes [name] ctx
    val s' = Free (name, tyb)
    val ctx = Variable.declare_constraints s' ctx
    val s' = Thm.cterm_of ctx s'
    val accept_proc_thm = Drule.infer_instantiate ctx [(("s'",0),s')] @{thm accept_proc}
    val sequent = sequent RS accept_proc_thm
    val assm = Thm.cprem_of sequent 1
    val ([cb],ctx) = Assumption.add_assms
          (fn _ => fn [cb] => (export_codeblock cb, I)) [assm] ctx
    val sequent = cb RS sequent
  in
    (sequent,ctx)
  end


fun apply ctx appliants major =
  NuApply.apply ctx appliants major
    |> Nu_Reasoner.reason_s ctx
    |> (fn x => case Seq.pull x
                  of SOME (th,_) => perhaps (try Goal.conclude) th
                   | NONE => raise THM ("fail to apply", 0, major::appliants))
val apply_proc_naive = NuApply.apply_proc_naive


fun param_type major =
  NuBasics.param_type major
    |> map_atyps (fn ty => case ty of TVar _ => dummyT | _ => ty)
  (* TODO: how to parse (check) the term of a desired type pattern? *)
fun set_param ctx term major =
  (term |> Type.constraint (param_type major)
            (* TODO: how to parse (check) the term of a desired type pattern? *)
        |> Syntax.check_term ctx |> Thm.cterm_of ctx |> NuBasics.intro_param)
    RS major
fun set_param_cmd ctx term major =
  case try (dest_funT #> apfst dest_named) (param_type major)
    of SOME (name_and_tys, rng) =>
        let
          val fixes = map (fn (name,ty) =>
                (Binding.name name, (if ty = dummyT then NONE else SOME ty), NoSyn)) name_and_tys
     |> @{print}
          val (fixed_names, ctx) = Proof_Context.add_fixes fixes ctx
          val term = Syntax.parse_term ctx term
                      |> tuple_abs (map fst name_and_tys ~~ map (rpair dummyT) fixed_names)
                      |> @{print}
                      |> mk_monop @{const_name case_named}
        in
          set_param ctx term major
        end
     | NONE => set_param ctx (Syntax.parse_term ctx term) major


fun finish_proc cc sequent =
  let
    val (s',H',_) = dest_CurrentConstruction_c cc
  in
    sequent
      |> Thm.implies_intr cc
      |> Thm.forall_intr H'
      |> Thm.forall_intr s'
      |> (fn th => th COMP @{thm reassemble_proc_final})
  end

fun start_proc blk_name arg_nuTy ctx =
  let
    val ty_a = (case typ_of_cterm arg_nuTy
                   of Type ("Set.set", [Type (@{type_name prod}, [_, ty])]) => ty
                    | _ => raise Fail "start_proc - argTy - not a set")
    val ([blk_name, H],ctx) = Variable.add_fixes [blk_name, "\<HH>"] ctx
    val stat_var = Free (blk_name, mk_stateT ty_a) 
    val ctx = Variable.declare_constraints stat_var ctx
    val init = Const(@{const_name CurrentConstruction},
                  fastype_of stat_var --> @{typ "heap set"} --> typ_of_cterm arg_nuTy --> boolT)
               $ stat_var $ Free (H, @{typ "heap set"})
    val init = Thm.apply @{cterm Trueprop} (Thm.apply (Thm.cterm_of ctx init) arg_nuTy)
    val ([init],ctx) = Assumption.add_assms
          (fn _ => fn [cc] => (finish_proc cc, I)) [init] ctx
  in
    (init,ctx)
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

fun rename_blk_var name meta =
  let
    val codeblock = current_codeblock meta
    val (s,_,_) = dest_codeblock_c codeblock
    val thy = Thm.theory_of_thm meta
    val s' = Thm.global_cterm_of thy (Free (name, typ_of_cterm s))
    val meta = meta |> implies_intr codeblock
                |> forall_intr s |> forall_elim s'
                (* |> forall_intr a |> forall_elim a' *)
  in
    (cprem_of meta 1, undisch meta)
  end


fun auto_construct ctx term sequent =
  let
    val sequent = @{thm AutoConstruct}
      |> Thm.instantiate ([((("'exp",0),["HOL.type"]),Thm.ctyp_of_cterm term)], [((("exp",0), Thm.typ_of_cterm term),term)])
      |> (fn th => sequent RS th)
      |> Goal.protect 1
      |> Nu_Reasoner.reason ctx
  in case sequent of SOME sequent =>
        if Thm.no_prems sequent
        then Goal.conclude sequent
        else raise TERM ("fail to construct", [Thm.term_of term])
      | NONE => raise TERM ("fail to construct", [Thm.term_of term])
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
      * "NuSys.used") stat) *)
  end
end
