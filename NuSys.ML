(* The Signature *)
signature NU_SYS = sig
  (** Tactics **)
  exception CastFail of thm
  exception ReasoningFail of thm
  type proc_conctx = {proc_const: cterm, binding: Binding.binding, goal: cterm}
  val raw_auto : Proof.context -> tactic
  val premise_tac : Proof.context -> tactic
  val auto_resolve : (thm list (*major*) * (thm list * thm list) option
        (* priority, minor*)) option ->
    thm list (*addtional major*) -> Proof.context -> tactic
  val auto_resolve_rule : (thm list (*major*) * (thm list * thm list) option (*minor*)) option ->
    thm list (*addtional major*) -> Proof.context -> thm -> thm
    (* raises ReasoningFail if none of premises is solved, but exits normally if
    * there is no premises in the theorem. *)


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
  val cast : Proof.context -> cterm (*desired nu*) -> thm (*major*) -> thm

  val apply : Proof.context -> thm list -> thm -> thm
  val apply_proc_naive : thm (*proc*) -> thm (*meta or major*) -> thm
  val accept_proc_naive : thm -> thm (* the version without auto *)
  val accept_proc : Proof.context -> thm -> thm
  val set_param : Proof.context -> term -> thm -> thm
  val set_param_cmd : Proof.context -> string -> thm -> thm

  val start_proc : Proof.context -> string (*blk name*) -> cterm -> thm (* see @{thm NuPrime.start_proc} *)
  val finish_proc : thm -> thm (* see @{thm NuPrime.finish_proc} *)
  val rename_blk_var : string -> thm -> cterm (*renamed block*) * thm
        (* current old_name reulst in ...
        * ---------------------------------
        *  current new_name reulst in *)

  (*
    `declare_facts` declares/addes ν-facts to be embedded in the specification theorem.
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
  val name_star_fact : Thm.binding -> thm -> Proof.context -> thm * Proof.context
  val delete_fact : string -> thm -> Proof.context -> thm * Proof.context
  (* declares all codeblock hypothesis *)
  val open_meta  : thm -> Proof.context -> Proof.context
  (* `load_specthm (ctx,specthm)` open the meta, and then 
    * puts all auxiliary facts into the context by the name `\<nu>aux` *)
  val load_specthm  : thm -> Proof.context -> Proof.context

  val auto_construct : Proof.context -> cterm -> thm -> thm
  val transfer_facts_data : Context.generic -> Context.generic -> Context.generic

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
type proc_conctx = {proc_const: cterm, binding: Binding.binding, goal: cterm}

structure NuFacts = Generic_Data
(
  (*key : name of the auxiliary fact, value: the attribute to be evaluated*)
  type T = (Position.T * attribute list) Symtab.table; 
  val empty: T = Symtab.empty
  val extend = I
  val merge : T * T -> T = Symtab.join (fn _ => fn _ => raise Symtab.SAME);
)
fun transfer_facts_data from = NuFacts.put (NuFacts.get from)

fun ap2_3 f (a,b,c) = (a,f b,c)
fun delete_fact name meta ctx =
  ctx |> Context.proof_map (NuFacts.map (Symtab.delete name))
    |> pair (elim_SPEC meta
        |> apsnd (elim_FactCollection
            #> ap2_3 (elim_AndFacts
              #> filter (fn th => name_of_Fact th <> name)
              #> intro_AndFacts)
            #> intro_FactCollection)
        |> intro_SPEC)
fun delete_fact_may name meta ctx =
  delete_fact name meta ctx handle Symtab.UNDEF _ => (meta,ctx)

fun get_aux_attrs ctx (name,auxth) =
  case the_default (Position.none,[]) (Symtab.lookup (NuFacts.get (Context.Proof ctx)) name)
    of (pos,attrs) =>
      ((Binding.make (name,pos), attrs), [(Conjunction.elim_conjunctions auxth,[])])
fun note_auxes auxes ctx =
  Proof_Context.note_thmss "\<nu>fact" (map (get_aux_attrs ctx) auxes) ctx
fun fold1 f (h::r) = fold f r h
  | fold1 f [] = raise Fail "fold1"
fun gen_declare_fact rule (binding,attrs) meta ctx =
  let
    val name = Binding.name_of binding
    val _ = if name = "\<glowing_star>" then error "reserved keyword: \<glowing_star>" else ()
    val (meta,ctx) = delete_fact_may name meta ctx
  in
  ctx |> Context.proof_map (NuFacts.map (Symtab.update_new (name, (Binding.pos_of binding, attrs))))
    |> pair (rule name meta)
  end
fun declare_fact (thmbind,auxes) = gen_declare_fact (fn name => fn meta =>
    (Thm.instantiate ([],[((("name",0), label_ty), mk_label_c name)])
      @{thm NuPrime.declare_fact})
    OF [fold1 Conjunction.intr auxes, meta]
  ) thmbind
fun declare_facts auxes meta ctx =
  fold (fn a => fn (th,ctx) => declare_fact a th ctx) auxes (meta,ctx)
fun name_star_fact binding = 
  gen_declare_fact (fn name => fn meta =>
    let
      val (target,_,_) = elim_SPEC meta |> #2 |> elim_FactCollection
    in
      meta RS (Thm.instantiate ([],[((("name",0), label_ty), mk_label_c name)])
          @{thm NuPrime.name_star_fact})
    end
  ) binding


val aux_name = "that" and aux_name_raw = "\<nu>aux'raw"
fun hyp_export is_goal asms = (I,I)
fun open_meta meta =
  Proof_Context.add_assms hyp_export (map (fn cb =>
    ((Binding.name (codeblock_name cb),[]),
        [(cb,[])])) (codeblocks_of meta)) #> #2
val curr_const_attrs = [Thm.declaration_attribute (Named_Theorems.add_thm "NuSys.used")]
fun load_specthm specthm ctx =
  let
    val (major,aux) = elim_SPEC specthm
    val auxes = user_facts_in_collection aux
    val (_,_,vcurrent) = elim_FactCollection aux
  in
    ctx |> open_meta specthm
      |> note_auxes auxes
      |-> (fn ths => Proof_Context.put_thms false (aux_name_raw, SOME (flat (map snd ths))))
      |> Proof_Context.note_thms "\<nu>current"
          ((Binding.name "\<nu>current", curr_const_attrs), [([vcurrent],[])]) |> #2
  end
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


(*** Simplify tag tac ***)
fun simp_tag_tac ctx th =
  case try (fn th => cprem_of th 1 |> dest_Trueprop_c |> dest_simplify_tag_c) th
    of SOME (_,y) => ((Simplifier.rewrite ctx y RS @{thm Simplify_I}) RS th) |> Seq.single
     | NONE => Seq.empty

(*** auto resolve tac ***)
fun SOLVED tac st =
  if Thm.nprems_of st = 0 then all_tac st
  else (tac st |> Seq.filter (fn st' => Thm.nprems_of st' < Thm.nprems_of st));
fun SOLVED_RULE rule fail th =
  if Thm.nprems_of th = 0 then th
  else let val th' = rule th
       in if Thm.nprems_of th' < Thm.nprems_of th then th'
          else fail th' end

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


fun auto_resolve thms addtion ctx  =
  let 
    val (thms,prio,minor_thms) =
      case thms of SOME (major, SOME (prio,minor)) => (major,prio,minor)
       | SOME (major, NONE) => (major,[],[])
       | NONE => (Named_Theorems.get ctx "NuPrime.\<nu>intro",
                  Named_Theorems.get ctx "NuPrime.\<nu>intro0",
                  Named_Theorems.get ctx "NuPrime.\<nu>intro'")
    val thms = addtion @ thms
    val lowest = Named_Theorems.get ctx "NuPrime.\<nu>intro''"
  in SOLVED (REPEATX (
      different_tag
        ORELSE simp_tag_tac ctx
        ORELSE print_dbg' (* TODO: support for debug printing *)
        APPEND (HEADGOAL (resolve_tac ctx prio))
        APPEND (HEADGOAL (resolve_tac ctx (@{print} thms)))
        APPEND (premise_tac ctx)
        APPEND resolve_tac ctx minor_thms 1
        APPEND resolve_tac ctx lowest 1
        ORELSE (fn th => Seq.make (fn () => (@{print} "END"; @{print} th; NONE)))
    )) (* #> Seq.map fininsh_premise_hyps *)
  end
val auto_resolve0 = auto_resolve NONE []


fun auto_resolve_rule' i major_minor addition ctx th =
  if Thm.nprems_of th = 0 then th else
  case Seq.pull (Goal.protect 1 th |> auto_resolve major_minor addition ctx)
    of SOME (th', _) =>
        Goal.conclude th' |> auto_resolve_rule' (i+1) major_minor addition ctx 
     | NONE => (if i = 0 then raise ReasoningFail th else th)
fun auto_resolve_rule major_minor addition ctx th =
  if can dest_SpecTop (prop_of th)
  then elim_SPEC th
    |> apfst (auto_resolve_rule' 0 major_minor addition ctx)
    |> intro_SPEC
  else auto_resolve_rule' 0 major_minor addition ctx th
val auto_resolve_rule0 = auto_resolve_rule NONE []



  (** Basic Operations **)
fun cast ctx desired_nu major =
  let
    val _ = term_of desired_nu |> dest_RepSet (*validates the argument*)
    val insts = ([((("'a",0),["NuPrime.lrep"]),
                        ctyp_of_cterm desired_nu |> dest_tynuset_c |> dest_ctyp1 
                                                    (*heap \<times> 'a*))],
                 [((("T'",0),typ_of_cterm desired_nu), desired_nu)])
  in
    (major RS Thm.instantiate insts @{thm "cast"})
      |> SOLVED_RULE (auto_resolve_rule0 ctx) (fn th => raise CastFail th)
  end

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
    (from RSN (2,rule))
      |> Goal.protect 1
      |> SOLVED_RULE (auto_resolve_rule0 ctx) (fn th => raise CastFail th)
      |> Goal.conclude
  end

fun accept_proc_naive meta =
  meta |> disch_current_codeblock
    |> mk_PropBlock 0 
    |> (fn x => x RS @{thm NuPrime.accept_proc} handle THM _ => x RS @{thm accept_proc'})
    |> (fn th => 
        let val thy = Thm.theory_of_thm th
          val (vname,vty) = prems_of th |> hd |> dest_codeblock |> #1 |> dest_Var
          val (name,_) = current_block_var meta |> dest_Free
        in Thm.instantiate ([],
            [((vname,vty), Thm.global_cterm_of thy (Free (name,vty)))]) th end)
    |> undisch
fun accept_proc ctx meta = 
  (if can (prop_of #> dest_SpecTop #> #1 #> dest_Trueprop #> dest_PendingConstruction) meta
  then meta else auto_resolve_rule0 ctx meta) |> accept_proc_naive

fun apply' ctx appliants major =
  NuApply.apply ctx appliants major
    |> Seq.maps (auto_resolve0 ctx)
    |> Seq.pull |> (fn x => 
        case x of SOME (th,_) => Goal.conclude th
                | NONE => raise THM ("fail to apply", 0, major::appliants))
fun apply ctx appliants = map_major (apply' ctx appliants)
val apply_proc_naive = NuApply.apply_proc_naive


fun param_type major =
  NuBasics.param_type major
    |> map_atyps (fn ty => case ty of TVar _ => dummyT | _ => ty)
  (* TODO: how to parse (check) the term of a desired type pattern? *)
fun set_param' ctx term major =
  (term |> Type.constraint (param_type major)
            (* TODO: how to parse (check) the term of a desired type pattern? *)
        |> Syntax.check_term ctx |> Thm.cterm_of ctx |> NuBasics.intro_param)
    RS major
fun set_param_cmd' ctx term major =
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
          set_param' ctx term major
        end
     | NONE => set_param' ctx (Syntax.parse_term ctx term) major

fun set_param ctx term = map_major (set_param' ctx term)
fun set_param_cmd ctx term = map_major (set_param_cmd' ctx term)


fun start_proc ctx blk_name arg_nuTy =
  let
    val argTy = (case typ_of_cterm arg_nuTy of Type ("Set.set", [Type (@{type_name prod}, [_, ty])]) => ty
                   | _ => raise Fail "start_proc - argTy - not a set")
    val stat_var = Free (blk_name, mk_stateT argTy) |> cterm_of ctx
    val arg_var = Free (blk_name^"_arg", HOLogic.mk_prodT(@{typ heap}, argTy)) |> cterm_of ctx
    val init_thm = Drule.instantiate'_normalize [SOME (ctyp_of ctx argTy)]
                      [SOME stat_var, SOME arg_var, SOME arg_nuTy] @{thm start_proc}
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

fun finish_proc th =
  let
    val codeblock = current_codeblock th
    val (s,a,_,_) = dest_codeblock_c codeblock
  in
    th |> implies_intr codeblock
       |> forall_intr s |> forall_intr a
       |> (fn x => x COMP @{thm NuPrime.finish_proc})
       |> @{print}
  end

fun rename_blk_var name meta =
  let
    val codeblock = current_codeblock meta
    val (s,_,_,_) = dest_codeblock_c codeblock
    val thy = Thm.theory_of_thm meta
    val s' = Thm.global_cterm_of thy (Free (name, typ_of_cterm s))
    val meta = meta |> implies_intr codeblock |> forall_intr s |> forall_elim s'
  in
    (cprem_of meta 1, undisch meta)
  end


fun auto_construct ctx term meta =
  let
    val (major,aux) = elim_SPEC meta
    val next = @{thm AutoConstruct}
      |> Thm.instantiate ([((("'exp",0),["HOL.type"]),Thm.ctyp_of_cterm term)], [((("exp",0), Thm.typ_of_cterm term),term)])
      |> (fn th => major RS th)
      |> Goal.protect 1 |> auto_resolve NONE [] ctx
  in case Seq.pull next
    of SOME (next, _) => Goal.conclude next |> rpair aux |> intro_SPEC
      | _ => raise TERM ("fail to construct", [Thm.term_of term])
  end


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
      (* |> apsnd (fn stat => using_facts (Named_Theorems.get (context_of stat)
      * "NuSys.used") stat) *)
  end
end
