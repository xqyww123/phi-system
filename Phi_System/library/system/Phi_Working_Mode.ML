signature PHI_WORKING_MODE = sig

type working_mode = {
  name: string,
  domain: Proof.context -> term -> bool,
  spec_of  :  term (*on-going construction assertion*) ->  term (*the BI assertion*),
  spec_of_c: cterm (*on-going construction assertion*) -> cterm,
  source_spec: term (*goal*) -> term,
  source_spec_c: cterm (*goal*) -> cterm,
(*  target_spec:   term (*proposition of a goal*) -> term option,
  target_spec_c: Proof.context -> cterm (*proposition of a goal*) -> cterm option,
  exception_spec  : term (*proposition of a goal*) -> term option,
  exception_spec_c: Proof.context -> cterm (*proposition of a goal*) -> cterm option, *)
  initial_sequent: cterm (*initial BI assertion*) -> Proof.context -> Proof.context * thm,
(*  block_name_of: term -> string, *)
  inhabited_rule: thm,
  transformation_rule : thm,
  view_shift_rule: thm option,
  cast: cterm (*desired*) -> Proof.context * thm (*sequent*) -> Proof.context * thm,
  cast_exception: cterm (*desired*) -> Proof.context * thm -> Proof.context * thm,
  vcg_before_assembling: cterm (*goal*) -> Proof.context * thm -> Proof.context * thm,
  introduce_existence: (string * typ) list -> Proof.context * thm -> Proof.context * thm,
  introduce_existence_in_assembling:
      (string * typ) list -> Proof.context * thm -> Proof.context * thm
}
(*
cast operation: transform to the desired assertion.
If successful, it results in \<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n P \<Longrightarrow> Result\<close>
which always has a leading obligation P no matter whether it is trivially true.
cast exception is the version for casting an exception assertion.
*)

val working_mode_on  : Proof.context -> term -> working_mode option
val working_mode_on1 : Proof.context -> term -> working_mode
val procedure : working_mode
val view_shift : working_mode
val implication : working_mode

val set  : working_mode -> Proof.context -> Proof.context
val mode : Proof.context -> working_mode

val cast : cterm -> Proof.context * thm -> Proof.context * thm
val cast_exception : cterm -> Proof.context * thm -> Proof.context * thm

end

structure Phi_Working_Mode : PHI_WORKING_MODE = struct

type working_mode = {
  name: string,
  domain: Proof.context -> term -> bool,
  spec_of  :  term (*on-going construction assertion*) ->  term,
  spec_of_c: cterm (*on-going construction assertion*) -> cterm,
  source_spec: term (*goal*) -> term,
  source_spec_c: cterm (*goal*) -> cterm,
(*  target_spec: term (*term of the state sequent*) -> term option,
  target_spec_c: Proof.context -> cterm (*term of the state sequent*) -> cterm option,
  exception_spec  : term (*proposition of a goal*) -> term option,
  exception_spec_c: Proof.context -> cterm (*proposition of a goal*) -> cterm option, *)
  inhabited_rule: thm,
  initial_sequent: cterm (*goal*) -> Proof.context -> Proof.context * thm,
  transformation_rule : thm,
  view_shift_rule: thm option,
  cast: cterm -> Proof.context * thm -> Proof.context * thm,
  cast_exception: cterm (*desired*) -> Proof.context * thm -> Proof.context * thm,
  vcg_before_assembling: cterm (*goal*) -> Proof.context * thm -> Proof.context * thm,
  introduce_existence: (string * typ) list -> Proof.context * thm -> Proof.context * thm,
  introduce_existence_in_assembling:
      (string * typ) list -> Proof.context * thm -> Proof.context * thm
}

structure Data = Generic_Data(
  type T = working_mode Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun working_mode_on ctxt goal =
      Symtab.get_first (fn (_,mode) => if #domain mode ctxt goal then SOME mode else NONE)
        (Data.get (Context.Proof ctxt))

fun working_mode_on1 ctxt goal =
      case working_mode_on ctxt goal of SOME x => x
         | NONE => error ("Do not know how to handle goal\n" ^ Syntax.string_of_term ctxt goal)

(* Set / Get Mode *)

structure Mode = Proof_Data(
  type T = working_mode option
  val init = K NONE
)

val set = Mode.put o SOME
fun mode ctxt = case Mode.get ctxt
                  of SOME x => x
                   | NONE => error ("No working mode has been set in this context.")
  

(* Auxiliaries *)

fun generic_cast rule place desired_nu (ctxt,sequent) =
  let
    val _ = Phi_Reasoner.debug_info ctxt (fn _ => "reasoning cast..." ^ Position.here \<^here>)
    val (ctxt', sequent') =
          case Phi_Reasoner.reason NONE (ctxt, sequent RS rule)
            of SOME ret => ret
             | NONE => raise Phi_Error.CastFail (place, desired_nu, sequent)
    val _ = case Thm.prop_of sequent'
              of (\<^const>\<open>Trueprop\<close> $ _) => ()
               | (\<^const>\<open>Pure.imp\<close>
                    $ (\<^const>\<open>Trueprop\<close> $ (\<^term>\<open>Proof_Obligation\<close> $ _))
                    $ (\<^const>\<open>Trueprop\<close> $ _)) => ()
               | _ => raise Phi_Error.CastFail (place, desired_nu, sequent)
  in (ctxt',sequent') end

fun cannot_cast_exception sequent =
  raise THM("cannot cast the exception of the sequent", 0, [sequent])

fun bad_sequent sequent =
  raise THM("Unrecognizable form of sequent.", 0, [sequent])

fun collect vs tm = Term.fold_aterms (fn Free v =>
                    if member (op =) vs v then insert (op =) v else I | _ => I) tm []

fun introduce_ex_ToA extract rule xs (ctxt, sequent) =
  let
    fun generalize x sequent =
      case Phi_Syntax.dest_ToA_Construction (Thm.concl_of sequent) of (_, S)
            => sequent RS Drule.infer_instantiate ctxt
                              [(("S",0), Thm.cterm_of ctxt (absfree x (extract S)))] rule
  in fold_rev generalize xs sequent |> pair ctxt
  end

fun introduce_existence_cc extract rule xs (ctxt,sequent) =
  if can Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)
  then let
      fun generalize x sequent =
        case Phi_Syntax.dest_PendingConstruction (Thm.concl_of sequent) of (_,_,_,_,E)
              => sequent RS Drule.infer_instantiate ctxt
                                    [(("S",0), Thm.cterm_of ctxt (absfree x (extract E)))] rule
      in fold_rev generalize xs sequent |> pair ctxt
      end
  else if can Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent)
  then let
      val (_,_,_,Q,E) = Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent)
      val bad_Q = collect xs Q
      val bad_E = collect xs E
      val rule_Q = @{thm introduce_Ex_pending}
      val rule_E = @{thm introduce_Ex_pending_E}
      fun generalize_Q x sequent =
        case Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent) of (_,_,_,Q,_)
          => sequent RS
               Drule.infer_instantiate ctxt [(("Q",0), Thm.cterm_of ctxt (absfree x Q))] rule_Q
      fun generalize_E x sequent =
        case Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent) of (_,_,_,_,E)
          => sequent RS
               Drule.infer_instantiate ctxt [(("E",0), Thm.cterm_of ctxt (absfree x E))] rule_E
      in fold_rev generalize_E bad_E (fold_rev generalize_Q bad_Q sequent) |> pair ctxt
      end
  else bad_sequent sequent

fun cast desired (ctxt,sequent) =
  let
    val mode = mode ctxt
  in
    #cast mode desired (ctxt,sequent)
  end

fun cast_exception desired (ctxt,sequent) =
  let
    val mode = mode ctxt
  in
    #cast_exception mode desired (ctxt,sequent)
  end

fun vcg_by_cast destination (ctxt,sequent) = (
      Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.block [
        Pretty.str "casting to the destined post-condition ",
        Syntax.pretty_term ctxt (Thm.term_of destination),
        Pretty.block (Pretty.here \<^here>)
      ]);
      cast destination (ctxt,sequent)
)

(* Working Modes *)

(** Procedure Mode **)    


local

fun finish_proc hyp (_,sequent) =
  let open Phi_Syntax
    val (_,s',H',_) = dest_CurrentConstruction_c hyp
  in
    sequent
      |> Thm.implies_intr hyp
      |> Thm.forall_intr H'
      |> Thm.forall_intr s'
      |> (fn th => th COMP @{thm \<phi>reassemble_proc_final})
  end

fun start_proc arg ctxt =
  let open Phi_Syntax
    val ([blk_name, RR],ctxt) = Variable.add_fixes ["\<SS>", "\<RR>"] ctxt
    val stat_var = Free (blk_name, \<^typ>\<open>resource\<close>)
    val ctxt = Variable.declare_constraints stat_var ctxt
    val init = Const(\<^const_name>\<open>CurrentConstruction\<close>,
                      \<^typ>\<open>mode\<close>
                  --> fastype_of stat_var
                  --> dummyT
                  --> Thm.typ_of_cterm arg
                  --> \<^typ>\<open>bool\<close>)
               $ \<^const>\<open>programming_mode\<close>
               $ stat_var
               $ Free (RR, dummyT)
    val init = Thm.cterm_of ctxt (Syntax.check_term ctxt init)
    val init = Thm.apply @{cterm Trueprop} (Thm.apply init arg)
    val ([init],ctxt) = Assumption.add_assms
          (fn _ => fn [hyp] => (finish_proc hyp o pair ctxt, I)) [init] ctxt
  in
    (ctxt,init)
  end

fun cast desired (ctxt, sequent) =
  let
    val idx = 1 + Thm.maxidx_of_cterm desired
    val rule =
     (if can (Phi_Syntax.dest_CurrentConstruction) (Thm.concl_of sequent)
      then @{thm "_\<phi>cast_internal_rule_"}
      else @{thm "_\<phi>cast_internal_rule_'"})
        |> Thm.incr_indexes idx
        |> Drule.infer_instantiate ctxt [(("T'",idx),desired)]
  in generic_cast rule "post-condition of the sequent" desired (ctxt, sequent)
  end

fun cast_exception desired (ctxt, sequent) =
  let
    val idx = 1 + Thm.maxidx_of_cterm desired
    val rule =
     (if can (Phi_Syntax.dest_PendingConstruction) (Thm.concl_of sequent)
      then @{thm "_\<phi>cast_exception_rule_"}
      else cannot_cast_exception sequent)
        |> Thm.incr_indexes idx
        |> Drule.infer_instantiate ctxt [(("E'",idx),desired)]
  in generic_cast rule "post-condition of the sequent" desired (ctxt, sequent)
  end

fun vcg_before_assembling goal (ctxt,sequent) =
  let
    val sequent' =
      if can Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)
      then let
        val (ins,current_nu) =
              #4 (Phi_Syntax.dest_CurrentConstruction_c (Thm.cprop_of sequent))
                 |> Thm.term_of
                 |> Procedure_Syntax.abstract_return_vals "\<r>\<e>\<t>"
                              (TVar (("ret", Thm.maxidx_of sequent), \<^sort>\<open>VALs\<close>)) true
                 |> apply2 (Thm.cterm_of ctxt)
        val idx_delt = 1 + Int.max (Thm.maxidx_of_cterm ins, Thm.maxidx_of_cterm current_nu)
        val return_rule = @{thm \<phi>return}
                       |> Thm.incr_indexes idx_delt
                       |> Drule.infer_instantiate ctxt
                              [(("T",idx_delt),current_nu),(("ret",idx_delt),ins)]
        in (sequent RS return_rule)
            |> rule_by_tactic ctxt
                  (SOLVED' (Simplifier.simp_tac ctxt) 1)
        end
      else sequent
    val desired_nu = #3 (Phi_Syntax.dest_procedure_c goal)
    val desired_arg_T = Thm.typ_of_cterm desired_nu |> Term.domain_type
                          |> Phi_Syntax.dest_sem_value_T
    val current_phi = #4 (Phi_Syntax.dest_PendingConstruction_c (Thm.cprop_of sequent'))
    val current_arg_T = Thm.typ_of_cterm current_phi |> Term.domain_type
                          |> Phi_Syntax.dest_sem_value_T
    val sequent'' = if can (Pattern.unify_types (Context.Proof ctxt)
                                                (current_arg_T, desired_arg_T)) Envir.init
                    then sequent'
                    else if can (Pattern.unify_types (Context.Proof ctxt)
                              (HOLogic.mk_prodT (current_arg_T, @{typ unit}), desired_arg_T))
                              Envir.init
                    then sequent' RS @{thm "\<phi>return_additional_unit"}
                    else error ("Current block expects returning "^
                            Syntax.string_of_typ ctxt desired_arg_T^
                            " but it actually returns "^
                            Syntax.string_of_typ ctxt current_arg_T)
  in (ctxt,sequent'')
  |> vcg_by_cast desired_nu
  end

in

val procedure : working_mode = 
  {
    name = "procedure",
    domain = (fn _ => fn tm =>
               can Phi_Syntax.dest_procedure tm
        orelse Phi_Syntax.is_construction_mode \<^const>\<open>programming_mode\<close> tm
        orelse can Phi_Syntax.dest_PendingConstruction tm
    ),
    spec_of   = #4 o Phi_Syntax.dest_CurrentConstruction,
    spec_of_c = #4 o Phi_Syntax.dest_CurrentConstruction_c,
    source_spec   = #2 o Phi_Syntax.dest_procedure,
    source_spec_c = #2 o Phi_Syntax.dest_procedure_c,
(*    target_spec = SOME o target_spec,
    target_spec_c = SOME oo target_spec_c,
    exception_spec = exception_spec,
    exception_spec_c = exception_spec_c, *)
    inhabited_rule = @{thm CurrentConstruction_Inhabited_rule},
    initial_sequent = start_proc,
    transformation_rule  = @{thm \<phi>apply_implication},
    view_shift_rule = SOME @{thm \<phi>apply_view_shift},
    cast = cast,
    cast_exception = cast_exception,
    vcg_before_assembling = vcg_before_assembling,
    introduce_existence = introduce_existence_cc I @{thm introduce_Ex},
    introduce_existence_in_assembling = introduce_existence_cc I @{thm introduce_Ex}
}
end


(** View Shift **)


val view_shift : working_mode = 
let
  fun target_spec term =
    let
      val (_,T,P) = Phi_Syntax.dest_view_shift term
    in
      Const (\<^const_name>\<open>Subjection\<close>, fastype_of T --> \<^typ>\<open>bool\<close> --> fastype_of T) $ T $ P
    end
  (*TODO: optimize this*)
  fun target_spec_c ctxt = Thm.term_of #> target_spec #> Thm.cterm_of ctxt

  fun finish_view_shift hyp (_,sequent) =
    let open Phi_Syntax
      val (_,s',H',_) = dest_CurrentConstruction_c hyp
    in
      sequent
        |> Thm.implies_intr hyp
        |> Thm.forall_intr H'
        |> Thm.forall_intr s'
        |> (fn th => th COMP @{thm \<phi>make_view_shift})
    end

  fun start_view_shift arg ctxt =
    let open Phi_Syntax
      val ([blk_name, RR],ctxt) = Variable.add_fixes ["\<VV>", "\<RR>"] ctxt
      val stat_var = Free (blk_name, \<^typ>\<open>resource\<close>)
      val ctxt = Variable.declare_constraints stat_var ctxt
      val init = Const(\<^const_name>\<open>CurrentConstruction\<close>,
                        \<^typ>\<open>mode\<close>
                    --> fastype_of stat_var
                    --> dummyT
                    --> Thm.typ_of_cterm arg
                    --> \<^typ>\<open>bool\<close>)
                 $ \<^const>\<open>view_shift_mode\<close>
                 $ stat_var
                 $ Free (RR, dummyT)
      val init = Thm.cterm_of ctxt (Syntax.check_term ctxt init)
      val init = Thm.apply @{cterm Trueprop} (Thm.apply init arg)
      val ([init],ctxt) = Assumption.add_assms
            (fn _ => fn [hyp] => (finish_view_shift hyp o pair ctxt, I)) [init] ctxt
    in
      (ctxt,init)
    end
in
{
    name = "view shift",
    domain = (fn _ => fn x => can Phi_Syntax.dest_view_shift x
                       orelse Phi_Syntax.is_construction_mode \<^const>\<open>view_shift_mode\<close> x),
    spec_of   = #4 o Phi_Syntax.dest_CurrentConstruction,
    spec_of_c = #4 o Phi_Syntax.dest_CurrentConstruction_c,
    source_spec   = #1 o Phi_Syntax.dest_view_shift,
    source_spec_c = #1 o Phi_Syntax.dest_view_shift_c,
(*    target_spec = SOME o target_spec,
    target_spec_c = SOME oo target_spec_c,
    exception_spec = K NONE,
    exception_spec_c = K (K NONE), *)
    inhabited_rule = @{thm CurrentConstruction_Inhabited_rule},
    initial_sequent = start_view_shift,
    transformation_rule  = @{thm \<phi>apply_implication},
    view_shift_rule = SOME @{thm \<phi>apply_view_shift},
    cast = (fn desired => fn (ctxt, sequent) =>
      let
        val idx = 1 + Thm.maxidx_of_cterm desired
        val rule = @{thm "_\<phi>cast_internal_rule_"}
          |> Thm.incr_indexes idx
          |> Drule.infer_instantiate ctxt [(("T'",idx),desired)]
      in
        generic_cast rule "sequent" desired (ctxt, sequent)
      end
    ),
    cast_exception = K (cannot_cast_exception o snd),
    vcg_before_assembling = (fn goal => fn (ctxt,sequent) =>
        vcg_by_cast (target_spec_c ctxt goal) (ctxt,sequent)),
    introduce_existence = introduce_existence_cc I @{thm introduce_Ex},
    introduce_existence_in_assembling =
      introduce_existence_cc (fn (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) => X
                               | _ => error ("bad form of the finalizing sequent"))
                             @{thm introduce_Ex_subj}
}
end

(** Implication **)


val implication : working_mode =
let
  fun target_spec term =
    let
      val (_,T,P) = Phi_Syntax.dest_implication term
    in
      Const (\<^const_name>\<open>Subjection\<close>, fastype_of T --> \<^typ>\<open>bool\<close> --> fastype_of T) $ T $ P
    end
  (*TODO: optimize this*)
  fun target_spec_c ctxt = Thm.term_of #> target_spec #> Thm.cterm_of ctxt

  fun finish_implication hyp (_,sequent) =
    let val (s,_) = Phi_Syntax.dest_ToA_Construction_c hyp
    in sequent
        |> Thm.implies_intr hyp
        |> Thm.forall_intr s
        |> (fn th => th COMP @{thm \<phi>make_implication})
    end
  
  fun start_implication arg ctxt =
    let open Phi_Syntax
      val ([blk_name],ctxt) = Variable.add_fixes ["\<CC>"] ctxt
      val Type (\<^type_name>\<open>set\<close>, [T]) = Thm.typ_of_cterm arg
      val stat_var = Free (blk_name, T)
      val ctxt = Variable.declare_constraints stat_var ctxt
      val init = Const(\<^const_name>\<open>ToA_Construction\<close>, dummyT) $ stat_var
      val init = Thm.cterm_of ctxt (Syntax.check_term ctxt init)
      val init = Thm.apply @{cterm Trueprop} (Thm.apply init arg)
      val ([init],ctxt) = Assumption.add_assms
            (fn _ => fn [hyp] => (finish_implication hyp o pair ctxt, I)) [init] ctxt
    in
      (ctxt,init)
    end
in
{
    name = "implication",
    domain = (fn _ => fn x => can Phi_Syntax.dest_implication x
                       orelse can Phi_Syntax.dest_ToA_Construction  x),
    spec_of   = #2 o Phi_Syntax.dest_ToA_Construction,
    spec_of_c = #2 o Phi_Syntax.dest_ToA_Construction_c,
    source_spec   = #1 o Phi_Syntax.dest_implication,
    source_spec_c = #1 o Phi_Syntax.dest_implication_c,
    inhabited_rule = @{thm ToA_Construction_Inhabited_rule},
    initial_sequent = start_implication,
    transformation_rule  = @{thm \<phi>apply_implication_impl},
    view_shift_rule = NONE,
    cast = (fn desired => fn (ctxt,sequent) =>
      let
        val idx = 1 + Thm.maxidx_of_cterm desired
        val rule = @{thm "_\<phi>cast_implication_"}
          |> Thm.incr_indexes idx
          |> Drule.infer_instantiate ctxt [(("T",idx),desired)]
      in
        generic_cast rule "sequent" desired (ctxt, sequent)
      end
    ),
    cast_exception = K (cannot_cast_exception o snd),
    vcg_before_assembling = (fn goal => fn (ctxt,sequent) =>
        vcg_by_cast (target_spec_c ctxt goal) (ctxt,sequent)),
    introduce_existence = introduce_ex_ToA I @{thm introduce_Ex_ToA},
    introduce_existence_in_assembling =
        introduce_ex_ToA (fn (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) => X
                           | _ => error ("bad form of the finalizing sequent"))
                         @{thm introduce_Ex_ToA_subj}
}
end


(*
local

val dest_SemType = Phi_Syntax.dest_tags #> Phi_Help.dest_binop \<^const_name>\<open>\<phi>SemType\<close>

in

val SemType = {
    name = "\<phi>SemType",
    domain = (fn _ => fn x => can dest_SemType x),
    spec_of   = #2 o Phi_Syntax.dest_ToA_Construction,
    spec_of_c = #2 o Phi_Syntax.dest_ToA_Construction_c,
    target_spec = K NONE,
    target_spec_c = K (K NONE),
    source_spec = source_spec,
(*    exception_spec = K NONE,
    exception_spec_c = K (K NONE), *)
    inhabited_rule = @{thm ToA_Construction_Inhabited_rule},
    initial_sequent = start_implication,
    block_name_of = (K "\<chi>"),
    transformation_rule  = @{thm \<phi>apply_implication_impl},
    view_shift_rule = NONE,
    cast = (fn desired => fn (ctxt,sequent) =>
      let
        val idx = 1 + Thm.maxidx_of_cterm desired
        val rule = @{thm "_\<phi>cast_implication_"}
          |> Thm.incr_indexes idx
          |> Drule.infer_instantiate ctxt [(("T",idx),desired)]
      in
        generic_cast rule "sequent" desired (ctxt, sequent)
      end
    ),
    cast_exception = K (cannot_cast_exception o snd),
    vcg_before_assembling = (K I),
    introduce_existence = introduce_ex_ToA I @{thm introduce_Ex_ToA},
    introduce_existence_in_assembling =
        introduce_ex_ToA (fn (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) => X
                           | _ => error ("bad form of the finalizing sequent"))
                         @{thm introduce_Ex_ToA_subj}
}

end
*)


val _ = Theory.setup (Context.theory_map
            (Data.map (Symtab.update_new ("procedure",   procedure)
                    #> Symtab.update_new ("view_shift",  view_shift)
                    #> Symtab.update_new ("implication", implication)
)))


end
