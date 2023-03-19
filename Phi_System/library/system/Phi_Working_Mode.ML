signature PHI_WORKING_MODE = sig

type working_mode = {
  name: string,
  domain: term -> bool,
  is_on_going_construction: term -> bool,
  spec_of  :  term (*on-going construction assertion*) ->  term (*the BI assertion*),
  spec_of_c: cterm (*on-going construction assertion*) -> cterm,
  initialize_sequent: Proof.state -> thm * Proof.state,
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
If successful, it results in \<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> P \<Longrightarrow> Result\<close>
which always has a leading obligation P no matter whether it is trivially true.
cast exception is the version for casting an exception assertion.
*)

val procedure : working_mode
val view_shift : working_mode
val implication : working_mode

val initialize_sequent_procedure : cterm (*argument*) -> Proof.context -> Proof.context * thm

val register :  working_mode list -> Context.generic -> Context.generic
val get_by_name  : Context.generic -> string -> working_mode option
val get_by_name1 : Context.generic -> string -> working_mode
val set  : working_mode -> Proof.context -> Proof.context
val mode  : Proof.context -> working_mode option
val mode1 : Proof.context -> working_mode
val mode_of  : Context.generic -> term -> working_mode option
val mode_of1 : Context.generic -> term -> working_mode

val cast : cterm -> Proof.context * thm -> Proof.context * thm
val cast_exception : cterm -> Proof.context * thm -> Proof.context * thm

val infer_working_mode_of_sequent : context_state -> working_mode * context_state

end

structure Phi_Working_Mode : PHI_WORKING_MODE = struct

type working_mode = {
  name: string,
  domain: term -> bool,
  is_on_going_construction: term -> bool,
  spec_of  :  term (*on-going construction assertion*) ->  term,
  spec_of_c: cterm (*on-going construction assertion*) -> cterm,
  inhabited_rule: thm,
  initialize_sequent: Proof.state -> thm * Proof.state,
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

val get_by_name = Symtab.lookup o Data.get
fun get_by_name1 ctxt name =
  case get_by_name ctxt name
    of SOME X => X
     | NONE => error ("No such registered mode: "^name)

fun mode_of ctxt term =
  Symtab.get_first (fn (_,m) => if #domain m term then SOME m else NONE)
                   (Data.get ctxt)

fun mode_of1 ctxt term =
  case mode_of ctxt term
    of SOME ret => ret
     | NONE => raise TERM ("No mode scopes term", [term])

fun register wms = Data.map (fold (fn wm => Symtab.update_new (#name wm, wm)) wms)

(* Set / Get Mode *)

structure Mode = Proof_Data(
  type T = working_mode option
  val init = K NONE
)

val set = Mode.put o SOME

val mode = Mode.get
fun mode1 ctxt = case Mode.get ctxt
                   of SOME x => x
                    | NONE => error ("No working mode has been set in this context.")


(** Auxiliaries **)

fun generic_initialize_sequent gen s =
  case Facts.lookup (Context.Proof (Proof.context_of s))
                    (Proof_Context.facts_of (Proof.context_of s)) "local.\<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l>"
    of SOME {thms=[X], dynamic=false} => (Thm.transfer' (Proof.context_of s) X, s)
     | _ => gen s

val default_initialize_sequent = generic_initialize_sequent (fn _ => error "BUG #q23c5nu9[")

(* Cast *)

fun generic_cast rule place desired_nu (ctxt,sequent) =
  let
    val _ = Phi_Reasoner.info_print ctxt 2 (fn _ => "reasoning cast..." ^ Position.here \<^here>)
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

fun introduce_ex_ToA extract rule0 xs (ctxt, sequent) =
  let
    val idx = Thm.maxidx_of sequent + 1
    val rule = Thm.incr_indexes idx rule0
    fun generalize x sequent =
      case Phi_Syntax.dest_ToA_Construction (Thm.concl_of sequent) of (_, S)
            => sequent RS Drule.infer_instantiate ctxt
                              [(("S",idx), Thm.cterm_of ctxt (absfree x (extract S)))] rule
  in fold_rev generalize xs sequent |> pair ctxt
  end

fun introduce_existence_cc extract rule0 xs (ctxt,sequent) =
  if can Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)
  then let
      val idx = Thm.maxidx_of sequent + 1
      val rule = Thm.incr_indexes idx rule0
      fun generalize x sequent =
        case Phi_Syntax.dest_PendingConstruction (Thm.concl_of sequent) of (_,_,_,_,E)
              => sequent RS Drule.infer_instantiate ctxt
                                    [(("S",idx), Thm.cterm_of ctxt (absfree x (extract E)))] rule
      in fold_rev generalize xs sequent |> pair ctxt
      end
  else if can Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent)
  then let
      val (_,_,_,Q,E) = Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent)
      val bad_Q = collect xs Q
      val bad_E = collect xs E
      val idx = Thm.maxidx_of sequent + 1
      val rule_Q = Thm.incr_indexes idx @{thm introduce_Ex_pending}
      val rule_E = Thm.incr_indexes idx @{thm introduce_Ex_pending_E}
      fun generalize_Q x sequent =
        case Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent) of (_,_,_,Q,_)
          => sequent RS
               Drule.infer_instantiate ctxt [(("Q",idx), Thm.cterm_of ctxt (absfree x Q))] rule_Q
      fun generalize_E x sequent =
        case Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent) of (_,_,_,_,E)
          => sequent RS
               Drule.infer_instantiate ctxt [(("E",idx), Thm.cterm_of ctxt (absfree x E))] rule_E
      in fold_rev generalize_E bad_E (fold_rev generalize_Q bad_Q sequent) |> pair ctxt
      end
  else bad_sequent sequent

fun cast desired (ctxt,sequent) =
      #cast (mode_of1 (Context.Proof ctxt) (Thm.concl_of sequent)) desired (ctxt,sequent)

fun cast_exception desired (ctxt,sequent) =
      #cast_exception (mode_of1 (Context.Proof ctxt) (Thm.concl_of sequent)) desired (ctxt,sequent)

fun vcg_by_cast destination (ctxt,sequent) = (
      Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.block [
        Pretty.str "casting to the destined post-condition ",
        Syntax.pretty_term ctxt (Thm.term_of destination),
        Pretty.block (Pretty.here \<^here>)
      ]);
      cast destination (ctxt,sequent)
)

(* Working Modes *)

(** Procedure Mode **)


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

structure Nested_Proc_Idx = Proof_Data (
  type T = int
  val init = K 0
)

fun initialize_sequent_procedure arg ctxt =
  let open Phi_Syntax
    val idx = string_of_int (Nested_Proc_Idx.get ctxt)
    val ([blk_name, RR],ctxt) = Variable.add_fixes ["\<SS>"^idx, "\<RR>"^idx] ctxt
                             |> apsnd (Nested_Proc_Idx.map (fn i => i + 1))
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

local

fun cast desired (ctxt, sequent) =
  let
    val idx = 1 + Thm.maxidx_of_cterm desired
    val concl = Thm.concl_of sequent
    val rule =
     (if can (Phi_Syntax.dest_CurrentConstruction) concl
      then @{thm "_\<phi>cast_internal_rule_"}
      else if can (Phi_Syntax.dest_PendingConstruction) concl
      then @{thm "_\<phi>cast_internal_rule_'"}
      else if can (Phi_Syntax.dest_procedure) concl
      then @{thm "_\<phi>cast_proc_return_internal_rule_"}
      else raise THM ("Don't know how to apply transformation on the sequent", 0, [sequent]))
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
                 |> Procedure_Syntax.package_values "\<r>\<e>\<t>"
                              (TVar (("ret", Thm.maxidx_of sequent), \<^sort>\<open>type\<close>)) true NONE
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
    val desired_nu = #4 (Phi_Syntax.dest_PendingConstruction_c goal)
    val desired_arg_T = Thm.typ_of_cterm desired_nu |> Term.domain_type
                          |> Phi_Syntax.dest_sem_value_T
    val idx = Term.maxidx_of_typ desired_arg_T + 1
    val current_phi = #4 (Phi_Syntax.dest_PendingConstruction_c (Thm.cprop_of sequent'))
    fun incr_idx_T d = Term.map_type_tvar (fn ((N,i),S) => TVar ((N,d+i),S))
    val current_arg_T = Thm.typ_of_cterm current_phi |> Term.domain_type
                          |> Phi_Syntax.dest_sem_value_T
                          |> incr_idx_T idx
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
    name = \<^const_name>\<open>working_mode_procedure\<close>,
    domain = (fn tm => Phi_Syntax.is_construction_mode \<^const>\<open>programming_mode\<close> tm orelse
                       can Phi_Syntax.dest_procedure tm),
    is_on_going_construction = can Phi_Syntax.dest_CurrentConstruction,
    spec_of   = #4 o Phi_Syntax.dest_CurrentConstruction,
    spec_of_c = #4 o Phi_Syntax.dest_CurrentConstruction_c,
(*    target_spec = SOME o target_spec,
    target_spec_c = SOME oo target_spec_c,
    exception_spec = exception_spec,
    exception_spec_c = exception_spec_c, *)
    inhabited_rule = @{thm CurrentConstruction_Inhabited_rule},
    initialize_sequent = default_initialize_sequent,
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
(* MAY NOT REMOVE
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
    end *)
in
{
    name = \<^const_name>\<open>working_mode_view_shift\<close>,
    domain = (fn tm => Phi_Syntax.is_construction_mode \<^const>\<open>view_shift_mode\<close> tm orelse
                       can Phi_Syntax.dest_view_shift tm),
    is_on_going_construction = can Phi_Syntax.dest_CurrentConstruction,
    spec_of   = #4 o Phi_Syntax.dest_CurrentConstruction,
    spec_of_c = #4 o Phi_Syntax.dest_CurrentConstruction_c,
(*    target_spec = SOME o target_spec,
    target_spec_c = SOME oo target_spec_c,
    exception_spec = K NONE,
    exception_spec_c = K (K NONE), *)
    inhabited_rule = @{thm CurrentConstruction_Inhabited_rule},
    initialize_sequent = default_initialize_sequent,
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
        vcg_by_cast (#4 (Phi_Syntax.dest_CurrentConstruction_c goal)) (ctxt,sequent)),
    introduce_existence = introduce_existence_cc I @{thm introduce_Ex},
    introduce_existence_in_assembling =
      introduce_existence_cc (fn (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) => X
                               | _ => error ("bad form of the finalizing sequent"))
                             @{thm introduce_Ex_subj}
}
end

(** Implication **)


local
(* MAY NOT REMOVE
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
    end *)
in
val implication : working_mode = {
    name = \<^const_name>\<open>working_mode_implication\<close>,
    domain = (fn tm => can Phi_Syntax.dest_ToA_Construction tm orelse
                       can Phi_Syntax.dest_implication tm),
    is_on_going_construction = can Phi_Syntax.dest_ToA_Construction,
    spec_of   = #2 o Phi_Syntax.dest_ToA_Construction,
    spec_of_c = #2 o Phi_Syntax.dest_ToA_Construction_c,
    inhabited_rule = @{thm ToA_Construction_Inhabited_rule},
    initialize_sequent = default_initialize_sequent,
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
        vcg_by_cast (#2 (Phi_Syntax.dest_ToA_Construction_c goal)) (ctxt,sequent)),
    introduce_existence = introduce_ex_ToA I @{thm introduce_Ex_ToA},
    introduce_existence_in_assembling =
        introduce_ex_ToA (fn (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) => X
                           | _ => error ("bad form of the finalizing sequent"))
                         @{thm introduce_Ex_ToA_subj}
}
end

val _ = Theory.setup (Context.theory_map (register [procedure, view_shift, implication]))



fun infer_working_mode_of_sequent (ctxt,sequent) =
  let val _ = Phi_Reasoner.info_pretty ctxt 2 (fn () => Pretty.chunks [
                Pretty.str "Inferring the working mode for the sequent:",
                Thm.pretty_thm ctxt sequent
            ])
      val (sequent',ctxt') =
          Phi_Reasoner.reason (SOME 1) (ctxt, @{thm reason_programming} RS sequent)
              |> (fn SOME (X,TH) => (TH, X)
                   | NONE => error (Pretty.string_of (Pretty.chunks [
                        Pretty.str "Don't know how to make by programming:",
                        Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
                       ])))
      val mode = case Thm.major_prem_of sequent'
                 of Const(\<^const_name>\<open>Pure.term\<close>, _) $ Const (N, _)
                      => get_by_name1 (Context.Proof ctxt') N
                  | X => Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
                          Pretty.str "Bad mode constant:",
                          Syntax.pretty_term ctxt' X
                      ]))
      val sequent'' = (Drule.termI RS sequent')
                   |> Raw_Simplifier.norm_hhf_protect ctxt'
   in (mode, (ctxt', sequent'')) end


end
