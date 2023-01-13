signature PHI_WORKING_MODE = sig

type working_mode = {
  domain: Proof.context -> term -> bool,
  argument_spec: term (*proposition of a goal or a state sequent*) -> term,
  return_spec:   term (*proposition of a goal*) -> term,
  return_spec_c: Proof.context -> cterm (*proposition of a goal*) -> cterm,
  exception_spec  : term (*proposition of a goal*) -> term option,
  exception_spec_c: Proof.context -> cterm (*proposition of a goal*) -> cterm option,
  inhabited_rule: Proof.context -> thm,
  initial_sequent: string (*block name*) -> cterm (*spec of initial state*)
                      -> Proof.context -> Proof.context * thm,
  block_name_of: term -> string,
  transform_rule : thm,
  view_shift_rule: thm option,
  cast: cterm (*desired*) -> Proof.context * thm (*sequent*) -> Proof.context * thm,
  cast_exception: cterm (*desired*) -> Proof.context * thm -> Proof.context * thm,
  before_finish: cterm -> Proof.context * thm -> Proof.context * thm
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
  domain: Proof.context -> term -> bool,
  argument_spec: term (*proposition of a goal or a state sequent*) -> term,
  return_spec: term (*term of the state sequent*) -> term,
  return_spec_c: Proof.context -> cterm (*term of the state sequent*) -> cterm,
  exception_spec  : term (*proposition of a goal*) -> term option,
  exception_spec_c: Proof.context -> cterm (*proposition of a goal*) -> cterm option,
  inhabited_rule: Proof.context -> thm,
  initial_sequent: string (*block name*) -> cterm (*spec of initial state*)
                      -> Proof.context -> Proof.context * thm,
  block_name_of: term -> string,
  transform_rule : thm,
  view_shift_rule: thm option,
  cast: cterm -> Proof.context * thm -> Proof.context * thm,
  cast_exception: cterm (*desired*) -> Proof.context * thm -> Proof.context * thm,
  before_finish: cterm -> Proof.context * thm -> Proof.context * thm
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
         | NONE => error ("Do not know how to handle goal " ^ Syntax.string_of_term ctxt goal)

fun orelse_opt f1 f2 x = case f1 x of SOME y => y | NONE => f2 x


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

(*
fun collect_free_variables vars term = inter (op =) vars (Term.add_frees term [])

fun generic_existential_generalization cast vars spec stat =
  if null vars
  then state
  else

fun eliminate_term ctxt xs thm =
  let open Phi_Basics Phi_Syntax Phi_Help
    val tm = Thm.prop_of thm
    val vs = map (dest_Free o Thm.term_of) xs;
    val bads = Term.fold_aterms (fn t as Free v =>
      if member (op =) vs v then insert (op aconv) t else I | _ => I) tm [];
  in
    if null bads then thm
    else let
      val typing' = dest_current_nu thm
            |> list_mk_binder @{const_name ExSet} bads
            |> Syntax.check_term ctxt |> Thm.cterm_of ctxt
    in
      Phi_Sys.cast typing' (ctxt,thm)
        |> Phi_Reasoners.naive_obligation_solver'
        |> snd
    end
  end *)

(* Working Modes *)

(** Procedure Mode **)    

val procedure : working_mode = 
  let
    val return_spec =
          orelse_opt (try (#4 o Phi_Syntax.dest_CurrentConstruction))
         (orelse_opt (try (#3 o Phi_Syntax.dest_procedure))
             (#4 o Phi_Syntax.dest_PendingConstruction))
    val return_spec_c = K (
          orelse_opt (try (#4 o Phi_Syntax.dest_CurrentConstruction_c))
         (orelse_opt (try (#3 o Phi_Syntax.dest_procedure_c))
             (#4 o Phi_Syntax.dest_PendingConstruction_c)))
    val exception_spec = 
          orelse_opt (try (#4 o Phi_Syntax.dest_procedure))
             (#5 o Phi_Syntax.dest_PendingConstruction) #> SOME
    val exception_spec_c = K (
          orelse_opt (try (#4 o Phi_Syntax.dest_procedure_c))
             (#5 o Phi_Syntax.dest_PendingConstruction_c) #> SOME)
    val argument_spec = orelse_opt (try (#4 o Phi_Syntax.dest_CurrentConstruction))
         (orelse_opt (try (#2 o Phi_Syntax.dest_procedure))
             (#4 o Phi_Syntax.dest_PendingConstruction))

    fun finish_proc hyp (ctxt,sequent) =
      let open Phi_Syntax
        val (_,s',H',_) = dest_CurrentConstruction_c hyp
      in
        sequent
          |> Thm.implies_intr hyp
          |> Thm.forall_intr H'
          |> Thm.forall_intr s'
          |> (fn th => th COMP @{thm \<phi>reassemble_proc_final})
      end
    
    fun start_proc blk_name arg ctxt =
      let open Phi_Syntax
        val ([blk_name, RR],ctxt) = Variable.add_fixes [blk_name, "\<RR>"] ctxt
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


    fun before_finish goal (ctxt,sequent) =
      let
        val sequent' =
          if can Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)
          then let
            val (ins,current_nu) =
                  return_spec_c ctxt (Thm.cprop_of sequent)
                     |> Thm.term_of
                     |> Procedure_Syntax.abstract_return_vals "\<r>\<e>\<t>" true
                     |> apply2 (Syntax.check_term ctxt #> Thm.cterm_of ctxt)
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
        val desired_nu = return_spec_c ctxt goal
        val desired_arg_T = Thm.typ_of_cterm desired_nu |> Term.domain_type
                              |> Phi_Syntax.dest_sem_value_T
        val current_phi = return_spec_c ctxt (Thm.cprop_of sequent')
        val current_arg_T = Thm.typ_of_cterm current_phi |> Term.domain_type
                              |> Phi_Syntax.dest_sem_value_T
        val sequent'' = if can (Pattern.unify_types (Context.Proof ctxt)
                                                    (current_arg_T, desired_arg_T)) Envir.init
                        then sequent'
                        else if current_arg_T = @{typ "unreachable"}
                        then sequent' RS Proof_Context.get_thm ctxt "\<phi>return_when_unreachable"
                        else if can (Pattern.unify_types (Context.Proof ctxt)
                                  (HOLogic.mk_prodT (current_arg_T, @{typ unit}), desired_arg_T))
                                  Envir.init
                        then sequent' RS Proof_Context.get_thm ctxt "\<phi>return_additional_unit"
                        else error ("Current block expects returning "^
                                Syntax.string_of_typ ctxt desired_arg_T^
                                " but it actually returns "^
                                Syntax.string_of_typ ctxt current_arg_T)
      in (ctxt,sequent'') end

  in {
    domain = (fn _ => fn tm =>
               can Phi_Syntax.dest_procedure tm
        orelse Phi_Syntax.is_construction_mode \<^const>\<open>programming_mode\<close> tm
    ),
    return_spec = return_spec,
    return_spec_c = return_spec_c,
    argument_spec = argument_spec,
    exception_spec = exception_spec,
    exception_spec_c = exception_spec_c,
    inhabited_rule = K @{thm CurrentConstruction_Inhabited_rule},
    initial_sequent = start_proc,
    block_name_of = (fn term => 
        case #1 (Phi_Syntax.dest_procedure term)
          of (Var ((x,_),_)) => x
           | _ => "block"),
    transform_rule  = @{thm \<phi>apply_implication},
    view_shift_rule = SOME @{thm \<phi>apply_view_shift},
    cast = (fn desired => fn (ctxt, sequent) =>
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
    ),
    cast_exception = (fn desired => fn (ctxt, sequent) =>
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
    ),
    before_finish = before_finish
} end


(** View Shift **)


val view_shift : working_mode = 
let
  fun return_spec term =
    let
      val (_,T,P) = Phi_Syntax.dest_view_shift term
    in
      Const (\<^const_name>\<open>Subjection\<close>, fastype_of T --> \<^typ>\<open>bool\<close> --> fastype_of T) $ T $ P
    end
  (*TODO: optimize this*)
  fun return_spec_c ctxt = Thm.term_of #> return_spec #> Thm.cterm_of ctxt

  fun finish_view_shift hyp (ctxt,sequent) =
    let open Phi_Syntax
      val (_,s',H',_) = dest_CurrentConstruction_c hyp
    in
      sequent
        |> Thm.implies_intr hyp
        |> Thm.forall_intr H'
        |> Thm.forall_intr s'
        |> (fn th => th COMP @{thm \<phi>make_view_shift})
    end

  fun start_view_shift blk_name arg ctxt =
    let open Phi_Syntax
      val ([blk_name, RR],ctxt) = Variable.add_fixes [blk_name, "\<RR>"] ctxt
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
    domain = (fn _ => fn x => can Phi_Syntax.dest_view_shift x
                       orelse Phi_Syntax.is_construction_mode \<^const>\<open>view_shift_mode\<close> x),
    return_spec = return_spec,
    return_spec_c = return_spec_c,
    argument_spec = orelse_opt (try (#4 o Phi_Syntax.dest_CurrentConstruction))
                                    (#1 o Phi_Syntax.dest_view_shift),
    exception_spec = K NONE,
    exception_spec_c = K (K NONE),
    inhabited_rule = K @{thm CurrentConstruction_Inhabited_rule},
    initial_sequent = start_view_shift,
    block_name_of = (fn term => 
        case #1 (Phi_Syntax.dest_view_shift term)
          of (Var ((x,_),_)) => x
           | _ => "\<V>\<S>"),
    transform_rule  = @{thm \<phi>apply_implication},
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
    before_finish = (K I)
}
end

(** Implication **)


val implication : working_mode =
let
  fun return_spec term =
    let
      val (_,T,P) = Phi_Syntax.dest_implication term
    in
      Const (\<^const_name>\<open>Subjection\<close>, fastype_of T --> \<^typ>\<open>bool\<close> --> fastype_of T) $ T $ P
    end
  (*TODO: optimize this*)
  fun return_spec_c ctxt = Thm.term_of #> return_spec #> Thm.cterm_of ctxt

  val argument_spec = orelse_opt (try (#2 o Phi_Syntax.dest_set_member))
                                      (#1 o Phi_Syntax.dest_implication)

  fun finish_implication hyp (ctxt,sequent) =
    let
      val (s,_) = Phi_Syntax.dest_Set_member_c hyp
    in
      sequent
        |> Thm.implies_intr hyp
        |> Thm.forall_intr s
        |> (fn th => th COMP @{thm \<phi>make_implication})
    end
  
  fun start_implication blk_name arg_phiTy ctxt =
    let open Phi_Syntax
      val ([blk_name],ctxt) = Variable.add_fixes [blk_name] ctxt
      val Type (\<^type_name>\<open>set\<close>, [T]) = Thm.typ_of_cterm arg_phiTy
      val stat_var = Free (blk_name, T)
      val ctxt = Variable.declare_constraints stat_var ctxt
      val init = Const(\<^const_name>\<open>Set.member\<close>, dummyT) $ stat_var
      val init = Thm.cterm_of ctxt (Syntax.check_term ctxt init)
      val init = Thm.apply @{cterm Trueprop} (Thm.apply init arg_phiTy)
      val ([init],ctxt) = Assumption.add_assms
            (fn _ => fn [hyp] => (finish_implication hyp o pair ctxt, I)) [init] ctxt
    in
      (ctxt,init)
    end
in
{
    domain = (fn _ => fn x => can Phi_Syntax.dest_implication x
                       orelse can Phi_Syntax.dest_Set_member  x),
    return_spec = return_spec,
    return_spec_c = return_spec_c,
    argument_spec = argument_spec,
    exception_spec = K NONE,
    exception_spec_c = K (K NONE),
    inhabited_rule = K @{thm Implication_Inhabited_rule},
    initial_sequent = start_implication,
    block_name_of = (K "\<chi>"),
    transform_rule  = @{thm \<phi>apply_implication_impl},
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
    before_finish = (K I)
}
end

val _ = Theory.setup (Context.theory_map
            (Data.map (Symtab.update_new ("procedure",   procedure)
                    #> Symtab.update_new ("view_shift",  view_shift)
                    #> Symtab.update_new ("implication", implication)
)))



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


end
