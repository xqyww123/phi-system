signature PHI_WORKING_MODE = sig

type working_mode = {
  domain: Proof.context -> term -> bool,
  argument_spec: term (*term of the current sequent*) -> term,
  return_spec:   term (*term of the current sequent*) -> term,
  return_spec_c: Proof.context -> cterm (*term of the current sequent*) -> cterm,
  inhabited_rule: Proof.context -> thm,
  initial_sequent: string (*block name*) -> cterm (*spec of initial state*)
                      -> Proof.context -> Proof.context * thm,
  block_name_of: term -> string,
  cast_rule:     Proof.context -> cterm (*desired*) -> term (*prop*) -> thm,
  before_finish: Proof.context -> cterm -> thm -> thm
}

val working_mode_on  : Proof.context -> term -> working_mode option
val working_mode_on1 : Proof.context -> term -> working_mode
val procedure : working_mode
val view_shift : working_mode
val implication : working_mode

val set  : working_mode -> Proof.context -> Proof.context
val mode : Proof.context -> working_mode

end

structure Phi_Working_Mode : PHI_WORKING_MODE = struct

type working_mode = {
  domain: Proof.context -> term -> bool,
  argument_spec: term (*term of the current sequent*) -> term,
  return_spec: term (*term of the current sequent*) -> term,
  return_spec_c: Proof.context -> cterm (*term of the current sequent*) -> cterm,
  inhabited_rule: Proof.context -> thm,
  initial_sequent: string (*block name*) -> cterm (*spec of initial state*)
                      -> Proof.context -> Proof.context * thm,
  block_name_of: term -> string,
  cast_rule: Proof.context -> cterm -> term -> thm,
  before_finish: Proof.context -> cterm -> thm -> thm
}

structure Data = Generic_Data(
  type T = working_mode Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K false)
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
  


(* Working Modes *)

(** Procedure Mode **)    

val procedure : working_mode = 
  let
    val return_spec =
          orelse_opt (try (#4 o PhiSyntax.dest_CurrentConstruction))
         (orelse_opt (try (#3 o PhiSyntax.dest_procedure))
             (#4 o PhiSyntax.dest_PendingConstruction))
    val return_spec_c = K (
          orelse_opt (try (#4 o PhiSyntax.dest_CurrentConstruction_c))
         (orelse_opt (try (#3 o PhiSyntax.dest_procedure_c))
             (#4 o PhiSyntax.dest_PendingConstruction_c)))
    val argument_spec = orelse_opt (try (#3 o PhiSyntax.dest_CurrentConstruction))
         (orelse_opt (try (#2 o PhiSyntax.dest_procedure))
             (#3 o PhiSyntax.dest_PendingConstruction))

    fun finish_proc hyp (ctxt,sequent) =
      let open PhiSyntax
        val reassemble_proc_final = Proof_Context.get_thm ctxt "local.\<phi>reassemble_proc_final"
        val (_,s',H',_) = dest_CurrentConstruction_c hyp
      in
        sequent
          |> Thm.implies_intr hyp
          |> Thm.forall_intr H'
          |> Thm.forall_intr s'
          |> (fn th => th COMP reassemble_proc_final)
      end
    
    fun start_proc blk_name arg ctxt =
      let open PhiSyntax
        val ([blk_name, RR],ctxt) = Variable.add_fixes [blk_name, "\<RR>"] ctxt
        val stat_var = Free (blk_name, mk_resourceT ctxt)
        val ctxt = Variable.declare_constraints stat_var ctxt
        val init = Const("local.CurrentConstruction",
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


    fun before_finish ctxt goal sequent =
      let
        val sequent' =
          if can PhiSyntax.dest_CurrentConstruction (Thm.concl_of sequent)
          then let
            val (ins,current_nu) =
                  return_spec_c ctxt (Thm.cprop_of sequent)
                     |> Thm.term_of
                     |> Procedure_Syntax.abstract_return_vals "\<r>\<e>\<t>" true
                     |> apfst (Syntax.check_term ctxt #> Thm.cterm_of ctxt)
                     |> apsnd (Syntax.check_term ctxt #> Thm.cterm_of ctxt)
            val idx_delt = 1 + Int.max (Thm.maxidx_of_cterm ins, Thm.maxidx_of_cterm current_nu)
            val return_rule = Proof_Context.get_thm ctxt "local.\<phi>return"
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
                              |> PhiSyntax.dest_sem_value_T
        val current_phi = return_spec_c ctxt (Thm.cprop_of sequent')
        val current_arg_T = Thm.typ_of_cterm current_phi |> Term.domain_type
                              |> PhiSyntax.dest_sem_value_T
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
      in sequent'' end

  in {
    domain = (fn _ => fn tm =>
               can PhiSyntax.dest_procedure tm
        orelse PhiSyntax.is_construction_mode \<^const>\<open>programming_mode\<close> tm
    ),
    return_spec = return_spec,
    return_spec_c = return_spec_c,
    argument_spec = argument_spec,
    inhabited_rule = (fn ctxt =>
        Proof_Context.get_thm ctxt "local.CurrentConstruction_Inhabited_rule"),
    initial_sequent = start_proc,
    block_name_of = (fn term => 
        case #1 (PhiSyntax.dest_procedure term)
          of (Var ((x,_),_)) => x
           | _ => "block"),
    cast_rule = (fn ctxt => fn desired => fn term =>
      let
        val idx = 1 + Thm.maxidx_of_cterm desired
        val rule =
          if can (PhiSyntax.dest_CurrentConstruction) term
          then Proof_Context.get_thm ctxt "local._\<phi>cast_internal_rule_"
          else Proof_Context.get_thm ctxt "local._\<phi>cast_internal_rule_'"
       in rule
            |> Thm.incr_indexes idx
            |> Drule.infer_instantiate ctxt [(("T'",idx),desired)]
       end
    ),
    before_finish = before_finish
} end


(** View Shift **)


val view_shift : working_mode = 
let
  fun return_spec term =
    let
      val (_,T,P) = PhiSyntax.dest_view_shift term
    in
      Const (\<^const_name>\<open>Subjection\<close>, fastype_of T --> \<^typ>\<open>bool\<close> --> fastype_of T) $ T $ P
    end
  (*TODO: optimize this*)
  fun return_spec_c ctxt = Thm.term_of #> return_spec #> Thm.cterm_of ctxt

  fun finish_view_shift hyp (ctxt,sequent) =
    let open PhiSyntax
      val reassemble_proc_final = Proof_Context.get_thm ctxt "local.\<phi>make_view_shift"
      val (_,s',H',_) = dest_CurrentConstruction_c hyp
    in
      sequent
        |> Thm.implies_intr hyp
        |> Thm.forall_intr H'
        |> Thm.forall_intr s'
        |> (fn th => th COMP reassemble_proc_final)
    end

  fun start_view_shift blk_name arg ctxt =
    let open PhiSyntax
      val ([blk_name, RR],ctxt) = Variable.add_fixes [blk_name, "\<RR>"] ctxt
      val stat_var = Free (blk_name, mk_resourceT ctxt)
      val ctxt = Variable.declare_constraints stat_var ctxt
      val init = Const("local.CurrentConstruction",
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
    domain = (fn _ => fn x => can PhiSyntax.dest_view_shift x
                       orelse PhiSyntax.is_construction_mode \<^const>\<open>view_shift_mode\<close> x),
    return_spec = return_spec,
    return_spec_c = return_spec_c,
    argument_spec = #1 o PhiSyntax.dest_view_shift,
    inhabited_rule = (fn ctxt =>
      Proof_Context.get_thm ctxt "local.CurrentConstruction_Inhabited_rule"),
    initial_sequent = start_view_shift,
    block_name_of = (fn term => 
        case #1 (PhiSyntax.dest_view_shift term)
          of (Var ((x,_),_)) => x
           | _ => "\<V>\<S>"),
    cast_rule = (fn ctxt => fn desired => fn _ =>
      let
        val idx = 1 + Thm.maxidx_of_cterm desired
      in
        Proof_Context.get_thm ctxt "local._\<phi>cast_internal_rule_"
          |> Thm.incr_indexes idx
          |> Drule.infer_instantiate ctxt [(("T'",idx),desired)]
      end
    ),
    before_finish = (K (K I))
}
end

(** Implication **)


val implication : working_mode =
let
  fun return_spec term =
    let
      val (_,T,P) = PhiSyntax.dest_implication term
    in
      Const (\<^const_name>\<open>Subjection\<close>, fastype_of T --> \<^typ>\<open>bool\<close> --> fastype_of T) $ T $ P
    end
  (*TODO: optimize this*)
  fun return_spec_c ctxt = Thm.term_of #> return_spec #> Thm.cterm_of ctxt

  val argument_spec = (#1 o PhiSyntax.dest_implication)

  fun finish_implication hyp (ctxt,sequent) =
    let
      val (s,_) = PhiSyntax.dest_Set_member_c hyp
    in
      sequent
        |> Thm.implies_intr hyp
        |> Thm.forall_intr s
        |> (fn th => th COMP @{thm \<phi>make_implication})
    end
  
  fun start_implication blk_name arg_phiTy ctxt =
    let open PhiSyntax
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
    domain = (fn _ => fn x => can PhiSyntax.dest_implication x
                       orelse can PhiSyntax.dest_Set_member  x),
    return_spec = return_spec,
    return_spec_c = return_spec_c,
    argument_spec = argument_spec,
    inhabited_rule = K @{thm Implication_Inhabited_rule},
    initial_sequent = start_implication,
    block_name_of = (K "\<chi>"),
    cast_rule = (fn ctxt => fn desired => fn _ =>
      let
        val idx = 1 + Thm.maxidx_of_cterm desired
      in
        @{thm "_\<phi>cast_implication_"}
          |> Thm.incr_indexes idx
          |> Drule.infer_instantiate ctxt [(("T",idx),desired)]
      end
    ),
    before_finish = (K (K I))
}
end

val _ = Theory.setup (Context.theory_map
            (Data.map (Symtab.update_new ("procedure",   procedure)
                    #> Symtab.update_new ("view_shift",  view_shift)
                    #> Symtab.update_new ("implication", implication)
)))


end
