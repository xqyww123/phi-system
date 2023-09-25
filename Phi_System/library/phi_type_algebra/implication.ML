signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val abstract_domain : quiet -> deriving_instruction list -> Phi_Type_Algebra.derive
val abstract_domain_L : quiet -> deriving_instruction list -> Phi_Type_Algebra.derive

val guess_property_like_abst_domain :
      bool * (typ * typ -> term)
      * (Proof.context * typ * term * term -> term list -> term list)
      * (Proof.context * typ * term * term -> term -> term)
      * sort * sort
      -> guess_property

(*Infers a predicate or a boolean condition making the obligation true.
  It supports upper and lower modes.

  Upper mode: the unknown locates at the consequent part, and we infer a satisfiable instantiation
              from the conditions of the oblgiation.
  Lower mode: the unknown locates at the condition part of the obligation, and we infer an instantiation
              as strong as possible (but does not weaken the entire obligation)
*)
val abstract_domain_solver : bool -> string -> solver

(*val guess_property_abst_dom : string -> guess_property
val abstract_domain_solver : bool -> string (*name of proof cache*) -> solver*)

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property_like_abst_domain (is_cov, prop_head, pass_ants, pass_pred, x_sort, model_sort) (phi0 : phi_type) ctxt =
  let val (rev_arg_tys0, x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val tpairs = map_filter (   try dest_parameterized_phi_ty
                               #> Option.map (fn (_, x, m) => [(x, x_sort), (m, model_sort)])
                              ) rev_arg_tys0
                |> flat
      val inst = lift_types_sort (Proof_Context.theory_of ctxt)
                                 ((x_ty0, x_sort) :: (model_ty0, model_sort) :: tpairs)
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val phi = instantiate_phi (inst',Vars.empty) phi0

      val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (rev_arg_tys,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term
      val x_ttys = map (#2 o #1) T_params
      val preds = Name.invent_names (Variable.names_of ctxt) "P"
                                     (map (fn T => T --> HOLogic.boolT) x_ttys)
      val ctxt = Variable.add_fixes_direct (map fst preds) ctxt
      val preds = x_ttys ~~ map Free preds
      val ants = map2 (fn ((rev_args, x, m), T'h) => fn (_, pred) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_args T'h
             in prop_head (x,m) $ T' $ pred
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params preds
      val idx = phi_maxidx_of phi ~1 + 1

      val (ants_delta, oblg_delta, cond_delta) =
              guess_conditions ctxt (prop_head (x_ty, model_ty), is_cov) phi T_term
      (*fun pass_pred pred =
            if is_cov then Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (cond_delta $ Bound 0) $ (pred $ Bound 0))
                      else Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (oblg_delta $ Bound 0) $ (pred $ Bound 0))*)

      val add_Pvar = if #is_recursive phi then I
                     else fn pred => 
                      let val Pvar = Var(("P",idx), x_ty --> HOLogic.boolT)
                       in Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (pred $ Bound 0) $ (Pvar $ Bound 0))
                      end
   in guess_predicate ctxt preds x_ty
   |> Seq.map (fn (pred, ctxt) =>
        (pass_ants (ctxt, x_ty, oblg_delta, cond_delta) (ants_delta @ ants),
         HOLogic.Trueprop $ (prop_head (x_ty, model_ty) $ T_term
            $ add_Pvar (pass_pred (ctxt, x_ty, oblg_delta, cond_delta) pred)),
         NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt))
  end


(*** Inhabitance ***)
(*
fun guess_property_abst_dom upper (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (rev_arg_tys,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term
      val x_ttys = map (#2 o #1) T_params
      val preds = Name.invent_names (Variable.names_of ctxt) "P"
                                     (map (fn T => T --> HOLogic.boolT) x_ttys)
      val ctxt = Variable.add_fixes_direct (map fst preds) ctxt
      val preds = x_ttys ~~ map Free preds
      val head_const = if upper then \<^const_name>\<open>Abstract_Domain\<close>
                                else \<^const_name>\<open>Abstract_Domain\<^sub>L\<close>
      fun head x m = Const(head_const, \<^Type>\<open>fun \<^Type>\<open>fun x \<^Type>\<open>set m\<close>\<close> \<^Type>\<open>fun \<^Type>\<open>fun x \<^Type>\<open>bool\<close>\<close> \<^Type>\<open>bool\<close>\<close>\<close>)
      val ants = map2 (fn ((rev_args, x, m), T'h) => fn (_, pred) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_args T'h
             in head x m $ T' $ pred
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params preds
      val idx = phi_maxidx_of phi ~1 + 1
      
      val (ants_delta, oblg_delta, cond_delta) =
              guess_conditions ctxt (head x_ty model_ty, not upper) phi T_term
      fun pass_pred pred =
            if upper then Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (cond_delta $ Bound 0) $ (pred $ Bound 0))
                     else Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (oblg_delta $ Bound 0) $ (pred $ Bound 0))

      val add_Pvar = if #is_recursive phi then I
                     else fn pred => 
                      let val Pvar = Var(("P",idx), x_ty --> HOLogic.boolT)
                       in Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (Pvar $ Bound 0) $ (pred $ Bound 0))
                      end
   in guess_predicate ctxt preds x_ty
   |> Seq.map (fn (pred, ctxt) =>
        (if upper then ants_delta @
                       PLPR_Syntax.dest_ant_sequence_or_HOL_conj (forall_qualify x_ty oblg_delta) @
                       ants
                  else ants_delta @ ants,
         HOLogic.Trueprop $ (head x_ty model_ty $ T_term $ add_Pvar (pass_pred pred)),
         NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt))
  end
*)
(*fun guess_property_inhab_atom upper (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (_,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val idx = phi_maxidx_of phi ~1 + 1
      fun head x m = if upper then \<^Const>\<open>Abstract_Domain x m\<close>
                              else \<^Const>\<open>Abstract_Domain\<^sub>L x m\<close>
      val Prop = HOLogic.Trueprop $ (head x_ty model_ty $ T_term $ Var(("P",idx), x_ty --> HOLogic.boolT))
   in Seq.single ([], Prop, NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end
*)

(*Infers a predicate or a boolean condition making the obligation true.
  It supports upper and lower modes.

  Upper mode: the unknown locates at the consequent part, and we infer a satisfiable instantiation
              from the conditions of the oblgiation.
  Lower mode: the unknown locates at the condition part of the obligation, and we infer an instantiation
              as strong as possible (but does not weaken the entire obligation)
*)
fun abstract_domain_solver upper name (phi,ctxt,sequent) =
  let fun err () = raise Automation_Fail (fn () =>
                        [Pretty.para "Obligation is obtained, but I fail to infer \
                                     \the expression of the implied pure fact from it."])
      val var = case Thm.concl_of sequent
                  of _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $ Var v) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Var v $ Bound 0))) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ Var v $ _)) => v
                   | _ => err ()

      fun binop H (SOME sa, SOME sb) = SOME (H $ sa $ sb)
        | binop _ (some_or_none, NONE) = some_or_none
        | binop _ (NONE, some) = some
      fun qualifies j vars =
             fold_index (fn (k, (N, ty)) => fn X =>
                if k = j then Abs (N, ty, X) $ Bound (length vars - 1 - k)
                else HOLogic.all_const ty $ Abs(N, ty, X)
             ) vars

      fun augment P prems = (*the inferred condition won't contain Inhabited and Satisfaction*)
            if exists_subterm (fn Const(\<^const_name>\<open>Inhabited\<close>, _) => true
                                | Const(\<^const_name>\<open>Satisfaction\<close>, _) => true
                                | _ => false) P
            then prems else P :: prems

      fun inst_Lw context (Const(\<^const_name>\<open>conj\<close>, _) $ X $ Y)
            = binop \<^Const>\<open>HOL.conj\<close> (inst_Lw context X, inst_Lw context Y)
        | inst_Lw context (Const(\<^const_name>\<open>disj\<close>, _) $ X $ Y)
            = binop \<^Const>\<open>HOL.disj\<close> (inst_Lw context X, inst_Lw context Y)
        | inst_Lw (vars,prems) (Const(\<^const_name>\<open>All\<close>, _) $ Abs (N,ty,X))
            = inst_Lw ((N,ty)::vars, map (Term.incr_boundvars 1) prems) X
        | inst_Lw (vars,prems) (\<^Const>\<open>All T\<close> $ X)
            = inst_Lw (vars,prems) (\<^Const>\<open>All T\<close> $ (Abs ("_", T, Term.incr_boundvars 1 X $ Bound 0)))
        | inst_Lw (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
            = let fun meet v j = if var = v
                                 then fold (fn prem => fn X => \<^Const>\<open>HOL.implies\<close> $ prem $ X) prems X
                                  |> qualifies j vars
                                  |> SOME
                                 else inst_Lw (vars, augment P prems) X
               in case P
               of Var v $ Bound j => meet v j
                | Var v => meet v ~1
                | Const (\<^const_name>\<open>HOL.conj\<close>, _) $ (Var v $ Bound j) $ _ => meet v j
                | _ => inst_Lw (vars, augment P prems) X
              end
        | inst_Lw _ _ = NONE

      fun inst_Lw' context X = case inst_Lw context X of SOME ret => ret
                                  | NONE => \<^Const>\<open>True\<close>

      fun inst_Pr context (Const(\<^const_name>\<open>conj\<close>, _) $ A $ B)
            = binop \<^Const>\<open>HOL.disj\<close> (inst_Pr context A, inst_Pr context B)
        | inst_Pr context (Const(\<^const_name>\<open>disj\<close>, _) $ A $ B)
            = binop \<^Const>\<open>HOL.conj\<close> (inst_Pr context A, inst_Pr context B)
        | inst_Pr (vars,prems) (Const(\<^const_name>\<open>All\<close>, _) $ Abs (N,ty,X))
            = inst_Pr ((N,ty)::vars, map (Term.incr_boundvars 1) prems) X
        | inst_Pr (vars,prems) (\<^Const>\<open>HOL.All ty\<close> $ X)
            = inst_Pr (vars,prems) (\<^Const>\<open>HOL.All ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | inst_Pr (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
            = inst_Pr (vars, augment P prems) X
        | inst_Pr (vars,prems) (Var v $ Bound j)
            = if v = var then SOME (qualifies j vars (Phi_Help.list_mk_conj prems)) else NONE
        | inst_Pr (vars,prems) (Var v)
            = if v = var then SOME (qualifies ~1 vars (Phi_Help.list_mk_conj prems)) else NONE
        | inst_Pr _ _ = NONE

      fun inst_Pr' context X = case inst_Pr context X of SOME ret => ret
                                  | NONE => \<^Const>\<open>False\<close>

  in case Thm.prop_of sequent
       of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _)
            $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ X)) $ _
            => let val X'1 = (if upper then inst_Pr' else inst_Lw') ([],[]) X
                   val X' = case snd var
                              of \<^Type>\<open>fun D _\<close> => Abs ("x", D, X'1)
                               | _ => X'1
                   val X' = if exists_subterm (fn Var v => v = var | _ => false) X'
                            then \<^Const>\<open>True\<close> (*the case of recursive, unsupported*)
                            else X'
                in SOME (Thm.instantiate (TVars.empty, Vars.make [(var, Thm.cterm_of ctxt X')]) sequent
                      |> oblg_solver (#proof_id phi ^ "/" ^ name) ctxt)
               end
        | _ => error "Internal bug"
 end

fun gen_inhab upper (der_id, name) instruction0 ctxt0 (phi0 : phi_type) thy =
  let val guess_property = guess_property_like_abst_domain (not upper,
            if upper then fn (x,m) => \<^Const>\<open>Abstract_Domain x m\<close>
                     else fn (x,m) => \<^Const>\<open>Abstract_Domain\<^sub>L x m\<close>,
            if upper then K I else fn (ctxt, x_ty, oblg, _) => fn ants =>
               (case oblg of Abs (_, _, \<^Const>\<open>True\<close>) => ants
                   | _ => (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_GUARD\<close> $ (simplified_forall_qualify ctxt x_ty oblg)) :: ants),
            if upper then fn (_, x_ty, _, cond) => fn pred =>
                              Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (cond $ Bound 0) $ (pred $ Bound 0))
                     else fn (_, x_ty, oblg, _) => fn pred =>
                              Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (oblg $ Bound 0) $ (pred $ Bound 0)),
            \<^sort>\<open>type\<close>, \<^sort>\<open>type\<close>)

      val mode_infer = not (is_some instruction0) andalso not (#is_recursive phi0)

      val parse_hint = parse_hint (
              fn Const(\<^const_name>\<open>Abstract_Domain\<close>, _) $ T $ _ => T
               | Const(\<^const_name>\<open>Abstract_Domain\<^sub>L\<close>, _) $ T $ _ => T)

      fun extract_oprs_from_hint (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ P) = [P]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (K (K (fn ctm => Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1} ctm)),
              fn ctxt => fn _ =>
                 (Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1} then_conv
                  Conv.implies_concl_conv (HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                    (if upper then Conv.arg1_conv else Conv.arg_conv) (Conv.arg_conv (
                      Simplifier.rewrite (Expansion.equip ctxt addsimps (#equations phi0)))))))))

      fun varify_subgoal _ (Trueprop $ (Action_Tag $ (Imp $ S $ P) $ AEIF)) =
            SOME ([P], fn [P'] => Trueprop $ (Action_Tag $ (Imp $ S $ P') $ AEIF))
        | varify_subgoal _ X = error ""

      fun Inh_reasoning phi ctxt =
            default_reasoning false
                default_reasoning_configure
                (if mode_infer then varify_subgoal else K (K NONE))
                (exhaustive_PLPR_reasoner_by_rule
                    (if upper then @{thm' \<phi>TA_Inh_step} else @{thm' \<phi>TA_Suc_step})
                    (K (chk_unfolded' ctxt phi)))
                phi
                ctxt

      val solver = if mode_infer then abstract_domain_solver upper name else K NONE
      val simp = if is_some instruction0 then K I
                 else default_simplifier' (fn rewr =>
                   Phi_Conv.hhf_concl_conv (fn ctxt =>
                      HOLogic.Trueprop_conv (Conv.arg_conv (rewr ctxt)) ))
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint, guess_property,
                                      (if upper then @{thm' \<phi>TA_Inh_rule} else @{thm' \<phi>TA_SuC_rule}),
                                      [(K (SOME [0]), ind_conv, Inh_reasoning)],
                                      solver, simp)
                                     phi0 (Option.map fst instruction0) ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property."])
         | SOME (rule', _) => thy
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.NORMAL_MODE
                                        (the_default @{reasoner_group %derived_abstract_domain}
                                                     (Option.mapPartial snd instruction0))
                                        ([],[]) NONE [Morphism.thm m rule'])
            |> note_properties_s phi0 [(name, [rule'])]
            |> pair [rule']
  end

val abstract_domain =
      deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Abstract_Domain") (gen_inhab true)
val abstract_domain_L =
      deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Abstract_Domain\<^sub>L") (gen_inhab false)

end
