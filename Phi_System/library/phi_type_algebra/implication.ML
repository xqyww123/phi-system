signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val inhabitance : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*** Inhabitance ***)

fun guess_property_inhab_tyop (x_term, T_term, (phi:phi_type)) ctxt =
  let val (rev_arg_tys,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term
      val x_ttys = map (#2 o #1) T_params
      val preds = Name.invent_names (Variable.names_of ctxt) "Pr"
                                     (map (fn T => T --> HOLogic.boolT) x_ttys)
      val ctxt = Variable.add_fixes_direct (map fst preds) ctxt
      val preds = x_ttys ~~ map Free preds
      val ants = map2 (fn ((rev_args, x, m), T'h) => fn (_, pred) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - i)) rev_args T'h
                val inh = \<^Const>\<open>Inhabited m\<close> $ (\<^Const>\<open>\<phi>Type x m\<close> $ Bound 0 $ T')
                val body = \<^Const>\<open>Action_Tag\<close>
                              $ (HOLogic.imp $ inh $ (pred $ Bound 0))
                              $ \<^Const>\<open>\<A>EIF\<close>
             in HOLogic.all_const x $ Abs("x", x, body)
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params preds
   in guess_predicate ctxt preds x_ty
   |> Seq.map (fn (pred, ctxt) =>
        (ants, HOLogic.Trueprop $ (HOLogic.all_const x_ty $ Abs ("x", x_ty, \<^Const>\<open>Action_Tag\<close>
                    $ (HOLogic.imp
                        $ (\<^Const>\<open>Inhabited model_ty\<close> $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ T_term))
                        $ (pred $ Bound 0))
                    $ \<^Const>\<open>\<A>EIF\<close>)),
         x_term, T_term, phi, ctxt))
  end

fun guess_property_inhab_atom (x_term, T_term, (phi:phi_type)) ctxt =
  let val (rev_arg_tys,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val idx = phi_maxidx_of phi ~1 + 1
      val Prop = HOLogic.Trueprop $ (HOLogic.all_const x_ty $ Abs ("x", x_ty, \<^Const>\<open>Action_Tag\<close>
                    $ (\<^Const>\<open>HOL.implies\<close>
                        $ (\<^Const>\<open>Inhabited model_ty\<close> $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ T_term))
                        $ (Var(("Pr",idx), x_ty --> HOLogic.boolT) $ Bound 0))
                    $ \<^Const>\<open>\<A>EIF\<close>))
   in Seq.single ([], Prop, x_term, T_term, phi, ctxt)
  end

fun gen_inhab hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val guess_property = if is_Type_Opr (Term.fastype_of (#term phi0))
                           then guess_property_inhab_tyop
                           else guess_property_inhab_atom
      val mode_infer = not (is_some hint0 orelse is_Type_Opr (Term.fastype_of (#term phi0)))

      val unify_hint_U = hint_unify_by_type (
            fn Const(\<^const_name>\<open>HOL.implies\<close>, _) $ (
                  Const(\<^const_name>\<open>Inhabited\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T)) $ _
                 => T
             | _ => raise TERM ("",[]))
      val ind_conv = default_ind_conv (K (K (Conv.rewr_conv @{thm' \<phi>TA_Inh_rewr})),
              fn ctxt => fn _ =>
                  Conv.rewr_conv @{thm' \<phi>TA_Inh_rewr} then_conv
                  Conv.implies_concl_conv (HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                    Conv.arg1_conv (Conv.arg_conv (
                      Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0))))))))
      fun Inh_reasoner ctxt sequent =
        case PLPR_Exhaustive.reason_exhaustively (SOME 2)
                  (ctxt, @{thm' \<phi>TA_Inh_step} RS sequent)
          of SOME th => th
           | NONE => raise Automation_Fail      
      fun varify_subgoal (Trueprop $ (Action_Tag $ (Imp $ S $ P) $ AEIF)) =
            SOME ([P], fn [P'] => Trueprop $ (Action_Tag $ (Imp $ S $ P') $ AEIF))
        | varify_subgoal X = error ""
      fun Inh_reasoning _ ctxt = gen_abstract_constraint_guided_reasoning
            (if mode_infer then varify_subgoal else K NONE) Inh_reasoner ctxt


      val solver =
        if mode_infer
        then (fn (phi,ctxt,sequent) =>
           let fun inst_Pr context (Const(\<^const_name>\<open>conj\<close>, _) $ X $ _)
                      = inst_Pr context X
                 | inst_Pr (vars,prems) (Const(\<^const_name>\<open>All\<close>, _) $ Abs (N,ty,X))
                      = inst_Pr ((N,ty)::vars, map (Term.incr_boundvars 1) prems) X
                 | inst_Pr (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
                      = inst_Pr (vars, P::prems) X
                 | inst_Pr (vars,prems) (Var (v as (("Pr",_), \<^Type>\<open>fun tyv _\<close>)) $ Bound j)
                      = Phi_Help.list_mk_conj prems
                          |> fold_index (fn (k, (N, ty)) => fn X =>
                                if k = j then Abs (N, ty, X) $ Bound (length vars - 1 - k)
                                else HOLogic.all_const ty $ Abs(N, ty, X)
                             ) vars
                          |> (fn X => Abs ("x", tyv, X))
                          |> (fn X => Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt X)]))
            in case Thm.prop_of sequent
                 of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _)
                      $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ X)) $ _
                      => SOME (inst_Pr ([],[]) X sequent
                                |> oblg_solver (#proof_id phi ^ "/Inh") ctxt)
                  | _ => error "Internal bug"
           end)
(*(fn (_,_,sequent) => SOME (@{thm' \<phi>TA_Inh_inst_P} RS sequent))*)
        else K NONE
      fun simp (_, ctxt) rule0 =
        let val rule = rule0 RS' (ctxt, @{thm' spec})
         in if is_some hint0
            then rule
            else Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                    HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                      Conv.arg_conv (Simplifier.rewrite (ctxt addsimps @{thms special_Ex_def}))
                    ))) ctxt) rule
        end
      val rules = mk_rule_by_guess_or_hint ("Implication", unify_hint_U, guess_property,
                                            @{thm' \<phi>TA_Inh_rule}, [0], SOME ind_conv,
                                            Inh_reasoning, solver, simp)
                                           phi0 hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail
         | SOME (rule', _) => thy
            |> Phi_Type_Algebra.note_properties phi0 [("Implication", [rule'])]
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.NORMAL 90 ([],[]) NONE
                                              [Morphism.thm m rule'])
  end

val inhabitance = accept_one "Implication" gen_inhab


end
