signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val inhabitance : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*** Inhabitance ***)

fun guess_property_inhab_tyop (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (rev_arg_tys,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
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
         NONE :: parse_parameters_of_phi_type T_term, phi, ctxt))
  end

fun guess_property_inhab_atom (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (_,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val idx = phi_maxidx_of phi ~1 + 1
      val Prop = HOLogic.Trueprop $ (HOLogic.all_const x_ty $ Abs ("x", x_ty, \<^Const>\<open>Action_Tag\<close>
                    $ (\<^Const>\<open>HOL.implies\<close>
                        $ (\<^Const>\<open>Inhabited model_ty\<close> $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ T_term))
                        $ (Var(("Pr",idx), x_ty --> HOLogic.boolT) $ Bound 0))
                    $ \<^Const>\<open>\<A>EIF\<close>))
   in Seq.single ([], Prop, NONE :: parse_parameters_of_phi_type T_term, phi, ctxt)
  end

val NAME = "Implication"
fun gen_inhab (der_id, name) hint00 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val hint0 = Option.map (chk_abstract_object_quantified (
            let fun target (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = target X
                  | target (Const(\<^const_name>\<open>HOL.implies\<close>, _)
                              $ (Const(\<^const_name>\<open>Inhabited\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ X $ T))
                              $ _) =
                        if Term.exists_subterm (fn x => x = X) T
                        then error "Fail to infer the implication when the \<phi>-type depends on its abstract object."
                        else SOME X
             in target
            end
            ) ctxt0) hint00

      val guess_property = if is_Type_Opr (Term.fastype_of (#term phi0))
                           then guess_property_inhab_tyop
                           else guess_property_inhab_atom
      val mode_infer = not (is_some hint0 orelse is_Type_Opr (Term.fastype_of (#term phi0)))

      val parse_hint = parse_hint_has_object_and_type (
            fn Const(\<^const_name>\<open>HOL.All\<close>, _) $ (Abs (_,_,
                  Const(\<^const_name>\<open>Action_Tag\<close>, _) $ 
                    (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ (
                       Const(\<^const_name>\<open>Inhabited\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T)) $ _)
                    $ _ ))
                 => (x,T))
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ P) = [P]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (K (K (fn ctm => Conv.rewr_conv @{thm' \<phi>TA_Inh_rewr} ctm)),
              fn ctxt => fn _ => fn ctm =>
                 (Conv.rewr_conv @{thm' \<phi>TA_Inh_rewr} then_conv
                  Conv.implies_concl_conv (HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                    Conv.arg1_conv (Conv.arg_conv (
                      Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)))))))) ctm)

      fun varify_subgoal _ (Trueprop $ (Action_Tag $ (Imp $ S $ P) $ AEIF)) =
            SOME ([P], fn [P'] => Trueprop $ (Action_Tag $ (Imp $ S $ P') $ AEIF))
        | varify_subgoal _ X = error ""

      val prem_extractions =
        if def_contains_satisfaction phi0
        then [("", Phi_Reasoners.Extract_Rule @{thm' \<phi>TA_Inh_extract_prem})]
        else []

      fun Inh_reasoning phi ctxt =
            default_reasoning false
                (default_reasoning_configure prem_extractions)
                (if mode_infer then varify_subgoal else K (K NONE))
                (exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_Inh_step} (K (chk_unfolded' ctxt phi)))
                ctxt


      val solver =
        if mode_infer
        then (fn (phi,ctxt,sequent) =>
           let fun inst_Pr context (Const(\<^const_name>\<open>conj\<close>, _) $ X $ _)
                      = inst_Pr context X
                 | inst_Pr (vars,prems) (Const(\<^const_name>\<open>All\<close>, _) $ Abs (N,ty,X))
                      = inst_Pr ((N,ty)::vars, map (Term.incr_boundvars 1) prems) X
                 | inst_Pr (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
                      = inst_Pr (vars, P::prems) X
                 | inst_Pr context (Const(\<^const_name>\<open>disj\<close>, _) $ A $ B)
                      = let val (va,ia) = inst_Pr context A
                            val (vb,ib) = inst_Pr context B
                         in if va = vb then (va, \<^Const>\<open>HOL.disj\<close> $ ia $ ib)
                            else raise Automation_Fail (fn () =>
                                  [Pretty.para "Obligation is obtained, but I fail to infer \
                                               \the expression of the implied pure fact from it."])
                        end
                 | inst_Pr (vars,prems) (Var (v as (("Pr",_), \<^Type>\<open>fun tyv _\<close>)) $ Bound j)
                      = Phi_Help.list_mk_conj prems
                          |> fold_index (fn (k, (N, ty)) => fn X =>
                                if k = j then Abs (N, ty, X) $ Bound (length vars - 1 - k)
                                else HOLogic.all_const ty $ Abs(N, ty, X)
                             ) vars
                          |> pair v
            in case Thm.prop_of sequent
                 of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _)
                      $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ X)) $ _
                      => let val (v, X) = inst_Pr ([],[]) X
                             val X = case snd v of \<^Type>\<open>fun tyv _\<close> => Abs ("x", tyv, X)
                                                 | _ => error "BUG GvwRuEdURwyJuFlxjBHOfQ"
                          in SOME (Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt X)]) sequent
                                |> oblg_solver (#proof_id phi ^ "/Inh") ctxt)
                         end
                  | _ => error "Internal bug"
           end)
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
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property, @{thm' \<phi>TA_Inh_rule},
                                      [(SOME ([0], ind_conv), Inh_reasoning)],
                                      solver, simp)
                                     phi0 hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property."])
         | SOME (rule', _) => thy
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.NORMAL_MODE 80 ([],[]) NONE
                                              [Morphism.thm m rule'])
            |> note_properties phi0 [(name, [rule'])]
            |> pair [rule']
  end

val inhabitance = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, NAME) gen_inhab


end
