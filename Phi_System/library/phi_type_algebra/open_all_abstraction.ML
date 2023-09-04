signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val open_all_abstraction : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*Guessing is not supported for recursive \<phi>-types*)

fun guess_property (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val _ = if #is_recursive phi
              then raise Automation_Fail (fn () => [
                      Pretty.para "Fail to guess the rule for a recursive \<phi>-type\
                                  \May manually annotate the expression."])
              else ()
      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term
      fun mk_prop r_term ((rev_arg_tys, x_ty, model_ty), T_term) =
        let val arity = length rev_arg_tys
            val T'_term = fold_index (fn (i,_) => fn X => X $ Bound (arity - i)) rev_arg_tys T_term
         in (HOLogic.all_const x_ty $ Abs ("x", x_ty,
              \<^Const>\<open>Action_Tag\<close>
                $ (\<^Const>\<open>Transformation model_ty\<close>
                    $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ T'_term)
                    $ (\<^Const>\<open>ExSet model_ty model_ty\<close> $ Abs ("y", model_ty,
                          \<^Const>\<open>Subjection model_ty\<close>
                            $ (\<^Const>\<open>\<phi>Type model_ty model_ty\<close> $ Bound 0 $ \<^Const>\<open>Itself model_ty\<close>)
                            $ (r_term $ Bound 1 $ Bound 0)))
                    $ \<^Const>\<open>True\<close>)
                $ (\<^Const>\<open>to model_ty model_ty\<close> $ \<^Const>\<open>Itself model_ty\<close>)))
         |> fold (fn T => fn X => HOLogic.all_const T $ Abs ("A", T, X)) rev_arg_tys
        end
      val r_types = map (fn ((_,x,m),_) => x --> m --> HOLogic.boolT) T_params
      val r_fixes = Name.invent_names (Variable.names_of ctxt) "r" r_types
      val ctxt' = Variable.add_fixes_direct (map fst r_fixes) ctxt
      val ants = map2 (mk_prop o Free) r_fixes T_params 
      val idx = phi_maxidx_of phi ~1 + 1
      val prop = mk_prop (Var(("r",idx), x_ty --> model_ty --> HOLogic.boolT)) (([], x_ty, model_ty), T_term)
   in Seq.single (ants, HOLogic.Trueprop $ prop,
                  NONE :: parse_parameters_of_phi_type T_term, phi, ctxt')
  end

fun reasoning phi ctxt =
  let (*val extract_prem =
        if def_contains_satisfaction phi
        then (fn _ => fn th => [])
        else K (K [])*)
   in default_reasoning false
         (default_reasoning_configure [])
         (K (K NONE))
         (exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__\<A>_simp_NToA} (K (chk_unfolded' ctxt phi)))
         ctxt
  end

fun instantiate_the_var var ctxt sequent =
  let val (x_ty, y_ty) = case snd var
                           of \<^Type>\<open>fun x_ty \<^Type>\<open>fun y_ty \<^Type>\<open>bool\<close>\<close>\<close> => (x_ty, y_ty)
                            | _ => error "BUG qC2wYScnQXiFvdGaUF/mBA"
      val [y] = Name.invent_names (Variable.names_of ctxt) "x" [y_ty]
             |> map Free

      val oblg = case Thm.prop_of sequent
                   of \<^Const>\<open>Pure.imp\<close> $ (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_COLLECT\<close> $ X)) $ _
                        => X
                    | _ => error "BUG zfkezUm3Rm62IQTK0kglKQ"

      fun mk_disj_inst vx concls (quants, prems) =
        let val qlen = length quants
         in fold_index (fn (i,(N,ty)) => fn X =>
                  if vx = i then Abs(N,ty,X) $ Bound (qlen-i)
                            else HOLogic.exists_const ty $ Abs(N,ty,X))
              quants (Phi_Help.list_mk_conj (concls @ prems))
        end

      fun mk_conj_inst concls (quants, prems) =
        Phi_Help.list_mk_conj concls
          |> fold (fn P => fn X => HOLogic.imp $ P $ X) prems
          |> fold (fn (N,ty) => fn X => HOLogic.exists_const ty $ Abs(N,ty,X)) quants
      fun mk_conj_inst' [] _ rets = rets
        | mk_conj_inst' concls qp rets = mk_conj_inst concls qp :: rets

      val has_the_var = Term.exists_subterm (fn Var v' => v' = var | _ => false)

      fun opt_join NONE x = SOME x
        | opt_join (SOME a) b = if a = b then SOME a else error "BUG"
      fun pass_conjs concls_varx (\<^Const>\<open>HOL.conj\<close> $ A $ B)
            = pass_conjs (pass_conjs concls_varx A) B
        | pass_conjs (concls,varx) (Var v' $ vx $ vy)
            = if v' = var
              then case vx of Bound i => ((\<^Const>\<open>HOL.eq y_ty\<close> $ y $ vy) :: concls, opt_join varx i)
                            | _ => ((\<^Const>\<open>HOL.eq y_ty\<close> $ y $ vy) :: concls, varx)
              else error "Phi_Type_Algebra_Derivers.instantiate_the_var: unexpected schematic variables"
        | pass_conjs (concls,meet) P
            = (if has_the_var P
               then raise Automation_Fail (fn () => let open Pretty in
                      [para "fail to infer the transformation relation: fail to normalize the obligation"]
                    end)
               else () ;
               (P::concls, meet))

      fun inst_body ret (quants, prems) (\<^Const>\<open>HOL.implies\<close> $ P $ X)
            = inst_body ret (quants, P::prems) X
        | inst_body ret (quants, prems) (\<^Const>\<open>HOL.All _\<close> $ Abs (N, ty, X))
            = inst_body ret ((N,ty)::quants, map (Term.incr_boundvars 1) prems) X
        | inst_body (disj, conj) qp P
            = case pass_conjs ([],NONE) P
                of (concls, SOME vx)  => (mk_disj_inst vx concls qp :: disj, conj)
                 | (concls, NONE) => (disj, mk_conj_inst' concls qp conj)

      fun assemble_dc (disj,conj) = Phi_Help.list_mk_conj (Phi_Help.list_mk_disj disj :: conj)
      fun final_assemble_dc dc = Abs("x", x_ty, Term.lambda y (assemble_dc dc))

      fun inst (quants, prems) (\<^Const>\<open>HOL.implies\<close> $ P $ X)
            = inst (quants, P::prems) X
        | inst (quants, prems) (\<^Const>\<open>HOL.All _\<close> $ Abs (N, ty, X))
            = inst ((N,ty)::quants, map (Term.incr_boundvars 1) prems) X
        | inst qp (\<^Const>\<open>HOL.conj\<close> $ A $ B)
            = let val (dA,cA) = inst qp A
                  val (dB,cB) = inst qp B
               in (dA@dB, cA@cB)
              end
       | inst qp (\<^Const>\<open>HOL.disj\<close> $ A $ B)
            = let val a = assemble_dc (inst qp A)
                  val b = assemble_dc (inst qp B)
               in ([a,b], [])
              end
        | inst qp (\<^Const>\<open>special_Ex _\<close> $ Abs (_, ty, X))
            = if ty = y_ty
              then inst_body ([],[]) qp (Term.subst_bounds ([y], X))
              else raise Automation_Fail (fn () => [Pretty.str "patch_for_Ex.ML fails to normalize the \<exists>\<^sup>\<phi>\<^sup>-\<^sup>L\<^sup>P\<^sup>R"])
        | inst qp P
            = if has_the_var P
              then inst_body ([],[]) qp P
              else ([], [mk_conj_inst [P] qp])

      val inst = final_assemble_dc (inst ([],[]) oblg)
              |> Thm.cterm_of ctxt
          handle Automation_Fail msg => raise Automation_Fail (fn () => let open Pretty in
                   [block [para "Fail to infer the transformation relation from the obtained proof obligation:",
                           Syntax.pretty_term ctxt oblg]] @
                    msg ()
                  end)
   in Thm.instantiate (TVars.empty, Vars.make [(var, inst)]) sequent
  end


fun chk_quantifier_place (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ A $ B)
      = \<^Const>\<open>Pure.imp\<close> $ chk_quantifier_place A $ chk_quantifier_place B
  | chk_quantifier_place ((H as Const(\<^const_name>\<open>Pure.all\<close>, _)) $ Abs (N,Ty,X))
      = H $ Abs (N,Ty, chk_quantifier_place X)
  | chk_quantifier_place (\<^Const>\<open>Trueprop\<close> $
                           ((H as Const(\<^const_name>\<open>Action_Tag\<close>, _))
                              $ ((H2 as Const(\<^const_name>\<open>HOL.All\<close>, _)) $ Abs (N,Ty,X))
                              $ A))
      = \<^Const>\<open>Trueprop\<close> $ (H2 $ Abs (N, Ty, H $ X $ A))
  | chk_quantifier_place X = X

fun gen_trans_to_raw_abst (_,name) hint00 ctxt0 (phi0 : phi_type) thy =
  let val hint0 = Option.map (chk_quantifier_place
            #> chk_abstract_object_quantified (
            let fun target (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = target X
                  | target (\<^Const>\<open>Transformation _\<close> $ (\<^Const>\<open>\<phi>Type _ _\<close> $ X $ T) $ _ $ _) =
                        if Term.exists_subterm (fn x => x = X) T
                        then error "Fail to infer the implication when the \<phi>-type depends on its abstract object."
                        else SOME X
             in target
            end
            ) ctxt0) hint00

      fun parse_hint ctxt _ hint =
            let fun extract (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = extract X
                  | extract (Const(\<^const_name>\<open>All\<close>, _) $ X) = extract X
                  | extract (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = extract X
                  | extract (Abs (_, _, X)) = extract X
                  | extract (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = extract X
                  | extract (\<^Const>\<open>Action_Tag\<close>
                              $ (\<^Const>\<open>Transformation _\<close>
                                  $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ T)
                                  $ (\<^Const>\<open>ExSet _ _\<close> $ Abs (_, _, (\<^Const>\<open>Subjection _\<close>
                                        $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ itself')
                                        $ _)))
                                  $ _)
                              $ (\<^Const>\<open>to _ _\<close> $ itself))
                      = (T, (itself, itself'))
                val (T', pair) = extract (Logic.strip_imp_concl hint)
                val pairs = pair :: (map (snd o extract) (Logic.strip_imp_prems hint))
                val idx = Term.maxidx_of_term hint
                val env = case Seq.pull (Unify.smash_unifiers (Context.Proof ctxt) pairs (Envir.empty idx))
                            of SOME (env, _) => env
                             | NONE => raise Match
                val hint' = Envir.norm_term env hint
                val T = Envir.norm_term env T'
             in (Term.fastype_of (Term.head_of T), NONE :: parse_parameters_of_phi_type T, hint')
            end
      fun extract_oprs_from_hint (\<^Const>\<open>Transformation _\<close> $ _
                                  $ (\<^Const>\<open>ExSet _ _\<close> $ Abs (_, _, (\<^Const>\<open>Subjection _\<close> $ _ $ r)))
                                  $ _) = [r]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (
            fn _ => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1},
            fn ctxt => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1} then_conv
                Conv.implies_concl_conv (Phi_Conv.action_tag_conv (
                  Phi_Syntax.transformation_conv
                    (Simplifier.rewrite (Expansion.equip ctxt addsimps (#equations phi0)))
                    Conv.all_conv Conv.all_conv)))
      fun simp (_, ctxt) rule = rule
         |> Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt => HOLogic.Trueprop_conv (Phi_Conv.hol_all_conv (fn (_, ctxt) =>
              Phi_Conv.action_tag_conv (Phi_Syntax.transformation_conv Conv.all_conv
                (Phi_Syntax.ExSet_conv (fn (bvar, ctxtxx) =>
                  let val turn_bvar_eq = Drule.infer_instantiate ctxtxx [(("b",0),bvar)] @{thm' HOL.eq_commute}
                   in Phi_Syntax.Subjection_conv Conv.all_conv (
                        Simplifier.rewrite (ctxtxx addsimps [turn_bvar_eq, @{thm special_Ex_def}]
                                              |> Simplifier.add_cong @{thm HOL.conj_cong}))
                  end) ctxt)
                Conv.all_conv)
            ) ctxt)) ctxt)
         |> (fn rule => (rule RS' (ctxt, @{thm' spec})))

      fun solver (phi, ctxt, sequent) =
            case Thm.concl_of sequent
              of _ (*Trueprop*) $ (\<^Const>\<open>All _\<close> $ Abs (_, _, \<^Const>\<open>Action_Tag\<close> $
                     (\<^Const>\<open>Transformation _\<close> $ _
                         $ (\<^Const>\<open>ExSet _ _\<close> $ Abs (_, _,
                             \<^Const>\<open>Subjection _\<close> $ _ $ X ))
                         $ _)
                     $ _))
                   => (case X of Var v $ _ $ _ =>
                                    SOME ( instantiate_the_var v ctxt sequent
                                      |> oblg_solver (#proof_id phi ^ "/" ^ name) ctxt)
                               | _ => NONE)
               | _ => error "BUG"


      val ctxt0' = if is_some hint0 then ctxt0
                   else Config.put Phi_Reasoners.existential_obligation 2 ctxt0
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property, @{thm' \<phi>TA_TrRA_rule},
                                      [(SOME ([0], ind_conv), reasoning)],
                                      solver, simp)
                                    phi0 hint0 ctxt0'
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80
                                              ([],[]) NONE [Morphism.thm m rule])
        |> note_properties_s phi0 [(name, [rule])]
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val open_all_abstraction = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Open_Abstraction_to_Raw") gen_trans_to_raw_abst

end

