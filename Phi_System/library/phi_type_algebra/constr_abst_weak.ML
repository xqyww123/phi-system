(* The file provides a very weak implementation for deriving \<open>MAKE_from_RAW\<close> property,
   as currently I still have no good ideas to make it.  *)

signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val Make_Abstraction_from_Raw : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property (phi:phi_type) ctxt =
  let val ((x_Term, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))

      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term

      val x_types = map (fn ((rev_arg_tys,x,_),_) => rev rev_arg_tys ---> x) T_params
      val c_types = map (fn ((rev_arg_tys,_,m),_) => rev rev_arg_tys ---> m) T_params
      val x_fixes = Name.invent_names (Variable.names_of ctxt) "x" x_types
      val c_fixes = Name.invent_names (Variable.names_of ctxt) "c" c_types
      val ctxt = Variable.add_fixes_direct (map fst x_fixes @ map fst c_fixes) ctxt
      val fixes = map2 (fn x => fn c => (Free x, Free c)) x_fixes c_fixes

      fun mk_prop (x_term, c_term) ((rev_arg_tys, x_ty, model_ty), T_term) =
        let val arity = length rev_arg_tys
            val x'_term = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_arg_tys x_term
            val c'_term = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_arg_tys c_term
            val T'_term = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_arg_tys T_term
         in \<^Const>\<open>Transformation model_ty\<close>
              $ (\<^Const>\<open>\<phi>Type model_ty model_ty\<close> $ c'_term $ \<^Const>\<open>Itself model_ty\<close>)
              $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ x'_term $ T'_term)
              $ \<^Const>\<open>True\<close>
         |> fold (fn T => fn X => HOLogic.all_const T $ Abs ("A", T, X)) rev_arg_tys
        end

      val ants = map2 mk_prop fixes T_params
      val idx = phi_maxidx_of phi ~1 + 1
      val prop = mk_prop (Var(("x",idx), x_ty), Var(("c",idx), model_ty))
                         (([], x_ty, model_ty), T_term)
   in Seq.single (ants, HOLogic.Trueprop $ prop,
                  NONE :: parse_parameters_of_phi_type T_term, phi, ctxt)
  end

fun gen_constr_from_raw (_,name) hint0 ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (
            fn (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) $ _)
                 => T
             | X => X
          )

      fun extract_oprs_from_hint
           (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ fx $ _) $ _ ) = [fx]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (
            fn _ => fn _ => Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_noact},
            fn ctxt => fn phi =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_noact} then_conv
                Conv.implies_concl_conv (Phi_Syntax.transformation_conv
                  Conv.all_conv
                  (let val sctxt = Expansion.equip ctxt addsimps (#equations phi)
                    in Phi_Reasoners.asm_rewrite false sctxt
                   end)
                  Conv.all_conv
                ))

      val mode_infer = not (is_some hint0)

      fun reasoning phi ctxt =
            default_reasoning false
              (default_reasoning_configure [])
              varify_all_vars
              (exhaustive_PLPR_reasoner_by_rule @{thm' transformation_weaken[where P'=True, simplified]}
                                                (K (chk_unfolded' ctxt phi)))
              ctxt

      fun solver (phi, ctxt, sequent) =
        if mode_infer then
          let val sctxt = Simplifier.add_cong @{thm HOL.conj_cong} ctxt
                          addsimps [@{thm special_Ex_def}]
           in SOME (sequent
           |> Conv.gconv_rule (HOLogic.Trueprop_conv (
                Conv.rewr_conv @{lemma \<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> P \<equiv> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close>
                                    by (unfold Premise_def) } then_conv
                Simplifier.rewrite sctxt
              )) 1
           |> Thm.permute_prems 0 ~1)
          end
        else NONE


      (*val ctxt0' = if is_some hint0 then ctxt0
                   else Config.put Phi_Reasoners.existential_obligation 2 ctxt0 *)
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property, @{thm' \<phi>TA_TrCstr_rule},
                                      [(SOME ([0,~1], ind_conv), reasoning)],
                                      solver, K I)
                                    phi0 hint0 ctxt0
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80
                                              ([],[]) NONE [Morphism.thm m rule])
        |> note_properties_s phi0 [(name, [rule])]
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val Make_Abstraction_from_Raw = deriver_framework
      (ACCEPT_ONE_HINT, ONLY_ONCE, "Make_Abstraction_from_Raw") gen_constr_from_raw


end