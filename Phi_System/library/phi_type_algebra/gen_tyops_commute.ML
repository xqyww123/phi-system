signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val meta_Tyops_Commute : bool * int -> quiet -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers



(*is_intro: True for applying the inductive destruction on the source, False for on the target*)
fun meta_gen_Tyops_Commute' (is_intro, rule, parse_hint', guess_property)
                            (_, name) instruction ctxt0 (phi0 : phi_type) thy =
  let val Const (const, _) = head_of (HOLogic.dest_Trueprop (Thm.concl_of rule))
      fun extract_oprs_from_hint (C $ D $ r) =
           (case head_of C
              of Const(const', _) => if const = const' then [D,r] else []
               | _ => [])
        | extract_oprs_from_hint _ = []

      val simps = map Phi_Syntax.wrap_equation_by_OPEN (#equations phi0)
                @ map_filter (Option.map  Phi_Syntax.wrap_equation_by_OPEN) (#type_equations phi0)
                @ map Phi_Syntax.wrap_equation_by_MAKE (#equations phi0)
                @ map_filter (Option.map Phi_Syntax.wrap_equation_by_MAKE) (#type_equations phi0)
      val ind_rewr = @{lemma' \<open> Trueprop (A \<longrightarrow> B \<longrightarrow> C @action \<phi>TA_ind_target \<A>)
                             \<equiv> (A \<Longrightarrow> B \<Longrightarrow> C @action \<A>)\<close>
                          by (unfold atomize_imp Action_Tag_def)}
      val ind_rewr_E_CL = @{lemma' \<open>Trueprop (A \<longrightarrow> B \<longrightarrow> (x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> (F T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) @action \<phi>TA_ind_target \<A>)
                                  \<equiv> (A \<Longrightarrow> B \<Longrightarrow> (x \<Ztypecolon> F T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) @action NToA)\<close>
                                by (unfold atomize_imp Action_Tag_def Bubbling_def)}
      fun gen_ind_conv is_IH ctxt _ = @{print} o
            Conv.rewr_conv (if not is_intro andalso not is_IH then ind_rewr_E_CL else ind_rewr) then_conv
            (if is_IH then Simplifier.rewrite (Simplifier.clear_simpset ctxt addsimps @{thms' OPEN_def MAKE_def})
             else Phi_Reasoners.asm_rewrite true (Expansion.equip ctxt addsimps simps)) then_conv
            Conv.implies_conv (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<phi>TA_ANT\<close>, symmetric]}))
              (if not is_intro andalso not is_IH
               then Conv.implies_concl_conv (Phi_Conv.action_tag_conv (
                       Phi_Syntax.transformation_conv Conv.all_conv
                                                      (Simplifier.rewrite (Tag_Has_Bubbling.equip ctxt))
                                                      Conv.all_conv))
               else Conv.all_conv)
      val ind_conv = default_ind_conv (gen_ind_conv true, gen_ind_conv false)
      (*val ind_conv = default_ind_conv (
            fn ctxt => fn _ =>
                Conv.rewr_conv @{lemma \<open>A \<longrightarrow> B \<longrightarrow> C \<equiv> (A \<Longrightarrow> B \<Longrightarrow> C)\<close> by blast} then_conv
                Phi_Reasoners.asm_rewrite true (
                    Expansion.equip ctxt addsimps (@{thm' \<phi>TA_ind_target_strip} :: #equations phi0)),
            fn ctxt => fn _ =>
                Phi_Conv.meta_alls_conv (fn ctxt => fn ctm => Conv.implies_concl_conv (
                  Phi_Reasoners.asm_rewrite true (
                      Expansion.equip ctxt addsimps (@{thm' \<phi>TA_ind_target_strip} :: #equations phi0))
                ) ctm) ctxt
            )
      val ind_conv_E = default_ind_conv (
            fn ctxt => fn _ =>
                Phi_Conv.meta_alls_conv (fn ctxt => Conv.implies_concl_conv (
                  Phi_Reasoners.asm_rewrite true (
                      Expansion.equip ctxt addsimps (@{thm' Action_Tag_def} :: #equations phi0))
                )) ctxt,
            fn ctxt => fn _ =>
                Phi_Conv.meta_alls_conv (fn ctxt => Conv.implies_concl_conv (
                  Phi_Reasoners.asm_rewrite true (
                      Expansion.equip ctxt addsimps (@{thm' Action_Tag_def} :: #equations phi0))
                )) ctxt
            )*)

      fun simp (_, ctxt) =
        if is_some instruction then I
        else Conv.fconv_rule (
               Phi_Conv.hhf_concl_conv (fn ctxt =>
                 let val sctxt = ctxt addsimps @{thms special_Ex_def}
                  in HOLogic.Trueprop_conv (Conv.combination_conv
                        (Conv.arg_conv (Simplifier.rewrite sctxt))
                        (Simplifier.rewrite sctxt))
                 end
             ) ctxt)

      fun reasoning is_intro phi ctxt =
            default_reasoning true
                default_reasoning_configure
                (K (K NONE))
                (fn ctxt => fn sequent =>
                   let fun chk 0 (Const(\<^const_name>\<open>times\<close>, _) $ X1 $ X2) = (chk_unfolded' ctxt phi X1; chk_unfolded' ctxt phi X2)
                         | chk 0 X = chk_unfolded' ctxt phi X
                         | chk _ _ = ()
                    in if is_intro
                    then exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__simp_NToA} chk ctxt sequent
                    else exhaustive_PLPR_reasoner NONE chk ctxt sequent
                   end) phi ctxt

      val rules = deriving_framework (name, parse_hint parse_hint', extract_oprs_from_hint, guess_property, rule,
                                     [(K (SOME (if is_intro then [0] else [0,~1])), ind_conv, reasoning is_intro)],
                                     K NONE, simp)
                                    phi0 (Option.map fst instruction) ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> note_properties_s phi0 [(name, [rule'])]
        |> Phi_Help.generic_theory_mapping (fn m =>
             Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE
                                   (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                 (Option.mapPartial snd instruction))
                                   ([],[]) NONE [Morphism.thm m rule'])
        |> pair [rule']
  end

fun meta_gen_Tyops_Commute reversed ctxt (phi : phi_type) =
  let val (rev_argtys, x_ty, c_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun calc_arity arity (argty :: rev_argtys) =
           (case try dest_parameterized_phi_ty argty
              of SOME ([], _, _) =>
                  if arity = 2
                  then ( warning "In deriving commutativity of \<phi>-type operators, we only support type \
                                 \operators of arity upto 2 right now." ;
                         (2, argty :: rev_argtys) )
                  else calc_arity (arity + 1) rev_argtys
               | NONE => (arity, argty :: rev_argtys))
        | calc_arity arity [] = (arity, [])
      val (arity, fixed_param_tys) = calc_arity 0 rev_argtys
      val idx = phi_maxidx_of phi ~1
      val F_term = fold_index (fn (i,(ty, N)) => fn X => X $ Var((N, i+idx), ty))
                              (rev fixed_param_tys ~~ map (the_default "A" o #name)
                                                          (List.take (#params phi, length fixed_param_tys)))
                              (#term phi)
      val F_cterm = Thm.cterm_of ctxt F_term

      val guess_property = gen_Guess_Tyops_Commute (F_term, arity)

      val parse_hint = case arity
            of 1 => (fn Const(\<^const_name>\<open>Tyops_Commute\<close>, _) $ G $ _ $ _ $ _ $ _ $ _ $ _ => G,
                     fn Const(\<^const_name>\<open>Tyops_Commute\<close>, _) $ _ $ _ $ G $ _ $ _ $ _ $ _ => G)
             | 2 => (fn Const(\<^const_name>\<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2\<close>, _) $ G $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _ => G,
                     fn Const(\<^const_name>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1\<close>, _) $ G $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _ => G)
             | _ => error "Unsupported arity"

      val rule = case arity
            of 1 => (@{thm' \<phi>TA_TyComm\<^sub>I_gen}, @{thm' \<phi>TA_TyComm\<^sub>E_gen})
             | 2 => (@{thm' \<phi>TA_TyComm\<^sub>2\<^sub>_\<^sub>1\<^sub>I_gen}, @{thm' \<phi>TA_TyComm\<^sub>2\<^sub>_\<^sub>1\<^sub>E_gen})
             | _ => error "Unsupported arity"
      val idx_F = Thm.maxidx_of_cterm F_cterm + 1
      val rule = apply2 (Drule.infer_instantiate ctxt [(("F",idx_F),F_cterm)] o Thm.incr_indexes idx_F) rule

      fun gen_rule th = case Phi_Reasoner.reason NONE NONE ctxt th
                          of SOME ret => ret
                           | NONE => raise Automation_Fail (fn () => [Pretty.str "\<phi>-LPR fails"])
      val rule = apply2 gen_rule rule |> @{print}

      val pattern = apply2 Thm.concl_of rule

      val name = Term.term_name (#term phi) ^ "_Comm"
      val name = if reversed then (name ^ "\<^sub>E", name ^ "\<^sub>I")
                             else (name ^ "\<^sub>I", name ^ "\<^sub>E")

      val deriving = (deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, fst name)
                          (meta_gen_Tyops_Commute' (true , fst rule, fst parse_hint, fst guess_property)),
                      deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, snd name)
                          (meta_gen_Tyops_Commute' (false , snd rule, snd parse_hint, snd guess_property)))

      val deriver = apply2 (fn der => {priority = @{priority %derived_commutativity_deriver},
                                       dependences = [],
                                       derive= der}) deriving

      val binding = Binding.qualify true (Term.term_name (#term phi)) (Binding.make ("Comm", #pos phi))

   in (binding, deriver, pattern)
  end

(*mode: 1 = only generates introduction deriver
        2 = only generates elimination deriver
        3 = generates both derivers*)
fun meta_Tyops_Commute (reversed,mode) quiet ctxt (phi : phi_type) thy =
  let val (binding, deriver, pattern) = meta_gen_Tyops_Commute reversed ctxt phi
      val (binding_I, binding_E) = if reversed
            then (Binding.suffix_name "\<^sub>E" binding, Binding.suffix_name "\<^sub>I" binding)
            else (Binding.suffix_name "\<^sub>I" binding, Binding.suffix_name "\<^sub>E" binding)

      val (gen_I, gen_E) = case mode of 1 => (true, false)
                                      | 2 => (false, true)
                                      | 3 => (true, true)
                                      | _ => error "bad mode"

      fun report (name, thy) = (
            if quiet then () else 
            Phi_Reasoner.info_pretty_generic thy 0 (fn () => let open Pretty in
              block (text "Deriver for \<phi>-Type Operator Commutativity :" @
                     [brk 1, Name_Space.pretty ctxt (Name_Space.space_of_table (deriver_name_space thy)) name])
            end) ;
            (name, thy)
          )
      fun bind pat (name, thy) = (name, Phi_Type_Algebra.bind_derivers_on_patterns [(pat, name)] thy)

      val (intro_deriver, thy) = ("", thy)
            |> gen_I ? (snd
                #> Context.mapping_result (define_deriver_global binding_I (fst deriver))
                                          (define_deriver binding_I (fst deriver))
                #> report
                #> bind (fst pattern))

      val (elim_deriver, thy) = ("", thy)
            |> gen_E ? (snd
                #> Context.mapping_result (define_deriver_global binding_E (snd deriver))
                                          (define_deriver binding_E (snd deriver))
                #> report
                #> bind (snd pattern))

      val combined_deriver = {priority = @{priority %derived_commutativity_deriver+1},
                              dependences = [(intro_deriver, false), (elim_deriver, false)],
                              derive= K (K (K (K I)))}
   in thy
   |> mode = 3 ? (
          Context.mapping_result (define_deriver_global binding combined_deriver)
                                 (define_deriver binding combined_deriver)
       #> report
       #> snd )
  end

end
