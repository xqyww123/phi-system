signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val meta_Tyops_Commute : bool * int -> quiet * Position.T -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers



(*is_intro: True for applying the inductive destruction on the source, False for on the target*)
fun meta_gen_Tyops_Commute' (is_intro, rule, parse_hint', guess_property)
                            (_, name) instruction (phi0 : phi_type) thy =
  let val Const (const, _) = head_of (HOLogic.dest_Trueprop (Thm.concl_of rule))
      fun extract_oprs_from_hint (C $ D $ r) =
           (case head_of C
              of Const(const', _) => if const = const' then [D,r] else []
               | _ => [])
        | extract_oprs_from_hint _ = []

      val ind_rewr_I = @{lemma' \<open> Trueprop (A \<longrightarrow> B \<longrightarrow> C @tag \<phi>TA_subgoal \<A>)
                             \<equiv> (A \<Longrightarrow> B \<Longrightarrow> C @tag \<A>)\<close>
                          by (unfold atomize_imp Action_Tag_def)}
      val ind_rewr_E_IH = @{lemma' \<open> Trueprop (A \<longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> B \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) @tag \<phi>TA_subgoal undefined)
                                  \<equiv> (\<And>x'. A \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> B \<and> x' = x \<Longrightarrow> (x' \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) @tag \<A>backward_simp)\<close>
                          by (simp add: atomize_imp Action_Tag_def atomize_all Premise_def)}
      val ind_rewr_E_CL = @{lemma' \<open>Trueprop (A \<longrightarrow> B \<longrightarrow> C @tag \<phi>TA_subgoal undefined)
                                  \<equiv> (A \<Longrightarrow> B \<Longrightarrow> C)\<close>
                                by (simp add: atomize_imp Action_Tag_def Bubbling_def atomize_all)}
      val equip_expansion = equip_expansion_ss phi0
      fun gen_ind_conv is_IH ctxt _ ctm = (
            Conv.rewr_conv (if is_intro then ind_rewr_I
                                        else if is_IH then ind_rewr_E_IH
                                                      else ind_rewr_E_CL) then_conv
            (if is_IH then Simplifier.rewrite (Simplifier.clear_simpset ctxt addsimps @{thms' OPEN_def MAKE_def})
                      else Phi_Reasoners.asm_rewrite true (equip_expansion ctxt)) then_conv
            (if not is_intro andalso is_IH then Phi_Conv.meta_all_conv o (fn C => C o snd)
                                           else I) (fn _ =>
            Conv.implies_conv (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<phi>TA_ANT\<close>, symmetric]})) Conv.all_conv
              (*(if not is_intro andalso not is_IH
               then Conv.implies_concl_conv (Phi_Conv.action_tag_conv (
                       Phi_Syntax.transformation_conv Conv.all_conv
                                                      (@{print} o Phi_Reasoners.tag_having_bubbling ctxt)
                                                      Conv.all_conv))
               else Conv.all_conv)*)) ctxt) ctm
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
        if is_some (#1 instruction) then I
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
                   let val bads = [\<^const_name>\<open>OPEN\<close>, \<^const_name>\<open>MAKE\<close>]
                       fun chk 0 (Const(\<^const_name>\<open>times\<close>, _) $ X1 $ X2) =
                              (chk_unfolded bads ctxt phi X1; chk_unfolded bads ctxt phi X2)
                         | chk 0 X = chk_unfolded bads ctxt phi X
                         | chk _ _ = ()
                    in if is_intro
                    then exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__simp} chk ctxt sequent
                    else exhaustive_PLPR_reasoner NONE chk ctxt sequent
                   end) phi ctxt

      val rules = deriving_framework (name, parse_hint parse_hint', extract_oprs_from_hint, guess_property, rule,
                                     [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning is_intro)],
                                     K NONE, K I, simp)
                                    phi0 instruction thy
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> note_properties_s false phi0 [(name, [rule'])]
        |> Local_Theory.declaration {syntax=false, pervasive=false, pos= #3 instruction} (
            fn m => fn lthy => lthy
              |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
              |> Phi_Reasoner.add_rule (#3 instruction) Phi_Reasoner.TO_BE_OVERRIDE'
                                   (SOME (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                      (#2 instruction)))
                                   ([],[]) NONE [Morphism.thm m rule']
              |> Config.restore_generic Phi_Reasoner.trace lthy)
        |> pair [rule']
  end

fun meta_gen_Tyops_Commute reversed ctxt (phi : phi_type) =
  let val (rev_args, x_ty, c_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
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
      val (arity, fixed_param_tys) = calc_arity 0 rev_args
      val idx = maxidx_of_phi phi ~1
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

      val name = Binding.name_of (#name phi) ^ "_Comm"
      val name = if reversed then (name ^ "\<^sub>E", name ^ "\<^sub>I")
                             else (name ^ "\<^sub>I", name ^ "\<^sub>E")

      val deriving = (deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, fst name)
                          (meta_gen_Tyops_Commute' (true , fst rule, fst parse_hint, fst guess_property)),
                      deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, snd name)
                          (meta_gen_Tyops_Commute' (false , snd rule, snd parse_hint, snd guess_property)))

      val deriver = apply2 (fn der => {priority = @{priority %derived_commutativity_deriver},
                                       dependences = [],
                                       derive= der}) deriving

      val binding = Binding.qualify true (Binding.name_of (#name phi)) (Binding.make ("Comm", #pos phi))

   in (binding, deriver, pattern)
  end

(*mode: 1 = only generates introduction deriver
        2 = only generates elimination deriver
        3 = generates both derivers*)
fun meta_Tyops_Commute (reversed,mode) (quiet,pos) (phi : phi_type) thy =
  let val (binding, deriver, pattern) = meta_gen_Tyops_Commute reversed thy phi
      val (binding_I, binding_E) = if reversed
            then (Binding.suffix_name "\<^sub>E" binding, Binding.suffix_name "\<^sub>I" binding)
            else (Binding.suffix_name "\<^sub>I" binding, Binding.suffix_name "\<^sub>E" binding)

      val (gen_I, gen_E) = case mode of 1 => (true, false)
                                      | 2 => (false, true)
                                      | 3 => (true, true)
                                      | _ => error "bad mode"

      fun report (name, thy) = (
            if quiet then () else 
            Phi_Reasoner.info_pretty thy 0 (fn () => let open Pretty in
              block (text "Deriver for \<phi>-Type Operator Commutativity :" @
                     [brk 1, Name_Space.pretty thy (Name_Space.space_of_table
                                  (deriver_name_space (Context.Proof thy))) name])
            end) ;
            (name, thy)
          )
      fun bind pat (name, thy) = (name,
            Local_Theory.declaration {syntax=false, pervasive=false, pos=pos} (fn _ =>
                Phi_Type.bind_derivers_on_patterns [(pat, name)]) thy)

      val (intro_deriver, thy) = ("", thy)
            |> gen_I ? (snd
                #> define_deriver binding_I (fst deriver)
                #> report
                #> bind (fst pattern))

      val (elim_deriver, thy) = ("", thy)
            |> gen_E ? (snd
                #> define_deriver binding_E (snd deriver)
                #> report
                #> bind (snd pattern))

      val combined_deriver = {priority = @{priority %derived_commutativity_deriver+1},
                              dependences = [(intro_deriver, false), (elim_deriver, false)],
                              derive= K (K (K I))}
   in thy
   |> mode = 3 ? (
          define_deriver binding combined_deriver
       #> report
       #> snd )
  end

end
