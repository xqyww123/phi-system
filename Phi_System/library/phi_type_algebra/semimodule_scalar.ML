signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_assoc_I : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val semimodule_assoc_E : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers


(*
fun infer_the_default_scalar_domain ctxt (s_ty, x_ty, model_ty) =
  let val g_Sdom = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>guess_domain_of_scalar s_ty model_ty x_ty\<close>
                                        $ \<^Const>\<open>Pure.type s_ty\<close>
                                        $ \<^Const>\<open>Pure.type model_ty\<close>
                                        $ \<^Const>\<open>Pure.type x_ty\<close>
                                        $ Var(("p",0), s_ty --> HOLogic.boolT))
   in Goal.init (Thm.cterm_of ctxt g_Sdom)
   |> Phi_Reasoner.reason NONE NONE ctxt
   |> (fn SOME ret => (case Thm.prop_of ret
                         of _ (*Pure.prop*) $ (_ (*Trueprop*) $ (_ (*guess_domain_of_scalar*)
                                    $ _ $ _ $ _ $ S)) => S
                          | _ => error "BUG")
        | _ => Abs("_", s_ty, \<^Const>\<open>True\<close>))
  end
*)
(*
fun Guess_Scalar_Assoc is_intro (phi : phi_type) ctxt =
  let val (s_ty, x_ele_ty, x_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi NONE
      val idx = maxidx_of_phi phi ~1 + 1
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term

      val (ss, st) = (TVar (("s\<^sub>s", idx), \<^sort>\<open>type\<close>), TVar (("s\<^sub>t", idx), \<^sort>\<open>type\<close>))
      val (at, as_t) = (TVar (("a\<^sub>t", idx), \<^sort>\<open>type\<close>), TVar (("a\<^sub>s\<^sub>_\<^sub>t", idx), \<^sort>\<open>type\<close>))
      val (Fs, Ft) = (Var (("F\<^sub>s", idx), ss --> mk_phi_type_ty(model_ty, at) --> mk_phi_type_ty(model_ty, as_t)),
                      Var (("F\<^sub>t", idx), st --> mk_phi_type_ty(model_ty, x_ele_ty) --> mk_phi_type_ty(model_ty, at)))
      val eta_F_term = Abs ("s", s_ty, Abs ("T", Term.fastype_of T_term, Abs ("x", x_ty,
                          \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ (Term.incr_boundvars 3 F_term $ Bound 2 $ Bound 1))))
      val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Scalar_Assoc s_ty model_ty x_ele_ty x_ty ss at as_t st\<close>
                $ (if is_intro then \<^Const>\<open>True\<close> else \<^Const>\<open>False\<close>)
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ele_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ Fs $ Ft $ F_term $ eta_F_term $ T_term
                $ Var(("Ds",0), ss --> HOLogic.boolT)
                $ Var(("Dt",0), st --> HOLogic.boolT)
                $ Var(("Dx",0), ss --> st --> as_t --> HOLogic.boolT)
                $ Var(("smul",0), ss --> st --> s_ty)
                $ Var(("f", 0), ss --> st --> as_t --> x_ty)
                $ Var(("antecedents", 0), HOLogic.boolT)
                $ Var(("conditions", 0), HOLogic.boolT))
      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 7 Conv.fun_conv (Conv.arg1_conv (
                      Conv.abs_conv (Conv.abs_conv (Conv.abs_conv (fn (_, ctxt) =>
                      fn ctm => Conv.rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                           (#equations phi)) ctm) o snd) o snd) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
   of SOME (inst, ret) =>
        (case Thm.prop_of ( ret
                         |> Simplifier.simplify (ctxt addsimps
                                @{thms' Premise_norm[where mode=\<open>default\<close>]
                                        Premise_norm[where mode=\<open>MODE_GUARD\<close>]
                                        Ant_Seq_reduct
                                        HOL.imp_conjR[folded Ant_Seq_def]
                                        HOL.all_conj_distrib[folded Ant_Seq_def]}) )
           of _ (*Trueprop*) $ (_ (*Guess_Scalar_Assoc*) $ _ $ _ $ _ $ _ $ _
                    $ Fs $ Ft $ Fc $ _ $ T $ Ds $ Dt $ Dx $ smul $ f $ ants $ conds)
                => let val ants = constrain_antecedents conds ants
                       val \<^Type>\<open>fun ss' \<^Type>\<open>fun st' \<^Type>\<open>fun as_t' ast'\<close>\<close>\<close> = Term.fastype_of f
                       val \<^Type>\<open>fun _ \<^Type>\<open>fun \<^Type>\<open>fun a' \<open>Type(_, [c'])\<close>\<close> \<^Type>\<open>fun at' _\<close>\<close>\<close> = Term.fastype_of Ft
                       val \<^Type>\<open>fun sc' _\<close> = Term.fastype_of Fc
                       val head = if is_intro then \<^Const>\<open>Module_Assoc\<^sub>I ss' at' c' as_t' st' a' sc' ast'\<close>
                                              else \<^Const>\<open>Module_Assoc\<^sub>E ss' at' c' as_t' st' a' sc' ast'\<close>
                       val prop = HOLogic.Trueprop $ (head $ Fs $ Ft $ Fc $ T $ Ds $ Dt $ Dx $ smul $ f)
                    in Seq.single (ants, prop,
                                   NONE :: parse_inst_params_from_phi_term (Fc $ Term.dummy $ T),
                                   instantiate_phi (inst, Vars.empty) phi,
                                   ctxt)
                   end
            | _ => error "BUG")
    | NONE => guess_fail ctxt phi (K [])
  end
*)
(*
fun guess_property is_intro (phi0 : phi_type) ctxt =
  let val (s_ty, x_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi0 (\<^sort>\<open>type\<close>, \<^sort>\<open>sep_carrier\<close>)
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term
      (*val ([Dx_name], ctxt) = Variable.add_fixes ["Dx"] ctxt
      val Dx = Free(Dx_name, x_ty --> HOLogic.boolT)
      val AD = \<^Const>\<open>Abstract_Domain\<^sub>M\<^sub>C x_ty model_ty\<close> $ T_term $ Dx*)
      val Ds = infer_the_default_scalar_domain ctxt (s_ty, x_ty, model_ty)
   in Seq.single ([], \<^Const>\<open>Trueprop\<close> $ (xxxx (*(if is_intro then \<^Const>\<open>Module_Assoc\<^sub>I s_ty x_ty model_ty\<close>
                                                      else \<^Const>\<open>Module_Assoc\<^sub>E s_ty x_ty model_ty\<close>)*)
                                            $ F_term $ T_term $ Ds (* $ Dx *)),
                  NONE :: parse_inst_params_from_phi_term FT_term, phi, ctxt)
  end
*)

fun gen_MS is_intro (_, name) instruction (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (
            fn (Const(\<^const_name>\<open>Module_Assoc\<^sub>I\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _) => F1
             | (Const(\<^const_name>\<open>Module_Assoc\<^sub>E\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _) => F1
          )
      val extract_oprs_from_hint = K []
      fun reasoning phi ctxt =
        default_reasoning false default_reasoning_configure (K (K NONE))
                          (exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))) phi ctxt
      val simp = K I

      val equip_expansion = equip_expansion_ss phi0
      val eqs = map Phi_Syntax.wrap_equation_by_OPEN (#equations phi0)
              @ map_filter (Option.map  Phi_Syntax.wrap_equation_by_OPEN) (#type_equations phi0)
              @ map Phi_Syntax.wrap_equation_by_MAKE (#equations phi0)
              @ map_filter (Option.map Phi_Syntax.wrap_equation_by_MAKE) (#type_equations phi0)
      val ind_conv = default_ind_conv (
             fn ctxt => fn _ =>
                  Conv.rewr_conv (if is_intro then @{thm' \<phi>TA_MS\<^sub>I_rewr_IH}
                                              else @{thm' \<phi>TA_common_rewr_imp2_noact}) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                                    (Conv.bottom_rewrs_conv @{thms' OPEN_def MAKE_def} ctxt),
             fn ctxt => fn _ =>
                  Conv.rewr_conv TA_common_rewr_imp2_noact then_conv
                  Phi_Reasoners.asm_rewrite true (equip_expansion ctxt addsimps eqs) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                                    (Phi_Conv.meta_alls_conv (fn ctxt =>
                                        conv_hol_imps_to_metas_if_has Conv.all_conv Conv.all_conv
                                     ) ctxt))
                                   
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      Guess_Scalar_Assoc is_intro,
                                      (if is_intro then @{thm' \<phi>TA_MS\<^sub>I_rule} else @{thm' \<phi>TA_MS\<^sub>E_rule}),
                                      [(SOME (if is_intro
                                              then default_ind_inst (fn [_,_,_,r,x] => [SOME r, NONE, SOME x])
                                              else default_ind_inst (fn [_,_,r,x] => [SOME r, NONE, SOME x]),
                                              K I),
                                        ind_conv, reasoning)],
                                      K NONE, K I, simp)
                                    phi0 instruction thy
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Local_Theory.declaration {syntax=false, pervasive=false, pos= #3 instruction} (
            fn m => fn lthy => lthy
              |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
              |> Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE'
                                       (SOME (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                          (#2 instruction)))
                                       ([],[]) NONE [Morphism.thm m rule']
              |> Config.restore_generic Phi_Reasoner.trace lthy)
        |> note_properties_s false phi0 [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_assoc_I = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Module_Assoc\<^sub>I") (gen_MS true)

val semimodule_assoc_E = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Module_Assoc\<^sub>E") (gen_MS false)

end