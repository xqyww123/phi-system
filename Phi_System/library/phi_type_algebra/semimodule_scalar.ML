signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val infer_the_default_scalar_domain : Proof.context -> typ * typ * typ -> term
val infer_zip_operator : Proof.context -> typ * typ * typ -> term * term * term
val semimodule_scalar : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun infer_the_default_scalar_domain ctxt (s_ty, x_ty, model_ty) =
  let val g_Sdom = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>guess_domain_of_scalar s_ty model_ty x_ty\<close>
                                        $ \<^Const>\<open>Pure.type s_ty\<close>
                                        $ \<^Const>\<open>Pure.type model_ty\<close>
                                        $ \<^Const>\<open>Pure.type x_ty\<close>
                                        $ Var(("p",0), s_ty --> HOLogic.boolT))
   in Goal.init (Thm.cterm_of ctxt g_Sdom)
   |> Phi_Reasoner.reason NONE true ctxt
   |> (fn SOME ret => (case Thm.prop_of ret
                         of _ (*Pure.prop*) $ (_ (*Trueprop*) $ (_ (*guess_domain_of_scalar*)
                                    $ _ $ _ $ _ $ S)) => S
                          | _ => error "BUG")
        | _ => Abs("_", s_ty, \<^Const>\<open>True\<close>))
  end

fun infer_zip_operator ctxt (s_ty, x_ty, model_ty) =
  let val sequent = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>guess_zip_of_semimodule s_ty model_ty x_ty\<close>
                                        $ \<^Const>\<open>Pure.type s_ty\<close>
                                        $ \<^Const>\<open>Pure.type model_ty\<close>
                                        $ \<^Const>\<open>Pure.type x_ty\<close>
                                        $ Var(("scalar_domain",0), s_ty --> HOLogic.boolT)
                                        $ Var(("abstract_domain",0), s_ty --> s_ty --> \<^Type>\<open>prod x_ty x_ty\<close> --> HOLogic.boolT)
                                        $ Var(("zip", 0), s_ty --> s_ty --> \<^Type>\<open>prod x_ty x_ty\<close> --> x_ty))
   in Goal.init (Thm.cterm_of ctxt sequent)
   |> Phi_Reasoner.reason NONE true ctxt
   |> (fn SOME ret => (case Thm.prop_of ret
                         of _ (*Pure.prop*) $ (_ (*Trueprop*) $ (_ (*guess_zip_of_semimodule*)
                                  $ _ $ _ $ _ $ Ds $ Dx $ z)) => (Ds, Dx, z)
                          | _ => error "BUG")
        | _ => raise Automation_Fail (fn () => let open Pretty in
                  [block (text "Fail to guess the semimodule zip operation as there is no registered \
                               \record giving the semimodule between scalar algebra" @
                          [brk 1, Syntax.pretty_typ ctxt s_ty, brk 1] @
                          text "abstrct algebra" @
                          [brk 1, Syntax.pretty_typ ctxt x_ty, brk 1] @
                          text "and concrete algebra" @
                          [brk 1, Syntax.pretty_typ ctxt model_ty, str ".", brk 1] @
                          text "You may either annotate the form of the rule or provide the record by"),
                   block ([keyword1 "lemma", brk 1, str "[\<phi>reasoner]", brk 1,
                           str "\<open>", Syntax.pretty_term ctxt sequent, str "\<close>"])]
                end))
  end

fun guess_property (phi0 : phi_type) ctxt =
  let val (s_ty, x_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi0 (\<^sort>\<open>type\<close>, \<^sort>\<open>type\<close>)
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term
      (*val ([Dx_name], ctxt) = Variable.add_fixes ["Dx"] ctxt
      val Dx = Free(Dx_name, x_ty --> HOLogic.boolT)
      val AD = \<^Const>\<open>Abstract_Domain\<^sub>M\<^sub>C x_ty model_ty\<close> $ T_term $ Dx*)
      val Ds = infer_the_default_scalar_domain ctxt (s_ty, x_ty, model_ty)
   in Seq.single ([], \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Semimodule_Scalar_Assoc s_ty x_ty model_ty\<close>
                                            $ F_term $ T_term $ Ds (* $ Dx *)),
                  NONE :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end

fun gen_MS (der_id, name) hint0 (phi : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val parse_hint = parse_hint (
              fn (Const(\<^const_name>\<open>Semimodule_Scalar_Assoc\<close>, _) $ F1 $ _ $ _) => F1)
      val extract_oprs_from_hint = K []
      fun reasoning phi =
        default_reasoning false
          (default_reasoning_configure [])
          (K (K NONE))
          (exhaustive_PLPR_reasoner NONE)
      val simp = K I
      val ind_conv = default_ind_conv (
             fn _ => fn _ => Conv.rewr_conv @{thm \<phi>TA_MS_rewr},
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_MS_rewr} then_conv
                  Conv.arg_conv (Conv.arg_conv (Phi_Conv.may_action_tag_conv (
                    let val sctxt = Simps.equip ctxt addsimps (#equations phi @ #type_equations phi)
                     in Phi_Syntax.transformation_conv
                            (Simplifier.rewrite sctxt)
                            (Simplifier.rewrite sctxt)
                            (Conv.all_conv)
                    end))))
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property, @{thm' \<phi>TA_MS_rule},
                                      [(SOME ([0,2,~1,~1], ind_conv), reasoning),
                                       (SOME ([0,2,~1], ind_conv), reasoning)], K NONE, simp)
                                    phi hint0 ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_scalar = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Scalar_Assoc") gen_MS

end