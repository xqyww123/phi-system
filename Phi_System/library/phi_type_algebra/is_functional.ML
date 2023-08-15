signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val is_functional : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property (phi:phi_type) ctxt =
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
      val ants = map2 (fn ((rev_args, x, m), T'h) => fn (_, pred) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_args T'h
             in \<^Const>\<open>Functionality x m\<close> $ T' $ pred
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params preds
      val idx = phi_maxidx_of phi ~1 + 1
      val Pvar = Var(("P",idx), x_ty --> HOLogic.boolT)
   in guess_predicate ctxt preds x_ty
   |> Seq.map (fn (pred, ctxt) =>
        (ants, HOLogic.Trueprop $ (\<^Const>\<open>Functionality x_ty model_ty\<close> $ T_term $
                  (Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (Pvar $ Bound 0) $ (pred $ Bound 0)))),
         NONE :: parse_parameters_of_phi_type T_term, phi, ctxt))
  end

fun solver name (phi,ctxt,sequent) =
  let fun err () = raise Automation_Fail (fn () =>
                        [Pretty.para "Obligation is obtained, but I fail to infer \
                                     \the expression of the implied pure fact from it."])
      val var = case Thm.concl_of sequent
                  of _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $ Var v) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Var v $ Bound 0) $ _)) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ Var v $ _)) => v
                   | _ => err ()

      fun binop H (SOME sa, SOME sb) = SOME (H $ sa $ sb)
        | binop _ (some_or_none, NONE) = some_or_none
        | binop _ (NONE, some) = some
      fun quantifies j vars =
             fold_index (fn (k, (N, ty)) => fn X =>
                if k = j then Abs (N, ty, X) $ Bound (length vars - 1 - k)
                else HOLogic.all_const ty $ Abs(N, ty, X)
             ) vars

      fun inst_Lw context (Const(\<^const_name>\<open>conj\<close>, _) $ X $ Y)
            = binop \<^Const>\<open>HOL.conj\<close> (inst_Lw context X, inst_Lw context Y)
        | inst_Lw context (Const(\<^const_name>\<open>disj\<close>, _) $ X $ Y)
            = binop \<^Const>\<open>HOL.disj\<close> (inst_Lw context X, inst_Lw context Y)
        | inst_Lw (vars,prems) (Const(\<^const_name>\<open>All\<close>, _) $ Abs (N,ty,X))
            = inst_Lw ((N,ty)::vars, map (Term.incr_boundvars 1) prems) X
        | inst_Lw (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
            = let fun meet v j = if var = v
                                 then fold (fn prem => fn X => \<^Const>\<open>HOL.implies\<close> $ prem $ X) prems X
                                  |> quantifies j vars
                                  |> SOME
                                 else inst_Lw (vars, P::prems) X
               in case P
               of Var v $ Bound j => meet v j
                | Var v => meet v ~1
                | Const (\<^const_name>\<open>HOL.conj\<close>, _) $ (Var v $ Bound j) $ _ => meet v j
                | _ => inst_Lw (vars, P::prems) X
              end
        | inst_Lw _ _ = NONE

      fun inst_Lw' context X = case inst_Lw context X of SOME ret => ret
                                  | NONE => \<^Const>\<open>True\<close>

  in case Thm.prop_of sequent
       of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _)
            $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ X)) $ _
            => let val X'1 = inst_Lw' ([],[]) X
                   val X' = case snd var
                              of \<^Type>\<open>fun D _\<close> => Abs ("x", D, X'1)
                               | _ => X'1
                in SOME (Thm.instantiate (TVars.empty, Vars.make [(var, Thm.cterm_of ctxt X')]) sequent
                      |> oblg_solver (#proof_id phi ^ "/" ^ name) ctxt)
               end
        | _ => error "Internal bug"
 end


fun gen_is_functional (_,name) hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val parse_hint = parse_hint_has_type_only (fn Const(\<^const_name>\<open>Functionality\<close>, _) $ T $ _ => T )

      val ind_conv = default_ind_conv (
            fn _ => fn _ => Conv.all_conv,
            fn ctxt => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_IsFunc_rewr} then_conv
                Conv.arg_conv (Conv.arg_conv (Conv.arg_conv (Conv.arg_conv (
                    Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0))
                )))))
      val reasoning = default_reasoning true
                          (default_reasoning_configure [])
                          (K (K NONE))
                          (exhaustive_PLPR_reasoner (SOME 1))

      val mode_infer = not (is_some hint0)
      val solver = if mode_infer then solver name else K NONE

      fun simp (_, ctxt) rule =
        if is_some hint0
        then rule
        else Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (Conv.arg_conv (
                  Simplifier.rewrite (ctxt addsimps @{thms special_Ex_def}))
                )) ctxt) rule

      val ctxt = ctxt0 (*Context.proof_map (Phi_Reasoners.add_premise_extraction_rules
                    @{thms' Is_Functional_premise_extraction Functionality_premise_extraction}) ctxt0*)
      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' \<phi>TA_IsFunc_rule},
                                      [(SOME ([0], ind_conv), K reasoning)], solver, simp)
                                    phi0 hint0 ctxt
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80
                                              ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val is_functional = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Functionality") gen_is_functional

end
