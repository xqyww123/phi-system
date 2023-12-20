signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val is_functional : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

(*val solver__abst_domain : string -> solver*)

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers


val guess_property = guess_property_like_abst_domain (
        false, false, true,
        fn (x,m) => \<^Const>\<open>Functionality x m\<close>,
        fn (ctxt, x_ty, _, cond) => fn ants =>
             maps (constrain_antecedents_by_boolean (simplified_exists_qualify ctxt x_ty cond)) ants,
        fn (_, x_ty, oblg, cond) => fn pred =>
              Abs ("x", x_ty, \<^Const>\<open>HOL.implies\<close>
                      $ (cond $ Bound 0)
                      $ (\<^Const>\<open>HOL.conj\<close> $ (oblg $ Bound 0) $ (pred $ Bound 0))),
        \<^sort>\<open>type\<close>, \<^sort>\<open>type\<close>)

(*fun solver__abst_domain name (phi,ctxt,sequent) =
  let fun err () = raise Automation_Fail (fn () =>
                        [Pretty.para "Obligation is obtained, but I fail to infer \
                                     \the expression of the implied pure fact from it."])
      val var = case Thm.concl_of sequent
                  of _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $ Var v) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Var v $ Bound 0))) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ Var v )) => v
                   | _ => err ()

      fun binop H (SOME sa, SOME sb) = SOME (H $ sa $ sb)
        | binop _ (some_or_none, NONE) = some_or_none
        | binop _ (NONE, some) = some
      fun qualifies j vars =
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
        | inst_Lw (vars,prems) (\<^Const>\<open>All ty\<close> $ X)
            = inst_Lw (vars,prems) (\<^Const>\<open>All ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | inst_Lw (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
            = let fun meet v j = if var = v
                                 then fold (fn prem => fn X => \<^Const>\<open>HOL.implies\<close> $ prem $ X) prems X
                                  |> qualifies j vars
                                  |> SOME
                                 else inst_Lw (vars, P::prems) X
               in case P
               of Var v $ Bound j => meet v j
                | Var v => meet v ~1
                | Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Var v $ Bound j) => meet v j
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
*)

fun gen_is_functional (_,name) instruction ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn Const(\<^const_name>\<open>Functionality\<close>, _) $ T $ _ => T )

      val equip_expansion = equip_expansion_ss phi0
      val ind_conv = default_ind_conv (
            fn _ => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_IsFunc_rewr_IH} then_conv
                Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv,
            fn ctxt => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_noact} then_conv
                Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
                Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv
          )

      val pre_simp = default_pre_simplifier (Phi_Conv.meta_alls_conv (fn ctxt =>
            Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_rev}) o snd)
            
      fun reasoning phi ctxt =
            default_reasoning true default_reasoning_configure (K (K NONE))
                              (exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded [] ctxt phi)))
                              phi ctxt

      val mode_infer = not (is_some (#1 instruction)) andalso not (#is_recursive phi0)
      val solver =
            if mode_infer
            then predicate_infer false
                    (fn _(*Trueprop*) $ (_ $ Abs (_, _, \<^Const>\<open>HOL.conj\<close> $ _ $ (Var v $ Bound 0))) => SOME v
                      | _(*Trueprop*) $ (_ $ X) =>
                             if Term.is_schematic X then raise Match else NONE)
                    (oblg_solver' name)
            else K NONE

      val simp = if is_some (#1 instruction) then K I
                 else simplifier_by_cong @{thms' \<phi>TA_IsFunc_cong}
(*Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (Conv.arg_conv (
                  Simplifier.rewrite (ctxt addsimps @{thms special_Ex_def}))
                )) ctxt) rule*)

      val ctxt = ctxt0 (*Context.proof_map (Phi_Reasoners.add_premise_extraction_rules
                    @{thms' Is_Functional_premise_extraction Functionality_premise_extraction}) ctxt0*)
              |> Config.put Phi_Reasoner.ignore_dup_reasoner true
              |> Bundle.includes ["Spec_Framework.Is_Functional_brute", "IDE_CP_Applications1.Functionality_OPEN"]
              |> Config.restore Phi_Reasoner.ignore_dup_reasoner ctxt0

      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' \<phi>TA_IsFunc_rule},
                                      [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning)],
                                       solver, pre_simp, simp)
                                    phi0 instruction ctxt
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %derived_\<phi>functionality}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val is_functional = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Functionality") gen_is_functional

end
