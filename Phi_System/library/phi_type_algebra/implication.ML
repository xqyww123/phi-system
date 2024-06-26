signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val abstract_domain : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val abstract_domain_L : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

val guess_property_like_abst_domain :
      bool * bool * bool
      * (typ * typ -> term)
      * (Proof.context * typ * term * term -> term list -> term list)
      * (Proof.context * typ * term * term -> term -> term)
      * sort * sort
      -> guess_property

(*Infers a predicate or a boolean condition making the obligation true.
  It supports upper and lower modes.

  Upper mode: the unknown locates at the consequent part, and we infer a satisfiable instantiation
              from the conditions of the oblgiation.
  Lower mode: the unknown locates at the condition part of the obligation, and we infer an instantiation
              as strong as possible (but does not weaken the entire obligation)
*)
val predicate_infer : bool -> (term -> (indexname * typ) option) -> solver -> solver
val predicate_infer__contains_bad : bool -> term -> bool

(*val guess_property_abst_dom : string -> guess_property
val predicate_infer : bool -> string (*name of proof cache*) -> solver*)

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

(*var_based_infer: whether to insert a schematic variable so that one can later infer the predicate
                   from the reported proof obligation which will contain the variable.
                   Such variable-based inference only works on non-recursive \<phi>-types.

  infer_from_BNF: whether to guess the predicate according to BNF (Bounded Natural Foundation) on
                  non-recursive \<phi>-types. Sometimes, var_based_infer is powerful enough on non-recursive \<phi>-types
                  to give the expected result but the guessing from BNF can be wrong and therefore
                  cause troubles. In this case, \<open>infer_from_BNF\<close> can be disabled.

                  The option only affects the cases of non-recursive \<phi>-types, because the guessing
                  from BNF is the only method for recursive \<phi>-types*)
fun guess_property_like_abst_domain (is_cov, infer_from_BNF, var_based_infer,
                                     prop_head, pass_ants, pass_pred, x_sort, model_sort) (phi0 : phi_type) ctxt =
  let val (rev_arg_tys0, x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val tpairs = map_filter (   try dest_parameterized_phi_ty
                               #> Option.map (fn (_, x, m) => [(x, x_sort), (m, model_sort)])
                              ) rev_arg_tys0
                |> flat
      val inst = lift_types_sort (Proof_Context.theory_of ctxt)
                                 ((x_ty0, x_sort) :: (model_ty0, model_sort) :: tpairs)
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val phi = instantiate_phi (inst',Vars.empty) phi0

      val ((_, T_term), ctxt) = fix_phi_term_params phi ctxt
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
             in prop_head (x,m) $ T' $ pred
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params preds
      val idx = maxidx_of_phi phi ~1 + 1

      val (ants_delta, oblg_delta, cond_delta) =
              guess_conditions ctxt (prop_head (x_ty, model_ty), is_cov) phi T_term
      (*fun pass_pred pred =
            if is_cov then Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (cond_delta $ Bound 0) $ (pred $ Bound 0))
                      else Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (oblg_delta $ Bound 0) $ (pred $ Bound 0))*)

      val add_Pvar = if #is_recursive phi orelse not var_based_infer then I
                     else fn pred => 
                      let val Pvar = Var(("P",idx), x_ty --> HOLogic.boolT)
                       in Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (pred $ Bound 0) $ (Pvar $ Bound 0))
                      end
   in (if not (#is_recursive phi) andalso not infer_from_BNF
       then Seq.single (Abs ("x", x_ty, \<^Const>\<open>True\<close>), ctxt)
       else guess_predicate ctxt preds x_ty)
   |> Seq.map (fn (pred, ctxt) =>
        (pass_ants (ctxt, x_ty, oblg_delta, cond_delta) (ants_delta @ ants),
         HOLogic.Trueprop $ (prop_head (x_ty, model_ty) $ T_term
            $ add_Pvar (pass_pred (ctxt, x_ty, oblg_delta, cond_delta) pred)),
         NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt))
  end


(*** Inhabitance ***)
(*
fun guess_property_abst_dom upper (phi:phi_type) ctxt =
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
      val head_const = if upper then \<^const_name>\<open>Abstract_Domain\<close>
                                else \<^const_name>\<open>Abstract_Domain\<^sub>L\<close>
      fun head x m = Const(head_const, \<^Type>\<open>fun \<^Type>\<open>fun x \<^Type>\<open>set m\<close>\<close> \<^Type>\<open>fun \<^Type>\<open>fun x \<^Type>\<open>bool\<close>\<close> \<^Type>\<open>bool\<close>\<close>\<close>)
      val ants = map2 (fn ((rev_args, x, m), T'h) => fn (_, pred) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_args T'h
             in head x m $ T' $ pred
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params preds
      val idx = maxidx_of_phi phi ~1 + 1
      
      val (ants_delta, oblg_delta, cond_delta) =
              guess_conditions ctxt (head x_ty model_ty, not upper) phi T_term
      fun pass_pred pred =
            if upper then Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (cond_delta $ Bound 0) $ (pred $ Bound 0))
                     else Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (oblg_delta $ Bound 0) $ (pred $ Bound 0))

      val add_Pvar = if #is_recursive phi then I
                     else fn pred => 
                      let val Pvar = Var(("P",idx), x_ty --> HOLogic.boolT)
                       in Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (Pvar $ Bound 0) $ (pred $ Bound 0))
                      end
   in guess_predicate ctxt preds x_ty
   |> Seq.map (fn (pred, ctxt) =>
        (if upper then ants_delta @
                       PLPR_Syntax.dest_ant_sequence_or_HOL_conj (forall_qualify x_ty oblg_delta) @
                       ants
                  else ants_delta @ ants,
         HOLogic.Trueprop $ (head x_ty model_ty $ T_term $ add_Pvar (pass_pred pred)),
         NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt))
  end
*)
(*fun guess_property_inhab_atom upper (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (_,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val idx = maxidx_of_phi phi ~1 + 1
      fun head x m = if upper then \<^Const>\<open>Abstract_Domain x m\<close>
                              else \<^Const>\<open>Abstract_Domain\<^sub>L x m\<close>
      val Prop = HOLogic.Trueprop $ (head x_ty model_ty $ T_term $ Var(("P",idx), x_ty --> HOLogic.boolT))
   in Seq.single ([], Prop, NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end
*)

(*Infers a predicate or a boolean condition making the obligation true.
  It supports upper and lower modes.

  Upper mode: the unknown locates at the consequent part, and we infer a satisfiable instantiation
              from the conditions of the oblgiation.
  Lower mode: the unknown locates at the condition part of the obligation, and we infer an instantiation
              as strong as possible (but does not weaken the entire obligation)
*)
fun predicate_infer__contains_bad allows_Satisfiable_and_Sat =
      exists_subterm (fn Const(\<^const_name>\<open>Satisfiable\<close>, _) => allows_Satisfiable_and_Sat
                       | Const(\<^const_name>\<open>Satisfaction\<close>, _) => allows_Satisfiable_and_Sat
                       | Var _ => true
                       | _ => false)

fun predicate_infer_var upper (SOME var) (phi,ctxt,sequent) =
  let val arity = length (Term.binder_types (snd var))

      fun binop H (SOME sa, SOME sb) = SOME (H $ sa $ sb)
        | binop _ (some_or_none, NONE) = some_or_none
        | binop _ (NONE, some) = some
      fun impop (SOME A, SOME B) = SOME (\<^Const>\<open>HOL.implies\<close> $ A $ B)
        | impop (SOME A, NONE) = NONE
        | impop (NONE, SOME B) = SOME B
        | impop (NONE, NONE) = NONE

      fun qualifies js vars =
             fold_index (fn (k, (N, ty)) => fn X =>
               let val ij = find_index (fn j => j = k) js
                in if ij = ~1
                   then HOLogic.all_const ty $ Abs(N, ty, X)
                   else Abs (N, ty, X) $ Bound (length vars - 1 - k + length js - 1 - ij)
               end
             ) vars

      val allows_Satisfiable_and_Sat = (*the inferred condition contains Satisfiable and Satisfaction
                                       only when they are also contained in the definition of the \<phi>-type,
                                       to prevent the result corrupted by noises*)
            exists (exists_subterm (fn Const(\<^const_name>\<open>Satisfiable\<close>, _) => true
                                     | Const(\<^const_name>\<open>Satisfaction\<close>, _) => true
                                     | _ => false) o Thm.prop_of) (#equations phi)
              |> not
      val exists_bad = predicate_infer__contains_bad allows_Satisfiable_and_Sat

      
      (*upper: true for parsing the conclusion part, false for parsing conditions*)
      fun filter_bad upper (\<^Const>\<open>HOL.conj\<close> $ A $ B) = binop \<^Const>\<open>HOL.conj\<close> (filter_bad upper A, filter_bad upper B)
        | filter_bad true (\<^Const>\<open>HOL.disj\<close> $ A $ B) = binop \<^Const>\<open>HOL.disj\<close> (filter_bad upper A, filter_bad upper B)
        | filter_bad upper (\<^Const>\<open>HOL.implies\<close> $ A $ B) =
            if upper then impop (filter_bad false A, filter_bad true B)
                     else if exists_bad A orelse exists_bad B then NONE
                          else SOME (\<^Const>\<open>HOL.implies\<close> $ A $ B)
        | filter_bad upper (\<^Const>\<open>HOL.All T\<close> $ Abs (N,T',X)) =
            (case filter_bad upper X of SOME X' => SOME (\<^Const>\<open>HOL.All T\<close> $ Abs (N,T',X'))
                                      | NONE => NONE)
        | filter_bad upper X = if exists_bad X then NONE else SOME X

      fun augment P prems = case filter_bad false P
                              of SOME P' => P' :: prems
                               | NONE => prems

      fun inst_Lw context (Const(\<^const_name>\<open>conj\<close>, _) $ X $ Y)
            = binop \<^Const>\<open>HOL.conj\<close> (inst_Lw context X, inst_Lw context Y)
        | inst_Lw context (Const(\<^const_name>\<open>disj\<close>, _) $ X $ Y)
            = binop \<^Const>\<open>HOL.conj\<close> (inst_Lw context X, inst_Lw context Y)
        | inst_Lw (vars,prems) (Const(\<^const_name>\<open>All\<close>, _) $ Abs (N,ty,X))
            = inst_Lw ((N,ty)::vars, map (Term.incr_boundvars 1) prems) X
        | inst_Lw (vars,prems) (\<^Const>\<open>All T\<close> $ X)
            = inst_Lw (vars,prems) (\<^Const>\<open>All T\<close> $ (Abs ("_", T, Term.incr_boundvars 1 X $ Bound 0)))
        | inst_Lw (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
            = let fun meet v js = if var = v
                                  then filter_bad true X
                                    |> Option.map (
                                          fold (fn prem => fn X =>
                                              \<^Const>\<open>HOL.implies\<close> $ prem $ X
                                             ) prems
                                       #> qualifies js vars)
                                  else inst_Lw (vars, augment P prems) X
                  val (h, args) = case P
                                    of Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ X => Term.strip_comb X
                                     | X => Term.strip_comb X
               in case h
               of Var v => if forall (fn Bound _ => true | _ => false) args andalso length args = arity
                           then meet v (map (fn Bound i => i) args)
                           else NONE
                | _ => inst_Lw (vars, augment P prems) X
              end
        | inst_Lw _ _ = NONE

      fun inst_Lw' context X = case inst_Lw context X of SOME ret => ret
                                  | NONE => \<^Const>\<open>True\<close>

      val exists_bad'Pr = exists_subterm (fn Const(\<^const_name>\<open>Satisfiable\<close>, _) => true
                                           | Const(\<^const_name>\<open>Satisfaction\<close>, _) => true
                                           | Var v => v <> var
                                           | _ => false)
      fun inst_Pr context (Const(\<^const_name>\<open>conj\<close>, _) $ A $ B)
            = binop \<^Const>\<open>HOL.disj\<close> (inst_Pr context A, inst_Pr context B)
        | inst_Pr context (Const(\<^const_name>\<open>disj\<close>, _) $ A $ B)
            = if exists_bad'Pr A
              then if exists_bad'Pr B
              then binop \<^Const>\<open>HOL.disj\<close> (inst_Pr context A, inst_Pr context B)
              else inst_Pr context B
              else if exists_bad'Pr B
              then inst_Pr context A
              else binop \<^Const>\<open>HOL.disj\<close> (inst_Pr context A, inst_Pr context B)
        | inst_Pr (vars,prems) (Const(\<^const_name>\<open>All\<close>, _) $ Abs (N,ty,X))
            = inst_Pr ((N,ty)::vars, map (Term.incr_boundvars 1) prems) X
        | inst_Pr (vars,prems) (\<^Const>\<open>HOL.All ty\<close> $ X)
            = inst_Pr (vars,prems) (\<^Const>\<open>HOL.All ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | inst_Pr (vars,prems) (Const(\<^const_name>\<open>implies\<close>, _) $ P $ X)
            = inst_Pr (vars, augment P prems) X
        | inst_Pr (vars,prems) X
            = let val (h, args) = Term.strip_comb X
               in case h
               of Var v =>
                  if v = var
                  then if forall (fn Bound _ => true | _ => false) args andalso length args = arity
                    then SOME (qualifies (map (fn Bound i => i) args) vars (Phi_Help.list_mk_conj prems))
                    else NONE
                  else NONE
                | _ => NONE
              end

      fun inst_Pr' context X = case inst_Pr context X of SOME ret => ret
                                  | NONE => \<^Const>\<open>True\<close>
   in case Thm.prop_of sequent
       of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Trueprop\<close>, _)
            $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ X)) $ _
            => let val X' = (if upper then inst_Pr' else inst_Lw') ([],[]) X
                         |> fold_rev (fn T => fn X => Abs ("_", T, X)) (Term.binder_types (snd var))
                   val X' = if exists_subterm (fn Var v => v = var | _ => false) X'
                            then \<^Const>\<open>True\<close> (*the case of recursive, unsupported*)
                            else X'
                   val sequent' = Thm.instantiate (TVars.empty, Vars.make [(var, Thm.cterm_of ctxt X')]) sequent
                in sequent'
               end
        | _ => error "Internal bug"
  end

fun predicate_infer upper parse_var solver (phi,ctxt,sequent0,text) =
  let fun err () = raise Automation_Fail (fn () =>
                        [Pretty.para "Obligation is obtained, but I fail to infer \
                                     \the expression of the implied pure fact from it."])
      val sequent =
         (case parse_var (Thm.concl_of sequent0)
            of NONE => sequent0
             | some_var => predicate_infer_var upper some_var (phi,ctxt,sequent0))
          handle Match => err ()
                (*of _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $ Var v) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Var v $ Bound 0))) => v
                   | _ (*Trueprop*) $ (_ (*Abstract_Domain*) $ _ $
                          Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ Var v $ _)) => v
                   | _ => err ()*)
      
  in solver (phi, ctxt, sequent, text)
 end

fun gen_inhab upper (der_id, name) (instruction : deriving_instruction) (phi0 : phi_type) thy =
  let val guess_property = guess_property_like_abst_domain (
            not upper, false, true,
            if upper then fn (x,m) => \<^Const>\<open>Abstract_Domain x m\<close>
                     else fn (x,m) => \<^Const>\<open>Abstract_Domain\<^sub>L x m\<close>,
            fn (ctxt, x_ty, oblg, cond) =>
                if upper then maps (constrain_antecedents_by_boolean (simplified_forall_qualify ctxt x_ty cond))
                         else maps (constrain_antecedents_by_boolean (simplified_forall_qualify ctxt x_ty oblg)),
            if upper then fn (_, x_ty, _, cond) => fn pred =>
                              Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (cond $ Bound 0) $ (pred $ Bound 0))
                     else fn (_, x_ty, oblg, _) => fn pred =>
                              Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (oblg $ Bound 0) $ (pred $ Bound 0)),
            \<^sort>\<open>type\<close>, \<^sort>\<open>type\<close>)

      val mode_infer = not (is_some (#1 instruction)) andalso not (#is_recursive phi0)

      val parse_hint = parse_hint (
              fn Const(\<^const_name>\<open>Abstract_Domain\<close>, _) $ T $ _ => T
               | Const(\<^const_name>\<open>Abstract_Domain\<^sub>L\<close>, _) $ T $ _ => T)

      fun extract_oprs_from_hint (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ P) = [P]
        | extract_oprs_from_hint _ = []

      val equip_expansion = equip_expansion_ss phi0
      val ind_conv = default_ind_conv (
              fn _ => (K (
                  Conv.rewr_conv (if upper then @{thm' \<phi>TA_Inh_rewr_IH}
                                           else @{thm' \<phi>TA_Suc_rewr_IH}) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv)),
              fn ctxt => fn _ =>
                 (Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_noact} then_conv
                  (Phi_Reasoners.asm_rewrite true (equip_expansion ctxt)) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv))

      val pre_simp = default_pre_simplifier (Phi_Conv.meta_alls_conv (fn ctxt => fn ctm =>
           (Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_rev}) ctm) o snd)

      fun varify_subgoal _ (Trueprop $ (rEIF $ S $ P)) =
            SOME ([P], fn [P'] => Trueprop $ (rEIF $ S $ P'))
        | varify_subgoal _ X = error ""

      fun Inh_reasoning phi ctxt =
            default_reasoning false
                default_reasoning_configure
                (if mode_infer then varify_subgoal else K (K NONE))
                (exhaustive_PLPR_reasoner_by_rule
                    (if upper then @{thm' \<phi>TA_Inh_step} else @{thm' \<phi>TA_Suc_step})
                    (K (chk_unfolded [] ctxt phi)))
                phi
                ctxt

      val solver =
            if mode_infer
            then predicate_infer upper
                    (fn _ (*Trueprop*) $ (_ $ Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Var v $ Bound 0)))
                          => SOME v
                      | _ (*Trueprop*) $ (_ $ X)
                          => if Term.is_schematic X then raise Match else NONE)
                    (oblg_solver' name)
            else K NONE
      val simp = if is_some (#1 instruction) then K I
                 else default_simplifier' (fn rewr =>
                   Phi_Conv.hhf_concl_conv (fn ctxt =>
                      HOLogic.Trueprop_conv (Conv.arg_conv (rewr ctxt)) ))

      val thy' = thy
              |> Bundle.includes ["IDE_CP_Applications1.abstract_domain_OPEN_MAKE"]
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint, guess_property,
                                      (if upper then @{thm' \<phi>TA_Inh_rule} else @{thm' \<phi>TA_SuC_rule}),
                                      [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, Inh_reasoning)],
                                      solver, pre_simp, simp)
                                     phi0 instruction thy'
   in case Seq.pull rules
        of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property."])
         | SOME (rule', _) => thy
            |> Local_Theory.declaration {syntax=false,pervasive=false, pos = #3 instruction} (fn m => fn lthy => lthy
               |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
               |> Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %derived_abstract_domain}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule']
               |> Config.restore_generic Phi_Reasoner.trace lthy)
            |> note_properties_s false phi0 [(name, [rule'])]
            |> pair [rule']
  end

val abstract_domain =
      deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Abstract_Domain") (gen_inhab true)
val abstract_domain_L =
      deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Abstract_Domain\<^sub>L") (gen_inhab false)

end
