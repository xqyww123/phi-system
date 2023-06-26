signature PHI_TYPE_ALGEBRA = sig
include PHI_TYPE_ALGEBRA

val gen_obj_equal : automation_on_def

end

structure Phi_Type_Algebra : PHI_TYPE_ALGEBRA = struct
open Phi_Type_Algebra

(*** Library ***)

exception Automation_Fail

fun reason_fail msg = (warning msg; raise Automation_Fail)

structure Simps = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>\<phi>constraint_expansion\<close>
  val comment = "Rules to expand constraints and conditions in \<phi>-type algebra automation"
)

structure Normalize_ToA = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>\<phi>type_algebra_normalize_ToA_ss\<close>
  val comment = "Internal simplification set to normalize ToA in \<phi>-type algebra automation"
)

val _ = Theory.setup (Context.theory_map (
  Normalize_ToA.map (fn ctxt =>
    (ctxt addsimprocs [Simplifier.the_simproc \<^context> "HOL.defined_All"])
      |> Simplifier.add_cong @{thm imp_cong[folded atomize_eq]})
))

fun classify_bnf_dead_live bnf tys =
  let val btys = snd (Term.dest_Type (BNF_Def.T_of_bnf bnf))
      val deads = BNF_Def.deads_of_bnf bnf
   in fold2 (fn t => fn bt => fn (D,L) =>
        if member (op =) deads bt then (t::D, L) else (D, t::L)
      ) tys btys ([],[])
  end

fun guess_operator ctxt mk_term known_oprs x_ty =
  case AList.lookup (op =) known_oprs x_ty
    of SOME opr => opr
     | _ => (
  case x_ty
    of Type(Tname, Targs) =>
        (case BNF_Def.bnf_of ctxt Tname
           of NONE => (warning ("Type " ^ fst (Term.dest_Type x_ty) ^ " is not a known BNF. \
                                \Fail to guess its abstract operator.");
                       raise Automation_Fail)
            | SOME bnf =>
         let val (D,L) = classify_bnf_dead_live bnf Targs
             val head = mk_term D L bnf
             val params = map (guess_operator ctxt mk_term known_oprs) L
          in fold (fn p => fn X => X $ p) params head
         end)
     | T => reason_fail ("Fail to guess the abstract operator for type " ^ Syntax.string_of_typ ctxt T))


(*** Equivalence of Abstract Objects ***)

local

fun set_last_schematic_var ctxt rule0 =
  let val rule = Phi_Reasoner.beta_eta_contract rule0
      val (t1,t2,tm) =
        case Thm.concl_of rule
          of _ (*Trueprop*) $ (_ (*\<phi>Equal_Obj*) $ Abs (_, t1, Abs (_, t2, tm)) $ _)
              => (t1,t2,tm)
           | _ => error "Internal bug cb9504e4-7db1-45f8-b1f6-ec37a5b75105"
      fun get_the_last_var (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ X) = get_the_last_var X
        | get_the_last_var (Var v $ Bound 0 $ Bound 1) = (v, Abs("",t2,Abs("",t1,\<^term>\<open>True\<close>)))
        | get_the_last_var (Var v $ Bound 1 $ Bound 0) = (v, Abs("",t1,Abs("",t2,\<^term>\<open>True\<close>)))
        | get_the_last_var _ = error "Internal bug 6160c2ee-6448-4654-b017-237c879c33a3"
      val last_var = get_the_last_var tm |> apsnd (Thm.cterm_of ctxt)
   in Thm.instantiate (TVars.empty, Vars.make [last_var]) rule
  end

fun set_eq_when_it_is_constant_true ctxt rule0 =
  let val rule = Phi_Reasoner.beta_eta_contract rule0
      val v = case Thm.concl_of rule
                of _ (*Trueprop*) $ (_ (*\<phi>Equal_Obj*) $ Var v $ _) => v
                 | _ => error "Internal bug 5d769e14-74ca-4afb-8d43-672e0afc5470"
      val P = case snd v
                of \<^Type>\<open>fun a \<open>\<^Type>\<open>fun b _\<close>\<close>\<close> => Abs("",a,Abs("",b,\<^term>\<open>True\<close>))
                 | _ => error "Internal bug a74fc08c-d9c1-4b19-99b2-4f18a07b31aa"
   in Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt P)]) rule
  end

fun infer_eq ctxt rule =
  let fun is_free_bound lev (Abs(_,_,X)) = is_free_bound (lev+1) X
        | is_free_bound lev (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ X $ _) = is_free_bound lev X
        | is_free_bound lev (A $ B) = is_free_bound lev A andalso is_free_bound lev B
        | is_free_bound lev (Bound i) = (i = lev)
        | is_free_bound _ _ = true
      fun is_free_bound' (Abs(_,_,X)) = is_free_bound 0 X
        | is_free_bound' _ = true
   in (case Thm.major_prem_of rule
        of _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (Const(\<^const_name>\<open>All\<close>, _) $ X ) $ _) =>
            infer_eq ctxt (if is_free_bound' X
                           then @{thm \<phi>Equiv_Obj_rule_move_all2} RS rule
                           else @{thm \<phi>Equiv_Obj_rule_move_all} RS rule)
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>, _)) =>
            (@{thm \<phi>Equiv_Obj_rule_move_set_eq_end} RS (@{thm simp_thms(21)[THEN iffD2]} RS rule))
              |> set_last_schematic_var ctxt
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
            infer_eq ctxt (@{thm \<phi>Equiv_Obj_rule_move_set_eq} RS rule)
         | _ (*Trueprop*) $ Const(\<^const_name>\<open>True\<close>, _) =>
            (@{thm TrueI} RS rule)
              |> set_eq_when_it_is_constant_true ctxt
         | _ => error "internal bug 7147bf3f-9e7d-4ffc-a40b-aa621a4fca21")
      handle THM _ => raise Automation_Fail
  end

(*
fun infer_eq_conv ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>conj\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>, _) =>
          Conv.rewr_conv @{thm simp_thms(21)[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _ =>
         (Conv.arg_conv infer_eq_conv then_conv
          Conv.rewr_conv @{thm imp_conjR[folded atomize_eq, symmetric]}) ctm
     | _ => Conv.all_conv ctm *)
      
(*
fun guess_obj_equal ctxt x_ty param_eqs =
  case BNF_Def.bnf_of ctxt (fst (Term.dest_Type x_ty))
    of NONE => (warning ("Type " ^ fst (Term.dest_Type x_ty) ^ " is not a known BNF. \
                  \Fail to guess its object equivalence.");
                raise Automation_Fail)
     | SOME bnf =>
        let val ty_args = snd (Term.dest_Type x_ty)
            val (D,L) = classify_bnf_dead_live bnf ty_args
            val rel = BNF_Def.mk_rel_of_bnf D L L bnf
            val params = map (fn T =>
                  case filter (fn tm =>
                    case Term.fastype_of tm
                      of \<^Type>\<open>fun T' _\<close> => T = T'
                       | _ => false) param_eqs
                    of [eq] => eq
                     | [] => reason_fail ("Fail to guess the object equivalence: \
                                \No object equivalence for type " ^ Syntax.string_of_typ ctxt T ^
                                " is found.")
                     | _ => reason_fail ("Fail to guess the object equivalence: \
                                \There are more than one candidates of object equivalence for type " ^
                                Syntax.string_of_typ ctxt T)) L
         in fold (fn p => fn X => X $ p) params rel
        end *)

fun conv_eq_imp ctxt ctm =
  (Conv.rewr_conv @{thm imp_ex[folded atomize_eq]} then_conv
   Phi_Helper_Conv.hol_all_conv (conv_eq_imp o snd) ctxt) ctm
  handle CTERM _ => Conv.all_conv ctm
       | THM _ => Conv.all_conv ctm

fun obj_equal_reasoner ctxt sequent0 =
  case Thm.major_prem_of sequent0
    of _ $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => @{thm \<r>Success_I} RS sequent0
     | _ =>
  let val (has_eq_constraint, sequent) = sequent0
                  |> Phi_Help.repeat (fn th => @{thm allI} RS th)
                  |> (fn th => case Thm.major_prem_of th
                                 of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                        Const(\<^const_name>\<open>implies\<close>, _)
                                            $ _
                                            $ (Const(\<^const_name>\<open>Imply\<close>, _) $ _ $ _ $ _))
                                      => (true, @{thm impI} RS th)
                                  | _ => (false, th) )
      val (focus, lsequent) = Subgoal.focus ctxt 1 NONE sequent
      val ctxt' = #context focus

      fun instantiate_ToA eq_constraint ToA =
        case Thm.prop_of ToA
          of Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ _
                $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                    Const(\<^const_name>\<open>Imply\<close>, _) $ _ $ _ $ _))
              => let
                val prem = Thm.cprop_of ToA
                            |> Thm.dest_arg1
                val insts = Goal.init prem
                        |> Method.insert_tac ctxt' [eq_constraint] 1
                        |> Seq.hd
                        |> Clasimp.fast_force_tac ctxt' 1
                        |> Seq.chop 21 |> fst
                        |> maps (fn th => let val th' = Goal.conclude th RS ToA
                                           in [th' RS @{thm mk_ToA_rule}, th' RS @{thm mk_ToA_rule'}]
                                          end)
                val _ = if length insts > 20
                        then warning "I find more than 20 instantiations which is very abnormal.\
                                     \ I only take the first 20 instantiations."
                        else ()
               in insts
              end
           | _ => []

      val prems' = if has_eq_constraint then Phi_Help.front (#prems focus) else #prems focus
      val eq_constraint = if has_eq_constraint then Phi_Help.last (#prems focus) else Drule.dummy_thm
      val ants' = Phi_Help.last prems'
      val prems = Phi_Help.front prems' |> map (fn th => ants' RS th)
      val ToAs = if has_eq_constraint
                 then maps (instantiate_ToA eq_constraint) prems
                 else []
      val ants = HOLogic.conj_elims ctxt ants'
(* filter (fn th =>
              case Thm.prop_of th of Const(\<^const_name>\<open>Trueprop\<close>, _)
                                        $ (Const (\<^const_name>\<open>\<phi>Equiv_Obj\<close>, _) $ _ $ _) => true
                                   | _ => false) prems *)

      val ctxt'' = ctxt'
            |> Context.proof_map (Phi_Reasoner.add_intro_rules (
                  map (fn rule => ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [], [], NONE)) ToAs))
            |> Context.proof_map (Phi_Reasoner.add_intro_rules (
                  map (fn rule => ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [], [], NONE)) ants))

      val lsequent'1 = (case Thm.major_prem_of lsequent
                          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Imply\<close>, _) $ _ $ _ $ _)
                               => @{thm Action_Tag_D[where A = \<open>ToSA\<close>]} RS lsequent
                           | _ => lsequent)

      val lsequent' = PLPR_Exhaustive.reason_exhaustively (SOME 1) (ctxt'', lsequent'1)
                    |> (fn SOME th => th
                         | NONE => raise Automation_Fail)
      val lsequent'' = if has_eq_constraint
                       then Conv.gconv_rule (PLPR_Syntax.premise_tag_conv (
                              Conv.rewr_conv (eq_constraint RS @{thm conv_intro_premise}))) 1
                              lsequent'
                       else lsequent'

      (*fun do_work (focus:Subgoal.focus) sequent =
        let val prems = if has_eq_constraint then Phi_Help.front (#prems focus) else #prems focus
            val ctxt' = #context focus
            
         in Seq.empty
        end*)
   in Subgoal.retrofit ctxt'' ctxt (#params focus) (#asms focus) 1 lsequent'' sequent
   |> Seq.hd
   |> Phi_Reasoners.defer_obligation_tac ctxt
   |> Seq.hd
   |> obj_equal_reasoner ctxt
  end

fun generic_auto generate_antecedents (phi0 : phi_type) hint0 thy =
  let val ctxt0 = Context.proof_of thy
      val (inst,inst',phi,ctxt01) = fix_phi_type true phi0 ctxt0
      val ((x_term, T_term, x_ty, arg_tys, model_ty), ctxt02) = fix_phi_term_params (#term phi) ctxt01
      val hint = Option.map (Term_Subst.instantiate inst) hint0
      val arity = length arg_tys
      val (gen_ants, ctxt) = generate_antecedents ctxt02 (x_ty, arg_tys, model_ty, hint)
   in ()
  end

fun gen_obj_equal' (phi0 : phi_type) hint0 thy =
  let val ctxt0 = Context.proof_of thy
      val (inst,inst',phi,ctxt01) = fix_phi_type true phi0 ctxt0
      val ((x_term, T_term, x_ty, arg_tys, model_ty), ctxt02) = fix_phi_term_params (#term phi) ctxt01
      val hint = Option.map (Term_Subst.instantiate inst) hint0
      val arity = length arg_tys

      fun mk_Ants ctxt (Ty::rev_arg_tys) (eq::eq_names) ants param_eqs (T_term $ A) =
           (let val (rev_arg_tys_A, x_ty_A, model_ty_A) = dest_parameterized_phi_ty Ty
                val arity_A = length rev_arg_tys_A
                val typ = x_ty_A --> x_ty_A --> \<^typ>\<open>bool\<close>
                val ant = (Term.incr_bv (arity_A, 0, A))
                        |> fold_index (fn (i,_) => fn X => X $ Bound (arity_A-1-i)) rev_arg_tys_A          
                        |> (fn X => \<^Const>\<open>\<phi>Equiv_Obj x_ty_A model_ty_A\<close> $ Free(eq, typ) $ X)
                        |> fold (fn T => fn X =>
                            Const(\<^const_name>\<open>All\<close>, (T --> HOLogic.boolT) --> HOLogic.boolT)
                              $ Abs("",T,X)
                           ) rev_arg_tys_A
             in mk_Ants ctxt rev_arg_tys eq_names (ant::ants)
                        ((x_ty_A, Free(eq, typ))::param_eqs) T_term
            end
            handle TYPE _ => (ants, param_eqs))
        | mk_Ants _ [] [] ants param_eqs _ = (ants, param_eqs)
        | mk_Ants _ _ _ _ _ _ = raise ListPair.UnequalLengths

      val rev_eq_names' = Name.invent (Variable.names_of ctxt02) "eq" arity
      val (rev_eq_names, ctxt) = Variable.add_fixes rev_eq_names' ctxt02
      val rev_arg_tys = rev arg_tys
      val (ants,param_eqs) = mk_Ants ctxt rev_arg_tys rev_eq_names [] [] T_term
      val ant = Phi_Help.list_mk_conj ants

      fun chk_known_oprs [] = ()
        | chk_known_oprs ((k,_)::L) =
           (if AList.defined (op =) L k
            then warning ("More than one \<phi>-type parameter has identical type at abstract domain.\n\
                          \It affects the guessing of the abstract operators. \
                          \Giving the operators manually is recommended if the automation fails.")
            else () ;
            chk_known_oprs L)
      val (eq_term_given, eq_term, ctxt'v) =
            (case hint of SOME H => (true, H, ctxt)
                | _ => if #is_recursive phi
                       then (chk_known_oprs param_eqs;
                             (true, guess_operator ctxt (fn D => fn L => BNF_Def.mk_rel_of_bnf D L L)
                                                  param_eqs x_ty, ctxt))
                       else let val [eq_name'] = Name.invent (Variable.names_of ctxt) "eq" 1
                                val ([eq_name], ctxt'v) = Variable.add_fixes [eq_name'] ctxt
                             in (false, Free(eq_name, x_ty --> x_ty --> HOLogic.boolT), ctxt'v)
                            end)

      val insts = (case hint of SOME H => [(("eq",0), Thm.cterm_of ctxt02 H)] | _ => [])
      val rule = Drule.infer_instantiate ctxt'v
                  ((("T",0), Thm.cterm_of ctxt'v T_term) ::
                   (("Ant",0), Thm.cterm_of ctxt'v ant) ::
                   (("eq",0), Thm.cterm_of ctxt'v eq_term) :: insts)
                  @{thm \<phi>Equiv_Obj_rule}

      val ind0 = Phi_Type_Algebra.mk_ind_dest_ToA ctxt'v phi (fn (x,T) =>
        let val x' = Term.incr_bv (1,0,x)
            val T' = Term.incr_bv (1,0,T)
         in \<^Const>\<open>implies\<close>
              $ Phi_Help.list_mk_conj (fst (mk_Ants ctxt'v rev_arg_tys rev_eq_names [] [] T))
              $ (Const(\<^const_name>\<open>All\<close>, (x_ty --> HOLogic.boolT) --> HOLogic.boolT) $ Abs ("", x_ty, 
                    \<^Const>\<open>implies\<close>
                      $ (eq_term $ x' $ Bound 0)
                      $ (\<^Const>\<open>Imply model_ty\<close>
                            $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ x' $ T')
                            $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ T')
                            $ \<^Const>\<open>True\<close>)))
        end)
      (*val P_term = fold_rev (fn T => fn X => Abs("",T,X)) arg_tys \<^const>\<open>True\<close>*)
              (*|> Drule.infer_instantiate ctxt [(("P",0), Thm.cterm_of ctxt P_term)]
              |> Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv (fn _ =>
                    HOLogic.Trueprop_conv (
                      Conv.arg1_conv (Conv.rewr_conv @{thm Premise_True[THEN Eq_TrueI]}) then_conv
                      Conv.rewr_conv @{thm simp_thms(15)[folded atomize_eq]})) ctxt)*)
      val ind = Conv.fconv_rule (
              Phi_Helper_Conv.hhf_conv (
                Phi_Helper_Conv.hhf_conv (fn ctxt => fn ctm =>
                  case Thm.term_of ctm
                    of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>implies\<close> $ _ $ (\<^Const>\<open>All _\<close> $ Abs (_,_,
                          \<^Const>\<open>implies\<close> $ _ $ (\<^Const>\<open>Imply _\<close> $ _ $ _ $ _)
                       )))
                        => (Conv.rewr_conv @{thm atomize_imp[symmetric]} then_conv
                            Conv.implies_concl_conv (
                              Conv.rewr_conv @{thm atomize_all[symmetric]} then_conv
                              Phi_Helper_Conv.meta_all_conv (fn _ =>
                                Conv.rewr_conv @{thm atomize_imp[symmetric]}) ctxt) then_conv
                            Conv.rewr_conv Drule.norm_hhf_eq) ctm
                     | _ => Conv.all_conv ctm
                ) (fn ctxt => fn ctm =>
                  case Thm.term_of ctm
                    of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>implies\<close> $ _ $ (\<^Const>\<open>All _\<close> $ Abs (_,_,
                          \<^Const>\<open>implies\<close> $ _ $ (\<^Const>\<open>Imply _\<close> $ _ $ _ $ _)
                       )))
                        => (Conv.rewr_conv @{thm atomize_imp[symmetric]} then_conv
                            Conv.implies_concl_conv (
                              HOLogic.Trueprop_conv (
                              Phi_Helper_Conv.hol_all_conv (fn (_,ctxt) =>
                                  Conv.arg1_conv (Simplifier.rewrite (Simps.equip ctxt)) then_conv
                                  conv_eq_imp ctxt
                                ) ctxt then_conv
                              Simplifier.asm_rewrite (Normalize_ToA.equip ctxt addsimps (#equations phi))
                           ))) ctm
                     | _ => Conv.all_conv ctm)
              ) (K Conv.all_conv) ctxt'v
            ) ind0

      val rule' = obj_equal_reasoner ctxt'v (singleton (Variable.export ctxt'v ctxt) (ind RS rule))
(*
      val ctxt'r = Context.proof_map (Phi_Reasoner.adds (map (fn pat => {
                name = \<^term>\<open>Local_\<phi>Equiv_Obj\<close>,
                pos = \<^here>,
                mode = Phi_Reasoner.LOCAL_CUT,
                pattern = [(HOLogic.mk_Trueprop pat, 1000)],
                blacklist = [],
                tactic = Phi_Reasoners.wrap (fn ctxt => Thm.assumption (SOME ctxt) 1)
            }) pats)) ctxt *)

(*      val (ctxt',rule') = Phi_Reasoner.reason NONE (ctxt, ind RS rule)
              |> (fn SOME ctxt_rule => ctxt_rule
                   | NONE => raise Automation_Fail) *)

      (*TODO: simplify the leading premises, expansion of existential quantification*)

      val rule'2 =
       (if eq_term_given
        then Phi_Sledgehammer_Solver.auto (SOME (#proof_id phi ^ "/obj_equal")) (ctxt, rule')
        else (@{thm Premise_I} RS rule')
          |> infer_eq ctxt
          |> Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv 
                (K (Conv.arg_conv (Conv.arg1_conv (Simplifier.rewrite ctxt)))) ctxt))
       |> singleton (Proof_Context.export ctxt ctxt0)
   in Phi_Reasoner.add_intro_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [rule'2] thy
  end

val select_hint = get_first (fn Const(\<^const_name>\<open>\<phi>Equiv_Obj\<close>, _) $ eq $ _ => SOME eq
                              | _ => NONE)

in

fun gen_obj_equal (phi,hints) thy =
  let val hint = select_hint hints
   in gen_obj_equal' phi hint thy
      handle Automation_Fail => (
        warning "Fail to reason the equivelance between abstract objects." ;
        (if is_some hint then () else
          warning "You may want to annotate it by \<open>is \<open>\<phi>Equiv_Obj eq\<close>\<close>");
        thy
      )
  end

end

(*** Transformation Functor ***)



(*** Install Automation ***)

val _ = Theory.setup (Context.theory_map (
  Phi_Type_Algebra.add_automation_on_def 100 gen_obj_equal
))

end