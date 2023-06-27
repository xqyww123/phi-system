signature PHI_TYPE_ALGEBRA = sig
include PHI_TYPE_ALGEBRA

val gen_obj_equal : automation_on_def
val guess_set_opr : Proof.context -> typ -> typ -> (term * Proof.context) Seq.seq

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
    (ctxt addsimprocs [\<^simproc>\<open>defined_Ex\<close>, \<^simproc>\<open>defined_All\<close>, \<^simproc>\<open>ExSet_expand_quantifier\<close>])
      |> Simplifier.add_cong @{thm imp_cong[folded atomize_eq]})
#> Simps.map (fn ctxt =>
    (ctxt addsimprocs [\<^simproc>\<open>defined_Ex\<close>, \<^simproc>\<open>defined_All\<close>, \<^simproc>\<open>ExSet_expand_quantifier\<close>])
      |> Simplifier.add_cong @{thm imp_cong[folded atomize_eq]})
))

fun classify_bnf_dead_live bnf tys =
  let val btys = snd (Term.dest_Type (BNF_Def.T_of_bnf bnf))
      val deads = BNF_Def.deads_of_bnf bnf
   in fold2 (fn t => fn bt => fn (D,L) =>
        if member (op =) deads bt then (t::D, L) else (D, t::L)
      ) tys btys ([],[])
  end

fun guess__get_bnf ctxt Tname =
  case BNF_Def.bnf_of ctxt Tname
    of NONE => (warning ("Type " ^ Tname ^ " is not a known BNF."); Seq.empty)
     | SOME bnf => Seq.single bnf

fun permute_seq (s::L) =
      Seq.maps (fn s' => permute_seq L |> Seq.map (fn L' => s'::L')) s
  | permute_seq [] = Seq.single []

fun guess_operator' ctxt mk_term known_oprs x_ty =
  case map_filter (fn (ty', term) => if ty' = x_ty then SOME term else NONE)
                  known_oprs
    of [] => (
      case x_ty
        of Type(Tname, Targs) =>
             guess__get_bnf ctxt Tname |> Seq.maps (fn bnf =>
             let val (D,L) = classify_bnf_dead_live bnf Targs
              in mk_term (ctxt, D, L, bnf)
              |> Seq.maps (fn (head,ctxt') =>
                  let fun mk_params ctxt (ty::L) =
                        guess_operator' ctxt mk_term known_oprs ty
                          |> Seq.maps (fn (opr, ctxt') =>
                                mk_params ctxt' L
                                  |> Seq.map (fn (oprs, ctxt'') => (opr::oprs, ctxt'')))
                        | mk_params ctxt [] = Seq.single ([], ctxt)
                   in mk_params ctxt' L
                   |> Seq.map (fn (params', ctxt'3) =>
                        (fold (fn p => fn X => X $ p) params' head, ctxt'3))
                  end)
             end)
         | _ => Seq.empty)
     | L => Seq.of_list L
         |> Seq.map (rpair ctxt)

fun guess_operator ctxt mk_term known_oprs x_ty =
  Seq.make (fn () =>
    case Seq.pull (guess_operator' ctxt mk_term known_oprs x_ty)
      of NONE => (warning ("Fail to guess the abstract operator for type " ^ Syntax.string_of_typ ctxt x_ty) ;
                  NONE)
       | some => some )

fun fp_sugar_of ctxt bnf =
  case BNF_Def.T_of_bnf bnf
    of Type(N, _) => BNF_FP_Def_Sugar.fp_sugar_of ctxt N
     | _ => NONE

(*
fun guess_operator' ctxt mk_term known_oprs x_ty =
  case AList.lookup (op =) known_oprs x_ty
    of SOME opr => opr
     | _ => (
  case x_ty
    of Type(Tname, Targs) =>
         let val bnf = guess__get_bnf ctxt Tname
             val (D,L) = classify_bnf_dead_live bnf Targs
             val head = mk_term D L bnf
             val params = map (guess_operator' ctxt mk_term known_oprs) L
          in fold (fn p => fn X => X $ p) params head
         end
     | T => reason_fail ("Fail to guess the abstract operator for type " ^ Syntax.string_of_typ ctxt T))

fun guess_operator ctxt mk_term known_oprs x_ty =
  let fun chk_known_oprs [] = ()
        | chk_known_oprs ((k,_)::L) =
           (if AList.defined (op =) L k
            then warning ("More than one \<phi>-type parameter has identical type at abstract domain.\n\
                          \It affects the guessing of the abstract operators. \
                          \Giving the operators manually is recommended if the automation fails.")
            else () ;
            chk_known_oprs L)
   in chk_known_oprs known_oprs ;
      guess_operator' ctxt mk_term known_oprs x_ty
  end *)


fun guess_set_opr ctxt ty element_ty =
  if ty = element_ty
  then Seq.single (Abs("",ty, \<^Const>\<open>insert ty\<close> $ Bound 0 $ \<^Const>\<open>bot \<^Type>\<open>set ty\<close>\<close>), ctxt)
  else case ty
         of Type(Tname, Targs) =>
              guess__get_bnf ctxt Tname |> Seq.maps (fn bnf =>
                let val (D,L) = classify_bnf_dead_live bnf Targs
                    val N = length (BNF_Def.sets_of_bnf bnf)
                    val tys1 = List.tabulate (N, K D)
                    val tys2 = List.tabulate (N, K L)
                    val sets = BNF_Def.mk_sets_of_bnf tys1 tys2 bnf
                    val bnf_fp = BNF_FP_Def_Sugar.fp_sugar_of ctxt Tname
                    val ctxt' = case bnf_fp of NONE => ctxt
                                   | SOME fp =>
                                        Context.proof_map (Simps.map (fn ctxt =>
                                                ctxt addsimps #set_thms (#fp_bnf_sugar fp))) ctxt
                 in Seq.of_list sets
                 |> Seq.maps (fn s =>
                      case Term.fastype_of s
                        of \<^Type>\<open>fun _ \<^Type>\<open>set x\<close>\<close> =>
                              if x = element_ty
                              then Seq.single (s, ctxt')
                              else guess_set_opr ctxt' x element_ty
                                     |> Seq.map (fn (s',ctxt'') =>
                                          (Abs("", ty, \<^Const>\<open>Set.bind x element_ty\<close> $ (s $ Bound 0) $ s'), ctxt''))
                         | _ => error "Internal bug f07de235-2838-4483-b2f9-b0cce6d06676")
                end
              )
          | _ => Seq.empty

fun guess_self_rel ctxt 
  = guess_operator ctxt (fn (ctxt, D, L, bnf) =>
      let val ctxt' = case fp_sugar_of ctxt bnf
                        of NONE => ctxt
                         | SOME fp => ctxt (*TODO somthing maybe #fp_bnf_sugar fp*)
       in Seq.single (BNF_Def.mk_rel_of_bnf D L L bnf, ctxt')
      end)

fun guess_rel_mapper target_ty ctxt ty element_ty =
  let val [g'] = Name.invent (Variable.names_of ctxt) "g" 1
      val ([g], ctxt') = Variable.add_fixes [g'] ctxt
      val element_ty' = singleton target_ty element_ty
      val g_ty = element_ty --> element_ty' --> HOLogic.boolT
      val g_term = Free(g, g_ty)
      val known_rels = [(element_ty, g_term)]
   in guess_operator ctxt' (fn (ctxt, D, L, bnf) =>
        let val ctxt' = case fp_sugar_of ctxt bnf
                          of NONE => ctxt
                           | SOME fp => ctxt (*TODO somthing maybe #fp_bnf_sugar fp*)
         in Seq.single (BNF_Def.mk_rel_of_bnf D L (target_ty L) bnf, ctxt')
        end
      ) known_rels ty
   |> Seq.map (fn (rel_term', ctxt) =>
        (Abs("", g_ty, Term.abstract_over (g_term, rel_term')), ctxt))
  end

fun select_one_hint prop_name hints =
  let fun is_the_hint (\<^Const>\<open>Trueprop\<close> $ X) = is_the_hint X
        | is_the_hint (\<^Const>\<open>Pure.imp\<close> $ _ $ X) = is_the_hint X
        | is_the_hint X = (case Term.head_of X
                             of Const(N',_) => N' = prop_name
                              | _ => false)
   in case filter is_the_hint hints
        of [ret] => SOME ret
         | [] => NONE
         | _ => error ("More than one hint of "^ prop_name ^ " are given!")
  end

fun select_hints prop_name hints =
  let fun is_the_hint (\<^Const>\<open>Trueprop\<close> $ X) = is_the_hint X
        | is_the_hint (\<^Const>\<open>Pure.imp\<close> $ _ $ X) = is_the_hint X
        | is_the_hint X = (case Term.head_of X
                             of Const(N',_) => N' = prop_name
                              | _ => false)
   in filter is_the_hint hints
  end


(*quants: an array telling how to interpret the quantified variables in the first antecedent of the rule.
  It is used in generating the induction rule.
  quants[i] = 0 means interpret the variable as the abstract object
  quants[i] = i means interpret the variable as the i-th parameter of the \<phi>-type
  quants[i] = ~1 means interpret it as a fixed variable
  Note the quants is reversed against the quantified variables*)
fun mk_rule_by_guess_or_hint (unify_hint,guess_property,quants,ind_conv) rule (phi0 : phi_type) hint ctxt0 =
  let val (inst,inst',phi,ctxt01) = fix_phi_type true phi0 ctxt0
      val ((x_term, T_term, x_ty, arg_tys, model_ty), ctxt02) = fix_phi_term_params (#term phi) ctxt01
   in (case hint of SOME H =>
              let fun collect_ants (\<^Const>\<open>Pure.imp\<close> $ (\<^Const>\<open>Trueprop\<close> $ L) $ R) = L :: collect_ants R
                    | collect_ants (\<^Const>\<open>Trueprop\<close> $ _) = []
                    | collect_ants _ = error "Bad hint"
                  fun concl_of_hint (\<^Const>\<open>Pure.imp\<close> $ (\<^Const>\<open>Trueprop\<close> $ _) $ R) = concl_of_hint R
                    | concl_of_hint (X as \<^Const>\<open>Trueprop\<close> $ _) = X
                    | concl_of_hint _ = error "Bad hint"
                  val property = concl_of_hint H
                  val Envir.Envir inst_hint = unify_hint (ctxt02, H) property (x_term, T_term)
                  val H' = Envir.subst_term (#tyenv inst_hint, #tenv inst_hint) H
                  val ([H''], ctxt) = Variable.import_terms true [H'] ctxt02
               in Seq.single (Phi_Help.list_mk_conj (collect_ants H''), concl_of_hint H'', ctxt)
              end
           | _ => guess_property (x_term, T_term, x_ty, arg_tys, model_ty, phi) ctxt02)
   |> Seq.map (fn (ant, property, ctxt) => 
  let val inst_rule = Pattern.match (Proof_Context.theory_of ctxt) (Thm.concl_of rule, property)
                                    (Vartab.empty, Vartab.empty)
                   |> apsnd (Vartab.update_new (("Ant",0), (\<^typ>\<open>bool\<close>, ant)))
                   |> Phi_Help.env_to_table ctxt
      val rule' = Thm.instantiate inst_rule rule
      
      fun mk_free_table i ret (X $ Free (N,_)) =
            mk_free_table (i+1) (Symtab.update_new ((N,i)) ret) X
        | mk_free_table _ ret _ = ret
      val free_tabel = mk_free_table 0 Symtab.empty (T_term $ x_term)
      fun mk_ind_prop lev lambs (X $ Y) = mk_ind_prop lev lambs X $ mk_ind_prop lev lambs Y
        | mk_ind_prop lev lambs (Bound i) =
            if i < lev then Bound i else
           (case try List.nth (quants, i-lev)
              of NONE => error "The rule contains unspecified quantified variable"
               | SOME j => if j = ~1
                           then (case List.nth (lambs, i) of (N,T) => Var((N,1),T)) (*the ind rule is zero-indexed*)
                           else Bound (lev+j))
        | mk_ind_prop lev lambs (Abs (N,T,X)) =
              Abs (N,T, mk_ind_prop (lev+1) ((N,T)::lambs) X)
        | mk_ind_prop lev lambs (Free (N,T)) =
           (case Symtab.lookup free_tabel N
              of SOME i => Bound (lev + i)
               | NONE => Free (N,T))
        | mk_ind_prop _ _ X = X

      val (lambs, _, rule_concl) = Phi_Help.strip_meta_hhf (Phi_Help.leading_antecedent' rule')
      val ind_prop = mk_ind_prop 0 (rev lambs) (HOLogic.dest_Trueprop rule_concl)
      val ind = Phi_Type_Algebra.mk_ind_dest_ToA ctxt phi (K ind_prop)
              |> Conv.fconv_rule (ind_conv ctxt phi)

      val ((inst,[rule't]), ctxt't) = Variable.import true [rule'] ctxt
      val ind't = Thm.instantiate inst ind
      val rule'2 = singleton (Variable.export ctxt't ctxt) (ind't RS rule't)

   in (rule'2, phi, ctxt)
  end)
  end




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
      val ants = Phi_Help.conj_elims ctxt ants'
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


      

fun unify_hint_obj_eq (ctxt, hint) (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>\<phi>Equiv_Obj _ _\<close> $  _ $ T')) (x, T) =
  Unify.smash_unifiers (Context.Proof ctxt) [(T',T)] Envir.init
    |> Seq.chop 2
    |> (fn ([], _) => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
         | ([x], _) => x
         | _ => error ("Multi-resolution in hint: " ^ Syntax.string_of_term ctxt hint))

fun guess_property_obj_eq (x_term, T_term, x_ty, arg_tys, model_ty, (phi:phi_type)) ctxt0 =
  let fun mk_Ants ctxt (Ty::rev_arg_tys) (eq::eq_names) ants param_eqs (T_term $ A) =
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

      val arity = length arg_tys
      val rev_eq_names' = Name.invent (Variable.names_of ctxt0) "eq" arity
      val (rev_eq_names, ctxt) = Variable.add_fixes rev_eq_names' ctxt0
      val rev_arg_tys = rev arg_tys
      val (ants,param_eqs) = mk_Ants ctxt rev_arg_tys rev_eq_names [] [] T_term
      val ant = Phi_Help.list_mk_conj ants

      val eq_terms =
             if #is_recursive phi
             then guess_self_rel ctxt param_eqs x_ty
             else Seq.single (Var(("eq", 1), x_ty --> x_ty --> HOLogic.boolT), ctxt)
   in eq_terms
   |> Seq.map (fn (eq_term, ctxt') =>
        (ant, \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>\<phi>Equiv_Obj x_ty model_ty\<close> $ eq_term $ T_term), ctxt'))
  end

(*
fun gen_ants_obj_equal ctxt (x_ty, arg_tys, model_ty, hint0) =
  let fun mk_hint *)

fun gen_obj_equal' (phi0 : phi_type) hint0 thy =
  let val ctxt0 = Context.proof_of thy
      fun ind_conv ctxt phi =
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
              ) (K Conv.all_conv) ctxt
      val rules = mk_rule_by_guess_or_hint (unify_hint_obj_eq, guess_property_obj_eq, [0], ind_conv)
                                     @{thm \<phi>Equiv_Obj_rule} phi0 hint0 ctxt0
               |> Seq.map (fn (rule, phi, ctxt) =>
            let val rule' = obj_equal_reasoner ctxt rule
             in (if is_some hint0 orelse #is_recursive phi
                 then Phi_Sledgehammer_Solver.auto (SOME (#proof_id phi ^ "/obj_equal")) (ctxt, rule')
                 else (@{thm Premise_I} RS rule')
                   |> infer_eq ctxt
                   |> Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv 
                         (K (Conv.arg_conv (Conv.arg1_conv (Simplifier.rewrite ctxt)))) ctxt))
                |> singleton (Proof_Context.export ctxt ctxt0)
            end 
          )
   in Seq.chop 2 rules
   |> (fn ([], _) => raise Automation_Fail
        | ([rule'], _) =>
              Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 40
                                          ([],[]) NONE [rule'] thy
        | (rules,_) => (warning "More than one property instances are inferred.";
                        raise Automation_Fail))
  end

in

fun gen_obj_equal (phi,hints) thy =
  let val hint = select_one_hint \<^const_name>\<open>\<phi>Equiv_Obj\<close> hints
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

local

fun is_TF ty =
  (case dest_parameterized_phi_ty ty
     of ([],_,_) => false
      | (arg_tys,_,_) => (
   case dest_parameterized_phi_ty (Phi_Help.last arg_tys)
     of ([],_,_) => true
      | _ => false)
   handle TYPE _ => false)

fun unify_hint_TF (ctxt, hint) (\<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Transformation_Functor\<close>, _)
                                                      $ F1 $ _ $ _ $ _)) (x, F' $ _) =
  Unify.smash_unifiers (Context.Proof ctxt) [(F1,F')] Envir.init
    |> Seq.chop 2
    |> (fn ([], _) => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
         | ([x], _) => x
         | _ => error ("Multi-resolution in hint: " ^ Syntax.string_of_term ctxt hint))
  | unify_hint_TF (ctxt, hint) _ _ = error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)

fun guess_property_TF (x_term, FT_term, x_ty, arg_tys, model_ty, (phi:phi_type)) ctxt =
  let val T_ty = Phi_Help.last arg_tys
      val ([],element_ty,_) = dest_parameterized_phi_ty T_ty
      val F_term = (case FT_term of F $ _ => F
                                  | _ => error "Internal bug: Not a TF")

      val param_typs = Term.add_tfreesT element_ty []
      val (param_typs', ctxt'1) = Variable.invent_types (map snd param_typs) ctxt
                                |> apfst (map TFree)
      val inst_ty = TFrees.make (param_typs ~~ param_typs')
      val F'1_term = Term_Subst.instantiate_frees (inst_ty, Frees.empty) F_term
      
      val params = Term.add_frees F'1_term []      
      val (param_names', ctxt') = Variable.variant_fixes (map fst params) ctxt'1
      val params' = map2 (fn N => fn (_,T) => Free(N,T)) param_names' params
      val inst = Frees.make (params ~~ params')
      val F'_term = Term_Subst.instantiate_frees (TFrees.empty, inst) F'1_term

      val ant = map2 (fn (N,T) => fn p' => \<^Const>\<open>HOL.eq T\<close> $ Free(N,T) $ p') params params'
              |> Phi_Help.list_mk_conj
              |> (fn X => \<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_SIMP\<close> $ X)

      val TF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                       of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                           \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                          \<^Const>\<open>Transformation_Functor a b c d e f\<close> $ F_term $ F'_term
                        | _ => error "Internal bug")

   in guess_set_opr ctxt' x_ty element_ty
   |> Seq.maps (fn (D_term, ctxt'2) =>
        guess_rel_mapper (map (Term_Subst.instantiateT_frees inst_ty)) ctxt'2 x_ty element_ty
     |> Seq.map (fn (rel_mapper, ctxt'3) =>
          (ant, \<^Const>\<open>Trueprop\<close> $ (TF_head $ D_term $ rel_mapper), ctxt'3)))
  end

fun chk_unfolded (phi : phi_type) ctm =
  let val (N,_) = raw_term_name_typ (#term phi)
      fun chk (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = chk X
        | chk (Abs(_,_,X)) = chk X
        | chk (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) = chk T
        | chk (Const(N',_)) = N = N'
        | chk (Free(N',_)) = N = N'
        | chk (X $ _) = chk X
        | chk _ = false
   in if chk (Thm.term_of ctm)
      then warning "The phi-type is not unfolded by simplification and inductive destruction. \
                   \The reasoning may fail."
      else () ;
      Conv.all_conv ctm
  end


fun TF_reasoner ctxt sequent0 =
  case Thm.major_prem_of sequent0
    of _ $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => @{thm \<r>Success_I} RS sequent0
     | _ =>
  let val sequent = sequent0
      val (focus, lsequent) = Subgoal.focus ctxt 1 NONE sequent
      val ctxt' = #context focus

      val len = length (#prems focus)
      val constraint = List.nth (#prems focus, len - 1)
      val ant = List.nth (#prems focus, len - 2)
      val (_, term_U) = List.nth (#params focus, 1)
      val (name_U, _) = Term.dest_Free (Thm.term_of term_U)
      val term_to = (Const(\<^const_name>\<open>to\<close>, Phi_Syntax.mk_phi_type_ty (
                        Phi_Syntax.dest_phi_type_ty (Thm.typ_of_cterm term_U))
                          --> \<^Type>\<open>action\<close>)
                      $ Thm.term_of term_U)
                  |> Thm.cterm_of ctxt
      val rule_to = Thm.instantiate (TVars.empty,
                                     Vars.make [((("A",0),\<^typ>\<open>action\<close>),term_to)])
                                    @{thm Action_Tag_I}
      val rule_step = Drule.infer_instantiate ctxt [(("U",0),term_U)] @{thm \<phi>TA_TF_rule_step}

      fun instantiate_ToA ToA =
        case Thm.concl_of ToA
          of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ \<^Const>\<open>\<phi>TA_ind_target\<close>)
              => let
                val ToA' = ant RS (Thm.permute_prems 0 ~2 ToA)
                val prem = Thm.cprop_of ToA' |> Thm.dest_arg1
                val insts = Goal.init prem
                        |> Method.insert_tac ctxt' [constraint] 1
                        |> Seq.hd
                        |> Simplifier.full_simp_tac (Simps.equip ctxt') 1 |> Seq.hd
                        |> @{print}
                        |> Clasimp.fast_force_tac ctxt' 1
                        |> Seq.chop 21 |> fst
                        |> maps (fn th => let val th' = Goal.conclude th RS ToA'
                                              val th2 = th' RS @{thm Action_Tag_D}
                                           in [th2 RS rule_to]
                                          end)
                val _ = if length insts > 20
                        then warning "I find more than 20 instantiations which is very abnormal.\
                                     \ I only take the first 20 instantiations."
                        else ()
               in insts
              end
           | _ => []

      val ToAs = maps instantiate_ToA (List.take (#prems focus, len - 2))
      val ants'1 = Phi_Help.conj_elims ctxt ant
      fun is_Premis (\<^Const>\<open>Premise\<close> $ _ $ _) = true
        | is_Premis (\<^Const>\<open>Trueprop\<close> $ X) = is_Premis X
        | is_Premis _ = false
      val prem_ants = filter (is_Premis o Thm.concl_of) ants'1
      val ants = filter (not o is_Premis o Thm.concl_of) ants'1

      fun chk_U_ToA (\<^Const>\<open>times _\<close> $ X $ Y) = chk_U_ToA X andalso chk_U_ToA Y
        | chk_U_ToA (\<^Const>\<open>\<phi>Type _ _\<close> $ Var _ $ Free (N, _)) = N <> name_U
        | chk_U_ToA (\<^Const>\<open>ExSet _ _\<close> $ X) = chk_U_ToA X
        | chk_U_ToA (\<^Const>\<open>Subjection _\<close> $ X $ _) = chk_U_ToA X
        | chk_U_ToA (Abs(_,_,X)) = chk_U_ToA X
        | chk_U_ToA (X $ _) = chk_U_ToA X
        | chk_U_ToA _ = true
      val U_ToAs = Simplifier.simplify (Simps.equip ctxt) constraint
                |> @{print}
                |> HOLogic.conj_elims ctxt
                |> map (Phi_Help.repeat (fn th => th RS @{thm spec})
                     #> Phi_Help.repeat (fn th => th RS @{thm mp}))
                |> map_filter (fn th =>
                      case Thm.concl_of th
                        of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Imply _\<close> $ src $ _ $ _) =>
                                if chk_U_ToA src
                                then SOME (th RS rule_to)
                                else NONE
                         | _ => NONE)

(* filter (fn th =>
              case Thm.prop_of th of Const(\<^const_name>\<open>Trueprop\<close>, _)
                                        $ (Const (\<^const_name>\<open>\<phi>Equiv_Obj\<close>, _) $ _ $ _) => true
                                   | _ => false) prems *)

      val ctxt'' = ctxt'
            |> Context.proof_map (Phi_Reasoner.add_intro_rules (
                  map (fn rule => ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [], [], NONE)) (U_ToAs @ ToAs)))
            |> Context.proof_map (Phi_Reasoner.add_intro_rules (
                  map (fn rule => ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [], [], NONE)) ants))

      val lsequent'1 = (rule_step RS lsequent)
                    |> Method.insert_tac ctxt' prem_ants 1
                    |> Seq.hd

      val lsequent' = PLPR_Exhaustive.reason_exhaustively (SOME 2) (ctxt'', lsequent'1)
                    |> (fn SOME th => th
                         | NONE => raise Automation_Fail)

      (*fun do_work (focus:Subgoal.focus) sequent =
        let val prems = if has_eq_constraint then Phi_Help.front (#prems focus) else #prems focus
            val ctxt' = #context focus
            
         in Seq.empty
        end*)
   in Subgoal.retrofit ctxt'' ctxt (#params focus) (#asms focus) 1 lsequent' sequent
   |> Seq.hd
   |> Phi_Reasoners.defer_obligation_tac ctxt
   |> Seq.hd
   |> TF_reasoner ctxt
  end



fun gen_TF' (phi0 : phi_type) hint0 thy =
  let val ctxt0 = Context.proof_of thy
      fun ind_conv ctxt phi =
              Phi_Helper_Conv.hhf_conv (
                Phi_Helper_Conv.hhf_conv (fn ctxt => fn ctm =>
                  case Thm.term_of ctm
                    of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ \<^Const>\<open>\<phi>TA_ind_target\<close>)
                        => (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm Action_Tag_def}) then_conv
                            Conv.rewr_conv @{thm atomize_imp[symmetric]} then_conv
                            Conv.implies_concl_conv (Conv.rewr_conv @{thm atomize_imp[symmetric]} then_conv
                            Conv.implies_concl_conv (HOLogic.Trueprop_conv (
                                Conv.rewr_conv @{thm Action_Tag_def[symmetric, where A=\<phi>TA_ind_target]})))) ctm
                     | _ => Conv.all_conv ctm
                ) (fn ctxt => fn ctm =>
                  case Thm.term_of ctm
                    of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ \<^Const>\<open>\<phi>TA_ind_target\<close>)
                        => (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm Action_Tag_def}) then_conv
                            Conv.rewr_conv @{thm atomize_imp[symmetric]} then_conv
                            Conv.implies_concl_conv (Conv.rewr_conv @{thm atomize_imp[symmetric]} then_conv
                            Conv.implies_concl_conv (
                              Phi_Syntax.implication_conv
                              (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)) then_conv
                               chk_unfolded phi)
                              (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)) then_conv
                               chk_unfolded phi)
                              Conv.all_conv))) ctm
                     | _ => Conv.all_conv ctm)
              ) (K Conv.all_conv) ctxt
      val rules = mk_rule_by_guess_or_hint (unify_hint_TF, guess_property_TF, [0,~1,~1,~1], ind_conv)
                                            @{thm \<phi>TA_TF_rule} phi0 hint0 ctxt0
                |> Seq.map (fn (rule, phi, ctxt) =>
                      (TF_reasoner ctxt rule, ctxt))
               (*|> Seq.map (fn (rule, phi, ctxt) =>
            let val rule' = obj_equal_reasoner ctxt rule
             in (if is_some hint0 orelse #is_recursive phi
                 then Phi_Sledgehammer_Solver.auto (SOME (#proof_id phi ^ "/obj_equal")) (ctxt, rule')
                 else (@{thm Premise_I} RS rule')
                   |> infer_eq ctxt
                   |> Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv 
                         (K (Conv.arg_conv (Conv.arg1_conv (Simplifier.rewrite ctxt)))) ctxt))
                |> singleton (Proof_Context.export ctxt ctxt0)
            end 
          )*)
   in Seq.chop 2 rules
   |> (fn ([], _) => raise Automation_Fail
        | ([(rule',ctxt)], _) =>
          let val rule'' = Phi_Sledgehammer_Solver.auto (SOME (#proof_id phi0 ^ "/TF"))
                                                        (ctxt, rule')
           in Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 40
                                          ([],[]) NONE [rule''] thy
          end
        | (rules,_) => (warning "More than one property instances are inferred.";
                        raise Automation_Fail))
  end

in

fun gen_TF (phi,hints) thy =
  if is_TF (Term.fastype_of (#term phi))
  then let val hints = select_hints \<^const_name>\<open>Transformation_Functor\<close> hints
        in (case hints
              of [] => gen_TF' phi NONE thy
               | _ => fold (fn H => fn thy =>
                        gen_TF' phi (SOME H) thy
                        handle Automation_Fail => (
                          error ("Fail to reason the transformation functor:\n" ^
                                 Context.cases Syntax.string_of_term_global Syntax.string_of_term thy H))
                      ) hints thy)
           handle Automation_Fail => (
             warning "Fail to reason the equivelance between abstract objects." ;
             (if null hints then warning "You may want to annotate it by \<open>is \<open>\<phi>Equiv_Obj eq\<close>\<close>" else ());
             thy
           )
       end
  else thy

end

(*
fun gen_TF (phi,hints) thy =
  if is_TF (Term.fastype_of (#term phi))
  then let val hint = select_hint \<^const_name>\<open>Transformation_Functor\<close> hints    
        in gen_obj_equal' phi hint thy
           handle Automation_Fail => (
             warning "Fail to reason the equivelance between abstract objects." ;
             (if is_some hint then () else
               warning "You may want to annotate it by \<open>is \<open>\<phi>Equiv_Obj eq\<close>\<close>");
             thy
            )
       end
  else thy *)

(*** Install Automation ***)

val _ = Theory.setup (Context.theory_map (
   Phi_Type_Algebra.add_automation_on_def 100 gen_obj_equal
#> Phi_Type_Algebra.add_automation_on_def 110 gen_TF
))

end