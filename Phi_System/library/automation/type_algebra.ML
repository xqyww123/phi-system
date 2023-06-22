signature PHI_TYPE_ALGEBRA = sig
include PHI_TYPE_ALGEBRA

val gen_obj_equal : automation_on_def

end

structure Phi_Type_Algebra : PHI_TYPE_ALGEBRA = struct
open Phi_Type_Algebra

(*** Objective Equal ***)

exception Obj_Eq_Fail

local

fun set_last_schematic_var ctxt rule0 =
  let val rule = Phi_Reasoner.beta_eta_contract rule0
      val (t1,t2,tm) =
        case Thm.prop_of rule
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
      val v = case Thm.prop_of rule
                of _ (*Trueprop*) $ (_ (*\<phi>Equal_Obj*) $ Var v $ _) => v
                 | _ => error "Internal bug 5d769e14-74ca-4afb-8d43-672e0afc5470"
      val P = case snd v
                of \<^Type>\<open>fun a \<open>\<^Type>\<open>fun b _\<close>\<close>\<close> => Abs("",a,Abs("",b,\<^term>\<open>True\<close>))
                 | _ => error "Internal bug a74fc08c-d9c1-4b19-99b2-4f18a07b31aa"
   in Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt P)]) rule
  end

fun infer_eq ctxt rule =
 (case Thm.major_prem_of rule
    of _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (Const(\<^const_name>\<open>All\<close>, _) $ _ ) $ _) =>
        infer_eq ctxt (@{thm \<phi>Equiv_Obj_rule_move_all} RS rule)
     | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>, _)) =>
        (@{thm \<phi>Equiv_Obj_rule_move_set_eq_end} RS (@{thm simp_thms(21)[THEN iffD2]} RS rule))
          |> set_last_schematic_var ctxt
     | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
        infer_eq ctxt (@{thm \<phi>Equiv_Obj_rule_move_set_eq} RS rule)
     | _ (*Trueprop*) $ Const(\<^const_name>\<open>True\<close>, _) =>
        (@{thm TrueI} RS rule)
          |> set_eq_when_it_is_constant_true ctxt
     | _ => error "internal bug 7147bf3f-9e7d-4ffc-a40b-aa621a4fca21")
  handle THM _ => raise Obj_Eq_Fail

(*
fun infer_eq_conv ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>conj\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>, _) =>
          Conv.rewr_conv @{thm simp_thms(21)[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _ =>
         (Conv.arg_conv infer_eq_conv then_conv
          Conv.rewr_conv @{thm imp_conjR[folded atomize_eq, symmetric]}) ctm
     | _ => Conv.all_conv ctm *)


fun gen_obj_equal' (phi : phi_type) eq_hint thy =
  let val ctxt0 = Context.proof_of thy
      val (eq_term, ctxt01) = Variable.import_terms true
              (case eq_hint of SOME eq => [eq] | _ => []) ctxt0
      val ((_, T_term, const, _, _), ctxt02) = fix_phi_type true (#const phi) ctxt01
      val insts = (case eq_term of [eq] => [(("eq",0), Thm.cterm_of ctxt02 eq)] | _ => [])

      fun mk_Ants ants pats (T_term $ (A as Free (_, Ty))) ctxt =
           (let val ((_, A_term, _, x_ty, s_ty), ctxt'1) = fix_phi_type true A ctxt
                val [eq'] = Name.invent (Variable.names_of ctxt) "eq" 1
                val ([eq],ctxt') = Variable.add_fixes [eq'] ctxt'1
                val typ = x_ty --> x_ty --> \<^typ>\<open>bool\<close>
                val ant = \<^Const>\<open>\<phi>Equiv_Obj x_ty s_ty\<close> $ Free(eq, typ) $ A_term
                val pat = singleton (Variable.export_terms ctxt' ctxt'1) ant
             in mk_Ants (ant::ants) (pat::pats) T_term ctxt'
            end
            handle TYPE _ => (ants, pats, ctxt))
        | mk_Ants ants pats _ ctxt = (ants, pats, ctxt)
      val (ants,pats,ctxt) = mk_Ants [] [] T_term ctxt02
      val ant = Phi_Help.list_mk_conj ants

      val rule = Drule.infer_instantiate ctxt
                  ((("T",0), Thm.cterm_of ctxt T_term) ::
                   (("Ant",0), Thm.cterm_of ctxt ant) :: insts)
                  @{thm \<phi>Equiv_Obj_rule}
               |> Conv.gconv_rule (Conv.forall_conv (Conv.forall_conv (K (Conv.implies_concl_conv (
                    Phi_Helper_Conv.expand_aggregated_imps (Conv.all_conv)
                  ))) o snd) ctxt) 1

      val arg_tys = Term.binder_types (Term.fastype_of const)
      val P_term = fold_rev (fn T => fn X => Abs("",T,X)) arg_tys \<^const>\<open>True\<close>
      val ind = snd (#ind_ToA phi)
              |> Drule.infer_instantiate ctxt [(("P",0), Thm.cterm_of ctxt P_term)]
              |> Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv (fn _ =>
                    HOLogic.Trueprop_conv (
                      Conv.arg1_conv (Conv.rewr_conv @{thm Premise_True[THEN Eq_TrueI]}) then_conv
                      Conv.rewr_conv @{thm simp_thms(15)[folded atomize_eq]})) ctxt)

      val ctxt'r = Context.proof_map (Phi_Reasoner.adds (map (fn pat => {
                name = \<^term>\<open>Local_\<phi>Equiv_Obj\<close>,
                pos = \<^here>,
                mode = Phi_Reasoner.LOCAL_CUT,
                pattern = [(HOLogic.mk_Trueprop pat, 1000)],
                blacklist = [],
                tactic = Phi_Reasoners.wrap (fn ctxt => Thm.assumption (SOME ctxt) 1)
            }) pats)) ctxt

      val (ctxt',rule') = Phi_Reasoner.reason NONE (ctxt'r, ind RS rule)
              |> (fn SOME ctxt_rule => ctxt_rule
                   | NONE => raise Obj_Eq_Fail)

      val rule'2 =
       (if is_some eq_hint
        then Phi_Sledgehammer_Solver.auto (SOME (#proof_id phi ^ "/obj_equal")) (ctxt', rule')
        else (@{thm Premise_I} RS rule')
          |> infer_eq ctxt
          |> Conv.fconv_rule (Conv.arg_conv (Conv.arg1_conv (Simplifier.rewrite ctxt))))
       |> singleton (Proof_Context.export ctxt' ctxt0)
   in Phi_Reasoner.add_intro_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [rule'2] thy
  end

val select_hint = get_first (fn Const(\<^const_name>\<open>\<phi>Equiv_Obj\<close>, _) $ eq $ _ => SOME eq
                              | _ => NONE)

in

fun gen_obj_equal (phi,hints) thy =
  let val hint = select_hint hints
   in gen_obj_equal' phi hint thy
      handle Obj_Eq_Fail => (
        warning "Fail to reason the equivelance between abstract objects." ;
        (if is_some hint then () else
          warning "You may want to annotate the equivelance relation by \<open>is \<open>\<phi>Equiv_Obj eq\<close>\<close>");
        thy
      )
  end

val _ = Theory.setup (Context.theory_map (
  Phi_Type_Algebra.add_automation_on_def 100 gen_obj_equal
))

end

end