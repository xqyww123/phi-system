signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val SE_Trime_Empty__generation_pass : Phi_Type_Algebra.rule_generation_pass
val SE_Trime_Empty : Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct

open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*fun set_to_empty th =
  let fun parse (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = parse X
        | parse (Const(\<^const_name>\<open>Identity_Element\<^sub>I\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ V) $ _) =
            if is_Var (Term.head_of V) then SOME @{thm' Identity_Element\<^sub>I_empty} else NONE
        | parse (Const(\<^const_name>\<open>Identity_Element\<^sub>E\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ V)) =
            if is_Var (Term.head_of V) then  SOME @{thm' Identity_Element\<^sub>E_empty} else NONE
        | parse (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = parse X
        | parse (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = parse X
        | parse _ = NONE
   in map_index (fn (i, tm) => case parse tm
                                 of SOME rule => try (fn th => rule RSN (i+1, th)) th
                                  | NONE => NONE) (Thm.prems_of th)
              |> map_filter I
  end*)

fun simp ctxt th =
  Conv.fconv_rule (Phi_Conv.hhf_concl_conv Simplifier.rewrite ctxt) th

fun SE_Trime_Empty (phi : phi_type) thy =
  let fun fetch_properties name = Phi_Type_Algebra.lookup_property_unify thy (#term phi) name
                               |> map #3
      fun fetch_property name =
            case fetch_properties name
              of [] => raise Automation_Fail ("Property " ^ name ^ " is not given")
               | x :: _ => x
      (*fun has_reasoned rule =
        *)

      val TVs = fetch_properties \<^const_name>\<open>Type_Variant_of_the_Same_Type_Operator\<close>
      val IE_I = fetch_property \<^const_name>\<open>Identity_Element\<^sub>I\<close>
      val IE_E = fetch_property \<^const_name>\<open>Identity_Element\<^sub>E\<close>
      val OE = fetch_property \<^const_name>\<open>Object_Equiv\<close>
      val intros = @{thms' derive_\<A>SE_trim_I derive_\<A>SE_trim_I_TH}
                |> map (Thm.transfer'' thy)
                |> maps (fn rule => map_filter (fn TV => SOME (rule OF [TV, IE_I, OE])
                                                         handle THM _ => NONE) TVs)
      val elims  = @{thms' derive_\<A>SE_trim_E derive_\<A>SE_trim_E_TH}
                |> map (Thm.transfer'' thy)
                |> maps (fn rule => map_filter (fn TV => SOME (rule OF [TV, IE_E])
                                                         handle THM _ => NONE) TVs)

      val ctxt' = Context.proof_of thy
               |> Config.put Phi_Reasoner_solve_obligation_and_no_defer 1
      fun red th = fold (fn tm => fn (i,th) =>
            let fun work (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = work X
                  | work (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = work X
                  | work (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = work X
                  | work (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $ eq) =
                      (case Term.fastype_of eq of \<^Type>\<open>fun \<^Type>\<open>unit\<close> _\<close> =>
                              (i, @{thm' Object_Equiv_fallback} RSN (i+1, th))
                          | _ => (i+1, th))
                  | work (Const(\<^const_name>\<open>Identity_Element\<^sub>I\<close>, _)
                            $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ Const(\<^const_name>\<open>\<phi>None\<close>, _))
                            $ _) =
                      (i, @{thm' Identity_Element\<^sub>I_empty} RSN (i+1, th))
                  | work (Const(\<^const_name>\<open>Identity_Element\<^sub>E\<close>, _)
                            $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ Const(\<^const_name>\<open>\<phi>None\<close>, _))) =
                      (i, @{thm' Identity_Element\<^sub>E_empty} RSN (i+1, th))
                  | work (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.eq\<close>, \<^Type>\<open>fun \<^Type>\<open>unit\<close> _\<close>) $ _ $ _)) =
                      (i+1, @{lemma \<open>Premise any (x = y)\<close> for x :: unit by (simp add: Premise_def)} RSN (i+1, th))
                  | work (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =
                      Thm.permute_prems 0 i th
                        |> Phi_Reasoner.reason (SOME 1) true ctxt'
                        |> Option.map (Thm.permute_prems 0 (~i))
                        |> the_default th
                        |> pair i
                  | work _ = (i+1, th)
             in work tm
            end) (Thm.prems_of th) (0, th)

      val thy' = Context.theory_of thy
      fun reason th =
        let val concl = Thm.concl_of th
            fun get_target (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = get_target X
              | get_target (Const _ $ _ $ T) = T
              | get_target (X $ _) = get_target X
            val reasoned = Phi_Reasoner.has_reasoner concl (fn r =>
                  case #tactic r of Phi_Reasoner.Tac_Rule ths =>
                          exists (fn th => Pattern.matches thy' (get_target concl, get_target (Thm.concl_of th))) ths
                     | _ => false) thy
         in if reasoned then NONE
            else SOME (snd (red th) |> simp ctxt')
        end

      val rules = map_filter (reason o Phi_Help.beta_eta_contract) (intros @ elims)
   in thy
   |> Phi_Help.generic_theory_mapping (fn m =>
        Phi_Reasoner.add_rules (map (fn rule => 
            ([rule], #pos phi, Phi_Reasoner.TO_BE_OVERRIDE, 40, [], [], NONE))
                                  (Morphism.fact m rules)))
  end

fun SE_Trime_Empty__generation_pass (_, gen, _, ctxt) th =
  let val rctxt = Config.put Phi_Reasoner_solve_obligation_and_no_defer 1 ctxt
      fun reason th =
        let val concl = Thm.cconcl_of th
            fun fix_target ctm =
              case Thm.term_of ctm
                of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ _) => fix_target (Thm.dest_arg ctm)
                 | (Const _ $ _ $ _ $ _ $ _) => map Drule.mk_term (snd (Drule.strip_comb ctm))
                 | (_ $ _) => fix_target (Thm.dest_fun ctm)
            val ((inst, _), ctxt') = Variable.import true (fix_target concl) rctxt
            val th' = Thm.instantiate inst th
         in Phi_Reasoner.reason NONE true ctxt' th'
         |> Option.map (singleton (Variable.export ctxt' rctxt)
                     #> simp ctxt)
        end
   in case reason th
   of SOME ret => gen ret
    | NONE => []
  end

end