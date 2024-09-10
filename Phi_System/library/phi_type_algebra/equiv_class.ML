signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val equiv_class : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers


fun guess_property (phi:phi_type) ctxt =
  let val ((_,T_term), ctxt) = fix_phi_term_params phi ctxt
      val (_, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi)) 

   in Seq.single
        ([],
         \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Equiv_Class x_ty model_ty\<close> $ T_term $ \<^Const>\<open>HOL.eq x_ty\<close>),
         NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end


val IH_rewr = @{lemma 
  \<open>(Ant \<Longrightarrow> Equiv_Class (\<lambda>x. x \<Ztypecolon> OPEN undefined T) r @tag \<phi>TA_subgoal A)
 \<equiv> (Ant @tag \<phi>TA_ANT \<Longrightarrow> Equiv_Class (\<lambda>x. x \<Ztypecolon> T) r) \<close>
  by (unfold Action_Tag_def atomize_imp OPEN_def) }

val CL_rewr = @{lemma 
  \<open>(Ant \<Longrightarrow> P @tag \<phi>TA_subgoal A)
 \<equiv> (Ant \<Longrightarrow> P) \<close>
  by (unfold Action_Tag_def atomize_imp OPEN_def) }

fun gen_equiv_class (_, name) instruction (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const>\<open>Equiv_Class _ _\<close> $ T $ _ => T)
      fun extract_oprs_from_hint (\<^Const>\<open>Equiv_Class _ _\<close> $ _ $ eq) = [eq]
        | extract_oprs_from_hint _ = []

      val equip_expansion = equip_expansion_ss phi0
      val ind_conv = default_ind_conv (
        fn _ => error "BUG lcV6vGmkQVaAPfW5Acrngw",
        fn ctxt => fn _ =>
           (Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_noact} then_conv
            Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv))

      val pre_simp = default_pre_simplifier (Phi_Conv.meta_alls_conv (fn ctxt => fn ctm =>
           (Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_rev}) ctm) o snd)

      val varifier = K (K NONE)

      fun reasoning phi ctxt sequent =
            default_reasoning true default_reasoning_configure varifier
                              (exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))) phi ctxt sequent

      val solver = K NONE
      val simp = K I

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint, guess_property, @{thm' \<phi>TA_EC_rule},
                                      [(NONE, ind_conv, reasoning)],
                                      solver, pre_simp, simp)
                                    phi0 instruction thy
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s false phi0 [(name, [rule])]
        |> Local_Theory.declaration {syntax=false,pervasive=false, pos = #3 instruction} (
              fn m => fn lthy => lthy
                  |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
                  |> Phi_Reasoner.add_rule (#3 instruction) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %Equiv_Class_derived}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule]
                  |> Config.restore_generic Phi_Reasoner.trace lthy)
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val equiv_class = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Equiv_Class") gen_equiv_class


end
