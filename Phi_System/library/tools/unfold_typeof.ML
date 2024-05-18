signature SEMANTIC_TYPE_TOOLS = sig

val unfold_typeof : morphism -> Proof.context -> cterm -> thm option
val unfold_typeof_simproc : simproc

end

structure Semantic_Type_Tools : SEMANTIC_TYPE_TOOLS = struct

val rule0 = @{lemma
  \<open> Semantic_Type T TY ||| EXCEPTION TEXT(\<open>S\<close>)
\<Longrightarrow> Inhabited T        ||| EXCEPTION TEXT(\<open>I\<close>)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> \<t>\<y>\<p>\<e>\<o>\<f> T \<equiv> TY \<close>
  by (simp add: atomize_Branch EXCEPTION_def, rule SType_Of_unfold, simp)
}

fun unfold_typeof _ ctxt cterm =
  let val T_term = Thm.dest_arg cterm
   in Drule.infer_instantiate ctxt [(("T",0),T_term)] rule0
   |> Phi_Reasoner.reason NONE NONE (Config.map Phi_Reasoner.trace (fn i => i-3)ctxt)
   |> Option.map (
        Conv.fconv_rule (Conv.implies_conv (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' Premise_def}))
                                           Conv.all_conv))
  handle PLPR_EXCEPTION "S" => (
    Phi_Reasoner.warn_pretty (Context.Proof ctxt) 2 (fn () => let open Pretty in
        block (text "Fail to unfold" @ [brk 1, Syntax.pretty_term ctxt (Thm.term_of cterm), brk 1] @
               text "because fail to infer the semantic type of \<phi>-type" @
               [brk 1, Syntax.pretty_term ctxt (Thm.term_of T_term), str ".", brk 1] @
               text "I need property (" @
               [brk 1, Syntax.pretty_term ctxt (
                  Const(\<^const_name>\<open>Semantic_Type\<close>, dummyT) $ Thm.term_of T_term $ \<^term>\<open>TY::TY\<close>),
                str ")"])
      end); NONE )
       | PLPR_EXCEPTION "I" => (
    Phi_Reasoner.warn_pretty (Context.Proof ctxt) 2 (fn () => let open Pretty in
        block (text "Fail to unfold" @ [brk 1, Syntax.pretty_term ctxt (Thm.term_of cterm), brk 1] @
               text "because fail to infer the Inhabitance of \<phi>-type" @
               [brk 1, Syntax.pretty_term ctxt (Thm.term_of T_term)] @
               text "I need property (" @
               [brk 1, Syntax.pretty_term ctxt (
                  Const(\<^const_name>\<open>Inhabited\<close>, dummyT) $ Thm.term_of T_term),
                str ")"])
      end); NONE )
  end

val unfold_typeof_simproc = Simplifier.make_simproc \<^context> "\<phi>.\<t>\<y>\<p>\<e>\<o>\<f>" {
        lhss = [\<^pattern>\<open>\<t>\<y>\<p>\<e>\<o>\<f> ?T\<close>],
        proc = unfold_typeof
    }

end

structure Syntactical_Type_Of = Pattern_Translation (
  val check_pattern = Syntax.check_terms
  val parse_pattern = Syntax.parse_term
  val multi_translation_err_msg =
        "The \<phi>-type is registered with multiple inconsistent semantic types!"
)

local

fun register_parse_rule pos rule ctxt =
  let val (_, prems, concl) =Phi_Help.strip_meta_hhf (Thm.prop_of rule)
      fun chk_atom (tm as Free _) = tm
        | chk_atom (tm as Var _) = tm
        | chk_atom tm = error (let open Pretty in string_of (
              block (text "Bad rule of Semantic_Type," @
                     [brk 1, Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm, brk 1] @
                     text "must be an atom")
          ) end)
      val subst = map_filter (fn prem =>
            case snd (PLPR_Syntax.concl_of_antecedent [] prem)
              of Const(\<^const_name>\<open>Semantic_Type\<close>, _) $ T $ TY =>
                  SOME (chk_atom TY, Const(\<^const_syntax>\<open>SType_Of\<close>, dummyT) $ T)
               | _ => NONE
              ) prems
      val (T,TY) = case snd (PLPR_Syntax.concl_of_antecedent [] concl)
                     of Const(\<^const_name>\<open>Semantic_Type\<close>, _) $ T $ TY => (T,TY)
      val TY = subst_atomic subst TY
   in ctxt
   |> Syntactical_Type_Of.add [
        (10, PLPR_Pattern.strip_typs T, pos,
            Syntactical_Type_Of.By_Pattern [Syntax.replace_types_to_dummy TY]) ]
  end

in

val _ = Theory.setup (Context.theory_map (
  Phi_Reasoner.add_pass (\<^term>\<open>Gen_Syntax_Rule_of \<t>\<y>\<p>\<e>\<o>\<f>\<close>,
                         \<^pattern_prop>\<open>Semantic_Type _ _\<close>,
    fn pos => fn (rules, group, pats, G, ctxt) =>
                 (rules, group, pats, G, fold (register_parse_rule pos) rules ctxt) )
))

end
