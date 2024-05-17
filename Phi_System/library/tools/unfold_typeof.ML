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
