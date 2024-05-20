structure Phi_Pointer_Of = Pattern_Translation (
  val check_pattern = Syntax.check_terms
  val parse_pattern = Syntax.parse_term
  val multi_translation_err_msg =
        "Fail to infer the pointer \<phi>-type as there are different possible resolutions"
)

local

val derv_rule = @{lemma
  \<open> Derive_Pointer_Of (assn::prop) ptr
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> TERM ptr \<close>
  by this
}

fun guess_pointer ctxt eqs =
  let val RHSS = map (Phi_Help.mk_term o #2 o Phi_Help.dest_eq_c o Thm.cconcl_of) eqs
              |> foldr1 Conjunction.mk_conjunction
      val rule = Thm.instantiate (TVars.empty,
                    Vars.make [((("assn",0),\<^Type>\<open>prop\<close>),RHSS)]) derv_rule
   in case Phi_Reasoner.reason NONE NONE ctxt rule
        of SOME ret => (Logic.dest_term (Thm.concl_of ret))
         | NONE => raise Phi_Type.Automation_Fail (fn () => let open Pretty in
                      [paragraph (text "Fail to infer the pointer assertion from the syntax")]
                   end)
  end

fun pointer_of_deriver (_, pos) intrs (phityp : phi_type) lthy =
  let open Phi_Type
      fun shouldn't_be_given name =
        raise Automation_Fail (fn () => let open Pretty in
            [block (text name @ [brk 1] @ text "is meaningless here in deriving \<open>Pointer_Of\<close>")]
          end)
      fun chk_intr (_, group, _, meth, notes, bundle) =
        if is_some group
        then shouldn't_be_given "Reasoner group or priority"
        else if is_some meth
        then shouldn't_be_given "Proof tactic"
        else if not (null notes)
        then shouldn't_be_given "Note"
        else if not (null notes)
        then shouldn't_be_given "Bundle"
        else ()
      val _ = List.app chk_intr intrs
      val hints = map_filter #1 intrs |> map fst
      val ptr = case hints
          of [] => guess_pointer lthy (#equations phityp)
           | [x] => (case x
                 of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Pointer_Of\<close>, _) $ Ty $ assn) =>
                    Thm.cterm_of lthy assn
                  | _ => raise Automation_Fail (fn () => let open Pretty in
                      [block (text "Bad hint" @ [brk 1, Syntax.pretty_term lthy x])]
                    end))
           | _ => raise Automation_Fail (fn () => let open Pretty in
                    [block (text "The deriver of \<open>Pointer_Of\<close> accepts at most one hint.")]
                  end)
   in lthy
   |> Context.proof_map (Phi_Pointer_Of.add [
        (10)
      ])
  end

in



end