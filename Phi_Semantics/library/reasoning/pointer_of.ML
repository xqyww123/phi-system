structure Phi_Pointer_Of = Pattern_Translation (
  val check_pattern = Syntax.check_terms
  val parse_pattern = Syntax.parse_term
  val multi_translation_err_msg =
        "Fail to infer the pointer \<phi>-type as there are different possible resolutions"
)

local

val derv_rule = @{lemma
  \<open> Derive_Pointer_Of assn ptr
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> TERM ptr \<close>
  by this
}

fun guess_pointer ctxt eqs =
  let fun infer_one eq =
        let val (LHS, RHS) = Phi_Help.dest_eq_c (Thm.cconcl_of eq)
            val T = case Thm.term_of LHS
                      of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T => T
                       | T => T
         in Drule.infer_instantiate ctxt [(("assn",0), RHS)] derv_rule
         |> Phi_Reasoner.reason NONE NONE ctxt
         |> Option.mapPartial (fn th =>
        let val term = Logic.dest_term (Thm.concl_of th)
            val frees = Term.add_frees term []
                     |> subtract (op =) (Term.add_frees T [])
            val vars  = Term.add_vars  term []
                     |> subtract (op =) (Term.add_vars T [])
         in if null frees andalso null vars
            then NONE
            else SOME (HOLogic.mk_prod (T, term))
        end)
        end

      val red_pairs = map_filter infer_one eqs

      val thy = Proof_Context.theory_of ctxt
      fun chk_all_equiv [] = NONE
        | chk_all_equiv [x] = SOME x
        | chk_all_equiv (x::y::L) =
            if Pattern.equiv thy (x,y)
            then chk_all_equiv (y::L)
            else NONE

   in case chk_all_equiv red_pairs
        of SOME ret => HOLogic.dest_prod ret
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
      val (T, ptr) = case hints
          of [] => guess_pointer lthy (#equations phityp)
           | [x] => (case x
                 of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Pointer_Of\<close>, _) $ Ty $ assn) =>
                    (Ty, assn)
                  | _ => raise Automation_Fail (fn () => let open Pretty in
                      [block (text "Bad hint" @ [brk 1, Syntax.pretty_term lthy x])]
                    end))
           | _ => raise Automation_Fail (fn () => let open Pretty in
                    [block (text "The deriver of \<open>Pointer_Of\<close> accepts at most one hint.")]
                  end)
   in lthy
   |> Context.proof_map (Phi_Pointer_Of.add [
        (10, T, pos, Phi_Pointer_Of.By_Pattern [ptr])
      ])
  end

open Phi_Type

in

val pointer_of_deriver : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
      = pointer_of_deriver

end