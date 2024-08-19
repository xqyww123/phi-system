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
\<Longrightarrow> TERM (T, ptr) \<close>
  by this
}

val Derive_Pointer_Of_I = @{lemma
  \<open>Derive_Pointer_Of (x \<Ztypecolon> T) (Some ptr)\<close>
  by (simp add: Derive_Pointer_Of_def)
}

fun guess_pointer ctxt eqs =
  let fun infer_one eq =
        let val (LHS, RHS) = Phi_Help.dest_eq_c (Thm.incr_indexes_cterm 1 (Thm.cconcl_of eq))
            val cT =
                case Thm.term_of LHS
                  of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => Thm.dest_arg LHS
                   | _ => LHS
         in Drule.infer_instantiate ctxt [(("assn",0), RHS), (("T",0), cT)] derv_rule
         |> Phi_Reasoner.reason NONE NONE ctxt
         |> Option.mapPartial (fn th =>
        let val ret = Logic.dest_term (Thm.concl_of th)
            val (T,term) = HOLogic.dest_prod ret
            val frees = Term.add_frees term []
                     |> subtract (op =) (Term.add_frees T [])
            val vars  = Term.add_vars  term []
                     |> subtract (op =) (Term.add_vars T [])
         in if null frees andalso null vars
            then (case term
                    of Const(\<^const_name>\<open>Some\<close>, _) $ ptr => SOME (HOLogic.mk_prod (T, ptr))
                     | _ => NONE)
            else NONE
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

      val _ = Phi_Reasoner.info_pretty lthy 0 (fn () =>
                let open Pretty
                    val (xty,mty) = Phi_Syntax.dest_phi_type_ty (fastype_of T)
                    val c_ty = Phi_Syntax.dest_BI_ty (fastype_of ptr)
                 in block ([str "Inferred: ", Syntax.pretty_term lthy (
                                  \<^Const>\<open>Pointer_Of xty mty c_ty\<close> $ T $ ptr)])
                end)

      val rule = Derive_Pointer_Of_I
              |> Drule.infer_instantiate lthy [(("T",0), Thm.cterm_of lthy T),
                                               (("ptr",0), Thm.cterm_of lthy ptr)]

   in lthy
   |> Local_Theory.declaration {syntax=false, pervasive=false, pos=pos} (fn m =>
        Phi_Pointer_Of.add [
          (10, Morphism.term m T, pos, Phi_Pointer_Of.By_Pattern [Morphism.term m ptr])
        ]
     #> Phi_Reasoner.add_rule pos Phi_Reasoner.TO_BE_OVERRIDE'
                               (SOME @{reasoner_group %deriving_pointer_derived})
                               ([],[]) NONE [Morphism.thm m rule] )
  end

open Phi_Type

in

val pointer_of_deriver : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
      = pointer_of_deriver

val _ = Theory.setup (Context.theory_map (Syntax_Phases.term_check 200 "syntax_of_<pointer_of>" (
  fn ctxt => fn tms =>
    let val qchk = Term.exists_Const (fn (\<^const_name>\<open>pointer_of_syntax\<close>, _) => true
                                       | (\<^const_name>\<open>pointer_val_of_syntax\<close>, _) => true
                                       | _ => false)

        fun fail_coerce tm =
              error (let open Pretty in string_of (
                      block (text "Fail to coerce" @ [brk 1,
                          Syntax.pretty_term ctxt tm, brk 1] @ text "to an assertion")
                   ) end)

        fun coerce_VAL v mty tm
              = (case tm
                   of \<^Const_>\<open>\<phi>Type x_ty _\<close> $ x $ T =>
                        \<^Const>\<open>\<phi>Type x_ty mty\<close> $ x
                            $ (\<^Const>\<open>Val x_ty mty\<close> $ v $ T)
                    | _ => fail_coerce tm)
      (*fun coercion \<^Type>\<open>VAL\<close> tm = tm
          | coercion (TVar _) tm = tm
          | coercion (TFree _) tm = tm
          | coercion ty tm =
              if ty = \<^typ>\<open>fiction\<close>
              then coerce_fiction tm
              else fail_coerce tm*)

        fun trans bvs (\<^Const>\<open>pointer_of_syntax _ _\<close> $ tm) =
             (case Phi_Pointer_Of.translate (Context.Proof ctxt) bvs tm
                of [ret] => SOME ret
                 | _ => error (let open Pretty in string_of (
                          block (text "The pointer of" @ [brk 1,
                              Syntax.pretty_term ctxt tm, brk 1] @ text "is unknown.")
                      ) end))
          | trans bvs (\<^Const>\<open>pointer_val_of_syntax _ _ mty\<close> $ v $ tm) =
             (case Phi_Pointer_Of.translate (Context.Proof ctxt) bvs tm
                of [ret] => SOME (coerce_VAL v mty ret)
                 | _ => error (let open Pretty in string_of (
                          block (text "The pointer of" @ [brk 1,
                              Syntax.pretty_term ctxt tm, brk 1] @ text "is unknown.")
                      ) end))
          | trans bvs (A $ B) =
              (case (trans bvs A, trans bvs B)
                 of (SOME A', SOME B') => SOME (A' $ B')
                  | (SOME A', NONE) => SOME (A' $ B)
                  | (NONE, SOME B') => SOME (A $ B')
                  | (NONE, NONE)    => NONE )
          | trans bvs (Abs (N,T,X)) =
              (case trans ((N,T)::bvs) X of SOME X' => SOME (Abs (N,T,X'))
                             | NONE => NONE)
          | trans _ _ = NONE

        fun translate tm =
          case trans [] tm
            of SOME tm' => tm'
             | NONE => tm

     in if exists qchk tms
     then map translate tms
     else tms
    end
)))

end