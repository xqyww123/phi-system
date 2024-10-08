signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val parse_semimodule_phityp' : typ -> typ * typ option * typ * typ option * typ

val parse_semimodule_phityp : Proof.context
                           -> Phi_Type.phi_type
                           -> (sort * sort) option (*optionally lift the types to (sort_scalar, sort_model)*)
                           -> typ * typ option * typ * typ option * typ * Phi_Type.phi_type

val Guess_Scalar_Zero : bool -> guess_property
val Guess_Scalar_One : bool -> guess_property
val Guess_Scalar_Assoc : bool -> guess_property
val Guess_Zip_of_Semimodule : bool -> guess_property

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun parse_semimodule_phityp' ty =
  let val (reversed_argtys', x_ty0, model_ty0) = dest_parameterized_phi_ty ty
      fun err_parse () = raise Automation_Fail (fn () => let open Pretty in
                            [para "I only accept the semimodule \<phi>-type giving its element \<phi>-type as \
                                  \its last parameter and the sclara as its second last paramter. \
                                  \However, the parameters of the given \<phi>-type does not seem to meet \
                                  \this requirement."]
                        end)
      val (x_ele_ty0, s_ty0, T_model_ty) =
            case reversed_argtys'
              of (\<^Type>\<open>fun x_ele_ty \<^Type>\<open>BI T_model_ty\<close>\<close> :: s_ty :: _) => (SOME x_ele_ty, s_ty, SOME T_model_ty)
               | (s_ty :: _) => (NONE, s_ty, NONE)
               | _ => err_parse ()
   in (s_ty0, x_ele_ty0, x_ty0, T_model_ty, model_ty0)
  end

fun parse_semimodule_phityp ctxt phi0 lift_sorts =
  let val (s_ty0, x_ele_ty0, x_ty0, T_model_ty0, model_ty0) = parse_semimodule_phityp' (Term.fastype_of (#term phi0))
      val (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, phi) =
            case lift_sorts
              of SOME (sort_scalar, sort_model) =>
                  let val inst = lift_types_sort (Proof_Context.theory_of ctxt)
                                                 [(s_ty0, sort_scalar), (model_ty0, sort_model)]
                      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
                      val s_ty = Term_Subst.instantiateT inst s_ty0
                      val x_ty = Term_Subst.instantiateT inst x_ty0
                      val model_ty = Term_Subst.instantiateT inst model_ty0
                      val T_model_ty = Option.map (Term_Subst.instantiateT inst) T_model_ty0
                      val phi = instantiate_phi (inst',Vars.empty) phi0
                   in (s_ty, x_ele_ty0, x_ty, T_model_ty, model_ty, phi)
                  end
               | NONE => (s_ty0, x_ele_ty0, x_ty0, T_model_ty0, model_ty0, phi0)

   in (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, phi) (*TODO: extend me! return x_ele_ty!*)
  end

fun Guess_Scalar_framework involve_T (sorts, mk_goal_term_and_parse_result) =
  Guess_Framework (fn (phi, ctxt) =>
    let val (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi sorts
        val idx = maxidx_of_phi phi ~1 + 1
        val ((_, FT_term), ctxt) = fix_phi_term_params phi ctxt
        fun parse_fail () = raise Automation_Fail (fn () => let open Pretty in
                              [para "Fail to parse the \<phi>-type as a module \<phi>-type"]
                            end)
        val (opt_T_term, _, F_term) =
          if involve_T
          then case separate_module_tyopr [] FT_term
                 of SOME (T,c,F) => (SOME T,c,F)
                  | NONE => parse_fail ()
          else case separate_scalar_tyopr [] FT_term
                 of SOME (T,c,F) => (T, c, F)
                  | _ => parse_fail ()
  
        val eta_F_term = Var (("unfolded_F", idx), Term.fastype_of F_term)
(*Abs ("s", s_ty, Abs ("T", Term.fastype_of T_term, Abs ("x", x_ty,
                            \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ (Term.incr_boundvars 3 F_term $ Bound 2 $ Bound 1))))*)
        val (goal_term, parse_result) =
                mk_goal_term_and_parse_result (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, idx, F_term, eta_F_term, opt_T_term, ctxt)
     in (goal_term, parse_result o Thm.prop_of, phi, ctxt)
    end)

(*
fun Guess_Scalar_framework (unfold_place, sorts, mk_goal_term_and_parse_result)
                           (phi : phi_type) ctxt =
  let val (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi sorts
      val module_ty = s_ty --> mk_phi_type_ty (model_ty, x_ele_ty) --> mk_phi_type_ty (model_ty, x_ty)
      val idx = maxidx_of_phi phi ~1 + 1
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term

      val eta_F_term = Abs ("s", s_ty, Abs ("T", Term.fastype_of T_term, Abs ("x", x_ty,
                          \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ (Term.incr_boundvars 3 F_term $ Bound 2 $ Bound 1))))
      val (goal_term, parse_result) =
              mk_goal_term_and_parse_result (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, module_ty, idx, F_term, eta_F_term, T_term, ctxt)
      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow unfold_place Conv.fun_conv (Conv.arg1_conv (
                      Conv.abs_conv (Conv.abs_conv (Conv.abs_conv (fn (_, ctxt) =>
                      fn ctm => Conv.rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                           (#equations phi)) ctm) o snd) o snd) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
        |> Option.map (apsnd (simplify_guessing_reasoning ctxt))
   of SOME (inst, ret) =>
        let val (prop, params, conds, ants) = parse_result (Thm.prop_of ret)
            val ants = constrain_antecedents conds ants
            val (inst'2, ctxt) = Variable.import_inst true (prop :: ants) ctxt
            val (prop :: ants) = map (Term_Subst.instantiate inst'2) (prop :: ants)
            val params = map (Option.map (Term_Subst.instantiate inst'2)) params
         in Seq.single (ants, prop, params,
                        phi |> instantiate_phi (inst, Vars.empty)
                            |> instantiate_phi (Phi_Help.certify_vars (Context.Proof ctxt) inst'2),
                        ctxt)
        end
    | NONE => guess_fail ctxt phi (K [])
  end
*)

fun Guess_Scalar_Zero is_closed = Guess_Scalar_framework false (SOME (\<^sort>\<open>type\<close>, \<^sort>\<open>one\<close>),
      fn (s_ty, _, x_ty, _, model_ty, idx, F_term, eta_F_term, _, _) =>
          (HOLogic.Trueprop $ (\<^Const>\<open>Guess_Scalar_Zero s_ty model_ty x_ty\<close>
              $ \<^Const>\<open>Pure.type s_ty\<close>
              $ \<^Const>\<open>Pure.type model_ty\<close>
              $ \<^Const>\<open>Pure.type x_ty\<close>
              $ F_term $ eta_F_term
              $ Var (("zero", idx), s_ty)
              $ Var (("ants", idx), HOLogic.boolT)
              $ Var (("conds", idx), HOLogic.boolT)),
           fn _ (*Trueprop*) $ (Const _ (*Guess_Scalar_Zero*) $ ty_s $ ty_model $ ty_x
                  $ F $ _ $ zero $ ants $ conds) =>
              let val (s_ty, model_ty, x_ty) = (Logic.dest_type ty_s, Logic.dest_type ty_model, Logic.dest_type ty_x)
               in (HOLogic.Trueprop $ (
                      (if is_closed then \<^Const>\<open>Closed_Semimodule_Zero s_ty x_ty model_ty\<close>
                                    else \<^Const>\<open>Semimodule_Zero s_ty x_ty model_ty\<close>)
                        $ F $ zero),
                   NONE :: parse_inst_params_from_phi_term (F $ Term.dummy),
                   conds, ants)
              end)
      )

fun Guess_Scalar_One is_intro = Guess_Scalar_framework false (NONE,
      fn (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, idx, F_term, eta_F_term, T_term, _) =>
        let val a1_ty = TVar(("a\<^sub>1",idx),\<^sort>\<open>type\<close>)
            val xL = if is_intro then a1_ty else x_ty
            val xR = if is_intro then x_ty else a1_ty
            val (x_ele_ty, T_model_ty, T_term) =
                case (x_ele_ty, T_model_ty, T_term)
                  of (SOME a, SOME b, SOME c) => (a,b,c)
                   | _ => raise Automation_Fail (fn () => [])
         in (\<^Const>\<open>Trueprop\<close> $ (
              (if is_intro then \<^Const>\<open>Guess_Scalar_One\<^sub>I s_ty T_model_ty model_ty x_ele_ty x_ty a1_ty\<close>
                           else \<^Const>\<open>Guess_Scalar_One\<^sub>E s_ty T_model_ty model_ty x_ele_ty x_ty a1_ty\<close>)
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type T_model_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ele_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ F_term $ eta_F_term $ T_term
                $ Var (("T\<^sub>1", idx), Phi_Syntax.mk_phi_type_ty (model_ty, a1_ty))
                $ Var (("one", idx), s_ty)
                $ Var (("Dx", idx), xL --> HOLogic.boolT)
                $ Var (("f", idx), xL --> xR)
                $ Var (("P", idx), xL --> HOLogic.boolT)
                $ Var (("ants", idx), HOLogic.boolT)
                $ Var (("conds", idx), HOLogic.boolT)),
             fn _ (*Trueprop*) $ (Const _ (*Guess_Scalar_One*) $ ty_s $ _ $ ty_model $ _ $ ty_x
                    $ F $ _ $ _ $ T1 $ one $ Dx $ f $ P $ ants $ conds) =>
              let val (s_ty, model_ty, x_ty) =
                        (Logic.dest_type ty_s, Logic.dest_type ty_model, Logic.dest_type ty_x)
                  val ty_x_1 = domain_type (Term.fastype_of T1)
               in (HOLogic.Trueprop $ (
                    (if is_intro then \<^Const>\<open>Semimodule_One\<^sub>I s_ty x_ty model_ty ty_x_1\<close>
                                 else \<^Const>\<open>Semimodule_One\<^sub>E s_ty x_ty model_ty ty_x_1\<close>)
                        $ F $ T1 $ one $ Dx $ f $ P),
                   NONE :: parse_inst_params_from_phi_term (F $ Term.dummy),
                   conds, ants)
              end)
        end
       )

fun Guess_Scalar_Assoc is_intro = Guess_Scalar_framework true (NONE,
      fn (s_ty, x_ele_ty, x_ty, T_model_ty, model_ty, idx, F_term, eta_F_term, T_term, ctxt) =>
        let val x_ele_ty = the x_ele_ty
            val T_model_ty = the T_model_ty
            val T_term = the T_term

            val ct = TVar (("c\<^sub>t", idx), \<^sort>\<open>type\<close>)
            val (ss, st) = (TVar (("s\<^sub>s", idx), \<^sort>\<open>type\<close>), TVar (("s\<^sub>t", idx), \<^sort>\<open>type\<close>))
            val (at, as_t) = (TVar (("a\<^sub>t", idx), \<^sort>\<open>type\<close>), TVar (("a\<^sub>s\<^sub>_\<^sub>t", idx), \<^sort>\<open>type\<close>))
            val (Fs, Ft) = (Var (("F\<^sub>s", idx), ss --> mk_phi_type_ty(ct, at) --> mk_phi_type_ty(model_ty, as_t)),
                            Var (("F\<^sub>t", idx), st --> mk_phi_type_ty(T_model_ty, x_ele_ty) --> mk_phi_type_ty(ct, at)))
            
            val as_t = TVar (("a\<^sub>s\<^sub>_\<^sub>t", idx), \<^sort>\<open>type\<close>)
         in (\<^Const>\<open>Trueprop\<close> $ (
                  (if is_intro then \<^Const>\<open>Guess_Scalar_Assoc\<^sub>I s_ty T_model_ty model_ty x_ele_ty x_ty ss at ct as_t st\<close>
                               else \<^Const>\<open>Guess_Scalar_Assoc\<^sub>E s_ty T_model_ty model_ty x_ele_ty x_ty ss at ct as_t st\<close>)
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type T_model_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ele_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ Fs $ Ft $ F_term $ eta_F_term $ T_term
                $ Var(("Ds",0), ss --> HOLogic.boolT)
                $ Var(("Dt",0), st --> HOLogic.boolT)
                $ Var(("Dx",0), ss --> st --> (if is_intro then as_t --> HOLogic.boolT else x_ty --> HOLogic.boolT))
                $ Var(("smul",0), ss --> st --> s_ty)
                $ Var(("f", 0), ss --> st --> (if is_intro then as_t --> x_ty else x_ty --> as_t))
                $ Var(("ants", 0), HOLogic.boolT)
                $ Var(("conds", 0), HOLogic.boolT)),

             fn _ (*Trueprop*) $ (Const _ (*Guess_Scalar_Assoc*) $ _ $ _ $ _ $ _ $ _
                    $ Fs $ Ft $ Fc $ _ $ T $ Ds $ Dt $ Dx $ smul $ f $ ants $ conds) =>
                 let val \<^Type>\<open>fun ss' \<^Type>\<open>fun st' \<^Type>\<open>fun t1 t2\<close>\<close>\<close> = Term.fastype_of f
                     val (as_t', ast') = if is_intro then (t1, t2) else (t2, t1)
                     val \<^Type>\<open>fun _ \<^Type>\<open>fun \<^Type>\<open>fun a' \<open>Type(_, [c'])\<close>\<close> \<^Type>\<open>fun at' \<open>Type (_, [ct'])\<close>\<close>\<close>\<close> = Term.fastype_of Ft
                     val \<^Type>\<open>fun sc' \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<open>Type(_, [cst'])\<close>\<close>\<close>\<close> = Term.fastype_of Fc
                     val head = if is_intro then \<^Const>\<open>Semimodule_Scalar_Assoc\<^sub>I ss' at' ct' as_t' cst' st' a' c' sc' ast'\<close>
                                            else \<^Const>\<open>Semimodule_Scalar_Assoc\<^sub>E ss' at' ct' as_t' cst' st' a' c' sc' ast'\<close>
                     val xx = Thm.cterm_of ctxt (HOLogic.Trueprop $ (head $ Fs $ Ft $ Fc $ T $ Ds $ Dt $ Dx $ smul $ f))
                  in (HOLogic.Trueprop $ (head $ Fs $ Ft $ Fc $ T $ Ds $ Dt $ Dx $ smul $ f),
                      NONE :: parse_inst_params_from_phi_term (Fc $ Term.dummy $ T),
                      conds, ants)
                 end)
        end)


fun Guess_Zip_of_Semimodule is_zip = Guess_Scalar_framework false ( SOME (\<^sort>\<open>type\<close>, \<^sort>\<open>sep_magma_1\<close>),
      fn (s_ty, _, x_ty, _, model_ty, idx, F_term, eta_F_term, _, ctxt) =>
           (\<^Const>\<open>Trueprop\<close> $ (
              (if is_zip then \<^Const>\<open>Guess_Zip_of_Semimodule s_ty model_ty x_ty\<close>
                         else \<^Const>\<open>Guess_Unzip_of_Semimodule s_ty model_ty x_ty\<close>)
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ F_term $ eta_F_term
                $ Var(("scalar_domain",idx), s_ty --> HOLogic.boolT)
                $ Var(("abstract_domain",idx), s_ty --> s_ty --> (if is_zip then \<^Type>\<open>prod x_ty x_ty\<close> else x_ty) --> HOLogic.boolT)
                $ Var(("f", idx), s_ty --> s_ty -->
                          (if is_zip then \<^Type>\<open>prod x_ty x_ty\<close> --> x_ty else x_ty --> \<^Type>\<open>prod x_ty x_ty\<close>))
                $ Var(("antecedents", idx), HOLogic.boolT)
                $ Var(("conditions", idx), HOLogic.boolT)),
            fn _ (*Trueprop*) $ (Const _ (*Guess_(Un)Zip_of_Semimodule*) $ ty_s  $ ty_model $ ty_x
                    $ F $ _ $ Ds $ Dx $ f $ ants $ conds) =>
              let val (s_ty, model_ty, x_ty) =
                        (Logic.dest_type ty_s, Logic.dest_type ty_model, Logic.dest_type ty_x)
                  val xxx = Thm.cterm_of ctxt (
                              HOLogic.Trueprop $ (
                      (if is_zip then \<^Const>\<open>Semimodule_SDistr_Homo\<^sub>Z s_ty x_ty model_ty\<close>
                                 else \<^Const>\<open>Semimodule_SDistr_Homo\<^sub>S s_ty x_ty model_ty\<close>)
                        $ F $ Ds $ Dx $ f))
               in (HOLogic.Trueprop $ (
                      (if is_zip then \<^Const>\<open>Semimodule_SDistr_Homo\<^sub>Z s_ty x_ty model_ty\<close>
                                 else \<^Const>\<open>Semimodule_SDistr_Homo\<^sub>S s_ty x_ty model_ty\<close>)
                        $ F $ Ds $ Dx $ f),
                   NONE :: parse_inst_params_from_phi_term (F $ Term.dummy),
                   conds, ants)
              end)
)


(*
fun Guess_Scalar_One_E (phi : phi_type) ctxt =
  let val (s_ty, x_ele_ty, x_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi NONE
      val idx = maxidx_of_phi phi ~1 + 1
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term

      val eta_F_term = Abs ("s", s_ty, Abs ("T", Term.fastype_of T_term, Abs ("x", x_ty,
                          \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ (Term.incr_boundvars 3 F_term $ Bound 2 $ Bound 1))))

      val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Scalar_One s_ty model_ty x_ele_ty x_ty\<close>
              $ \<^Const>\<open>Pure.type s_ty\<close>
              $ \<^Const>\<open>Pure.type model_ty\<close>
              $ \<^Const>\<open>Pure.type x_ele_ty\<close>
              $ \<^Const>\<open>Pure.type x_ty\<close>
              $ F_term $ eta_F_term $ T_term
              $ Var (("one", idx), s_ty)
              $ Var (("Dx", idx), x_ty --> HOLogic.boolT)
              $ Var (("f", idx), x_ty --> x_ele_ty)
              $ Var (("ants", idx), HOLogic.boolT)
              $ Var (("conds", idx), HOLogic.boolT))

      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 5 Conv.fun_conv (Conv.arg1_conv (
                      Conv.abs_conv (Conv.abs_conv (Conv.abs_conv (fn (_, ctxt) =>
                      fn ctm => Conv.rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                           (#equations phi)) ctm) o snd) o snd) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
        |> Option.map (apsnd (simplify_guessing_reasoning ctxt))
   of SOME (inst, ret) =>
       (case Thm.prop_of ret
          of _ (*Trueprop*) $ (_ (*Guess_Scalar_One*) $ _ $ _ $ _ $ _
                $ F $ _ $ T $ one $ Dx $ f $ ants $ conds) =>
            let val ants = constrain_antecedents conds ants
                val head = \<^Const>\<open>Semimodule_One s_ty x_ele_ty model_ty x_ty\<close>
                val prop = HOLogic.Trueprop $ (head $ F $ T $ one $ Dx $ f)
             in Seq.single (ants, prop,
                            NONE :: parse_inst_params_from_phi_term (F $ Term.dummy $ T),
                            instantiate_phi (inst, Vars.empty) phi,
                            ctxt)
            end
           | _ => error "BUG")
    | NONE => guess_fail ctxt phi (K [])
  end
*)

(*
fun Guess_Unzip_of_Semimodule ctxt (phi : phi_type) (s_ty, x_ty, model_ty, typ_expr) =
  let val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Unzip_of_Semimodule s_ty model_ty x_ty\<close>
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ typ_expr
                $ Var(("scalar_domain",0), s_ty --> HOLogic.boolT)
                $ Var(("abstract_domain",0), s_ty --> s_ty --> x_ty --> HOLogic.boolT)
                $ Var(("zip", 0), s_ty --> s_ty --> x_ty --> \<^Type>\<open>prod x_ty x_ty\<close>)
                $ Var(("antecedents", 0), HOLogic.boolT)
                $ Var(("conditions", 0), HOLogic.boolT))
      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 4 Conv.fun_conv (Conv.arg1_conv (
                      Conv.top_rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                               (#equations phi)) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
   of SOME (inst, ret) =>
        (case Thm.prop_of ( ret
                         |> Simplifier.simplify (ctxt addsimps
                                @{thms' Premise_norm[where mode=\<open>default\<close>]
                                        Premise_norm[where mode=\<open>MODE_GUARD\<close>]
                                        Ant_Seq_reduct
                                        HOL.imp_conjR[folded Ant_Seq_def]
                                        HOL.all_conj_distrib[folded Ant_Seq_def]}) )
           of _ (*Trueprop*) $ (_ (*Guess_Unzip_of_Semimodule*)
                    $ _ $ _ $ _ $ _ $ Ds $ Dx $ zi $ ants $ cond)
                => (Ds, Dx, zi, constrain_antecedents cond ants, inst)
            | _ => error "BUG")
    | NONE => raise Automation_Fail (fn () => let open Pretty in
              [block (text "Fail to guess the semimodule unzip operation as there is no registered \
                           \record giving the semimodule between scalar algebra" @
                      [brk 1, Syntax.pretty_typ ctxt s_ty, brk 1] @
                      text "abstrct algebra" @
                      [brk 1, Syntax.pretty_typ ctxt x_ty, brk 1] @
                      text "and concrete algebra" @
                      [brk 1, Syntax.pretty_typ ctxt model_ty, str ".", brk 1] @
                      text "You may either annotate the form of the rule or provide the record by"),
               block ([keyword1 "lemma", brk 1, str "[\<phi>reasoner]", brk 1,
                       str "\<open>", Syntax.pretty_term ctxt goal_term, str "\<close>"])]
            end)
  end


fun Guess_Zip_of_Semimodule ctxt (phi : phi_type) (s_ty, x_ty, model_ty, typ_expr) =
  let val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Zip_of_Semimodule s_ty model_ty x_ty\<close>
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ typ_expr
                $ Var(("scalar_domain",0), s_ty --> HOLogic.boolT)
                $ Var(("abstract_domain",0), s_ty --> s_ty --> \<^Type>\<open>prod x_ty x_ty\<close> --> HOLogic.boolT)
                $ Var(("zip", 0), s_ty --> s_ty --> \<^Type>\<open>prod x_ty x_ty\<close> --> x_ty)
                $ Var(("antecedents", 0), HOLogic.boolT)
                $ Var(("conditions", 0), HOLogic.boolT))
      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 4 Conv.fun_conv (Conv.arg1_conv (
                      Conv.top_rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                               (#equations phi)) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
   of SOME (inst, ret) =>
        (case Thm.prop_of ( ret
                         |> Simplifier.simplify (ctxt addsimps
                                @{thms' Premise_norm[where mode=\<open>default\<close>]
                                        Premise_norm[where mode=\<open>MODE_GUARD\<close>]
                                        Ant_Seq_reduct
                                        HOL.imp_conjR[folded Ant_Seq_def]
                                        HOL.all_conj_distrib[folded Ant_Seq_def]}) )
           of _ (*Trueprop*) $ (_ (*Guess_Zip_of_Semimodule*)
                    $ _ $ _ $ _ $ _ $ Ds $ Dx $ zi $ ants $ cond)
                => (Ds, Dx, zi, constrain_antecedents cond ants, inst)
            | _ => error "BUG")
    | NONE => raise Automation_Fail (fn () => let open Pretty in
              [block (text "Fail to guess the semimodule zip operation as there is no registered \
                           \record giving the semimodule between scalar algebra" @
                      [brk 1, Syntax.pretty_typ ctxt s_ty, brk 1] @
                      text "abstrct algebra" @
                      [brk 1, Syntax.pretty_typ ctxt x_ty, brk 1] @
                      text "and concrete algebra" @
                      [brk 1, Syntax.pretty_typ ctxt model_ty, str ".", brk 1] @
                      text "You may either annotate the form of the rule or provide the record by"),
               block ([keyword1 "lemma", brk 1, str "[\<phi>reasoner]", brk 1,
                       str "\<open>", Syntax.pretty_term ctxt goal_term, str "\<close>"])]
            end)
  end
*)


end