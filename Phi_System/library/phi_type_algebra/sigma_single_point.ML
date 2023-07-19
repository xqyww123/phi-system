signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

(* val sigma_trivial_homo : hint list -> Phi_Type_Algebra.derive *)

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers


fun guess_projector bnf i insts =
  let val (Tname, targs) = case eBNF_Info.T_of_bnf bnf
                             of Type (N, args) => (N, args)
                              | _ => error "BUG yovXA3RKT76zCozhObW5NQ"
      val target = List.nth (targs, i)
      val casex = eBNF_Info.case_of1 bnf
      val case_args = Term.binder_types (Term.fastype_of casex)
      fun mk_one ty =
        let val args = Term.binder_types ty
            val arity = length args
            fun mk i (ty :: tys) = if ty = target
                                   then Abs ("x", ty, mk 0 tys)
                                   else Abs ("x", ty, mk (i+1) tys)
              | mk i [] = if i >= arity
                          then raise Automation_Fail ("Type " ^ Tname ^ " does not have the " ^
                                        string_of_int (i+1) ^ "th projector")
                          else Bound i
         in mk arity args
        end
   in Term.subst_atomic_types (targs ~~ insts) casex
   |> fold (fn ty => fn X => X $ mk_one ty) case_args
  end

fun fail () = raise Automation_Fail "Fail to guess the \<Sigma> trivial homomorphism."

fun guess_ssp _ sigma_ty (T as \<^Type>\<open>prod ta tb\<close>) =
      if ta = sigma_ty
      then SOME (Abs ("x", T, \<^Const>\<open>True\<close>), \<^Const>\<open>fst ta tb\<close>, \<^Const>\<open>snd ta tb\<close>)
      else NONE
  | guess_ssp ctxt sigma_ty (T as Type(Tname, args0)) =
      if exists_subtype (fn ty => ty = sigma_ty) T
      then let val bnf = eBNF_Info.get_bnf1 ctxt Tname
               fun pass_args _ (Ps, sels, rev_maps, rev_lives') [] = (Ps, sels, rev_maps, rev_lives')
                 | pass_args i (Ps, sels, rev_maps, rev_lives') ((is_live, arg) :: args) =
                     if arg = sigma_ty then fail ()
                     else if is_live
                     then case guess_ssp ctxt sigma_ty arg
                       of SOME (P, sel, mapper) =>
                            let val prj = guess_projector bnf i args0 $ Bound 0
                                val t' = Term.body_type (Term.fastype_of mapper)
                             in pass_args (i+1) ((P $ prj) :: Ps, (sel $ prj) :: sels, mapper :: rev_maps, t' :: rev_lives') args
                            end
                        | NONE => pass_args (i+1) (Ps, sels, (Abs("x", arg, Bound 0)) :: rev_maps, arg :: rev_lives') args
                     else pass_args (i+1) (Ps, sels, rev_maps, rev_lives') args
               val (Ps, sels, rev_maps, rev_lives') = pass_args 0 ([], [], [], [])
                                                                  (eBNF_Info.tyargs_is_live_or_dead bnf ~~ args0)
               val (S, Ps') = case sels of [] => fail () 
                                 | (S :: SS) =>
                              (S, fold (fn S' => fn Ps => (\<^Const>\<open>HOL.eq sigma_ty\<close> $ S $ S') :: Ps) SS Ps)
               val P = Abs("x", T, Phi_Help.list_mk_conj Ps')
               val (deads, lives) = eBNF_Info.classify_bnf_dead_live bnf args0
               val mapper = eBNF_Info.mk_map_of_bnf deads lives (rev rev_lives') bnf
                         |> fold (fn M => fn X => X $ M) rev_maps
            in SOME (P, S, mapper)
           end
      else NONE
  | guess_ssp _ sigma_ty T =
      if T = sigma_ty
      then fail ()
      else NONE


fun guess_property_SSP (x_term0, FT_term0, phi0) ctxt =
  Seq.of_list (separate_type_operator_and_its_non_parameterized_parameter FT_term0)
    |> Seq.map (fn (T_term0, F_term0) =>
  let val (instTy, _, phi) = instantiate_phi_to_pair_x ctxt (T_term0, phi0)

      val inst = Term_Subst.instantiate (instTy, Vars.empty)
      val (x_term, FT_term, F_term, T_term) = (inst x_term0, inst FT_term0, inst F_term0, inst T_term0)

      val (_, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([], element_ty, _) = dest_parameterized_phi_ty (Term.fastype_of T_term)
      val (sigma_ty, _) = case element_ty
                            of \<^Type>\<open>prod a b\<close> => (a,b)
                             | _ => error "BUG wN93cAxkQ2e4WYDsi8LfVA"

      val (P, sel, mapper) = case guess_ssp (Context.Proof ctxt) sigma_ty x_ty
                               of SOME X => X
                                | NONE => fail ()

      val SSP = (case (Term.fastype_of F_term, Term.fastype_of mapper)
                  of (\<^Type>\<open>fun \<^Type>\<open>fun \<^Type>\<open>prod a b\<close> \<^Type>\<open>set c\<close>\<close> \<^Type>\<open>fun d \<^Type>\<open>set e\<close>\<close>\<close>, \<^Type>\<open>fun _ f\<close>) =>
                    let val Fb = Term.map_types (subst_ty [(element_ty, b), (d, f)]) F_term
                     in \<^Const>\<open>\<Sigma>_Homo\<^sub>E a b c d e f\<close> $ F_term $ Fb $ P
                          $ (Abs ("x", x_ty, \<^Const>\<open>Pair a f\<close> $ (sel $ Bound 0) $ (mapper $ Bound 0)))
                    end
                   | _ => error "Internal bug")

   in ([], HOLogic.Trueprop $ SSP, x_term, FT_term, phi)
  end)

fun gen_STH hint0 (phi0 : phi_type) generic =
  let val ctxt0 = Context.proof_of generic
      val unify_hint_SH = hint_unify_by_type_operator (
            fn Const(\<^const_name>\<open>\<Sigma>_Homo\<^sub>E\<close>, _) $ F $ _ $ _ $ _ => F)
      val 
   in ()
  end

end
