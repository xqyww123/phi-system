(* FILE: library/system/sys.ML
   AUTHOR: Qiyuan Xu

   Several core operations in IDE-CP.
*)

signature PHI_SYS = sig
  include PHI_SYS

  (** Basic Operations **)
  val cast : cterm -> Proof.context -> thm -> thm
  val cast_exception : cterm -> Proof.context -> thm -> thm

  val accept_proc : context_state -> context_state

  val set_param : term -> context_state -> context_state
  val set_param_cmd : string -> context_state -> context_state
  val set_label : string -> context_state -> context_state

  val synthesis : cterm -> Proof.context -> thm -> thm

  val obligation_proof :  (Proof.context -> (string * string) * (string * thm list) list -> unit)
        -> Proof_Context.mode -> string -> Method.text option
        -> (thm -> Proof.state -> Proof.state)
        -> (binding * typ option * mixfix) list
        -> (Thm.binding * (term * term list) list) list
        -> thm -> Proof.state -> thm list * Proof.state

end

structure Phi_Sys : PHI_SYS = struct
open Thm Phi_Envir Term Phi_Sys

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg'' th = Seq.make (fn () => (@{print} th; raise NDBG th))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty))) *)

(** Basic Operations **)

val cast = Phi_Working_Mode.cast
val cast_exception = Phi_Working_Mode.cast_exception

val conv_E_thms =
  @{thms add_0_right[where 'a=\<open>'a::sep_magma set\<close>, folded atomize_eq]
         add_0_right[where 'a=\<open>'b \<Rightarrow> 'a::sep_magma set\<close>, folded atomize_eq]
         add_0_left[where 'a=\<open>'a::sep_magma set\<close>, folded atomize_eq]
         add_0_left[where 'a=\<open>'b \<Rightarrow> 'a::sep_magma set\<close>, folded atomize_eq]
         zero_fun[folded atomize_eq]
         mult_zero_right[where 'a=\<open>'a::sep_magma set\<close>, folded atomize_eq]
         mult_zero_left[where 'a=\<open>'a::sep_magma set\<close>, folded atomize_eq]
   }

fun export_codeblock ctxt (param_s, param_ret) rule assm sequent0 =
  let val (_,_,_,_,E) = Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequent0)
      val Free param_ret' = Thm.term_of param_ret
      fun has_bound_ret (Free X) = (X = param_ret')
        | has_bound_ret (A $ B) = has_bound_ret A orelse has_bound_ret B
        | has_bound_ret (Abs (_,_,X)) = has_bound_ret X
        | has_bound_ret _ = false
      val sequent = if has_bound_ret E
                    then let val E' = Term.absfree param_ret' E
                                   |> Thm.cterm_of ctxt
                             val E_idx = Thm.maxidx_of_cterm E' + 1
                             val ex_rule = Thm.incr_indexes E_idx @{thm \<phi>ex_quantify_E}
                                        |> Drule.infer_instantiate ctxt [(("E",E_idx),E')]
                          in sequent0 RS ex_rule end
                    else sequent0
   in
     sequent |> Thm.implies_intr assm
             |> Drule.forall_intr_list [param_s, param_ret]
             |> (fn th => (th COMP_INCR rule)
                       |> Conv.fconv_rule (Phi_Syntax.pending_construction_abnm_conv
                             (Conv.repeat_conv (Conv.rewrs_conv conv_E_thms))))
  end

structure CodeBlock_Idx = Proof_Data (
  type T = int
  val init = K 0
)


fun accept_proc' (ctxt,sequent) =
  let open Phi_Syntax
    val rule' = sequent RS @{thm \<phi>assemble_proc}
    val \<^Const_>\<open>Pure.all _\<close> $ Abs (_, _, \<^Const_>\<open>Pure.all _\<close> $ Abs (_, ret_ty,
            \<^Const_>\<open> Pure.imp for _ _ \<close>))
        = Phi_Help.leading_antecedent' rule'

    val rule =
          if Term.maxidx_of_typ ret_ty <> ~1
          then(case ret_ty
                 of Type (\<^type_name>\<open>\<phi>arg\<close>, [TVar V]) =>
                      let val (f,_,_,_,_) = Phi_Syntax.dest_PendingConstruction (Thm.concl_of sequent)
                          val _ = warning "The return arity of a procedure is not fixed.\
                                          \ Assume there is no return."
                          val _ = Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
                              Pretty.block [Pretty.str "In procedure ", Syntax.pretty_term ctxt f],
                              Pretty.block [
                                Pretty.str "the arity of the return is not fixed, but a variable ",
                                Syntax.pretty_typ ctxt ret_ty]
                           ])
                      in Thm.instantiate (TVars.make [(V,\<^ctyp>\<open>unit\<close>)], Vars.empty) rule'
                      end)
          else rule'

    val \<^Const_>\<open>Pure.all _\<close> $ Abs (_, _, \<^Const_>\<open>Pure.all _\<close> $ Abs (_, ret_ty,
            \<^Const_>\<open> Pure.imp for codeblk_term _ \<close>))
        = Phi_Help.leading_antecedent' rule

    val blk_idx = CodeBlock_Idx.get ctxt
    val (ret_name, ctxt'1) = Generic_Variable_Access.assign_anony_local_val (SOME ret_ty) ctxt
    val ([s_name], ctxt') = Proof_Context.add_fixes [
                                   (Binding.name ("\<s>" ^ string_of_int blk_idx), NONE, NoSyn)] ctxt'1
                         |> apsnd (CodeBlock_Idx.map (fn i => i+1))
    val codeblk_cterm =
          Term.subst_bounds ([Free (ret_name, ret_ty), Free (s_name, \<^typ>\<open>resource\<close>)], codeblk_term)
              |> Thm.cterm_of ctxt
    val param_cterms = (Free (s_name, \<^typ>\<open>resource\<close>), Free (ret_name, ret_ty))
              |> apply2 (Thm.cterm_of ctxt)

    val (_,_,f,_) = Phi_Syntax.dest_CodeBlock_c codeblk_cterm
    val _ = if Thm.maxidx_of_cterm f <> ~1
            then error (Pretty.string_of (Pretty.chunks [
                    Pretty.str "The pending procedure to be accepted has schematic variable(s)!",
                    Syntax.pretty_term ctxt (Thm.term_of f)
                 ]))
            else ()


    val ([codeblk],ctxt'2) = Assumption.add_assms
            (fn _ => fn [assm] => (export_codeblock ctxt' param_cterms rule assm, I))
            [codeblk_cterm] ctxt'
  in
    (ctxt'2, @{thm \<phi>accept_proc} OF [sequent, codeblk])
  end

fun accept_proc (ctxt,sequent0) =
  let
    val sequent = Phi_Procedure.simp_monads ctxt sequent0
    val (f,_,_,_,_) = Phi_Syntax.dest_PendingConstruction (Thm.concl_of sequent)
  in case f of Const (\<^const_name>\<open>Return\<close>, _) $ _
         => (ctxt, sequent RS @{thm \<phi>accept_proc_optimize_return_v})
     | _ => accept_proc' (ctxt,sequent)
  end

(*Param & Label*)
fun param_type sequent =
  PLPR_Syntax.param_type sequent
    |> map_atyps (fn ty => case ty of TVar _ => dummyT | _ => ty)
  (* TODO: how to parse (check) the term of a desired type pattern
  * (schematic type variable)? *)

fun set_param' ctxt term sequent =
    (term |> Thm.cterm_of ctxt
          |> PLPR_Syntax.intro_param)
      RS sequent

fun set_param raw_term (ctxt,sequent) =
  let
    val ctxt_parse = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
    val (\<^const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>ParamTag\<close>, _) $ goal)) = Thm.major_prem_of sequent
    val term = raw_term |> Type.constraint (param_type sequent)
                        |> Syntax.check_term ctxt_parse
                        |> Variable.expand_binds ctxt_parse
    fun has_multiple_ex_quantification X
      = case X of (Const(\<^const_name>\<open>ExSet\<close>, _) $ (Abs (_,_,(Const(\<^const_name>\<open>ExSet\<close>, _) $ _))))
                    => true
                | _ => false
    fun has_only_one_ex_quantification X =
          case X of Const(\<^const_name>\<open>ExSet\<close>, _) $ _ => not (has_multiple_ex_quantification X)
                  | _ => false
  in
    if has_only_one_ex_quantification goal
    then (* We aggregate the user input `term` into a single ex quantification with name preserved*)
      case term
        of SP as \<^Const_>\<open>Subjection \<open>ty\<close>\<close> $ _ $ _ =>
            let val sequent' = set_param' ctxt_parse
                                    (\<^Const>\<open>ExSet \<^typ>\<open>unit\<close> \<open>ty\<close>\<close> $ Abs ("", \<^typ>\<open>unit\<close>, SP)) sequent
                            |> Conv.fconv_rule (
                                  Phi_Conv.pure_imp_antecedents_conv (
                                    Conv.try_conv (Conv.rewr_conv @{thm unit_all_eq1})))
             in (ctxt, sequent') end
         | _ =>
            let
              val (N,term') = QuantExpansion.aggregate_vars_quantification ~1 term
              val sctxt = clear_simpset ctxt
                          addsimps QuantExpansion.aux_expansions ctxt
                          addsimprocs [QuantExpansion.named_forall,
                                       QuantExpansion.named_ex,
                                       QuantExpansion.named_ExSet,
                                       QuantExpansion.named_metaAll]
            in (ctxt, set_param' ctxt_parse term' sequent
                        |> QuantExpansion.named_predicate_expansion sctxt
                        |> Simplifier.full_simplify sctxt)
            end
    else (ctxt, set_param' ctxt_parse term sequent)
  end

fun set_param_cmd xterm (ctxt,sequent) =
  case try (dest_funT #> apfst Phi_Syntax.dest_namedT) (param_type sequent)
    of SOME (name_and_tys, rng) =>
        let
          val fixes = map (fn (name,ty) =>
                (Binding.name name, (if ty = dummyT then NONE else SOME ty), NoSyn)) name_and_tys
          val (fixed_names, ctxt) = Proof_Context.add_fixes fixes ctxt
          val ctxt_parse = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
          val term = Syntax.parse_term ctxt_parse xterm
                      |> Phi_Help.tuple_abs (map fst name_and_tys ~~ map (rpair dummyT) fixed_names)
                      |> Phi_Help.mk_monop @{const_name case_named}
        in
          set_param term (ctxt,sequent)
        end
     | NONE =>
        let
          val ctxt_parse = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
        in
          set_param (Syntax.parse_term ctxt_parse xterm) (ctxt,sequent)
        end

fun set_label name (ctxt,sequent) = (ctxt, Phi_Syntax.mk_label_thm name RS sequent)




fun synthesis term ctxt sequent =
  let
    val i_s = Thm.maxidx_of sequent + 1
    val i_t = Thm.maxidx_of_cterm term + 1
    val sequent' = @{thm \<phi>synthesis}
          |> Thm.incr_indexes (i_s + i_t)
          |> Drule.infer_instantiate ctxt [(("X",i_s + i_t), Thm.incr_indexes_cterm i_s term),
                                           (("sequent",i_s + i_t), Thm.cprop_of sequent)]
          |> (fn rule => Thm.implies_elim rule sequent)
    val _ = Phi_Reasoner.info_print ctxt 2 (fn _ => "reasoning synthesis..." ^ Position.here \<^here>)
  in Phi_Reasoner.reason1 (fn () =>
        error ("fail to synthesis "^Syntax.string_of_term ctxt (Thm.term_of term))
      ) NONE NONE ctxt sequent'
  end

(*the sequent must be leaded by a premises antecedent*)
fun obligation_proof print_results mode kind before_qed after_qed fixes assumes sequent0 state =
  let
    val sequent01 = Phi_Reasoners.obligation_intro_Ex_conv ~1 (Proof.context_of state) sequent0
    val (oblg,sequent) =
        let val th = @{thm Premise_I} RS sequent01
            (*handle THM _ => @{thm Simplify_I} RS sequent01*)
         in ([Phi_Help.leading_antecedent' th], th) end
        handle THM _ => ([], sequent01)
    fun after_qed' (ctxt, thmss) stat =
      let
        val ctxt' = Proof.context_of stat
        val thms = Proof_Context.export ctxt ctxt' (flat thmss)
        val sequent' = fold (fn x => fn s => x RS s) thms sequent
       in after_qed sequent' stat
      end
    val setup_environ = Phi_Envir.freeze_dynamic_lemmas
  in state
  |> Proof.map_context setup_environ
  |> Proof.internal_goal print_results mode true kind before_qed after_qed' fixes assumes
       (map (fn t => (Binding.empty_atts,[(t,[])])) oblg)
  end


end