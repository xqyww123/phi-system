(* FILE: library/system/sys.ML
   AUTHOR: Qiyuan Xu

   Several core operations in IDE-CP.
*)

signature PHI_SYS = sig
  (** Basic Operations **)
  val cast : cterm -> Proof.context * thm -> Proof.context * thm
  val cast_exception : cterm -> Proof.context * thm -> Proof.context * thm
  val move_lemmata : context_state -> context_state
  val apply_automatic_morphism : context_state -> context_state

  val accept_proc : context_state -> context_state

  val set_param : term -> context_state -> context_state
  val set_param_cmd : string -> context_state -> context_state
  val set_label : string -> context_state -> context_state

  val synthesis : cterm -> context_state -> context_state

  val obligation_proof :  (Proof.context -> (string * string) * (string * thm list) list -> unit)
        -> Proof_Context.mode -> string -> Method.text option
        -> (thm -> Proof.state -> Proof.state)
        -> (binding * typ option * mixfix) list
        -> (Thm.binding * (term * term list) list) list
        -> thm -> Proof.state -> thm list * Proof.state
end

structure Phi_Sys : PHI_SYS = struct
open Thm Phi_Envir Term

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg'' th = Seq.make (fn () => (@{print} th; raise NDBG th))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty))) *)

(** Automatic Transformation **)

structure Automatic_Transformation = Proof_Data (
  type T = thm list
  val init = K []
);

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>morphism\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => Automatic_Transformation.get ctxt))

(** Basic Operations **)

val cast = Phi_Working_Mode.cast
val cast_exception = Phi_Working_Mode.cast_exception

fun apply_automatic_morphism' _ [] _ = raise Empty
  | apply_automatic_morphism' R (M::L) stat =
      case Thm.concl_of M
        of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Automatic_Transformation\<close>, _) $ \<^const>\<open>MODE_AUTO\<close> $ _ $ _)
             => (rev R @ L, NuApply.apply [M] stat)
         | _ =>apply_automatic_morphism' (M::R) L stat

fun apply_automatic_morphism (ctxt,sequent) =
  case apply_automatic_morphism' [] (Automatic_Transformation.get ctxt) (ctxt,sequent)
    of (R, stat') => apfst (Automatic_Transformation.put R) stat'

fun simplify_morphisms _   [] = []
  | simplify_morphisms ctxt L =
      map (Raw_Simplifier.rewrite_rule ctxt @{thms FOCUS_TAG_def[folded atomize_eq]}) L

fun move_lemmata' (ctxt, sequent) =
  let
    fun filter_lemma th =
      case Thm.prop_of th
        of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>USELESS\<close> $ _) => NONE
         | \<^const>\<open>Trueprop\<close> $ \<^const>\<open>True\<close> => NONE
         | _ => SOME th
    fun is_morphism th =
      case Thm.concl_of th
        of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Automatic_Transformation\<close>, _) $ _ $ _ $ _) => true
         | _ => false
    val all_lemmas = (sequent RS @{thm conjunct2})
                  |> HOLogic.conj_elims ctxt
                  |> map_filter filter_lemma
    val lemmas = all_lemmas |> filter (not o is_morphism)
    val morphisms = all_lemmas |> filter is_morphism |> simplify_morphisms ctxt
    val ctxt' =
      if null lemmas
      then ctxt
      else Context.proof_map (fold (fold (fn th =>
               Named_Theorems.add_thm \<^named_theorems>\<open>\<phi>lemmata\<close> th
            #> Useful_Thms.add_thm th
           ) o Phi_Envir.process_useful_lemmata true ctxt
           ) lemmas) ctxt
    val ctxt'' =
      if null morphisms
      then ctxt'
      else Automatic_Transformation.map (fn L => morphisms@L) ctxt'
  in
    (ctxt'', sequent RS @{thm conjunct1})
  end

fun move_lemmata (ctxt, sequent) =
  case Thm.prop_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>conj\<close> $ _ $ _) => move_lemmata (move_lemmata' (ctxt, sequent))
     | _ => (ctxt, sequent)

val conv_E_thms =
  @{thms add_0_right[where 'a=\<open>'a::sep_magma set\<close>, folded atomize_eq]
         add_0_right[where 'a=\<open>'b \<Rightarrow> 'a::sep_magma set\<close>, folded atomize_eq]
         add_0_left[where 'a=\<open>'a::sep_magma set\<close>, folded atomize_eq]
         add_0_left[where 'a=\<open>'b \<Rightarrow> 'a::sep_magma set\<close>, folded atomize_eq]
         zero_fun[where 'a=\<open>'a::sep_magma set\<close>, folded atomize_eq]
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
                             val ex_rule = @{thm \<phi>ex_quantify_E}
                                        |> Drule.infer_instantiate ctxt [(("E",0),E')]
                          in sequent0 RS ex_rule end
                    else sequent0
   in
     sequent |> Thm.implies_intr assm
             |> Drule.forall_intr_list [param_s, param_ret]
             |> (fn th => (th COMP_INCR rule)
                       |> Conv.fconv_rule (Phi_Syntax.pending_construction_abnm_conv
                             (Conv.repeat_conv (Conv.rewrs_conv conv_E_thms))))
  end


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
                                          \ Regard it to no return."
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

    val (ret_name, ctxt'1) = Generic_Variable_Access.assign_anony_local_val (SOME ret_ty) ctxt
    val ([s_name], ctxt') = Proof_Context.add_fixes [(Binding.name "\<s>", NONE, NoSyn)] ctxt'1
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
  Phi_Syntax.param_type sequent
    |> map_atyps (fn ty => case ty of TVar _ => dummyT | _ => ty)
  (* TODO: how to parse (check) the term of a desired type pattern
  * (schematic type variable)? *)

fun set_param' ctxt term sequent =
    (term |> Thm.cterm_of ctxt
          |> Phi_Syntax.intro_param)
      RS sequent

fun set_param raw_term (ctxt,sequent) =
  let
    val ctxt_parse = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
    val (\<^const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>ParamTag\<close>, _) $ X)) = Thm.major_prem_of sequent
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
    if has_only_one_ex_quantification X
    then (* We aggregate the user input `term` into a single ex quantification with name preserved*)
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




fun synthesis term (ctxt, sequent) =
  let
    val i_s = Thm.maxidx_of sequent + 1
    val i_t = Thm.maxidx_of_cterm term + 1
    val sequent' = @{thm \<phi>synthesis}
          |> Thm.incr_indexes (i_s + i_t)
          |> Drule.infer_instantiate ctxt [(("X",i_s + i_t), Thm.incr_indexes_cterm i_s term),
                                           (("sequent",i_s + i_t), Thm.cprop_of sequent)]
          |> (fn rule => Thm.implies_elim rule sequent)
    val _ = Phi_Reasoner.info_print ctxt 2 (fn _ => "reasoning synthesis..." ^ Position.here \<^here>)
  in
    case Phi_Reasoner.reason NONE (ctxt, sequent')
      of SOME ret => ret
       | NONE => error ("fail to synthesis "^Syntax.string_of_term ctxt (Thm.term_of term))
  end


fun obligation_proof print_results mode kind before_qed after_qed fixes assumes sequent0 =
  let
    val (oblg,sequent) =
        let val th = @{thm Premise_I} RS sequent0
            handle THM _ => @{thm Simplify_I} RS sequent0
         in ([Phi_Help.leading_antecedent' th], th) end
        handle THM _ => ([], sequent0)
    fun after_qed' (ctxt, thmss) stat =
      let
        val ctxt' = Proof.context_of stat
        val thms = Proof_Context.export ctxt ctxt' (flat thmss)
        val sequent' = fold (fn x => fn s => x RS s) thms sequent
       in after_qed sequent' stat
      end
    val setup_environ = Phi_Envir.freeze_dynamic_lemmas
  in
    Proof.map_context setup_environ
  #>Proof.internal_goal print_results mode true kind before_qed after_qed' fixes assumes
       (map (fn t => (Binding.empty_atts,[(t,[])])) oblg)
  end


end