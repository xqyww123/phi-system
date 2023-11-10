signature BI_QUANTIFIERS = sig
val defined_Ex : Proof.context -> cterm -> thm option
end

structure BI_Quantifiers : BI_QUANTIFIERS = struct

fun quick_check quantifier =
  let fun qchkB lv (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound i $ _) = i = lv
        | qchkB lv (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ Bound i) = i = lv
        | qchkB lv (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) = qchkB lv A orelse qchkB lv B
        | qchkB _ _ = false

      fun qchk lv (Const(N, _) $ Abs (_, _, X)) =
            if quantifier = N then qchk (lv+1) X else false
        | qchk lv (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ P) =
            qchkB lv P andalso
            Phi_Syntax.forall_item_of_assertion (
                fn (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) => not (Term.loose_bvar1 (T, lv))
                 | X => not (Term.loose_bvar1 (X, lv))
              ) X
        | qchk _ _ = false

   in qchk ~1
  end

fun sink_quantifier rewr C =
  let fun conv ctxt =
        Conv.rewr_conv rewr then_conv Conv.arg_conv (Phi_Conv.abs_conv_eta (conv o snd) ctxt)
        else_conv C ctxt
   in conv
  end

fun move_conj qvar =
  let fun pop_left ctm =
        case Thm.term_of ctm
          of Const _ (*conj*) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) $ _   => Conv.all_conv ctm
           | Const _ (*conj*) $ (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) $ _ => Conv.rewr_conv @{thm' conj_assoc[folded atomize_eq]} ctm
           | _ => error "BI.defined_Ex"

      fun pop_right ctm =
        case Thm.term_of ctm
          of Const _ (*conj*) $ _ $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _)   => Conv.rewr_conv @{thm' conj_commute[folded atomize_eq]} ctm
           | Const _ (*conj*) $ _ $ (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) => Conv.rewr_conv @{thm' conj_left_commute[folded atomize_eq]} ctm
           | _ => error "BI.defined_Ex"

      fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Free x $ _ =>
              if x = qvar then SOME (Conv.all_conv ctm)
                          else NONE
           | Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ Free x =>
              if x = qvar then SOME (Conv.rewr_conv @{thm' eq_commute[folded atomize_eq]} ctm)
                          else NONE
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
             (case (conv (Thm.dest_arg1 ctm), conv (Thm.dest_arg ctm))
                of (SOME rewr, _) => SOME ((Conv.arg1_conv (K rewr) then_conv pop_left) ctm)
                 | (_, SOME rewr) => SOME ((Conv.arg_conv (K rewr) then_conv pop_right) ctm)
                 | _ => NONE)
           | _ => NONE
   in conv
  end

fun defined_Ex_direct ctm =
  case Thm.term_of ctm
    of Const _ (*Ex*) $ Abs (_, _, Const _ (*Subj*) $ _ $ X) =>
        (case X
           of Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _ =>
                Conv.rewr_conv @{thm' ExSet_simps_ex(1)[folded atomize_eq]} ctm
            | Const (\<^const_name>\<open>HOL.conj\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) $ _ =>
                Conv.rewr_conv @{thm' ExSet_simps_ex(3)[folded atomize_eq]} ctm
            | _ => error "BI.defined_Ex")
     | _ => error "BI.defined_Ex"

fun defined_Ex ctxt ctm =
  if quick_check \<^const_name>\<open>ExSet\<close> (Thm.term_of ctm)
  then SOME (sink_quantifier @{thm' BI_Ex_comm[folded atomize_eq]} (fn ctxt =>
          Conv.arg_conv (Phi_Conv.abs_conv_eta (fn (qvar, _) =>
              Conv.arg_conv (the o move_conj (dest_Free (Thm.term_of qvar)))
            ) ctxt) then_conv
          defined_Ex_direct)
          ctxt ctm)
  else NONE

end


(*
structure BI_Quantifiers = Quantifier1 (

  fun dest_eq (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(\<^const_name>\<open>HOL.conj\<close>,_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(\<^const_name>\<open>HOL.implies\<close>,_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp

  val iff_reflection = @{thm' eq_reflection}
  val ex_iffI = @{lemma' \<open>(P \<Longrightarrow> Q) \<Longrightarrow> (Q \<Longrightarrow> P) \<Longrightarrow> (A \<s>\<u>\<b>\<j> P) = (A \<s>\<u>\<b>\<j> Q)\<close>
                     by (simp add: BI_eq_iff, blast)}
  val iff_trans = @{thm' trans}
  val conjI= @{thm' conjI}
  val conjE= @{thm' conjE}
  val impI = @{thm' impI}
  val mp   = @{thm' mp}
  val uncurry = @{thm' uncurry}
  val ex_comm = @{thm' BI_Ex_comm}
  val all_comm = @{thm' BI_All_comm}
  val iff_exI = @{thm' BI_iff_exI}
  val iff_allI = @{thm' BI_iff_allI}
  val exE = @{thm' BI_exE}

  val atomize =
    let val rules = @{thms atomize_all atomize_imp atomize_eq atomize_conj}
    in fn ctxt => Raw_Simplifier.rewrite ctxt true rules end
)

(*


signature BI_QUANTIFIER1 = sig
include QUANTIFIER1

val nominal : ctyp -> cterm
val nominal_sat : ctyp -> cterm

end

structure BI_Quantifiers : BI_QUANTIFIER1 = struct

val nominal0_idx = (("'c",0),\<^sort>\<open>type\<close>)
val nominal0_ty = \<^Type>\<open>set \<open>TVar nominal0_idx\<close>\<close>
val nominal0_tm = Free("_\<c>_", nominal0_ty)
val nominal0_sat_tm = \<^Const>\<open>Satisfaction nominal0_ty\<close> $ nominal0_tm
val nominal0_cty = Thm.trim_context_cty (Thm.ctyp_of \<^context> nominal0_ty)
val nominal0 = Thm.trim_context_cterm (Thm.cterm_of \<^context> nominal0_tm)
val nominal0_sat = Thm.trim_context_cterm (Thm.cterm_of \<^context> nominal0_sat_tm)

fun nominal cty = Thm.instantiate_cterm (TVars.make [(nominal0_idx, cty)], Vars.empty) nominal0
fun nominal_sat cty = Thm.instantiate_cterm (TVars.make [(nominal0_idx, cty)], Vars.empty) nominal0_sat
  

structure Q1 = Quantifier1 (

  fun dest_eq (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(\<^const_name>\<open>HOL.conj\<close>,_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(\<^const_name>\<open>HOL.implies\<close>,_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp

  val iff_reflection = @{thm' eq_reflection}
  val iffI = @{thm' iffI}
  val iff_trans = @{thm' trans}
  val conjI= @{thm' conjI}
  val conjE= @{thm' conjE}
  val impI = @{thm' impI}
  val mp   = @{thm' mp}
  val uncurry = @{thm' uncurry}

  val exI = @{lemma' \<open>nominal0 \<Turnstile> S x \<Longrightarrow> nominal0 \<Turnstile> (ExSet S)\<close>
                  by (simp, blast)}
)

open Q1

end
*)
*)