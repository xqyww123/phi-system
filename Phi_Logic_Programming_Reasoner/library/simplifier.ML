signature PLPR_SIMPLIFIER = sig

(* The simplification only uses premises tagged by \<open>Premise default\<close> or \<open>Premise MODE_GUARD\<close>,
   or any extracted premises by means of Phi_Reasoners.extract_prem *)

(* The simplifiers are not always as powerful as expected especially when it contains schematic variables.
   Specific reasoning apps may fix the variables to boost its ability. *)

val simplifier : (thm -> thm Seq.seq) -> (Proof.context -> Proof.context)
              -> {fix_vars: bool} (*if to fix schematic variable so boost the simplification*)
              -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss : (thm -> thm Seq.seq) -> simpset -> {fix_vars: bool} -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss' : (thm -> thm Seq.seq) -> (Proof.context -> simpset)
                     -> {fix_vars: bool} -> Proof.context -> thm -> thm Seq.seq
val simplifier_only: (thm -> thm Seq.seq) -> (Proof.context -> thm list)
                  -> {fix_vars: bool} -> Proof.context -> thm -> thm Seq.seq

val conjs_to_aseq : conv
val aseq_to_conjs : conv

(*For leading antecedents which are a sequence of conjunctions (either \<open>\<and>\<close> or \<open>\<and>\<^sub>\<r>\<close>),
  all simplifiers above simplify each conjugated item using other items.

  For now we only support simplification in order where an item only uses items in its left side
  but those on the right side are not used. This is a planed feature, a mutual simplification
  over conjunctions*)

end

structure PLPR_Simplifier : PLPR_SIMPLIFIER = struct

type fix_variables = bool

fun conjs_to_aseq ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
         Conv.combination_conv
            (Conv.combination_conv (Conv.rewr_conv @{thm' Ant_Seq_def[symmetric]}) conjs_to_aseq)
            conjs_to_aseq ctm
     | _ => Conv.all_conv ctm

fun aseq_to_conjs ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _ =>
         Conv.combination_conv
            (Conv.combination_conv (Conv.rewr_conv @{thm' Ant_Seq_def}) aseq_to_conjs)
            aseq_to_conjs ctm
     | _ => Conv.all_conv ctm

fun simplification {simp_conj_items, fix_vars} fallback F ctxt sequent = Seq.make (fn () =>
  let val ((inst, [sequent']), ctxt') = if fix_vars
             then Variable.import true [sequent] ctxt
             else (((TVars.empty, Vars.empty), [sequent]), ctxt)

      val has_bare_conj = case Thm.major_prem_of sequent'
                            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Simplify\<close>, _) $ _ $ _ $ X) =>
                                (case X of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ => true
                                         | _ => false)
                             | _ => raise THM ("simplification", 1, [sequent])

   in sequent'
   |> (has_bare_conj andalso simp_conj_items) ? Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
        HOLogic.Trueprop_conv (Conv.arg_conv conjs_to_aseq)
      ) ctxt) 1
   |> Conv.gconv_rule (Phi_Reasoners.asm_lr_rewrite true (F ctxt')) 1
   |> fix_vars ? (fn th => Thm.generalize (Variable.export_generalization' inst) (Thm.maxidx_of th + 1) th)
   |> (has_bare_conj andalso simp_conj_items) ? Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
        HOLogic.Trueprop_conv (Conv.arg_conv aseq_to_conjs)
      ) ctxt) 1
   |> (fn th => case Phi_Reasoner.single_RS' @{thm End_Simplification} ctxt th
                  of SOME ret => SOME (ret, Seq.empty)
                   | NONE => Seq.pull (fallback th))
  end
)
(*    |> Tactical.HEADGOAL (Phi_Reasoners.simp_tac (F ctxt))
    |> Seq.map_filter (fn th =>
          (*case*) Phi_Reasoner.single_RS' @{thm End_Simplification} ctxt th
          (*of NONE => Phi_Reasoner.single_RS' @{thm End_Simplification'} ctxt th
             | some => some*))*)

fun simp_premis F fix_vars ctxt sequent =
  let val (sequent', ctxt') = if fix_vars
             then case Variable.import false [sequent] ctxt
                    of ((_,[sequent']), ctxt') => (sequent', ctxt')
             else (sequent, ctxt)
   in (@{thm Premise_I} RS sequent')
   |> Tactical.HEADGOAL (Tactical.SOLVED' (Phi_Reasoners.asm_lr_simp_tac true (F ctxt')))
   |> Seq.map (fix_vars ? singleton (Variable.export ctxt' ctxt))
  end

fun simplifier fallback F {fix_vars} ctxt sequent =
  case Thm.major_prem_of sequent
    of _ (*Trueprop*) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =>
            simp_premis F fix_vars ctxt sequent
     | _ (*Trueprop*) $ (Const (\<^const_name>\<open>Simplify\<close>, _) $ _ $ _ $ _) =>
            simplification {simp_conj_items=true, fix_vars=fix_vars} fallback F ctxt sequent
     | _ => Seq.empty


fun simplifier_only fallback thms = simplifier fallback (fn ctxt => clear_simpset ctxt addsimps (thms ctxt))
fun simplifier_by_ss  fallback ss = simplifier fallback (Raw_Simplifier.put_simpset ss)
fun simplifier_by_ss' fallback ss = simplifier fallback (fn ctxt => Raw_Simplifier.put_simpset (ss ctxt) ctxt)


end