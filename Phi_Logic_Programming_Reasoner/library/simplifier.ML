signature PLPR_SIMPLIFIER = sig

(* The simplification only uses premises tagged by \<open>Premise default\<close> or \<open>Premise MODE_SIMP\<close>,
   or any extracted premises by means of Phi_Reasoners.extract_prem *)

(* The simplifiers are not always as powerful as expected especially when it contains schematic variables.
   Specific reasoning apps may fix the variables to boost its ability. *)

type fix_variables = bool (*if to fix schematic variable so boost the simplification*)
val simplifier : (thm -> thm Seq.seq) -> (Proof.context -> Proof.context) -> fix_variables
              -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss : (thm -> thm Seq.seq) -> simpset -> fix_variables -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss' : (thm -> thm Seq.seq) -> (Proof.context -> simpset)
                     -> fix_variables -> Proof.context -> thm -> thm Seq.seq
val simplifier_only: (thm -> thm Seq.seq) -> (Proof.context -> thm list)
                  -> fix_variables -> Proof.context -> thm -> thm Seq.seq

end

structure PLPR_Simplifier : PLPR_SIMPLIFIER = struct

type fix_variables = bool

fun simplification fallback F to_fix ctxt sequent = Seq.make (fn () =>
  let val (names, sequent', ctxt') = if to_fix
             then case Variable.import true [sequent] ctxt
                    of (((tyvars, tmvars),[sequent']), ctxt') =>
                  ((Names.build (TVars.fold (fn (_, cty) => case Thm.typ_of cty
                                                              of TFree (N, _) => Names.add_set N) tyvars),
                    Names.build (Vars.fold (fn (_, ctm) => Names.add_set (Term.term_name (Thm.term_of ctm))) tmvars)),
                    sequent', ctxt')
             else ((Names.empty, Names.empty), sequent, ctxt)
   in sequent'
   |> Conv.gconv_rule (Phi_Reasoners.asm_full_rewrite true (F ctxt')) 1
   |> to_fix ? (fn th => Thm.generalize names (Thm.maxidx_of th + 1) th)
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

fun simp_premis F to_fix ctxt sequent =
  let val (sequent', ctxt') = if to_fix
             then case Variable.import false [sequent] ctxt
                    of ((_,[sequent']), ctxt') => (sequent', ctxt')
             else (sequent, ctxt)
   in (@{thm Premise_I} RS sequent')
   |> Tactical.HEADGOAL (Tactical.SOLVED' (Phi_Reasoners.asm_lr_simp_tac true (F ctxt')))
   |> Seq.map (to_fix ? singleton (Variable.export ctxt' ctxt))
  end

fun simplifier fallback F fix_variables ctxt sequent =
  case Thm.major_prem_of sequent
    of _ (*Trueprop*) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =>
            simp_premis F fix_variables ctxt sequent
     | _ (*Trueprop*) $ (Const (\<^const_name>\<open>Simplify\<close>, _) $ _ $ _ $ _) =>
            simplification fallback F fix_variables ctxt sequent
     | _ => Seq.empty


fun simplifier_only fallback thms = simplifier fallback (fn ctxt => clear_simpset ctxt addsimps (thms ctxt))
fun simplifier_by_ss  fallback ss = simplifier fallback (Raw_Simplifier.put_simpset ss)
fun simplifier_by_ss' fallback ss = simplifier fallback (fn ctxt => Raw_Simplifier.put_simpset (ss ctxt) ctxt)

end