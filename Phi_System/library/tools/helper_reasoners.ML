signature PHI_REASONERS = sig
include PHI_REASONERS

(*For a ToA like \<open>if C then A else B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close> that will be split to two subgoals and in which
  the schematic variables in the target \<open>Y\<close> may be instantiated to different values,
  reasoner_ToA_conditioned_subgoals merges the instantiations between the two subgoals.
  For example, if the two branches returns \<open>Y[x/a]\<close> and \<open>Y[x/b]\<close> respectively for different two
  instantiations \<open>a\<close> and \<open>b\<close>, reasoner_ToA_conditioned_subgoals returns \<open>Y[x/(if C then a else b)]\<close>
  for each schematic variable.

  See \<open>case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close> as an example.

  The normal rule must of form, for example:
    \<open>     Y \<equiv> If C Y\<^sub>a Y\<^sub>B
      \<Longrightarrow> \<cdots> such as X\<^sub>a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<^sub>a
      \<Longrightarrow> If C X\<^sub>a X\<^sub>b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<close>
  with R:
    \<open>     Y \<equiv> If C Y\<^sub>a Y\<^sub>B
      \<Longrightarrow> \<cdots> such as X\<^sub>a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<^sub>a
      \<Longrightarrow> If C X\<^sub>a X\<^sub>b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<close>
  quick rule is the quick-cut used when the Y contains no schematic variables.
  *)
val reasoner_ToA_conditioned_subgoals :
          thm (*rule having no Remainder*) * thm (*with conditioned Remainder*) (** thm (*necessarily with remainder*)*) *
        ( bool (*if to split the source or to split the target*) *
          thm list (*rewrites degenerating the branch*) * 
          thm list (*reductions*)) *
        (Proof.context
            -> (indexname * typ) list (*vars in Y*) * cterm (*LHS, the Y*) * cterm (*RHS, the If C Y\<^sub>a Y\<^sub>B*)
            -> (cterm Vars.table (*instantiations*) * term(*the condition term*))) *
        Proof.context (*context for preparation time*)
     -> Proof.context * thm -> (Proof.context * thm) Seq.seq

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

fun reasoner_ToA_conditioned_subgoals (rule, ruleR, (*ruleRT,*) (split_source, degenerates, reds),
                                       mk_insts, ctxt_gen) =
  let datatype has_remainder = No_Rem | Has_Rem (*| True_Rem*)
      fun has_no_var tm = maxidx_of_term tm = ~1
      fun strip (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = strip X
        | strip (Const(\<^const_name>\<open>Orelse_shortcut\<close>, _) $ _ $ X) = strip X
        | strip X = X
      fun dest_Tr tm =
        case (if split_source then #2 else #1)
             (Phi_Syntax.dest_transformation (strip (Logic.strip_assums_concl tm)))
          of Const(\<^const_name>\<open>REMAINS\<close>, _) $ Y $ \<^Const>\<open>True\<close> $ _
               => error "True_Rem" (*(Y, \<^Const>\<open>True\<close>, True_Rem)*)
           | Const(\<^const_name>\<open>REMAINS\<close>, _) $ Y $ C $ _
               => (Y, C, Has_Rem)
           | Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const(\<^const_name>\<open>Cond_\<phi>Prod\<close>, _) $ _ $ _ $ _)
               => error "BAD CONFIGURATION"
           | Y => (Y, Term.dummy, No_Rem)

      fun mk_inst base abst (X $ _) = mk_inst base (abst+1) X
        | mk_inst base abst (Var (N,ty)) =
            let val args = (take abst (binder_types ty))
             in fold_rev (fn Ty => fn Y => Abs ("_", Ty, Y)) args base
             |> Thm.cterm_of ctxt_gen
             |> pair ((N,ty))
            end

      fun mk_quick_rule rule =
        let val Y = #1 (dest_Tr (Thm.concl_of rule))
            val Ys = map_filter (try (mk_inst Y 0 o #1 o dest_Tr)) (Thm.prems_of rule)
         in Thm.instantiate (TVars.empty, Vars.make Ys) rule
         |> Simplifier.rewrite_rule ctxt_gen degenerates
         |> (fn th => @{thm' HOL.refl} RS' (ctxt_gen, th))
         |> Thm.trim_context
        end

      val (quick_rule, quick_ruleR(*, quick_ruleRT*)) =
          (mk_quick_rule rule, mk_quick_rule ruleR(*, mk_quick_rule ruleRT*))

   in fn (ctxt,sequent) => Seq.make (fn () =>
  let val (Y, _, has_rem) = dest_Tr (Thm.major_prem_of sequent)
      val no_var = false (*has_no_var Y*) (*BUG: this short cut has problem, so disabled, may re-enable it after fixing*)
      val rule' = if no_var
                  then case has_rem of No_Rem => quick_rule | Has_Rem => quick_ruleR (*| True_Rem => quick_ruleRT*)
                  else case has_rem of No_Rem => rule | Has_Rem => ruleR (*| True_Rem => ruleRT*)
      val sequent' = rule' RS' (ctxt, sequent)
   in if no_var
   then SOME ((ctxt, sequent'), Seq.empty)
   else let
      (*val Y0 = case Thm.major_prem_of sequent'
                 of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ Y $ _ => Y
                  | _ => error "BUG: reasoner_ToA_conditioned_subgoals: bad rule"*)

      val (_, _, equation0, ctxt'N) =
              Phi_Help.strip_meta_hhf_c (fst (Thm.dest_implies (Thm.cprop_of sequent'))) ctxt
      (*val qvar_names = Names.build (fold (Names.add_set o Term.term_name o Thm.term_of) qvars)
      val idx = Thm.maxidx_of sequent' *)

      val (Y,RHS) = equation0
                 |> Phi_Help.dest_Trueprop_c
                 |> Phi_Help.dest_binop_c \<^const_name>\<open>HOL.eq\<close>
      val vars = Term.add_vars (Thm.term_of Y) []
            (*TODO: existing `mk_insts` have to be improved.
                    diverge the schematic variables in object side only and keeps variables in
                    types unchanged. May provide a generic implementation.*)
      val (inst, condition_term) = mk_insts ctxt'N (vars,Y,RHS)
    
      val sequent'' = Thm.instantiate (TVars.empty, inst) sequent'
               |> Tactic.rule_by_tactic ctxt ( SOLVED' (
                    Induct.cases_tac ctxt true [[SOME condition_term]] NONE [] THEN_ALL_NEW
                    Simplifier.asm_simp_tac (Simplifier.clear_simpset ctxt addsimps (@{thm' HOL.refl} :: reds))
                  ) 1)
   in SOME ((ctxt, sequent''), Seq.empty)
  end
  end)
  end

end

