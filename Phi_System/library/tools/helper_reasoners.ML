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
        (thm (*normal rule*) * thm (*with R*)) *
        (thm (*quick rule*) * thm (*with R*)) *
        ( string (*head of the conditional branch, e.g., If*) *
          int (*arity of the head, e.g., 3*) *
          thm list (*rewrite rules to move the conditional branch to the top*)) *
        (Proof.context
            -> (indexname * typ) list (*vars in Y*) * cterm (*LHS, the Y*) * cterm (*RHS, the If C Y\<^sub>a Y\<^sub>B*)
            -> cterm Vars.table (*instantiations*))
     -> Proof.context * thm -> (Proof.context * thm) Seq.seq

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

fun reasoner_ToA_conditioned_subgoals ((rule, ruleR),
                                       (quick_rule, quick_ruleR),
                                       (head_const, arity, rewrs),
                                       mk_insts)
                                      (ctxt,sequent) =
  Seq.make (fn () =>
  let fun has_var tm = maxidx_of_term tm >= 0
      val (no_var, has_remainder) =
        case #2 (Phi_Syntax.dest_transformation (Thm.major_prem_of sequent))
          of Const(\<^const_name>\<open>times\<close>, _) $ Y $ (Const(\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _)
               => (has_var Y, true)
           | Y => (has_var Y, false)
      val rule' = if no_var
                  then if has_remainder then quick_ruleR else quick_rule
                  else if has_remainder then ruleR else rule
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

      val (Y,RHS) = (*Thm.generalize_cterm (Names.empty, qvar_names) (idx+1)*) equation0
                 |> Phi_Help.dest_binop_c \<^const_name>\<open>Pure.eq\<close>
      val vars = Term.add_vars (Thm.term_of Y) []
      val inst = mk_insts ctxt'N (vars,Y,RHS)
      val move_to_top = Conv.bottom_conv (fn _ => fn ctm =>
            case Term.strip_comb (Thm.term_of ctm)
              of (Const (N, _), args) =>
                    if N = head_const andalso length args = arity
                    then (Phi_Help.beta_eta_conversion then_conv
                         (fn ctm =>
                            case get_first (fn rule => try (Conv.rewr_conv rule) ctm) rewrs
                              of SOME ret => ret
                              | NONE => Conv.all_conv ctm)) ctm
                    else Conv.all_conv ctm
               | _ => Conv.all_conv ctm) ctxt'N
      val sequent'' = Thm.instantiate (TVars.empty, inst) sequent'
               |> Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn _ =>
                      Conv.arg_conv move_to_top then_conv
                      Conv.arg1_conv move_to_top) ctxt) 1
               |> (fn th => @{thm' Pure.reflexive} RS th
                            handle THM _ => error "BUG: fail to solve the equation")
   in SOME ((ctxt, sequent''), Seq.empty)
  end
  end)

end

