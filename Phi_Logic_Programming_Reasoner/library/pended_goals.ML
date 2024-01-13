signature PHI_REASONERS = sig
include PHI_REASONERS

val gen_defer_antecedent :
        (term (*leading antecedent*) -> term list (*premises*) -> int (*index in the premises*))
      -> tactic
val defer_antecedent: thm -> thm Seq.seq
val defer_param_antecedent: thm -> thm Seq.seq

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

fun find_obligation flag i (( _ $ (@{term Proof_Obligation} $ _ ))::L) =
      if flag then i else find_obligation true (i+1) L
  | find_obligation flag i (X::L) =
      find_obligation (flag orelse not (PLPR_Syntax.is_deferable X)) (i+1) L
  | find_obligation _ _ [] = ~1

fun gen_defer_antecedent find_idx thm =
  case Thm.prems_of thm
    of (H::L) =>
      let val idx = find_idx H L
      in
        if idx = ~1
        then error ("Fail to defer a proof obligation: an \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> antecedent is not found.")
        else Thm.permute_prems 1 idx thm
          |> Thm.permute_prems 0 (~idx)
          |> Seq.single
      end
     | [] => Seq.single thm

val defer_antecedent = gen_defer_antecedent (fn _ => fn L => find_obligation false 0 L)

val err_msg = "Bad configuration of reasoning rules!\n\
            \Some antecedents are bound on undetermined variables to be given by users in future, \
            \which can only be used in \<d>\<o>, \<p>\<a>\<r>\<a>\<m>, \<u>\<s>\<e>\<r> and \<p>\<r>\<e>\<m>\<i>\<s>\<e>.\n\
            \Check any variables assigned by \<p>\<a>\<r>\<a>\<m> antecedent are only used in \
            \\<d>\<o>, \<p>\<a>\<r>\<a>\<m>, \<u>\<s>\<e>\<r> and \<p>\<r>\<e>\<m>\<i>\<s>\<e>."

fun chk_param X L idx =
  let
    val vars = Term.add_vars  X [] |> Vartab.make
    val tvars= Term.add_tvars X [] |> Vartab.make
    fun T_has_bad (TVar (N, _)) = Vartab.defined tvars N
      | T_has_bad (Type (_, L)) = exists T_has_bad L
      | T_has_bad _ = false
    fun has_bad (Const (_,T)) = T_has_bad T
      | has_bad (Free (_, T)) = T_has_bad T
      | has_bad (Var (N,T)) = Vartab.defined vars N orelse T_has_bad T
      | has_bad (Bound _) = false
      | has_bad (Abs (_,T,X)) = T_has_bad T orelse has_bad X
      | has_bad (X $ Y) = has_bad X orelse has_bad Y
    fun chk _ [] = ()
      | chk i (X::L) =
        if i <= 0 then ()
        else if not (PLPR_Syntax.is_deferable X) andalso has_bad X
        then Phi_Reasoner.error err_msg
        else chk (i-1) L
  in (chk idx L; idx)
  end

val defer_param_antecedent = gen_defer_antecedent (fn X => fn L =>
      chk_param X L (find_obligation false 0 L))


end
