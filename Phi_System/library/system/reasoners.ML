signature PHI_SYS_REASONERS = sig

val gen_defer_antecedent :
        (term (*leading antecedent*) -> term list (*premises*) -> int (*index in the premises*))
      -> tactic
val defer_antecedent: thm -> thm Seq.seq
val defer_param_antecedent: thm -> thm Seq.seq

val is_user_dependent_antecedent : term -> bool
val is_proof_obligation : term -> bool

end

structure Phi_Sys_Reasoner : PHI_SYS_REASONERS = struct

fun is_deferable (\<^const>\<open>Trueprop\<close> $ X) = is_deferable X
  | is_deferable (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_,_,X)) = is_deferable X
  | is_deferable (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_deferable X
  | is_deferable (Const (\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = is_deferable X
  | is_deferable (Const (\<^const_name>\<open>ParamTag\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Argument\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Do\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Premise\<close>, _) $ _) = true
  | is_deferable _ = false

fun find_obligation flag i (( _ $ (@{term Proof_Obligation} $ _ ))::L) =
      if flag then i else find_obligation true (i+1) L
  | find_obligation flag i (X::L) =
      find_obligation (flag orelse not (is_deferable X)) (i+1) L
  | find_obligation _ _ [] = ~1

val err_msg = "Bad configuration of reasoning rules!\n\
            \Some antecedents are bound on undetermined variables to be given by users in future, \
            \which can only be used in \<^bold>d\<^bold>o, \<p>\<a>\<r>\<a>\<m>, \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t and \<p>\<r>\<e>\<m>\<i>\<s>\<e>.\n\
            \Check any variables assigned by \<p>\<a>\<r>\<a>\<m> antecedent are only used in \
            \\<^bold>d\<^bold>o, \<p>\<a>\<r>\<a>\<m>, \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t and \<p>\<r>\<e>\<m>\<i>\<s>\<e>."

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
        else if not (is_deferable X) andalso has_bad X
        then Phi_Reasoner.error err_msg
        else chk (i-1) L
  in (chk idx L; idx)
  end

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

val defer_param_antecedent = gen_defer_antecedent (fn X => fn L =>
      chk_param X L (find_obligation false 0 L))

fun is_user_dependent_antecedent (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Argument\<close>, _) $ _ ) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Do\<close>, _) $ _ ) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>ParamTag\<close>, _) $ _ ) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _) = true
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (\<^Const>\<open>Pure.all ty\<close> $ X) =
      is_user_dependent_antecedent (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, _, X)) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (\<^Const>\<open>HOL.All ty\<close> $ X) =
      is_user_dependent_antecedent (\<^Const>\<open>HOL.All ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Labelled\<close>, _) $ _ $ X) = is_user_dependent_antecedent X
  | is_user_dependent_antecedent (Const(\<^const_name>\<open>Technical\<close>, _) $ X) = is_user_dependent_antecedent X
(*  | is_user_dependent_antecedent (Const(\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ Abs (_, _, X)) = is_user_dependent_antecedent X *)
  | is_user_dependent_antecedent _ = false

fun is_proof_obligation (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_proof_obligation X
  | is_proof_obligation (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>default\<close>, _) $ _) = true
  | is_proof_obligation (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _) = true
  | is_proof_obligation _ = false

end


