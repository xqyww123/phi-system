signature PHI_SYS_REASONERS = sig

val defer_antecedent: thm -> thm Seq.seq
val defer_param_antecedent: thm -> thm Seq.seq

end

structure Phi_Sys_Reasoner : PHI_SYS_REASONERS = struct

fun is_deferable (\<^const>\<open>Trueprop\<close> $ X) = is_deferable X
  | is_deferable (Const (\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = is_deferable X
  | is_deferable (Const (\<^const_name>\<open>ParamTag\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Argument\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Do\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Premise\<close>, _) $ _) = true
  | is_deferable _ = false

fun find_obligation flag i (( _ $ (@{term Proof_Obligation} $ _ ))::L) =
      if flag then i else find_obligation true (i+1) L
  | find_obligation flag i (X::L) =
      find_obligation (flag orelse is_deferable X) (i+1) L
  | find_obligation _ _ [] = ~1

fun gen_defer_antecedent chk thm =
  let
    val idx = tl (Thm.prems_of thm) |> find_obligation false 0
    val _ = chk idx (Thm.prems_of thm)
  in
    if idx = ~1
    then error ("Fail to defer a proof obligation: an \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n antecedent is not found.")
    else Thm.permute_prems 1 idx thm
      |> Thm.permute_prems 0 (~idx)
      |> Seq.single
  end

val defer_antecedent = gen_defer_antecedent (K I)

val err_msg = "Bad configuration of reasoning rules!\n\
            \Some antecedents are bound on undetermined variables to be given by users in future, \
            \which can only be used in \<^bold>d\<^bold>o, \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m, \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t and \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e.\n\
            \Check any variables assigned by \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m antecedent are only used in \
            \\<^bold>d\<^bold>o, \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m, \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t and \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e."

fun chk_param idx (X::L) =
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
  in chk idx L
  end

val defer_param_antecedent = gen_defer_antecedent chk_param

end