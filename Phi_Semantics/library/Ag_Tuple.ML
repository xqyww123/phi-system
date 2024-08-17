local

val is_poison_0 = @{lemma
  \<open> sem_tup_T (\<p>\<o>\<i>\<s>\<o>\<n> # Ts) \<equiv> \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by (smt (verit, ccfv_SIG) list.set_intros(1) semty_tup_eq_poison) }

val is_poison_N = @{lemma
  \<open> sem_tup_T Ts \<equiv> \<p>\<o>\<i>\<s>\<o>\<n>
\<Longrightarrow> sem_tup_T (T # Ts) \<equiv> \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by (smt (verit, best) list.set_intros(2) semty_tup_eq_poison) }

fun has_poison (Const(\<^const_name>\<open>Nil\<close>, _)) = SOME false
  | has_poison (Const(\<^const_name>\<open>Cons\<close>, _) $ Const(\<^const_name>\<open>\<p>\<o>\<i>\<s>\<o>\<n>\<close>, _) $ _) = SOME true
  | has_poison (Const(\<^const_name>\<open>Cons\<close>, _) $ _ $ X) = has_poison X
  | has_poison _ = NONE

in

val setup_semty_tup_to_poison =
  Simplifier.define_simproc \<^binding>\<open>semty_ntup_to_poison\<close> {
      lhss = [\<^term>\<open>sem_tup_T X\<close>],
      proc = fn _ => fn ctxt => fn ctm =>
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>sem_tup_T\<close>, _) $ X =>
              (case has_poison X
                 of SOME true =>
                      Thm.apply (Thm.apply \<^cterm>\<open>Pure.eq :: TY \<Rightarrow> TY \<Rightarrow> prop\<close> ctm) \<^cterm>\<open>\<p>\<o>\<i>\<s>\<o>\<n>\<close>
                        |> Thm.trivial
                        |> REPEAT_DETERM (CHANGED (resolve_tac ctxt [is_poison_0, is_poison_N] 1))
                        |> Seq.pull
                        |> Option.map fst
                  | _ => NONE)
           | _ => NONE
              
    }


end