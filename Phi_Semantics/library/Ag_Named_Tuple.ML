local

val is_poison_0 = @{lemma
  \<open> sem_ntup_T (fmupd k \<poison> Ts) \<equiv> \<poison> \<close>
  by (simp add: atomize_eq semty_ntup_eq_poison, meson fmranI fmupd_lookup) }

val is_poison_N = @{lemma
  \<open> sem_ntup_T Ts \<equiv> \<poison>
\<Longrightarrow> k |\<notin>| fmdom Ts
\<Longrightarrow> sem_ntup_T (fmupd k TY Ts) \<equiv> \<poison> \<close>
  by (clarsimp simp add: semty_ntup_eq_poison atomize_eq,
      metis fmdom_notD fmlookup_ran_iff fmupd_lookup option.distinct(1)) }

fun has_poison (Const(\<^const_name>\<open>fmempty\<close>, _)) = SOME false
  | has_poison (Const(\<^const_name>\<open>fmupd\<close>, _) $ _ $ Const(\<^const_name>\<open>sem_poison_T\<close>, _) $ _) = SOME true
  | has_poison (Const(\<^const_name>\<open>fmupd\<close>, _) $ _ $ _ $ X) = has_poison X
  | has_poison _ = NONE

in

val setup_semty_ntup_to_poison =
  Simplifier.define_simproc {
      passive = false,
      name = \<^binding>\<open>semty_ntup_to_poison\<close>,
      kind = Simproc,
      lhss = [\<^term>\<open>sem_ntup_T X\<close>],
      proc = fn _ => fn ctxt => fn ctm =>
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>sem_ntup_T\<close>, _) $ X =>
              (case has_poison X
                 of SOME true =>
                      Thm.apply (Thm.apply \<^cterm>\<open>Pure.eq :: TY \<Rightarrow> TY \<Rightarrow> prop\<close> ctm) \<^cterm>\<open>\<poison>\<close>
                        |> Thm.trivial
                        |> REPEAT_DETERM (CHANGED (resolve_tac ctxt [is_poison_0, is_poison_N] 1))
                        |> Seq.pull
                        |> Option.map fst
                  | _ => NONE)
           | _ => NONE,
      identifier = []
    } #> snd


end