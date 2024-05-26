local

val is_poison_0 = @{lemma
  \<open> semty_ntup (fmupd k \<p>\<o>\<i>\<s>\<o>\<n> Ts) \<equiv> \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by (simp add: atomize_eq semty_ntup_eq_position, meson fmranI fmupd_lookup) }

val is_poison_N = @{lemma
  \<open> semty_ntup Ts \<equiv> \<p>\<o>\<i>\<s>\<o>\<n>
\<Longrightarrow> k |\<notin>| fmdom Ts
\<Longrightarrow> semty_ntup (fmupd k TY Ts) \<equiv> \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by (clarsimp simp add: semty_ntup_eq_position atomize_eq,
      metis fmdom_notD fmlookup_ran_iff fmupd_lookup option.distinct(1)) }

fun has_poison (Const(\<^const_name>\<open>fmempty\<close>, _)) = SOME false
  | has_poison (Const(\<^const_name>\<open>fmupd\<close>, _) $ _ $ Const(\<^const_name>\<open>\<p>\<o>\<i>\<s>\<o>\<n>\<close>, _) $ _) = SOME true
  | has_poison (Const(\<^const_name>\<open>fmupd\<close>, _) $ _ $ _ $ X) = has_poison X
  | has_poison _ = NONE

in

val setup_semty_ntup_to_poison =
  Simplifier.define_simproc \<^binding>\<open>semty_ntup_to_poison\<close> {
      lhss = [\<^term>\<open>semty_ntup X\<close>],
      proc = fn _ => fn ctxt => fn ctm =>
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>semty_ntup\<close>, _) $ X =>
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