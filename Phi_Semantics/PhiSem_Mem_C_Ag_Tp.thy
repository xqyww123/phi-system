theory PhiSem_Mem_C_Ag_Tp
  imports PhiSem_Mem_C PhiSem_Aggregate_Tuple
begin

section \<open>Tuple in Memory\<close>

subsection \<open>Semantics\<close>

debt_axiomatization
    Map_of_Val_tup: \<open>Map_of_Val (sem_mk_tup vs) =
      (\<lambda>path. case path of AgIdx_N i # path' \<Rightarrow>
                                if i < length vs then Map_of_Val (vs ! i) path' else 1
                         | _ \<Rightarrow> 1)\<close>

subsection \<open>Syntax\<close>

setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 110 (
    fn ((ctxt,i), f, Const(\<^const_syntax>\<open>Tuple_Field\<close>, _) $ T) =>
        SOME (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, dummyT)
                $ (Const(\<^const_name>\<open>Cons\<close>, dummyT)
                    $ (Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ (HOLogic.mk_number HOLogic.natT i))
                    $ Const(\<^const_name>\<open>Nil\<close>, dummyT))
                $ f (ctxt,0) T)
     | ((ctxt,i), f, Const(\<^const_syntax>\<open>\<phi>Share\<close>, _) $ sh $ (
                        Const (\<^const_name>\<open>Tuple_Field\<close>, _) $ T)) =>
        SOME (Const(\<^const_name>\<open>\<phi>Share\<close>, dummyT)
          $ sh
          $ (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, dummyT)
                $ (Const(\<^const_name>\<open>Cons\<close>, dummyT)
                    $ (Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ (HOLogic.mk_number HOLogic.natT i))
                    $ Const(\<^const_name>\<open>Nil\<close>, dummyT))
                $ f (ctxt,0) T))
     | X => NONE)
)\<close>

(* example
term \<open>\<m>\<e>\<m>[addr] \<lbrace> T, U, E \<rbrace> \<close>
*)

setup \<open>Context.theory_map (
  Phi_Mem_Printer.add 90 (fn (ctxt, f, X) =>
  let exception BYPASS
      exception REJECT in
  let fun chk_seps1 (tm as Const(\<^const_syntax>\<open>Phi_Types.\<phi>MapAt_L1\<close>, _)
                              $ (Const(\<^const_syntax>\<open>AgIdx_N\<close>, _) $ n)
                              $ T)
            = SOME (dest_synt_numeral n, tm)
        | chk_seps1 _ = NONE

      val Xs0 = Phi_Help.strip_binop_r \<^const_syntax>\<open>\<phi>Prod\<close> X
            |> map chk_seps1
      val _ = if forall is_none Xs0 then raise BYPASS
              else if exists is_none Xs0 then raise REJECT else ()

      fun chk_seq _ [] = true
        | chk_seq i ((j,_)::L) = i = j andalso chk_seq (i+1) L

      val Xs = map_filter I Xs0
            |> sort (int_ord o apply2 fst)
      val _ = if chk_seq 0 Xs then () else raise REJECT

      fun tr (Const(\<^const_syntax>\<open>Phi_Types.\<phi>MapAt_L1\<close>, _)
                          $ (Const(\<^const_syntax>\<open>AgIdx_N\<close>, _) $ _)
                          $ T)
            = Const(\<^const_syntax>\<open>Tuple_Field\<close>, dummyT) $ f ctxt T
        | tr _ = raise BYPASS

   in SOME (Phi_Help.list_mk_binop_r \<^const_syntax>\<open>\<phi>Prod\<close> (map (tr o snd) Xs))
  end
  handle BYPASS => NONE
       | REJECT => SOME X
  end)
)\<close>

(* example
term \<open>\<m>\<e>\<m>[addr] (AG_IDX(2\<^sup>\<t>\<^sup>\<h>) \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> E \<^emph> AG_IDX(1\<^sup>\<t>\<^sup>\<h>) \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U \<^emph> AG_IDX(0\<^sup>\<t>\<^sup>\<h>) \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)\<close>
*)

subsection \<open>Reasoning\<close>

subsubsection \<open>ToA Mapper\<close>

lemma Mem_Coerce_NTup:
  \<open> (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<lbrace> T \<rbrace>) = (AgIdx_N 0 \<^bold>\<rightarrow>\<^sub># \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) \<close>
  apply (rule \<phi>Type_eqI_BI; unfold BI_eq_iff; clarsimp; rule; clarsimp)
  subgoal for x v
    by (rule exI[where x=\<open>to_share \<circ> map_option discrete \<circ> Map_of_Val v\<close>],
        auto simp add: Map_of_Val_tup fun_eq_iff push_map_cons_neq
             split: aggregate_index'.split list.split)
  subgoal for x v
    by (rule exI[where x=\<open>sem_mk_tup [v]\<close>],
        auto simp add: Map_of_Val_tup fun_eq_iff push_map_cons_neq
             split: aggregate_index'.split list.split) .

definition shift_map

lemma
  \<open> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (T \<^emph> U) = \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T \<^emph> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U \<close>





end