theory PhiEx_All
  imports PhiEx_DynArr
          PhiEx_Linked_Lst
          PhiEx_Slice
          PhiEx_BinTree
          PhiEx_Strassen
begin




ML \<open>PLPR_Statistics.utilization \<^theory> "program" |> Net.content |> map (apfst (Thm.cterm_of \<^context>))
      |> length \<close>


ML \<open>fun report_utilization statistic_groups reasoner_groups =
  let open Pretty
   in writeln (chunks (map (fn sgroup =>
        chunks [str sgroup,
                block (separate ", " (
                  map (fn rgroup => 
                    block [str (the (snd rgroup)), str ": ",
                           str (string_of_int (
                        Phi_Reasoner.utilization_of_group_in_all_theories
                            (Context.Theory \<^theory>) (the (snd rgroup)) sgroup
                          |> filter (fn (_, i) => i > 0)
                          |> length
                      ))]) reasoner_groups)) ]
      ) statistic_groups))
  end

  val counters = [transformation_counter]
  fun report_transformation_performance () =
    File_Stream.open_output (fn out =>
      List.app (fn (cnter, data) =>
                  if member pointer_eq counters cnter
                  then List.app (fn (num_opr, steps, _) =>
                          let open File_Stream
                           in output out (string_of_int num_opr) ;
                              output out ", " ;
                              output out (string_of_int steps) ;
                              output out "\n"
                          end ) data
                  else ())
               (PLPR_Statistics.get_subgoal_statistics ())
      )
      (Path.make ["Phi_Examples", "transformation-opr-step.csv"])

\<close>

ML \<open>report_utilization ["program", "derivation"]
       [@{reasoner_group %Field}, @{reasoner_group %Array},
        @{reasoner_group %\<phi>MapAt}, @{reasoner_group %\<phi>MapAt_L}, @{reasoner_group %\<phi>Some},
        @{reasoner_group %Mem_Coercion}, @{reasoner_group %\<phi>Share},
        @{reasoner_group %Var}, @{reasoner_group %MemBlk}, 
        @{reasoner_group %\<phi>Mul_Quant_Tree},
        @{reasoner_group %Linked_Lst}, @{reasoner_group %DynArr} (*,
        @{reasoner_group %BinTree}, @{reasoner_group %Bin_Search_Tree}, @{reasoner_group %AVL_Tree}*) ] \<close>

ML \<open>report_transformation_performance ()\<close>

end