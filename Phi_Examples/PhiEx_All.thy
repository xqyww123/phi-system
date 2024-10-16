theory PhiEx_All
  imports Dynamic_Array
          Linked_List
          Quicksort
          Rational_Arith
          Binary_Trees
          Matrix_Oprs
          Binary_Search
          Bucket_Hash
begin

ML \<open>PLPR_Statistics.utilization \<^theory> "program" |> Net.content |> map (apfst (Thm.cterm_of \<^context>))
      |> length \<close>

ML \<open>
  fun filter_out (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>to\<close>, _) $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>OPEN\<close>, _) $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>MAKE\<close>, _) $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = filter_out X
    | filter_out (Abs (_, _, X)) = filter_out X
    | filter_out (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>Identifier_of\<close>, _) $ _ $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>Semantic_Type\<close>, _) $ _ $ _) = true
    | filter_out _ = false

  fun report_utilization statistic_groups reasoner_groups =
  let open Pretty
   in writeln (chunks (map (fn sgroup =>
        chunks [str sgroup,
                block (separate ", " (
                  map (fn rgroup => 
                    block [str (the (snd rgroup)), str ": ",
                           str (string_of_int (
                        Phi_Reasoner.utilization_of_group_in_all_theories
                            (Context.Theory \<^theory>) (the (snd rgroup)) [sgroup]
                          |> filter (fn (th, i) => i > 0 andalso
                                        not (filter_out (Thm.concl_of th)))
                          |> length
                      ))]) reasoner_groups)) ]
      ) statistic_groups))
  end

  fun report_utilization_to_file statistic_groups reasoner_groups =
    let open File_Stream
     in open_output (fn out =>
        List.app (fn (column,sgroup) => (
          output out column ; output out "\n" ;
          List.app (fn (name, rgroup) => (
            output out name ;
            output out ", " ;
            output out (string_of_int (
              Phi_Reasoner.utilization_of_group_in_all_theories
                (Context.Theory \<^theory>) (the (snd rgroup)) [sgroup]
                  |> filter (fn (th, i) => i > 0 andalso
                                not (filter_out (Thm.concl_of th)))
                  |> length));
            output out "\n"
          )) reasoner_groups;
          output out "\n"
      )) statistic_groups
    ) (Path.make ["Phi_Examples", "usage_of_generated_rules.csv"])
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

  fun report_timing () =
    File_Stream.open_output (fn out =>
        let val timing = PLPR_Statistics.timing_of_semantic_operations ()
         in List.app (fn {total, reasoning, proof_evaluation, proof_search} =>
                          let open File_Stream
                           in output out (string_of_int (Time.toMicroseconds reasoning)) ;
                              output out ", " ;
                              output out (string_of_int (Time.toMicroseconds proof_evaluation)) ;
                              output out ", " ;
                              output out (string_of_int (Time.toMilliseconds proof_search)) ;
                              output out ", " ;
                              output out (string_of_int (Time.toMilliseconds total)) ;
                              output out "\n"
                          end ) timing
        end
      ) (Path.make ["Phi_Examples", "timing.csv"])
\<close>

ML \<open>report_utilization ["program", "derivation"]
       [@{reasoner_group %Field}, @{reasoner_group %Array},
        @{reasoner_group %\<phi>MapAt}, @{reasoner_group %\<phi>MapAt_L}, @{reasoner_group %\<phi>Some},
        @{reasoner_group %Mem_Coercion}, @{reasoner_group %\<phi>Share},
        @{reasoner_group %Resource_Space},
        @{reasoner_group %Var}, @{reasoner_group %MemBlk},
        @{reasoner_group %\<phi>Mul_Quant_Tree}, @{reasoner_group %\<phi>Mul_Quant},
        @{reasoner_group %Linked_Lst}, @{reasoner_group %Dynamic_Array_arbi_len.DynArr},
        @{reasoner_group %BinTree}, @{reasoner_group %Bin_Search_Tree}, @{reasoner_group %AVL_Tree},
  @{reasoner_group %Hash} ] \<close>

ML \<open>report_utilization_to_file [("column R", "program"), ("column R'", "derivation")]
      [("Record", @{reasoner_group %\<phi>MapAt_L}),
       ("Variable", @{reasoner_group %Var}),
       ("Ref", @{reasoner_group %MemBlk}),
       ("Quantifier Star", @{reasoner_group %\<phi>Mul_Quant}),
       ("Array Slice", @{reasoner_group %\<phi>Mul_Quant_Tree}),
       ("Linked List", @{reasoner_group %Linked_Lst}),
       ("Dynamic Array", @{reasoner_group %Dynamic_Array_arbi_len.DynArr}),
       ("Binary Tree", @{reasoner_group %BinTree}),
       ("Search Tree", @{reasoner_group %Bin_Search_Tree}),
       ("Lookup AVL", @{reasoner_group %AVL_Tree}),
       ("Bucket Hash", @{reasoner_group %Hash})]  \<close>

ML \<open>report_transformation_performance ()\<close>
ML \<open>report_timing ()\<close>

ML \<open>PLPR_Statistics.timing_of_semantic_operations ()\<close>



end