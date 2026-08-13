theory PhiSem_Mem_C_AI \<comment> \<open>AI: Integer of Arbitrary precision\<close>
  imports PhiSem_Mem_C PhiSem_Int_ArbiPrec PhiSem_Aggregate_Array
begin


debt_axiomatization
      MemObj_Size_aint: \<open>0 < MemObj_Size \<aint>\<close>

lemma phantom_mem_semantic_type_aint[simp]:
  \<open> \<not> phantom_mem_semantic_type \<aint> \<close>
  unfolding phantom_mem_semantic_type_def
  using MemObj_Size_aint by blast





proc calloc_aN:
  requires \<open>\<param> T\<close>
  input \<open>n \<Ztypecolon> \<val> \<nat>\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  premises \<open>TY \<noteq> \<poison>\<close>
  output \<open>replicate n z \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce> (Array n T))\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr (\<array>[n] TY)
          \<subj> addr. address_to_base addr \<close>
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  note list_all2_conv_all_nth[simp] ;;

  semantic_local_value($n) \<open>\<aint>\<close>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=\<open>\<array>[nat (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>1))] TY\<close>
                                               and U=\<open>{sem_mk_array (replicate (nat (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>1))) (the (Zero TY)))}\<close>]

  semantic_assumption \<open>type_storable_in_mem (\<array>[nat (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>1))] TY)\<close>

  \<open>replicate n z \<Ztypecolon> MAKE _ (\<mem>-\<blk>[blk] (MAKE _ (\<mem>-\<coerce> (Array n T))))\<close>
  \<open>replicate n z \<Ztypecolon> MAKE _ (\<mem>[Addr blk 0] (Array n T))\<close>

  have t1: \<open>valid_memaddr (Addr blk [])\<close>
    unfolding valid_memaddr_def Valid_MemBlk_def
    using \<open>block.layout blk = \<array>[n] TY\<close>
    by (cases blk; clarsimp simp: \<open>type_storable_in_mem (\<array>[n] TY)\<close> address_type_def the_\<phi>(8)) \<semicolon>
  
  semantic_return \<open>sem_mk_pointer (Addr (\<phi>arg.dest \<v>2) 0) \<Turnstile> (Addr blk 0 \<Ztypecolon> TypedPtr (\<array>[n] TY))\<close>

\<medium_right_bracket> .


proc calloc_aN2:
  requires \<open>\<param> T\<close>
  input \<open>n \<Ztypecolon> \<val> \<nat>\<heavy_comma> m \<Ztypecolon> \<val> \<nat>\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  premises \<open>TY \<noteq> \<poison>\<close>
  output \<open>replicate n (replicate m z) \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce> \<Array>[n] \<Array>[m] T)\<heavy_comma>
          addr \<Ztypecolon> \<val> TypedPtr (\<array>[n] \<array>[m] TY)
          \<subj> addr. address_to_base addr \<close>
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  note list_all2_conv_all_nth[simp] ;;

  semantic_local_value($n) \<open>\<aint>\<close>
  semantic_local_value($m) \<open>\<aint>\<close>
  semantic_assert \<open>Zero TY \<noteq> None\<close>

  apply_rule FIC.aggregate_mem.allocate_rule
            [where TY=\<open>\<array>[n] \<array>[m] TY\<close>
               and U=\<open>{sem_mk_array (replicate (nat (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>1)))
                                    (sem_mk_array (replicate (nat (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>2))) (the (Zero TY)))))}\<close>]

  semantic_assumption \<open>type_storable_in_mem (\<array>[nat (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>1))] \<array>[nat (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>2))] TY)\<close>

  \<open>replicate n (replicate m z) \<Ztypecolon> MAKE _ (\<mem>-\<blk>[blk] (MAKE _ (\<mem>-\<coerce> (Array n (Array m T)))))\<close>
  \<open>replicate n (replicate m z) \<Ztypecolon> MAKE _ (\<mem>[Addr blk 0] (Array n (Array m T)))\<close>

  have t1: \<open>valid_memaddr (Addr blk [])\<close>
    unfolding valid_memaddr_def Valid_MemBlk_def
    using \<open>block.layout blk = \<array>[n] \<array>[m] TY\<close>
    by (cases blk; clarsimp simp: \<open>type_storable_in_mem (\<array>[n] \<array>[m] TY)\<close> address_type_def the_\<phi>(9)) \<semicolon>
  
  semantic_return \<open>sem_mk_pointer (Addr (\<phi>arg.dest \<v>3) 0) \<Turnstile> (Addr blk 0 \<Ztypecolon> TypedPtr (\<array>[n] \<array>[m] TY))\<close>

\<medium_right_bracket> .


end