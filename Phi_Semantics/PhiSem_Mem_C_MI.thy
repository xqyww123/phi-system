theory PhiSem_Mem_C_MI \<comment> \<open>MI: Machine Integer\<close>
  imports PhiSem_Mem_C PhiSem_Machine_Integer PhiSem_Aggregate_Array
begin


debt_axiomatization
      MemObj_Size_int: \<open>MemObj_Size (sem_int_T n) = 0 \<longleftrightarrow> n = 0\<close>
  and int_t_neq_array [simp]: \<open>sem_int_T n \<noteq> \<array>[N] TY\<close>
      \<comment> \<open>No guard needed: \<open>sem_int_T n\<close> is never \<open>\<poison>\<close> (int_t_neq_poison'), so the
          two differ even where the array type degenerates to \<open>\<poison>\<close>.  This is the
          earliest theory that sees both constructors.\<close>

lemma array_neq_int_t [simp]:
  \<open>\<array>[N] TY \<noteq> sem_int_T n\<close>
  using int_t_neq_array by (rule not_sym)

lemma phantom_mem_semantic_type_aint[simp]:
  \<open> phantom_mem_semantic_type (sem_int_T n) \<longleftrightarrow> n = 0 \<close>
  unfolding phantom_mem_semantic_type_def
  using MemObj_Size_int by clarsimp

abbreviation sem_size_t ("\<size_t>")
  where \<open>sem_size_t \<equiv> \<int'>(size_t)\<close>
 

proc calloc:
  requires \<open>\<param> T\<close>
  input \<open>n \<Ztypecolon> \<val> \<nat>(\<size_t>)\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  premises \<open>TY \<noteq> \<poison>\<close>
  output \<open>replicate n z \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce> (Array n T))\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr (\<array>[n] TY)
          \<subj> addr. addr.offset addr = 0\<close>
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  note list_all2_conv_all_nth[simp] \<semicolon>

  semantic_local_value($n) \<open>\<int'>(\<size_t>)\<close>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=\<open>\<array>[snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>1))] TY\<close>
                                               and U=\<open>{sem_mk_array (replicate (snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>1))) (the (Zero TY)))}\<close>]

  semantic_assumption \<open>type_storable_in_mem (\<array>[snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>1))] TY)\<close>

  \<open>replicate n z \<Ztypecolon> MAKE _ (\<mem>-\<blk>[blk] (MAKE _ (\<mem>-\<coerce> (Array n T))))\<close>
  \<open>replicate n z \<Ztypecolon> MAKE _ (\<mem>[Addr blk 0] Array n T)\<close>

  have t1: \<open>valid_memaddr (Addr blk [])\<close>
    unfolding valid_memaddr_def Valid_MemBlk_def
    using \<open>block.layout blk = \<array>[n] TY\<close>
    by (cases blk; clarsimp simp: \<open>type_storable_in_mem (\<array>[n] TY)\<close> address_type_def; auto_sledgehammer)
  note address_type_def [\<phi>sledgehammer_simps] \<semicolon>
  
  semantic_return \<open>sem_mk_pointer (Addr (\<phi>arg.dest \<v>2) 0) \<Turnstile> (Addr blk 0 \<Ztypecolon> TypedPtr (\<array>[n] TY))\<close>
\<medium_right_bracket> .


proc op_shift_pointer [\<phi>overload +]:
  requires \<open>\<param> TY\<close>
  input  \<open>addr \<Ztypecolon> \<val> RawPointer\<heavy_comma> n \<Ztypecolon> \<val> \<nat>('b::len)\<close>
  output \<open>addr ||+ of_nat (MemObj_Size TY * n) \<Ztypecolon> \<val> RawPointer\<close>
\<medium_left_bracket>
  $addr semantic_local_value \<ptr>
  semantic_return \<open>
    sem_mk_pointer (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1) ||+ of_nat (MemObj_Size TY * n))
        \<Turnstile> (addr ||+ of_nat (MemObj_Size TY * n) \<Ztypecolon> RawPointer)\<close>
\<medium_right_bracket> .

proc abst_shift_pointer [\<phi>overload +]:
  requires [unfolded abstract_address_offset_def, useful]: \<open>abstract_address_offset addr TY TY' n addr'\<close>
  input  \<open>addr \<Ztypecolon> \<val> TypedPtr TY\<heavy_comma> n \<Ztypecolon> \<val> \<nat>('b::len)\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>addr' \<Ztypecolon> \<val> TypedPtr TY'\<close>
\<medium_left_bracket>
  op_shift_pointer ($addr to RawPointer, $n) \<open>TY\<close> to \<open>TypedPtr TY'\<close>
\<medium_right_bracket> .
  


end