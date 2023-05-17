theory PhiSem_Aggregate_Path
  imports PhiSem_Base PhiTool_Symbol
begin

section \<open>Path of Elements in an Aggregate Structure\<close>

datatype 'val aggregate_index' = AgIdx_N nat | AgIdx_S symbol | AgIdx_V 'val

type_synonym aggregate_index = \<open>VAL aggregate_index'\<close>
type_synonym aggregate_path = \<open>aggregate_index list\<close>

nonterminal "\<phi>_ag_idx_"

syntax "_ID_ag_idx_"  :: \<open>\<phi>_symbol_ \<Rightarrow> \<phi>_ag_idx_\<close> ("_")
       "_0_ag_idx_"   :: \<open>\<phi>_ag_idx_\<close> ("0")
       "_1_ag_idx_"   :: \<open>\<phi>_ag_idx_\<close> ("1")
       "_num_ag_idx_" :: \<open>num_token \<Rightarrow> \<phi>_ag_idx_\<close> ("_")
       "_log_ag_idx_" :: \<open>logic \<Rightarrow> \<phi>_ag_idx_\<close> ("LOGIC'(_')")
       "_MK_ag_idx_"  :: \<open>\<phi>_ag_idx_ \<Rightarrow> aggregate_index\<close> ("\<phi>AG'_IDX'(_')")

ML \<open>
structure Phi_Aggregate_Syntax = struct

fun parse_index (Const(\<^syntax_const>\<open>_ID_ag_idx_\<close> , _) $ id) =
        Const(\<^const_name>\<open>AgIdx_S\<close>, dummyT) $ (Const(\<^const_name>\<open>mk_symbol\<close>, dummyT) $ id)
  | parse_index (Const(\<^syntax_const>\<open>_num_ag_idx_\<close>, _) $ Free (n, _)) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ mk_numeral_nat (Value.parse_nat n)
  | parse_index (Const(\<^syntax_const>\<open>_log_ag_idx_\<close>, _) $ tm) = tm
  | parse_index (Const(\<^syntax_const>\<open>_0_ag_idx_\<close>, _)) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ mk_numeral_nat 0
  | parse_index (Const(\<^syntax_const>\<open>_1_ag_idx_\<close>, _)) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ mk_numeral_nat 1
  | parse_index x = (@{print} x; error "SYNTAX ERROR #ee2e77a2-b6d7-4acf-ae18-5d266dc2f06e")

fun print_index (Const(\<^const_syntax>\<open>AgIdx_S\<close>, _) $ (Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ tm)) =
     (case Phi_Tool_Symbol.revert_symbol (dest_synt_numeral tm)
        of SOME id => Free(id, dummyT)
         | NONE => tm)
  | print_index (Const (\<^const_syntax>\<open>AgIdx_N\<close>, _) $ tm) =
      Free(string_of_int (dest_synt_numeral tm), dummyT)
  | print_index tm = Const(\<^syntax_const>\<open>_log_ag_idx_\<close>, dummyT) $ tm

end
\<close>

parse_translation \<open>[
  (\<^syntax_const>\<open>_MK_ag_idx_\<close>, fn ctxt => fn [x] => Phi_Aggregate_Syntax.parse_index x)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>AgIdx_S\<close>, (fn ctxt => fn [Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ tm] =>
      case Phi_Tool_Symbol.revert_symbol (dest_synt_numeral tm)
        of SOME id => Const (\<^syntax_const>\<open>_MK_ag_idx_\<close>, dummyT) $ Free(id, dummyT)
         | NONE => tm)),
  (\<^const_syntax>\<open>AgIdx_N\<close>, (fn ctxt => fn [tm] =>
      case try dest_synt_numeral tm
        of SOME N => Const (\<^syntax_const>\<open>_MK_ag_idx_\<close>, dummyT) $ Free(string_of_int N, dummyT)))
]\<close>




end