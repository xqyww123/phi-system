theory Phi_Element_Path
  imports Phi_System.Calculus_of_Programming Phi_BI.PhiTool_Symbol
begin

section \<open>Path of Elements in an Aggregate Structure\<close>

unspecified_type sVAL \<comment> \<open>small Value\<close>

debt_axiomatization sVAL_emb :: \<open>sVAL \<Rightarrow> VAL\<close>  \<comment> \<open>embedding small value\<close>
                and is_sTY   :: \<open>TY \<Rightarrow> bool\<close>   \<comment> \<open>is small type\<close>
  where sVAL_emb_inj: \<open>sVAL_emb x = sVAL_emb y \<longleftrightarrow> x = y\<close>
    and is_sTY: \<open>is_sTY T \<Longrightarrow> v \<in> Well_Type T \<Longrightarrow> v \<in> range sVAL_emb\<close>
    and is_sTY_poison: \<open>is_sTY \<p>\<o>\<i>\<s>\<o>\<n>\<close>

lemma inj_sVAL_emb:
  \<open>inj sVAL_emb\<close>
  by (meson injI sVAL_emb_inj)


datatype 'val aggregate_index' = AgIdx_N nat | AgIdx_S symbol | AgIdx_V 'val

declare aggregate_index'.simps[\<phi>safe_simp]

type_synonym aggregate_index = \<open>sVAL aggregate_index'\<close>
type_synonym aggregate_path = \<open>aggregate_index list\<close>

nonterminal "\<phi>_ag_idx_"

syntax "_ID_ag_idx_"  :: \<open>\<phi>_symbol_ \<Rightarrow> \<phi>_ag_idx_\<close> ("_")
       "_0_ag_idx_"   :: \<open>\<phi>_ag_idx_\<close> ("0")
       "_1_ag_idx_"   :: \<open>\<phi>_ag_idx_\<close> ("1")
       "_num_ag_idx_" :: \<open>num_token \<Rightarrow> \<phi>_ag_idx_\<close> ("_")
       "_log_ag_idx_" :: \<open>logic \<Rightarrow> \<phi>_ag_idx_\<close> ("LOGIC'_IDX'(_')")
       "_log_num_ag_idx_" :: \<open>logic \<Rightarrow> \<phi>_ag_idx_\<close> ("_\<^sup>\<t>\<^sup>\<h>" [1000] 999)
       "_log_num_ag_idx'_" :: \<open>logic \<Rightarrow> \<phi>_ag_idx_\<close> ("'(_')\<^sup>\<t>\<^sup>\<h>")
       "_log_num_ag_idx_ascii_" :: \<open>logic \<Rightarrow> \<phi>_ag_idx_\<close> ("#_" [1000] 999)
       "_log_num_ag_idx_ascii'_" :: \<open>logic \<Rightarrow> \<phi>_ag_idx_\<close> ("#'(_')")
       "_MK_ag_idx_"  :: \<open>\<phi>_ag_idx_ \<Rightarrow> aggregate_index\<close> ("AG'_IDX'(_')")

ML \<open>
structure Phi_Aggregate_Syntax = struct

fun parse_index (Const(\<^syntax_const>\<open>_ID_ag_idx_\<close> , _) $ id) =
        Const(\<^const_name>\<open>AgIdx_S\<close>, dummyT) $ id
  | parse_index (Const(\<^syntax_const>\<open>_num_ag_idx_\<close>, _) $ Free (n, _)) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ mk_numeral_nat (Value.parse_nat n)
  | parse_index (Const(\<^syntax_const>\<open>_log_ag_idx_\<close>, _) $ tm) = tm
  | parse_index (Const(\<^syntax_const>\<open>_log_num_ag_idx_\<close>, _) $ tm) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ tm
  | parse_index (Const(\<^syntax_const>\<open>_log_num_ag_idx'_\<close>, _) $ tm) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ tm
  | parse_index (Const(\<^syntax_const>\<open>_log_num_ag_idx_ascii_\<close>, _) $ tm) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ tm
  | parse_index (Const(\<^syntax_const>\<open>_log_num_ag_idx_ascii'_\<close>, _) $ tm) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ tm
  | parse_index (Const(\<^syntax_const>\<open>_0_ag_idx_\<close>, _)) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ mk_numeral_nat 0
  | parse_index (Const(\<^syntax_const>\<open>_1_ag_idx_\<close>, _)) =
        Const(\<^const_name>\<open>AgIdx_N\<close>, dummyT) $ mk_numeral_nat 1
  | parse_index x = (@{print} x; error "SYNTAX ERROR #ee2e77a2-b6d7-4acf-ae18-5d266dc2f06e")

fun is_atom (Const ("_free", _) $ X) = is_atom X
  | is_atom (Const ("_var", _) $ X) = is_atom X
  | is_atom (_ $ _) = false
  | is_atom _ = true

fun print_index (Const(\<^const_syntax>\<open>AgIdx_S\<close>, _) $ (Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ tm)) =
     (case Phi_Tool_Symbol.revert_symbol (dest_synt_numeral tm)
        of SOME id => Free(id, dummyT)
         | NONE => tm)
  | print_index (Const(\<^const_syntax>\<open>AgIdx_S\<close>, _) $ tm) =
     Const (\<^syntax_const>\<open>_LOG_EXPR_SYMBOL_\<close>, dummyT) $ tm
  | print_index (Const (\<^const_syntax>\<open>AgIdx_N\<close>, _) $ tm) =
      (case try dest_synt_numeral tm
         of SOME N => Const(\<^syntax_const>\<open>_log_num_ag_idx_\<close>, dummyT) $ Free(string_of_int N, dummyT)
          | _ => if is_atom tm
                 then Const(\<^syntax_const>\<open>_log_num_ag_idx_\<close>, dummyT) $ tm
                 else Const(\<^syntax_const>\<open>_log_num_ag_idx'_\<close>, dummyT) $ tm)
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
        of SOME N => Const (\<^syntax_const>\<open>_MK_ag_idx_\<close>, dummyT) $
                        (Const(\<^syntax_const>\<open>_log_num_ag_idx_\<close>, dummyT) $ Free(string_of_int N, dummyT))
         | NONE => Const (\<^syntax_const>\<open>_MK_ag_idx_\<close>, dummyT) $ (
            if Phi_Aggregate_Syntax.is_atom tm
            then Const (\<^syntax_const>\<open>_log_num_ag_idx_\<close>, dummyT) $ tm
            else Const (\<^syntax_const>\<open>_log_num_ag_idx'_\<close>, dummyT) $ tm)))
]\<close>






end