theory Scratch_Export
  imports Phi_Examples.Dynamic_Array_arbi_len
begin

declare [[\<phi>trace_reasoning = 2]]

abbreviation \<open>BIGSTAR ps buckets T \<equiv> buckets \<Ztypecolon> \<big_ast>\<^sup>\<phi> {i. length ps \<le> i \<and> i < length ps} (\<lambda>i. DynArr (ps ! i) \<lbrace> k: \<nat>(\<size_t>), v: T \<rbrace>)\<close>

lemma a_opaque_F_target_with_unit:
  \<open> BIGSTAR ps buckets T\<heavy_comma> F \<transforms> F\<heavy_comma> Void \<close>
  for F :: assn
  by \<phi>reason

lemma b_opaque_F_target_keeps_L:
  \<open> BIGSTAR ps buckets T\<heavy_comma> F \<transforms> F\<heavy_comma> BIGSTAR ps buckets T \<close>
  for F :: assn
  by \<phi>reason

lemma c_opaque_F_remainder_unit:
  \<open> BIGSTAR ps buckets T\<heavy_comma> F \<transforms> F \<remains> 1 \<close>
  for F :: assn
  by \<phi>reason

end
