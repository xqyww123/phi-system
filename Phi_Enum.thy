theory Phi_Enum
  imports NuSys Phi_Min
begin

section \<open>Semantic\<close>

subsection \<open>Models\<close>

type_synonym enum_raw_value = nat

datatype enum_type = Enum_Type (id: nat) (members: \<open>enum_raw_value list\<close>)
hide_const (open) id members

datatype enum_value = Enum_Value (type: enum_type) (val: enum_raw_value)
hide_const (open) type val

definition \<open>Enum_Value_of_Type ety ev \<longleftrightarrow>
    enum_value.type ev = ety \<and>
    enum_value.val ev \<in> set (enum_type.members ety)\<close>
definition \<open>Zero_of_Enum ety =
  (if 0 \<in> set (enum_type.members ety) then Some (Enum_Value ety 0) else None)\<close>


subsubsection \<open>Type\<close>

virtual_datatype \<phi>enum_ty = \<phi>min_ty +
  T_enum    :: enum_type \<comment> \<open>in unit of bits\<close>

context \<phi>enum_ty begin
abbreviation \<open>\<tau>Enum \<equiv> T_enum.mk\<close>
end


subsubsection \<open>Value\<close>

virtual_datatype 'TY \<phi>enum_val :: "nonsepable_semigroup" = 'TY \<phi>min_val +
  V_enum    :: enum_value


subsubsection \<open>Semantic Locale\<close>

locale \<phi>enum_sem =
  \<phi>min_sem where TYPES = TYPES
+ \<phi>enum_ty  where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ \<phi>enum_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ \<phi>resource_sem where Resource_Validator = Resource_Validator
for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N => 'VAL::nonsepable_semigroup)
                \<times> ('RES_N => 'RES::total_sep_algebra)) itself\<close>
+
assumes WT_enum[simp]:
  \<open>Well_Type (\<tau>Enum ety)  = { V_enum.mk eval |eval. Enum_Value_of_Type ety eval } \<close>
assumes can_eqcmp_enum[simp]: "Can_EqCompare res (V_enum.mk e1) (V_enum.mk e2) \<longleftrightarrow> enum_value.type e1 = enum_value.type e2"
assumes eqcmp_enum[simp]: "EqCompare (V_enum.mk e1) (V_enum.mk e2) \<longleftrightarrow> e1 = e2"
assumes zero_enum[simp]: \<open>Zero (\<tau>Enum ety) = map_option V_enum.mk (Zero_of_Enum ety)\<close>
begin

lemma Valid_Types[simp]:
  \<open>Valid_Type (\<tau>Enum ety) \<longleftrightarrow> enum_type.members ety \<noteq> []\<close>
  unfolding Inhabited_def
  apply (simp add: Enum_Value_of_Type_def)
  by (metis all_not_in_conv enum_value.sel(1) enum_value.sel(2) set_empty2)

end

locale \<phi>enum =
  \<phi>enum_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                            \<times> ('RES_N \<Rightarrow> 'RES::total_sep_algebra))\<close>
+ \<phi>min where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                          \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                          \<times> ('RES_N \<Rightarrow> 'RES::total_sep_algebra)
                          \<times> ('FIC_N \<Rightarrow> 'FIC::total_sep_algebra))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>


section \<open>\<phi>-Types\<close>

definition (in \<phi>enum_sem) Enum :: \<open>enum_type \<Rightarrow> ('VAL, enum_value) \<phi>\<close>
  where \<open>Enum ety = (\<lambda>ev. { V_enum.mk ev } \<^bold>s\<^bold>u\<^bold>b\<^bold>j Enum_Value_of_Type ety ev)\<close>

lemma (in \<phi>enum_sem) Enum_expn[\<phi>expns]:
  \<open>p \<in> (ev \<Ztypecolon> Enum ety) \<longleftrightarrow> p = V_enum.mk ev \<and> Enum_Value_of_Type ety ev\<close>
  unfolding \<phi>Type_def Enum_def by (simp add: \<phi>expns)

lemma (in \<phi>enum_sem) Enum_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (ev \<Ztypecolon> Enum ety) \<Longrightarrow> (Enum_Value_of_Type ety ev \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma (in \<phi>enum_sem) Enum_eq[\<phi>reason 1000]:
  \<open>\<phi>Equal (Enum ety) (\<lambda>_ _. True) (=)\<close>
  unfolding \<phi>Equal_def by (simp add: \<phi>expns Enum_Value_of_Type_def)

section \<open>Instructions\<close>

paragraph \<open>Constant\<close>

definition (in \<phi>enum_sem) op_const_enum :: \<open>enum_type \<Rightarrow> enum_value \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>op_const_enum ety ev = \<phi>M_assert (Enum_Value_of_Type ety ev) \<ggreater> Return (sem_value (V_enum.mk ev))\<close>

lemma (in \<phi>enum) op_const_enum_\<phi>app:
  \<open> Enum_Value_of_Type ety ev
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_enum ety ev \<lbrace> Void \<longmapsto> \<^bold>v\<^bold>a\<^bold>l ev \<Ztypecolon> Enum ety\<rbrace>\<close>
  unfolding op_const_enum_def
  by (\<phi>reason, assumption, \<phi>reason)

paragraph \<open>Conversion to Int\<close>

definition (in \<phi>enum_sem) op_conv_enum_to_int :: \<open>enum_type \<Rightarrow> nat \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_conv_enum_to_int ety bits v =
    \<phi>M_getV (\<tau>Enum ety) V_enum.dest v (\<lambda>ev.
    \<phi>M_assert (Enum_Value_of_Type ety ev) \<ggreater>
    Return (sem_value (V_int.mk (bits, enum_value.val ev mod 2^bits)))
)\<close>

lemma (in \<phi>enum) op_conv_enum_to_int_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e enum_value.val ev < 2^bits
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_conv_enum_to_int ety bits raw \<lbrace> ev \<Ztypecolon> Val raw (Enum ety) \<longmapsto> \<^bold>v\<^bold>a\<^bold>l enum_value.val ev \<Ztypecolon> \<nat>[bits] \<rbrace>\<close>
  unfolding op_conv_enum_to_int_def
  by (cases raw, simp, \<phi>reason, simp add: Enum_Value_of_Type_def \<phi>expns, \<phi>reason)

paragraph \<open>Conversion from Int\<close>

definition (in \<phi>enum_sem) op_conv_enum_from_int :: \<open>enum_type \<Rightarrow> nat \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_conv_enum_from_int ety bits v =
    \<phi>M_getV (\<tau>Int bits) V_int.dest v (\<lambda>(_,n).
    \<phi>M_assert (n \<in> set (enum_type.members ety)) \<ggreater>
    Return (sem_value (V_enum.mk (Enum_Value ety n)))
)\<close>

lemma (in \<phi>enum) op_conv_enum_from_int_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n \<in> set (enum_type.members ety)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_conv_enum_from_int ety bits raw \<lbrace> n \<Ztypecolon> Val raw \<nat>[bits] \<longmapsto> \<^bold>v\<^bold>a\<^bold>l Enum_Value ety n \<Ztypecolon> Enum ety \<rbrace>\<close>
  unfolding op_conv_enum_from_int_def
  by (cases raw, simp, \<phi>reason, simp add: \<phi>expns, simp add: \<phi>Nat_expn, \<phi>reason,
        simp add: \<phi>expns, \<phi>reason, simp add: \<phi>expns Enum_Value_of_Type_def)

(* TODO:
commands that defines enum type and members.

Syntax:

\<phi>enum name:
  member_name [= <value>]
  ...

 *)



end