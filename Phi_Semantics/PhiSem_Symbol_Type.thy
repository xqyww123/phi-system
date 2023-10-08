theory PhiSem_Symbol_Type
  imports PhiSem_Symbol
begin

text \<open>Semantic symbol type is a literal string which cannot be modified runtime and has fixed range
  during compilation time and runtime. Some languages have such notion in their semantics, like Ruby,
  while such notion can also be used as a pure tool for semantics formalization, for example,
  to model the attributes or the field names of a structure. \<close>

section \<open>Semantics\<close>

subsection \<open>Type\<close>

virtual_datatype \<phi>symbol_ty = T_symbol :: unit

debt_axiomatization T_symbol :: \<open>unit type_entry\<close>
  where \<phi>symbol_ty_ax: \<open>\<phi>symbol_ty TY_CONS_OF T_symbol\<close>

interpretation \<phi>symbol_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_symbol using \<phi>symbol_ty_ax .

hide_fact \<phi>symbol_ty_ax \<phi>symbol_ty_axioms \<phi>symbol_ty_names_def \<phi>symbol_ty_def
  \<phi>symbol_ty_prjs_axioms \<phi>symbol_ty_prjs_def \<phi>symbol_ty.axioms \<phi>symbol_ty.intro
  \<phi>symbol_ty_prjs.axioms

abbreviation symbol :: TY where \<open>symbol \<equiv> T_symbol.mk ()\<close>


subsection \<open>Value\<close>

virtual_datatype \<phi>symbol_val =
  V_symbol     :: \<open>symbol\<close>

debt_axiomatization V_symbol :: \<open>symbol value_entry\<close>
  where \<phi>symbol_val_ax: \<open>\<phi>symbol_val VAL_CONS_OF V_symbol\<close>

interpretation \<phi>symbol_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_symbol using \<phi>symbol_val_ax .

hide_fact \<phi>symbol_val_ax \<phi>symbol_val_axioms


subsection \<open>Semantic Properties\<close>

debt_axiomatization
    \<phi>embed_semantic_symbol: \<open>\<phi>embed_semantic_symbol = V_symbol.mk\<close>
and WT_symbol  [simp]: \<open>Well_Type symbol = { V_symbol.mk sym | sym. True } \<close>
and can_eqcmp_aint[simp]: \<open>Can_EqCompare res (V_symbol.mk s1) (V_symbol.mk s2)\<close>
and eqcmp_aint[simp]: \<open>EqCompare (V_symbol.mk s1) (V_symbol.mk s2) \<longleftrightarrow> s1 = s2\<close>
and  zero_aint[simp]: \<open>Zero symbol = Some (V_symbol.mk SYMBOL(zero))\<close>

section \<open>\<phi>-Types\<close>

lemma [\<phi>reason 1000]:
  "\<phi>Equal Symbol (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: Symbol_expn \<phi>embed_semantic_symbol)

lemma [\<phi>reason 1000]:
  "Semantic_Zero_Val symbol Symbol SYMBOL(zero)"
  unfolding Semantic_Zero_Val_def by (simp add: Symbol_expn \<phi>embed_semantic_symbol)

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> Symbol) symbol\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: Symbol_expn \<phi>embed_semantic_symbol)


end