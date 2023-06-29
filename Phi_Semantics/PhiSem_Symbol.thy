theory PhiSem_Symbol
  imports PhiSem_Base
begin

text \<open>Semantic symbol type is a literal string which cannot be modified runtime and has fixed range
  during compilation time and runtime. Some languages have such notion in their semantics, like Ruby,
  while such notion can also be used as a pure tool for semantics formalization, for example,
  to model the attributes or the field names of a structure. \<close>

section \<open>Semantics\<close>

debt_axiomatization \<phi>embed_semantic_symbol :: \<open>symbol \<Rightarrow> VAL\<close>

section \<open>\<phi>-Types\<close>

definition Symbol :: "(VAL, symbol) \<phi>"
  where "Symbol = (\<lambda>s. { \<phi>embed_semantic_symbol s })"

lemma Symbol_expn[\<phi>expns]:
  \<open>p \<in> (s \<Ztypecolon> Symbol) \<longleftrightarrow> p = \<phi>embed_semantic_symbol s\<close>
  unfolding \<phi>Type_def by (simp add: Symbol_def)

lemma Symbol_inhabited[elim!]:
  "Inhabited (x \<Ztypecolon> Symbol) \<Longrightarrow> C \<Longrightarrow> C" .

lemma [\<phi>inhabitance_rule 1000]:
  "Inhabited (x \<Ztypecolon> Symbol) \<longrightarrow> True"
  by blast


section \<open>Instructions\<close>

text \<open>There is no semantic instruction to make a symbol, because they are merely literal string
  known during compilation time.\<close>

lemma "_intro_symbol_\<phi>app":
  \<open>Void \<i>\<m>\<p>\<l>\<i>\<e>\<s> s \<Ztypecolon> \<v>\<a>\<l>[\<phi>literal (\<phi>embed_semantic_symbol s)] Symbol\<close>
  unfolding Imply_def \<phi>literal_def
  by (clarsimp simp add: Symbol_expn Val_expn)

lemma "_intro_symbol_":
  \<open>S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S \<heavy_comma> s \<Ztypecolon> \<v>\<a>\<l>[\<phi>literal (\<phi>embed_semantic_symbol s)] Symbol\<close>
  unfolding Imply_def \<phi>literal_def
  by (clarsimp simp add: Symbol_expn Val_expn)


\<phi>processor literal_symbol 8500 (\<open>CurrentConstruction programming_mode ?blk ?H ?S\<close>) \<open>
fn (ctxt,sequent) => Parse.string >> (fn s => fn _ =>
  (ctxt, #transformation_rule Phi_Working_Mode.programming
            OF [sequent, Thm.instantiate
                            (TVars.empty, Vars.make [((("s",0),\<^typ>\<open>symbol\<close>),
                                                     Thm.cterm_of ctxt (Phi_Tool_Symbol.mk_symbol s))])
                            @{thm "_intro_symbol_"}]))
\<close>



end