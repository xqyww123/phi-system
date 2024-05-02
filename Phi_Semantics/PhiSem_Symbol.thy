theory PhiSem_Symbol
  imports PhiSem_Base
begin

text \<open>Semantic symbol type is a literal string which cannot be modified runtime and has fixed range
  during compilation time and runtime. Some languages have such notion in their semantics, like Ruby,
  while such notion can also be used as a pure tool for semantics formalization, for example,
  to model the attributes or the field names of a structure. \<close>

section \<open>Semantics\<close>

debt_axiomatization \<phi>embed_semantic_symbol :: \<open>symbol \<Rightarrow> VAL\<close>
  where \<phi>embed_semantic_symbol_inj[simp]: \<open>\<phi>embed_semantic_symbol x = \<phi>embed_semantic_symbol y \<longleftrightarrow> x = y\<close>

section \<open>\<phi>-Types\<close>

\<phi>type_def Symbol :: "(VAL, symbol) \<phi>"
  where \<open>s \<Ztypecolon> Symbol \<equiv> \<phi>embed_semantic_symbol s \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality

section \<open>Instructions\<close>

text \<open>There is no semantic instruction to make a symbol, because they are merely literal string
  known during compilation time.\<close>

lemma [\<phi>reason %\<phi>synthesis_literal]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (\<phi>embed_semantic_symbol s)] Symbol \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
  unfolding Transformation_def semantic_literal_def Action_Tag_def
  by clarsimp

lemma "_intro_symbol_":
  \<open>S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S \<heavy_comma> s \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (\<phi>embed_semantic_symbol s)] Symbol\<close>
  unfolding Transformation_def semantic_literal_def
  by clarsimp


\<phi>lang_parser literal_symbol (%\<phi>parser_unique, %\<phi>lang_push_val) ["<string>"]
                            (\<open>CurrentConstruction programming_mode ?blk ?H ?S\<close>) \<open>
fn (oprs,(ctxt,sequent)) => Parse.string >> (fn s => fn _ =>
  (oprs, (ctxt, #transformation_rule Phi_Working_Mode.programming
            OF [sequent, Thm.instantiate
                            (TVars.empty, Vars.make [((("s",0),\<^typ>\<open>symbol\<close>),
                                                     Thm.cterm_of ctxt (Phi_Tool_Symbol.mk_symbol s))])
                            @{thm "_intro_symbol_"}])))
\<close>



end