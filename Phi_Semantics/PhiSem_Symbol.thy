theory PhiSem_Symbol
  imports PhiSem_Base
  abbrevs "<symbol>" = "\<s>\<y>\<m>\<b>\<o>\<l>"
begin

text \<open>Semantic symbol type is a literal string which cannot be modified runtime and has fixed range
  during compilation time and runtime. Some languages have such notion in their semantics, like Ruby,
  while such notion can also be used as a pure tool for semantics formalization, for example,
  to model the attributes or the field names of a structure. \<close>

section \<open>Semantics\<close>

debt_axiomatization \<s>\<y>\<m>\<b>\<o>\<l> :: TY
                and sem_mk_symbol   :: \<open>symbol \<Rightarrow> VAL\<close>
                and sem_dest_symbol :: \<open>VAL \<Rightarrow> symbol\<close>
where WT_symbol  [simp]: \<open>Well_Type \<s>\<y>\<m>\<b>\<o>\<l> = { sem_mk_symbol sym | sym. True } \<close>
  and can_eqcmp_aint[simp]: \<open>Can_EqCompare res (sem_mk_symbol s1) (sem_mk_symbol s2)\<close>
  and eqcmp_aint[simp]: \<open>EqCompare (sem_mk_symbol s1) (sem_mk_symbol s2) \<longleftrightarrow> s1 = s2\<close>
  and  zero_aint[simp]: \<open>Zero \<s>\<y>\<m>\<b>\<o>\<l> = Some (sem_mk_symbol SYMBOL(zero))\<close>

lemma sem_mk_symbol_inj[simp]:
  \<open>sem_mk_symbol x = sem_mk_symbol y \<longleftrightarrow> x = y\<close>
  by (metis eqcmp_aint)

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal \<s>\<y>\<m>\<b>\<o>\<l> \<close>
  unfolding Is_Type_Literal_def ..

section \<open>\<phi>-Types\<close>

\<phi>type_def Symbol :: "(VAL, symbol) \<phi>"
  where \<open>s \<Ztypecolon> Symbol \<equiv> sem_mk_symbol s \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality
       and \<open>\<t>\<y>\<p>\<e>\<o>\<f> Symbol = \<s>\<y>\<m>\<b>\<o>\<l>\<close>
       and \<open>Semantic_Zero_Val \<s>\<y>\<m>\<b>\<o>\<l> Symbol SYMBOL(zero)\<close>
       and Inhabited


lemma [\<phi>reason 1000]:
  "\<phi>Equal Symbol (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by simp


section \<open>Instructions\<close>

text \<open>There is no semantic instruction to make a symbol, because they are merely literal string
  known during compilation time.\<close>

lemma [\<phi>reason %\<phi>synthesis_literal]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (sem_mk_symbol s)] Symbol \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
  unfolding Transformation_def semantic_literal_def Action_Tag_def
  by clarsimp

lemma "_intro_symbol_":
  \<open>S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S \<heavy_comma> s \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (sem_mk_symbol s)] Symbol\<close>
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