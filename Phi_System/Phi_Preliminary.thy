chapter \<open>Theoretical Foundations\<close>

section \<open>Preliminary\<close>

theory Phi_Preliminary
  imports Main "Phi_Algebras.Algebras"
          Phi_Logic_Programming_Reasoner.Phi_Logic_Programming_Reasoner
          Phi_Logic_Programming_Reasoner.PLPR_error_msg
  keywords "optional_translations" :: thy_decl
begin

declare [ [ML_debugger, ML_exception_debugger]]

subsection \<open>Named Theorems\<close>

named_theorems \<phi>expns \<open>Semantics Expansions, used to expand assertions semantically.\<close>
and \<phi>programming_simps \<open>Simplification rules used in the deductive programming\<close>

declare set_mult_expn[\<phi>expns] Premise_def[\<phi>expns]

subsection \<open>Error Mechanism\<close>

declare [ [ML_debugger, ML_exception_debugger] ]

ML_file \<open>library/tools/error.ML\<close>

subsection \<open>Helper ML\<close>

ML_file \<open>library/tools/Phi_Help.ML\<close>
ML_file \<open>library/tools/Hook.ML\<close>

ML \<open>signature PHI_SYNTAX = sig end
structure Phi_Syntax : PHI_SYNTAX = struct end\<close>

subsection \<open>Helper Lemmas\<close>

lemma imp_implication: "(P \<longrightarrow> Q \<Longrightarrow> PROP R) \<equiv> ((P \<Longrightarrow> Q) \<Longrightarrow> PROP R)" by rule simp+

subsection \<open>Helper Attributes \& Tactics\<close>

attribute_setup rotated = \<open>Scan.lift (Scan.optional Parse.int 1 -- Scan.optional Parse.int 0) >>
  (fn (k,j) => Thm.rule_attribute [] (fn _ => Thm.permute_prems j k))\<close>
  \<open>Enhanced version of the Pure.rotated\<close>

attribute_setup TRY_THEN = \<open>(Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- Attrib.thm
      >> (fn (i, B) => Thm.rule_attribute [B] (fn _ => fn A => A RSN (i, B) handle THM _ => A)))
    \<close> "resolution with rule, and do nothing if fail"


subsection \<open>Helper Objects\<close>

subsubsection \<open>Big Number\<close>

text \<open>A tag to suppress unnecessary expanding of big numbers like \<open>2^256  \<close>\<close>

definition \<open>Big x = x\<close>

lemma [iff]:
  \<open>(2::nat) ^ Big 8  = 256\<close>
  \<open>(2::nat) ^ Big 16 = 65536\<close>
  \<open>(2::nat) ^ Big 32 = 4294967296\<close>
  by (simp add: Big_def)+

lemma [iff]:
  \<open> numeral x < (2::'a) ^ Big n \<longleftrightarrow> numeral x < (2::'a::{numeral,power,ord}) ^ n\<close>
  \<open> 1 < (2::'a) ^ Big n \<longleftrightarrow> 1 < (2::'a::{numeral,power,ord}) ^ n\<close>
  \<open> 0 < (2::'b) ^ Big n \<longleftrightarrow> 0 < (2::'b::{numeral,power,ord,zero}) ^ n\<close>
  \<open> n < 16 \<Longrightarrow> Big n = n \<close>
  unfolding Big_def by simp+



subsection \<open>Helper Antiquotations\<close>

setup \<open>
let
  val basic_entity = Document_Output.antiquotation_pretty_source_embedded
  fun pretty_term_style ctxt (style, t) = Document_Output.pretty_term ctxt (style t)

  fun typ  mode = Scan.peek (Args.named_typ  o Syntax.read_typ
                                             o Proof_Context.set_mode mode o Context.proof_of)
  fun term mode = Scan.peek (Args.named_term o Syntax.read_term
                                             o Proof_Context.set_mode mode o Context.proof_of)
  fun prop mode = Scan.peek (Args.named_term o Syntax.read_prop
                                             o Proof_Context.set_mode mode o Context.proof_of)

in
   ML_Antiquotation.inline_embedded \<^binding>\<open>pattern\<close>
    (Args.term_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term))
#> ML_Antiquotation.inline_embedded \<^binding>\<open>pattern_prop\<close>
    (prop Proof_Context.mode_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term))
#> ML_Antiquotation.value_embedded \<^binding>\<open>schematic_ctyp\<close> (typ Proof_Context.mode_schematic
      >> (fn T => "Thm.ctyp_of ML_context"  ^ ML_Syntax.atomic (ML_Syntax.print_typ T)))
#> ML_Antiquotation.value_embedded \<^binding>\<open>schematic_cterm\<close> (term Proof_Context.mode_schematic
      >> (fn t => "Thm.cterm_of ML_context" ^ ML_Syntax.atomic (ML_Syntax.print_term t)))
#> ML_Antiquotation.value_embedded \<^binding>\<open>schematic_cprop\<close> (prop Proof_Context.mode_schematic
      >> (fn t => "Thm.cterm_of ML_context" ^ ML_Syntax.atomic (ML_Syntax.print_term t)))
#> basic_entity \<^binding>\<open>schematic_term\<close> (Term_Style.parse -- term Proof_Context.mode_schematic)
                                        pretty_term_style
#> basic_entity \<^binding>\<open>schematic_prop\<close> (Term_Style.parse -- prop Proof_Context.mode_schematic)
                                        pretty_term_style
#> basic_entity \<^binding>\<open>pattern_term\<close> (Term_Style.parse -- term Proof_Context.mode_pattern)
                                        pretty_term_style
#> basic_entity \<^binding>\<open>pattern_prop\<close> (Term_Style.parse -- prop Proof_Context.mode_pattern)
                                        pretty_term_style

end\<close>

subsection \<open>Helper Isar Commands\<close>

ML_file \<open>library/tools/optional_translation.ML\<close>

subsection \<open>The Friendly Character\<close>

ML_file \<open>library/tools/the_friendly_character.ML\<close>

definition Friendly_Help :: \<open>text \<Rightarrow> bool\<close> where [iff]: \<open>Friendly_Help _ \<longleftrightarrow> True\<close>

term \<open>ERROR\<close>
lemma Friendly_Help_I: \<open>Friendly_Help ANY\<close> unfolding Friendly_Help_def ..

\<phi>reasoner_ML Friendly_Help 1000 (\<open>Friendly_Help _\<close>) = \<open>fn (ctxt,sequent) =>
 (if Config.get ctxt Phi_The_Friendly_Character.enable
  then let
        val _ $ (_ $ text) = Thm.major_prem_of sequent
        val pretty = Text_Encoding.decode_text_pretty ctxt text
       in Phi_The_Friendly_Character.info ctxt (fn _ => pretty) end
  else ();
  Seq.single (ctxt, @{thm Friendly_Help_I} RS sequent)
 )
\<close>


subsection \<open>Some very Early Reasoning\<close>

subsubsection \<open>Convert Generalized Elimination to Plain Conjunction\<close>

definition \<open>CONV_GE \<longleftrightarrow> False\<close>
definition \<open>CONV_GE_Ex \<equiv> Ex\<close>
definition \<open>CONV_GE_conj \<equiv> (\<and>)\<close>

lemma CONV_GE_phase_1:
  \<open>A \<longrightarrow> B \<longrightarrow> CONV_GE \<equiv> CONV_GE_conj A B \<longrightarrow> CONV_GE\<close>
  \<open>(\<forall>x. P x \<longrightarrow> CONV_GE) \<equiv> (CONV_GE_Ex P \<longrightarrow> CONV_GE)\<close>
  \<open>CONV_GE_Ex (\<lambda>x. CONV_GE_conj A (B' x)) \<equiv> CONV_GE_conj A (CONV_GE_Ex B')\<close>
  \<open>CONV_GE_Ex (\<lambda>x. CONV_GE_conj (A' x) B) \<equiv> CONV_GE_conj (CONV_GE_Ex A') B\<close>
  \<open>(Q \<longrightarrow> CONV_GE) \<longrightarrow> Q' \<equiv> Q \<or> Q'\<close>
  \<open>Q \<or> CONV_GE \<equiv> Q\<close>
  \<open>CONV_GE \<longrightarrow> CONV_GE \<equiv> True\<close>
  unfolding atomize_eq CONV_GE_Ex_def CONV_GE_def CONV_GE_conj_def by blast+

lemma CONV_GE_phase_2:
  \<open>Trueprop (CONV_GE_conj A B) \<equiv> (A &&& B)\<close>
  unfolding CONV_GE_conj_def atomize_conj .

lemma CONV_GE_phase_3:
  \<open>CONV_GE_conj A B \<equiv> A \<and> B\<close>
  unfolding CONV_GE_conj_def atomize_conj .

subsubsection \<open>Extract Elimination Rule - Part I\<close>

definition Extract_Elimination_Rule :: \<open>prop \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> prop\<close>
  where \<open>Extract_Elimination_Rule IN OUT_L OUT_R \<equiv> (PROP IN \<Longrightarrow> OUT_L \<Longrightarrow> OUT_R)\<close>

declare [[\<phi>reason_default_pattern \<open>PROP Extract_Elimination_Rule ?I _ _\<close>
                                \<Rightarrow> \<open>PROP Extract_Elimination_Rule ?I _ _\<close> (100) ]]

lemma Do_Extract_Elimination_Rule:
  \<open> PROP IN
\<Longrightarrow> PROP Extract_Elimination_Rule IN OUT_L OUT_R
\<Longrightarrow> \<r>Success
\<Longrightarrow> OUT_L \<Longrightarrow> (OUT_R \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Extract_Elimination_Rule_def
proof -
  assume IN: \<open>PROP IN\<close>
    and  RL: \<open>PROP IN \<Longrightarrow> OUT_L \<Longrightarrow> OUT_R\<close>
    and  OL: \<open>OUT_L\<close>
    and  OR: \<open>OUT_R \<Longrightarrow> C\<close>
  from OR[OF RL[OF IN OL]] show \<open>C\<close> .
qed

ML_file \<open>library/tools/elimination_rule.ML\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP Extract_Elimination_Rule (PROP P) OL OR
\<Longrightarrow> PROP Extract_Elimination_Rule (PROP P @action A) OL OR\<close>
  unfolding Extract_Elimination_Rule_def Action_Tag_def .

subsubsection \<open>Inhabitance Reasoning - Part I\<close>

text \<open>is by a set of General Elimination rules~\cite{elim_resolution} that extracts pure facts from
  an inhabited BI assertion, i.e., of a form like
  \[ \<open>Inhabited X \<Longrightarrow> (Pure1 \<Longrightarrow> Pure2 \<Longrightarrow> \<dots> \<Longrightarrow> C) \<Longrightarrow> \<dots> \<Longrightarrow> C\<close> \]
\<close>

ML_file \<open>library/tools/inhabited_rule.ML\<close>

declare (* disjE[\<phi>inhabitance_rule] *) (*I don't like divergence!*)
        conjE[\<phi>inhabitance_rule]
        set_mult_inhabited[\<phi>inhabitance_rule]
        set_plus_inhabited[\<phi>inhabitance_rule]

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited 1 \<Longrightarrow> C \<Longrightarrow> C\<close> .

(*TODO: Move this*)
end