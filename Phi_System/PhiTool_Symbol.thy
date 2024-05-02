theory PhiTool_Symbol
  imports Main
begin

section \<open>Symbol Identifier unique in Isabelle Runtime and Its Persistent Image\<close>

text \<open>When the runtime system uses N symbols in total, the length of the representation
      consumes at most 2 + log2(N) terms.
TODO: don't use nat but make a numeral so we don't need the mk_symbol wrapper\<close>

typedef symbol = \<open>UNIV::nat set\<close>
  morphisms Abs_symbol mk_symbol
  by auto

hide_const Abs_symbol

declare mk_symbol_inject[simplified, iff]

lemma mk_symbol_cong[cong]:
  \<open>mk_symbol A \<equiv> mk_symbol A\<close> .

ML_file \<open>PhiTool_Symbol_syntax.ML\<close>
ML_file \<open>PhiTool_Symbol.ML\<close>

nonterminal "\<phi>_symbol_"

syntax "_ID_SYMBOL_" :: \<open>id \<Rightarrow> \<phi>_symbol_\<close> ("_")
       "_LOG_EXPR_SYMBOL_" :: \<open>logic \<Rightarrow> \<phi>_symbol_\<close> ("SYMBOL'_VAR'(_')")
       "_MK_SYMBOL_" :: \<open>\<phi>_symbol_ \<Rightarrow> symbol\<close> ("SYMBOL'(_')")

ML \<open>
structure Phi_Tool_Symbol = struct
open Phi_Tool_Symbol

fun parse (Free (id, _)) = Phi_Tool_Symbol.mk_symbol id
  | parse tm = (@{print} tm; error "Expect an identifier.")

fun print tm =
  case Option.map Phi_Tool_Symbol.revert_symbol (try dest_synt_numeral tm)
    of SOME (SOME id) => Free(id, dummyT)
     | SOME NONE => error ("Phi_Tool_Symbol: " ^ string_of_int (dest_synt_numeral tm) ^ " is not a known symbol!")
     | NONE => tm

end
\<close>

parse_translation \<open>[
  (\<^syntax_const>\<open>_ID_SYMBOL_\<close>, (fn ctxt => fn [x] => Phi_Tool_Symbol.parse x)),
  (\<^syntax_const>\<open>_LOG_EXPR_SYMBOL_\<close>, (fn ctxt => fn [x] =>
        Const (\<^syntax_const>\<open>_constrain\<close>, dummyT) $ x $ Const(\<^type_syntax>\<open>symbol\<close>, dummyT))),
  (\<^syntax_const>\<open>_MK_SYMBOL_\<close>, (fn ctxt => fn [x] => x))
]\<close>


print_translation \<open>[
  (\<^const_syntax>\<open>mk_symbol\<close>, (fn ctxt => fn [tm] => Const (\<^syntax_const>\<open>_MK_SYMBOL_\<close>, dummyT) $ Phi_Tool_Symbol.print tm))
]\<close>

ML \<open>@{term \<open>SYMBOL(xxx)\<close>}\<close>


end