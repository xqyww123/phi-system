signature SYNT_INDEX_PARAM = sig

datatype index = By_Num of int | By_Ident of string

val mk_index_step : index -> term
val mk_index : index list -> term
val raw_index_parser : index list parser
val index_term_parser : term context_parser

end

structure Synt_Index_Param : SYNT_INDEX_PARAM = struct

datatype index = By_Num of int | By_Ident of string

fun mk_index_step_N N = if N <= 0 then \<^term>\<open>0::nat\<close> else \<^term>\<open>Suc\<close> $ mk_index_step_N (N - 1)

fun mk_index_step (By_Num i) = mk_index_step_N i
  | mk_index_step (By_Ident s) = Phi_Syntax.mk_labelled s Term.dummy

(*may containing dummy term for schematic variable*)
val mk_index = HOLogic.mk_list \<^typ>\<open>element_index\<close> o map mk_index_step

val raw_index_parser = Parse.list1 (Parse.nat >> By_Num || Parse.short_ident >> By_Ident)

val check_pattern = Syntax.check_term o Proof_Context.set_mode Proof_Context.mode_pattern
val index_term_parser = Scan.peek (fn ctxt =>
      raw_index_parser >> (check_pattern (Context.proof_of ctxt) o mk_index))

end