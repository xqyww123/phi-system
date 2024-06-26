signature PHI_TOOL_SYMBOL = sig

val mk_symbol : string -> term
val revert_symbol : int -> string option
val revert_symbol1: int -> string
val revert_symbol_term : term -> string option

end

structure Phi_Tool_Symbol : PHI_TOOL_SYMBOL = struct


val symbols = Synchronized.var "Phi_Tool_Symbol.symbols"
                {cnt = 0,
                 syms = Symtab.empty : term Symtab.table,
                 lookup = Inttab.empty : string Inttab.table}

fun mk_symbol_inner_rep identifier =
  Synchronized.change_result symbols (fn (data as {cnt, syms, lookup}) =>
    case Symtab.lookup syms identifier
      of SOME tm => (tm, data)
       | NONE =>
          let val tm = mk_numeral_nat cnt
           in (tm, {cnt = cnt+1, syms = Symtab.update_new (identifier, tm) syms,
                    lookup = Inttab.update_new (cnt, identifier) lookup}) end)

fun mk_symbol identifier = \<^const>\<open>mk_symbol\<close> $ mk_symbol_inner_rep identifier

fun revert_symbol id =
  Inttab.lookup (#lookup (Synchronized.value symbols)) id

fun revert_symbol1 id =
  case revert_symbol id
    of SOME x => x
     | NONE => error ("Phi_Tool_Symbol: bad symbol " ^ string_of_int id)


fun revert_symbol_term (Const(\<^const_name>\<open>mk_symbol\<close>, _) $ num) =
      SOME (revert_symbol1 (snd (HOLogic.dest_number num)))
  | revert_symbol_term _ = NONE


end