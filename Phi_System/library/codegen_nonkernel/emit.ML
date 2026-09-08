structure Phi_CG_Emit = struct open Phi_CG_Emit

val export_code = Attrib.setup_config_string \<^binding>\<open>\<phi>export_code\<close> (K "")

structure Generated = Theory_Data (
  type T = Symtab.set; val empty = Symtab.empty; val merge = Symtab.merge (K true) )

(*Exports in the definition order of their constants over the theory and its ancestors, so that
  a callee is defined under its export name before any caller instantiates it; a definition can
  only mention constants defined before it, so this order is callee first.  A wrong order costs
  a duplicate function, never wrong code.*)
fun definition_order thy intrfs =
  let val defs = maps (fn thy' => rev (Phi_Procedure.procedures_of (Context.Theory thy'))) (rev (Theory.nodes_of thy))
      fun const_of th = (case Thm.concl_of th
                           of Const ("Pure.eq",_) $ LHS $ _ => try (Term.dest_Const_name o Term.head_of) LHS
                            | _ => NONE)
      val consts = map_filter const_of defs
      fun rank (_, tm) = (case try (Term.dest_Const_name o Term.head_of o Term.strip_abs_body) tm
                            of SOME c => find_index (fn c' => c' = c) consts
                             | NONE => ~1)
   in sort (int_ord o apply2 rank) (Symtab.dest intrfs) end

fun codegen' cfg oself intrfs procs thy ctxt =
  let val thyname = Context.theory_name {long=false} thy
      val path = Path.append (Resources.master_directory thy)
                             (Path.basic (Context.theory_name {long=false} thy))
              |> Path.expand |> Path.implode
   in codegen cfg oself path (definition_order thy intrfs) procs thyname ctxt
   |> tap (fn _ => if Symtab.is_empty intrfs
                   then warning ("No procedure of theory " ^ thyname ^ " is tagged [\<phi>export]; " ^
                                 "the transliteration is compiled but no " ^ #lang cfg ^ " file is written")
                   else writeln (#lang cfg ^ " program written to " ^ path ^ "." ^ #lang cfg))
  end

val _ = Theory.setup (Theory.at_end (fn thy =>
  let val name = Context.theory_name {long=false} thy
      val lang = Config.get_global thy export_code
   in if lang <> "" andalso not (Symtab.defined (Generated.get thy) name)
   then let val intrfs = Phi_Procedure.interfaces_of thy
            val procs  = rev (Phi_Procedure.procedures_of (Context.Theory thy))
     in SOME ( Context.theory_map (codegen' {lang=lang} false intrfs procs thy) thy
            |> Generated.map (Symtab.insert_set name) )
    end
   else NONE
  end))

end