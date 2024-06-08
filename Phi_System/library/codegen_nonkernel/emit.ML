structure Phi_CG_Emit = struct open Phi_CG_Emit

val export_code = Attrib.setup_config_string \<^binding>\<open>\<phi>export_code\<close> (K "")

structure Generated = Theory_Data (
  type T = Symtab.set; val empty = Symtab.empty; val merge = Symtab.merge (K true) )

fun codegen' cfg oself intrfs procs thy ctxt =
  let val thyname = Context.theory_name {long=false} thy
      val path = Path.append (Resources.master_directory thy)
                             (Path.basic (Context.theory_name {long=false} thy))
              |> Path.expand |> Path.implode
   in codegen cfg oself path intrfs procs thyname ctxt
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