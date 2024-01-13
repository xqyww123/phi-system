signature PLPR_STATISTICS = sig

(*the statistics is not shared or inherited among theories*)

val enable_collection : bool Config.T
val count : theory -> term -> unit
val utilization : theory -> (term * int Unsynchronized.ref) Net.net 
val reset : theory -> unit

end

structure PLPR_Statistics : PLPR_STATISTICS = struct

val enable_collection = Attrib.setup_config_bool \<^binding>\<open>\<phi>LPR_collect_statistics\<close> (K false)

val rule_usage : (term * int Unsynchronized.ref) Net.net Synchronized.var Symtab.table Synchronized.var
      = Synchronized.var "PLPR_Statistics.Rule_Usage.root" Symtab.empty

fun reset thy = Synchronized.change rule_usage (
      Symtab.update (Context.theory_long_name thy, Synchronized.var "PLPR_Statistics.Rule_Usage" Net.empty))

fun utilization thy =
  case Symtab.lookup (Synchronized.value rule_usage) (Context.theory_long_name thy)
    of NONE => Net.empty
     | SOME var => Synchronized.value var

fun count' var prop =
  let val prop = Phi_Help.beta_eta_contract_term prop
   in Synchronized.change var (fn net =>
      case Net.match_term net prop
        |> filter (fn (prop', _) => prop' aconv prop )
        of [] => Net.insert_term ((op aconv) o apply2 #1)
                                 (prop, (prop, Unsynchronized.ref 1)) net
         | L => ( List.app (fn (prop', ctr) =>
                    if prop' aconv prop
                    then ctr := !ctr + 1
                    else () ) L ;
                  net ))
  end

fun count thy =
  Synchronized.change_result rule_usage (fn bigtab =>
    let val thyname = Context.theory_long_name thy
     in case Symtab.lookup bigtab thyname
     of NONE => let val var = Synchronized.var "PLPR_Statistics.Rule_Usage" Net.empty
                 in (count' var, Symtab.update_new (thyname, var) bigtab)
                end
      | SOME var => (count' var, bigtab)
    end
  )

val _ = Theory.at_begin (fn thy => (reset thy; NONE))

end