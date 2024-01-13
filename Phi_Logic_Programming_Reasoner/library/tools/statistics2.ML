signature PLPR_STATISTICS = sig
include PLPR_STATISTICS

type group_name = string
val start_collecting_LPR_rules : group_name -> Context.generic -> Context.generic
val stop_collecting_LPR_rules  : group_name -> Context.generic -> Context.generic
val LPR_rules_of : Context.generic -> group_name -> term Net.net

val utilization_of_group : theory -> group_name -> (term * int) list

end

structure PLPR_Statistics : PLPR_STATISTICS = struct
open PLPR_Statistics

type group_name = string

structure Rule_Collection = Generic_Data (
  type T = term Net.net Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (K (Net.merge (op aconv)))
)

fun LPR_rules_of ctxt group_name =
  the_default Net.empty (Symtab.lookup (Rule_Collection.get ctxt) group_name)

val rule_pass_pattern = Var(("_", 0), TVar(("_",0),[]))
fun start_collecting_LPR_rules group_name =
  Phi_Reasoner.add_pass (Const("PLPR_Statistics", dummyT) $ Const(group_name, dummyT), rule_pass_pattern,
      fn _ => fn (rules, prio, patterns, guard, ctxt) =>
          let val rules = map Phi_Help.beta_eta_contract rules
           in (rules, prio, patterns, guard,
              Rule_Collection.map (Symtab.map_default (group_name, Net.empty)
                  (fold (fn rule => let val prop = Thm.prop_of rule
                                     in Net.insert_term_safe (op aconv) (prop, prop)
                                    end) rules))
                  ctxt )
          end )

fun stop_collecting_LPR_rules group_name =
  Phi_Reasoner.del_pass (Const("PLPR_Statistics", dummyT) $ Const(group_name, dummyT), rule_pass_pattern)

fun utilization_of_group thy name =
  let val all_utilization = utilization thy
   in Net.content (LPR_rules_of (Context.Theory thy) name)
   |> map (fn prop =>
         case find_first (fn (prop', _) => prop' aconv prop)
                            (Net.match_term all_utilization prop)
           of SOME (_, cnt) => (prop, !cnt)
            | NONE => (prop, 0)
      )
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>collect_LPR_rules\<close> (
    Scan.lift (Parse.name -- ( Args.$$$ "start" >> K true
                            || Args.$$$ "stop"  >> K false )) >> (fn (name, start) =>
    Thm.declaration_attribute (fn _ =>
        if start then start_collecting_LPR_rules name
                 else stop_collecting_LPR_rules  name))
) "start or stop collecting LPR rule of the given group.")

end