signature PLPR_STATISTICS = sig


(* collecting usage of LPR reaosners  *)
(*the statistics is not shared or inherited among theories*)

type group_name = string

val count : Context.generic -> term -> unit
val utilization : theory -> group_name -> (term * int Unsynchronized.ref) Net.net
val utilization_in_all_theories : group_name -> (term * int Unsynchronized.ref) Net.net
val reset_utilization_statistics : theory -> unit
val reset_utilization_statistics_all : unit -> unit

(* collecting satatistics (time, LPR steps) of subgoals *)

type num_of_operator = int
type LPR_steps = int
type subgoal_counter = thm -> num_of_operator option

val collecting_subgoal_statistics : bool Config.T
val count_subgoal : Context.generic -> thm -> (int * Time.time -> unit) option
val reset_subgoal_statistics : unit -> unit
val get_subgoal_statistics : unit -> (subgoal_counter * (int * int * Time.time) list) list
val add_subgoal_counter : term * subgoal_counter -> unit

(* Common *)
val reset_all : unit -> unit

end

structure PLPR_Statistics : PLPR_STATISTICS = struct

(* collecting usage of LPR reaosners  *)

type group_name = string

structure Opening_Statistic_Groups = Generic_Data (
  type T = Symtab.set
  val empty = Symtab.empty
  val merge = Symtab.merge (op =)
)

val rule_usage : (term * int Unsynchronized.ref) Net.net Symtab.table Synchronized.var Symtab.table Synchronized.var
      = Synchronized.var "PLPR_Statistics.Rule_Usage.root" Symtab.empty

fun reset_utilization_statistics thy = Synchronized.change rule_usage (
      Symtab.update (Context.theory_long_name thy, Synchronized.var "PLPR_Statistics.Rule_Usage" Symtab.empty))

fun reset_utilization_statistics_all () =
  Synchronized.change rule_usage (K Symtab.empty)

fun utilization thy group =
  case Symtab.lookup (Synchronized.value rule_usage) (Context.theory_long_name thy)
    of NONE => Net.empty
     | SOME var => the_default Net.empty (Symtab.lookup (Synchronized.value var) group)

(*
fun utilization_in_all_theories group =
  Symtab.fold (fn (_, statistics) => fn ret =>
                  case Symtab.lookup (Synchronized.value statistics) group
                    of SOME net => fold (fn (key, num) => Termtab.map_default (key, 0) (fn n => n + !num))
                                        (Net.content net)
                                        ret
                     | NONE => ret)
              (Synchronized.value rule_usage)
              Termtab.empty*)

fun utilization_in_all_theories group =
  Symtab.fold (fn (_, statistics) => fn ret =>
                  case Symtab.lookup (Synchronized.value statistics) group
                    of SOME net => fold (fn (key, num) => fn net =>
                                            case Net.match_term net key
                                              |> filter (fn (term, _) => term aconv key)
                                              of [] => Net.insert_term (op aconv o apply2 #1)
                                                                       (key, (key, Unsynchronized.ref (!num))) net
                                               | L => (List.app (fn (_, n) => n := !n + !num) L; net))
                                        (Net.content net)
                                        ret
                     | NONE => ret)
              (Synchronized.value rule_usage)
              Net.empty

fun count' var groups prop =
  let val prop = Phi_Help.beta_eta_contract_term prop
   in Synchronized.change var (fold (fn group =>
        Symtab.map_default (group, Net.empty) (fn net =>
      case Net.match_term net prop
        |> filter (fn (prop', _) => prop' aconv prop )
        of [] => Net.insert_term ((op aconv) o apply2 #1)
                                 (prop, (prop, Unsynchronized.ref 1)) net
         | L => ( List.app (fn (prop', ctr) =>
                    if prop' aconv prop
                    then ctr := !ctr + 1
                    else () ) L ;
                  net )) ) groups)
  end

fun count ctxt =
  let val thyname = Context.theory_long_name (Context.theory_of ctxt)
      val opening_groups = Opening_Statistic_Groups.get ctxt
                        |> Symtab.keys
   in if null opening_groups
      then K ()
      else Synchronized.change_result rule_usage (fn bigtab =>
              case Symtab.lookup bigtab thyname
                of NONE => let val var = Synchronized.var "PLPR_Statistics.Rule_Usage" Symtab.empty
                           in (count' var opening_groups, Symtab.update_new (thyname, var) bigtab)
                          end
                 | SOME var => (count' var opening_groups, bigtab))
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>LPR_collect_statistics\<close> (
    Scan.lift (Parse.name
            -- ( Args.$$$ "start" >> K true
              || Args.$$$ "stop"  >> K false )) >> (fn (name, start) =>
    Thm.declaration_attribute (fn _ =>
        Opening_Statistic_Groups.map (
          if start then Symtab.insert_set name
                   else Symtab.remove_set name ) ))
) "start or stop collecting LPR rule of the indicated group.")



(* collecting satatistics (time, LPR steps) of subgoals *)

val collecting_subgoal_statistics = Attrib.setup_config_bool \<^binding>\<open>collecting_subgoal_statistics\<close> (K false)

type num_of_operator = int
type LPR_steps = int
type subgoal_counter = thm -> num_of_operator option
val subgoal_statistics : (subgoal_counter * (num_of_operator * LPR_steps * Time.time) list Synchronized.var)
                              Net.net Synchronized.var
      = Synchronized.var "\<phi>.subgoal_statistics" Net.empty

fun count_subgoal ctxt =
  if Config.get_generic ctxt collecting_subgoal_statistics
  then fn st =>
    if Thm.no_prems st
    then NONE
    else case Net.match_term (Synchronized.value subgoal_statistics) (Thm.major_prem_of st)
           |> map_filter (fn (collector, data_set) => Option.map (rpair data_set) (collector st))
      of [] => NONE
       | L => SOME (fn (steps, time) =>
                List.app (fn (size, data_set) =>
                    Synchronized.change data_set (fn LL => (size, steps, time) :: LL)) L)
  else K NONE

fun reset_subgoal_statistics () =
  List.app (fn (_, data_set) => Synchronized.change data_set (K []))
           (Net.content (Synchronized.value subgoal_statistics))

fun get_subgoal_statistics () =
      Synchronized.value subgoal_statistics
        |> Net.content
        |> map (apsnd Synchronized.value)

fun add_subgoal_counter (pattern, subgoal_counter) =
  Synchronized.change subgoal_statistics (
    Net.insert_term (pointer_eq o apply2 fst)
                    (pattern, (subgoal_counter, Synchronized.var "\<phi>.subgoal_statistic" [])) )

val _ = Theory.at_begin (fn thy => (reset_utilization_statistics thy; NONE))

fun reset_all () = (reset_utilization_statistics_all () ;
                    reset_subgoal_statistics ())


end