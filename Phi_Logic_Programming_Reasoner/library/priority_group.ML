(* A reasoner group is a set of reasoners having close priorities and for an identical kind of problems. *)

signature REASONER_GROUP = sig

type name = string
type offset = int
type priority = int

type T = {
  base: int,
  range: int * int, (*left closed, right closed*)
  task: term, (*the predicate or any illustrative term that exhibits the sort of reasoning problems
                that the group of reasoners tackles*)
  comment: string
}

val define_global : binding -> T -> theory -> name * theory
val define : binding -> T -> local_theory -> name * local_theory
val check : Context.generic -> xstring * Position.T -> name * T
val pretty : Context.generic -> name * T -> Pretty.T
val space : Context.generic -> T Name_Space.table

datatype priority_syntax = Literal of int | Relative of (xstring * Position.T) * offset
val parser : priority_syntax parser
val parser_with_default : priority -> priority_syntax parser
val check_priority : Context.generic -> priority_syntax -> priority

end

structure Reasoner_Group : REASONER_GROUP = struct

type name = string
type offset = int
type priority = int

type T = {
  base: int,
  range: int * int, (*left closed, right closed*)
  task: term, (*the predicate or any illustrative term that exhibits the sort of reasoning problems
                that the group of reasoners tackles*)
  comment: string
}

structure Entries = Generic_Data (
  type T = T Name_Space.table
  val empty = Name_Space.empty_table "reasoner group"
  val merge = Name_Space.merge_tables
)

val data_ops = {
  get_data = Entries.get,
  put_data = Entries.put
}

val define_global = Entity.define_global data_ops
val define = Entity.define data_ops
fun check ctxt = Name_Space.check ctxt (Entries.get ctxt)
val space = Entries.get

datatype priority_syntax = Literal of int | Relative of (xstring * Position.T) * offset
local open Parse
val offset = (\<^keyword>\<open>+\<close> |-- int) || (Args.$$$ "-" |-- int >> (op ~)) || Scan.succeed 0
in val parser = (\<^keyword>\<open>%\<close> |-- name_position -- offset >> Relative) || (int >> Literal)
   fun parser_with_default default = parser || (Scan.succeed (Literal default) >> @{print})
end

fun check_priority _ (Literal i) = i
  | check_priority ctxt (Relative (name, offset)) =
      let val (name, group) = check ctxt name
          val ret = #base group + offset
          val _ = if fst (#range group) <= ret andalso ret <= snd (#range group) then ()
                  else error (let open Pretty
                                  val names = Name_Space.space_of_table (Entries.get ctxt)
                               in string_of (block (
                                     text "The given priority" @ [brk 1, str (string_of_int ret), brk 1] @
                                     text "is out of the convention of the group" @
                                     [Name_Space.pretty (Context.proof_of ctxt) names name]))
                              end)
       in ret
      end

fun pretty ctxt = let val names = Name_Space.space_of_table (Entries.get ctxt)
                      val ctxt' = Context.proof_of ctxt in
  fn (name, {base, range, task, comment}) => let open Pretty in
      block [chunks [block [Name_Space.pretty ctxt' names name,
                            brk 1, str "of priority between", brk 1,
                            str "[", str (string_of_int (fst range)), str ", ", str (string_of_int (snd range)), str "]",
                            brk 1, str "(default ", str (string_of_int base), str ")",
                            brk 1, str "for task", brk 1,
                            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt task],
                     para comment]]
  end
  end

datatype 'a constraints = Less of 'a | Greater of 'a | Included_In of 'a
val constraints_parser = Parse.and_list (Scan.repeat (
          (\<^keyword>\<open><\<close> |-- (Scan.repeat (Parse.name_position >> Less))) ||
          (\<^keyword>\<open>>\<close> |-- (Scan.repeat (Parse.name_position >> Greater))) ||
          (\<^keyword>\<open>in\<close> |-- (Scan.repeat (Parse.name_position >> Included_In)))
      )) >> (flat o flat)

fun check_constraints ctxt (Less x) = Less (check ctxt x)
  | check_constraints ctxt (Greater x) = Greater (check ctxt x)
  | check_constraints ctxt (Included_In x) = Included_In (check ctxt x)

fun verify_fail opr ctxt xname iname = let open Pretty in
    error (string_of (block (text "the priorities of group" @
                             [brk 1, Binding.pretty xname, brk 1, str "must be", brk 1, str opr, brk 1] @
                             text "the group" @
                             [brk 1, Name_Space.pretty ctxt (Name_Space.space_of_table (Entries.get (Context.Proof ctxt))) iname])))
  end

fun verify_constraints ctxt (xname, group) (Less (iname, group')) =
      if snd (#range group) < fst (#range group') then ()
      else verify_fail "less than" ctxt xname iname
  | verify_constraints ctxt (xname, group) (Greater (iname, group')) =
      if snd (#range group') < fst (#range group) then ()
      else verify_fail "greater than" ctxt xname iname
  | verify_constraints ctxt (xname, group) (Included_In (iname, group')) =
      if fst (#range group') <= fst (#range group) andalso snd (#range group) <= snd (#range group') then ()
      else verify_fail "included in" ctxt xname iname

fun verify ctxt (xname, group) constraints =
  if fst (#range group) <= #base group andalso #base group <= snd (#range group)
  then List.app (verify_constraints ctxt (xname, group)) constraints
  else error (let open Pretty in string_of (
                block (text "The base priority of group" @ [brk 1, Binding.pretty xname, brk 1] @
                       text "is not within its declared range" @
                       [brk 1, str "(", str (string_of_int (fst (#range group))), str ", ",
                        str (string_of_int (snd (#range group))), str ")"])
             )end)

val _ = Outer_Syntax.local_theory' \<^command_keyword>\<open>\<phi>reasoner_group\<close>
  "Define a \<phi>reason group. A \<phi>reason group is a set of reasoners having close priorities and \
  \for an identical kind of problems. It aims to provide an organized manage for priorities of reasoners, \
  \free user from unmanageable magic numbers."
  (let open Parse in and_list1 (Scan.repeat1 (
     binding --| \<^keyword>\<open>=\<close> --
        ((\<^keyword>\<open>(\<close> |--
            nat (*base*) --| \<^keyword>\<open>,\<close>
                         -- (\<^keyword>\<open>[\<close> |-- nat --| \<^keyword>\<open>,\<close> -- nat --| \<^keyword>\<open>]\<close>) (*priority interval*)
          --| \<^keyword>\<open>)\<close>) --
         (\<^keyword>\<open>for\<close> |-- prop (*task*)) --
         constraints_parser --
         document_source)
   )) >> flat end >> (fn data => fn int =>
   fold (fn (binding, ((((base, range), raw_task), constrains), comment)) => fn lthy =>
     let val task = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern lthy) raw_task
         val _ = if int then (
                    Document_Output.check_comments lthy (Input.source_explode comment) ;
                    Context_Position.reports lthy (Document_Output.document_reports comment)
                 ) else ()
         val group = {base=base, range=range, task=task, comment=Input.string_of comment}
         val _ = verify lthy (binding, group) (map (check_constraints (Context.Proof lthy)) constrains)
      in snd (define binding group lthy)
     end) data
  ))

val _ = Outer_Syntax.command \<^command_keyword>\<open>print_\<phi>reasoner_groups\<close>
  "Prints existing reasoner groups. Supports search by matching the task of the reasoner groups."
  (Scan.option Parse.prop >> (fn raw_pattern => Toplevel.keep (fn s =>
    let val ctxt = Toplevel.context_of s
        val thy = Proof_Context.theory_of ctxt
        val pattern = Option.map (Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)) raw_pattern
        val match = case pattern
                      of SOME pat => (fn group => Pattern.matches thy (pat, #task group))
                       | NONE => K true
        val groups = Name_Space.fold_table (fn (name, T) => fn L =>
                        if match T then pretty (Context.Proof ctxt) (name, T) :: L
                                   else L)
                      (Entries.get (Context.Proof ctxt)) []
     in case groups
     of [] => writeln "No reasoner group is found."
      | _ => Pretty.writeln (Pretty.chunks groups)
    end)))

end