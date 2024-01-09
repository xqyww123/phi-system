signature TYPE_INFO_DB = sig

datatype entry_kind = KTYPE | KTYPES | KTERM | KTERMS | KTERMSS | KTHM | KTHMS
datatype entry = ETYPE of typ list | ETERM of term list | ETERMSS of term list list | ETHM of thm list
type properties = entry Symtab.table

val get_type_info : Context.generic -> string -> properties
val update_type_info : string -> (string * entry) list -> Context.generic -> Context.generic

exception BAD_TYPE
val add_property_kinds : (string * entry_kind) list -> unit

val get_types : string -> properties -> typ list option
val get_type  : string -> properties -> typ option
val get_termss: string -> properties -> term list list option
val get_terms : string -> properties -> term list option
val get_term  : string -> properties -> term option
val get_thms  : string -> properties -> thm list option
val get_thm   : string -> properties -> thm option

val type_property_attr_binding : binding

end

structure Type_Info_DB : TYPE_INFO_DB = struct

datatype entry_kind = KTYPE | KTYPES | KTERM | KTERMS | KTERMSS | KTHM | KTHMS
datatype entry = ETYPE of typ list | ETERM of term list | ETERMSS of term list list | ETHM of thm list

fun entry_eq' (ETYPE ts, ETYPE ts') = eq_list (op =) (ts, ts')
  | entry_eq' (ETERM ts, ETERM ts') = eq_list (op aconv) (ts, ts')
  | entry_eq' (ETERMSS ts, ETERMSS ts') = eq_list (eq_list (op aconv)) (ts, ts')
  | entry_eq' (ETHM ths, ETHM ths') = eq_list Thm.eq_thm (ths, ths')
fun entry_eq pair = pointer_eq pair orelse entry_eq' pair

type properties = entry Symtab.table

structure Data = Generic_Data (
  type T = properties Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (K (Symtab.merge entry_eq))
)

val kinds = Synchronized.var "Datatype_Info.kind" Symtab.empty
fun add_property_kinds new_kinds =
      Synchronized.change kinds (fold Symtab.update new_kinds)

fun get_type_info ctxt iname = the_default Symtab.empty (Symtab.lookup (Data.get ctxt) iname)
fun update_type_info iname property_values =
      Data.map (Symtab.map_default (iname, Symtab.empty) (fold Symtab.update property_values))

exception BAD_TYPE

fun parse_types (ETYPE tys) = tys
  | parse_types _ = raise BAD_TYPE
fun parse_type  (ETYPE [ty]) = ty
  | parse_type  _ = raise BAD_TYPE
fun parse_terms (ETERM tms) = tms
  | parse_terms _ = raise BAD_TYPE
fun parse_term (ETERM [tm]) = tm
  | parse_term  _ = raise BAD_TYPE
fun parse_termss (ETERMSS tms) = tms
  | parse_termss _ = raise BAD_TYPE
fun parse_thms (ETHM ths) = ths
  | parse_thms _ = raise BAD_TYPE
fun parse_thm  (ETHM [th]) = th
  | parse_thm   _ = raise BAD_TYPE

fun get_types name prop = Option.map parse_types (Symtab.lookup prop name)
fun get_type  name prop = Option.map parse_type  (Symtab.lookup prop name)
fun get_termss name prop = Option.map parse_termss (Symtab.lookup prop name)
fun get_terms name prop = Option.map parse_terms (Symtab.lookup prop name)
fun get_term  name prop = Option.map parse_term  (Symtab.lookup prop name)
fun get_thms  name prop = Option.map parse_thms  (Symtab.lookup prop name)
fun get_thm   name prop = Option.map parse_thm   (Symtab.lookup prop name)


(** Syntax **)

val ident = Parse.token
  (Parse.short_ident || Parse.long_ident || Parse.sym_ident || Parse.term_var ||
    Parse.type_ident || Parse.type_var || Parse.number);

val property_name =
  (ident || Parse.token Parse.keyword) :|-- (fn tok =>
    let val y = Token.content_of tok
     in Token.assign (SOME (Token.Literal (false, Markup.quasi_keyword))) tok;
        Scan.succeed y
    end)

fun array T = Scan.lift \<^keyword>\<open>[\<close> |-- Parse.enum' "," T --| Scan.lift \<^keyword>\<open>]\<close>
val property_synt = Scan.lift (property_name --| \<^keyword>\<open>=\<close>) :|-- (fn name =>
      let val keys = Synchronized.value kinds
       in (case Symtab.lookup keys name
             of NONE => Scan.fail_with (K (fn () => name ^ " is not a known property of types."))
              | SOME KTYPE  => Args.typ >> (ETYPE o single)
              | SOME KTYPES => Scan.repeat Args.typ >> ETYPE
              | SOME KTERM  => Args.term >> (ETERM o single)
              | SOME KTERMS => Scan.repeat Args.term >> ETERM
              | SOME KTERMSS => array (array Args.term) >> ETERMSS
              | SOME KTHM   => Attrib.thm  >> (ETHM o single)
              | SOME KTHMS  => Attrib.thms >> ETHM)
       >> pair name
      end)

val properties_synt = Parse.and_list' property_synt

val type_property_attr_binding = \<^binding>\<open>type_property\<close>
val _ = Theory.setup (
  Attrib.setup type_property_attr_binding (
    Args.type_name {proper=true, strict=true} -- properties_synt >> (fn (Tname, kvs) =>
      Thm.declaration_attribute (K (update_type_info Tname kvs))))
  "update properties of a type"
)

end
