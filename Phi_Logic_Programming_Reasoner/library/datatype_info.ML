signature TYPE_INFO_DB = sig

datatype entry_kind = KTYPE | KTYPES | KTERM | KTERMS | KTHM | KTHMS
datatype entry = ETYPE of typ list | ETERM of term list | ETHM of thm list
type properties = entry Symtab.table

val get_type_info : Context.generic -> string -> properties
val update_type_info : string -> string * entry -> Context.generic -> Context.generic

exception BAD_TYPE

val get_types : properties -> string -> typ list option
val get_type  : properties -> string -> typ option
val get_terms : properties -> string -> term list option
val get_term  : properties -> string -> term option
val get_thms  : properties -> string -> thm list option
val get_thm   : properties -> string -> thm option

end

structure Type_Info_DB : TYPE_INFO_DB = struct

datatype entry_kind = KTYPE | KTYPES | KTERM | KTERMS | KTHM | KTHMS
datatype entry = ETYPE of typ list | ETERM of term list | ETHM of thm list

fun entry_eq' (ETYPE ts, ETYPE ts') = eq_list (op =) (ts, ts')
  | entry_eq' (ETERM ts, ETERM ts') = eq_list (op aconv) (ts, ts')
  | entry_eq' (ETHM ths, ETHM ths') = eq_list Thm.eq_thm (ths, ths')
fun entry_eq pair = pointer_eq pair orelse entry_eq' pair

type properties = entry Symtab.table

structure Data = Generic_Data (
  type T = properties Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (K (Symtab.merge entry_eq))
)

val kinds = Synchronized.var "Datatype_Info.kind" Symtab.empty

fun get_type_info ctxt iname = the_default Symtab.empty (Symtab.lookup (Data.get ctxt) iname)
fun update_type_info iname property_value =
      Data.map (Symtab.map_default (iname, Symtab.empty) (Symtab.update property_value))

exception BAD_TYPE

fun parse_types (ETYPE tys) = tys
  | parse_types _ = raise BAD_TYPE
fun parse_type  (ETYPE [ty]) = ty
  | parse_type  _ = raise BAD_TYPE
fun parse_terms (ETERM tms) = tms
  | parse_terms _ = raise BAD_TYPE
fun parse_term (ETERM [tm]) = tm
  | parse_term  _ = raise BAD_TYPE
fun parse_thms (ETHM ths) = ths
  | parse_thms _ = raise BAD_TYPE
fun parse_thm  (ETHM [th]) = th
  | parse_thm   _ = raise BAD_TYPE

val get_types = Option.map parse_types oo Symtab.lookup
val get_type  = Option.map parse_type  oo Symtab.lookup
val get_terms = Option.map parse_terms oo Symtab.lookup
val get_term  = Option.map parse_term  oo Symtab.lookup
val get_thms  = Option.map parse_thms  oo Symtab.lookup
val get_thm   = Option.map parse_thm   oo Symtab.lookup


end
