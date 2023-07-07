signature PHI_PROPERTY_DERIVER = sig



end

structure Phi_Property_Deriver = struct

type hints = term list
type priority = int
type deriver_name = string
type deriver = {
  priority: priority,
  name: deriver_name,
  dependends: deriver_name list,
  derive: hints -> generic_theory -> generic_theory
}

structure Derivers = Generic_Data (
  type T = deriver Name_Space.table
  val empty = Name_Space.empty_table "\<phi>deriver"
  val merge = Name_Space.merge_tables
)

structure Derivings = Table (type key = priority * deriver_name; val ord = prod_ord int_ord string_ord)

type const_name = string (*internal name*)
structure Deriver_Bindings = Generic_Data (
  type T = deriver_name Symtab.table (*key: const_name*)
  val empty = Symtab.empty
  val merge = Symtab.merge (op =)
)




end