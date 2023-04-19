signature PHI_VARIABLE = sig

  val external_name_of : Proof.context -> string -> xstring option
  val bind_variable : string * xstring -> Proof.context -> Proof.context

end

structure Phi_Variable : PHI_VARIABLE = struct

structure Variables = Proof_Data (
  type T = string Symtab.table (*key: internal names of the varname term, value: external name*)
  val init = K Symtab.empty
)

val external_name_of = Symtab.lookup o Variables.get
val bind_variable = Variables.map o Symtab.update_new

end