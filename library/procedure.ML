signature NU_PROCEDURE = sig
  val defined : Context.generic -> string -> bool
  val declare : binding -> Context.generic -> Context.generic
  val define : xstring * Position.T -> thm -> Context.generic -> Context.generic
  val check : Context.generic -> xstring * Position.T -> thm list
end

structure NuProcedure : NU_PROCEDURE = struct
structure Data = Generic_Data
(
  type T = thm Item_Net.T Name_Space.table
  val empty: T = Name_Space.empty_table "\<nu>procedure"
  val extend = I
  val merge : T * T -> T = Name_Space.join_tables (K Item_Net.merge)
)

fun intern name f ctx = 
  let
    val tab = Data.get ctx
    val name = Name_Space.intern (Name_Space.space_of_table tab) name
  in
    f tab name ctx
  end
fun defined ctx name = intern name (K oo Name_Space.defined) ctx

val ops_processor = {get_data = Data.get, put_data = Data.put}
fun declare binding = intern (Binding.name_of binding) (fn tab => fn name =>
  if Name_Space.defined tab name
  then error ("Duplicate declaration of \<nu>procedure "^name)
  else Context.mapping (Entity.define_global ops_processor binding Thm.full_rules #> #2)
      (Entity.define ops_processor binding Thm.full_rules #> #2))
fun define name th ctx =
  let
    val tab = Data.get ctx
    val name = Name_Space.check ctx tab name |> #1
  in
    (Name_Space.map_table_entry name (Item_Net.update th) |> Data.map) ctx
  end
fun check ctx name = Name_Space.check ctx (Data.get ctx) name |> #2 |> Item_Net.content |> @{print}


end
