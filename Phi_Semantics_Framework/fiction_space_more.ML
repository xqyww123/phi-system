structure Fiction_Space_Argument : GENERIC_RESOURCE_SPACE_ARGUMENT = struct

structure Loc = Fiction_Locale_Argument

val additional_data' = \<^typ>\<open>RES_N \<Rightarrow> RES\<close>
val prepare_space_name_binding = Binding.suffix_name "_fic"
val mandatory_path = "FIC"

fun prepare_map_rewr field_B field domain (Expression.Positional TMS, rw) =
      (Expression.Positional (TMS @ [SOME field]), rw)
  | prepare_map_rewr field_B field domain (Expression.Named TMS, rw) =
      (Expression.Named (("Fic", field) :: TMS), rw)

fun field_typ_of tm =
  case type_of tm of \<^Type>\<open>fun T _\<close> => \<^Type>\<open>Resource_Space.kind \<^Type>\<open>FIC_N\<close> \<^Type>\<open>FIC\<close> T\<close>
                   | TY => raise TYPE ("Internal Bug #qcujm903", [TY], [])

fun space_locale_exp fields =
  (Expression.Positional ([SOME \<^term>\<open>FIC.DOMAIN\<close>, SOME \<^term>\<open>INTERPRET\<close>]
      @ map SOME fields
      @ [SOME \<^term>\<open>TYPE(FIC_N)\<close>, SOME \<^term>\<open>TYPE(FIC)\<close>]), [])

end

structure Fiction_Space = Generic_Resource_Space(Fiction_Space_Argument)