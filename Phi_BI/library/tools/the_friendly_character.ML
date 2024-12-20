signature PHI_THE_FRIENDLY_CHARACTER = sig

val enable : bool Config.T

val info : Proof.context -> (unit -> Pretty.T) -> unit

end

structure Phi_The_Friendly_Character : PHI_THE_FRIENDLY_CHARACTER = struct

val enable = Attrib.setup_config_bool \<^binding>\<open>\<phi>show_helps\<close> (K false)

fun info ctxt G =
  if Config.get ctxt enable
  then tracing (Pretty.string_of (Pretty.chunks [
          G (), Pretty.str "This is a kindly help from \<phi>-The-Friendly-Character. \
                           \Turn off it by \<open>declare [[\<phi>show_helps = false]]\<close>."
       ]))
  else ()

end