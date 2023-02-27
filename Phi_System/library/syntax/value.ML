val phi_display_value_internal_name =
      Attrib.setup_config_bool \<^binding>\<open>\<phi>display_value_internal_name\<close> (K true)

val _ = Theory.setup (Sign.print_ast_translation (let open Ast in
  [(\<^const_syntax>\<open>Val\<close>, (fn ctxt => fn (args as [a,b]) =>
      if Config.get ctxt phi_display_value_internal_name
      then raise Match
      else Appl [Constant \<^syntax_const>\<open>val_syntax\<close>, b]))
  ]
end))