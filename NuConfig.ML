signature NU_CONFIG = sig
  val show_codeblock_expression : bool Config.T
end
structure NuConfig : NU_CONFIG = struct
val show_codeblock_expression =
  Config.declare_bool ("show_codeblock_expression", @{here}) (K false)
end
