val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>type\<close> (Scan.succeed (
  Thm.rule_attribute [] (fn _ => fn thm =>
    case get_first (fn rule => SOME (thm RS rule)
                                  handle THM _ => NONE) @{thms declare_phi_Type}
      of SOME thm' => thm'
       | NONE => raise THM ("Not a \<phi>-type definition.\n\
                            \A \<phi>-type definition must be a lambda abstraction, of form\n\
                            \  T p\<^sub>1 \<dots> p\<^sub>n = (\<lambda>x. BI-assertion)\n\
                            \The lambda abstraction is compulsory and should not be expanded.",
                            0, [thm]))
)) "define a \<phi>-type")