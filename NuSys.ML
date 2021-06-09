(*  Title:      NuSys.ML
    Author:     Qiyuan Xu

The toplevel structure of the ν-system.

`begin_proc (name, [(register name, (abstractor, image))])`
    starts the block for procedure constrruction. The block is based on `notepad`. 

*)

signature NU_SYS = sig
  type state = Proof.state
  val show_proc_expression_attr : attribute context_parser
  (* val begin_proc : (binding * (string * (string * string)) list) -> state -> state
  val end_proc : state -> state *)
end

structure NuSys : NU_SYS = struct
  type state = Proof.state

  fun ctx_parser_wrap f (ctx,tok) = case f tok of (x,tok') => (x,(ctx,tok'))
  val ctx_parser_wrap : 'a parser -> 'a context_parser = ctx_parser_wrap
  val bool_opt_parser = ctx_parser_wrap
        (Parse.$$$ "=" |-- ((Args.$$$ "false" >> K false) || (Args.$$$ "true" >> K true)))

  fun map_theory_total f = Context.mapping f (Proof_Context.background_theory f)

  (* val show_proc_expression = Config.declare_bool ("show_proc_expression", \<^here>) (K false) *)
  local
  val omitted = [Syntax.Print_Rule (("logic", "_codeblock_ x"),
        ("logic", "CONST CodeBlock x exp"))]
  val detailed = [Syntax.Print_Rule (("logic", "_codeblock_exp_ x exp"),
        ("logic", "CONST CodeBlock x exp"))]
  in
  val show_proc_expression_attr = let
    fun attr opt _ ctx = ctx |> map_theory_total
      (Isar_Cmd.no_translations (if opt then omitted else detailed)
      #> Isar_Cmd.translations  (if opt then detailed else omitted))
    in bool_opt_parser >> (Thm.declaration_attribute o attr) end
  end
end
