(* FILE: Phi_System/library/tools/optional_translation.ML
   AUTHOR: Qiyuan Xu

   Syntax translation command like that in Isar but improved by option flags controlling whether
   the translations are enabled.
*)

signature OPTIONAL_TRANSLATION = sig
end

structure Optional_Translation : OPTIONAL_TRANSLATION = struct

fun read_trrules thy raw_rules =
  let
    val ctxt = Proof_Context.init_global thy;
    val read_root =
      #1 o dest_Type o Proof_Context.read_type_name {proper = true, strict = false} ctxt;
  in
    raw_rules
    |> map (Syntax.map_trrule (fn (r, s) => Syntax_Phases.parse_ast_pattern ctxt (read_root r, s)))
  end

val equals = Parse.$$$ "=";

val scan_value =
      equals -- Args.$$$ "false" >> K Sign.del_trrules ||
      equals -- Args.$$$ "true" >> K Sign.add_trrules ||
      Scan.succeed Sign.add_trrules

fun translations ((b, args), text) thy =
  let
    val rules = read_trrules thy args
  in Attrib.setup b (Scan.lift scan_value >> (fn f =>
        Thm.declaration_attribute (K
            (Context.mapping (f rules) (Proof_Context.background_theory (f rules))))))
        text thy
  end

fun trans_arrow toks =
  ((\<^keyword>\<open>\<rightharpoonup>\<close> || \<^keyword>\<open>=>\<close>) >> K Syntax.Parse_Rule ||
    (\<^keyword>\<open>\<leftharpoondown>\<close> || \<^keyword>\<open><=\<close>) >> K Syntax.Print_Rule ||
    (\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) >> K Syntax.Parse_Print_Rule) toks;

val trans_pat =
  Scan.optional
    (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.inner_syntax Parse.name --| \<^keyword>\<open>)\<close>)) "logic"
    -- Parse.inner_syntax Parse.string;


val trans_line =
  trans_pat -- Parse.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>optional_translations\<close> "add syntax translation rules"
    ((\<^keyword>\<open>(\<close> |-- Parse.binding --| \<^keyword>\<open>)\<close>)
     -- Scan.repeat1 trans_line
     -- Parse.embedded >> (Toplevel.theory o translations));

end