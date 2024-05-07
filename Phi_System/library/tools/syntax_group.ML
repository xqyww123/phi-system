(* FILE: Phi_System/library/tools/Syntax_Group.ML
   AUTHOR: Qiyuan Xu

   Syntax translation command like that in Isar but improved by option flags controlling whether
   the translations are enabled.
*)

signature SYNTAX_GROUP = sig

val define_group : binding -> string -> (bool -> Context.generic -> Context.generic) -> theory -> theory
val check : theory -> xstring * Position.T -> string * (bool * Ast.ast Syntax.trrule list)
val add_trrules : string -> Ast.ast Syntax.trrule list -> theory -> theory
val is_enabled : theory -> string -> bool

val ML_sender : (bool -> Context.generic -> Context.generic) option Unsynchronized.ref

end

structure Syntax_Group : SYNTAX_GROUP = struct

structure Trrules = Theory_Data (
  type T = (bool * Ast.ast Syntax.trrule list) Name_Space.table
  val empty = Name_Space.empty_table "Groups of Syntactic Translation Rules"
  val merge = Name_Space.merge_tables
)

val Trrules_ops = {
  get_data = Trrules.get o Context.the_theory,
  put_data = Context.map_theory o Trrules.put
}

fun define_group_i name = Entity.define_global Trrules_ops name (false, [])

fun check thy = Name_Space.check (Context.Theory thy) (Trrules.get thy)

fun is_enabled thy name =
  fst (Name_Space.get (Trrules.get thy) name)

fun add_trrules name rules thy =
  let val flag' = Unsynchronized.ref false
   in thy
   |> Trrules.map (Name_Space.map_table_entry name (fn (flag,L) =>
        (flag' := flag ; (flag,rules @ L))))
   |> (if !flag' then Sign.add_trrules else Sign.del_trrules) rules
  end


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
      equals -- Args.$$$ "false" >> K (false, Sign.del_trrules) ||
      equals -- Args.$$$ "true" >> K (true, Sign.add_trrules) ||
      Scan.succeed (true, Sign.add_trrules)

fun define_group name description additional thy = thy
  |> define_group_i name
  |-> (fn iname =>
    Attrib.setup name (Scan.lift scan_value >> (fn (flag,f) =>
      Thm.declaration_attribute (fn _ => fn ctxt =>
      let val (_,rules) = Name_Space.get (Trrules.get (Context.theory_of ctxt)) iname
          fun mapping G = Context.mapping G (Proof_Context.background_theory G)
       in ctxt
       |> mapping (f rules #>
                   Trrules.map (Name_Space.map_table_entry iname (fn (_,L) => (flag,L))))
       |> additional flag
      end))) description)

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

val ML_sender_locker = Synchronized.var "Syntax_Group.ML_sender_locker" ()
val ML_sender = Unsynchronized.ref NONE

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>optional_translation_group\<close>
    "declare translation rules that can be enabled or disabled by configurations"
    ((Parse.binding -- Parse.cartouche -- Scan.option Parse.ML_source)
    >> (fn ((name, descr), src) => Toplevel.theory (fn thy =>
      let val additional = src
                |> Option.map (fn src => 
                    Synchronized.change_result ML_sender_locker (fn _ =>
                      let val _ = ML_Context.expression (Input.pos_of src)
                            (ML_Lex.read "Syntax_Group.ML_sender := SOME ((" @
                             ML_Lex.read_source src @
                             ML_Lex.read ") : bool -> Context.generic -> Context.generic)")
                            (Context.Theory thy)
                          val ret = the (!ML_sender)
                          val _ = ML_sender := NONE
                       in (ret, ())
                      end ))
       in define_group name descr (the_default Phi_Help.K_I additional) thy
      end )));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>optional_translations\<close> "add syntax translation rules"
    ((\<^keyword>\<open>(\<close> |-- Parse.name_position --| \<^keyword>\<open>)\<close>)
     -- Scan.repeat1 trans_line
  >> (fn (xname, raw_trrules) => Toplevel.theory (fn thy =>
    let val (iname, _) = check thy xname
        val trrules = read_trrules thy raw_trrules
     in add_trrules iname trrules thy
    end )));

val _ = Theory.setup (
  ML_Antiquotation.value \<^binding>\<open>syntax_group\<close>
    (Scan.peek (fn ctxt => Parse.name_position >> (fn name =>
        check (Context.theory_of ctxt) name
          |> fst
          |> ML_Syntax.print_string ))))

end