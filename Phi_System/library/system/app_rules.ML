(* FILE: library/system/app_rules.ML
   AUTHOR: Qiyuan Xu

   The module manages application rules in the system, like name convention,
   parser, and overloading.
*)

signature PHI_APP_RULES = sig
  val parse_fact : Proof.context -> Facts.ref -> Facts.ref
  val app_rules : Proof.context -> (Facts.ref * Token.src list) list -> thm list
  val declare_overloading : binding -> string (*comment*) -> local_theory -> string * local_theory
  val overload : thm -> (string * Position.T) -> Context.generic -> Context.generic
  val parser : (Facts.ref * Token.src list) parser
  val name_position : (string * Position.T) parser
  val symbol_position : (string * Position.T) parser
  val name_and_symbol_position : (string * Position.T) parser
end

structure Phi_App_Rules : PHI_APP_RULES = struct

fun parse_fact ctxt fact =
  let val names = Facts.space_of (Proof_Context.facts_of ctxt)
      fun declared xN = Name_Space.declared names (Name_Space.intern names xN)
      fun parse_name xN =
        if declared (prefix "local." xN) then prefix "local." xN
        else if declared (suffix "_\<phi>app" xN) then suffix "_\<phi>app" xN
        else xN
   in case fact of Facts.Fact term => Facts.Fact term
                 | Facts.Named ((name,pos),int) => Facts.Named ((parse_name name,pos),int)
  end

fun app_rules ctxt facts =
  Attrib.eval_thms ctxt (map (apfst (parse_fact ctxt)) facts)

val declare_overloading = Named_Theorems.declare o Binding.suffix_name "_\<phi>app"

fun overload th (name,pos) ctxt = (
  if Context_Position.reports_enabled_generic ctxt
  then Context_Position.reports_generic ctxt [(pos, Markup.dynamic_fact name)]
  else ();
  Named_Theorems.add_thm (Named_Theorems.check (Context.proof_of ctxt)
    (suffix "_\<phi>app" name, pos)) th ctxt
)

local open Parse Scan in

val id = group (fn () => "name") (short_ident || long_ident || keyword)

val id_position = input id >> Input.source_content

val name = group (fn () => "name")
    (short_ident || long_ident (* || sym_ident *) || keyword || string)

val name_position = input name >> Input.source_content

val symbol = group (fn () => "symbol") (sym_ident || keyword)
val symbol_position = input symbol >> Input.source_content

val name_and_symbol =
  group (fn () => "name") (short_ident || long_ident || sym_ident || keyword || string)
val name_and_symbol_position = input name_and_symbol >> Input.source_content

val attrib = token liberal_name ::: !!! args;
val xattribs = $$$ "[" |-- list attrib --| $$$ "]";
val xopt_attribs = Scan.optional xattribs [];

val parser =
  (* $$$ "[" |-- attribs --| $$$ "]" >> pair (Facts.named "") || *)
  \<^keyword>\<open>apply_rule\<close> |-- ((name_position -- Scan.option thm_sel >> Facts.Named) -- xopt_attribs) ||
  id_position >> (fn name => (Facts.Named (name, NONE), []))
  

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>overloads} "declare procedure overloads"
    (and_list1 (binding -- Scan.optional Parse.embedded "") >>
        (fold (fn (b,s) => declare_overloading b s #> #2)))

end

end
