(* FILE: library/system/app_rules.ML
   AUTHOR: Qiyuan Xu

   The module manages application rules in the system, like name convention,
   parser, and overloading.
*)

signature PHI_APP_RULES = sig
  val app_rules : Proof.context -> (Facts.ref * Token.src list) -> thm list
  val declare_overloading : binding -> string (*comment*) -> local_theory -> string * local_theory
  val overload : thm -> (string * Position.T) -> Context.generic -> Context.generic
  val parser : (Facts.ref * Token.src list) parser
  val name_position : (string * Position.T) parser
end

structure Phi_App_Rules : PHI_APP_RULES = struct

fun suffix_fact _   (Facts.Fact thm) = Facts.Fact thm
  | suffix_fact suf (Facts.Named ((name,pos),int)) = Facts.Named ((suffix suf name,pos),int)

fun app_rules ctxt fact =
  Attrib.eval_thms ctxt [apfst (suffix_fact "_\<phi>app") fact]
  handle ERROR _ => Attrib.eval_thms ctxt [fact]

val declare_overloading = Named_Theorems.declare o Binding.suffix_name "_\<phi>app"
fun overload th (name,pos) ctx =
  Named_Theorems.add_thm (Named_Theorems.check (Context.proof_of ctx)
    (suffix "_\<phi>app" name, pos)) th ctx

local open Parse Scan in

val name =
  group (fn () => "name")
    (short_ident || long_ident || sym_ident || keyword || string)

val name_position = input name >> Input.source_content

val parser =
  $$$ "[" |-- attribs --| $$$ "]" >> pair (Facts.named "") ||
  (name_position -- Scan.option thm_sel >> Facts.Named) -- opt_attribs;

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>overloads} "declare procedure overloads"
    (and_list1 (binding -- Scan.optional Parse.text "") >>
        (fold (fn (b,s) => declare_overloading b s #> #2)))

end

end
