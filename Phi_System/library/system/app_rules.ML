(* FILE: library/system/app_rules.ML
   AUTHOR: Authors of Submission 96

   The module manages application rules in the system, like name convention,
   parser, and overloading.
*)

signature PHI_APP_RULES = sig

  type priority = int

  val get_overloadings : Proof.context -> string -> thm list
  val clear_overloadings : string -> Context.generic -> Context.generic
  val check_overloading : Context.generic -> xstring * Position.T -> string
  val declare_overloading : binding -> local_theory -> string * local_theory
  val declare_overloading_global : binding -> theory -> string * theory
  val overload : priority * thm -> (string * Position.T) -> Context.generic -> Context.generic
  val del_overloading : string -> thm -> Context.generic -> Context.generic

  val parse_fact : Proof.context -> Facts.ref -> Facts.ref
  val app_rules : Proof.context -> (Facts.ref * Token.src list) list -> thm list
  val parser : (Facts.ref * Token.src list) parser
  val name_pos_of_rule_ref : Facts.ref * Token.src list -> xstring * Position.T
  val name_position : (string * Position.T) parser
  val symbol_position : (string * Position.T) parser
  val name_and_symbol_position : (string * Position.T) parser

(* DO NOT REMOVE
  type ovld_resolver = Proof.context * thm -> thm list

  val resolve_ad_hoc_overloadings : Proof.context * thm -> string -> thm list
  val add_ovld_resolver : string * priority * ovld_resolver -> Context.generic -> Context.generic
*)

end

structure Phi_App_Rules : PHI_APP_RULES = struct

type priority = int

(* DO NOT REMOVE
type ovld_resolver = Proof.context * thm -> thm list

structure Adhoc_Ovld_Resolvers = Generic_Data (
  type T = ovld_resolver Inttab.table Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (fn _ => Inttab.join (fn _ => fn (a,b) =>
                  if pointer_eq (a,b) then a else (fn s => a s @ b s)))
)

fun resolve_ad_hoc_overloadings stat name =
  case Symtab.lookup (Adhoc_Ovld_Resolvers.get (Context.Proof (fst stat))) name
    of SOME itab =>
          these (Inttab.get_first (fn (_, resolver) =>
                    case resolver stat of [] => NONE
                                        | L => SOME L ) itab)
     | _ => []

fun add_ovld_resolver (name, prio, resolver) =
  Adhoc_Ovld_Resolvers.map (Symtab.map_default (name, Inttab.empty)
      (fn itab => if Inttab.defined itab prio
                  then Inttab.map_entry prio (fn old => fn s => resolver s @ old s) itab
                  else Inttab.update_new (prio, resolver) itab ))
*)

(*val adhoc_ovld_ops =*)

(* context data *)

fun ovld_equiv thy = eq_pair (op =) (Thm.equiv_thm thy)

structure Overloadings = Generic_Data (
  type T = (priority * thm) iNet.net Name_Space.table
  val empty = Name_Space.empty_table "overloaded operation"
  val merge = Name_Space.join_tables (K (iNet.merge (eq_pair (op =) pointer_eq)))
)

val ovld_ops = {
  get_data = Overloadings.get,
  put_data = Overloadings.put
}

fun new_entry_local bind =
  Entity.define ovld_ops bind iNet.empty

fun new_entry_global bind = 
  Entity.define_global ovld_ops bind iNet.empty

(*fun new_entry name =
  Overloadings.map (fn data =>
    if Symtab.defined data name
    then error ("Duplicate declaration of overloaded operation: " ^ quote name)
    else Symtab.update (name, iNet.empty) data);*)

fun undeclared name = "Undeclared overloaded operation " ^ quote name;

val defined_entry = Name_Space.defined o Overloadings.get;

fun the_entry context name =
  (case Name_Space.lookup (Overloadings.get context) name of
    NONE => error (undeclared name)
  | SOME entry => entry);

fun map_entry name f context =
  (the_entry context name; Overloadings.map (Name_Space.map_table_entry name f) context);


(* maintain content *)

fun content context = the_entry context
                   #> iNet.content
                   #> sort (int_ord o apply2 ((op ~) o fst))
                   #> map (Thm.transfer'' context o snd)

val get_overloadings  = content o Context.Proof;

fun clear_overloadings name = map_entry name (K iNet.empty)

fun add_overloading name (priority,thm) ctxt =
  let val thm = Thm.trim_context (Phi_Help.beta_eta_contract thm)
   in map_entry name
        (iNet.insert_term_safe (ovld_equiv (Context.theory_of ctxt))
                               (Thm.prop_of thm, (priority, thm)))
        ctxt
  end

fun del_overloading name thm ctxt =
  let val thm = Phi_Help.beta_eta_contract thm
   in map_entry name
        (iNet.delete_term_safe (fn (tha, (_, thb)) => Thm.equiv_thm (Context.theory_of ctxt) (tha,thb))
                               (Thm.prop_of thm, thm))
        ctxt
  end


fun declare_overloading binding lthy =
  let val binding' = Binding.suffix_name "_\<phi>app" binding
      val name = Local_Theory.full_name lthy binding
      val lthy' = lthy
        |> new_entry_local binding |> snd
        |> Local_Theory.add_thms_dynamic (binding', fn context => content context name)
   in (name, lthy')
  end

fun declare_overloading_global binding gthy =
  let val binding' = Binding.suffix_name "_\<phi>app" binding
      val name = Sign.full_name gthy binding
      val gthy' = gthy
        |> new_entry_global binding |> snd
        |> Global_Theory.add_thms_dynamic (binding', fn context => content context name)
   in (name, gthy')
  end

fun check_overloading ctxt =
  let val overloadings = Overloadings.get ctxt
   in fst o Name_Space.check ctxt overloadings 
  end

fun overload th (name,pos) ctxt = (
  if Context_Position.reports_enabled_generic ctxt
  then Context_Position.reports_generic ctxt [(pos, Markup.dynamic_fact name)]
  else ();
  add_overloading (check_overloading ctxt (name, pos)) th ctxt
)




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

fun name_pos_of_rule_ref (Facts.Named (name_pos, _), _) = name_pos

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>overloads} "declare procedure overloads"
    (and_list1 binding >>
        (fold (fn b => declare_overloading b #> snd)))

fun attr_add name =
      (Scan.optional Parse.nat 0) >> (fn prio =>
        Thm.declaration_attribute (fn thm => add_overloading name (prio, thm)))

val del = Thm.declaration_attribute o del_overloading
fun attr name =
     Args.$$$ "add" |-- attr_add name
  || Args.$$$ "del" |-- Scan.succeed (del name)
  || attr_add name

val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>overload\<close> (
  Scan.lift (name_and_symbol_position) :|-- (fn name_pos => Scan.peek (fn ctxt =>
    let val iname = check_overloading ctxt name_pos
     in attr iname
    end))
) "overload onto the given symbol")

val _ = Theory.setup
  (ML_Antiquotation.inline_embedded \<^binding>\<open>\<phi>overloading\<close>
    (Args.context -- Scan.lift Parse.embedded_position >>
      (fn (ctxt, name) => ML_Syntax.print_string (check_overloading (Context.Proof ctxt) name))));


end

end
