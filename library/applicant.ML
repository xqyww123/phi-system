signature NU_APPLICANT = sig
  val applicant_thms : Proof.context -> (xstring * Position.T) -> thm list
  val appliable_thms : Proof.context -> thm (*sequent*) -> (xstring * Position.T) -> thm list
  val parser : (xstring * Position.T) parser

  type overloading = {rule:thm, ordered_patterns: term list}
  exception OVERLOADING_DETERMINE_FAIL of thm (*sequent*)
                                        * overloading list (*given*)
                                        * thm list (*available candidates*)
  
  val overload : string -> overloading -> Context.generic -> Context.generic
  val del_overloading : string -> overloading -> Context.generic -> Context.generic

  val member_overloading: Context.generic -> string -> overloading -> bool
  val get_overloading: Context.generic -> string -> overloading list
  val clear_overloading: string -> Context.generic -> Context.generic

  val is_overloaded : Proof.context -> xstring * Position.T -> string option
  val check_overloading : Proof.context -> xstring * Position.T -> string
  val declare_overloading : binding -> xstring (*comment*) -> local_theory -> string * local_theory
  val appliable_overloading : Context.generic -> thm (*sequent*) -> overloading list (*applicants*) -> thm (*appliable rule*)

  val add_elements_extractor : term * (term -> term list) -> Context.generic -> Context.generic
  val get_elements_extractor : Context.generic -> term -> (term -> term list) list
  val list_elements_extractor: Context.generic -> (term * (term -> term list)) list
end

structure NuApplicant : NU_APPLICANT = struct

fun applicant_thms ctxt (name,pos) =
  Proof_Context.get_fact ctxt (Facts.Named ((suffix "_\<phi>app" name, pos), NONE))
  handle ERROR _ => Proof_Context.get_fact ctxt (Facts.Named ((name, pos), NONE))
  

(*overloads*)

type overloading = {rule:thm, ordered_patterns: term list}

fun ap_rule f ({rule,ordered_patterns}:overloading) : overloading =
  {rule= f rule, ordered_patterns=ordered_patterns}

fun mk_overloading ({rule,ordered_patterns}:overloading) : overloading =
  {rule= Thm.trim_context rule, ordered_patterns=ordered_patterns}

structure Overloadings = Generic_Data
(
  type T = overloading Item_Net.T Symtab.table;
  val empty: T = Symtab.empty;
  val merge : T * T -> T = Symtab.join (K Item_Net.merge);
);

val overloadings_item_net = Item_Net.init
      (fn (old1:overloading, old2:overloading) =>
            Thm.eq_thm_prop (#rule old1, #rule old2)
            andalso #ordered_patterns old1 = #ordered_patterns old2)
      (single o Thm.full_prop_of o #rule);

fun new_entry name =
  Overloadings.map (fn data =>
    if Symtab.defined data name
    then error ("Duplicate declaration of overloading: " ^ quote name)
    else Symtab.update (name, overloadings_item_net) data);

fun undeclared name = "Undeclared overloading " ^ quote name;

val defined_entry = Symtab.defined o Overloadings.get;

fun the_entry context name =
  (case Symtab.lookup (Overloadings.get context) name of
    NONE => error (undeclared name)
  | SOME entry => entry);

fun map_entry name f context =
  (the_entry context name; Overloadings.map (Symtab.map_entry name f) context);

val member_overloading = Item_Net.member oo the_entry;

fun get_overloading ctxt =
  rev o map (ap_rule (Thm.transfer'' ctxt)) o Item_Net.content o the_entry ctxt;

fun clear_overloading name = map_entry name (K overloadings_item_net);

fun overload name ovld = map_entry name (Item_Net.update (mk_overloading ovld));
fun del_overloading name = map_entry name o Item_Net.remove;


fun attrib_add_overloading name =
  Scan.lift \<^keyword>\<open>on\<close> |-- Args.term_pattern >> NuHelp.strip_binop_l \<^const_name>\<open>times\<close>
    >> (fn ordered_patterns =>
        Thm.declaration_attribute (fn rule =>
            overload name {rule=rule, ordered_patterns=ordered_patterns}))

fun attrib_del_overloading name =
  Scan.lift \<^keyword>\<open>on\<close> |-- Args.term_pattern >> NuHelp.strip_binop_l \<^const_name>\<open>times\<close>
    >> (fn ordered_patterns =>
        Thm.declaration_attribute (fn rule =>
            del_overloading name {rule=rule, ordered_patterns=ordered_patterns}))

fun is_overloaded ctxt (xname, pos) =
  let
    val context = Context.Proof ctxt;
    val fact_ref = Facts.Named ((xname, Position.none), NONE);
  in
    (case try (Proof_Context.get_fact_generic context) fact_ref of
      SOME (SOME name, _) => if defined_entry context name then SOME name else NONE
    | _ => NONE)
  end;

fun check_overloading ctxt (xname, pos) =
  let
    val context = Context.Proof ctxt;
    fun err () =
      let
        val space = Facts.space_of (Proof_Context.facts_of ctxt);
        val completion = Name_Space.completion context space (defined_entry context) (xname, pos);
      in error (undeclared xname ^ Position.here pos ^ Completion.markup_report [completion]) end;
  in
    case is_overloaded ctxt (xname, pos) of SOME name => name
      |  _ => err ()
  end;

fun declare_overloading binding descr lthy =
  let
    val name = Local_Theory.full_name lthy binding;
    val lthy' = lthy
      |> Local_Theory.background_theory (Context.theory_map (new_entry name))
      |> Local_Theory.map_contexts (K (Context.proof_map (new_entry name)))
      |> Local_Theory.add_thms_dynamic
              (binding, fn context => get_overloading context name |> map #rule)
  in (name, lthy') end;


val overload_attrib =
  Scan.peek (fn ctxt => Args.name_position >> check_overloading (Context.proof_of ctxt))
#-> (fn name =>
     Scan.lift Args.add |-- attrib_add_overloading name
  || Scan.lift Args.del |-- attrib_del_overloading name
  || attrib_add_overloading name);

val _ = Theory.setup (
    Attrib.setup \<^binding>\<open>\<phi>overload\<close> overload_attrib
    "add or delete overloadings"
  )




local open Parse Scan in

val parser = position (short_ident || long_ident || sym_ident || keyword || string)

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>overloads} "declare overloads of rules"
    (and_list1 (binding -- Scan.optional Parse.text "") >>
        (fold (fn (b,s) => declare_overloading b s #> #2)))

end





(* Appliable? *)

val extractor_item_net = Item_Net.init              
        (fn ((pat1,_), (pat2,_)) => pat1 = pat2) (single o fst)

structure Elements_Extractor = Generic_Data
(
  type T = (term * (term -> term list)) Item_Net.T;
  val empty: T = extractor_item_net;
  val merge : T * T -> T = Item_Net.merge;
);

val add_elements_extractor = Elements_Extractor.map o Item_Net.update
val list_elements_extractor = Item_Net.content o Elements_Extractor.get

fun get_elements_extractor ctxt term =
  let
    val thy = Context.theory_of ctxt
  in
    Item_Net.retrieve_matching (Elements_Extractor.get ctxt) term
      |> map_filter (fn (pat,extractor) =>
           if Pattern.matches thy (pat, term)
           then SOME extractor
           else NONE)
  end

exception OVERLOADING_DETERMINE_FAIL of thm (*sequent*)
                                      * overloading list (*given*)
                                      * thm list (*available candidates*)

fun appliable_overloading ctxt sequent (overloadings:overloading list) =
  let
    val thy = Context.theory_of ctxt
    val term = NuHelp.headgoal sequent
    val elementss = map (fn ex => ex term) (get_elements_extractor ctxt term)
    val candicates =
          maps (fn elements =>
            map_filter (fn ovld =>
              if eq_list (Pattern.matches thy)
                         (#ordered_patterns ovld, take (length (#ordered_patterns ovld)) elements)
              then SOME (#rule ovld)
              else NONE
            ) overloadings
          ) elementss
  in
    case candicates of [x] => x
       | _ => raise OVERLOADING_DETERMINE_FAIL (sequent, overloadings, candicates)
  end


fun appliable_thms ctxt sequent xname_pos =
  case is_overloaded ctxt xname_pos
    of SOME name =>
        [appliable_overloading (Context.Proof ctxt) sequent
            (get_overloading (Context.Proof ctxt) name)]
     | _ => applicant_thms ctxt xname_pos

end
