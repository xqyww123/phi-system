signature PREMISES_ATTRIBUTE = sig

val register_attribute : Reasoner_Group.group * bool (*mandatory*) * term (*pattern*) * attribute list * Position.T
                      -> Context.generic -> Context.generic
      (*if an attribute is mandatory, it is always applied prior before user's attribute.
        By contrast, if it is not, it is for the default case when user does not bind the
        premise and is not applied once user bind the premises.
        '_' is a place holder and not considered as a binding.*)
val register_attribute_lthy : Reasoner_Group.group * bool * term * attribute list * Position.T -> local_theory -> local_theory

(* If multiple attributes match the given term, returns the concatenation of the
  attributes in the order of declaration. *)
val attribute_of : Context.generic -> bool (*involve-default?*) -> term -> attribute list

end

structure Premises_Attribute : PREMISES_ATTRIBUTE = struct

val trace_premise_attrs = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_premise_attrs\<close> (K false)

val data_eq = (op = o apply2 #1)

structure Data = Generic_Data (
  (*It relies on that the serial is incremental with time*)
  type T = (Reasoner_Group.group * bool * term (*pattern*) * attribute list (*TODO: change this to Token.T!!*) * Position.T) Net.net
  val empty = Net.empty
  val merge = Net.merge data_eq
)

fun register_attribute attr = Data.map (Net.insert_term data_eq (#3 attr, attr))

fun register_attribute_lthy (i,mandatory,pat,attr,pos) =
  Local_Theory.declaration {syntax=false, pervasive=false, pos=Position.none}
    (fn m => register_attribute (i,mandatory, Morphism.term m pat, attr, pos))

fun attribute_of ctxt =
  let val data = Data.get ctxt
      val matches = PLPR_Pattern.matches (Context.theory_of ctxt) (K true)
      val trace = Config.get_generic ctxt trace_premise_attrs
   in fn default => fn term =>
  let val (bvs, concl) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.beta_eta_contract_term term)
   in Net.match_term data concl
   |> map_filter (fn (i,mandatory,pat,attr,pos) =>
         if (default orelse mandatory)
         andalso matches bvs (pat,concl)
         then SOME (i, attr, pos) else NONE)
   |> sort (int_ord o apply2 (#1 o #1))
   |> (fn [] => []
        | L => ((if trace then let open Pretty in
                    tracing (string_of (chunks [
                        block ( text "applying default attributes"
                              @ [brk 1] 
                              @ maps (fn (_, _, pos) => Pretty.here pos @ [brk 1]) L
                              @ text "on local premise"),
                        Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt concl]))
                  end
                 else ()) ;
                maps #2 L))
  end end

val prop_patterns = Scan.peek (fn generic =>
  let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of generic)
   in Scan.repeat (Args.named_term (fn str =>
        let val term = Syntax.read_prop ctxt str
            val ctxt' = Proof_Context.augment term ctxt
         in singleton (Variable.export_terms ctxt' ctxt) term
        end))
  end)

fun chk_attribute ctxt = map (Context.cases Attrib.attribute_global Attrib.attribute ctxt)

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>premise_attribute\<close> (
    Scan.lift (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) --
    Attrib.attribs -- Scan.lift (Parse.position \<^keyword>\<open>for\<close>) -- prop_patterns --
    Scan.lift (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>)
    >> (fn ((((mandatory, attr), (_, pos)), pats), group') => Thm.declaration_attribute (fn _ => fn ctxt =>
          let val group = Reasoner_Group.check_group false ctxt group'
           in fold (fn pat => register_attribute (group, mandatory, pat, chk_attribute ctxt attr, pos))
                            pats ctxt
          end))
    ) "register attributes applying on premises matching the given pattern, for those premises\
      \ in \<phi>-programming block."
#>Attrib.setup \<^binding>\<open>\<phi>premise_attribute_ML\<close> (
    Scan.lift (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) --
    phi_system_ML_attribute_parser -- Scan.lift (Parse.position \<^keyword>\<open>for\<close>) -- prop_patterns --
    Scan.lift (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>)
    >> (fn ((((mandatory, attr), (_, pos)), pats), group') => Thm.declaration_attribute (fn _ => fn ctxt =>
          let val group = Reasoner_Group.check_group false ctxt group'
           in fold (fn pat => register_attribute (group, mandatory, pat, [Morphism.form attr], pos))
                              pats ctxt
          end))
    ) "register attributes applying on premises matching the given pattern, for those premises\
      \ in \<phi>-programming block."
)
(*Syntax: \<phi>premise_attribute  [attribute] for \<open>pattern_of_the_antecedent_to_be_bound\<close>
          \<phi>premise_attribute? [attribute] for \<open>pattern_of_the_antecedent_to_be_bound\<close>

If the question mark is given, the attribute is NOT activated once the user manually give
  an attribute to the premise, e.g. premise[some], or even empty bracket like premise[].
Else, the attribute is always applied BEFORE any attributes given by user.
*)

end