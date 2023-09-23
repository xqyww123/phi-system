signature PREMISES_ATTRIBUTE = sig

val register_attribute : serial * bool (*mandatory*) * term (*pattern*) * attribute list
                      -> Context.generic -> Context.generic
      (*if an attribute is mandatory, it is always applied prior before user's attribute.
        By contrast, if it is not, it is for the default case when user does not bind the
        premise and is not applied once user bind the premises.
        '_' is a place holder and not considered as a binding.*)
val register_attribute_lthy : serial * bool * term * attribute list -> local_theory -> local_theory

(* If multiple attributes match the given term, returns the concatenation of the
  attributes in the order of declaration. *)
val attribute_of : bool (*involve-default?*) -> term -> Context.generic -> attribute list

end

structure Premises_Attribute : PREMISES_ATTRIBUTE = struct

val data_eq = (op = o apply2 #1)

structure Data = Generic_Data (
  (*It relies on that the serial is incremental with time*)
  type T = (serial * bool * term (*pattern*) * attribute list (*TODO: change this to Token.T!!*)) Net.net
  val empty = Net.empty
  val merge = Net.merge data_eq
)

fun register_attribute attr = Data.map (Net.insert_term data_eq (#3 attr, attr))

fun register_attribute_lthy (i,mandatory,pat,attr) =
  Local_Theory.declaration {syntax=false, pervasive=false, pos=Position.none}
    (fn m => register_attribute (i,mandatory, Morphism.term m pat, attr))

fun attribute_of default term ctxt =
  Net.match_term (Data.get ctxt) (Envir.beta_eta_contract term)
    |> map_filter (fn (i,mandatory,pat, attr) =>
          if (default orelse mandatory)
          andalso Pattern.matches (Context.theory_of ctxt) (pat,term)
          then SOME (i,attr) else NONE)
    |> sort (int_ord o apply2 #1)
    |> maps snd

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
    Attrib.attribs --| Scan.lift \<^keyword>\<open>for\<close> -- prop_patterns
    >> (fn ((mandatory, attr), pats) => Thm.declaration_attribute (fn _ => fn ctxt =>
            fold (fn pat => register_attribute (serial(), mandatory, pat, chk_attribute ctxt attr))
                            pats ctxt))
    ) "register attributes applying on premises matching the given pattern, for those premises\
      \ in \<phi>-programming block."
#>Attrib.setup \<^binding>\<open>\<phi>premise_attribute_ML\<close> (
    Scan.lift (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) --
    phi_system_ML_attribute_parser --| Scan.lift \<^keyword>\<open>for\<close> -- prop_patterns
    >> (fn ((mandatory, attr), pats) => Thm.declaration_attribute (fn _ => fn ctxt =>
            fold (fn pat => register_attribute (serial(), mandatory, pat, [Morphism.form attr]))
                            pats ctxt))
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