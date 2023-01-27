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
  type T = (serial * bool * term (*pattern*) * attribute list) Net.net
  val empty = Net.empty
  val merge = Net.merge data_eq
)

fun register_attribute attr = Data.map (Net.insert_term data_eq (#3 attr, attr))

fun register_attribute_lthy (i,mandatory,pat,attr) =
  Local_Theory.declaration {syntax=false, pervasive=false}
    (fn m => register_attribute (i,mandatory, Morphism.term m pat, attr))

fun attribute_of default term ctxt =
  Net.match_term (Data.get ctxt) (Envir.beta_eta_contract term)
    |> map_filter (fn (i,mandatory,pat, attr) =>
          if (default orelse mandatory)
          andalso Pattern.matches (Context.theory_of ctxt) (pat,term)
          then SOME (i,attr) else NONE)
    |> sort (int_ord o apply2 #1)
    |> (fn L => fold (fn (_,X) => fn L => X @ L) L [])

val prop_pattern = Scan.peek (Args.named_term o
        Syntax.read_prop o Proof_Context.set_mode Proof_Context.mode_pattern o Context.proof_of)

fun chk_attribute ctxt = map (Context.cases Attrib.attribute_global Attrib.attribute ctxt)

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>premise_attribute\<close> (
    Scan.lift (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) --
    Attrib.attribs --| Scan.lift \<^keyword>\<open>for\<close> -- Scan.repeat prop_pattern
    >> (fn ((mandatory, attr), pats) => Thm.declaration_attribute (fn _ => fn ctxt =>
          fold (fn pat => register_attribute (serial(), mandatory, pat, chk_attribute ctxt attr)) pats ctxt))
    ) "register attributes applying on premises matching the given pattern, for those premises\
      \ in \<phi>-programming block."
)
end