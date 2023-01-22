signature PREMISES_ATTRIBUTE = sig

val register_attribute : bool (*mandatory*) * term (*pattern*) * Token.src list
                      -> Context.generic -> Context.generic
      (*if an attribute is mandatory, it is always applied prior before user's attribute.
        By contrast, if it is not, it is for the default case when user does not bind the
        premise and is not applied once user bind the premises.
        '_' is a place holder and not considered as a binding.*)
val register_attribute_lthy : bool * term * Token.src list -> local_theory -> local_theory

(* If multiple attributes match the given term, returns the concatenation of the
  attributes in the order of declaration. *)
val attribute_of : bool (*involve-default?*) -> term -> Context.generic -> Token.src list

end

structure Premises_Attribute : PREMISES_ATTRIBUTE = struct

fun attr_eq ((a1,b1,_), (a2,b2,_)) = (a1 = a2) andalso b1 aconv b2
fun attr_merge (a1,b1,c1) (_,_,c2) = (a1, b1, c1 @ c2)

structure Data = Generic_Data (
  type T = (bool * term (*pattern*) * Token.src list) Item_Net.T
  val empty = Item_Net.init attr_eq (single o #2)
  val merge = Item_Net.merge
)

fun register_attribute attr = Data.map (fn X =>
     Item_Net.update
       (case Item_Net.lookup X attr
          of [] => attr
           | [x] => attr_merge attr x
           | _ => error "impossible! #gqnipe4")
       X)
fun register_attribute_lthy (mandatory, pat,attr) =
  Local_Theory.declaration {syntax=false, pervasive=false}
    (fn m => register_attribute (mandatory, Morphism.term m pat, attr))

fun attribute_of default term ctxt =
  Item_Net.retrieve_matching (@{print} ((Data.get) ctxt)) (Envir.beta_eta_contract term)
    |> map_filter (fn (mandatory,pat, attr) =>
          if (default orelse mandatory)
          andalso Pattern.matches (Context.theory_of ctxt) (pat,term)
          then SOME attr else NONE)
    |> (fn L => fold (fn X => fn L => X @ L) L [])

val prop_pattern = Scan.peek (Args.named_term o
        Syntax.read_prop o Proof_Context.set_mode Proof_Context.mode_pattern o Context.proof_of)

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>premise_attribute\<close> (
    Scan.lift (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) --
    Attrib.attribs --| Scan.lift \<^keyword>\<open>for\<close> -- prop_pattern
    >> (fn ((mandatory, attr), pat) => Thm.declaration_attribute (fn _ =>
          register_attribute (mandatory, pat, attr)))
    ) "register attributes applying on premises matching the given pattern, for those premises\
      \ in \<phi>-programming block."
)
end