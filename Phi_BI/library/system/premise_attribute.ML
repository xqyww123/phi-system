signature PREMISES_ATTRIBUTE = sig

val register_attribute : bool (*once*) * Reasoner_Group.group * bool (*mandatory*) * term (*pattern*) * attribute list * Position.T
                      -> Context.generic -> Context.generic
      (*if an attribute is mandatory, it is always applied prior before user's attribute.
        By contrast, if it is not, it is for the default case when user does not bind the
        premise and is not applied once user bind the premises.
        '_' is a place holder and not considered as a binding.*)
val register_attribute_lthy : bool (*once*) * Reasoner_Group.group * bool * term * attribute list * Position.T -> local_theory -> local_theory

(* If multiple attributes match the given term, returns the concatenation of the
  attributes in the order of declaration. *)
val apply_attribute : Context.generic -> bool (*involve-default?*) -> attribute

end

structure Premises_Attribute : PREMISES_ATTRIBUTE = struct

val trace_premise_attrs = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_premise_attrs\<close> (K false)

val data_eq = (op = o apply2 #1)

structure Data = Generic_Data (
  (*It relies on that the serial is incremental with time*)
  type T = ( serial
           * bool (*whether to be applied at most once*)
           * Reasoner_Group.group
           * bool (*whether to be applied when user attributes are given. If false, it is a default attribute
                    used only when no user attributes are given*)
           * term (*pattern*)
           * attribute list
           * Position.T) Net.net
  val empty = Net.empty
  val merge = Net.merge data_eq
)

fun register_attribute (once,prio,mandatory,pat,attr,pos)
  = Data.map (Net.insert_term data_eq (pat, (serial(),once,prio,mandatory,pat,attr,pos)))

fun register_attribute_lthy (once,prio,mandatory,pat,attr,pos) =
  Local_Theory.declaration {syntax=false, pervasive=false, pos=Position.none}
    (fn m => register_attribute (once,prio,mandatory, Morphism.term m pat, attr, pos))

fun apply_attribute ctxt default =
  let val data = Data.get ctxt
      val matches = PLPR_Pattern.matches (Context.theory_of ctxt) (K true)
      val trace = Config.get_generic ctxt trace_premise_attrs
   in fn (ctxt, th) =>
      if Thm.is_free_dummy th then (NONE, NONE) else
      let val positions = if trace then SOME (Unsynchronized.ref [])
                                   else NONE
          fun apply disabled (th, ctxt) =
            let val (bvs, concl) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.beta_eta_contract_term (Thm.concl_of th))
                val (bvs, concl, th) = if null bvs then (bvs, concl, th)
                                       else let val th' = Thm.forall_elim_vars (Thm.maxidx_of th) th
                                                val (bvs, concl) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.beta_eta_contract_term (Thm.concl_of th))
                                             in (bvs,concl,th')
                                            end
             in Net.match_term data concl
             |> map_filter (fn (id,once,prio,mandatory,pat,attr,pos) =>
                   if (default orelse mandatory) andalso
                      (not once orelse not (Inttab.defined disabled id)) andalso
                      matches bvs (pat,concl)
                   then SOME (prio, (if once then SOME id else NONE), attr, pos) else NONE)
             |> Phi_Help.max_of (int_ord o apply2 (#1 o #1))
             |> (fn NONE => (th,ctxt)
                  | SOME (_, id, attrs, pos) =>
                      let val _ = case positions of NONE => ()
                                                  | SOME L => L := pos :: !L
                          val disabled' = case id of NONE => disabled
                                                   | SOME id => Inttab.insert_set id disabled
                       in apply disabled'
                                (fold (uncurry o Thm.apply_attribute) attrs (th, ctxt))
                      end)
            end
          val (th', ctxt') = apply Inttab.empty (th, ctxt)
       in (case positions of NONE => ()
                           | SOME poss =>
              let open Pretty
               in tracing (string_of (chunks [
                    block ( text "applying default attributes"
                          @ [brk 1] 
                          @ maps (fn pos => Pretty.here pos @ [brk 1]) (!poss)
                          @ text "on local premise"),
                    Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt (Thm.concl_of th)]))
              end);
          (SOME ctxt', SOME th')
       end
  end

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
    Scan.lift (Scan.optional (Args.$$$ "once" >> K true) false) --
    Scan.lift (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) --
    Attrib.attribs -- Scan.lift (Parse.position \<^keyword>\<open>for\<close>) -- prop_patterns --
    Scan.lift (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>)
    >> (fn (((((once, mandatory), attr), (_, pos)), pats), group') => Thm.declaration_attribute (fn _ => fn ctxt =>
          let val group = Reasoner_Group.check_group false ctxt group'
           in fold (fn pat => register_attribute (once, group, mandatory, pat, chk_attribute ctxt attr, pos))
                            pats ctxt
          end))
    ) "register attributes applying on premises matching the given pattern, for those premises\
      \ in \<phi>-programming block."
#>Attrib.setup \<^binding>\<open>\<phi>premise_attribute_ML\<close> (
    Scan.lift (Scan.optional (Args.$$$ "once" >> K true) false) --
    Scan.lift (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) --
    phi_system_ML_attribute_parser -- Scan.lift (Parse.position \<^keyword>\<open>for\<close>) -- prop_patterns --
    Scan.lift (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>)
    >> (fn (((((once, mandatory), attr), (_, pos)), pats), group') => Thm.declaration_attribute (fn _ => fn ctxt =>
          let val group = Reasoner_Group.check_group false ctxt group'
           in fold (fn pat => register_attribute (once, group, mandatory, pat, [Morphism.form attr], pos))
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