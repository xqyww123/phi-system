signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val meta_Synt_Deriver : string * thm * (priority * Reasoner_Group.name option)
                     -> quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun meta_Synt_Deriver' (rule, default_group) (_, name) (H, group, pos, text, notes, bundles) ctxt phi thy =
  let fun err s = raise Automation_Fail (fn () => [Pretty.para s])
      val result =
        case H of SOME H' => Thm.instantiate (Thm.match (Thm.cprop_of rule, Thm.cterm_of ctxt H')) rule
                | NONE => (case Term.add_vars (Thm.prop_of rule) []
                             of [] => rule
                              | [v] => Thm.instantiate (Thm.match (Thm.var (apsnd (Thm.ctyp_of ctxt) v), Thm.cterm_of ctxt (#term phi))) rule
                              | _ => err "requires the form of the rule to be given.")
      val _ = if null notes then () else err "notes here are meaningless."
      val _ = if null bundles then () else err "bundles here are meaningless."
      val _ = if is_none text then () else err "tactic hint here is meaningless."
   in thy
   |> Phi_Help.generic_theory_mapping pos (fn m =>
         Phi_Reasoner.add_rule pos Phi_Reasoner.TO_BE_OVERRIDE
                               (the_default default_group group)
                               ([],[]) NONE [Morphism.thm m result])
   |> pair [result]
  end

fun meta_Synt_Deriver (name, rule, group) =
      deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, name)
                        (meta_Synt_Deriver' (rule, group))

end
