signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val meta_Synt_Deriver : string * thm * (priority * Reasoner_Group.name option)
                     -> quiet * Position.T -> deriving_instruction list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun meta_Synt_Deriver' (rule, default_group) (_, name) (H, group, pos, text) ctxt phi thy =
  let val H' = Thm.cterm_of ctxt (the H)
      val result = Thm.instantiate (Thm.match (Thm.cprop_of rule, H')) rule
   in thy
   |> Phi_Help.generic_theory_mapping pos (fn m =>
         Phi_Reasoner.add_rule pos Phi_Reasoner.TO_BE_OVERRIDE
                               (the_default default_group group)
                               ([],[]) NONE [Morphism.thm m result])
   |> pair [result]
  end

fun meta_Synt_Deriver (name, rule, group) =
      deriver_framework (REQUIRE_EXACT_ONE_HINT, ONLY_ONCE, name)
                        (meta_Synt_Deriver' (rule, group))

end
