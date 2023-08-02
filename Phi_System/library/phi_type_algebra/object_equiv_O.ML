signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val object_equiv_O : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers



val object_equiv_O = accept_one NAME gen_obj_equal'

end