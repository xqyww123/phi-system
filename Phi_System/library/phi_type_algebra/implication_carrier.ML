signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val abstract_domain_MC : quiet -> hint list -> Phi_Type.derive
val abstract_domain_MCL : quiet -> hint list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

(*** Inhabitance ***)

end
