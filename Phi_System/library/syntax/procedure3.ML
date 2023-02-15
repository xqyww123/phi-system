signature PROCEDURE_SYNTAX = sig
include PROCEDURE_SYNTAX

(*Given a procedure spec (a triple), proc f arg \<lbrace> X arg \<longmapsto> Y \<rbrace>
  it universally quantifies the term, returning \<open>\<forall>arg. proc f arg \<lbrace> X arg \<longmapsto> Y \<rbrace>\<close>
  using the argument encoding*)
val quantify_args_of_proc : term -> term

end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct
open Procedure_Syntax



end
