(*Any interfaces in this kernel is not designed to be used directly, please refer to Debt_Axiom.ML*)

signature DEBT_AXIOM_KERNEL = sig
  val axiomize: (string (*full name*) * cterm) -> theory -> thm * theory
  val debts: theory -> term Symtab.table (*axiom type*)
  val discharge: (string (*full name*) * thm) list -> theory -> theory
  val instantiate_type : string (*full name of the type T to be instantiated*)
                      -> string (*full name of the type T' to which T instantiates*)
                      -> binding (*name of the bijection axiom*)
                      -> string (*full name of the const of the injector T \<Rightarrow> T'*)
                      -> string (*full name of the const of the projector T' \<Rightarrow> T*)
                      -> theory -> theory
end
