theory PhiSem_Common_Int
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Preliminary\<close>

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")

\<phi>overloads nat and int

end