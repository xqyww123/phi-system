theory Debt_Axiom
  imports Pure
  keywords "debt_axiomatization"  :: thy_stmt
    and    "discharge_debt_axiom" :: thy_decl
    and    "print_debt_axiom"     :: diag
    and "unspecified_type" :: thy_decl
    and "specify_type"     :: thy_decl
    and "morphisms"        :: quasi_command
begin

declare [ [ML_debugger, ML_exception_debugger] ]

ML_file \<open>kernel-sig.ML\<close>
ML_file \<open>kernel.ML\<close> \<comment> \<open>the only kernel, consisting of 28 lines of ML excluding blanks\<close>
ML_file \<open>Debt_Axiom.ML\<close>

end
