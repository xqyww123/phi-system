theory PhiSem_Void
  imports Phi_System.PhiSem_Formalization_Tools2
begin

section \<open>Semantics\<close>

subsection \<open>Type\<close>

virtual_datatype \<phi>void_ty = T_void :: unit

debt_axiomatization T_void :: \<open>unit type_entry\<close>
  where \<phi>void_ty_ax: \<open>\<phi>void_ty TY_CONS_OF T_void\<close>

interpretation \<phi>void_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_void using \<phi>void_ty_ax .

hide_fact \<phi>void_ty_ax \<phi>void_ty_axioms \<phi>void_ty_names_def \<phi>void_ty_def
  \<phi>void_ty_prjs_axioms \<phi>void_ty_prjs_def \<phi>void_ty.axioms \<phi>void_ty.intro
  \<phi>void_ty_prjs.axioms

abbreviation void :: TY where \<open>void \<equiv> T_void.mk ()\<close>

debt_axiomatization
    WT_void  [simp]: \<open>Well_Type void = {} \<close>



end