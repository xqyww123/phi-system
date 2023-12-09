theory PhiSem_Mem_C_Ag_NT \<comment> \<open>Named Tuple\<close>
  imports PhiSem_Mem_C PhiSem_Aggregate_Named_Tuple
begin



syntax "\<phi>_shared_named_tuple_" :: \<open>logic \<Rightarrow> \<phi>_symbol_ \<Rightarrow> logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_ \<odiv> _: _")

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_shared_named_tuple_ n s X))" => "\<phi>_shared_named_tuple_ n s X"

setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 100 (
    fn (ctxt, f, Const(\<^const_name>\<open>Named_Tuple_Field\<close>, _) $ s $ T) =>
        SOME (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, dummyT)
                $ (Const(\<^const_name>\<open>Cons\<close>, dummyT) $ (Const(\<^const_name>\<open>AgIdx_S\<close>, dummyT) $ s) $ Const(\<^const_name>\<open>Nil\<close>, dummyT))
                $ f ctxt T)
     | (ctxt, f, Const(\<^syntax_const>\<open>\<phi>_shared_named_tuple_\<close>, _) $ sh $ s $ T) =>
        SOME (Const(\<^const_name>\<open>\<phi>Share\<close>, dummyT)
          $ sh
          $ (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, dummyT)
                $ (Const(\<^const_name>\<open>Cons\<close>, dummyT) $ (Const(\<^const_name>\<open>AgIdx_S\<close>, dummyT) $ s) $ Const(\<^const_name>\<open>Nil\<close>, dummyT))
                $ f ctxt T))
     | _ => NONE)

#>Phi_Mem_Printer.add 100 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>Phi_Types.\<phi>MapAt_L1\<close>, _)
          $ (Const(\<^const_syntax>\<open>AgIdx_S\<close>, _) $ s)
          $ T) =>
        SOME (Const(\<^const_syntax>\<open>Named_Tuple_Field\<close>, dummyT) $ s $ f ctxt T)
     | (ctxt, f, Const(\<^const_syntax>\<open>\<phi>Share\<close>, _) $ sh
        $ (Const(\<^const_syntax>\<open>Phi_Types.\<phi>MapAt_L1\<close>, _)
            $ (Const(\<^const_syntax>\<open>AgIdx_S\<close>, _) $ sym)
            $ T)) =>
          SOME (Const (\<^syntax_const>\<open>_\<phi>Tuple\<close>, dummyT) $
                  (Const (\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $ (
            Const(\<^syntax_const>\<open>\<phi>_shared_named_tuple_\<close>, dummyT) $ sh
                  $ (case sym of Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ id => Phi_Tool_Symbol.print id
                           | _ => sym)
                  $ f ctxt T)))
     | X_ => NONE
)
)\<close>

(* example
term \<open>a \<odiv> b\<close>
    
term \<open>\<m>\<e>\<m>[addr] \<lbrace> c \<odiv> a: T, dd \<odiv> b: \<lbrace> e: U \<rbrace>\<rbrace>\<close>
term \<open>\<m>\<e>\<m>[addr] \<lbrace> a: T, b: (U \<^emph> D)\<rbrace>\<close>
*)


end