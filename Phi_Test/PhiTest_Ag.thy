theory PhiTest_Ag
  imports Phi_Semantics.PhiSem_Aggregate_Named_Tuple
          Phi_Semantics.PhiSem_Aggregate_Tuple
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

proc test_ag1:
  input  \<open>Void\<close>
  output \<open>(1, 2, 3) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> b: \<nat>, c: \<nat>, d: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  \<open>(1,2,3) \<Ztypecolon> \<lbrace> b: \<nat>, c: \<nat>, d: \<nat> \<rbrace>\<close>
\<medium_right_bracket> .

proc test_ag2:
  input  \<open>Void\<close>
  output \<open>(1, 2, 3) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<nat>, \<nat>, \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  \<open>(1,2,3) \<Ztypecolon> \<lbrace> \<nat>, \<nat>, \<nat> \<rbrace>\<close>
\<medium_right_bracket> .

no_notation Set.member ("(_/ : _)" [51, 51] 50) (*TODO!*)

proc test_ag3:
  input  \<open>Void\<close>
  output \<open>(1, 2, 1) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> b: \<nat>, c: \<nat>, d: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  \<open>1 \<Ztypecolon> \<nat>\<close> \<rightarrow> val v1 ; 
  \<lbrace> b: $v1, c: \<open>2 \<Ztypecolon> \<nat>\<close>, d: $v1 \<rbrace>
\<medium_right_bracket> .

proc test_ag4:
  input  \<open>Void\<close>
  output \<open>(1, 2, 3) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<nat>, \<nat>, \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  \<open>1 \<Ztypecolon> \<nat>\<close> \<rightarrow> val v1 ;
  \<lbrace> $v1, \<open>2 \<Ztypecolon> \<nat>\<close>, \<open>1 + 2 \<Ztypecolon> \<nat>\<close> \<rbrace>
\<medium_right_bracket> .


end