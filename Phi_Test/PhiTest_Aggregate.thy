theory PhiTest_Aggregate
  imports Phi_Semantics.PhiSem_Aggregate_Array
          Phi_Semantics.PhiSem_Aggregate_Tuple
          Phi_Semantics.PhiSem_CF_Routine
          Phi_Semantics.PhiSem_CF_Breakable
          Phi_Semantics.PhiSem_Variable
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")


proc
  input \<open>(x,y,(z1,z2)) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<nat> , \<int> , \<lbrace> \<nat>, \<int> \<rbrace> \<rbrace>\<heavy_comma> aa \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>z1 \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>   
  \<medium_left_bracket> op_set_aggregate 0
    op_get_aggregate 2,0 \<medium_right_bracket>. .
  
proc
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  premises \<open>x < 10\<close>
  output \<open>\<v>\<a>\<l> 10 \<Ztypecolon> \<nat>\<close>
  is [routine]
  \<medium_left_bracket> $x \<rightarrow> var v (*x is an immutable value, and here we assign it to a variable v*);;
    while \<open>x \<Ztypecolon> ?T \<s>\<u>\<b>\<j> x. Inv: (x \<le> 10) \<and> Guard: True \<and> End: (x = 10)\<close> (*annotation*)
    \<medium_left_bracket> \<open>True\<close> \<medium_right_bracket>. (*guard*)
    \<medium_left_bracket>
      if \<open>$v = 10\<close> \<medium_left_bracket> break \<medium_right_bracket>. \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v;; continue \<medium_right_bracket>.
      assert \<bottom>
    \<medium_right_bracket>. (*loop body*)
    $v
    \<medium_right_bracket>. .



end