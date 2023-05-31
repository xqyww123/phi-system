theory PhiSem_Real_Abst_Int
  imports PhiSem_Real_Abst PhiSem_Int_ArbiPrec
begin

setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put
                                          (SOME Generic_Variable_Access.store_value_no_clean))\<close>

section \<open>Conversion between Abstract Real and Arbitrary-precision Integers\<close>

definition op_Ra_floor_Za :: \<open>(VAL, VAL) proc'\<close>
  where \<open>op_Ra_floor_Za rv =
    \<phi>M_getV areal V_areal.dest rv (\<lambda>v.
    Return (\<phi>arg (V_aint.mk \<lfloor>v\<rfloor>)))\<close>

definition op_Ra_ceiling_Za :: \<open>(VAL, VAL) proc'\<close>
  where \<open>op_Ra_ceiling_Za rv =
    \<phi>M_getV areal V_areal.dest rv (\<lambda>v.
    Return (\<phi>arg (V_aint.mk \<lceil>v\<rceil>)))\<close>

lemma op_Ra_floor_Za_\<phi>app[\<phi>overload floor, \<phi>synthesis 100]:
  \<open>\<p>\<r>\<o>\<c> op_Ra_floor_Za raw \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw] \<real> \<longmapsto> \<lfloor>x\<rfloor> \<Ztypecolon> \<v>\<a>\<l> \<int> \<rbrace>\<close>
  unfolding op_Ra_floor_Za_def
  by (cases raw; simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_Ra_ceiling_Za_\<phi>app[\<phi>overload ceiling, \<phi>synthesis 100]:
  \<open>\<p>\<r>\<o>\<c> op_Ra_ceiling_Za raw \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw] \<real> \<longmapsto> \<lceil>x\<rceil> \<Ztypecolon> \<v>\<a>\<l> \<int> \<rbrace>\<close>
  unfolding op_Ra_ceiling_Za_def
  by (cases raw; simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)


\<phi>overloads to_real

definition op_Za_to_Ra :: \<open>(VAL, VAL) proc'\<close>
  where \<open>op_Za_to_Ra rv =
    \<phi>M_getV aint V_aint.dest rv (\<lambda>v.
    Return (\<phi>arg (V_areal.mk (real_of_int v))))\<close>


declare [[
    overloaded_operator_in_synthesis \<open>real_of_int\<close>,
    overloaded_operator_in_synthesis \<open>real_of_nat\<close>
 ]]

lemma op_Za_to_Ra_\<phi>app
  [\<phi>overload to_real, \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<int>\<close> \<Rightarrow> \<open>\<lambda>v. real_of_int x \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_Za_to_Ra raw \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw] \<int> \<longmapsto> real_of_int x \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  unfolding op_Za_to_Ra_def
  by (cases raw; simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns)

lemma op_Na_to_Ra_\<phi>app
  [\<phi>overload to_real, \<phi>synthesis for _ (100)
                                 and \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> \<Rightarrow> \<open>\<lambda>v. real_of_int x \<Ztypecolon> _\<close> (1200)]:
  \<open> \<p>\<r>\<o>\<c> op_Za_to_Ra raw \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw] \<nat> \<longmapsto> real_of_nat x \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  \<medium_left_bracket> op_Za_to_Ra \<medium_right_bracket>.


setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put NONE)\<close>

end