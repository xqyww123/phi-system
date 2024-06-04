theory PhiTest_Arithmetic
  imports
    Phi_Semantics.PhiSem_CF_Routine
    Phi_Semantics.PhiSem_CF_Breakable
    Phi_Semantics.PhiSem_Variable
    Phi_Semantics.PhiSem_Int_ArbiPrec
    "HOL-Computational_Algebra.Primes"
    Phi_Semantics.PhiCG_C
begin

declare [[\<phi>variable_is_typed]]

proc test_prime:
  input  \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> prime x \<Ztypecolon> \<bool>\<close> \<comment> \<open>\<^term>\<open>prime :: nat => bool\<close> is a predicate checking primes\<close>
  is [routine]
\<medium_left_bracket>
  if ( x \<le> 1 )  \<medium_left_bracket>
    return (False)
  \<medium_right_bracket>
  \<medium_left_bracket> 
    2 \<rightarrow> var v \<semicolon>

    while \<open>i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i.
            Inv: (1 < i \<and> i \<le> x \<and> (\<forall>j. 1 < j \<and> j < i \<longrightarrow> \<not> j dvd x)) \<and>
            Guard: (i \<noteq> x) \<and>
            End: (i = x)\<close> \<comment> \<open>Specification of the loop\<close>
          ( \<open>$v \<noteq> $x\<close> ) \<comment> \<open>Code for loop guard\<close>
    \<medium_left_bracket>                   \<comment> \<open>Code for loop body\<close>
      if (x % v = 0) \<medium_left_bracket>
        return (False)
      \<medium_right_bracket> \<medium_left_bracket>
        v + 1 \<rightarrow> v
      \<medium_right_bracket> 
    \<medium_right_bracket>
    return (True)
  \<medium_right_bracket>
\<medium_right_bracket> .

term \<open>(\<lambda>e. \<b>\<r>\<e>\<a>\<k> lb \<w>\<i>\<t>\<h> (\<lambda>_. i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i. (1 < i \<and> i \<le> x \<and> (\<forall>j. 1 < j \<and> j < i \<longrightarrow> \<not> j dvd x)) \<and> i = x) \<o>\<r> \<b>\<r>\<e>\<a>\<k> lc
                 \<w>\<i>\<t>\<h> (\<lambda>_. i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i. 1 < i \<and> i \<le> x \<and> (\<forall>j. 1 < j \<and> j < i \<longrightarrow> \<not> j dvd x)) \<o>\<r> i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat>\<heavy_comma>
                 (\<^bold>b\<^bold>r\<^bold>o\<^bold>k\<^bold>e\<^bold>n label_ret \<w>\<i>\<t>\<h> (\<lambda>\<r>\<e>\<t>. prime x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<bool>)))\<close>

thm test_prime_def \<comment> \<open>Semantic definition\<close>
thm test_prime_\<phi>app \<comment> \<open>Specification theorem\<close>


proc test_prime':
  input  \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> prime x \<Ztypecolon> \<bool>\<close>
  is [routine]
\<medium_left_bracket>
  if \<open>$x \<le> 1\<close> \<medium_left_bracket>
    return (False)
  \<medium_right_bracket> \<medium_left_bracket>
    \<open>2 \<Ztypecolon> \<nat>\<close> \<rightarrow> var v \<semicolon>
    while \<open>i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i.
          Inv: (1 < i \<and> i \<le> x \<and> (\<forall>j \<in> {1<..<i}. \<not> j dvd x)) \<and>
          Guard: (i * i \<le> x) \<and>
          End: (x < i * i)\<close>
        ( v * v \<le> x )
    \<medium_left_bracket>
      if \<open>$x mod $v = 0\<close> \<medium_left_bracket>
        return (False)
      \<medium_right_bracket> \<medium_left_bracket>
        \<open>$v + 1\<close> \<rightarrow> $v 
      \<medium_right_bracket>
    \<medium_right_bracket>

    return (True) (*with this optimization, the final obligation fails to be solved
                    automatically, but the manual proof is intuitive and semi-automated.*)
    certified proof simp
        have \<open>False\<close> if assm: \<open>\<not> prime x\<close>
          proof -
            obtain k where t1: \<open>k dvd x \<and> 1 < k \<and> k < x\<close> by auto_sledgehammer
            then have \<open>k < i \<or> x div k < i\<close> by auto_sledgehammer
            then show False using t1
              by (metis One_nat_def dvd_mult_div_cancel dvd_triv_right greaterThanLessThan_iff nat_mult_1_right nat_mult_less_cancel_disj the_\<phi>lemmata(3))
          qed
        then show \<open>prime x\<close>
          by auto_sledgehammer
      qed
  \<medium_right_bracket> \<comment> \<open>Close the top branch\<close>
\<medium_right_bracket> \<comment> \<open>Close the function body\<close> .

declare [[\<phi>hide_techinicals=false]] 

proc GCD:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>gcd x y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> 
  is [recursive x y] \<comment> \<open>x, y are variable through recursive callings\<close>
  is [routine]
\<medium_left_bracket>
  if ($y < $x) \<medium_left_bracket> GCD ($y, $x) \<medium_right_bracket>
  \<medium_left_bracket>
    \<open>$y mod $x\<close> \<rightarrow> val t
    if \<open>$t = 0\<close> \<medium_left_bracket> $x \<medium_right_bracket> \<medium_left_bracket> GCD ($t, $x) \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket>.


thm GCD_def

declare GCD_\<phi>app[\<phi>synthesis add] \<comment> \<open>So that we can use abstract spec \<open>gcd\<close> in synthesis\<close>

proc Coprime:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>coprime x y \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  \<open>gcd $x $y = 1\<close>
\<medium_right_bracket>.

proc binary_search:
  requires F: \<open>\<forall>i v. \<p>\<r>\<o>\<c> F v \<lbrace> i \<Ztypecolon> \<v>\<a>\<l>[v] \<int> \<longmapsto> f i \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close> \<comment> \<open>v: raw value\<close>
  premises \<open>mono f\<close>
  input  \<open>lower \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  premises \<open>f upper\<close> and \<open>lower < upper\<close>
  output \<open>(LEAST i. lower \<le> i \<and> i \<le> upper \<and> f i) \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  is [routine]
\<medium_left_bracket> 
  holds_fact \<open>i \<le> j \<Longrightarrow> f i \<Longrightarrow> f j\<close> for i j ;;

  if ( F($lower) ) \<medium_left_bracket>
     return ($lower)
  \<medium_right_bracket> \<medium_left_bracket> 
    ($lower, $upper) \<rightarrow> var $l, $u ;;
    while \<open>l \<Ztypecolon> \<v>\<a>\<r>[l] \<int>\<heavy_comma> u \<Ztypecolon> \<v>\<a>\<r>[u] \<int> \<s>\<u>\<b>\<j> l u.
            Inv: (lower \<le> l \<and> l < u \<and> u \<le> upper \<and> \<not> f l \<and> f u) \<and>
            Guard: (l + 1 < u) \<and>
            End: (l + 1 = u)\<close>
          ( \<open>$l + 1 < $u\<close> )
    \<medium_left_bracket>
      \<open>($l + $u) div 2\<close> \<rightarrow> val m
      if ( F($m) ) \<medium_left_bracket> $m \<rightarrow> $u \<medium_right_bracket> \<medium_left_bracket> $m \<rightarrow> $l \<medium_right_bracket>
    \<medium_right_bracket>
    return ($u)
  \<medium_right_bracket>
\<medium_right_bracket> .


ML \<open>Phi_Procedure.procedures_of (Context.Theory \<^theory>)\<close>

thm if_def

ML \<open>structure CG_PhiSem_CF_Basic = struct
open CG_PhiSem_CF_Basic
val if_ = (fn a_t0 => (fn b2 => (fn b3 => (fn b4 => CG_Phi_Semantics_Framework.bind_ (b2) (op_if_ (b3) (b4))))))
val while_ = (fn b1 => (fn b2 =>
  CG_Phi_Semantics_Framework.bind_ (b1) (
  op_if_ (
op_do_while_ (
CG_Phi_Semantics_Framework.bind_
(b2) ((fn b3 => b1))))
  (CG_Phi_Semantics_Framework.Return_ (CG_Phi_Semantics_Framework.phi_V_none_)))))
val _ = Phi_CG.codegen "PhiSem_CF_Basic" ()
end\<close>


ML \<open>Context.get_theory {long=false} \<^theory> "PhiSem_CF_Basic"\<close>

thm if_def
setup \<open>Context.theory_map (Phi_CG_Emit.codegen true (Context.get_theory {long=false} \<^theory> "PhiSem_CF_Basic"))\<close>

thm test_prime_def
ML \<open>@{thm test_prime_def} |> Thm.prop_of\<close>

thm op_var_scope_def
thm op_get_var_def

ML \<open>fn b2 => fn b3 => fn b4 => 
((fn b6 => (fn b7 => CG_PhiSem_CF_Basic.if_ (CG_Product_Type.unit_T)
 (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_))
 ((fn b8 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_amod_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b3) (b8)))
 ((fn b9 => CG_PhiSem_Generic_Boolean.op_equal_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_Phi_Semantics_Framework.phi_V_pair_ (b9)
 (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.zero_class.zero_)))))))))
 (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Generic_Boolean.op_const_bool_ (CG_HOL.False_)) (CG_PhiSem_CF_Break.op_break_
 (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b2))) (CG_Phi_Semantics_Framework.bind_ 
(CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b8 => 
CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_aadd_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b8) 
(CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.one_class.one_))))) 
(CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b4) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__))
 (CG_List.list.Nil_))))))))\<close>

ML \<open>structure CG_PhiTest_Arithmetic = struct
val test_prime_ = (fn b1 => CG_PhiSem_CF_Routine.op_routine_ (CG_Phi_Semantics_Framework.VAL_T) (CG_Phi_Semantics_Framework.VAL_T)
 (CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) (CG_List.list.Cons_ (CG_PhiSem_Generic_Boolean.b_o_o_l__)
 (CG_List.list.Nil_)) ((fn b2 => (fn b3 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_CF_Basic.if_ (CG_Product_Type.unit_T)
 (CG_PhiSem_Int_ArbiPrec.op_a_le_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b3) (CG_PhiSem_Formalization_Tools.semantic_literal_
 (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.one_class.one_))))) (CG_Phi_Semantics_Framework.bind_ 
(CG_PhiSem_Generic_Boolean.op_const_bool_ (CG_HOL.False_)) (CG_PhiSem_CF_Break.op_break_ (CG_Product_Type.unit_T)
 (CG_Phi_Semantics_Framework.VAL_T) (b2))) (CG_PhiSem_Variable.op_var_scope_ (CG_Product_Type.unit_T)
 (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__)) ((fn b4 => CG_Phi_Semantics_Framework.bind_
 (CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b4) (CG_Option.option.None_) 
(CG_List.list.Nil_) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ 
(CG_Num.numeral_class.numeral_ (CG_Num.num.Bit0_ (CG_Num.num.One_)))))) ((fn b5 => CG_Phi_Semantics_Framework.bind_
 (CG_PhiSem_CF_Breakable.while_ (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b4) 
(CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b6 => CG_Phi_Semantics_Framework.bind_ 
(CG_PhiSem_Generic_Boolean.op_equal_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_Phi_Semantics_Framework.phi_V_pair_ (b6) (b3)))
 (CG_PhiSem_Generic_Boolean.op_not_)))) ((fn b6 => (fn b7 => CG_PhiSem_CF_Basic.if_ (CG_Product_Type.unit_T)
 (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_))
 ((fn b8 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_amod_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b3) (b8)))
 ((fn b9 => CG_PhiSem_Generic_Boolean.op_equal_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_Phi_Semantics_Framework.phi_V_pair_ (b9)
 (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.zero_class.zero_)))))))))
 (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Generic_Boolean.op_const_bool_ (CG_HOL.False_)) (CG_PhiSem_CF_Break.op_break_
 (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b2))) (CG_Phi_Semantics_Framework.bind_ 
(CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b8 => 
CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_aadd_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b8) 
(CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.one_class.one_))))) 
(CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b4) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__))
 (CG_List.list.Nil_))))))))) ((fn b6 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Generic_Boolean.op_const_bool_ (CG_HOL.True_)) 
(CG_PhiSem_CF_Break.op_break_ (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b2)))))))))) 
((fn b4 => CG_Phi_Semantics_Framework.Return_ (CG_Phi_Semantics_Framework.phi_arg.phi_arg_ (CG_Phi_Semantics_Framework.unreachable_))))))) (b1))

val test_prime'_ = (fn b1 => CG_PhiSem_CF_Routine.op_routine_ (CG_Phi_Semantics_Framework.VAL_T) (CG_Phi_Semantics_Framework.VAL_T) (CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) (CG_List.list.Cons_ (CG_PhiSem_Generic_Boolean.b_o_o_l__) (CG_List.list.Nil_)) ((fn b2 => (fn b3 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_CF_Basic.if_ (CG_Product_Type.unit_T) (CG_PhiSem_Int_ArbiPrec.op_a_le_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b3) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.one_class.one_))))) (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Generic_Boolean.op_const_bool_ (CG_HOL.False_)) (CG_PhiSem_CF_Break.op_break_ (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b2))) (CG_PhiSem_Variable.op_var_scope_ (CG_Product_Type.unit_T) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__)) ((fn b4 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b4) (CG_Option.option.None_) (CG_List.list.Nil_) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Num.numeral_class.numeral_ (CG_Num.num.Bit0_ (CG_Num.num.One_)))))) ((fn b5 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_CF_Breakable.while_ (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b6 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b7 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_amul_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b6) (b7))) ((fn b8 => CG_PhiSem_Int_ArbiPrec.op_a_le_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b8) (b3))))))))) ((fn b6 => (fn b7 => CG_PhiSem_CF_Basic.if_ (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b8 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_amod_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b3) (b8))) ((fn b9 => CG_PhiSem_Generic_Boolean.op_equal_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_Phi_Semantics_Framework.phi_V_pair_ (b9) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.zero_class.zero_))))))))) (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Generic_Boolean.op_const_bool_ (CG_HOL.False_)) (CG_PhiSem_CF_Break.op_break_ (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b2))) (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b4) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b8 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_aadd_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b8) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.one_class.one_))))) (CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b4) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__)) (CG_List.list.Nil_))))))))) ((fn b6 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Generic_Boolean.op_const_bool_ (CG_HOL.True_)) (CG_PhiSem_CF_Break.op_break_ (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b2)))))))))) ((fn b4 => CG_Phi_Semantics_Framework.Return_ (CG_Phi_Semantics_Framework.phi_arg.phi_arg_ (CG_Phi_Semantics_Framework.unreachable_))))))) (b1))

val GCD_ = (fn b1 => CG_PhiSem_CF_Routine.op_rec_routine_ (CG_Phi_Semantics_Framework.VAL_T) 
(CG_Product_Type.prod_T (CG_Phi_Semantics_Framework.VAL_T) (CG_Phi_Semantics_Framework.VAL_T)) 
(CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) 
(CG_List.list.Nil_))) (CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) 
((fn b2 => (fn b3 => (fn b4 => CG_PhiSem_CF_Basic.if_ (CG_Phi_Semantics_Framework.VAL_T) 
(CG_PhiSem_Int_ArbiPrec.op_a_lt_ (CG_Phi_Semantics_Framework.phi_V_pair_ (CG_Phi_Semantics_Framework.phi_V_snd_ (b4)) 
(CG_Phi_Semantics_Framework.phi_V_fst_ (b4)))) (b2 (CG_Phi_Semantics_Framework.phi_V_pair_ 
(CG_Phi_Semantics_Framework.phi_V_snd_ (b4)) (CG_Phi_Semantics_Framework.phi_V_fst_ (b4)))) (CG_Phi_Semantics_Framework.bind_ 
(CG_PhiSem_Int_ArbiPrec.op_amod_ (CG_Phi_Semantics_Framework.phi_V_pair_ (CG_Phi_Semantics_Framework.phi_V_snd_ (b4)) 
(CG_Phi_Semantics_Framework.phi_V_fst_ (b4)))) ((fn b5 => CG_PhiSem_CF_Basic.if_ (CG_Phi_Semantics_Framework.VAL_T) 
(CG_PhiSem_Generic_Boolean.op_equal_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_Phi_Semantics_Framework.phi_V_pair_ (b5)
 (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.zero_class.zero_)))))
 (CG_Phi_Semantics_Framework.Return_ (CG_Phi_Semantics_Framework.phi_V_fst_ (b4))) (b2 (CG_Phi_Semantics_Framework.phi_V_pair_ 
(b5) (CG_Phi_Semantics_Framework.phi_V_fst_ (b4))))))))))) (b1))

val Coprime_ = (fn b1 => CG_Phi_Semantics_Framework.bind_ (GCD_ (b1)) ((fn b2 => CG_PhiSem_Generic_Boolean.op_equal_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_Phi_Semantics_Framework.phi_V_pair_ (b2) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.one_class.one_)))))))
val binary_search_ = (fn b1 => (fn b2 => CG_PhiSem_CF_Routine.op_routine_ (CG_Phi_Semantics_Framework.VAL_T) (CG_Product_Type.prod_T (CG_Phi_Semantics_Framework.VAL_T) (CG_Phi_Semantics_Framework.VAL_T)) (CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_))) (CG_List.list.Cons_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b3 => (fn b4 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_CF_Basic.if_ (CG_Product_Type.unit_T) (b1 (CG_Phi_Semantics_Framework.phi_V_fst_ (b4))) (CG_PhiSem_CF_Break.op_break_ (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b3) (CG_Phi_Semantics_Framework.phi_V_fst_ (b4))) (CG_PhiSem_Variable.op_var_scope_ (CG_Product_Type.unit_T) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__)) ((fn b5 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b5) (CG_Option.option.None_) (CG_List.list.Nil_) (CG_Phi_Semantics_Framework.phi_V_snd_ (b4))) ((fn b6 => CG_PhiSem_Variable.op_var_scope_ (CG_Product_Type.unit_T) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__)) ((fn b7 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b7) (CG_Option.option.None_) (CG_List.list.Nil_) (CG_Phi_Semantics_Framework.phi_V_fst_ (b4))) ((fn b8 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_CF_Breakable.while_ (CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b7) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b9 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_aadd_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b9) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Groups.one_class.one_))))) ((fn b10 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b5) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b11 => CG_PhiSem_Int_ArbiPrec.op_a_lt_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b10) (b11))))))))) ((fn b9 => (fn b10 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b7) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b11 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b5) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) ((fn b12 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_aadd_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b11) (b12))) ((fn b13 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Int_ArbiPrec.op_adiv_ (CG_Phi_Semantics_Framework.phi_V_pair_ (b13) (CG_PhiSem_Formalization_Tools.semantic_literal_ (CG_PhiSem_Int_ArbiPrec.sem_mk_aint_ (CG_Num.numeral_class.numeral_ (CG_Num.num.Bit0_ (CG_Num.num.One_))))))) ((fn b14 => CG_PhiSem_CF_Basic.if_ (CG_Product_Type.unit_T) (b1 (b14)) (CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b5) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__)) (CG_List.list.Nil_) (b14)) (CG_PhiSem_Variable.op_set_var_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (b7) (CG_Option.option.Some_ (CG_PhiSem_Int_ArbiPrec.a_i_n_t__)) (CG_List.list.Nil_) (b14)))))))))))))) ((fn b9 => CG_Phi_Semantics_Framework.bind_ (CG_PhiSem_Variable.op_get_var_ (b5) (CG_PhiSem_Int_ArbiPrec.a_i_n_t__) (CG_List.list.Nil_)) (CG_PhiSem_CF_Break.op_break_ (CG_Product_Type.unit_T) (CG_Phi_Semantics_Framework.VAL_T) (b3)))))))))))))) ((fn b5 => CG_Phi_Semantics_Framework.Return_ (CG_Phi_Semantics_Framework.phi_arg.phi_arg_ (CG_Phi_Semantics_Framework.unreachable_))))))) (b2)))
end\<close>

ML \<open>#lookupStruct (ML_Name_Space.global_values []) "PhiSem_CF_Basic"\<close>
ML \<open>#allStruct (ML_Name_Space.global_values []) ()
      |> List.app (fn (a,_) => tracing a)\<close>
 
declare [[\<phi>export_code ]]

end
