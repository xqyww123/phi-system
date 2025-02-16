fun dest_synt_numeral (Const (\<^const_syntax>\<open>zero_class.zero\<close>, _)) = 0
  | dest_synt_numeral (Const (\<^const_syntax>\<open>one_class.one\<close>, _)) = 1
  | dest_synt_numeral (Const (\<^const_syntax>\<open>num.One\<close>, _)) = 1
  | dest_synt_numeral (Const (\<^const_syntax>\<open>num.Bit0\<close>, _) $ bs) = 2 * dest_synt_numeral bs
  | dest_synt_numeral (Const (\<^const_syntax>\<open>num.Bit1\<close>, _) $ bs) = 2 * dest_synt_numeral bs + 1
  | dest_synt_numeral (Const (\<^const_syntax>\<open>numeral_class.numeral\<close>, _) $ X) = dest_synt_numeral X
  | dest_synt_numeral (Const (\<^const_syntax>\<open>Suc\<close>, _) $ X) = dest_synt_numeral X + 1
  | dest_synt_numeral t = raise TERM ("dest_num", [t])

local

val numT = Type ("Num.num", []);

val one_const = Const ("Num.num.One", numT)
and bit0_const = Const ("Num.num.Bit0", numT --> numT)
and bit1_const = Const ("Num.num.Bit1", numT --> numT)

in
fun mk_numeral_nat 0 = \<^term>\<open>0::nat\<close>
  | mk_numeral_nat 1 = \<^term>\<open>1::nat\<close>
  | mk_numeral_nat i =
  let
    fun mk 1 = one_const
      | mk i =
          let
            val (q, r) = Integer.div_mod i 2
          in (if r = 0 then bit0_const else bit1_const) $ mk q end
  in
    if i > 0
    then \<^term>\<open>numeral::num \<Rightarrow> nat\<close> $ mk i 
    else raise TERM ("mk_numeral: " ^ string_of_int i, [])
  end
end
