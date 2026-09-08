structure C'G_Groups = struct
structure one_class = struct val one_ = 1 end
structure zero_class = struct val zero_ = 0 end
end

structure C'G_Nat = struct fun Suc_ i = i+1; val nat_K = Phi_CG.key_int end

structure C'G_Product_Type = struct
fun prod_T f g = f #-> (fn a => g #-> (fn b => pair (Phi_CG.V2 (a,b))))
val unit_T : Phi_CG.ty = pair Phi_CG.V0
val Unity_ = Phi_CG.V0
val Pair_ = pair
val prod_K = fn _ => pair NONE   (*a pair parameter has no text yet*)
end

structure C'G_Option = struct structure option = struct val None_ = NONE; val Some_ = SOME end
  val option_K = fn _ => pair NONE   (*an option parameter has no text yet*) end

(* structure TyCG_Word = struct val word = NuCG.T_int end *)

structure C'G_Numeral_Type =
  struct val num0_ = 0; val num1_ = 1; fun bit0_ x = x + x; fun bit1_ x = x + x + 1 end

structure C'G_Num = struct
structure numeral_class = struct val numeral_ = I end
structure num = struct val One_ = 1; fun Bit0_ x = x + x; fun Bit1_ x = x + x + 1 end
end

structure C'G_HOL = struct val Trueprop_ = I; val True_ = true; val False_ = false; val bool_K = Phi_CG.key_bool end

(*a procedure-valued parameter has no text (a later hook may run it on placeholders instead)*)
val C'G_fun_K = fn _ => pair NONE
structure C'G_Finite_Map = struct val fmempty_ = []; fun fmupd_ k v L = (k,v)::L end

(*a TYPE parameter of a len-sorted type variable is a width code (int.ML)*)
structure C'G_Type_Length = struct structure len0_class = struct val len_of_ = I end; val len_K = Phi_CG.key_int end

structure C'G_Power = struct structure power_class = struct
  fun power_ b e = if e <= 0 then 1 else b * power_ b (e - 1)
end end
