structure CG_Groups = struct
structure one_class = struct val one_ = 1 end
structure zero_class = struct val zero_ = 0 end
end

structure CG_Product_Type = struct
fun prod_T f g = f #-> (fn a => g #-> (fn b => pair (Phi_CG.V2 (a,b))))
val unit_T : Phi_CG.ty = pair Phi_CG.V0
end

structure CG_Option = struct structure option = struct val None_ = NONE; val Some_ = SOME end end

(* structure TyCG_Word = struct val word = NuCG.T_int end *)

structure CG_Numeral_Type =
  struct val num0_ = 0; val num1_ = 1; fun bit0_ x = x + x; fun bit1_ x = x + x + 1 end

structure CG_Num = struct
structure numeral_class = struct val numeral_ = I end
structure num = struct val One_ = 1; fun Bit0_ x = x + x; fun Bit1_ x = x + x + 1 end
end

structure CG_HOL = struct val Trueprop_ = I; val True_ = true; val False_ = false end
structure Finite_Map = struct val fmempty_ = []; fun fmupd_ k v L = (k,v)::L end

