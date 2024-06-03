structure CG_Groups = struct
structure one_class = struct val one_gen = 1 end
structure zero_class = struct val zero_gen = 0 end
end

structure CG_Product_Type =
  struct fun prod_genT f g = f #-> (fn a => g #-> (fn b => pair (Phi_CG.V2 (a,b)))) end

(* structure TyCG_Word = struct val word = NuCG.T_int end *)

structure CG_Numeral_Type =
  struct val num0 = 0; val num1 = 1; fun bit0 x = x + x; fun bit1 x = x + x + 1 end

structure CG_Num = struct
structure numeral_class = struct val numeral_gen = I end
structure num = struct val One_gen = 1; fun Bit0_gen x = x + x; fun Bit1_gen x = x + x + 1 end
end

structure CG_HOL = struct val Trueprop_gen = I; val True = ["True"]; val False = ["False"] end
structure Finite_Map = struct val fmempty = []; fun fmupd k v L = (k,v)::L end

