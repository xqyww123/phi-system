structure C'G_PhiSem_CF_Routine = struct local open Phi_C'G in

fun call name T v = if v = V0 then pair v else var T (puts([name,"("] @ pV v @ [");\n"]))

fun op_rec_routine_ _ aG Ta Tb F = fun_name () (new_fun (fn N =>
  fold_map I Ta #-> (fn ta => fold_map I Tb #-> (fn tb =>
  let fun chk1 [x] = x | chk1 [] = ["void"] | chk1 _ = error ("multi-return in "^N)
      val args = catw ", " (map_index (fn (i,t) => cat t ^" v"^ string_of_int i) ta)
      val call = call N (pair (chk1 tb))
   in puts (chk1 tb @[" ",N,"(", args, ") {\n"]) #> aG #-> F call (bk "return")
  #-> (fn V0 => I | v => puts(["return "]@ pV v @[";\n"]) ) #> put "}\n\n" #> pair call end))))

fun op_routine_ rG aG ta tb F = op_rec_routine_ rG aG ta tb (K F)

end end
