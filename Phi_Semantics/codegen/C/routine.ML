structure C'G_PhiSem_CF_Routine = struct local open Phi_C'G in

fun call name T v = var T (puts([name,"("] @ pV v @ [");\n"]))

(*the body is the routine's, or, given the name of a function to forward to, a call of it*)
fun op_rec_routine_ _ aG Ta Tb F = new_fun (fn N => fn fwd =>
  fold_map I Ta #-> (fn ta => fold_map I Tb #-> (fn tb =>
  let fun chk1 [x] = x | chk1 [] = ["void"] | chk1 _ = error ("multi-return in "^N)
      val vs = map_index (fn (i,_) => "_v"^ string_of_int i) ta
      val args = catw ", " (map2 (fn t => fn v => cat t ^" "^ v) ta vs)
      val call = call N (pair (chk1 tb))
      val body = case fwd
        of NONE => aG #-> F call (bk "return") #-> (fn V0 => I | v => puts(["return "]@ pV v @[";\n"]))
         | SOME m => puts ((if chk1 tb = ["void"] then [] else ["return "]) @ [m, "(", catw ", " vs, ");\n"])
   in puts (chk1 tb @[" ",N,"(", args, ") {\n"]) #> body #> put "}\n\n" #> pair call end)))

fun op_routine_ rG aG ta tb F = op_rec_routine_ rG aG ta tb (K F)

end end
