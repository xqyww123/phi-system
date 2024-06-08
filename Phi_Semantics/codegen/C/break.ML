structure C'G_PhiSem_CF_Break : C'G_PHISEM_CF_BREAK = struct fun op_break_ tr ta F v = F tr ta v end

structure C'G_PhiSem_CF_Breakable = struct local open Phi_C'G in

fun while_ c b = c #-> (fn v => puts ["while (", dV v, ") {\n"]
      #> b (bk "break ") (bk "continue") #> chkV0 #> c #-> (fn u => puts [dV v," = ",dV u,";\n}\n"]) #> pair V0)

end end
