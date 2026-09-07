structure C'G_PhiStd_Slice = struct local open Phi_C'G in
fun memcpy_ _ T (V2(dst, V2(src, len))) = T #-> (fn t =>
      puts'' (["memcpy(", dV dst, ", ", dV src, ", ", dV len, " * sizeof("] @t@ ["))"]))
end end
