structure C'G_PhiStd_Slice_a = struct local open Phi_C'G in
fun memcpy_a_ T (V2(dst, V2(src, len))) = T #-> (fn t =>
      puts'' (["memcpy(", dV dst, ", ", dV src, ", ", dV len, " * sizeof("] @t@ ["))"]))
end end
