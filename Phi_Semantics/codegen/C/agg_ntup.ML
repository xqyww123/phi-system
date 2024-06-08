structure C'G_PhiSem_Aggregate_Named_Tuple : C'G_PhiSem_Aggregate_Named_Tuple = struct open Phi_C'G
fun semty_ntup_ Ts = fold_map (fn (n,T) => T #> apfst (pair n)) Ts
       #-> (fn ts => defty (cat(["struct {"] @ maps (fn (n,t) => t@[" ",n,"; "]) (sort_by #1 ts) @ ["}"])))
fun semantic_named_tuple_constructor_ syms vs T =
      var T (puts(["{"]@ separate "," (map (dV o #2) (sort_by #1 (syms ~~ vs))) @["};\n"]))
end
