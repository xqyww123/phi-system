structure C'G_Phi_Element_Path = struct structure aggregate_index' = struct
 datatype agidx = AgIdx_N_ of int | AgIdx_S_ of string | AgIdx_V_ of string 
end open aggregate_index' end

(* signature CG_EP = sig val eleidx : CG_Phi_Element_Path.agidx list -> string list end *)