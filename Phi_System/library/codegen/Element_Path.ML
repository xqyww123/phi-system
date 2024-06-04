structure CG_Phi_Element_Path =
  struct datatype agidx = AgIdx_N_ of int | AgIdx_S_ of string | AgIdx_V_ of string end

(* signature CG_EP = sig val eleidx : CG_Phi_Element_Path.agidx list -> string list end *)