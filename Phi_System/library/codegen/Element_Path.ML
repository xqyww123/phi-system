structure CG_Phi_Element_Path =
  struct datatype agidx = AgIdx_N of int | AgIdx_S of string | AgIdx_V of string end

(* signature CG_EP = sig val eleidx : CG_Phi_Element_Path.agidx list -> string list end *)