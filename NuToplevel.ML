(*  Title:      NuSys.ML
    Author:     Qiyuan Xu

The toplevel structure of the ν-system.

`begin_proc (name, [(register name, (abstractor, image))])`
    starts the block for procedure constrruction. The block is based on `notepad`. 

*)

signature NU_TOPLEVEL = sig
  type state = Proof.state
  val begin_proc : (binding * (string * (string * string)) list) -> state -> state
  val end_proc : state -> state
  val 
  
end
