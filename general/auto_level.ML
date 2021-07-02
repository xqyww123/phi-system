(* auto level: 2 - fully auto, 1 - paritally auto, 0 - fully manual *)
signature AUTO_LEVEL = sig
  val get : Proof.context -> int
  val put : int -> Proof.context -> Proof.context
  val reduce : int -> Proof.context -> Proof.context
end
structure AutoLevel : AUTO_LEVEL = struct
structure Data = Generic_Data
(
  type T = int
  val empty: T = 2
  val extend = I
  val merge : T * T -> T = Int.min
)
val get = Data.get o Context.Proof
val put = Context.proof_map o Data.put
fun reduce i ctx = put (Int.min (i,get ctx)) ctx
end
