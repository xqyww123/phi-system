signature C'G_PhiSem_Aggregate_Named_Tuple = sig
include PHI_C'G
val semty_ntup_ : (string * T) list -> T
val semantic_named_tuple_constructor_ : string list -> V list -> T -> M
end