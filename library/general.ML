signature NU_GENERAL = sig
  val repeat_n : int -> ('a -> 'a) -> 'a -> 'a
end
structure NuGeneral : NU_GENERAL = struct
fun repeat_n n f x = if n <= 0 then x else repeat_n (n-1) f (f x)
end
