structure C'G_Phi_Semantics_Framework = struct local open Phi_CG in

val phi_V_none_  = V0; fun phi_V_pair_ a b = V2(a,b)
fun phi_V_fst_ (V2(x,_)) = x | phi_V_fst_ V0 = V0; fun phi_V_snd_ (V2(_,y)) = y | phi_V_snd_ V0 = V0
fun phi_V_case_prod_ f v = case v of V2(x,y) => f x y | V0 => f V0 V0
val VAL_T = assign_var #> apfst V
val phi_V_nil_ = V0; fun phi_V_cons_ a b = V2(a,b);
val phi_V_hd_ = phi_V_fst_ ; val phi_V_tl_ = phi_V_snd_
fun Return_ v c = (v,c); fun bind_ (f : M) (g : V -> M) : M = f #-> g

val unreachable_ = V0; structure phi_arg = struct val phi_arg_ = I end

(*parameter texts: a semantic type by its C spelling, printed in the live context so that the
  typedef it may create is memoised and the name stays stable; a value shape by the V its
  printer produces, run in a scratch context since it allocates variables*)
val TY_K = key_strs
fun FIX_ARITY_VALs_K (P : ty) : keyp = fn c =>
  let fun shape (V _) = "V" | shape V0 = "0" | shape (V2 (a,b)) = "(" ^ shape a ^ "," ^ shape b ^ ")"
      val (_,_,ftab,ss,_,_) = c
      val (v, (out,_,_,_,_,_)) = P ([[]], NONE, ftab, ss, 0, Anonymous)
   in if out = [[]] then (SOME (shape v), c) else error "a value-shape printer must not print" end

end end