structure CG_Phi_Semantics_Framework = struct local open Phi_CG in

val phi_V_none_  = V0; fun phi_V_pair_ a b = V2(a,b)
fun phi_V_fst_ (V2(x,_)) = x | phi_V_fst_ V0 = V0; fun phi_V_snd_ (V2(_,y)) = y | phi_V_snd_ V0 = V0
fun phi_V_case_prod_ f v = case v of V2(x,y) => f x y | V0 => f V0 V0
val VAL_T = assign_var #> apfst V
val phi_V_nil_ = V0; fun phi_V_cons_ a b = V2(a,b);
val phi_V_hd_ = phi_V_fst_ ; val phi_V_tl_ = phi_V_snd_
fun Return_ v c = (v,c); fun bind_ f g = f #-> (fn v => put "\n" #> g v)

val unreachable_ = V0; structure phi_arg = struct val phi_arg_ = I end

end end