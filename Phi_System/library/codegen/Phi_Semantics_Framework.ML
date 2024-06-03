structure CG_Phi_Semantics_Framework = struct local open Phi_CG in

val phi_V_none  = V ""; val phi_V_pair = V2; fun phi_V_fst (V2(x,_)) = x; fun phi_V_snd (V2(_,y)) = y
fun phi_V_case_prod f (V2(x,y)) = f x y; val VAL_genT = assign_var #> apfst V
val phi_V_nil = V ""; fun phi_V_cons a b = V2(a,b); val phi_V_hd = phi_V_fst ; val phi_V_tl = phi_V_snd
val Return = I; fun bind f g = f #-> (fn v => put "\n" #> g v)

end end