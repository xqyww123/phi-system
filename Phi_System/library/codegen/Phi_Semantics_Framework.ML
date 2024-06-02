structure CG_Phi_Semantics_Framework = struct local open Phi_CodeGen in

val phi_V_none  = () ; val phi_V_pair = pair ; val phi_V_fst = fst ; val phi_V_snd = snd
fun phi_V_case_prod f (x,y) = f x y
val phi_V_nil = [] ; val phi_V_cons = (::) ; val phi_V_hd = hd ; val phi_V_tl = tl
val Return = I; fun bind f g = f #-> (fn v => put "\n" #> g v)

end end