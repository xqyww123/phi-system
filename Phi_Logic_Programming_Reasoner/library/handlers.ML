signature PLPR_HANDLERS_ARG = sig

type domT
type retT
val default : domT -> retT
val current_level : Proof.context -> int
val ctxt_of : domT -> Proof.context

end

signature PLPR_HANDLERS = sig

structure Arg : PLPR_HANDLERS_ARG

val push : (Arg.domT -> Arg.retT option) -> Proof.context -> serial * Proof.context
val push_localctxt : int -> (Arg.domT -> Arg.retT option) -> Proof.context -> serial * Proof.context
val remove : serial -> Proof.context -> Proof.context
val invoke : Proof.context -> Arg.domT -> Arg.retT

end

functor PLPR_Handlers(Arg : PLPR_HANDLERS_ARG) : PLPR_HANDLERS = struct

structure Data = Proof_Data (
  type T = serial * (serial * (Arg.domT -> Arg.retT option)) list
  val init = K (0,[])
)

fun push h ctxt =
  let val (serial, L) = Data.get ctxt
   in (serial, Data.put (serial + 1, (serial, h) :: L) ctxt) end

(*delt: 0 for the current reasoning context
        1 for the sub-calling environment (children of the current context)*)
fun push_localctxt delt h ctxt =
  let val lev = Arg.current_level ctxt + delt
      val _ = if lev = 0 then error "Not in PLPR reasoning environment" else ()
   in push (fn a =>
        if lev = Arg.current_level (Arg.ctxt_of a)
        then h a
        else NONE) ctxt
  end

fun remove serial = Data.map (apsnd (filter_out (fn (s, _) => s = serial)))

fun invoke ctxt arg =
  let fun call [] = Arg.default arg
        | call ((_,h)::L) = case h arg
                              of SOME ret => ret
                               | NONE => call L
   in call (snd (Data.get ctxt))
  end

structure Arg = Arg

end