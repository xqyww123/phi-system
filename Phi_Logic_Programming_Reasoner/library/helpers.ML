signature PHI_REASONER_HELPERS = sig

val pos_parser : string -> Position.T parser

end

structure Phi_Reasoner_Helpers : PHI_REASONER_HELPERS = struct

fun pos_parser name =
  let val msg = name ^ " cannot capture the position of your rule \
                  \when no argument is given to the attribute.\n\
                  \Please use \<open>" ^ name ^" add\<close> to address it.\n\
                  \The recorded position can be very helpful for debuging, albeit it \
                  \is not mandatory.\n\
                  \It is a technical limitation of Isar."
   in fn x => let val pos = Token.pos_of (hd x)
                  val _ = if pos = Position.none
                          then warning msg
                           else ()
               in (pos,x) end
  end
end
