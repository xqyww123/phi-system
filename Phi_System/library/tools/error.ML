(* FILE: library/tools/error.ML
   AUTHOR: Authors of Submission 96

   An unfinished error mechanism for IDE-CP.
*)

signature PHI_ERROR = sig

exception CastFail of (*place*) string * (*desired*) cterm * (*sequent*) thm
exception ReasoningFail of thm

val register_handler : ((exn -> unit) -> exn -> unit) -> theory -> theory
val handle_errors_toplevel : theory -> (unit -> 'a) -> 'a

end

structure Phi_Error : PHI_ERROR = struct
exception CastFail of (*name*) string * (*desired*) cterm * (*sequent*) thm
exception ReasoningFail of thm


(*THIS MERGE IS WRONG! ! ! !*)
fun merge (f,g) = (fn c => fn e => f (g c) e)

structure D = Theory_Data(struct
  type T = (exn -> unit) -> exn -> unit
  val empty = I
  val merge = merge
end)

fun handle_errors_toplevel thy f =
  Runtime.exn_trace (fn _ => f ())
  handle e =>
    (D.get thy (fn e => raise e) e; error "BUG: bad error handle!")

fun register_handler f = D.map (fn g => merge (f,g))

val _ = Theory.setup (
  register_handler (fn c => fn e =>
    case e of CastFail (name,d,t) =>
                  raise THM ("Fail to cast the "^name, 0, [Drule.mk_term d, t])
            | _ => c e)
)

end