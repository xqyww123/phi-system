signature PHI_ID = sig

type ID
  (*The address of a statement or of one operation within it, inside a named construct
    (a phi procedure): the construct's full name ("" while no construct has been
    entered -- such an anonymous ID mints no key), a path of counters -- one level per
    nested block or per-line expression chain, INNERMOST LEVEL FIRST, the system-wide
    convention; presentation reverses it -- and the obligation counter of this address.
    Every value-level construction (next/step_in/nth_child/set_construct_v) starts a
    fresh counter.  Carrying an ID value around (set_expr_id, eval_cfg record literals)
    must NEVER rebuild it: obligation streams sharing one address share its numbering
    exactly because they share the value.*)
type key_spec
  (*How one obligation is keyed in the proof store: a structural key minted from an ID,
    a name given by a deriver, or no key.  Constructed ONLY by mint/named/no_key.*)

(* value level *)
val next            : ID -> ID
val step_in         : ID -> ID
val nth_child       : int -> ID -> ID       (*= funpow i next o step_in; i < 0 is an error*)
val set_construct_v : string -> ID -> ID    (*expects a full name; fails if already set*)
val path            : ID -> int list
  (*innermost level first; the only read-out of an ID's content*)

(* minting *)
val mint       : ID -> key_spec
  (*anonymous construct: no key, no tick; named: ticks the ID's counter and encodes*)
val named      : string -> key_spec
val no_key     : key_spec
val key_string : key_spec -> string option  (*the only conversion to a store key*)

(* context level *)
val get           : Proof.context -> ID
val set_construct : string -> Proof.context -> Proof.context
val next_ctxt     : Proof.context -> Proof.context
val step_in_ctxt  : Proof.context -> Proof.context

end

fun rev_map _ ret [] = ret
  | rev_map f ret (a::b) = rev_map f (f a :: ret) b

structure Phi_ID : PHI_ID = struct

type ID = string (*construct*) * int list (*path, innermost first*)
        * int Unsynchronized.ref (*obligation counter*)
  (*The counter needs no synchronization: keys are minted synchronously before any
    proof fork (Phi_Envir passes them through); there is no concurrent tick path.*)

datatype key_spec = Structural of string | Named of string | No_Key

fun next (c, i::p, _) = (c, i+1::p, Unsynchronized.ref 0)
  | next (_, [], _) = error "BUG: the path of a Phi_ID cannot be empty"

fun step_in (c, p, _) = (c, 0::p, Unsynchronized.ref 0)

fun nth_child i id =
  if i < 0 then error "BUG: nth_child expects a non-negative index"
  else funpow i next (step_in id)

fun set_construct_v name ("", _, _) = (name, [0], Unsynchronized.ref 0)
  | set_construct_v _ _ = error "Construct has been set in this context"

fun path (_, p, _) = p

fun mint ("", _, _) = No_Key
  | mint (c, p, counter) =
      let val n = !counter
          val _ = counter := n + 1
       in Structural (String.concatWith "/" (c :: rev_map string_of_int [] p)
                      ^ ":" ^ string_of_int n)
      end

val named = Named
val no_key = No_Key

fun key_string (Structural s) = SOME s
  | key_string (Named s) = SOME s
  | key_string No_Key = NONE

structure ID = Proof_Data (
  type T = ID
  fun init _ = ("", [0], Unsynchronized.ref 0)
    (*fresh cell per context on purpose: `val init = K ...` would evaluate the ref
      once and share it process-wide*)
)

val get = ID.get

fun set_construct name ctxt =
  ID.map (set_construct_v
            (if name = "" then ""
             else Sign.full_bname (Proof_Context.theory_of ctxt) name)) ctxt

val next_ctxt = ID.map next
val step_in_ctxt = ID.map step_in

end
