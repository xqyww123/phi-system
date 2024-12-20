signature PHI_ID = sig

type construct = string
type ID = construct * int list
type encoded_ID = string

val cons : int list -> ID -> ID

val get : Proof.context -> ID
val get_if_is_named : Proof.context -> ID option
val set_construct : string -> Proof.context -> Proof.context
val step_in : Proof.context -> Proof.context
val next : Proof.context -> Proof.context

val encode : ID -> encoded_ID
val dep  : encoded_ID -> encoded_ID -> bool
val dep' : ID -> ID -> bool

val father : ID -> ID

structure Tab : TABLE

end

fun rev_map _ ret [] = ret
  | rev_map f ret (a::b) = rev_map f (f a :: ret) b

structure Phi_ID : PHI_ID = struct

type construct = string
type ID = construct * int list
type encoded_ID = string

fun father (c,[]) = (c,[])
  | father (c,p::r) = (c,r)

fun cons i (c,p) = (c,i@p)

structure ID = Proof_Data (
  type T = ID
  val init = K ("",[0])
)

val get = ID.get
fun get_if_is_named ctxt =
  let val id = get ctxt
   in if fst id = ""
      then NONE
      else SOME id
  end

fun set_construct name ctxt =
  ID.map (fn ("", _) =>
              if name = ""
              then ("",[0])
              else (Sign.full_bname (Proof_Context.theory_of ctxt) name, [0])
           | _ => error "Construct has been set in this context") ctxt

val step_in = ID.map (fn (c, p) => (c, 0::p))
val next = ID.map (fn (c, i::p) => (c, i+1::p))

fun encode (c,p) = String.concatWith "/" (c :: rev_map string_of_int [] p)

(* i \<le> j \<Longrightarrow> string_of_int i \<le> string_of_int j, if no leading zero *)
val int_string_ord = pointer_eq_ord (size_ord ||| string_ord)

fun dep ida idb =
  let val ha::ida' = String.fields (fn c => c = #"/") ida
      val hb::idb' = String.fields (fn c => c = #"/") idb
   in ha = hb andalso is_less_equal (dict_ord int_string_ord (ida',idb'))
  end

fun dep'' [ha] (hb::_) = ha <= hb
  | dep'' (ha::La) (hb::Lb) =
      if ha = hb then dep'' La Lb else false
  | dep'' _ _ = false

fun dep' (ca,pa) (cb,pb) = (ca = cb andalso dep'' (rev pa) (rev pb))

structure Tab = Table (type key = ID val ord = prod_ord string_ord (list_ord int_ord))

end