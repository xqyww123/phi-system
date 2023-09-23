signature HASHER = sig

type digest = string
val string : string -> digest
val class : class -> digest
val sort  : sort -> digest
val typ  : typ -> digest
val term : term -> digest
val goal : context_state -> digest

end

structure Hasher : HASHER = struct

type digest = string

fun typ_str (Type (N,TYs)) ret = fold (typ_str) TYs (N::ret)
  | typ_str (TFree (N,S)) ret = N::S@ret
  | typ_str (TVar ((N,i),S)) ret = N::string_of_int i::S@ret

fun term_str (Const (N,T)) ret = typ_str T (N::ret)
  | term_str (Free (N,T)) ret = typ_str T (N::ret)
  | term_str (Var ((N,i),T)) ret = N::string_of_int i::typ_str T ret
  | term_str (Bound i) ret = string_of_int i :: ret
  | term_str (Abs (N,T,X)) ret = term_str X (typ_str T (N :: ret))
  | term_str (A $ B) ret = term_str A (term_str B ret)

fun string s = SHA1.digest s |> SHA1.rep
fun hash strs = SHA1.digest (String.concat strs) |> SHA1.rep

val class = string
val sort = hash
fun typ ty = hash (typ_str ty [])
fun term term = hash (term_str term [])

fun goal (ctxt,stat) =
  hash (fold (term_str o Thm.term_of) (Assumption.all_assms_of ctxt)
             (Context.theory_name {long=false} (Proof_Context.theory_of ctxt) :: term_str (Thm.prop_of stat) []))

(* TOO SLOW:
fun typ (Type (N,TYs)) = fold (curry hashOne o typ) TYs (hashOne (wordP1, string N))
  | typ (TFree (N,S)) = hashOne (wordP2, hashOne (string N, sort S))
  | typ (TVar (N,S)) = hashOne (wordP3, hashOne (hash_index_name N, sort S))

fun term (Const (N,T)) = hashOne (wordP1, hashOne (string N, typ T))
  | term (Free (N,T)) = hashOne (wordP2, hashOne (string N, typ T))
  | term (Var (N,T)) = hashOne (wordP3, hashOne (hash_index_name N, typ T))
  | term (Bound i) = hashOne (wordP4, Word64.fromInt i)
  | term (Abs (N,T,X)) = hashOne (wordP5, hashOne (string N,
                                hashOne (typ T, term X)))
  | term (A $ B) = hashOne (wordP6, hashOne (term A, term B))

fun fast_term' 0 _ = word0
  | fast_term' _ (Const (N,_)) = hashOne (wordP1, string N)
  | fast_term' _ (Free (N,_)) = hashOne (wordP2, string N)
  | fast_term' _ (Var (N,_)) = hashOne (wordP3, hash_index_name N)
  | fast_term' _ (Bound i) = hashOne (wordP4, Word64.fromInt i)
  | fast_term' i (Abs (N,T,X)) = hashOne (wordP5, fast_term' i X)
  | fast_term' i (A $ B) = hashOne (wordP6, hashOne (fast_term' (i-1) A, fast_term' (i-1) B))

val fast_term = fast_term' 1000 *)

end