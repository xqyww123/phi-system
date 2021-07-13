signature BI_TREE = sig
  datatype ('a,'b) T =
    Leaf of ('a * 'b) | Node of ('a * ('a,'b) T * ('a,'b) T)
  val get_tag : ('a,'b) T -> 'a
  val set_tag : 'a -> ('a,'b) T -> ('a,'b) T
  val map_leaf : ('b -> 'b2) -> ('a,'b) T -> ('a,'b2) T
  (* val insert_balancedly : 'a -> ('a,'b) T -> ('a,'b) T *)
end
structure BiTree : BI_TREE = struct
datatype ('a,'b) T =
  Leaf of ('a * 'b) | Node of ('a * ('a,'b) T * ('a,'b) T)
fun get_tag (Leaf (t,_)) = t
  | get_tag (Node (t,_,_)) = t
fun set_tag t (Leaf (_,a)) = Leaf (t,a)
  | set_tag t (Node (_,l,r)) = Node (t,l,r)
fun map_leaf f (Leaf (t,v)) = Leaf (t, f v)
  | map_leaf f (Node (t,l,r)) = Node (t, map_leaf f l, map_leaf f r)

(* fun split_impl ret n l = if n = 0 then (ret,l) else split_impl (hd l ::ret) (n-1) (tl l)
fun split n l = split_impl [] n l
fun floor2n_i y x = if x <= (2*y) then y else floor2n_i (2*y) x
fun floor2n x = if x <= 1 then 0 else floor2n_i 1 x
fun cut_impl (len,n) ret l =
  if len <= 2 then rev(l::ret)
  else (case split (len-n) l of (L,R) => cut_impl (n,n div 2) (L::ret) R)
fun cut l = if null l then []
  else cut_impl (length l+1, floor2n (length l +1)) [] l

datatype btree = Node of (int * btree * btree) | Leaf of int | LeafNone
fun heap_impl merge ret ((a::b::l1)::(x::l2)::ll) =
      heap_impl merge (merge (x, SOME a, SOME b) ::ret) (l1::l2::ll)
  | heap_impl merge ret ([a]::(x::l2)::ll) =
      heap_impl merge (merge (x, SOME a, NONE) ::ret) ([]::l2::ll)
  | heap_impl merge ret ([]::(x::l2)::ll) =
      heap_impl merge (merge (x, NONE, NONE) ::ret) ([]::l2::ll)
  | heap_impl merge ret ([]::[]::ll) =
      heap_impl merge [] (rev ret ::ll)
  | heap_impl merge ret [[x]] = x
fun heap merge l = heap_impl merge [] (cut l)

fun resemble [x] = x
  | resemble (l::r::remain) = 
fun insert_balancedly_impl x () *)
end
