signature BI_TREE = sig
  datatype ('a,'b) T =
    Leaf of ('a * 'b) | Node of ('a * ('a,'b) T * ('a,'b) T)
  val get_tag : ('a,'b) T -> 'a
  val set_tag : 'a -> ('a,'b) T -> ('a,'b) T
  val map_leaf : ('b -> 'b2) -> ('a,'b) T -> ('a,'b2) T
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
end
