(*
A modified version of the `Item_Net`, where elements are sorted according to
cost rather than order of insertion.
*)

signature COST_NET =
sig
  type cost = int
  type 'a T
  val init: ('a * 'a -> bool) -> ('a -> term list) -> 'a T
  val is_empty: 'a T -> bool
  val content: 'a T -> (cost * 'a) list
  val length: 'a T -> int
  val retrieve: 'a T -> term -> (cost * 'a) list
  val retrieve_matching: 'a T -> term -> (cost * 'a) list
  val member: 'a T -> 'a -> bool
  val lookup: 'a T -> 'a -> (cost * 'a) list
  val merge: 'a T * 'a T -> 'a T
  val remove: 'a -> 'a T -> 'a T
  val update: (cost * 'a) -> 'a T -> 'a T
  val filter: ('a -> bool) -> 'a T -> 'a T
end;

structure Cost_Net : COST_NET =
struct

(* datatype *)
type cost = int
datatype 'a T =
  Items of {
    eq: 'a * 'a -> bool,
    index: 'a -> term list,
    content: (cost * 'a) list,
    net: (cost * 'a) Net.net};

fun mk_items eq index content net =
  Items {eq = eq, index = index, content = content, net = net};

fun init eq index = mk_items eq index [] Net.empty;
fun is_empty (Items {content, ...}) = null content;

fun content (Items {content, ...}) = content;
fun length items = List.length (content items);
fun retrieve (Items {net, ...}) = sort (int_ord o apply2 fst) o Net.unify_term net;
fun retrieve_matching (Items {net, ...}) = sort (int_ord o apply2 fst) o Net.match_term net;


(* standard operations *)
fun cost_eq eq (b,(_,a)) = eq (b,a)
fun member (Items {eq, index, content, net, ...}) x =
  (case index x of
    [] => Library.member (cost_eq eq) content x
  | t :: _ => exists (fn y => cost_eq eq (x, y)) (Net.unify_term net t));

fun lookup (Items {eq, index, content, net, ...}) x =
  (case index x of
    [] => content
  | t :: _ => Net.unify_term net t)
  |> filter (fn y => cost_eq eq (x, y));

fun cons (cost,x) (Items {eq, index, content, net}) =
  mk_items eq index ((cost,x) :: content)
    (fold (fn t => Net.insert_term (K false) (t, (cost, x))) (index x) net);

fun merge (items1, items2) =
  if pointer_eq (items1, items2) then items1
  else if is_empty items1 then items2
  else fold_rev (fn (cost,y) => if member items1 y then I else cons (cost,y)) (content items2) items1;

fun remove x (items as Items {eq, index, content, net}) =
  if member items x then
    mk_items eq index (Library.remove (cost_eq eq) x content)
      (fold (fn t => Net.delete_term_safe (eq o apply2 #2) (t, (0, x))) (index x) net)
  else items;

fun update (cost,x) items = cons (cost,x) (remove x items);

fun filter pred items =
  fold (fn (_,x) => not (pred x) ? remove x) (content items) items;

end;
