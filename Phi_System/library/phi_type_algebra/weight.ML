signature PHI_TYPE = sig

datatype weight = Weight of int | Lexical_W | Not_Assigned_W
datatype weight'= Static_W of weight | Dynamic_W of (Context.generic -> term -> weight)

val weight_geq : term * term -> weight * weight -> bool
val weight_of : Context.generic -> term -> weight
val assign_weight : term -> weight' -> Context.generic -> Context.generic

end

structure Phi_Type : PHI_TYPE = struct

datatype weight = Weight of int | Lexical_W | Not_Assigned_W
datatype weight'= Static_W of weight | Dynamic_W of (Context.generic -> term -> weight)
(* the lexical order considers the term of the operator but not the operands *)

fun weight_geq _ (_, Not_Assigned_W) = false
  | weight_geq _ (Not_Assigned_W, _) = false
  | weight_geq (opra, oprb) (Lexical_W, Lexical_W) = Term_Ord.term_ord (opra, oprb) <> LESS
  | weight_geq _ (Lexical_W, _) = true
  | weight_geq _ (_, Lexical_W) = false
  | weight_geq _ (Weight a, Weight b) = a >= b

fun weight'_eq (Static_W a, Static_W b) = a = b
  | weight'_eq (Dynamic_W _, Dynamic_W _) = true
  | weight'_eq _ = false

fun eval_weight _ _ (Static_W w) = w
  | eval_weight ctxt term (Dynamic_W f) = f ctxt term

val record_eq = eq_pair (op aconv) weight'_eq

structure Weights = Generic_Data (
  type T = (term * weight') Net.net
  val empty = Net.empty
  val merge = Net.merge record_eq
)

fun weight_of ctxt term
  = Net.match_term (Weights.get ctxt) term
 |> map_filter (fn (tm, w) => if Pattern.matches (Context.theory_of ctxt) (tm, term)
                              then SOME (eval_weight ctxt term w)
                              else NONE)
 |> distinct (op =)
 |> (fn [w] => w
      | [] => Not_Assigned_W
      | _ => raise TERM ("Multiple different weight!", [term]))

fun assign_weight term w
  = Weights.map (Net.insert_term record_eq (term, (term, w)))

end