signature PHI_TYPE = sig
include PHI_TYPE

datatype weight = Weight of int | Lexical_W | Leaf_W | Undefined_W
datatype weight'= Static_W of weight
                | Dynamic_W of (Context.generic -> PLPR_Pattern.bv_typs * term (*\<phi>-type operator*) -> weight)

val weight_geq : term * term -> weight * weight -> bool
val weight_of : Context.generic -> PLPR_Pattern.bv_typs * term -> weight
val assign_weight : term -> weight' -> Context.generic -> Context.generic

val require_weight_normalization : Context.generic -> PLPR_Pattern.bv_typs * term -> bool

end

structure Phi_Type : PHI_TYPE = struct
open Phi_Type

datatype weight = Weight of int | Lexical_W | Leaf_W | Undefined_W
datatype weight'= Static_W of weight | Dynamic_W of (Context.generic -> PLPR_Pattern.bv_typs * term -> weight)
(* the lexical order considers the term of the operator but not the operands *)

(* Leaf_W > Lexical_W > Weight, no (\<ge>) for Undefined_W *)
fun weight_geq _ (_, Undefined_W) = false
  | weight_geq _ (Undefined_W, _) = false
  | weight_geq _ (_, Leaf_W) = false
  | weight_geq _ (Leaf_W, _) = true
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

fun pad_phi term =
  let val idx = maxidx_of_term term
      fun pad _ [] _ = raise TERM("not a \<phi>-type", [term])
        | pad _ [_] X = X
        | pad i (ty :: tys) X = pad (i+1) tys (X $ Var(("T",idx+i),ty))
   in pad 0 (binder_types (fastype_of term)) term
  end

fun weight_of ctxt=
  let val weights = Weights.get ctxt
   in fn (bvtys, term') =>
  let val term = pad_phi term'
   in Net.match_term weights term
   |> map_filter (fn (tm, w) => if Pattern.matches (Context.theory_of ctxt) (tm, term)
                                then SOME (eval_weight ctxt (bvtys, term') w)
                                else NONE)
   |> distinct (op =)
   |> (fn [w] => w
        | [] => Undefined_W
        | _ => raise TERM ("Multiple different weight!", [term']))
  end
  end

fun assign_weight term w
  = Weights.map (Net.insert_term record_eq (pad_phi term, (pad_phi term, w)))

fun require_weight_normalization ctxt =
  let val parse = parse_F_Gs_of_comm_typor_appl ctxt
      val w_of = weight_of ctxt
   in fn (bvtys, F_G_T) =>
      exists (fn (F,Gs) => forall (fn G => weight_geq (F,G) (w_of (bvtys,F), w_of (bvtys,G))) Gs)
             (parse (bvtys, F_G_T))
  end

(*
fun comm_weight_geq ctxt =
  let val comm = are_commutative ctxt
      val w_of = weight_of ctxt
   in fn bv_tys => fn (F,Gs) => 
      let val N = length Gs
          val (F', Gs') = (Logic.incr_indexes ([],[],1) F, map (Logic.incr_indexes ([],[],1)) Gs)
          val partial_F_G = List.tabulate (N, fn i =>
                let val G = nth Gs i
                    val ty = Term.fastype_of1 (bv_tys, G)
                 in fold_index (fn (j,G) => fn X => if j = i then X $ Bound 0 else X $ G) Gs' F'
                 |> (fn X => (Abs("G", ty, X), [G]) )
                end)
          val F_G_pairs = (F,Gs) :: partial_F_G
       in exists (fn (F,Gs) =>
            comm (F,Gs) andalso forall (fn G => weight_geq (F,G) (apply2 w_of (F,G))) Gs
          ) F_G_pairs
      end
  end
*)

end