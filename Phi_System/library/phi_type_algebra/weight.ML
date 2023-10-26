signature PHI_TYPE = sig
include PHI_TYPE

datatype weight = Weight of int * term ord | Leaf_W | Undefined_W
datatype weight'= Static_W of weight
                | Dynamic_W of (Context.generic -> PLPR_Pattern.bv_typs * term (*\<phi>-type operator*) -> weight)
(*A weight cannot be greater than 10000.
  The default weight is Undefined_W

  Two syntactically non-identical \<phi>-type (T,U) operators may have identical weight, if so, they should be either
  1. non-commutative between each other
  2. their commutativity are always identical to any other \<phi>-types, i.e.,
     \<forall>W. commutative(T,W) \<longleftrightarrow> commutative(U,W)
  3. they never occur simultaneously in a \<phi>-type, otherwise, normalization would be incomplete.

  \<phi>-Types may in addition provide a term order, to fine control the weight order between two operators
  having an identical weight. Note we always use the order of \<open>T\<close> when determining \<open>T > U\<close>.
*)


val weight_gt : term * term -> weight * weight -> bool
val weight_of : Context.generic -> PLPR_Pattern.bv_typs * term -> weight
val assign_weight : term -> weight' -> Context.generic -> Context.generic

val require_weight_normalization : Context.generic -> PLPR_Pattern.bv_typs * term -> bool

val ML_sender__weight_ord : term ord option Unsynchronized.ref
val ML_sender__dynamic_weight : (Context.generic -> PLPR_Pattern.bv_typs * term -> weight) option Unsynchronized.ref

val weight_synt : (Context.generic -> weight) parser
val dynamic_weight_synt : (Context.generic -> weight') parser

end

structure Phi_Type : PHI_TYPE = struct
open Phi_Type

datatype weight = Weight of int * term ord | Leaf_W | Undefined_W
datatype weight'= Static_W of weight | Dynamic_W of (Context.generic -> PLPR_Pattern.bv_typs * term -> weight)
(* the lexical order considers the term of the operator but not the operands *)

fun leading_term_name (X $ _) = leading_term_name X
  | leading_term_name (Abs(_,_,X)) = leading_term_name X
  | leading_term_name (Free (N,_)) = N
  | leading_term_name (Const (N,_)) = N
  | leading_term_name _ = ""
  

(* Leaf_W > > Weight, no (>) for Undefined_W *)
fun weight_gt _ (_, Undefined_W) = false
  | weight_gt _ (Undefined_W, _) = false
  | weight_gt _ (_, Leaf_W) = false
  | weight_gt _ (Leaf_W, _) = true
  | weight_gt (opra, oprb) (Weight (a, orda), Weight (b, _)) =
      if a = b then orda (opra, oprb) = GREATER
               else a > b

fun weight_eq (Weight (ia,oa), Weight (ib,ob)) = ia = ib andalso pointer_eq (oa,ob)
  | weight_eq (Leaf_W, Leaf_W) = true
  | weight_eq (Undefined_W, Undefined_W) = true
  | weight_eq _ = false

fun weight'_eq (Static_W a, Static_W b) = weight_eq (a,b)
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
   |> distinct weight_eq
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
      exists (fn (F,Gs) => forall (fn G => weight_gt (F,G) (w_of (bvtys,F), w_of (bvtys,G))) Gs)
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

val ML_parser_locker__weight = Synchronized.var "\<phi>Type.ML_parser_locker__weight" ()
val ML_sender__weight_ord : term ord option Unsynchronized.ref = Unsynchronized.ref NONE
val ML_sender__dynamic_weight : (Context.generic -> PLPR_Pattern.bv_typs * term -> weight) option Unsynchronized.ref
      = Unsynchronized.ref NONE

val weight_synt = 
      Args.$$$ "leaf" >> K (K Leaf_W)
   || Args.$$$ "undefined" >> K (K Leaf_W)
   || Args.$$$ "_" >> K (K Leaf_W)
   || Reasoner_Group.parser >> (fn w => fn ctxt =>
          Weight (fst (Reasoner_Group.check_priority true ctxt w), K EQUAL))
   || \<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>,\<close> --| Args.$$$ "lexical" --| \<^keyword>\<open>)\<close> >>
      (fn w => fn ctxt =>
          Weight (fst (Reasoner_Group.check_priority true ctxt w), Term_Ord.term_ord))
   || \<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>,\<close> -- Parse.ML_source --| \<^keyword>\<open>)\<close> >>
      (fn (w,src) => fn ctxt =>
          Synchronized.change_result ML_parser_locker__weight (fn () =>
            let val _ = ctxt
                     |> ML_Context.expression (Input.pos_of src)
                       (ML_Lex.read "Phi_Type.ML_sender__weight_ord := SOME ((" @
                        ML_Lex.read_source src @
                       ML_Lex.read ") : term ord)")
                val ml = the (!ML_sender__weight_ord)
                val _ = ML_sender__weight_ord := NONE
             in (Weight (fst (Reasoner_Group.check_priority true ctxt w), ml), ())
            end
          ))

val dynamic_weight_synt =
     weight_synt >> (fn w => Static_W o w)
  || Parse.ML_source >> (fn src => fn ctxt =>
        Synchronized.change_result ML_parser_locker__weight (fn () =>
          let val _ = ctxt
                   |> ML_Context.expression (Input.pos_of src)
                     (ML_Lex.read "Phi_Type.ML_sender__dynamic_weight := SOME ((" @
                      ML_Lex.read_source src @
                     ML_Lex.read ") : Context.generic -> PLPR_Pattern.bv_typs * term -> Phi_Type.weight)")
              val ml = the (!ML_sender__dynamic_weight)
              val _ = ML_sender__dynamic_weight := NONE
           in (Dynamic_W ml, ())
          end
          )
      ) 


end