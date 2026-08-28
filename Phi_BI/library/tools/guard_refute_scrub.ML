(*  Title:      guard_refute_scrub.ML
    Author:     the phi-system project

Assuming inhabitation of an abstract phi-type when refuting a guard by model
search: a Phi_Guard_Refute preprocessing hook.  Measurements in
Docs/GUARD_NITPICK_FALSIFY_PLAN.md sections 20-21.

WHY.  Satisfiable (x : T) enters guards through Abstract_Domain: to fold or
unfold a phi-type assertion the reasoner must know the abstract values are
representable, and for an atomic phi-type the weakest such bound is exactly
their satisfiability.  Recursive structures multiply it -- a tree carries one
per node through pred_tree.  Nitpick cannot evaluate the atom (Phi_BI.thy:383
says as much: "should be always regarded as an atom in the view of ATPs"), so
it comes out unknown and an unknown premise poisons the implication.  Assuming
it costs 19 refutations of 223 on the measured corpus if dropped.

WHEN.  Only where the phi-type is a free or schematic VARIABLE.  Then the
guard cannot be constraining it and inhabitation is a fact of the program
state.  Where the phi-type is concrete the atom may carry real content, and
the same goes for the elementwise satisfaction  v |= (x : T)  of Array: that
one asks whether the UPDATED structure is still representable, a genuine
obligation, and is deliberately left alone.  Scrubbing it as well buys one
refutation of 223 and is not worth the exposure (author ruling 2026-08-28).

WHERE.  Positive positions only, and never the conclusion -- the hook is
handed premises alone.  Replacing a subformula by True in a positive position
weakens; in a negative one it would produce ~True = False, making the
premises contradictory and every guard vacuously true.
*)

structure Phi_Guard_Refute_Scrub =
struct

(*** Positive positions ***)

(*Which containers may be entered is not a fixed list: every (co)datatype
  registered with the BNF package exports a predicator and a relator whose
  predicate arguments are covariant, and the package proves it.  We admit a
  container only if the certificate is really there, so anything arriving by
  another route degrades to "not entered".  The sweep costs 3.93ms for 51
  datatypes (plan 20.4), so the table is built once per guard -- never cached
  across guards, and never rebuilt per premise.  Symtab, not a hash table:
  the walk queries 56680 constant occurrences of which 1% hit, and over that
  stream Symtab.lookup costs less than Hashers.string alone does, since
  fast_string_ord settles most misses on length while hashing must copy and
  scan the whole name (plan 22.5).*)

local

fun certificate_exists ctxt type_name suffix =
  is_some (try (Proof_Context.get_thm ctxt) (type_name ^ "." ^ suffix))

(*pred_inject / rel_inject read  pred_T P\<^sub>1 \<dots> P\<^sub>k (Ctr \<dots>) = \<dots>  : the head names
  the operator, its leading functional arguments count the predicate slots*)
fun head_and_slots th =
  (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.concl_of) th of
     SOME (lhs, _) =>
       (case strip_comb lhs of
          (Const (c, _), args) =>
            let
              fun is_predicate t = can dest_funT (fastype_of t)
              val k = length (take_prefix is_predicate args)
            in if k > 0 then SOME (c, k) else NONE end
        | _ => NONE)
   | NONE => NONE)

in

(*Keyed by constant name; the value is how many LEADING arguments are
  predicate slots, i.e. how far into the application the walk may descend --
  list_all2 P xs ys has one, pred_sum P Q (Inl a) has two.  The remaining
  arguments carry the data and are never entered.*)
fun container_table ctxt =
  let
    fun of_sugar (sugar : BNF_FP_Def_Sugar.fp_sugar) =
      let
        val bnf_sugar = #fp_bnf_sugar sugar
        val type_name = fst (dest_Type (#T sugar))
        fun entries certificate selector =
          if certificate_exists ctxt type_name certificate
          then map_filter head_and_slots (selector bnf_sugar) else []
      in entries "pred_mono_strong" #pred_injects @ entries "rel_mono" #rel_injects end
  in
    fold Symtab.update
      (maps of_sugar (BNF_FP_Def_Sugar.fp_sugars_of ctxt)) Symtab.empty
  end

end

(*Rewrite the subterms that sit where replacing them weakens.  `replace' sees
  only such subterms and answers SOME for the ones it wants gone.*)
fun at_positive containers replace t =
  let
    fun go positive t =
      (case (if positive then replace t else NONE) of
         SOME t' => t'
       | NONE =>
        (case t of
           Const (\<^const_name>\<open>HOL.conj\<close>, T) $ a $ b =>
             Const (\<^const_name>\<open>HOL.conj\<close>, T) $ go positive a $ go positive b
         | Const (\<^const_name>\<open>HOL.disj\<close>, T) $ a $ b =>
             Const (\<^const_name>\<open>HOL.disj\<close>, T) $ go positive a $ go positive b
         | Const (\<^const_name>\<open>HOL.implies\<close>, T) $ a $ b =>
             Const (\<^const_name>\<open>HOL.implies\<close>, T) $ go (not positive) a $ go positive b
         | Const (\<^const_name>\<open>HOL.Not\<close>, T) $ a =>
             Const (\<^const_name>\<open>HOL.Not\<close>, T) $ go (not positive) a
         | Const (\<^const_name>\<open>HOL.All\<close>, T) $ a =>
             Const (\<^const_name>\<open>HOL.All\<close>, T) $ go positive a
         | Const (\<^const_name>\<open>HOL.Ex\<close>, T) $ a =>
             Const (\<^const_name>\<open>HOL.Ex\<close>, T) $ go positive a
         | Const (\<^const_name>\<open>Ball\<close>, T) $ A $ a =>
             Const (\<^const_name>\<open>Ball\<close>, T) $ A $ go positive a
         | Const (\<^const_name>\<open>Bex\<close>, T) $ A $ a =>
             Const (\<^const_name>\<open>Bex\<close>, T) $ A $ go positive a
           (*Premise mode x \<equiv> x, hence monotone in x*)
         | Const (\<^const_name>\<open>Premise\<close>, T) $ mode $ a =>
             Const (\<^const_name>\<open>Premise\<close>, T) $ mode $ go positive a
           (*a predicate slot may be curried, as list_all2's (%x y. \<dots>) is*)
         | Abs (x, T, body) => Abs (x, T, go positive body)
         | _ =>
             (case strip_comb t of
                (head as Const (c, _), args) =>
                  (case Symtab.lookup containers c of
                     SOME k =>
                       if length args >= k
                       then
                         list_comb (head,
                           map_index (fn (i, a) => if i < k then go positive a else a) args)
                       else t
                   | NONE => t)
              | _ => t)))
  in go true t end


(*** The hook ***)

(*The True this leaves behind is not tidied up here.  Phi_Guard_Refute runs
  the simplifier over the result, and it collapses the debris on its own: the
  propositional laws are in every simpset, and the predicator law
  pred\<^sub>T (\<lambda>_. True) \<dots> = (\<lambda>_. True) is in the system simpset because
  Phi_Preliminary's BNF interpretation puts every datatype's pred_True there.
  A whole premise that became True IS dropped below -- a premise, unlike a
  subterm, costs the model search a formula.*)

fun is_true (Const (\<^const_name>\<open>True\<close>, _)) = true
  | is_true _ = false

fun assumed (Const (\<^const_name>\<open>Satisfiable\<close>, _) $
               (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T)) =
      if is_Free T orelse is_Var T then SOME \<^term>\<open>True\<close> else NONE
  | assumed _ = NONE

fun scrub ctxt prems =
  let
    (*the table costs a registry sweep, so it is built once per guard, not
      once per premise*)
    val containers = container_table ctxt
    fun one (Const (\<^const_name>\<open>Trueprop\<close>, T) $ t) =
          Const (\<^const_name>\<open>Trueprop\<close>, T) $ at_positive containers assumed t
      | one prem = prem
    fun vanished (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = is_true t
      | vanished _ = false
  in map one prems |> filter_out vanished end

val _ = Theory.setup (Context.theory_map (Phi_Guard_Refute.Preprocess_Hooks.add 100 scrub))

end
