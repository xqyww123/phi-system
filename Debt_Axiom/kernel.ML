(*Interfaces in this file is not ready to be used directly. See Debt_Axiom.ML instead.*)

structure Debt_Axiom_Kernel : DEBT_AXIOM_KERNEL = struct

structure Axioms = Theory_Data (
  type T = term Symtab.table (*the ledger of debt axioms*)
  val empty = Symtab.empty
  val merge = Symtab.merge (op aconv)
)

val debts = Axioms.get

val (oracle, axgen) = Context.>>> (Context.map_theory_result (Thm.add_oracle (@{binding debt}, I)))
(*Make the axiom and record them in the ledger.*)
fun axiomize (N,TM) thy = (axgen TM, Axioms.map (Symtab.update_new (N, Thm.term_of TM)) thy)

fun assert err P = if P then () else raise Fail err

fun discharge certs thy =
  let val axs = map (the o Symtab.lookup (debts thy) o fst) certs
  in (*check the certifications are not depended on any axioms*)
     assert "dep"  (forall (fn ((x,_),_) => x <> oracle) (Thm_Deps.all_oracles (map snd certs)));
     (*check the propositions of the certifications identical to that of axioms,
       so that the certifications validate the axioms*)
     assert "cert" (eq_list (op =) (map (Thm.full_prop_of o Thm.transfer thy o snd) certs, axs));
     (*clear debt record if the above assertions succeed*)
     Axioms.map (fold (Symtab.delete o fst) certs) thy end

(*Definitional axioms relating an unspecified (but declared) type to be identical to another type.
  It axiomatizes a bijection theorem \<open>prj (inj x) = x &&& inj (prj y) = y\<close>
  between the two types.

  N : full name of the unspecified type T
  N': full name of the type T' to which T instantiates
  R : representation function from T to T'
  A : abstraction function from T' to T
  B : binding of the axiom

  instantiate_type then declares an axiom:
    \<open>A (R v) \<equiv> v &&& R (V u) \<equiv> u\<close>
  showing there is a bijection between T and T', so T and T' are equivalent.

  The axiom is definitional, and it requires T, A, R are not defined yet.
*)
fun instantiate_type N N' B RN AN thy =
  let val n = Sign.arity_number thy N
      val args = map (fn a => TFree (a, [])) (Name.invent Name.context Name.aT n)
      val (T,T') = (Type (N, args), Type (N', args))
      val (v,u) = (Free ("v", T), Free ("u", T'))
      val (R,A) = (Const (RN, T --> T'), Const (AN, T' --> T))
      val ax = Logic.mk_conjunction (Logic.mk_equals (A $ (R $ v), v),
                                     Logic.mk_equals (R $ (A $ u), u))
  in thy |> Theory.add_deps_type N
         |> Theory.add_deps_const RN |> Theory.add_deps_const AN
         |> Theory.add_axiom (Proof_Context.init_global thy) (B, ax)
  end

end