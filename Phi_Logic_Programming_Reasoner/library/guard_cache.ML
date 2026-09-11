(*  Title:      guard_cache.ML
    Author:     Qiyuan Xu

The guard cache of PLPR (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md): what the store
holds for one guard (an entry: the judge's lemmas with their tiers and the last
verdict), the user simpset strengthening guard proving (Guard_Simp_SS), the
lemma list carried by the context (Guard_Lemmas), the lemma budget enforced
inside the simplifier (enhance_with_lemmas), and the export hook carrying the
lemma list across run and block boundaries.  The store instance and the entry
codec are added by step 4 of the plan.  prove_or_refute, the factory, the
refuters and the judge live in reasoners.ML.
*)

signature PHI_GUARD_CACHE = sig

(*The tier is the judge's estimate of how often a lemma is applied in one
  consumer run; its budget is the number of rewrites the lemma may make there.*)
datatype tier = Only_Once | Rarely | Normal | Frequent
type lemma = term * Phi_Proof_Store.proof_cache * tier
      (*statement, (replay times, method text), budget*)
datatype verdict = Proved | Refuted | Unknown
type entry = {lemmas : lemma list, verdict : verdict}

val guard_cache : bool Config.T            (*\<phi>guard_cache: read and write the store*)
val guard_lemma_apply_limit : int Config.T (*\<phi>guard_lemma_apply_limit: Frequent's budget, the ceiling*)
val budget_of_tier : Proof.context -> tier -> int

(*the store, keyed by the guard digest; TRANSITIONAL (plan step 2): one in-memory
  table per process, which step 4 replaces by the persistent store Phi_Guard_Store
  behind these two functions -- the theory then selects the file.  Not gated by
  \<phi>guard_cache: the switch is enforced by prove_or_refute at its read and writes.*)
val lookup_entry : theory -> Hasher.digest -> entry option
val write_entry : theory -> Hasher.digest -> entry -> unit

(*user-declared rewrite rules strengthening guard proving; attribute \<phi>guard_simp*)
structure Guard_Simp_SS : SIMPSET

(*the lemma list: each replayed judge lemma in the canonical form, with its budget*)
val get_lemmas : Proof.context -> (thm * int) list
(*append a replayed theorem with its budget, in the canonical form -- hhf-normal
  by ctxt0, outer parameters generalised, every type variable no hyp pins
  generalised, indices renumbered: a fixed point of the run-boundary export, so
  one canonical proposition is stored once -- unless a theorem of that
  proposition is present, which keeps its budget*)
val add_lemma : Proof.context -> thm * int -> Proof.context -> Proof.context
(*the same, but a theorem of that proposition already present takes the given budget:
  the judge's lemmas (plan section 5 step 6)*)
val update_lemma : Proof.context -> thm * int -> Proof.context -> Proof.context

(*the ONE way a consumer gets the lemmas into its simplifier, under the lemma
  budget: every rewrite rule of every lemma is weakened with a last premise
  \<open>Guard_Budget \<r>BUDGET<i>\<close> that one context-local simproc discharges while
  counting; a lemma at zero stops matching for the rest of this consumer run*)
val enhance_with_lemmas : Proof.context -> Proof.context

end

structure Phi_Guard_Cache : PHI_GUARD_CACHE = struct

datatype tier = Only_Once | Rarely | Normal | Frequent
type lemma = term * Phi_Proof_Store.proof_cache * tier
datatype verdict = Proved | Refuted | Unknown
type entry = {lemmas : lemma list, verdict : verdict}

val guard_cache = Attrib.setup_config_bool \<^binding>\<open>\<phi>guard_cache\<close> (K true)
val guard_lemma_apply_limit = Attrib.setup_config_int \<^binding>\<open>\<phi>guard_lemma_apply_limit\<close> (K 1000)

fun budget_of_tier ctxt tier =
  let val limit = Config.get ctxt guard_lemma_apply_limit
   in Int.min (limit, case tier of Only_Once => 3 | Rarely => 30 | Normal => 300 | Frequent => limit)
  end

(*the store's key (plan section 1): the compact rendering, never printed*)
fun key_of d = "PLPRGUARD" ^ Hasher.compact d

val table = Synchronized.var "Phi_Guard_Cache.table" (Symtab.empty : entry Symtab.table)

fun lookup_entry _ d = Symtab.lookup (Synchronized.value table) (key_of d)
fun write_entry _ d entry = Synchronized.change table (Symtab.update (key_of d, entry))

structure Guard_Simp_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>guard_simp\<close>
  val comment = "rewrite rules strengthening the automatic proving of guard conditions"
  val attribute = NONE
  val post_merging = I
)

structure Guard_Lemmas = Proof_Data (
  type T = (thm * int) list
  val init = K []
)

val get_lemmas = Guard_Lemmas.get

fun canonical_form ctxt0 th =
  let val th1 = Raw_Simplifier.norm_hhf_protect ctxt0 th
      val pinned = fold Term.add_tfree_names (Thm.hyps_of th1) []
      val tfrees = subtract (op =) pinned (Term.add_tfree_names (Thm.prop_of th1) [])
   in th1
   |> Thm.generalize (Names.make_set tfrees, Names.empty) (Thm.maxidx_of th1 + 1)
   |> Drule.zero_var_indexes
  end

(*on_present decides the budget of a theorem of the same canonical proposition
  already in the list, given (its budget, the new one)*)
fun add_lemma_with on_present ctxt0 (th, budget) =
  let val th' = canonical_form ctxt0 th
      fun same (th'', _) = Thm.eq_thm_prop (th', th'')
   in Guard_Lemmas.map (fn lemmas =>
        if exists same lemmas
        then map (fn l as (th'', b) => if same l then (th'', on_present (b, budget)) else l) lemmas
        else lemmas @ [(th', budget)])
  end

val add_lemma = add_lemma_with fst
val update_lemma = add_lemma_with snd

(*the guard-cache export hook: at every run and block boundary the outer lemma
  list is OVERWRITTEN with the inner one, each theorem through export_aux_lemma
  (a theorem it refuses is dropped, the rest keep their budgets); overwriting
  satisfies H2 of the hook contract (context_export.ML)*)
val _ = Theory.setup (Context.theory_map (PLPR_Context_Export.Hooks.add 200 (fn inner => fn outer =>
  Guard_Lemmas.put
    (map_filter (fn (th, budget) =>
        Option.map (rpair budget) (PLPR_Context_Export.export_aux_lemma inner outer th))
      (Guard_Lemmas.get inner))
    outer)))

val budgetT = \<^typ>\<open>ind\<close>
val Guard_Budget = Const (\<^const_name>\<open>Guard_Budget\<close>, budgetT --> \<^typ>\<open>bool\<close>)

(*Nesting -- a prove_or_refute call re-entered from inside the judge -- enhances a
  second batch of variables and a second simproc on the same chain; each simproc
  answers only the names in its own table.  Not designed for; the simproc never
  calls back into PLPR.*)
fun enhance_with_lemmas ctxt =
  case Guard_Lemmas.get ctxt of
    [] => ctxt
  | lemmas =>
      let val (names, ctxt1) =
            Variable.add_fixes (map_index (fn (i, _) => "\<r>BUDGET" ^ string_of_int i) lemmas) ctxt
          val remaining = Strhashtab.make (names ~~ map snd lemmas)
          fun premise name =
            Thm.cterm_of ctxt1 (HOLogic.mk_Trueprop (Guard_Budget $ Free (name, budgetT)))
          (*mksimps FIRST, on the lemma itself, so that it yields exactly the rules an
            ordinary simp declaration would; then the budget premise, rotated LAST, so
            that the simplifier charges the budget only once the rule's own premises
            are proved and the rewrite is about to be applied*)
          fun weaken (name, (th, _)) =
            map (Drule.rotate_prems 1 o Thm.implies_intr (premise name))
                (Raw_Simplifier.mksimps ctxt1 th)
          val rules = maps weaken (names ~~ lemmas)
          val simproc = Simplifier.make_simproc ctxt1
                {name = "Guard_Budget", kind = Simplifier.Simproc,
                 lhss = [Guard_Budget $ Var (("v", 0), budgetT)],
                 identifier = [],
                 proc = fn _ => fn _ => fn ct =>
                   case Thm.term_of ct of
                     _ $ Free (name, _) =>
                       (case Strhashtab.lookup remaining name of
                          SOME n => if n > 0
                                    then (Strhashtab.update remaining (name, n - 1);
                                          SOME (Conv.rewr_conv @{thm Guard_Budget_def} ct))
                                    else NONE
                        | NONE => NONE)
                   | _ => NONE}
       in ctxt1 |> Raw_Simplifier.add_proc simproc |> (fn c => c addsimps rules)
      end

end
