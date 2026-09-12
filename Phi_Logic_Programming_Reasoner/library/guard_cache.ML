(*  Title:      guard_cache.ML
    Author:     Qiyuan Xu

The guard cache of PLPR (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md): what the store
holds for one guard (an entry: the judge's lemmas with their tiers and the last
verdict), the user simpset strengthening guard proving (Guard_Simp_SS), the
lemma list carried by the context (Guard_Lemmas), the lemma budget enforced
inside the simplifier (enhance_with_lemmas), the export hook carrying the
lemma list across run and block boundaries, the store instance Phi_Guard_Store
(<thy>.guard-cache beside the theory) and the entry codec.  prove_or_refute,
the factory, the refuters and the judge live in reasoners.ML.
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

(*the store, keyed by the guard digest: the theory's <thy>.guard-cache, an
  instance of the proof store's functor (plan section 8), read and written through
  these two functions only.  An entry that does not decode is no entry.  Not gated
  by \<phi>guard_cache: the switch is enforced by prove_or_refute at its read and
  writes.*)
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

(*the guard cache's view of its store instance (plan section 8)*)
signature PHI_GUARD_STORE = sig
  val store_path : theory -> Path.T
  val get_cached_proof : theory -> string -> Phi_Proof_Store.proof_cache option
  val update_cached_proof : theory -> {id: string, hash: Hasher.digest option}
                            -> Phi_Proof_Store.proof_cache -> unit
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

(*The store: the proof store's functor over the guard cache's kind -- no legacy
  file to migrate, no write marks (an entry is legitimately rewritten), its own
  words in the two user-facing messages, \<phi>guard_cache as the switch the
  functor requires (it gates nothing inside).  Ascribed PHI_GUARD_STORE: the two
  entry points the guard cache uses and the path; the by-hash surface stays unused.*)
structure Phi_Guard_Store : PHI_GUARD_STORE = Proof_Store (struct
  val ext = "guard-cache"
  val migrates = false
  val marks_writes = false
  val describe = ("Guard cache", "cached guard advice")
  val switch = guard_cache
end)

(*the store's key (plan section 1): the compact rendering, never printed*)
fun key_of d = "PLPRGUARD" ^ Hasher.compact d

(*The entry codec (plan section 8): the entry value packed with the msgpack
  packers into the record's string half -- a lemma's statement through the
  term codec of Isabelle_RPC (a runtime symbol travels as its identifier), its
  times as the store's own (cpu_ms, wall_ms) pair, the tier and the verdict as
  int tags.  No format version: a payload that does not decode is no entry.*)
local
  structure P = MessagePackBytesIO.Pack
  structure U = MessagePackBytesIO.Unpack
  fun int_of_tier Only_Once = 0 | int_of_tier Rarely = 1 | int_of_tier Normal = 2 | int_of_tier Frequent = 3
  fun tier_of_int 0 = Only_Once | tier_of_int 1 = Rarely | tier_of_int 2 = Normal
    | tier_of_int 3 = Frequent | tier_of_int _ = raise U.Unpack
  fun int_of_verdict Proved = 0 | int_of_verdict Refuted = 1 | int_of_verdict Unknown = 2
  fun verdict_of_int 0 = Proved | verdict_of_int 1 = Refuted | verdict_of_int 2 = Unknown
    | verdict_of_int _ = raise U.Unpack
  val entry_packer =
    P.packPair (P.packList (P.packTuple3 (RPC_Pretty_Bytes.pack_raw_term,
                                          P.packPair (P.packPair (P.packInt, P.packInt), P.packString),
                                          P.packInt)),
                P.packInt)
  val entry_unpacker =
    U.>> (U.unpackPair (U.unpackList (U.unpackTuple3 (RPC_Pretty_Bytes.unpack_raw_term,
                                                     U.unpackPair (U.unpackPair (U.unpackInt, U.unpackInt), U.unpackString),
                                                     U.unpackInt)),
                        U.unpackInt),
          fn (lemmas, verdict) =>
            {lemmas = map (fn (stmt, (ms, script), tier) =>
                             (stmt, (Phi_Proof_Store.times_of_ms ms, script), tier_of_int tier)) lemmas,
             verdict = verdict_of_int verdict} : entry)
in
fun encode_entry ({lemmas, verdict} : entry) =
  let val outs = BytesIO.mkOutstream ()
   in entry_packer (map (fn (stmt, (times, script), tier) =>
                           (stmt, (Phi_Proof_Store.ms_of_times times, script), int_of_tier tier)) lemmas,
                    int_of_verdict verdict) outs;
      BytesIO.toString outs
  end
(*catch-all: a truncated payload raises Subscript out of BytesIO, a foreign one
  Unpack; \<^try> re-raises interrupts*)
fun decode_entry s =
  \<^try>\<open>SOME (#1 (U.doUnpack entry_unpacker (BytesIO.fromString s))) catch _ => NONE\<close>
end

fun lookup_entry thy d =
  case Phi_Guard_Store.get_cached_proof thy (key_of d) of
    NONE => NONE
  | SOME (_, payload) => decode_entry payload
fun write_entry thy d entry =
  Phi_Guard_Store.update_cached_proof thy {id = key_of d, hash = NONE}
    (Phi_Proof_Store.zero_times, encode_entry entry)

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
