(*  Title:      guard_cache.ML
    Author:     Qiyuan Xu

The guard cache of PLPR (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md): what the store
holds for one guard (an entry: the guard's delta to the lemma list -- the lemmas
it adds, with their tiers, and the statements it deletes -- and the last
verdict), the user simpset strengthening guard proving (Guard_Simp_SS), the
lemma list carried by the context (Guard_Lemmas), the lemma budget enforced
inside the simplifier (enhance_with_lemmas), the export hook carrying the
lemma list across run and block boundaries, and the entry codec over the proof
store of auto_sledgehammer (the theory's <thy>.proof-store holds the entries).
prove_or_refute, the factory, the refuters and the judge live in reasoners.ML.
*)

signature PHI_GUARD_CACHE = sig

(*The tier is the judge's estimate of how often a lemma is applied in one
  consumer run; its budget is the number of rewrites the lemma may make there.*)
datatype tier = Only_Once | Rarely | Normal | Frequent
type lemma = term * Phi_Proof_Store.proof_cache * tier
      (*statement, (replay times, method text), budget*)
(*what the guard does to the lemma list of the context it is met in: the deleted
  statements' theorems leave, whichever guard added them, then the added lemmas
  go in by add_lemma below (plan section 5 step 1)*)
type delta = {added : lemma list, deleted : term list}
val empty_delta : delta
datatype verdict = Proved | Refuted | Unknown
type entry = {delta : delta, verdict : verdict}

val guard_cache : bool Config.T            (*\<phi>guard_cache: read and write the store*)
val guard_lemma_apply_limit : int Config.T (*\<phi>guard_lemma_apply_limit: Frequent's budget, the ceiling*)
val budget_of_tier : Proof.context -> tier -> int

(*the store, keyed by the guard digest: the theory's proof store (<thy>.proof-store,
  auto_sledgehammer's Phi_Proof_Store; plan section 8), read and written through
  these two functions only, under ids no proof obligation uses.  An entry that
  does not decode is no entry.  Not gated by \<phi>guard_cache: the switch is
  enforced by prove_or_refute at its read and writes.*)
val lookup_entry : theory -> Hasher.digest -> entry option
val write_entry : theory -> Hasher.digest -> entry -> unit

(*user-declared rewrite rules strengthening guard proving; attribute \<phi>guard_simp*)
structure Guard_Simp_SS : SIMPSET

(*the lemma list: each replayed judge lemma as its replay produced it, with its
  budget; a theorem's identity here is its proposition, up to renaming of
  schematic variables (Pattern.equiv)*)
val get_lemmas : Proof.context -> (thm * int) list
(*remove every theorem whose proposition is one of the statements*)
val delete_lemmas : term list -> Proof.context -> Proof.context
(*append a replayed theorem with its budget; a theorem of that proposition
  already present takes the budget instead -- the one rule for an entry's delta
  and for the judge's*)
val add_lemma : thm * int -> Proof.context -> Proof.context

(*the ONE way a consumer gets the lemmas into its simplifier, under the lemma
  budget: every rewrite rule of every lemma is weakened with a last premise
  \<open>Guard_Budget \<r>BUDGET<i>\<close> that one context-local simproc discharges while
  counting; a lemma at zero stops matching for the rest of this consumer run*)
val enhance_with_lemmas : Proof.context -> Proof.context

end

structure Phi_Guard_Cache : PHI_GUARD_CACHE = struct

datatype tier = Only_Once | Rarely | Normal | Frequent
type lemma = term * Phi_Proof_Store.proof_cache * tier
type delta = {added : lemma list, deleted : term list}
val empty_delta : delta = {added = [], deleted = []}
datatype verdict = Proved | Refuted | Unknown
type entry = {delta : delta, verdict : verdict}

val guard_cache = Attrib.setup_config_bool \<^binding>\<open>\<phi>guard_cache\<close> (K true)
val guard_lemma_apply_limit = Attrib.setup_config_int \<^binding>\<open>\<phi>guard_lemma_apply_limit\<close> (K 1000)

fun budget_of_tier ctxt tier =
  let val limit = Config.get ctxt guard_lemma_apply_limit
   in Int.min (limit, case tier of Only_Once => 3 | Rarely => 30 | Normal => 300 | Frequent => limit)
  end

(*A guard entry is a record of the theory's proof store under an id no proof
  obligation uses -- this prefix and the digest -- with no goal hash, zero times
  and the packed entry as its text.*)
fun key_of d = "PLPRGUARD" ^ Hasher.compact d

(*The entry codec (plan section 8): the triple (added, deleted, verdict) packed
  with the msgpack packers into the record's string half -- a statement through
  the term codec of Isabelle_RPC (a runtime symbol travels as its identifier), a
  lemma's times as the store's own (cpu_ms, wall_ms) pair, the tier and the
  verdict as int tags.  No format version: a payload that does not decode is no
  entry.*)
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
    P.packTuple3 (P.packList (P.packTuple3 (RPC_Pretty_Bytes.pack_raw_term,
                                            P.packPair (P.packPair (P.packInt, P.packInt), P.packString),
                                            P.packInt)),
                  P.packList RPC_Pretty_Bytes.pack_raw_term,
                  P.packInt)
  val entry_unpacker =
    U.>> (U.unpackTuple3 (U.unpackList (U.unpackTuple3 (RPC_Pretty_Bytes.unpack_raw_term,
                                                       U.unpackPair (U.unpackPair (U.unpackInt, U.unpackInt), U.unpackString),
                                                       U.unpackInt)),
                          U.unpackList RPC_Pretty_Bytes.unpack_raw_term,
                          U.unpackInt),
          fn (added, deleted, verdict) =>
            {delta = {added = map (fn (stmt, (ms, script), tier) =>
                                     (stmt, (Phi_Proof_Store.times_of_ms ms, script), tier_of_int tier)) added,
                      deleted = deleted},
             verdict = verdict_of_int verdict} : entry)
in
fun encode_entry ({delta = {added, deleted}, verdict} : entry) =
  let val outs = BytesIO.mkOutstream ()
   in entry_packer (map (fn (stmt, (times, script), tier) =>
                           (stmt, (Phi_Proof_Store.ms_of_times times, script), int_of_tier tier)) added,
                    deleted,
                    int_of_verdict verdict) outs;
      BytesIO.toString outs
  end
(*catch-all: a truncated payload raises Subscript out of BytesIO, a foreign one
  Unpack; \<^try> re-raises interrupts*)
fun decode_entry s =
  \<^try>\<open>SOME (#1 (U.doUnpack entry_unpacker (BytesIO.fromString s))) catch _ => NONE\<close>
end

fun lookup_entry thy d =
  case Phi_Proof_Store.get_cached_proof thy (key_of d) of
    NONE => NONE
  | SOME (_, payload) => decode_entry payload
fun write_entry thy d entry =
  Phi_Proof_Store.update_cached_proof thy {id = key_of d, hash = NONE}
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

(*an ill-formed statement is the proposition of no theorem*)
fun same_prop ctxt t (th, _) =
  Pattern.equiv (Proof_Context.theory_of ctxt) (t, Thm.prop_of th)
  handle TYPE _ => false | TERM _ => false

fun delete_lemmas stmts ctxt =
  Guard_Lemmas.map (filter_out (fn l => exists (fn t => same_prop ctxt t l) stmts)) ctxt

fun add_lemma (th, budget) ctxt =
  let val same = same_prop ctxt (Thm.prop_of th)
   in Guard_Lemmas.map (fn lemmas =>
        if exists same lemmas
        then map (fn l as (th', _) => if same l then (th', budget) else l) lemmas
        else lemmas @ [(th, budget)]) ctxt
  end

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
