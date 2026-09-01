(*  Title:      guard_refute.ML
    Author:     the phi-system project

Refutation of guard conditions by finite model search: preprocessing plus the
patched Nitpick copy Phi_Nitpick.  Design and measurements in
Docs/GUARD_NITPICK_FALSIFY_PLAN.md, sections 19 to 22.

What the guard means is not known here: the rewrites come from the memory
model and from each struct, and any weakening of the premises comes from a
hook registered by the theory that owns the notion being weakened.  This file
is loaded from PLPR, which precedes all of them.
*)

signature PHI_GUARD_REFUTE =
sig
  (*Not reasoners.ML's race_result: Provable carries no proof object, only the
    news that this refuter should keep its hands off.  The caller maps into
    the race -- today Refuted wins, Provable and Unknown give up.*)
  datatype verdict = Refuted | Provable | Unknown

  (*arg = Proof.context, state = term list; see the structure below*)
  structure Preprocess_Hooks : HOOKS

  (*arg = unit, state = Proof.context; see the structure below*)
  structure Simpset_Hooks : HOOKS

  (*premises and conclusion, both with the goal's \<And>-binders fixed*)
  val premises_of : Proof.context -> term list -> term -> term list * term
  val slice : term list -> term -> term
  val preprocess : Proof.context -> term list -> term -> (term list * term) option

  val nitpick : Proof.context -> Phi_Nitpick.params -> int * int ->
                (term * term) list * term list * term -> verdict
end

structure Phi_Guard_Refute : PHI_GUARD_REFUTE =
struct

datatype verdict = Refuted | Provable | Unknown


(*** Stores ***)

(*Rewrites run over the guard before the search.  Registered rules must be
  THEOREMS: Provable below rests on the preprocessing being meaning-preserving.
  Do NOT register addr_gep_def -- its map_addr lambda defeats the [iff] gep
  lemmas and cost refutations when tried (plan 19.4).*)
structure Guard_Refute_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>guard_refute_simp\<close>
  val comment = "rewrites applied to a guard before refuting it by model search"
  val attribute = NONE
  val post_merging = I
)

(*Premise transformers, run in priority order before the simplifier.  A hook
  may only WEAKEN: the caller's soundness story (see the header) is that
  P ==> P', and nothing checks it -- a hook that strengthens or that touches
  the conclusion breaks this refuter silently.  The polarity discipline that
  makes a weakening legal belongs to the hook, which knows what it is
  weakening; see Phi_BI's satisfaction scrub for the reference shape.*)
structure Preprocess_Hooks = Hooks (
  type arg = Proof.context
  type state = term list
)

(*Simpsets the refuter must also consult, contributed by theories this file
  cannot name: it is loaded from PLPR, which precedes the memory model and
  every aggregate.  A contributor registers its ENHANCER, not its rules, so
  the store is read when the refuter runs and a rule declared later still
  arrives.  Copying the rules instead would be a snapshot, and no snapshot can
  work here: the aggregate kinds are siblings and no single theory sees them
  all.*)
structure Simpset_Hooks = Hooks (
  type arg = unit
  type state = Proof.context
)


(*** Which context assumptions travel with the guard ***)

(*Premise-tagged ones only (author ruling, plan 19.2); an obligation is a
  goal, not a fact.  Dropping a premise ENLARGES the model space, so this
  filter widens the misjudgment surface -- it is a ruling, not an
  optimisation.*)

(*The tag sits on the CONCLUSION, so an assumption that is itself an hhf
  formula is classified by what it concludes; it then travels whole, binders
  and all -- a universally quantified fact is still a fact.*)
fun is_premise assm =
  (case snd (Phi_Help.strip_meta_hhf_bvs assm) of
     Const (\<^const_name>\<open>Trueprop\<close>, _) $
        (Const (\<^const_name>\<open>Premise\<close>, _) $ mode $ _) =>
       (case mode of
          Const (\<^const_name>\<open>default\<close>, _) => true         (*\<premise>*)
        | Const (\<^const_name>\<open>MODE_GUARD\<close>, _) => true      (*\<condition>*)
        | _ => false)                                       (*\<obligation>: a goal*)
   | _ => false)

(*Logic.strip_imp_prems stops at Pure.all, so a \<And>-headed subgoal used to reach
  the search with NO antecedents at all -- not the recipe weakened but bypassed,
  on 181 of the 1538 goals in the production dump.  Phi_Help.strip_meta_hhf goes
  under both connectives in one pass; what it returns carries loose Bounds,
  closed here by fixing each binder as a fresh Free.  That is also the form the
  model search wants: Nitpick assigns free variables, which is exactly "some x
  refutes \<And>x. ...".  Premises and conclusion must come from this ONE call --
  taking the conclusion separately would close it over different Frees.*)
fun premises_of ctxt assms goal =
  let
    val (bvs, prems, concl) = Phi_Help.strip_meta_hhf goal
    (*names only -- these Frees never enter the context, so variant_fixes,
      which would build one, is not the interface.  Everything they must stay
      clear of is declared here, so freshness does not rest on the caller.*)
    val frees =
      map Free (Variable.variant_names (fold Variable.declare_term (goal :: assms) ctxt) bvs)
    fun close t = subst_bounds (rev frees, t)
  in (map close prems @ filter is_premise assms, close concl) end


(*** Conjunction splitting and variable-closure slicing ***)

(*A premise is kept or dropped whole, so splitting conjunctions first is what
  lets slicing separate an unrelated invariant from the conclusion's
  variables.  Both run on the simplifier's output, where unfolding a
  definition has just produced fresh conjunctions.*)

fun split_conjunctions prem =
  (case prem of
     Const (\<^const_name>\<open>Trueprop\<close>, _) $ t =>
       let
         fun split (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ a $ b) = split a @ split b
           | split t = [t]
       in map HOLogic.mk_Trueprop (split t) end
   | _ => [prem])

fun slice prems concl =
  let
    fun frees_of t = map fst (Term.add_frees t [])
    fun grow known pending =
      let
        val (connected, rest) =
          List.partition (fn p => exists (member (op =) known) (frees_of p)) pending
      in
        if null connected then []
        else
          let val known' = fold (union (op =) o frees_of) connected known
          in connected @ grow known' rest end
      end
  in
    Logic.list_implies (grow (frees_of concl) (maps split_conjunctions prems), concl)
  end


(*** Case distinctions ***)

(*A case over a FREE variable reduces by no rewrite, and neither clarsimp nor
  auto helps: both use the simplifier's splitter, whose only default rule is
  if_split.  The datatype's split theorem does it, and the goal's own case
  constants name the datatypes -- empty table, no cost, when there are none.*)

fun case_splits ctxt t =
  Term.add_consts t []
  |> map fst
  |> distinct (op =)
  |> map_filter (Ctr_Sugar.ctr_sugar_of_case ctxt)
  |> map #split


(*** The pipeline ***)

(*NONE means the simplifier closed the goal.  That is a real proof of the
  ORIGINAL guard: the hooks and the slice weaken the premises, and P ==> P'
  with a proof of P' ==> C gives P ==> C.  In the other direction the weakening only
  costs completeness -- see the verdict map in reasoners.ML.*)

fun preprocess ctxt assms goal =
  let
    val (prems0, concl) = premises_of ctxt assms goal
    val prems = Preprocess_Hooks.invoke (Context.Proof ctxt) ctxt prems0
    val prepared = Logic.list_implies (prems, concl)
    val simp_ctxt =
      Guard_Refute_SS.enhance ctxt
        |> Simpset_Hooks.invoke (Context.Proof ctxt) ()
        |> fold Splitter.add_split (case_splits ctxt prepared)
        (*EXPERIMENT 2 (2026-08-30, author's step 2): R-nitpick's preprocessing
          runs WITHOUT the guess_inst looper, which `enhance` inherits from the
          ambient context (equipped once in guard_condition_solver's auto_tac,
          reasoners.ML).  P-auto and R-conv keep it.  Compare the R-nitpick
          refutation count against experiment 1 (312 of 640 on cslh19).*)
        |> Raw_Simplifier.del_loop "inst_var_by_Ctr_sels"
    val st =
      (case SINGLE (Simplifier.asm_full_simp_tac simp_ctxt 1)
              (Goal.init (Thm.cterm_of ctxt prepared)) of
         SOME st => st
       | NONE => Goal.init (Thm.cterm_of ctxt prepared))
  in
    if Thm.nprems_of st = 0 then NONE
    else
      let
        val residue = Thm.term_of (Thm.cprem_of st 1)
        val sliced = slice (Logic.strip_imp_prems residue) (Logic.strip_imp_concl residue)
      in SOME (Logic.strip_imp_prems sliced, Logic.strip_imp_concl sliced) end
  end

(*The premises go in through the ASSUMPTION parameter, not inside the goal:
  only then are they separate formulas internally, and only per formula can
  Phi_Nitpick take a soundness flag.  Passing them inside the goal turns the
  trust patch silently off.

  genuine and quasi_genuine both count, as in reasoners.ML's verdict map and
  for its reason: under user_axioms = false nothing can be certified genuine.

  The model search gets its OWN timeout, independent of what preprocessing
  cost (author ruling 2026-08-28).  Charging preprocessing against the search
  makes the search's reach depend on a quantity that has nothing to do with
  it, and makes two measurements incomparable whenever preprocessing differs.
  Since 2026-09-01 the assembly wrap is only a hang net; the search's bound
  is Nitpick's own internal net (see the note at the search call below).*)

(*TEMPORARY probe (2026-08-31): the refuter as it runs INSIDE the race -- the
  residue it hands to Nitpick and what Nitpick answers.  Text is markup-free.*)
val refuter_probe_category =
  Event_Log.category {name = "refuter_probe", enabled = fn () => true,
    encode = fn {i, n, n_assms, n_prems, n_subst, code, pre_ms, search_ms, residue, msgs,
                 rerun_same, rerun_global, rerun_more, ml} =>
      ([("subgoal", string_of_int i ^ "/" ^ string_of_int n),
        ("assms", string_of_int n_assms), ("prems", string_of_int n_prems),
        ("subst", string_of_int n_subst),
        ("code", code), ("pre_ms", string_of_int pre_ms), ("search_ms", string_of_int search_ms),
        (*the four rerun columns are constantly "-": their bisection reruns
          were disabled with the per-racer knife (2026-09-01, unbounded
          without a uniform outer knife); fields stay until the probe's
          removal*)
        ("rerun_same", rerun_same), ("rerun_global", rerun_global),
        ("rerun_external", #1 rerun_more), ("rerun_locked", #2 rerun_more)],
       [Event_Log.elem_text "residue" residue, Event_Log.elem_text "msgs" msgs,
        Event_Log.elem_text "ml" ml])}

fun plain_term ctxt t =
  XML.content_of (YXML.parse_body (Print_Mode.setmp []
    (Syntax.string_of_term (ctxt |> Config.put show_types true |> Config.put show_sorts true)) t))

(*served the disabled "locked" rerun; kept until the probe's removal*)
val probe_lock = Synchronized.var "refuter_probe_lock" ()

fun nitpick ctxt params (i, n) (subst, assms, goal) =
  let val t0 = Timing.start ()
      val pre = preprocess ctxt assms goal
      val pre_ms = Time.toMilliseconds (#elapsed (Timing.result t0))
      fun log n_prems code search_ms residue msgs reruns rerun_more ml =
        Event_Log.append refuter_probe_category
          {i = i, n = n, n_assms = length assms, n_prems = n_prems, n_subst = length subst,
           code = code, pre_ms = pre_ms, search_ms = search_ms, residue = residue, msgs = msgs,
           rerun_same = fst reruns, rerun_global = snd reruns, rerun_more = rerun_more, ml = ml}
      fun plain s = XML.content_of (YXML.parse_body s)
      fun run prems concl =
        let val t = Timing.start ()
            val (code, msgs) =
              Phi_Nitpick.pick_nits_in_term (Proof.init ctxt) params true
                Phi_Nitpick.Auto_Try i n 0 subst [] prems concl
         in (code, msgs, Time.toMilliseconds (#elapsed (Timing.result t))) end
      fun timed (code, _, ms) = code ^ "@" ^ string_of_int ms ^ "ms"
  in
  (case pre of
     NONE => (log 0 "simp_proved" 0 "-" "-" ("-", "-") ("-", "-") "-"; Provable)
   | SOME (prems, concl) =>
       (*no knife here (author ruling 2026-09-01): the model search's bound
         is Nitpick's own Timeout.apply (timeout + timeout_bonus) inside the
         vendored phi_nitpick.ML -- a rebase must keep it; the assembly's
         hang net is the only bound this module owns.  Preprocessing stays
         uncharged (ruling 2026-08-28).*)
       let val (code, msgs, search_ms) = run prems concl
           val reruns = ("-", "-")  (*disabled; see the category's note*)
           val rerun_more = ("-", "-")
           val _ = log (length prems) code search_ms
                       (plain_term ctxt (Logic.list_implies (prems, concl)))
                       (cat_lines (map plain msgs)) reruns rerun_more
                       (if code = Phi_Nitpick.noneN
                        then ML_Syntax.print_term (Logic.list_implies (prems, concl)) else "-")
        in if code = Phi_Nitpick.genuineN orelse code = Phi_Nitpick.quasi_genuineN
           then Refuted else Unknown
       end)
  end

end
