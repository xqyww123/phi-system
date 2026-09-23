theory Guard_Decision_Smoke
  imports "Phi_Logic_Programming_Reasoner.PLPR"
begin

(* Probes of one prove_or_refute call (library/reasoners.ML): every path
   of Docs/GUARD_CACHE_QUICK_MODE_PLAN.md section 5 -- hits of each verdict,
   lemma enabling, a looping lemma cut off by its budget, an entry's deletion,
   the judge's delta replacing this entry's, both warnings, the judge's three errors --
   and the check \<check> \<premise> \<consistency>, the guard \<condition> False decided
   without assuming the premises consistent (plan section 1, the check) -- driven through the guard
   factory with entries injected into the store and a test judge installed into
   the ref.  Not registered in any ROOT: evaluate on demand (e.g. via
   Isabelle-MCP under session Phi_System_Base).

   Reachability constraint: every guard below must survive the factory's own
   exits (the TrueI exit, fast_inst) so that it reaches prove_or_refute, and
   must not be closed by guard_simp_tac there, so that P-auto's search decides
   it: the atoms below carry classical rules only, never a simp rule, and no
   guard is an equation.  Three exceptions: the probe of the simplifier's
   own refutation (plan section 5 step 1 1/2), whose injected lemma rewrites
   the guard to False on purpose; and, in the section The check, the probe
   whose premise guard_simp_tac rewrites to False (closing the goal) and the
   regression probe, an equation guard on purpose.  The other check probes are
   decided by P-auto, by R-nitpick or by the judge, and BADN's ends unknown.

   The store is this theory's proof store, Guard_Decision_Smoke.proof-store (plan
   step 4), with no deletion, and it outlives a re-evaluation of this theory and
   the process: a guard decided once keeps its entry.  So every probe
   gives its guard an argument no call in this or any earlier run used (`fresh`: a
   wall-clock run tag plus a process serial), and a probe that needs an entry
   writes it first.

   NB the helpers take the calling block's \<^context> explicitly: the
   antiquotation is static, and a helper-captured context would predate the
   construct declarations below, turning them into frees (measured trap). *)

declare [[\<phi>trace_reasoning = 3]]
declare [[ML_debugger]]  \<comment> \<open>the guard_decision records are written under it\<close>

ML \<open>
(*locate this process's guard_decision log file; pid reuse across reboots, and
  every reload of reasoners.ML (a fresh Event_Log category value), leave several
  files with our suffix -- the lexicographically last one is the newest, and the
  digest filter below neutralizes any inherited content*)
fun log_file () =
  (case Event_Log.log_dir () of
     NONE => error "Guard_Decision_Smoke requires event logging (ISABELLE_EVENT_LOG_DIR must not be empty)"
   | SOME dir =>
       let val category_dir = Path.append dir (Path.basic "guard_decision")
           val suffix = "-" ^ string_of_int (ML_Pid.get ()) ^ ".xml"
       in if not (File.is_dir category_dir) then NONE
          else (case filter (String.isSuffix suffix) (File.read_dir category_dir) of
                  [] => NONE
                | names => SOME (Path.append category_dir (Path.basic (List.last names))))
       end)

fun decision_records () =
  (case log_file () of
     NONE => []
   | SOME path =>
       map_filter (fn XML.Elem (("record", atts), body) =>
                        if AList.lookup (op =) atts "category" = SOME "guard_decision"
                        then SOME (atts, body) else NONE
                    | _ => NONE)
         (Event_Log.read_file path))

(*the projection of a guard_decision record every probe asserts on (see the
  guard_decision comment in reasoners.ML's signature): the verdict, the entry's
  verdict, the refuter, the judge's answer; the timing-dependent fields stay out*)
fun attr a ((atts, _): Properties.T * XML.body) =
  the_default "?" (AList.lookup (op =) atts a)
fun path_of r = (attr "verdict" r, attr "hit" r, attr "refuter" r, attr "judge" r)
fun show_record ((atts, _): Properties.T * XML.body) =
  commas (map (fn (a, v) => a ^ "=" ^ v) atts)

(*the guard digest as the factory computes it, through the factory itself and under
  the kind of the state as written (guard_digest_of, the engine's own digest step): a
  solving function that records what the digest step handed it*)
fun digest_of can_inst ctxt st =
  let val d = Unsynchronized.ref NONE
      val _ = Seq.pull (Phi_Reasoners.gen_guard_condition_solver (Phi_Reasoners.guard_digest_of st)
                (fn _ => fn _ => fn d' => fn _ => (d := SOME d'; Seq.empty))
                {can_inst = can_inst} (ctxt, st))
   in the (! d) end

fun entry_of ctxt d = Phi_Guard_Cache.lookup_entry (Proof_Context.theory_of ctxt) d

fun show_entry NONE = "no entry"
  | show_entry (SOME {delta = {added, deleted}, verdict}) =
      (case verdict of Phi_Guard_Cache.Proved => "Proved"
                     | Phi_Guard_Cache.Refuted => "Refuted"
                     | Phi_Guard_Cache.Unknown => "Unknown") ^
      " with " ^ string_of_int (length added) ^ " lemma(s)" ^
      (if null deleted then "" else ", " ^ string_of_int (length deleted) ^ " deletion(s)")

fun adds lemmas : Phi_Guard_Cache.delta = {added = lemmas, deleted = []}

fun show_lemmas ctxt = @{make_string} (map (apfst Thm.prop_of) (Phi_Guard_Cache.get_lemmas ctxt))

(*the judge's argument contract (plan section 1, section 5 step 6), checked on every
  call of a test judge: `ctxt` and `outer_ctxt` carry the lemma list as it was before
  this entry's delta was applied -- the probe context's, statement for statement --
  `delta` is the injected entry's (every probe's entry replays whole), `can_inst` is
  the probe's, and the goal state has subgoals*)
fun contract name ctxt can_inst entry j (arg : Phi_Reasoners.judge_arg) =
  let fun props c = map (Thm.prop_of o fst) (Phi_Guard_Cache.get_lemmas c)
      fun same c = eq_list (op aconv) (props c, props ctxt)
      val {added, deleted} = (case entry of SOME {delta, ...} => delta | NONE => Phi_Guard_Cache.empty_delta)
      fun check what ok = if ok then () else error (name ^ ": the judge's argument breaks its contract: " ^ what)
   in check "ctxt's lemma list is not the probe context's" (same (#ctxt arg));
      check "outer_ctxt's lemma list is not the probe context's" (same (#outer_ctxt arg));
      check "delta's added lemmas are not the entry's"
            (eq_list (fn ((s, (_, m), t), (s', (_, m'), t')) => s aconv s' andalso m = m' andalso t = t')
                     (#added (#delta arg), added));
      check "delta's deletions are not the entry's" (eq_list (op aconv) (#deleted (#delta arg), deleted));
      check "can_inst is not the probe's" (#can_inst arg = can_inst);
      check "the goal state has no subgoal" (Thm.nprems_of (#thm arg) > 0);
      j arg
  end

(*the engine seam, written once: the goal state, the guard's digest through the
  factory, the injected entry written under it, the judge installed under the
  contract, the guard driven through guard_condition_judge, the judge restored;
  the digest and the captured result*)
fun run_guard {can_inst, entry, judge} ctxt name t =
  let val st = Thm.trivial (Thm.cterm_of ctxt t)
      val d = digest_of can_inst ctxt st
      val _ = (case entry of NONE => ()
               | SOME e => Phi_Guard_Cache.write_entry (Proof_Context.theory_of ctxt) d e)
      val _ = Phi_Reasoners.judge := Option.map (contract name ctxt can_inst entry) judge
      val res = Exn.capture_body (fn () => Timing.timing (fn () =>
                  Phi_Reasoners.guard_condition_judge {can_inst = can_inst} (ctxt, st) |> Seq.pull) ())
      val _ = Phi_Reasoners.judge := NONE
   in (d, res) end

(*one engine for every probe: run the guard, then assert on the projection of the
  record THIS call appended -- the records carrying this guard's digest, which
  `fresh` makes unique to this probe and this evaluation; a count delta would not
  do, since other theories loading in the same process append to the same file,
  and a reload of reasoners.ML starts a new file -- and on the entry left in the
  store.  Returns the result state, for assertions on the context it carries.*)
fun decide opts ctxt name {path, store} t =
  let val (d, res) = run_guard opts ctxt name t
      val (time, r) = Exn.release res
      val new = filter (fn r => attr "digest" r = Hasher.hex d) (decision_records ())
      val observed = map path_of new
      val _ = if observed = [path] then ()
              else error (name ^ ": expected " ^ @{make_string} path ^
                          " but logged " ^ @{make_string} observed ^
                          (if null new then " (no decision logged)"
                           else "\n" ^ cat_lines (map (prefix "  " o show_record) new)))
      val left = entry_of ctxt d
      val _ = if show_entry left = store then ()
              else error (name ^ ": expected the store to hold " ^ store ^
                          " but it holds " ^ show_entry left)
      val _ = writeln (name ^ ": " ^ (case r of SOME _ => "state" | NONE => "empty") ^
                       " in " ^ string_of_int (Time.toMilliseconds (#elapsed time)) ^ "ms; " ^
                       show_entry left ^ "\n  log: " ^ cat_lines (map show_record new))
   in Option.map fst r end

(*the same call expected to raise: the error text (markup stripped) must begin with
  the given prefix*)
fun decide_error opts ctxt name prefix t =
  let val (_, res) = run_guard opts ctxt name t
   in case res of
        Exn.Exn (ERROR msg) =>
          let val text = XML.content_of (YXML.parse_body msg)
           in if String.isPrefix prefix text then writeln (name ^ ": raised as expected: " ^ text)
              else error (name ^ ": raised " ^ quote text ^ ", expected the prefix " ^ quote prefix)
          end
      | Exn.Exn e => Exn.reraise e
      | Exn.Res _ => error (name ^ ": did not raise")
  end

fun read can_inst ctxt =
  Syntax.read_prop (if can_inst then Proof_Context.set_mode Proof_Context.mode_schematic ctxt else ctxt)

fun test (opts as {can_inst, entry = _, judge = _}) ctxt name expect prop_str =
  decide opts ctxt name expect (read can_inst ctxt prop_str)
fun test_error (opts as {can_inst, entry = _, judge = _}) ctxt name prefix prop_str =
  decide_error opts ctxt name prefix (read can_inst ctxt prop_str)

val plain = {can_inst = false, entry = NONE, judge = NONE}
val schematic = {can_inst = true, entry = NONE, judge = NONE}
fun with_delta delta verdict = {can_inst = false, entry = SOME {delta = delta, verdict = verdict}, judge = NONE}
fun with_entry lemmas verdict = with_delta (adds lemmas) verdict
fun with_judge j = {can_inst = false, entry = NONE, judge = SOME j}
fun with_delta_and_judge delta verdict j =
  {can_inst = false, entry = SOME {delta = delta, verdict = verdict}, judge = SOME j}
fun with_entry_and_judge lemmas verdict j = with_delta_and_judge (adds lemmas) verdict j

fun expect path store = {path = path, store = store}

(*the warnings a probe prints, markup stripped, for the probes that assert on the
  loud guard warning*)
fun warnings_of f =
  let val got = Unsynchronized.ref ([] : string list)
   in Unsynchronized.setmp Private_Output.warning_fn
        (fn outs => got := XML.content_of (YXML.parse_body (implode outs)) :: ! got) f ();
      rev (! got)
  end
val loud_line = "A guard condition proved before is now refuted by the LLM judge:"
val loud_simp_line = "A guard condition proved before is now refuted by the simplifier:"
(*the undecided-guard warning and the undecided-check warning are trace-gated; this
  theory's \<phi>trace_reasoning = 3 keeps them on*)
val undecided_line = "Fail to prove or falsify the following guard condition"
val undecided_check_line = "Fail to check the consistency of the premises:"
val warning_lines = [loud_line, loud_simp_line, undecided_line, undecided_check_line]
fun assert_warnings name line expected ws =
  let val n = length (filter (String.isPrefix line) ws)
   in if n = expected then writeln (name ^ ": " ^ string_of_int n ^ " warning(s) " ^ quote line ^ ", as expected")
      else error (name ^ ": " ^ string_of_int n ^ " warning(s) " ^ quote line ^ ", expected " ^ string_of_int expected)
  end
(*the given line the given number of times, every other line of warning_lines never*)
fun assert_only name line expected ws =
  (assert_warnings name line expected ws;
   List.app (fn l => assert_warnings name l 0 ws) (remove (op =) line warning_lines))
fun assert_loud name = assert_only name loud_line
fun assert_loud_simp name = assert_only name loud_simp_line
fun assert_undecided name = assert_only name undecided_line
fun assert_undecided_check name = assert_only name undecided_check_line

(*a numeral no call of this or any earlier run used, for a guard that must meet no
  entry: the store outlives the process, and a process serial alone could repeat
  one an earlier process used*)
val run_tag = Time.toNanoseconds (Time.now ())
fun fresh () = string_of_int (run_tag + serial ())
\<close>

section \<open>Constructs\<close>

text \<open>Every guard must reach prove_or_refute and then defeat, or need, one prover
in particular.  An intro! rule that loops upward (\<open>SPIN\<close>, \<open>BLIND_SPIN\<close>) burns
P-auto's budget; a chain of safe intro! steps that terminates in success
(\<open>CHAIN\<close>) needs P-auto; a chain of safe elim! steps that terminates in a
contradiction (\<open>FALLS\<close>) makes a hypothesis vacuous the slow way; \<open>LOOP\<close> and \<open>PP\<close>
make a guard provable ONLY with a judge lemma that loops.\<close>

(* BAD: false atom invisible to simp (no simp rule), instantly eliminable by
   the classical refuter (elim!), and a countermodel for the model refuter:
   the one atom BOTH refuters decide.
   SPIN: goal-side-only spinner -- the intro! rule loops upward forever, so
   PROVING `SPIN n` burns any budget, while `SPIN n` as an ASSUMPTION is
   inert (no elim rule). *)
definition BAD :: bool where "BAD = False"
lemma BAD_E[elim!]: "BAD \<Longrightarrow> P" unfolding BAD_def by simp

definition SPIN :: "nat \<Rightarrow> bool" where "SPIN n = False"
lemma SPIN_I[intro!]: "SPIN (Suc n) \<Longrightarrow> SPIN n" unfolding SPIN_def by simp

(* BADN: false atom with NO rule at all -- no simp rule, no elim rule.  The
   classical refuter cannot touch it (auto cannot unfold a bare definition),
   so R-conv comes back empty; Nitpick unfolds definitions and refutes. *)
definition BADN :: "nat \<Rightarrow> bool" where "BADN n = False"

(* BLIND_SPIN: false, yet TRUE IN EVERY FINITE MODEL, so the model refuter --
   which only ever searches finite scopes -- can never exhibit a
   countermodel.  The elim! rule kills it in the classical refuter in one
   step, and the intro! rule loops upward like SPIN's: the construct every
   "R-conv must refute" probe needs. *)
definition BLIND_SPIN :: "nat \<Rightarrow> bool"
  where "BLIND_SPIN n = finite (UNIV::nat set)"
lemma BLIND_SPIN_E[elim!]: "BLIND_SPIN n \<Longrightarrow> P" unfolding BLIND_SPIN_def by simp
lemma BLIND_SPIN_I[intro!]: "BLIND_SPIN (Suc n) \<Longrightarrow> BLIND_SPIN n"
  unfolding BLIND_SPIN_def by simp

(* CHAIN: provable, but only after one safe intro! step per list element --
   a tunable amount of successful search.  True by definition, so the model
   refuter finds nothing either. *)
definition CHAIN :: "nat list \<Rightarrow> bool" where "CHAIN xs = True"
lemma CHAIN_nil[intro!]: "CHAIN []" unfolding CHAIN_def by simp
lemma CHAIN_cons[intro!]: "CHAIN xs \<Longrightarrow> CHAIN (x # xs)" unfolding CHAIN_def by simp

(* FALLS: false, and refuted only after one safe elim! step per list element
   -- a tunable amount of search before the contradiction shows up.  Used as
   a HYPOTHESIS, it makes a guard vacuous the slow way. *)
definition FALLS :: "nat list \<Rightarrow> bool" where "FALLS xs = False"
lemma FALLS_nil[elim!]: "FALLS [] \<Longrightarrow> P" unfolding FALLS_def by simp
lemma FALLS_cons[elim!]: "FALLS (x # xs) \<Longrightarrow> (FALLS xs \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding FALLS_def by simp

(* SOMETRUE: true for exactly one argument, with an intro! rule that supplies
   that argument.  As a guard with a schematic variable it is provable BY
   INSTANTIATION and must therefore never be refuted. *)
definition SOMETRUE :: "nat \<Rightarrow> bool" where "SOMETRUE n = (n = 0)"
lemma SOMETRUE_I[intro!]: "SOMETRUE 0" unfolding SOMETRUE_def by simp

(* BADT: BADN with a type argument -- rule-free too, so the classical refuter
   comes back empty and the call reaches R-nitpick, whose screen stands the
   whole refuter down on a schematic TYPE variable.  The carrier of that probe. *)
definition BADT :: "'a \<Rightarrow> bool" where "BADT x = False"

(* LOOP, PP: the lemma path.  Neither has a simp rule.  `PP (LOOP n)` is
   provable by PP_I only once the argument is at least four LOOPs deep, which
   the looping judge lemma `LOOP n = LOOP (LOOP n)` achieves -- and only
   because the lemma budget cuts the loop off: without the budget the rewrite
   would run until the timeout; without the lemma nothing proves it, R-conv
   cannot refute a true statement and the model refuter finds no countermodel
   to a truth, so the guard ends unknown. *)
definition LOOP :: "nat \<Rightarrow> nat" where "LOOP n = n"
definition PP :: "nat \<Rightarrow> bool" where "PP n = True"
lemma PP_I[intro!]: "PP (LOOP (LOOP (LOOP (LOOP x))))" unfolding PP_def by simp

(* QQ, RR: a deletion observed in the provers' context.  QQ n is provable by
   QQ_I once RR n is, and RR n only through the lemma `RR n = True`, whose
   left-hand side first appears in the subgoal the classical search creates:
   guard_simp_tac, which sees the goal before QQ_I is applied, never meets it,
   and only the searches -- P-auto's, and R-conv's -- can use it. *)
definition RR :: "nat \<Rightarrow> bool" where "RR n = True"
definition QQ :: "nat \<Rightarrow> bool" where "QQ n = True"
lemma QQ_I[intro!]: "RR n \<Longrightarrow> QQ n" unfolding QQ_def by simp

ML \<open>(*chain length, tuned by measurement: CHAIN's intro! search is superlinear
  and must finish well inside the 400 ms P-auto budget with a margin for a
  loaded machine -- the bound is thread CPU, which contention still inflates
  (1000 = 126 ms unloaded, but it proved in 220 ms and once missed the bound
  with the corpus loading alongside; 700 leaves the margin).*)
fun chain_list n = "[" ^ commas (map string_of_int (1 upto n)) ^ "]"
val intro_chain = chain_list 700
val elim_chain = chain_list 800

(*the judge lemmas; times are raw measurements, floored to the classic bound at replay*)
val times = {thread_cpu = Time.fromMilliseconds 20, wall = Time.fromMilliseconds 20}
fun lemma ctxt stmt script tier = (Syntax.read_prop ctxt stmt, (times, script), tier)
fun looping ctxt = lemma ctxt "\<And>n. LOOP n = LOOP (LOOP n)" "(simp add: LOOP_def)" Phi_Guard_Cache.Only_Once
fun useless ctxt = lemma ctxt "CHAIN []" "(rule CHAIN_nil)" Phi_Guard_Cache.Rarely
fun useless_once ctxt = lemma ctxt "CHAIN []" "(rule CHAIN_nil)" Phi_Guard_Cache.Only_Once
(*the replacement probe's entry lemma: its statement must DIFFER from the seeded one
  (CHAIN []), or add_lemma merges the two and the probe cannot fail*)
fun useless_other ctxt = lemma ctxt "CHAIN [1]" "(rule CHAIN_cons, rule CHAIN_nil)" Phi_Guard_Cache.Rarely
fun unreplayable ctxt = lemma ctxt "\<And>n. LOOP n = LOOP (LOOP n)" "(rule no_such_fact)" Phi_Guard_Cache.Normal
(*a true lemma that rewrites a BADN guard to False*)
fun badn_false ctxt = lemma ctxt "\<And>n. BADN n = False" "(simp add: BADN_def)" Phi_Guard_Cache.Normal
fun uncertifiable ctxt = (Syntax.read_term ctxt "LOOP 0", (times, "simp"), Phi_Guard_Cache.Normal)

(*a run context that already carries a lemma of an earlier guard: CHAIN [] at
  budget 30, the budget of Rarely*)
fun seeded ctxt = Phi_Guard_Cache.add_lemma (@{thm CHAIN_nil}, 30) ctxt
val chain_nil = Thm.prop_of @{thm CHAIN_nil}
(*the looping lemma and the RR lemma as theorems, for seeding them directly; Goal.prove
  exports, so their propositions carry ?n where the statements bind n*)
fun looping_thm ctxt =
  Goal.prove ctxt [] [] (#1 (looping ctxt)) (fn {context, ...} => simp_tac (context addsimps @{thms LOOP_def}) 1)
fun rr_thm ctxt =
  Goal.prove ctxt [] [] (Syntax.read_prop ctxt "\<And>n. RR n = True")
    (fn {context, ...} => simp_tac (context addsimps @{thms RR_def}) 1)\<close>

section \<open>The lemma budget on its own\<close>

(*enhance_with_lemmas on a non-empty list: the looping lemma at budget 3 rewrites
  LOOP 0 exactly three times and then stops matching*)
ML \<open>
let val ctxt = \<^context>
    val ctxt' = Phi_Guard_Cache.add_lemma (looping_thm ctxt, 3) ctxt |> Phi_Guard_Cache.enhance_with_lemmas
    val rhs = Thm.rhs_of (Simplifier.rewrite ctxt' \<^cterm>\<open>LOOP 0\<close>)
    val expected = \<^cterm>\<open>LOOP (LOOP (LOOP (LOOP 0)))\<close>
 in if Thm.term_of rhs aconv Thm.term_of expected then writeln "budget: three rewrites, then cut off"
    else error ("budget: expected " ^ Syntax.string_of_term ctxt (Thm.term_of expected) ^
                " but got " ^ Syntax.string_of_term ctxt (Thm.term_of rhs))
end\<close>

section \<open>No entry\<close>

ML \<open>test plain \<^context> "no entry, proved by P-auto; nothing written"
  (expect ("proved", "none", "-", "-") "no entry")
  ("\<condition> (CHAIN (" ^ fresh () ^ " # " ^ intro_chain ^ "))")\<close>

ML \<open>test plain \<^context> "no entry, refuted by R-conv"
  (expect ("refuted", "none", "R-conv", "-") "Refuted with 0 lemma(s)")
  ("\<condition> (BLIND_SPIN " ^ fresh () ^ ")")\<close>

(*needs the external kodkodi process*)
ML \<open>test plain \<^context> "no entry, refuted by R-nitpick"
  (expect ("refuted", "none", "R-nitpick", "-") "Refuted with 0 lemma(s)")
  ("\<condition> (BADN " ^ fresh () ^ " \<and> SPIN 0)")\<close>

(*BAD is decided by both refuters; the fixed order (plan section 5 step 4) makes
  R-conv the one that answers*)
ML \<open>test plain \<^context> "no entry, refutable by both refuters: R-conv answers first"
  (expect ("refuted", "none", "R-conv", "-") "Refuted with 0 lemma(s)")
  ("\<condition> (BAD \<and> SPIN " ^ fresh () ^ ")")\<close>

(*the undecided-guard warning is printed here (trace-gated, \<phi>trace_reasoning = 3)*)
ML \<open>test plain \<^context> "no entry, nobody decides, no judge: the undecided-guard warning; Unknown written"
  (expect ("unknown", "none", "-", "-") "Unknown with 0 lemma(s)")
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

(*vacuous hypothesis: FALLS ... is contradictory, so both `H \<Longrightarrow> C` and `H \<Longrightarrow> \<not>C`
  are provable; P-auto runs first and proves it, no refuter is consulted*)
ML \<open>test plain \<^context> "vacuous hypothesis (proved by P-auto, not refuted)"
  (expect ("proved", "none", "-", "-") "no entry")
  ("FALLS " ^ elim_chain ^ " \<Longrightarrow> \<condition> (SPIN " ^ fresh () ^ ")")\<close>

section \<open>Hits\<close>

(*the entry's verdict selects the path; each probe uses a fresh guard*)
ML \<open>test (with_entry [] Phi_Guard_Cache.Refuted) \<^context>
  "Refuted hit, P-auto fails: silent, no refuter, entry kept"
  (expect ("refuted", "refuted", "-", "-") "Refuted with 0 lemma(s)")
  ("\<condition> (BLIND_SPIN " ^ fresh () ^ ")")\<close>

ML \<open>test (with_entry [] Phi_Guard_Cache.Refuted) \<^context>
  "Refuted hit, P-auto proves: silent promotion to Proved"
  (expect ("proved", "refuted", "-", "-") "Proved with 0 lemma(s)")
  ("\<condition> (CHAIN (" ^ fresh () ^ " # " ^ intro_chain ^ ") \<and> True)")\<close>

ML \<open>test (with_entry [] Phi_Guard_Cache.Unknown) \<^context>
  "Unknown hit, no judge: the undecided-guard warning again, no refuter, nothing rewritten"
  (expect ("unknown", "unknown", "-", "-") "Unknown with 0 lemma(s)")
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

ML \<open>assert_loud "a refuter's verdict over a Proved entry" 0 (warnings_of (fn () =>
  test (with_entry [] Phi_Guard_Cache.Proved) \<^context>
    "Proved hit that P-auto cannot prove: R-conv refutes it silently, Refuted written"
    (expect ("refuted", "proved", "R-conv", "-") "Refuted with 0 lemma(s)")
    ("\<condition> (BLIND_SPIN " ^ fresh () ^ ")")))\<close>

(*a Proved entry does not change the report unless the judge overturns it: this
  ending gets the undecided-guard warning, as a call without an entry does; the
  delta stays through the Unknown write*)
ML \<open>assert_undecided "an Unknown ending over a Proved entry" 1 (warnings_of (fn () =>
  test (with_delta {added = [useless_other \<^context>], deleted = [chain_nil]} Phi_Guard_Cache.Proved) \<^context>
    "Proved hit that nobody decides, no judge: the undecided-guard warning, Unknown written"
    (expect ("unknown", "proved", "-", "-") "Unknown with 1 lemma(s), 1 deletion(s)")
    ("\<condition> (PP (LOOP " ^ fresh () ^ "))")))\<close>

section \<open>Lemmas\<close>

(*the looping lemma, enabled from an Unknown entry, cut off by its budget of 3 --
  the guard is proved only through it; the returned context carries it*)
ML \<open>
let val ctxt = \<^context>
    val r = test (with_entry [looping ctxt] Phi_Guard_Cache.Unknown) ctxt
      "Unknown hit with a looping lemma: enabled, cut off by its budget, P-auto proves; Proved written"
      (expect ("proved", "unknown", "-", "-") "Proved with 1 lemma(s)")
      ("\<condition> (PP (LOOP " ^ fresh () ^ "))")
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(_, 3)] => writeln "the returned context carries the lemma at budget 3"
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

(*a lemma at zero stops matching but is enabled again with a fresh budget at the
  next call: the same entry decides the same way twice*)
ML \<open>test (with_entry [looping \<^context>] Phi_Guard_Cache.Proved) \<^context>
  "Proved hit with the looping lemma: proved again, fresh budget"
  (expect ("proved", "proved", "-", "-") "Proved with 1 lemma(s)")
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

(*two dropped lemmas -- one uncertifiable, one unreplayable -- each with the
  dropped-lemma warning; the entry is rewritten without them, P-auto then fails,
  both refuters fail, the undecided-guard warning, Unknown written*)
ML \<open>test (with_entry [uncertifiable \<^context>, unreplayable \<^context>] Phi_Guard_Cache.Proved) \<^context>
  "Proved hit whose lemmas fail to certify and to replay: both dropped, Unknown written"
  (expect ("unknown", "proved", "-", "-") "Unknown with 0 lemma(s)")
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

(*step 1's drop write on its own: a Refuted hit writes nothing afterwards, so the
  entry left is the one step 1 rewrote -- the survivor without the dropped lemma*)
ML \<open>test (with_entry [useless \<^context>, unreplayable \<^context>] Phi_Guard_Cache.Refuted) \<^context>
  "Refuted hit with a replayable and an unreplayable lemma: the drop write is the store's final state"
  (expect ("refuted", "refuted", "-", "-") "Refuted with 1 lemma(s)")
  ("\<condition> (BLIND_SPIN " ^ fresh () ^ ")")\<close>

(*a lemma that replays but does not suffice: it stays in the entry through a refutation,
  and so does the entry's deletion*)
ML \<open>test (with_delta {added = [useless \<^context>], deleted = [chain_nil]} Phi_Guard_Cache.Proved) \<^context>
  "Proved hit with an insufficient lemma: R-conv refutes, the delta stays"
  (expect ("refuted", "proved", "R-conv", "-") "Refuted with 1 lemma(s), 1 deletion(s)")
  ("\<condition> (BLIND_SPIN " ^ fresh () ^ ")")\<close>

section \<open>An entry's deletion\<close>

(*the entry's delta deletes an earlier guard's lemma by its proposition: the run
  context carries CHAIN [] (seeded), the Unknown entry deletes it and adds the
  looping lemma; the returned list holds the looping lemma alone*)
ML \<open>
let val ctxt = seeded \<^context>
    val r = decide (with_delta {added = [looping ctxt], deleted = [chain_nil]} Phi_Guard_Cache.Unknown) ctxt
      "Unknown hit whose delta deletes the seeded lemma: gone from the returned context, Proved written"
      (expect ("proved", "unknown", "-", "-") "Proved with 1 lemma(s), 1 deletion(s)")
      (read false ctxt ("\<condition> (PP (LOOP " ^ fresh () ^ "))"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(_, 3)] => writeln "the seeded lemma is deleted, the entry's lemma alone remains"
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

(*a deletion naming no lemma of the list deletes nothing: the seeded lemma survives
  at its budget -- the probe that catches over-deletion*)
ML \<open>
let val ctxt = seeded \<^context>
    val r = decide (with_delta {added = [], deleted = [#1 (useless_other ctxt)]} Phi_Guard_Cache.Unknown) ctxt
      "Unknown hit whose delta deletes a lemma the context does not carry: nothing deleted, Proved written"
      (expect ("proved", "unknown", "-", "-") "Proved with 0 lemma(s), 1 deletion(s)")
      (read false ctxt ("FALLS " ^ elim_chain ^ " \<Longrightarrow> \<condition> (SPIN " ^ fresh () ^ ")"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(th, 30)] =>
             if Thm.prop_of th aconv chain_nil then writeln "the seeded lemma survives at budget 30"
             else error ("the returned context carries " ^ show_lemmas ctxt1)
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

(*a deletion reaches the provers' context.  Not with the looping lemma: it rewrites
  the guard term itself, so guard_simp_tac applies it and no search is needed.  RR's
  lemma is met only by P-auto's search (QQ, RR above): seeded, an empty delta proves
  the guard through it; the deletion leaves nobody to decide.  A deletion names the
  proposition as the list holds it, here `RR ?n = True`*)
ML \<open>
let val th = rr_thm \<^context>
    val ctxt = Phi_Guard_Cache.add_lemma (th, 3) \<^context>
    val _ = test (with_entry [] Phi_Guard_Cache.Unknown) ctxt
      "the seeded RR lemma, Unknown hit with an empty delta: P-auto proves through it, Proved written"
      (expect ("proved", "unknown", "-", "-") "Proved with 0 lemma(s)")
      ("\<condition> (QQ " ^ fresh () ^ ")")
 in test (with_delta {added = [], deleted = [Thm.prop_of th]} Phi_Guard_Cache.Unknown) ctxt
      "the seeded RR lemma, Unknown hit whose delta deletes it: nobody decides"
      (expect ("unknown", "unknown", "-", "-") "Unknown with 0 lemma(s), 1 deletion(s)")
      ("\<condition> (QQ " ^ fresh () ^ ")")
end\<close>

(*the identity is Pattern.equiv: a deletion naming the seeded lemma under other
  schematic names removes it; under aconv it would survive*)
ML \<open>
let val ctxt = Phi_Guard_Cache.add_lemma (looping_thm \<^context>, 3) \<^context>
    val r = decide (with_delta {added = [], deleted = [read true ctxt "LOOP ?m = LOOP (LOOP ?m)"]} Phi_Guard_Cache.Unknown) ctxt
      "Unknown hit whose delta names the seeded lemma under other schematic names: deleted"
      (expect ("proved", "unknown", "-", "-") "Proved with 0 lemma(s), 1 deletion(s)")
      (read false ctxt ("FALLS " ^ elim_chain ^ " \<Longrightarrow> \<condition> (SPIN " ^ fresh () ^ ")"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [] => writeln "the seeded lemma is deleted under renamed schematic variables"
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

(*a delta deletes before it adds: deleting and adding the seeded lemma in one delta
  leaves exactly one copy at the delta's budget*)
ML \<open>
let val ctxt = seeded \<^context>
    val r = decide (with_delta {added = [useless_once ctxt], deleted = [chain_nil]} Phi_Guard_Cache.Unknown) ctxt
      "Unknown hit whose delta deletes and adds the seeded lemma: one copy, at the delta's budget"
      (expect ("proved", "unknown", "-", "-") "Proved with 1 lemma(s), 1 deletion(s)")
      (read false ctxt ("FALLS " ^ elim_chain ^ " \<Longrightarrow> \<condition> (SPIN " ^ fresh () ^ ")"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(th, 3)] =>
             if Thm.prop_of th aconv chain_nil then writeln "deleted, then added: one copy at budget 3"
             else error ("the returned context carries " ^ show_lemmas ctxt1)
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

section \<open>The one append rule\<close>

(*a replayed entry rebuilds the list the recording call returned: a proposition already
  in the list takes the delta's budget (the one rule of step 1 and step 6)*)
ML \<open>
let val ctxt = seeded \<^context>
    val r = decide (with_entry [useless_once ctxt] Phi_Guard_Cache.Unknown) ctxt
      "Unknown hit adding the seeded lemma at Only_Once: its budget becomes 3"
      (expect ("proved", "unknown", "-", "-") "Proved with 1 lemma(s)")
      (read false ctxt ("FALLS " ^ elim_chain ^ " \<Longrightarrow> \<condition> (SPIN " ^ fresh () ^ ")"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(th, 3)] =>
             if Thm.prop_of th aconv chain_nil then writeln "the seeded lemma now at the entry's budget 3"
             else error ("the returned context carries " ^ show_lemmas ctxt1)
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

section \<open>The judge\<close>

(*Provable REPLACES this entry's delta and no other: the run context carries an
  earlier guard's lemma (seeded), the Unknown entry adds `useless_other` and deletes
  the seeded lemma; no refuter runs, the judge is consulted on the context as it was
  BEFORE the delta -- the seeded lemma there, `useless_other` not -- and with the
  entry's delta (the contract check in `run_guard`); its delta, applied to that
  context, gives the seeded lemma at its own budget followed by the judge's --
  `useless_other` gone, the entry's deletion gone*)
ML \<open>
let val ctxt = seeded \<^context>
    val r = decide (with_delta_and_judge {added = [useless_other ctxt], deleted = [chain_nil]} Phi_Guard_Cache.Unknown
                      (fn _ => Phi_Reasoners.Provable (adds [looping ctxt]))) ctxt
      "Unknown hit with a delta, the judge answers Provable: the delta replaced whole, the earlier lemma kept"
      (expect ("proved", "unknown", "-", "Provable") "Proved with 1 lemma(s)")
      (read false ctxt ("\<condition> (PP (LOOP " ^ fresh () ^ "))"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(th, 30), (_, 3)] =>
             if Thm.prop_of th aconv chain_nil then writeln "the seeded lemma stays first at budget 30, the judge's follows at 3"
             else error ("the returned context carries " ^ show_lemmas ctxt1)
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

(*the judge deletes an earlier guard's lemma by its proposition; the deletion is
  written with the entry*)
ML \<open>
let val ctxt = seeded \<^context>
    val r = decide (with_judge (fn _ => Phi_Reasoners.Provable {added = [looping ctxt], deleted = [chain_nil]})) ctxt
      "no entry, the judge answers Provable deleting the seeded lemma: gone, the deletion written"
      (expect ("proved", "none", "-", "Provable") "Proved with 1 lemma(s), 1 deletion(s)")
      (read false ctxt ("\<condition> (PP (LOOP " ^ fresh () ^ "))"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(_, 3)] => writeln "the seeded lemma is deleted, the judge's lemma alone remains"
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

(*a judge lemma of a proposition already in the list takes the judge's budget*)
ML \<open>
let val ctxt = seeded \<^context>
    val r = decide (with_judge (fn _ => Phi_Reasoners.Provable (adds [useless_once ctxt, looping ctxt]))) ctxt
      "the judge re-proposes the seeded lemma at Only_Once: its budget is updated"
      (expect ("proved", "none", "-", "Provable") "Proved with 2 lemma(s)")
      (read false ctxt ("\<condition> (PP (LOOP " ^ fresh () ^ "))"))
 in case r of
      SOME (ctxt1, _) =>
        (case Phi_Guard_Cache.get_lemmas ctxt1 of
           [(th, 3), (_, 3)] =>
             if Thm.prop_of th aconv chain_nil then writeln "the seeded lemma now at budget 3, the judge's looping lemma follows"
             else error ("the returned context carries " ^ show_lemmas ctxt1)
         | _ => error ("the returned context carries " ^ show_lemmas ctxt1))
    | NONE => error "no state returned"
end\<close>

(*a Proved hit the entry's lemma cannot carry: the judge's delta replaces the entry's,
  P-auto proves, the entry is rewritten -- and no loud warning (plan section 5 step 6)*)
ML \<open>test (with_entry_and_judge [useless \<^context>] Phi_Guard_Cache.Proved
            (fn _ => Phi_Reasoners.Provable (adds [looping \<^context>]))) \<^context>
  "Proved hit, refuters fail, the judge answers Provable: the entry's lemma is replaced, no warning"
  (expect ("proved", "proved", "-", "Provable") "Proved with 1 lemma(s)")
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

ML \<open>test (with_judge (K Phi_Reasoners.Unprovable)) \<^context>
  "no entry, refuters fail, the judge answers Unprovable: Refuted written, no warning"
  (expect ("refuted", "none", "-", "Unprovable") "Refuted with 0 lemma(s)")
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

ML \<open>test (with_delta_and_judge {added = [useless_other \<^context>], deleted = [chain_nil]} Phi_Guard_Cache.Unknown
            (K Phi_Reasoners.Unprovable)) \<^context>
  "Unknown hit with a judge: no refuter runs, the judge decides; the delta stays"
  (expect ("refuted", "unknown", "-", "Unprovable") "Refuted with 1 lemma(s), 1 deletion(s)")
  ("\<condition> (BLIND_SPIN " ^ fresh () ^ ")")\<close>

ML \<open>assert_loud "the judge overturning a Proved entry" 1 (warnings_of (fn () =>
  test (with_entry_and_judge [] Phi_Guard_Cache.Proved (K Phi_Reasoners.Unprovable)) \<^context>
    "Proved hit, refuters fail, the judge answers Unprovable: the loud guard warning"
    (expect ("refuted", "proved", "-", "Unprovable") "Refuted with 0 lemma(s)")
    ("\<condition> (PP (LOOP " ^ fresh () ^ "))")))\<close>

(*the judge's lemma may not fail: the error names the judge*)
ML \<open>test_error (with_judge (fn _ => Phi_Reasoners.Provable (adds [unreplayable \<^context>]))) \<^context>
  "the judge proposes a lemma that fails to replay: error"
  "The judge is broken: its lemma fails to replay"
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

(*a Provable after which P-auto still fails: the other error*)
ML \<open>test_error (with_judge (fn _ => Phi_Reasoners.Provable (adds [useless \<^context>]))) \<^context>
  "the judge answers Provable with a lemma that does not suffice: error"
  "The judge is broken: P-auto cannot prove"
  ("\<condition> (PP (LOOP " ^ fresh () ^ "))")\<close>

(*the simplifier refuting a Proved entry: the entry's own lemma rewrites the guard to
  False at step 1 1/2 -- Refuted written with the delta, the refuter guard_simp_tac in
  the record, the loud guard warning naming the simplifier; neither P-auto nor R-conv
  nor R-nitpick nor the judge runs*)
ML \<open>assert_loud_simp "the simplifier refuting a Proved entry" 1 (warnings_of (fn () =>
  test (with_entry [badn_false \<^context>] Phi_Guard_Cache.Proved) \<^context>
    "Proved hit whose lemma rewrites the guard to False: refuted by the simplifier, Refuted written"
    (expect ("refuted", "proved", "guard_simp_tac", "-") "Refuted with 1 lemma(s)")
    ("\<condition> (BADN " ^ fresh () ^ ")")))\<close>

(*a Provable whose lemma rewrites the guard to False: the third error.  An Unknown hit
  goes straight to the judge, so no refuter pre-empts it; BADN has no rule, so P-auto
  fails, and the judge's true lemma `BADN n = False` lets guard_simp_tac rewrite the
  conclusion to False, which the judge path's own test refuses for an ordinary guard*)
ML \<open>test_error (with_entry_and_judge [] Phi_Guard_Cache.Unknown
                (fn _ => Phi_Reasoners.Provable (adds [badn_false \<^context>]))) \<^context>
  "the judge answers Provable with a lemma that rewrites the guard to False: error"
  "The judge is broken: its lemmas rewrite the guard to False"
  ("\<condition> (BADN " ^ fresh () ^ ")")\<close>

section \<open>The check\<close>

(*\<check> \<premise> \<consistency>, the guard \<condition> False as written (plan section 1,
  the check; the probes' design is the check plan's section 6, which that entry names):
  decided without the three steps that presuppose consistent premises -- the refutation by the
  simplifier, R-conv, R-nitpick's slice -- and ending with the verdicts of the check:
  Proved when the premises are found inconsistent, Refuted on R-nitpick's model of them
  or on the judge's Unprovable, Unknown otherwise.  The conclusion is the literal False
  and cannot carry the fresh numeral, so the numeral goes into a premise.*)

(*the simplification finds the contradiction: proved with refuter -, nothing written*)
ML \<open>test plain \<^context> "the check, the premises contradictory by simp: proved"
  (expect ("proved", "none", "-", "-") "no entry")
  ("Suc " ^ fresh () ^ " = 0 \<Longrightarrow> \<check> \<premise> \<consistency>")\<close>

(*P-auto finds it: FALLS has no simp rule, and FALLS_cons ignores the head*)
ML \<open>test plain \<^context> "the check, the premises contradictory by P-auto's search: proved"
  (expect ("proved", "none", "-", "-") "no entry")
  ("FALLS (" ^ fresh () ^ " # " ^ elim_chain ^ ") \<Longrightarrow> \<check> \<premise> \<consistency>")\<close>

(*consistent premises: R-nitpick exhibits a model of them.  This probe reads
  "guard_simp_tac" if the refutation by the simplifier still fires on a check, and
  "R-conv" if R-conv is not skipped*)
ML \<open>test plain \<^context> "the check, consistent premises: refuted by R-nitpick's model"
  (expect ("refuted", "none", "R-nitpick", "-") "Refuted with 0 lemma(s)")
  ("CHAIN [" ^ fresh () ^ "] \<Longrightarrow> \<check> \<premise> \<consistency>")\<close>

(*the check is not mode-specific: the same path under \<condition>[NO_INST] False*)
ML \<open>test plain \<^context> "the check under NO_INST: the same path"
  (expect ("refuted", "none", "R-nitpick", "-") "Refuted with 0 lemma(s)")
  ("CHAIN [" ^ fresh () ^ "] \<Longrightarrow> \<condition>[NO_INST] False")\<close>

(*undecided: BADN has no rule for P-auto and no model for Nitpick -- the undecided-check
  warning once, the undecided-guard warning never, Unknown written.  With the premise
  still sliced away this would read ("refuted", "none", "R-nitpick", "-")*)
ML \<open>assert_undecided_check "the check nobody decides" 1 (warnings_of (fn () =>
  test plain \<^context> "the check, a premise nobody decides: the undecided-check warning, Unknown written"
    (expect ("unknown", "none", "-", "-") "Unknown with 0 lemma(s)")
    ("BADN " ^ fresh () ^ " \<Longrightarrow> \<check> \<premise> \<consistency>")))\<close>

(*the judge overturns a Proved entry of a check: the loud guard warning naming the judge*)
ML \<open>assert_loud "the judge overturning a Proved check" 1 (warnings_of (fn () =>
  test (with_entry_and_judge [] Phi_Guard_Cache.Proved (K Phi_Reasoners.Unprovable)) \<^context>
    "the check, Proved hit, nobody decides, the judge answers Unprovable: the loud guard warning"
    (expect ("refuted", "proved", "-", "Unprovable") "Refuted with 0 lemma(s)")
    ("BADN " ^ fresh () ^ " \<Longrightarrow> \<check> \<premise> \<consistency>")))\<close>

(*the regression probe: an ordinary guard the template's rewrite turns into
  \<condition> False, under a prefix -- the kind is read on the state as written, so it
  keeps the refutation by the simplifier, and no warning line*)
ML \<open>assert_only "an ordinary guard rewritten to False" loud_line 0 (warnings_of (fn () =>
  test plain \<^context> "an ordinary guard the template's rewrite turns into False: refuted by the simplifier"
    (expect ("refuted", "none", "guard_simp_tac", "-") "Refuted with 0 lemma(s)")
    ("CHAIN [" ^ fresh () ^ "] \<Longrightarrow> \<condition> (Suc " ^ fresh () ^ " = 0)")))\<close>

(*the digest marker, through the digest step itself: two states as written, one of each
  kind, given as guard_digest_of's first argument, digest ONE state differently -- one
  assertion over the marker, over guard_kind_of on both written forms, and over
  guard_digest_of reading its first argument (the wiring inside guard_condition_judge is
  not covered)*)
ML \<open>
let val ctxt = \<^context>
    fun state s = Thm.trivial (Thm.cterm_of ctxt (read false ctxt s))
    val st = state "CHAIN [1] \<Longrightarrow> \<check> \<premise> \<consistency>"
    fun hex th0 = Hasher.hex (Phi_Reasoners.guard_digest_of th0 ctxt st)
 in if hex st <> hex (state "CHAIN [1] \<Longrightarrow> \<condition> (Suc 0 = 0)")
    then writeln "the digest marker: the check's kind and an ordinary guard's digest one state differently"
    else error "the digest marker: the two kinds digest one state alike"
end\<close>

section \<open>The method \<phi>guard_P_auto\<close>

(*no caller anywhere, so it is exercised here: the guard-side simplification and P-auto on
  a raw Isar goal with a BARE False conclusion (the method's context carries no
  Premise_def, so a tagged conclusion is never unfolded there).  The cut that used to sit
  inside guard_simp_tac failed this at once; now P-auto proves it from the premise*)
lemma "FALLS [1,2,3,4,5,6,7,8,9,10] \<Longrightarrow> False" by \<phi>guard_P_auto

(*the negative control: consistent premises, and the method must still fail*)
lemma "CHAIN [1] \<Longrightarrow> False"
  apply (fails \<open>\<phi>guard_P_auto\<close>)
  oops

section \<open>The switch and the variable disciplines\<close>

(*\<phi>guard_cache = false: the injected entry is neither read nor rewritten -- its
  verdict differs from the one this call reaches, so a leaked write would show*)
ML \<open>
let val ctxt = Config.put Phi_Guard_Cache.guard_cache false \<^context>
 in test (with_entry [] Phi_Guard_Cache.Unknown) ctxt
      "cache off: the Unknown entry is ignored, R-conv runs, nothing written"
      (expect ("refuted", "none", "R-conv", "-") "Unknown with 0 lemma(s)")
      ("\<condition> (BLIND_SPIN " ^ fresh () ^ ")")
end\<close>

(*can_inst = true and SOME instantiation is provable: neither refuter may kill
  it -- P-auto proves by instantiation first*)
ML \<open>test schematic \<^context> "instantiable guard, some instance provable (proved by P-auto)"
  (expect ("proved", "none", "-", "-") "no entry")
  ("\<condition> (CHAIN (" ^ fresh () ^ " # " ^ intro_chain ^ ") \<and> SOMETRUE ?x)")\<close>

(*the control -- every instantiation false: R-conv's frozen-Free branch*)
ML \<open>test schematic \<^context> "instantiable guard, every instance false (refuted by R-conv)"
  (expect ("refuted", "none", "R-conv", "-") "Refuted with 0 lemma(s)")
  ("\<condition> (BLIND_SPIN ?x \<and> SPIN " ^ fresh () ^ ")")\<close>

(*a schematic TYPE variable silences R-nitpick (its screen): BADT has no rule, so
  R-conv comes back empty and the call reaches R-nitpick, which stands down; the
  guard ends unknown.  Nothing in the surface syntax produces a schematic ?'a
  (read_prop FIXES type variables), hence the term surgery.*)
ML \<open>
let val t = Syntax.read_prop \<^context> ("\<condition> (BADT (undefined::'a) \<and> SPIN " ^ fresh () ^ ")")
    val t' = Term.map_types (Term.map_atyps
               (fn TFree (a, S) => TVar ((a, 0), S) | T => T)) t
 in decide plain \<^context> "schematic type variable: the model refuter is silenced, nobody decides"
      (expect ("unknown", "none", "-", "-") "Unknown with 0 lemma(s)") t'
end\<close>

(*pollution immunity: everything set below would break R-nitpick if the pinned
  parameter list (pinned_nitpick_params) did not override it: `expect` would
  raise on the genuine outcome, the 1ms timeout would abort the search, card 1-1
  would shrink the scope, and verbose would break silence.  Kept LAST in the
  theory because it changes theory-level defaults for everything after it.*)
nitpick_params [expect = unknown, timeout = 0.001, card = 1-1,
                max_potential = 5, verbose]

ML \<open>test plain \<^context> "nitpick_params pollution immunity"
  (expect ("refuted", "none", "R-nitpick", "-") "Refuted with 0 lemma(s)")
  ("\<condition> (BADN " ^ fresh () ^ " \<and> SPIN 0)")\<close>

end
