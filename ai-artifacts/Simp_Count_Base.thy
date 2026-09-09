theory Simp_Count_Base
  imports
    Phi_Semantics.PhiSem_CF_Routine
    Phi_Semantics.PhiSem_CF_Breakable
    Phi_Semantics.PhiSem_Variable
    Phi_Semantics.PhiSem_Int_ArbiPrec
    Phi_Semantics.PhiSem_Aggregate_Array
    Phi_Semantics.PhiSem_Aggregate_Tuple
    "HOL-Computational_Algebra.Primes"
begin

section \<open>Per-invocation rewrite counting through Raw_Simplifier.trace_ops\<close>

text \<open>
  One \<^emph>\<open>invocation\<close> = one top-level call of \<^ML>\<open>Raw_Simplifier.rewrite_cterm\<close>.
  Nested calls (conditional-premise proving, subgoalers, solvers) inherit the
  enclosing invocation's record, because \<^ML_text>\<open>trace_invoke\<close> returns the context
  that the whole simplification is run under.  So "top level" is detected
  structurally (our context slot is still empty), not by comparing depths;
  the depth reported by the simplifier is recorded anyway, for the record.
\<close>

ML \<open>
structure Simp_Count =
struct

(* ------------------------------------------------------------------ *)
(* one live invocation                                                  *)

type live =
 {no: int,
  depth: int,
  goal: term,
  counts: int Symtab.table Synchronized.var};

(* ------------------------------------------------------------------ *)
(* accumulated summary of finished invocations                          *)

type summary =
 {n_inv: int,                          (*invocations started*)
  n_folded: int,                       (*invocations already summarised*)
  depths: int Inttab.table,            (*top-level depth -> occurrences*)
  max_hist: int * int * int * int,     (*max single-rule count per invocation*)
  tot_hist: int * int * int * int,     (*total rewrites per invocation*)
  grand_total: int,
  rule_max: int Symtab.table,          (*rule -> max count in one invocation*)
  rule_tot: int Symtab.table,          (*rule -> total count over all*)
  hot: (int * term * int * (string * int) list) list};  (*invocations with a rule >= 100*)

val empty_summary : summary =
 {n_inv = 0, n_folded = 0, depths = Inttab.empty,
  max_hist = (0,0,0,0), tot_hist = (0,0,0,0), grand_total = 0,
  rule_max = Symtab.empty, rule_tot = Symtab.empty, hot = []};

(*keep memory bounded: at most this many invocations retained un-summarised*)
val prune_threshold = 20000;
val prune_keep = 5000;
val hot_limit = 500;

val state =
  Synchronized.var "Simp_Count.state"
    (empty_summary, 0 (*length of pending*), [] : live list);

fun bump (a, b, c, d) n =
  if n < 10 then (a+1, b, c, d)
  else if n < 100 then (a, b+1, c, d)
  else if n < 1000 then (a, b, c+1, d)
  else (a, b, c, d+1);

fun fold_live ({no, depth = _, goal, counts} : live) (s : summary) =
  let
    val items = Symtab.dest (Synchronized.value counts);
    val tot = fold (fn (_, n) => fn a => a + n) items 0;
    val mx = fold (fn (_, n) => fn a => Int.max (a, n)) items 0;
    val rule_max' =
      fold (fn (k, n) => Symtab.map_default (k, 0) (fn m => Int.max (m, n))) items (#rule_max s);
    val rule_tot' =
      fold (fn (k, n) => Symtab.map_default (k, 0) (fn m => m + n)) items (#rule_tot s);
    val hot' =
      if mx >= 100 andalso length (#hot s) < hot_limit
      then (no, goal, tot, sort (int_ord o apply2 snd o swap) items) :: #hot s
      else #hot s;
  in
   {n_inv = #n_inv s, n_folded = #n_folded s + 1, depths = #depths s,
    max_hist = bump (#max_hist s) mx,
    tot_hist = bump (#tot_hist s) tot,
    grand_total = #grand_total s + tot,
    rule_max = rule_max', rule_tot = rule_tot', hot = hot'}
  end;

fun note_depth d (s : summary) =
 {n_inv = #n_inv s + 1, n_folded = #n_folded s,
  depths = Inttab.map_default (d, 0) (fn n => n + 1) (#depths s),
  max_hist = #max_hist s, tot_hist = #tot_hist s, grand_total = #grand_total s,
  rule_max = #rule_max s, rule_tot = #rule_tot s, hot = #hot s};

fun start_invocation depth ct =
  Synchronized.change_result state (fn (s, pn, pending) =>
    let
      val s1 = note_depth depth s;
      val cell : live =
       {no = #n_inv s1, depth = depth, goal = Thm.term_of ct,
        counts = Synchronized.var "Simp_Count.counts" Symtab.empty};
      val res =
        if pn >= prune_threshold
        then
          let val (keep, old) = chop prune_keep (cell :: pending)
          in (fold fold_live old s1, prune_keep, keep) end
        else (s1, pn + 1, cell :: pending);
    in (cell, res) end);

(* ------------------------------------------------------------------ *)
(* the hook                                                             *)

structure Current = Proof_Data (
  type T = live option;
  fun init _ = NONE);

fun trace_invoke {depth, cterm} ctxt =
  (case Current.get ctxt of
    SOME _ => ctxt   (*nested: share the enclosing record*)
  | NONE => Current.put (SOME (start_invocation depth cterm)) ctxt);

fun rule_name (rrule : Raw_Simplifier.rrule) thm =
  let val name = #name rrule : Thm_Name.T in
    if Thm_Name.is_empty name
    then
      let val hint = Thm.get_name_hint thm
      in if Thm_Name.is_empty hint then "<unnamed>" else Thm_Name.print hint end
    else Thm_Name.print name
  end;

fun trace_rrule {unconditional = _, cterm = _, thm, rrule} ctxt cont =
  (case cont ctxt of
    NONE => NONE
  | some =>
      (case Current.get ctxt of
        NONE => some
      | SOME {counts, ...} =>
          let val nm = rule_name rrule thm in
            Synchronized.change counts (Symtab.map_default (nm, 0) (fn n => n + 1));
            some
          end));

val trace_ops =
 {trace_invoke = trace_invoke,
  trace_rrule = trace_rrule,
  trace_simproc = fn _ => fn ctxt => fn cont => cont ctxt};

(* ------------------------------------------------------------------ *)
(* reporting                                                            *)

fun reset () = Synchronized.change state (fn _ => (empty_summary, 0, []));

fun snapshot () =
  Synchronized.value state |> (fn (s, _, pending) => fold fold_live pending s);

fun short_term ctxt t =
  let
    val s =
      the_default "<unprintable>"
        (try (XML.content_of o YXML.parse_body o Syntax.string_of_term ctxt) t)
      |> translate_string (fn c => if c = "\n" then " " else c);
  in
    if size s <= 200 then s else String.substring (s, 0, 200) ^ " ..."
  end;

fun show4 (a, b, c, d) =
  "<10: " ^ string_of_int a ^ "   10-99: " ^ string_of_int b ^
  "   100-999: " ^ string_of_int c ^ "   >=1000: " ^ string_of_int d;

fun report_ctxt ctxt =
  let
    val s = snapshot ();
    val lines =
      ["==== SIMP_COUNT REPORT ===================================================",
       "invocations (top-level simplifier calls): " ^ string_of_int (#n_inv s),
       "invocations summarised:                   " ^ string_of_int (#n_folded s),
       "total successful rewrites:                " ^ string_of_int (#grand_total s),
       "top-level depths observed (depth=count):  " ^
         commas (map (fn (d, n) => string_of_int d ^ "=" ^ string_of_int n)
                     (Inttab.dest (#depths s))),
       "",
       "histogram of MAX single-rule count per invocation:",
       "  " ^ show4 (#max_hist s),
       "histogram of TOTAL rewrites per invocation:",
       "  " ^ show4 (#tot_hist s),
       ""] @
      ["---- invocations where some rule reached >= 100 (" ^
         string_of_int (length (#hot s)) ^ " shown, cap " ^ string_of_int hot_limit ^ ") ----"] @
      maps (fn (no, goal, tot, items) =>
        ["#" ^ string_of_int no ^ "  total=" ^ string_of_int tot ^
           "  goal: " ^ short_term ctxt goal] @
        map (fn (k, n) =>
              "      " ^ (if n >= 1000 then "!!! " else "    ") ^
              string_of_int n ^ "  " ^ k)
            (take 5 items))
        (sort (int_ord o apply2 (fn (no, _, _, _) => no)) (#hot s)) @
      ["",
       "---- overall top 20 rules by MAX count within a single invocation ----"] @
      map (fn (k, n) => "  " ^ string_of_int n ^ "  " ^ k)
        (take 20 (sort (int_ord o apply2 snd o swap) (Symtab.dest (#rule_max s)))) @
      ["",
       "---- overall top 20 rules by TOTAL count over all invocations ----"] @
      map (fn (k, n) => "  " ^ string_of_int n ^ "  " ^ k)
        (take 20 (sort (int_ord o apply2 snd o swap) (Symtab.dest (#rule_tot s)))) @
      ["==== END SIMP_COUNT REPORT ==============================================="];
    val text = cat_lines lines;
    val _ =
      ignore (try
        (File.append
          (Path.explode "/home/qiyuan/Current/MLML/contrib/phi-system/ai-artifacts/simp_count_report.txt"))
        (text ^ "\n"));
  in writeln text end;

fun report () = report_ctxt (Context.proof_of (Context.the_generic_context ()));

end;

val report = Simp_Count.report;
\<close>

setup \<open>Simplifier.set_trace_ops Simp_Count.trace_ops\<close>

end
