theory Glue
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>Plan section 8.3-0 glue checks (after the patch): the named discharge
  error for all THREE certificate shapes; the entry check's message; the
  ares_tac head at work on a debt whose conclusion is one of its own premises.
  The command-level demonstrations below record the user-visible transcripts;
  the ML block then re-drives discharge_cmd and ASSERTS the message texts
  (val true = ... raises Bind on mismatch), as plan 8.3-0 demands.\<close>

debt_axiomatization glue1: \<open>(1::nat) + 1 = 2\<close>

text \<open>Certificate shape 1: named fact that does not resolve.
  EXPECT: discharge_debt_axiom: discharging "Glue.glue1" by conj_commute
  failed: Proof failed. ... with the goal displayed and NO exception-wrapper
  line (review fix R2).\<close>
discharge_debt_axiom glue1 : conj_commute

text \<open>Certificate shape 2: literal fact.  EXPECT the named error, naming the
  literal fact.\<close>
discharge_debt_axiom glue1 : \<open>(1::nat) + 1 = 2\<close>

text \<open>Certificate shape 3: attributes only.  It carries no name; with no
  renderable position the fallback reads "by the given certificate"
  (review fix M4).\<close>
discharge_debt_axiom glue1 : [[rule_format]]

text \<open>The asserted message texts, through the same discharge_cmd the command
  calls.  Also asserts the duplicate-name rejection (review fix m8) and the
  entry check (reachable only from ML: both real creators close their
  propositions via Logic.close_prop -- gen_axioms and resource_space_more.ML).\<close>
ML \<open>
  (*strip PIDE markup, so the assertions match the text a user actually sees*)
  val clean = XML.content_of o YXML.parse_body
  fun msg_of certs =
    (Debt_Axiom.discharge_cmd certs \<^theory>; "NO ERROR")
      handle ERROR m => clean m
  fun assert_has what needle hay =
    if String.isSubstring needle hay then ()
    else error ("ASSERTION FAILED (" ^ what ^ "): missing " ^ quote needle ^ " in:\n" ^ hay)
  fun assert_lacks what needle hay =
    if String.isSubstring needle hay
    then error ("ASSERTION FAILED (" ^ what ^ "): unexpected " ^ quote needle ^ " in:\n" ^ hay)
    else ()
  (*shape 1: named fact that does not resolve; R2: no exception wrapper*)
  val m1 = msg_of [(("glue1", Position.none), (Facts.named "conj_commute", []))]
  val _ = assert_has "shape1" "discharging \"Glue.glue1\" by conj_commute failed:" m1
  val _ = assert_has "shape1" "Proof failed." m1
  val _ = assert_has "shape1" "1 + 1 = 2" m1
  val _ = assert_lacks "shape1/R2" "exception THM" m1
  (*shape 2: literal fact*)
  val m2 = msg_of [(("glue1", Position.none), (Facts.Fact "(1::nat) + 1 = 2", []))]
  val _ = assert_has "shape2" "by literal fact \"(1::nat) + 1 = 2\" failed:" m2
  val _ = assert_has "shape2" "Failed to retrieve literal fact" m2
  (*shape 3: attributes only, no renderable position (M4)*)
  val m3 = msg_of [(("glue1", Position.none),
                    (Facts.named "", [Token.make_src ("rule_format", Position.none) []]))]
  val _ = assert_has "shape3/M4" "by the given certificate failed:" m3
  val _ = assert_has "shape3" "Proof failed." m3
  (*duplicate debt name in one command (m8; checked before any proof runs)*)
  val m5 = msg_of [(("glue1", Position.none), (Facts.named "refl", [])),
                   (("glue1", Position.none), (Facts.named "refl", []))]
  val _ = assert_has "duplicate/m8" "is named twice in one discharge" m5
  (*the entry check*)
  val m4 = ((Debt_Axiom.add_debt_axiom_global (\<^binding>\<open>bad\<close>, \<^prop>\<open>P\<close>) \<^theory>;
             "NO ERROR") handle ERROR m => clean m)
  val _ = assert_has "entry-check" "add_debt_axiom: free term variables in" m4
  val _ = writeln "Glue ML assertions PASS"
\<close>

text \<open>A debt whose conclusion is one of its own premises must still discharge
  (the assume leg of the ares_tac head; plain resolve_tac would lose it).\<close>
debt_axiomatization glue2: \<open>A \<Longrightarrow> A\<close>

discharge_debt_axiom glue2 : refl

print_debt_axiom

end
