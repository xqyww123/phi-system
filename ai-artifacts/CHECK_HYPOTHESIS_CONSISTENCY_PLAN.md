# `\<check> \<premise> \<consistency>` — deciding a guard without assuming the premises consistent

Status: rev 5 (2026-09-23) — **READY FOR STAGE 1 on the author's word;
stage P done and committed (phi-system `be16be02`); three reviews done
(§10), every condition ruled (§2, items 1-20) or applied.  No ML has been
changed.**  Still open in §9: the ML names and the record token, which
stage 1 settles with the author before typing them.  Points marked [drafter] are the drafter's and stand only
until the author rules on them.  Line numbers are those of phi-system
commit `1f3c2142` (master).

The parent plan is `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` ("the guard plan"
below); this is the "plan of its own" that its §33 rulings of 2026-09-11
deferred until after step 5 (guard plan §37 item 11).

What changed from rev 2, in one paragraph: the account of Phi_Nitpick's
`trust_assms` is corrected — the check's premises are on the strict rail
because they are antecedents of the conjecture, and what the flag still
governs is the nondefinitional axioms Nitpick generates from the conjecture
itself, which the check now puts on the strict rail too by the author's
ruling (§4.3 c, §7); `guard_kind` is declared in `Phi_Guard_Refute` and
re-exported from `Phi_Reasoners` (§4.2); `concl_is_false` takes a subgoal
and strips the prefix itself (§4.3 a); one `string_of_guard_kind` feeds the
record and the trace line (§4.7); the abbreviation's right-hand side is
written raw by ruling (§4.8); the `\<condition> P` paragraph gets a light
correction by ruling (§4.8); the probes, the checklists and the citations
are corrected where the second review found them wrong (§5, §6, §10).


## 0. Essence

A guard written `\<condition> False` asks one question: are the premises of
the current goal inconsistent?  Proving it means they are (the case cannot
occur, and what the guard guards applies); refuting it means a model of them
exists.  Today the guard machinery decides it with the shortcut it applies
to every guard — a conclusion that is `False` after the guard-side
simplification counts as a refutation — and that shortcut is only valid on
the assumption that the premises ARE consistent, which is the very thing
this guard asks.  The two refuters rest on the same assumption: R-conv
proves the negation of the conclusion, and the negation of `False` is
provable from anything; R-nitpick's premise slice keeps only the premises
connected to the conclusion's free variables, and `False` has none, so it
keeps nothing — the premise list Nitpick receives today is EMPTY and the
verdict carries no information at all.

The change: `prove_or_refute` learns which kind of guard it decides —
`Normal`, or `Check_Premise_Consistency` — and the three steps that would
refute the check unconditionally are off for it: the refutation by the
simplifier, R-conv, and the slice.  For the check, R-nitpick is given the
premises as antecedents of the very formula it must falsify, so a
countermodel is a model in which every premise is definitely true: the
question itself, asked of the standard model search.  P-auto, the judge and
the entries are assumption-free and are not touched.  A fourth place in the
code base spells the same assumption — Phi_Nitpick's `trust_assms`, the
patch that lets a formula on the unknown-tolerant rail pass when it cannot
be evaluated (phi_nitpick.ML:14-22; hard-coded `true` at
guard_refute.ML:226).  The check's premises cannot ride that rail in any
case, because they are antecedents of the conjecture; what the flag still
governs is the nondefinitional axioms Nitpick generates from the
conjecture's own constants and types, and by the author's ruling the check
passes `false`, so those ride the strict rail too (§4.3 c).  The guard gets
a readable spelling, `\<check> \<premise> \<consistency>`, as an
abbreviation of `\<condition> False`, so the eight live uses in
`Phi_BI/Phi_BI.thy` change nothing but their display.


## 1. Glossary

The guard plan's §1 is authoritative for every term it defines (guard,
entry, delta, the judge, the factory, the solving function, P-auto, R-conv,
R-nitpick, `guard_simp_tac`, `p_auto_tac`, `p_auto_attempt`, the guard
digest, the loud guard warning, the undecided-guard warning, the out-of-run
instance, the obligation instance, the goal state).  New terms:

- **the check**: a guard whose leading antecedent, under its `\<And>`/`\<Longrightarrow>`
  prefix, concludes `False` under a premise tag AS WRITTEN — `\<condition> False`,
  `\<condition>[NO_INST] False`, and the new spelling, which is the same term.
  A guard whose conclusion only BECOMES `False` later — by the template's
  rewrite or by `guard_simp_tac` — is not the check and keeps today's
  treatment.
- **the template's rewrite**: `oblg_template`'s `Simplifier.full_rewrite`
  of the premise tag's content (reasoners.ML:386-387, through
  `PLPR_Syntax.premise_tag_conv`, PLPR_Syntax.ML:39-44: the tag stays, the
  content is rewritten in the run's full simpset).  It turns
  `\<condition> (n < 0)` on a nat, or `\<condition> (Inr b = Inl a)`, into
  `\<condition> False` before any solving function sees the state.
- **the premises**: what the check is about — the subgoal's premises and
  the context's Premise-tagged assumptions, i.e. what R-nitpick's
  `premises_of` (guard_refute.ML:104-116) collects.  The code's word
  everywhere ("premises", "contextual premises", the `Premise` tag,
  `is_premise`), the guard's name, and every text of this plan use this one
  word [author 2026-09-22 "按已有的词汇来"].
- **`guard_kind`**: `datatype guard_kind = Normal | Check_Premise_Consistency`
  — which kind of guard a decision is about.  `Normal`: every ordinary
  guard, whose premises may be assumed consistent.
  `Check_Premise_Consistency`: the check.  Declared in `Phi_Guard_Refute`,
  the earliest structure that must name it (guard_refute.ML loads before
  reasoners.ML, PLPR.thy:1966 and :1970), and re-exported from
  `Phi_Reasoners` as `datatype guard_kind = datatype Phi_Guard_Refute.guard_kind`,
  the idiom Pure uses (Isar/locale.ML:104, Isar/expression.ML:50,
  proofterm.ML:2243-2244, zterm.ML:266-268, ML/ml_pretty.ML:9, :15), so
  that `Phi_Reasoners.Normal` is the spelling everywhere outside
  guard_refute.ML, as the smoke test qualifies every constructor it names.
  Passed as a value of this type, never as a bool, so that it cannot be
  confused with `can_inst` and so that each consumer names both cases.  The
  type name is the drafter's [author 2026-09-22 "名字你随意起"]; it is not
  `mode`, which in PLPR already names the Premise tag's HOL type
  (PLPR.thy:185-194, the variable `mode` in guard_refute.ML:88-98) and the
  reasoner's cut and backtrack modes.
- **`guard_kind_of`**: `thm -> guard_kind`, the function that computes the
  kind from a goal state: `Check_Premise_Consistency` iff the state has a
  premise and that premise's conclusion under its prefix
  (`Logic.strip_assums_concl`, the same reading `quick_cut` uses today at
  :976) is `False`, tagged (`Premise _ False`) or bare; `Normal` otherwise,
  and for a state with no premise.  Its `False` test is its own — it must
  ACCEPT the tagged form, which `concl_is_false` (§4.3 a) must REJECT so
  that the factory's front `quick_cut 1 th` stays a no-op before
  `Premise_def` is unfolded (§4.4) — and it is deliberately not
  `concl_is_false`.  No mode check on the tag: into `guard_condition_judge`
  only `\<condition>` guards arrive, selected by the registered patterns
  (PLPR.thy:2005-2009); the out-of-run instance has no registration and is
  called from ML at four live sites, but after this plan it reads no kind at
  all (§4.4).  "Or bare" is there for the method `\<phi>guard_P_auto`,
  which is applied to a raw Isar goal — see §6 item 6.
- **the three steps**: the three steps of one `prove_or_refute` call whose
  validity rests on the assumption that the premises are consistent, and
  which therefore refute unconditionally every check the guard-side
  simplification does not prove (§3 item 2): the refutation
  by the simplifier (a conclusion left as `False` by `guard_simp_tac`),
  R-conv, and the slice inside R-nitpick's `preprocess`.  Not "the
  consumers of the flag": the functions that read the kind are
  `prove_or_refute`, `guard_digest`, `Phi_Guard_Refute.preprocess` and
  `Phi_Guard_Refute.nitpick` (§4.1; §4.3 b says why R-conv is switched off
  from outside and R-nitpick reshaped from inside).
- **the strict rail, the unknown-tolerant rail**: Phi_Nitpick's own words
  (phi_nitpick.ML:14-22).  Nitpick evaluates a formula in a finite model as
  definitely true, definitely false, or unknown (an atom it cannot
  evaluate).  A formula on the strict rail must come out definitely true; on
  the unknown-tolerant rail it passes unless definitely false.  Nitpick
  keeps the problem's nondefinitional formulas in one list whose HEAD is the
  negated conjecture and whose TAIL is every other nondefinitional formula:
  the assumptions handed over (`nondef_assm_ts`) and the nondefinitional
  axioms Nitpick generates from the conjecture's and the assumptions' own
  constants and types (nitpick_preproc.ML:1031-1040 builds the list from
  `add_axioms_for_term 1 neg_t` and then from `nondef_assm_ts`, each
  recursing through `add_axiom` at :902, and returns `neg_t :: nondefs`).
  The patch `trust_assms` puts the whole TAIL on the unknown-tolerant rail
  and leaves the head on the problem's own flag (phi_nitpick.ML:527-533, and
  its comment at :524-526: "head keeps the problem's own flag, tail gets the
  relaxed one"; that comment's earlier clause at :520-521 names
  "typedef/class axioms" and is wrong on "typedef" — typedef axioms are
  definitional and reach `defs`, which `trust_assms` never touches, §4.3 c),
  and that flag is strict here: `unsound` is always `false` because
  `max_potential = 0` is pinned (reasoners.ML:1254; phi_nitpick.ML:860-862),
  so `unsound orelse trust_assms` collapses to `trust_assms`.  Antecedents
  of the conjecture itself are in the head and are on the strict rail
  whatever the flag says (guard_refute.ML:202-205 states this from the
  other side: "Passing them inside the goal turns the trust patch silently
  off").
- **the verdicts of the check**: Proved = the premises are inconsistent;
  Refuted = a finite model of them exists (R-nitpick's), or the judge said
  Unprovable; Unknown = undecided, and the guard fails, which is the safe
  outcome (the branch is treated as live).
- **the undecided-check warning**: the level-1 message printed over a check
  that ends Unknown, in place of the undecided-guard warning (text in §4.6,
  approved); one ML function prints both (§4.6).
- **the digest marker**: the term `False` prepended to the term list the
  guard digest hashes, for the check only (§4.5).


## 2. The rulings of 2026-09-22, verbatim

**First round** (the design).  The author opened with: "我的想法是也许我们可以在
PLPR.thy 中引入 \<check> \<hypothesis> \<consistency> \<equiv> \<condition> False 这个
abbreviation 然后在 guard condition judge 中特判，如果 the conclusion is False
那么不会启用那个 False short cut 来迫使继续进行之后的 P-auto 以及 R-conv,
R-nitpick, LLM judge 等，你觉得如何？"  The drafter answered that the
shortcut is not the only place: R-conv and R-nitpick as they stand refute
the check unconditionally (§3).

1. **One parameter, meaning an assumption.**  "我们是否应该给一个参数来控制是否发生这一行为
   （例如名叫："是否可以假设 premises 的一致性"，或者直接就叫"mode"来看是否是要检查
   premises 的一致性）然后对于 condition False 直接设置此参数为 False 这是否就够了？"
   — enough: the three steps (§1) are the ones whose validity rests on the
   assumption (the wording "exactly" softened in the second round, item 10).
2. **Computed at the entrance of `guard_condition_judge`, not in the factory.**
   "guard_condition_judge 是我们自己写的，我们不能在 guard_condition_judge 的最外部
   算出来这个值，然后作为参数传给 prove_or_refute 吗？" — yes: "好的，同意".
   (The drafter's extension of this ruling to the out-of-run instance and
   the method is withdrawn by R1, item 9.)
3. **The judge is asked for the check.**  "1. 要问的".
4. **Unknown stays at level 1, with its own text.**  "2. 建议依旧在 level 1
   然后措辞请你起草，大意是 Fail to check the consistency of the premises ...
   之类的" — the drafter's text: "批准" (§4.6; the first line is now the
   author's own words, item 12).
5. **The cost is accepted.**  Per live branch: P-auto's full 400 ms, then
   R-nitpick (default `\<phi>guard_refute_timeout` 2000 ms plus its 5 s
   margin per subgoal), then the judge on a cold miss; 400 ms warm, against
   about 1 ms today.  "接受".  The increment is still measured on the corpus
   in the verification stage, for the record, and no bound is tuned (§6).
6. **The word symbols are a preparatory stage of this plan.**
   "没错，要在 symbols-words 里按高水位分配新码点，并用 fonts/build_word_glyphs.py
   重建 PhiSymbols.ttf 建议放在这个计划里作为一个准备阶段去做".
7. **R-nitpick's two weakenings stay** (the `is_premise` filter and the
   `Preprocess_Hooks`; §7): explained, "好。没有异议".
8. **The plan lives in `ai-artifacts/`.**  "计划文件放 ai-artifacts/".

**Second round** (after the review of rev 1).

9. **R1 accepted**: "A 批准" — the refutation by the simplifier moves out
   of `guard_simp_tac` into `prove_or_refute` (§4.3 a), with the judge's
   three corrections.
10. **R-nitpick for the check: the premises as antecedents of the goal.**
    "我认为最理想的情况是，在 assume_consistent = False 时候，令 R-niptick 把 the
    premises 不要视作 contextual assumptions 而是 a part, antecedents of the goal
    你觉得如何？" — adopted (§4.3 c).  Its second half, "所以你的建议是在
    Check_Premise_Consistency 模式下不启动 trust rail 吗？我赞同", was given on
    the drafter's statement that with the premises as antecedents "there is
    nothing to trust"; that statement was wrong (the second review's F1, §10)
    and the question was re-put with the facts — item 17.  The wording "the
    three consumers are exactly the steps whose validity rests on it" is
    replaced by the glossary entry "the three steps" (§1).
11. **A datatype, not a bool.**  "那么我建议，改名 assume_consistent 为 datatype
    mode = Normal | Check_Premise_Consistency 你觉得如何？ 然后在
    Check_Premise_Consistency mode 下，禁用 R-conv" — adopted; the type name
    is the drafter's ("这是一个内部用的 datatype，所以名字你随意起"): `guard_kind`.
12. **One word: premise.**  "按已有的词汇来. 按你的建议来。" — the spelling is
    `\<check> \<premise> \<consistency>` (`\<premise>` is an existing word
    symbol; only `check` and `consistency` are new), the warning's first
    line is "Fail to check the consistency of the premises:" (the author's
    draft of ruling 4), the glossary term is "the premises".
13. **R-conv is trivial for the check** — confirmed by the author ("此外我还
    意识到 R-conv 是 trivial 的对吗？"): the negation of `False` is `True`, so
    R-conv would prove `premises \<Longrightarrow> True` at once; it is not run for the
    check (§4.3 b).

**Third round** (after the review of rev 2).

14. **The abbreviation's right-hand side is written raw**,
    `\<equiv> Premise MODE_GUARD False`: "赞同" (§4.8).
15. **`\<condition>[\<safe>] P` is deferred**: "\<condition>[\<safe>] P 是另一个问题，
    其实我有计划打算最后都换成 \<condition> P 的。不过这个我们之后再讨论吧。请记一笔"
    — recorded in §9, not this plan's.
16. **The `\<condition> P` paragraph gets a light correction**: "你可以适当稍微
    改一下" (§4.8).
17. **`trust_assms` for the check is `false`**: "建议 the check 传 false" —
    re-put by the drafter with the corrected facts (item 10; §4.3 c, §7).

**Fourth round** (after the targeted third read, 2026-09-23).

18. **The `\<condition> P` paragraph's light correction covers both
    sentences** (the third read's F7): "F7 批准" (§4.8).
19. **Stage 1 corrects two comment blocks of phi_nitpick.ML** (the third
    read's R2): "R2 好" (§4.4, §5 stage 1 item 0).
20. **The plan's text is the drafter's, within the author's design**: "计划
    文本只要不违背我的设计可以你自行书写" — under it the drafter took the third
    read's R1 (the tail recorded as a rule, not a list, §4.3 c).

Earlier rulings this plan rests on: the `is_F` shortcut is deleted [author
2026-09-15 "建议直接删除 is_F 分支"; guard plan §39]; the 2026-09-11 follow-up
proposal (a new antecedent constant defined as `False` with reasoners of
its own above the condition solver; guard plan §33) is superseded by the
abbreviation plus the kind [author 2026-09-22, the opening design above].


## 3. Diagnosis — what the check meets today

One `prove_or_refute` call on `\<condition> False` (reasoners.ML:1433):

1. The factory's own `quick_cut 1 th` (:1617) never fires on it: at that
   point the conclusion is still `Premise MODE_GUARD False`, not the bare
   `Trueprop False` that `quick_cut` (:975-978) looks for — `oblg_template`
   tags an untagged major premise (:383-385) and the template's rewrite
   keeps the tag (PLPR_Syntax.ML:39-44).  Corroborated by guard plan §33
   item 3's measurement, where the same guard reached the simplification and
   was PROVED with useful facts `x = None`, `x = Some y`.
2. Step 1½, `guard_simp_tac` (:1074-1085): asm_full_simp in the enhanced
   context, which carries `Premise_def` (:1615), unfolds the tag; if the
   premises collapse to `False` the goal closes — Proved, logged with
   refuter `-` like any P-auto proof (:1538-1542, :1577); otherwise the
   conclusion is now the bare `False` and `quick_cut` yields the empty
   sequence, which `prove_or_refute` maps to `refuted_by simp_refuter`
   (:1553-1555): Refuted, the entry written, nothing else runs.
3. Had the cut not fired, R-conv (`r_conv`, ~:1131; `conv_goal`'s
   `Trueprop` case wraps the conclusion in `Not`) would prove
   `premises \<Longrightarrow> \<not> False` at once: an unconditional refutation.
4. Had R-conv not fired, R-nitpick's `preprocess` (guard_refute.ML:176-200)
   would `slice` (:135-150, called at :198): `grow` starts from the free
   variables of the conclusion, `False` has none, `connected` is empty on
   the first call and `grow` returns `[]`; Nitpick receives `False` with an
   EMPTY assumption list, every assignment is a countermodel, the code is
   quasi-genuine (§4.3 c): an unconditional refutation that carries no
   information about the premises.
5. And had the premises reached Nitpick as assumptions, not one of them
   would be on the strict rail: those Nitpick keeps in its nondefinitional
   list ride the unknown-tolerant rail (§1; `Phi_Guard_Refute.nitpick`
   passes the literal `true` for `trust_assms`, guard_refute.ML:226), and a
   premise that exclusively defines a free variable is partitioned out of
   that list by Nitpick's own preprocessing (nitpick_preproc.ML:888-889) and
   enters the problem only when its free is met during the scan
   (:981-986) — and the check's negated conjecture is `False \<Longrightarrow> False`
   (phi_nitpick.ML:278-279), which has no free, so such a premise can be
   dropped outright.  For the check the head carries nothing either, so the
   verdict would rest on the tolerant rail and on whatever was not dropped,
   never on a model of the premises.

So the check is simp-only today, as guard plan §33 item 3 found; an
undetected contradiction leaves a dead branch unpruned — not unsound.  The
live uses are the four sum-type case-split rules of `Phi_BI/Phi_BI.thy`,
two occurrences each: `ToA_case_sum_src` (:6217), `ToA_case_sum_src_R`
(:6224), `ToA_case_sum_src_W` (:6257), `ToA_case_sum_src_WR` (:6264) —
eight in all; twelve further occurrences sit in commented-out lemmas whose
registrations are themselves commented out (:6331, :6339), among them every
`if`-branching variant, so no live `if`-branching rule uses the check.
Each live use has the shape

    \<And>a. \<condition> x = Inl a \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> P = (\<lambda>_. False) \<or>\<^sub>c\<^sub>u\<^sub>t (the real transformation)

— the check under a `\<And>`/`\<Longrightarrow>` prefix, which is why `guard_kind_of` must
look under the prefix (PLPR's live dispatch matches under it too, through
`Phi_Help.strip_meta_hhf_bvs`, reasoner.ML:849-851); the deleted `is_false`
did not, and so was false for this very shape.


## 4. Design

### 4.1 The kind

`datatype guard_kind = Normal | Check_Premise_Consistency` (§1).  Four
functions read it: `prove_or_refute` (§4.3 a, b, §4.6, §4.7),
`guard_digest` (§4.5), `Phi_Guard_Refute.preprocess` (§4.3 c: split and
slice, or hand the residue whole) and `Phi_Guard_Refute.nitpick` (§4.3 c:
its read decides the rail of Nitpick's generated nondefinitional axioms);
`r_nitpick` passes it along.  Each consumer names both cases where it
branches, so a reader sees what the check changes at the place it changes
it.

### 4.2 Where it is computed

`guard_condition_judge` receives the state before `oblg_template` — the
factory passes `th0` straight into it (:1610-1611) — so "the guard as
written" is visible there and nowhere later.  Partial application does the
rest, and the factory, its type, the two non-judge instances and the
obligation instance are untouched:

    fun guard_digest_of th0 = guard_digest (guard_kind_of th0)

    fun guard_condition_judge cfg (ctxt0, th0) =
      gen_guard_condition_solver (guard_digest_of th0)
                                 (prove_or_refute (guard_kind_of th0)) cfg (ctxt0, th0)

`guard_digest_of` is exported and is the one value both the judge instance
and the smoke test's `digest_of` helper name, so the kind enters the digest
in one place in the system (the first review's R5, its narrower form).

Why "as written" and not "is `False` when the solving function sees it":
the template's rewrite (§1) turns ordinary guards into `\<condition> False`
after instantiation — `\<condition> (Inr b = Inl a)`, `\<condition> (n < 0)`
on a nat — and those must keep the refutation by the simplifier (about
1 ms), not run P-auto's 400 ms, R-nitpick and the judge.

The out-of-run instance and the method compute no kind (§4.4): after R1
nothing on their path branches on it.

### 4.3 The three steps

(a) **The refutation by the simplifier moves into `prove_or_refute`** (R1,
ruling 9).  `guard_simp_tac` becomes the simplification alone —
`ALLGOALS (asm_full_simp_tac (enhance_for_guard ctxt))` under its 60 s
bound — and yields exactly one state: `asm_full_simp_tac` is
`PREFER_GOAL (simp_loop_tac 1)` (Pure/simplifier.ML:328), which is empty
only for an out-of-range index (Pure/goal.ML:275-277); `ALLGOALS`
(Pure/tactical.ML:236-240) fixes the goal count at entry and descends over
goals the simplification cannot remove, so the index is always in range;
within range `generic_rewrite_goal_tac` returns `Seq.single`
(Pure/raw_simplifier.ML:1518-1521 — its `else Seq.empty` is the
out-of-range branch just excluded) and `simp_loop_tac`'s continuation,
`solve_tac i ORELSE TRY (...)`, cannot fail (Pure/simplifier.ML:325-327)
— that rules out zero states; the cap is `Seq.take 1` (:1075), which yields
at most one element and an empty tail (Pure/General/seq.ML:106-109), so the
one 60 s bound over the first pull (:1076-1077) covers everything any caller
can pull.  `Seq.take 1` and the sentence that records it (:1068) stay.
The one place that could still fail is the 60 s timeout path (:1078-1082),
which today returns `SOME (th, Seq.empty)` "since an empty sequence would
read as a refutation" (:1066-1068); that reason retires and the shape stays
for the surviving one: after the hoist the function's post-condition is one
state, and the caller that would notice an empty sequence is
`p_auto_attempt` (:1097-1098), which composes with `THEN` — emptiness there
would be a failed attempt (the out-of-run instance's `error`, :1646-1650;
the method's failure), not a verdict, and inside `prove_or_refute` both
pulls are total.  The source comment keeps one concise clause and points at
this paragraph, the file's own habit.  The `quick_cut` after the
simplification (:1075) goes; `quick_cut` itself stays for its two other
callers (the factory front :1617 and `safe_obligation_solver` :1661),
rewritten over a shared predicate on a SUBGOAL [drafter]:

    fun concl_is_false subgoal =
      case Logic.strip_assums_concl subgoal
        of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>False\<close>, _) => true
         | _ => false
    fun quick_cut i th = if concl_is_false (Logic.nth_prem (i, Thm.prop_of th)) then Seq.empty else Seq.single th

— today's `quick_cut` verbatim (:975-978), with the prefix stripped inside
the predicate so that no caller can forget it (the second review's F9).
`prove_or_refute` then reads:

    (*step 1 1/2: the simplification, then -- for an ordinary guard -- the refutation by
      the simplifier: a subgoal whose conclusion the simplification left as False*)
    val th1 = case Seq.pull (guard_simp_tac ctxt_g th0) of SOME (th, _) => th | NONE => th0
    val refuted_by_simp =
          case kind of Normal => exists concl_is_false (Thm.prems_of th1)
                     | Check_Premise_Consistency => false
    val goals = Thm.cprems_of (if refuted_by_simp then th0 else th1)
    val outcome = if refuted_by_simp then refuted_by simp_refuter else decide th1

The `case` on `Seq.pull` stays total (the first review's R1, third
correction); its `NONE` arm is unreachable and says so in a comment.  The
judge path (:1511-1516) changes the same way: its `case Seq.pull` becomes
total, and after the re-simplification of `th0` with the judge's delta,
`exists concl_is_false (Thm.prems_of th')` is the "judge is broken" error
under `Normal` and the NORMAL state of a check under
`Check_Premise_Consistency` (the judge answering Provable and the
re-simplification leaving `premises \<Longrightarrow> False` is exactly what the check
looks like before P-auto proves it).  `goals` keeps today's two branches
(:1479) — the state `prove_or_refute` was given, UNSIMPLIFIED, when the
simplifier refuted, and the simplified state otherwise — so the two
warnings, the record's `subgoals` field and the trace line are unchanged.
The record's refuter name `guard_simp_tac`
(`simp_refuter`, :1389) still names what happened: the simplification left
the conclusion `False`.

Consequences: `guard_simp_tac` keeps today's signature (:118) and is called
from the same three places (:1098, :1478, :1514) — only its body loses the
cut and its comments are rewritten (§5 stage 1 item 2); `p_auto_attempt`,
`p_auto_solving`, `guard_condition_solver'`, the method `\<phi>guard_P_auto`
and `PLPR.thy`'s ML keep today's code; the one place in the pipeline where a
verdict was the
ABSENCE of a result is gone, and the shortcut sits on the same line as the
kind that authorises it; and the author's ruling that `guard_simp_tac` is
standard simp whose output P-auto, R-conv, R-nitpick and the judge share
(guard plan §39 rulings 1-2) becomes true without exception.  What the
out-of-run instance and the method give up is in §7.

(b) **R-conv is not run for the check** (rulings 11, 13):
`case kind of Normal => r_conv can_inst ctxt_g ctxt0 goals | Check_Premise_Consistency => false`
at :1548.  There is no check-variant of R-conv to write: its whole method
is proving the negation of the conclusion, which inconsistent premises
prove too, and for the check that negation is `True`.  R-conv is switched
off from outside, at its call site, because it has nothing to do; R-nitpick
is reshaped from inside, because its assumption-free form is the question.

(c) **R-nitpick receives the premises as antecedents of its conjecture**
(ruling 10), on the strict rail throughout (ruling 17).
`Phi_Guard_Refute.preprocess kind ctxt assms goal` collects, weakens and
simplifies exactly as today (:177-192); then, on the residue:

    case kind of
      Normal => the residue split back into (premises, conclusion) and sliced (:196-199, as today)
    | Check_Premise_Consistency => ([], residue)

— no split, so no `split_conjunctions` (:122-133) and no `slice`
(:135-150) run for the check; `slice` itself is unchanged.
`Phi_Guard_Refute.nitpick kind ...` then calls
`Phi_Nitpick.pick_nits_in_term ... (kind = Normal) ... [] prems concl` — the
conjecture for the check is the whole residue `P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> False`,
which Nitpick negates to `P\<^sub>1 \<and> \<dots> \<and> P\<^sub>n`: the HEAD of its nondefinitional
list, on the strict rail whatever `trust_assms` says (§1), so a countermodel
is an assignment under which every premise is DEFINITELY true — a finite
model of the premises, the question the check asks, put to the standard
search.  Nothing is sliced.

What `trust_assms` still governs, and the value the check passes.  The
flag relaxes the TAIL of the list (§1), and the tail is decided by a RULE,
not a list (the third read's R1, under ruling 20): it is exactly what
Nitpick's `add_nondef_axiom` puts there — the assumptions handed over, and
the nondefinitional axioms Nitpick generates from the constants and types
of the conjecture and of the assumptions (nitpick_preproc.ML:1031-1040, the
recursion through `add_axiom` at :902), where "nondefinitional" is decided
by two routers and nothing else: `add_maybe_def_axiom` (:907-909; an axiom
is nondefinitional iff its head is `Pure.imp`) and `add_eq_axiom`
(:910-912; an equation is definitional iff `is_constr_pattern_formula`
holds).  Exhaustive by construction: the accumulator's `nondefs` component
(:891) is written only by `add_nondef_axiom` (:905-906), the two routers
are the only conditional writers, after the folds only `defs` is appended
to (:1037), and the function returns `neg_t :: nondefs` (:1040).
Examples, marked as examples: the monomorphic class axioms of a type
variable's sort (`add_axioms_for_sort`, :1026); an equational axiom of a
function whose left-hand side is not a constructor pattern.  Not in the
tail: typedef axioms, which are `Trueprop`-headed and definitional
(`optimized_typedef_axioms`, nitpick_hol.ML:1974-1996).  The theory's OWN
nondefinitional axioms enter only through `nondef_props_for_const`
lookups: the one on an ordinary constant (:976-978) is off under the
pinned `user_axioms = false`, the two on a typedef's `Abs_`/`Rep_`
constant (:949-951, :957-959) are ungated — no phi-system axiom is known
to mention one, and one more tail formula only costs an Unknown.  For the
check the assumption list is empty, so the tail is the generated axioms
alone.  By
the author's ruling the check passes `false` — `trust_assms = (kind = Normal)`
— so those generated axioms ride the strict rail for the check, and its
problem is STRICTER than an ordinary guard's in that one respect.  The
direction of the difference is one-way: R-nitpick reports Refuted or stands
down (guard_refute.ML:16-18, :228-229), so it can only turn a Refuted into
an Unknown, never produce a wrong Proved; and it is NOT probed — no smoke
construct rests on an unevaluable atom, and no corpus measurement can
separate its effect from `card 1-6`, the hooks or the preprocessing (§7).
The label is not the reason for the value: `user_axioms = false`
(reasoners.ML:1256) fixes `genuine_means_genuine` false whatever the flag
says (phi_nitpick.ML:665-668 with :328-329 and
nitpick_preproc.ML:1038-1039), so a check's Refuted is `quasi_genuine` as
every R-nitpick refutation is (the verdict map, reasoners.ML:1266-1286;
guard_refute.ML:207-208), and the caller reads neither label
(guard_refute.ML:225, :228-229).  Stage 1 records in guard_refute.ML what
the flag moves (§5 stage 1 item 1).

What keeping every premise buys is CONTENT, not certification.  With the
slice on, the assumption list is empty and every assignment refutes (§3
item 4); with the premises as antecedents, the search must exhibit an
assignment under which each of them is definitely true, and a premise
Kodkod can evaluate and no assignment satisfies blocks every model.  The
model is still not a certificate of consistency: `is_premise` and the hooks
weaken the premise set before it is simplified (§7); `card 1-6` makes the
model finite, so it says nothing about the infinite types the premises
quantify over; and `user_axioms = false` keeps phi-system's own axioms out
of the problem (reasoners.ML:1231-1237), so nothing is certified genuine.
A wrong Refuted costs completeness only: the branch stays live.  For the
record: the check's conclusion carries no schematic variable, so the
template's fix level 1 (vars of the premises minus vars of the conclusion,
:403) fixes every variable of the premises before any solving function
runs, and `can_inst` has no effect on a check.

The comment above `nitpick` about the assumption parameter (:202-205) is
REWRITTEN to state both cases — its rationale survives, its unqualified
first sentence and its closing warning do not: the premises go in as
assumptions under `Normal`, where `trust_assms = true` is the deliberate
choice, and as
antecedents under `Check_Premise_Consistency`, where the strict rail is the
question; the flag then governs only Nitpick's generated axioms, and the
check passes `false`.  `preprocess`'s `NONE` (its own simplification closed
the goal: Provable) is unchanged and, as today, only means "not refuted" to
the caller.

### 4.4 What does not change

`guard_simp_tac`'s callers and signature, `p_auto_tac`, `p_auto_attempt`,
`p_auto_solving`, the out-of-run instance `guard_condition_solver'` and its
four live callers (`local_value.ML:169`, `toplevel0.ML:387`,
`generic_variable_access2.ML:182`, `:272`; `application.ML:137` is inside
the comment `:112-141`), the method `\<phi>guard_P_auto`, and every line of
ML in `PLPR.thy`.  P-auto: it only proves, and proving
`premises \<Longrightarrow> False` IS finding the inconsistency.  The judge: asked as for
any guard (ruling 3) — on a cold miss after R-nitpick finds nothing, and on
an Unknown entry; its argument `judge_arg` does not carry the kind; its
Provable answer is replayed, the guard re-simplified from the raw state and
proved by P-auto exactly as today.  Entries, deltas, the store, the lemma
budget.  The loud guard warning (a Proved check overturned by the judge's
Unprovable is a real flip, and warns as today; its "by the simplifier" case
cannot fire on a check).  `solve_obligation_now` (PLPR.thy:1983-1990): its
solving function never sees the kind.  `safe_obligation_solver` (:1652):
does not go through the factory, proves or fails, no refutation.  The
factory `gen_guard_condition_solver`: untouched, including its front
`quick_cut 1 th` (:1617), which cannot fire on a tagged conclusion and is
not to be wired to the kind.  Every ordinary guard's digest (§4.5), so every
existing entry keeps hitting.  `slice`, `split_conjunctions`,
`premises_of`, the hooks, and every line of code in phi_nitpick.ML — two
of its COMMENT blocks are corrected (ruling 19, §5 stage 1 item 1).

### 4.5 The digest of a check [drafter]

`guard_digest kind ctxt th` prepends the digest marker (`\<^prop>\<open>False\<close>`) to
the hashed term list for the check only:

    Hasher.terms ((case kind of Normal => [] | Check_Premise_Consistency => [\<^prop>\<open>False\<close>]) @
                  Thm.prop_of th :: map Thm.prop_of (Assumption.all_prems_of ctxt))

(inside `Phi_Reasoners`, where the re-exported constructors are in scope
unqualified).  Ordinary digests are byte-for-byte what they are today.
Why: without the marker a check and an ordinary guard that the template's
rewrite turned into `\<condition> False` in the same goal state would share
one entry; the ordinary path's refutation by the simplifier would then
overwrite a Proved entry with Refuted and fire the loud guard warning
falsely (the false alarm of guard plan §33 item 4, in a new place), and the
check would honour a Refuted that the shortcut wrote.  The digest is
computed AFTER the template's rewrite, so the marker is load-bearing, not a
precaution; it makes the collision impossible by construction at the cost
of one term in one list.

### 4.6 The undecided-check warning (text approved; first line per ruling 12)

Printed by `prove_or_refute` in place of the undecided-guard warning when
the kind is `Check_Premise_Consistency` and the verdict is Unknown; the same
gate (`Phi_Reasoner.warn_pretty (Context.Proof ctxt) 1`, which
`\<phi>trace_reasoning` controls, reasoner.ML:316, :337-340), one message
per goal, the goal printed as the undecided-guard warning prints it:

    Fail to check the consistency of the premises:
    <goal>
    We assume they are consistent. If they are not, the reasoning continues
    in a case that cannot occur, and may fail there.

The last sentence states the consequence rather than a safety guarantee: on
the `Phi_BI` rules an undetected contradiction sends the reasoning into an
impossible case, whose transformation may not be derivable automatically.

ONE function prints both messages: `undecided_guard_warning` (:1371-1378)
takes the kind and selects its two text lines from it, the way
`loud_guard_warning ctxt who goals` (:1382-1386) selects `who` at its two
call sites (:1565, :1567).  The gate, the per-goal loop and
`Goal_Display.pretty_a_goal` then exist once, and "the same gate, the same
rendering" is structural rather than a promise (the first review's F13;
guard plan §28 records that a duplicated undecided-guard warning was
removed once before).  The glossary term "the undecided-check warning"
names the message, not an ML identifier.

### 4.7 The record and the trace line [drafter]

One `string_of_guard_kind`, beside `string_of_verdict` (:1365-1367), renders
the kind for both the `guard_decision` record (:1358-1364; the body copy of
its attribute list is :1355-1357) and the trace line (:1581-1587): the
record gets one more attribute, `kind`, carrying the token for both kinds,
so that the check's decisions can be counted and timed on a corpus run
(§6); the trace line prints nothing for `Normal` and ", " followed by the
token for the check.  The existing readers (`ai-artifacts/step5/analyze.py`,
the smoke test's `path_of`) select the attributes they know and are
unaffected.  The token is the constructor's own spelling, `Normal` /
`Check_Premise_Consistency` [drafter; §9 — the record already holds a
lowercased rendering, `proved`, and a capitalized one, `Provable`, so the
casing is the author's].

### 4.8 The spelling

In `PLPR.thy`, right after `Simp_Premise` (:204-205):

    abbreviation Check_Premise_Consistency ("\<check> \<premise> \<consistency>")
      where "\<check> \<premise> \<consistency> \<equiv> Premise MODE_GUARD False"

An abbreviation, so the term IS `Premise MODE_GUARD False`: the registered
reasoner for `\<condition> ?P` (:2005-2006) matches it unchanged, no new
reasoner, no term inspection beyond `guard_kind_of`, and `Phi_BI.thy`'s
eight live `\<condition> False` need no edit.  The constant name echoes the
three words of the spelling, as `Normal_Premise`/`\<premise>` and
`Proof_Obligation`/`\<obligation>` echo theirs; it is also the ML
constructor's name — one name for one concept, in two namespaces that never
meet in one expression [drafter; §9].

The right-hand side is written RAW, `Premise MODE_GUARD False` (ruling 14),
the block's own idiom (:203, :205, :207 write `Premise default`,
`Premise MODE_GUARD`, `Premise MODE_COLLECT`); the author's opening design
wrote `\<condition> False`, which denotes the identical term and differs
only in the key under which the abbreviation is reverted for printing.
Why: `abbreviation` certifies its right-hand side with `normalize = false`
(proof_context.ML:701-703, consts.ML:196-200), and `Consts.abbreviate`
registers the reverting rule on that UNEXPANDED term (consts.ML:320-343);
written `\<condition> False`, the key would be `Simp_Premise False`, which
matches `Premise MODE_GUARD False` neither at the top (pattern.ML:349-352:
different constant names) nor by type (pattern.ML:374-377).  Printing would
still come out right — `contract_abbrevs` (proof_context.ML:728-743)
rewrites with `Pattern.rewrite_term_yoyo` (more_pattern.ML:119-130): the
node, then the subterms, then the node again, so `Premise MODE_GUARD` would
first fold to `Simp_Premise` and then the whole term to the new spelling —
but by two steps nobody documented.  With the raw right-hand side the key
is the whole term and the first attempt at the node matches.  This is
inferred from the source and MUST be measured in stage 1 (§6 item 1).

Two `\<^descr>` paragraphs in the text block that documents `\<condition> P`
(:210-226) — user-visible text:

- The existing paragraph for `\<condition> P` (:213-217) says the assertion
  "is attempted with a weak but safe solver (usually @{method clarsimp})",
  which is `\<condition>[\<safe>] P`'s behaviour (registered to
  `safe_obligation_solver`, :2011-2012, whose `clarsimp_tac` is
  reasoners.ML:1657-1659) and has not been `\<condition> P`'s since the
  guard machinery replaced it; a new paragraph beside it would contradict
  it.  By ruling 16 the correction is light, and it covers the paragraph's
  two sentences (:214-217; only :213 stays verbatim), because the second
  sentence, "Therefore, any rule protected by it is appliable only when the
  condition \<open>P\<close> is provable using the safe solver", repeats the claim and
  would refer to a solver the block no longer introduces (the third read's
  F7, §10).  The first sentence becomes "The assertion \<open>P\<close> is decided by the
  guard machinery under its own bounds (library/reasoners.ML,
  prove_or_refute), so that an unprovable assertion cannot loop the
  reasoning"; the second becomes "Therefore, any rule protected by it is
  applicable only when \<open>P\<close> is decided provable." (three words deleted, the
  adjective corrected); `\<condition>[\<safe>] P` is not mentioned (ruling 15
  defers it).  Both sentences approved (ruling 18).
- The new paragraph: "\<^prop>\<open>\<check> \<premise> \<consistency>\<close> is the guard
  \<open>\<condition> False\<close> under its own name: it holds exactly when the premises are
  inconsistent, so what it guards applies only in a case that cannot occur.
  Unlike every other guard, the three steps that presuppose consistent
  premises are off for it: the simplifier's refutation by a \<open>False\<close>
  conclusion, R-conv, and R-nitpick's premise slice — R-nitpick is instead
  asked for a model of the premises themselves (library/reasoners.ML,
  \<open>guard_kind\<close>)."  [drafter's wording; §9]

### 4.9 The two word symbols (stage P)

`\<check>` and `\<consistency>` are new word symbols of the `PhiSymbols`
font; `\<premise>` exists (`symbols-words`: code `0x00E04C`).
`symbols-words` is generated ("do not edit"; its line 2 carries the
high-water mark, `0x00E086`); the source is `fonts/words.txt` (one word per
line; all lower-case gives the mathematical-bold alphabet), and
`fonts/build_word_glyphs.py` assigns each new word the next code point
after the highest ever assigned (decision 15 of
`jedit/WORD_CLIPBOARD_PLANS.md`: a retired code point is never reused) —
`0x00E087` and `0x00E088`, in `words.txt` order — rewrites
`fonts/PhiSymbols.ttf`, `symbols-words` and `jedit/word-clipboard-text`
together, and `--check` verifies those three files, and only those three,
against the inputs; the count and the range stated in the component's
prose are hand-maintained (§5 stage P).  No clash: the standard table has
`\<checkmark>` only.  Procedure: `fonts/WORD_GLYPHS.md` "Adding or changing
a word".  The generator names `Isabelle2025-2` and asserts the versions of
the faces it merges (STIX version-asserted, build_word_glyphs.py:79); its
one unpinned input is the local `fontTools`.  A nullary mixfix of three
space-separated symbols has a precedent in `PhSm_Ag_Base.thy:551`.


## 5. Stages

**Stage P — the symbols.**

1. First, on the UNTOUCHED tree: `python3 fonts/build_word_glyphs.py --check`
   (it writes nothing: every write is under `if not args.check`,
   :861-871).  A pass makes the whole later diff of `PhiSymbols.ttf`
   attributable to the two words.  A failure naming all three generated
   files means the committed files are stale; a failure naming
   `fonts/PhiSymbols.ttf` alone means the local `fontTools` differs from the
   one that built it (the failure text, :688-695) — then STOP and ask,
   because regenerating would rewrite the whole font inside a commit that
   adds two words.
2. Append `check` and `consistency` to `fonts/words.txt`; run the
   generator; run it with `--check`; run `jedit/run_word_clipboard_test.sh`.
   What is observed here: the generator's per-word ink check (:621-623,
   run in both modes, :874) and the clipboard test's rasterisation carry
   the "do the glyphs draw" question; the new code points are `0x00E087`
   and `0x00E088` and the high-water line moved.  How the two look in a
   text area is the author's check in his own jEdit after restarting it;
   a headless Isabelle-MCP server has no text area.
3. Hand-update the five sites that state the number of word symbols (135
   → 137) and, where they do, the code-point range (`U+E000..U+E086` →
   `U+E000..U+E088`): `fonts/WORD_GLYPHS.md:256`,
   `fonts/phi-font-readme.txt:84`, `jedit/WORD_CLIPBOARD_PLANS.md:20-21`,
   `jedit/DRAG_AND_DROP_PLAN.md:221-222` and `:457`.  NOT
   `jedit/UI_FONT_PLAN.md:330-331`, which records an earlier stale value
   as history.
4. Commit: `fonts/words.txt`, the three generated files, the five prose
   files (phi-system master, root bump; nothing pushed).

Stage P touches no ML and depends on no ruling; it may start as soon as the
author allows.

**Stage 1 — the code.**  First, restart the Isabelle-MCP session: a running
Isabelle read `symbols-words` at startup and `PLPR.thy` is about to use the
two symbols.  Then, in this order, each file's edits complete before the
next (the tree does not compile between items 1 and 2 — `reasoners.ML:1320`
is the one caller of `Phi_Guard_Refute.nitpick` — and that is expected;
re-evaluating after item 1 still typechecks the edited file against its
own signature):

0. `Phi_Logic_Programming_Reasoner/library/phi_nitpick.ML`, COMMENTS ONLY
   (ruling 19): the patch header (:14-22) says the patch puts "the premises
   of the guard" on the unknown-tolerant rail and that "Premises reach this
   file as nondef_assm_ts" — an under-claim: it relaxes the whole TAIL of
   the nondefinitional list, every nondefinitional formula but the negated
   conjecture, built from the conjecture's own generated axioms as well as
   from `nondef_assm_ts`; one clause says that antecedents of the
   conjecture are in the head and are never relaxed, and one that a
   premise which exclusively defines a free is moved to the definitional
   list by Nitpick's own preprocessing (nitpick_preproc.ML:888-889).  The
   PHI-PATCH comment (:519-526) names "typedef/class axioms": typedef
   axioms are definitional and unaffected; say "class axioms and the other
   nondefinitional axioms Nitpick generates" (§4.3 c's rule).  Constraints:
   no distribution line changes; the `fun_box` paragraph (:24-28) is not
   touched; phi-system's pinned parameter values stay out of the header
   (they belong at reasoners.ML:1254-1256 and guard_refute.ML:207-208).
   Both blocks are phi-system's own text (the distribution's nitpick.ML
   header is :1-6), so a diff-and-reapply rebase never meets them.
1. `Phi_Logic_Programming_Reasoner/library/guard_refute.ML`: the datatype
   `guard_kind` in the signature and the structure (the signature already
   carries a `datatype` spec, :19); `preprocess` and `nitpick` take the
   kind first; the residue is split and sliced under `Normal`, handed whole
   under `Check_Premise_Consistency` (§4.3 c); `trust_assms` =
   `(kind = Normal)`; the comments — the pipeline comment (:168-174), the
   assumption-parameter comment above `nitpick` (:202-205, rewritten as
   §4.3 c says: the two ways the premises go in, and what the flag then
   governs; its closing sentence "Passing them inside the goal turns the
   trust patch silently off" is a warning addressed to `Normal`'s path and
   is either scoped to it or dropped, since the check passes them inside the
   goal on purpose), and what
   keeping every premise buys (§4.3 c — content, not certification; NOT a
   claim that the model satisfies the premises, and NOT a claim that the
   patch has nothing to act on) — each concise, pointing at this plan.
2. `Phi_Logic_Programming_Reasoner/library/reasoners.ML`:
   `datatype guard_kind = datatype Phi_Guard_Refute.guard_kind` in the
   signature and the structure; `guard_kind_of`, `guard_digest_of`,
   `concl_is_false` (on a subgoal), `string_of_guard_kind` (exported where
   §6 needs them: `guard_kind_of`, `guard_digest_of`, `guard_digest`,
   `string_of_guard_kind`); `quick_cut` over `concl_is_false`;
   `guard_simp_tac` without the cut and with its comment rewritten (§4.3 a:
   one state — the cap `Seq.take 1` and the bound it carries; the timeout
   path's surviving reason); `prove_or_refute kind ...`
   with the refutation by the simplifier (§4.3 a), the judge-path test,
   R-conv under `Normal` (§4.3 b), `r_nitpick kind`, the warning selected
   by the kind (§4.6), the record attribute and the trace suffix (§4.7);
   `guard_digest kind`; `guard_condition_judge` (§4.2); the comments: the
   signature block (`gen_guard_condition_solver`'s "UNSIMPLIFIED" sentence
   :88, `guard_digest` :98-102, `prove_or_refute` :103, `guard_simp_tac`
   :112-117, `p_auto_attempt` :122-123, the record's attribute list
   :193-196), the body copy of the record's attribute list (:1355-1357),
   R-nitpick's doc comment — the one sentence at :1169-1172 that gains the
   check's case (:1181-1184 and :1187-1190 stay true: the call still
   assembles the full assumption set and threads `subst`) — and the two
   body comments that spell `prove_or_refute`'s argument list (:1430-1432)
   and the factory's "of prove_or_refute's type" (:1596-1600 — the
   factory's CODE stays untouched, §4.4).
3. `Phi_Logic_Programming_Reasoner/PLPR.thy`: the abbreviation and the two
   `\<^descr>` paragraphs (§4.8).  No ML changes.
4. `Phi_Logic_Programming_Reasoner/Test/Guard_Decision_Smoke.thy`: the
   probes of §6, a new section "The check" after "The judge"; the header's
   summary line names the check, and its reachability constraint (:14-20)
   gains a second exception — the check's probes are decided by
   `guard_simp_tac` or by P-auto on a `False` conclusion, and the
   regression probe is an equation guard on purpose; the helper `digest_of`
   (:74-79) passes `Phi_Reasoners.guard_digest_of st` (§4.2); the comment
   on the judge's third error (:685-686), whose "which quick_cut drops"
   becomes the judge path's own test (the probe's expectation is
   unchanged).
5. `ai-artifacts/Guard_False_Probe.thy`: retired — deleted, its question
   (does a contradiction that needs classical search get proved?) now
   answered by the probes [drafter; §9].

Re-evaluate under Isabelle-MCP session `Phi_System_Base` after every `.ML`
edit; no `isabelle build`.

**Stage 2 — verification (§6).**

**Stage 3 — review, documents, commit.**  The standard adversarial review
(Opus agents, English: interrogators, one defender per finding, a judge;
the report to the author in Chinese), its conditions applied and
re-verified; then the documents: the guard plan's §1 entries
(`guard_simp_tac` — which carries the retired reason for the timeout path,
"Not `timed_tac` …", and gets §4.3 a's replacement —
`gen_guard_condition_solver`, guard digest, R-conv and R-nitpick, the
undecided-guard warning, the loud guard warning), its §5 steps 1½, 3 and
4, its §33 item 3 (the idiom is no longer simp-only), its §39 (ruling 10's
mechanism "`quick_cut` leaves no state", the step-1½ and judge-path shapes,
and its "Stated consequences" line), its status line; the resume handoff in
`ai-artifacts/` (`GUARD_CACHE_RESUME_HANDOFF_2026-09-11.md`, a dated
addendum, which also records ruling 15's deferred item).  Commit on
phi-system master with the root submodule bump; nothing pushed.


## 6. Verification

All under Isabelle-MCP, session `Phi_System_Base`, theories loaded from
source.

1. `PLPR.thy` clean.  The display measured: `term \<open>\<condition> False\<close>` and
   `thm ToA_case_sum_src` (after `Phi_BI.thy`) print the new spelling.
2. `Guard_Decision_Smoke.thy` clean twice in a row.  The second run runs
   against the store the first run's entries were written into and against
   the same `guard_decision` log, and must be unaffected by both, because
   the `fresh` numerals (:220-221) give every probe a digest no earlier run
   used — so no probe meets an earlier run's entry, and no probe's digest
   filter sees an earlier run's record.  A check probe's conclusion is the
   literal `False` and cannot carry the numeral, so the numeral goes into a
   premise (the method probes of item 6 carry none: the method computes no
   digest and writes no record).  The probes (each asserts on the record's
   projection (verdict, hit, refuter, judge), on the store and, where named,
   on the warning lines, exactly as the existing probes do):
   - **simp finds the contradiction**: `Suc <fresh> = 0 \<Longrightarrow> \<condition> False`
     → ("proved", "none", "-", "-"), no entry written (a Proved first
     decision writes none, :1540-1541).
   - **P-auto finds it**: `FALLS (<fresh> # <elim_chain>) \<Longrightarrow> \<condition> False`
     (the list shape :360 already uses; `FALLS` has no simp rule and
     `FALLS_cons` ignores the head, :271-274) → ("proved", "none", "-", "-"),
     no entry.
   - **consistent premises, R-nitpick's model**:
     `CHAIN [<fresh>] \<Longrightarrow> \<condition> False` → ("refuted", "none", "R-nitpick", "-"),
     "Refuted with 0 lemma(s)".  This is the probe that reads
     "guard_simp_tac" if the refutation by the simplifier still fires on a
     check and "R-conv" if R-conv is not skipped.
   - **the same with `\<condition>[NO_INST] False`**: the check is not
     mode-specific → the same path.
   - **undecided**: `BADN <fresh> \<Longrightarrow> \<condition> False` (no rule for P-auto,
     no model for Nitpick) → ("unknown", "none", "-", "-"), "Unknown with
     0 lemma(s)", the undecided-check warning once, the undecided-guard
     warning and both loud lines zero.  This is the probe of §4.3 c's
     shape: with the premise still sliced away it would read ("refuted",
     "none", "R-nitpick", "-").  The rail (§4.3 c, `trust_assms`) is not
     probed (§7).
   - **the judge overturns a Proved entry**: the undecided shape with
     `with_entry_and_judge [] Proved (K Unprovable)` → ("refuted", "proved",
     "-", "Unprovable"), "Refuted with 0 lemma(s)", the loud guard warning
     naming the LLM judge once.
   - **the regression probe**: `CHAIN [<fresh>] \<Longrightarrow> \<condition> (Suc <fresh> = 0)`
     — an ordinary guard the template's rewrite turns into
     `\<condition> False`, under a prefix so that step 1½'s test runs under
     one — keeps the refutation by the simplifier: ("refuted", "none",
     "guard_simp_tac", "-"), "Refuted with 0 lemma(s)", no warning line.
   - **the digest marker**: on one state,
     `Phi_Reasoners.guard_digest Phi_Reasoners.Normal` and
     `Phi_Reasoners.guard_digest Phi_Reasoners.Check_Premise_Consistency`
     differ (an `ML` assertion).
   The existing probes keep their expectations: "the simplifier refuting a
   Proved entry" (`\<condition> (BADN n)`, kind `Normal`) now runs through
   the refutation by the simplifier inside `prove_or_refute` (§4.3 a), and
   "the judge answers Provable with a lemma that rewrites the guard to
   False" through the judge path's own test.
3. `Phi_BI/Phi_BI.thy` clean (the eight live uses load through the new
   display; nothing else in it changes).
4. The corpus, for flips and for the cost: `Phi_Test.PhiTest_Arithmetic`
   with its imports and the eight `Phi_Examples` theories (guard plan §38's
   corpus), under a TEMPORARY `declare [[ML_debugger]]` in `PLPR.thy`,
   reverted afterwards; `ai-artifacts/step5/analyze.py` reads the records,
   the `kind` attribute counted with `grep`.  Floors: every ordinary
   guard's digest and verdict as before (0 flips against the committed
   stores, and against the `V_on_dbg` leg of 2026-09-21 for the decisions
   the stores do not cover — a Proved first decision writes no entry); the
   check's records (`kind` = the check's token) counted with their verdict
   split (proved / refuted / unknown) and `elapsed_ms`, and the total
   increment reported — accepted in advance (ruling 5), reported for the
   record, no bound tuned.  How many checks to expect is not known in
   advance and is itself part of what this leg reports: the latest recorded
   leg of this corpus (`ai-artifacts/step5/ANALYSIS_2026-09-14.txt`, the
   `V_on_dbg` block, 377 decisions: proved 206, refuted 166, unknown 5)
   logs 20 decisions with `refuter = guard_simp_tac`, which bounds the
   checks that leg REFUTES by the simplifier; a check the simplification
   proves is logged `proved` with refuter `-` and sits among the 206, where
   no refuter histogram can see it (§3 item 2).  `Phi_System`'s `case_sum`
   users (`Spec_Framework.thy`, `Phi_Types.thy`, `Phi_Type.thy`) are inside
   the import closure, so the sum rules may fire there; the `kind`
   attribute separates checks from ordinary guards the template's rewrite
   turned into `\<condition> False`.  If the corpus exercises no check, that
   is the finding, and the smoke probes are the check's only exercise.
5. The out-of-run instance: one of its four callers is exercised by the
   corpus (`toplevel0.ML:387` runs on every procedure application) — clean
   runs are the evidence; no separate probe.
6. The method `\<phi>guard_P_auto` has no caller anywhere, so it gets a
   two-line probe of its own, with a BARE `False` conclusion — the method's
   context carries no `Premise_def` (`Premise_def` is added to the
   factory's `guard_ctxt` at :1615 and declared into `\<phi>guard_refute_simp`
   at PLPR.thy:1967, not into `\<phi>guard_simp`), so a tagged conclusion is
   never unfolded there: `lemma "FALLS <elim_chain> \<Longrightarrow> False" by \<phi>guard_P_auto`
   must now succeed (today the cut inside `guard_simp_tac` fails it), and a
   negative control (`CHAIN [1] \<Longrightarrow> False`, written with Eisbach's `fails`,
   the theory's idiom) must still fail.


## 7. Accepted imprecisions and recorded differences — so that they are not re-raised

- **R-nitpick's two weakenings stay** (ruling 7): the `is_premise` filter
  (guard_refute.ML:88-98: only Premise-tagged context assumptions travel;
  `\<obligation>`-tagged ones are goals, untagged ones are dropped) and the
  `Preprocess_Hooks` (the sole registered hook is `Phi_BI`'s scrub,
  `guard_refute_scrub.ML:161-165`, which replaces `Satisfiable (x : T)` by
  `True` and deletes the premises that became `True`; without such hooks
  Nitpick cannot read φ-System's terms).  For the check a model of the
  weakened premises can be reported as consistency while the original
  premises are inconsistent: a dead branch not pruned, the same class of
  loss as today's simp-only idiom; nothing false is derived.  The tolerant
  rail (§1) is NOT among the check's weakenings: the check's premises are
  in the head of Nitpick's list, and by ruling 17 its problem's tail is
  strict too.
- **The check's Nitpick problem is stricter than an ordinary guard's**
  (ruling 17, `trust_assms = false` for the check) — a difference, not a
  weakening: Nitpick's generated nondefinitional axioms (§4.3 c) must come
  out definitely true in a check's countermodel, where an ordinary guard's
  may stay unknown.  Its direction is one-way — it can only turn a Refuted
  into an Unknown (then the judge, or the undecided-check warning), never
  into a wrong Proved — and it is NOT probed: no smoke construct rests on
  an unevaluable atom, and neither §6 item 4's verdict split nor any other
  measurement in this plan can attribute an Unknown to this rail rather
  than to `card 1-6`, the hooks or the preprocessing.
- **A finite model is not a certificate** (§4.3 c): `card 1-6` makes it
  finite; `user_axioms = false` keeps phi-system's own axioms out, so
  nothing is certified genuine and a check's Refuted is `quasi_genuine`,
  as every R-nitpick refutation is (the verdict map, reasoners.ML:1266-1286).
- **The cost** (ruling 5), §2 item 5.
- **The judge on every cold check** (ruling 3): one consultation per digest
  on a cold miss, then the entry; an Unknown entry consults it again on
  every run, as for any guard.
- **The out-of-run instance and the method lose the refutation by the
  simplifier for every guard** (R1, ruling 9): on an ordinary guard the
  template's rewrite turned into `\<condition> False`, `p_auto_attempt` now
  runs P-auto for up to `\<phi>guard_classic_prover_timeout` (400 ms) before
  failing, where `guard_simp_tac`'s cut failed it at once.  All four live
  callers of the out-of-run instance fail through `error`
  (`guard_condition_solver1`'s callback, :1646-1650;
  `generic_variable_access2.ML:182-185` supplies its own), so on any run
  that does not abort the cut never fired there, and when it did the run
  was already aborting and now waits at most 400 ms for its message — and
  P-auto may prove such a goal from contradictory premises, a completeness
  gain.  The method has no caller.  For the method the cut is lost only on
  a bare `False` conclusion (§6 item 6).
- **A guard instantiated to a literal `False` by unification** (e.g. the
  `\<r>if` rule of PLPR.thy:2779 with `C := False`, reached only when
  `RDB_False` fails and the search backtracks) is the check by this
  definition and gets the check's cost; semantically that is the question
  it asks.
- **`preprocess`'s Provable is thrown away** (:217-218): when R-nitpick's
  own simplification (with the datatype split rules) closes a check's goal,
  the caller only learns "not refuted" and goes on to the judge; a cheap
  proof of inconsistency is lost.  Pre-existing, the same for every guard;
  not this plan's.


## 8. Rejected alternatives — with the reason, so that they are not re-proposed

From the design rounds:

- **A dedicated reasoner for the pattern `\<condition> False` above
  `\<condition> ?P`**, the kind supplied by the registration like
  `can_inst` (the 2026-09-11 idea's shape): when the check fails, PLPR
  backtracks to the `\<condition> ?P` reasoner, which simplifies the same
  premises again (seconds on large premise sets) and, without the digest
  marker, writes the same digest from the other path.  A cut mark on the
  dedicated reasoner cannot help: the registered cut mode is read only
  where a result was pulled (reasoner.ML:858, inside the branch opened at
  :809), while a reasoner whose tactic yields nothing falls through at
  :892 to the remaining candidates — here PLPR.thy:2005-2009.  The double
  simplification is therefore unavoidable in that shape.
- **Computing the kind inside `prove_or_refute`** from the state it
  receives: it sees the state after the template's rewrite and would
  classify `\<condition> (Inr b = Inl a)` as the check (§4.2).
- **Computing the kind in the factory and forwarding it to every solving
  function**: correct, but it touches the factory and the obligation
  instance's type for nothing; superseded by ruling 2.
- **A bool (`assume_consistent`) instead of the datatype**: superseded by
  ruling 11 — the constructor names the situation at every site.
- **`mode` as the type name**: the Premise tag's word (§1).
- **A rule inside `slice`** ("a conclusion without free variables keeps
  every premise"): implicit, and it would also change R-nitpick on ordinary
  guards whose conclusion happens to be closed; superseded by ruling 10,
  under which the check is not sliced because it is not split.
- **Passing the premises as trusted assumptions and only turning the slice
  off** (rev 1's shape): no premise would be on the strict rail — those
  Nitpick keeps nondefinitional would ride the tolerant rail, and one that
  exclusively defines a free could be dropped outright (§3 item 5);
  superseded by ruling 10.
- **Keeping the literal `true` for `trust_assms` under the check** (the
  second review's R1, recommended by its judge): the check's Nitpick call
  would be identical to an ordinary guard's except for the antecedents, and
  a stage-2 difference attributable to the antecedents alone; the author
  ruled `false` instead (ruling 17), taking the stricter problem and the
  unprobed one-way difference recorded in §7.
- **Unknown of the check silent, or at trace level 2**: ruled level 1 with
  the dedicated text (ruling 4).
- **The kind in `judge_arg`**: the judge is assumption-free (§4.4); phase 2
  can add it if the judge's prompt turns out to want it.

From the review of rev 1 (§10), rejected by its judge — one line each:

- **Delete the factory's front `quick_cut 1 th` as dead code** (F11): a
  no-op is not an invariant anyone must remember; deleting the sibling at
  :1661 would drag `safe_obligation_solver` under the corpus floor.
- **`guard_kind_of` should return a record** (F14, on the bool of rev 1):
  moot under the datatype; the type already names both cases.
- **Stage 1's file order "contradicts" per-edit re-evaluation** (F16):
  every ordered multi-file refactor has non-compiling intermediate states;
  the order states the dependency.
- **Give the kind to `nitpick` only, not to `preprocess`** (F20): the
  exported type of `preprocess` would then keep its shape while its contract
  changed, and the file's one-place enumeration of weakenings would break.
- **P-auto may prove the check by instantiation, so hedge the texts**
  (F21) and **no probe states `can_inst`** (F6): both invert `subtract`'s
  argument order; fix level 1 fixes every variable of the check's premises
  (§4.3 c), so `can_inst` cannot bite.
- **The abbreviation also spells ordinary guards the template's rewrite
  turned into `False`** (F22): the printed goals are post-simplification
  and untagged; §1 draws the distinction; the proposed clause would be
  false in the direction that governs behaviour.
- **Rename the constant to `Inconsistent_Premises`** (F26): a third
  vocabulary for one concept, against the author's spelling and the
  approved warning.
- **The corpus floor is unobtainable** (F7): the baseline is the committed
  stores plus the `V_on_dbg` leg of 2026-09-21, run after §39.
- **Skip R-nitpick for the check as R-conv is skipped** (R2): R-conv has no
  assumption-free variant; R-nitpick's assumption-free form is the
  question; the judge is not installed today; an Unknown entry pays P-auto
  on every run where a Refuted entry costs 1 ms.
- **Make stage P a companion commit after the code** (R3): reorders work
  without changing the result and splits `PLPR.thy`'s edits.
- **Carry the kind as a `Config` value in the context** (R4): does not
  compile as proposed (guard_refute.ML loads first), the smoke test's digest
  would silently disagree with the engine's, and a goal-derived value in a
  context-scoped carrier makes cache correctness a remembered invariant.
- **Widen the factory's digest callback to take `th0`** (R5): trades the
  engine-enforced contract of the digest step for a test-enforced one;
  its gain is taken by `guard_digest_of` (§4.2) instead.

From the review of rev 2 (§10), rejected by its judge — one line each:

- **Spell "R-nitpick is asked for a model of the premises themselves"
  differently in the `\<^descr>`** (F5): the sentence is right; a hedge
  there would misinform.
- **List which signature declarations change type** (F10): a stale
  declaration is a compile error at reasoners.ML:201; the checklist names
  the comments, the types are enforced.
- **The hoist gives up the step-1½ short-circuit** (F18): measured zero on
  the committed records — every `guard_simp_tac` refutation there has one
  subgoal.
- **`guard_kind_of` re-spells `Thm.major_prem_of`** (F20): it is the
  reading the file already uses at five sites.
- **Test the judge path with a probe** (F6's headline): the judge ref is
  `NONE` in shipped code; every check probe already runs under a `\<Longrightarrow>`
  prefix; the surviving half is §4.3 a's `concl_is_false` seam, closed by
  construction.
- **A smoke construct Kodkod cannot evaluate, to probe the rail** (F4's
  proposed probe): a test resting on an artefact of the vendored tool's
  finitization is a dirty hack in test clothing; the rail is not probed
  (§7).
- **`case` instead of `(kind = Normal)` at the `trust_assms` site** (F13):
  equality on a datatype is the idiom of the engine, the vendored copy and
  the function being edited; a `case` there makes nothing impossible that
  `=` allows.
- **Let `guard_simp_tac` return a state instead of a sequence** (R2): every
  `*_tac` in the exported signature is a tactic; the gain is two
  unreachable `case` arms.
- **Rename `Normal` to avoid `Phi_Guard_Cache.Normal`** (R3): nothing opens
  either structure unqualified where both are visible; cross-structure
  constructor reuse is the codebase's normal state.
- Also refuted on the facts: the smoke helpers "off the checklist" (F14:
  `assert_warnings` is parametric), the negative control "cannot be a
  theory command" (F17: Eisbach's `fails`), `GUARD_NITPICK_FALSIFY_PLAN.md`
  "omitted" (F19: a closed archive this plan does not edit), `preprocess`'s
  "unchanged type" (F21: it gains the kind as its first parameter).


## 9. User-visible text and names awaiting the author; deferred items

Approved: the undecided-check warning (§4.6, its first line the author's);
the constructor names `Normal` and `Check_Premise_Consistency` (the
author's); the spelling `\<check> \<premise> \<consistency>` (ruling 12); the
raw right-hand side `Premise MODE_GUARD False` (ruling 14); the light
correction of the `\<condition> P` paragraph, both sentences, in the
drafter's wording (rulings 16 and 18); `trust_assms = false` for the check
(ruling 17); the comment corrections in phi_nitpick.ML (ruling 19); the
plan's text within the design (ruling 20, under which R1 is taken).

Pending [drafter]: the type name `guard_kind` (delegated: "名字你随意起") and
its owning structure `Phi_Guard_Refute` with the re-export (§1, §4.2); the
ML names `guard_kind_of`, `guard_digest_of`, `concl_is_false`,
`string_of_guard_kind`; the HOL abbreviation's constant name
`Check_Premise_Consistency` (§4.8); the wording of the two `\<^descr>`
paragraphs (§4.8); the record attribute `kind`, its token (the
constructor's spelling) and the trace suffix (§4.7); the retirement of
`Guard_False_Probe.thy` (§5 stage 1 item 5).  The wording of the new
`\<^descr>` paragraph (§4.8) is covered by ruling 20 unless the author
objects to it on reading.

Deferred, recorded at the author's request and NOT this plan's: the author
intends to replace `\<condition>[\<safe>] P` by `\<condition> P` everywhere,
eventually [author 2026-09-22 "\<condition>[\<safe>] P 是另一个问题，其实我有计划
打算最后都换成 \<condition> P 的。不过这个我们之后再讨论吧。请记一笔"] (ruling
15).  Until then the `\<condition> P` paragraph of §4.8 does not mention the
safe variant.


## 10. The reviews and what each revision applied

**Rev 1 → rev 2.**  `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_REVIEW_2026-09-22.md`:
six lenses, a curator, one fresh defender per point, a judge; 26 findings
and 5 relaxation proposals; MET_ON_CONDITION.  Applied in rev 2: R1
accepted (§4.3 a); F1/F2 — the trust rail — resolved by ruling 10 (rev 2's
account of it was itself wrong, see below); F3, F4, F5, F8, F9, F10, F12,
F13, F15, F17, F18, F19, F23, F24, F25 and R5's narrower form.  Rejected:
§8.

**Rev 2 → rev 3.**  `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_REREVIEW_2026-09-22.md`:
four lenses on rev 2's changes, a curator, one fresh defender per point, a
judge; 22 findings and 3 relaxation proposals; MET_ON_CONDITION, the design
unchanged.  Applied here:

- MUST_DISCUSS, ruled by the author: F1 with R1 — rev 2 said "with no
  assumptions handed over, there is nothing to trust" and that passing the
  kind bought an honest label; both false (the flag relaxes the whole tail,
  which the conjecture's own generated axioms are part of; the label is
  fixed by `user_axioms = false` and unread).  The author re-ruled: the
  check passes `false` (ruling 17).  §0, §1's rails entry, §3 item 5,
  §4.1, §4.3 c, §5 stage 1 item 1, §7 and §8's bullet are rewritten on the
  true mechanism.
- DRAFTER_DECIDES: F3 (the owning structure and the re-export, §1, §4.2,
  §4.5, §5, §6), F9 (`concl_is_false` on a subgoal, §4.3 a), F6 (the
  regression probe under a prefix; the judge path's total case, §4.3 a,
  §6), F15 (`string_of_guard_kind`, §4.7), F22 (the two causes split,
  §4.3 c, §7).
- DRAFTER_APPLIES: F2 (`FALLS (<fresh> # …)`, §6), F16 (the corpus
  forecast, §6 item 4), F12 (the totality chain, §4.3 a), F4 (the rail is
  not probed, §6, §7), F7 (the checklists, §5; §6 item 2's account of the
  two existing probes), F8 (the citations, §5), F11 (the timeout path's
  surviving reason, §4.3 a, §5 stage 3), F13 (§4.1's list of readers).
- Rejected by the judge: §8.

**Rev 3 → rev 4.**  `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_THIRD_READ_2026-09-22.md`:
the targeted third read the second review's judge asked for — three
readers over the five passages that land in source comments (§4.3 a's
sketch, §4.3 c, §1's rails entry, §7, §8's `trust_assms` bullets) and, for
accuracy only, §4.8's two `\<^descr>` paragraphs; a curator, one fresh
defender per point, a judge; 13 findings and 2 relaxation proposals;
MET_ON_CONDITION, the design untouched.  Applied here (DRAFTER_APPLIES,
each checked again in stage 3's code review beside the code): F6 (`goals`
described in the file's own word, UNSIMPLIFIED — "the guard as written"
must not be typed into reasoners.ML, §4.3 a), F1 and F13 (the comment above
`nitpick` is rewritten, not extended, §4.3 c, §5), F3 (§1's quotation of the
patch comment corrected in place), F4 (the assumptions' own generated
axioms in §1; the two ungated `Abs_`/`Rep_` sites, §4.3 c), F5 (`Seq.take 1`
named as the cap, §4.3 a, §5), F8 ("every check the guard-side
simplification does not prove", §1, §2), F9 (`guard_simp_tac` keeps its
signature and call sites, not its body, §4.3 a), F10 (`add_eq_axiom` cited
to nitpick_preproc.ML:910-912), F11 (§3 item 5 and §8's first bullet: a
premise that exclusively defines a free is partitioned out; "where
`trust_assms = true` is the deliberate choice", §4.3 c), F12 (the F18
measurement moved from §7 to §8).  Rejected as nitpicking: F2 (§8's list is
not extended for it: the "definitely true" sentence stands, it is not the
forbidden sentence).  Ruled in the fourth round (§2 items 18-20): F7 —
the light correction covers both sentences of the `\<condition> P`
paragraph (§4.8); R2 — stage 1 corrects two comment blocks of
phi_nitpick.ML, comments only (§5 stage 1 item 0); R1 — taken by the
drafter under ruling 20: §4.3 c records the tail as the rule `add_nondef_axiom`
enforces, with two examples marked as examples, in place of the list the
two reviews had each caught inexact.

**Stage P** is done: phi-system `be16be02` (with the plan rev 3 and the two
review reports), root `603fefa2`; the two extra stale counts the stage
found (`jedit/DRAG_AND_DROP_PLAN.md:745`, `jedit/WORD_BOUNDARY_PLAN.md:207`,
`:217`) were corrected in the same commit by ruling.  Stage 1 begins with
the Isabelle-MCP restart (§5).

The vocabulary change of ruling 12 (premise, not hypothesis) renames the
file's subject but not the file: the plan and the reviews keep their names
(`CHECK_HYPOTHESIS_CONSISTENCY_*`) so that the reviews' citations stay
valid.
