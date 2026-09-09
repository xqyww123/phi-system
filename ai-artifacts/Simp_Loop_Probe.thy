theory Simp_Loop_Probe
  imports Main
begin

section \<open>A rewrite counter installed through Raw_Simplifier.trace_ops\<close>

ML \<open>
(*Per-context slot holding the counter cell of the current measured run.
  NONE = not measuring, so the hook costs one Proof_Data lookup elsewhere.*)
structure Rewrite_Counter = Proof_Data (
  type T = int Unsynchronized.ref option;
  fun init _ = NONE);

exception REWRITE_LIMIT of int;

(*negative = no limit*)
val rewrite_limit = Unsynchronized.ref ~1;

fun count_rrule (_: {unconditional: bool, cterm: cterm, thm: thm,
                     rrule: Raw_Simplifier.rrule}) ctxt cont =
  (case cont ctxt of
    NONE => NONE
  | some =>
      (case Rewrite_Counter.get ctxt of
        NONE => some
      | SOME r =>
          let val n = ! r + 1 in
            r := n;
            if ! rewrite_limit >= 0 andalso n > ! rewrite_limit
            then raise REWRITE_LIMIT n
            else some
          end));
\<close>

setup \<open>
  Simplifier.set_trace_ops
    {trace_invoke = fn _ => fn ctxt => ctxt,
     trace_rrule = count_rrule,
     trace_simproc = fn _ => fn ctxt => fn cont => cont ctxt}
\<close>

ML \<open>
fun probe name ctxt goal tac =
  let
    val r = Unsynchronized.ref 0;
    val ctxt' = Rewrite_Counter.put (SOME r) ctxt;
    val start = Timing.start ();
    val msg =
      (Timeout.apply (Time.fromSeconds 2)
        (fn () =>
          (Goal.prove ctxt' [] [] goal (fn {context, ...} => tac context 1); "PROVED")) ())
      handle
        Timeout.TIMEOUT t => "TIMEOUT " ^ Time.toString t
      | REWRITE_LIMIT n => "REWRITE_LIMIT " ^ string_of_int n
      | ERROR msg => "ERROR " ^ msg
      | THM (msg, _, _) => "THM " ^ msg
      | TERM (msg, _) => "TERM " ^ msg;
  in writeln (name ^ ": " ^ msg ^ "   rewrites=" ^ string_of_int (! r) ^
              "   " ^ Timing.message (Timing.result start)) end;
\<close>

section \<open>(a) counting on a normal simpset\<close>

ML \<open>
probe "a1/simp" \<^context>
  \<^prop>\<open>rev (rev [a, b, c]) = [a, b, c] \<and> (2::nat) + 2 = 4\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);

probe "a2/auto" \<^context>
  \<^prop>\<open>\<forall>xs. length (rev (xs @ [x])) = Suc (length xs)\<close>
  (fn ctxt => fn _ => Clasimp.auto_tac ctxt);
\<close>

section \<open>(b) looping rule sets\<close>

axiomatization f g :: "nat \<Rightarrow> nat" and aa bb :: nat
  where selfloop: "f x = f x"
    and growth:   "g x = g (g x)"
    and ab: "aa = bb"
    and ba: "bb = aa"

ML \<open>
val loop_ctxt = \<^context>;

(*L1: reflexive rule f x = f x*)
probe "b1/selfloop" (loop_ctxt addsimps @{thms selfloop})
  \<^prop>\<open>f (0::nat) = f 0\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);

(*L2: growth rule g x = g (g x)*)
probe "b2/growth" (loop_ctxt addsimps @{thms growth})
  \<^prop>\<open>g (0::nat) = g 0\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);

(*L3: the classic a = b / b = a pair*)
probe "b3/ab-ba" (loop_ctxt addsimps @{thms ab ba})
  \<^prop>\<open>aa = bb\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);
\<close>

section \<open>(c) the same loops with the rewrite-count limit armed\<close>

ML \<open>
rewrite_limit := 2000;

probe "c1/selfloop" (\<^context> addsimps @{thms selfloop})
  \<^prop>\<open>f (0::nat) = f 0\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);

probe "c2/growth" (\<^context> addsimps @{thms growth})
  \<^prop>\<open>g (0::nat) = g 0\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);

probe "c3/ab-ba" (\<^context> addsimps @{thms ab ba})
  \<^prop>\<open>aa = bb\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);

probe "c4/auto-with-loop" (\<^context> addsimps @{thms ab ba})
  \<^prop>\<open>aa = bb \<and> (1::nat) + 1 = 2\<close>
  (fn ctxt => fn _ => Clasimp.auto_tac ctxt);

rewrite_limit := ~1;
\<close>

section \<open>(d) a CONDITIONAL loop: the only loop simp_depth_limit does catch\<close>

axiomatization k :: "nat \<Rightarrow> nat"
  where kcond: "k x = 0 \<Longrightarrow> k x = 1"

ML \<open>
(*proving the condition k ?x = 0 re-invokes the simplifier on k ?x, so each
  nesting level raises simp_depth; the limit stops it -- silently, as NONE.*)
probe "d1/cond-loop (limit 40)" (\<^context> addsimps @{thms kcond})
  \<^prop>\<open>k (0::nat) = 1\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);

probe "d2/cond-loop (limit 5)"
  (Config.put simp_depth_limit 5 (\<^context> addsimps @{thms kcond}))
  \<^prop>\<open>k (0::nat) = 1\<close>
  (fn ctxt => fn i => Simplifier.asm_full_simp_tac ctxt i);
\<close>

end
