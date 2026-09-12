(*  Probe: is a term-exported statement aconv to the proposition of the
    thm-exported theorem?  See the report accompanying this file.        *)

theory Export_Sync_Probe
  imports Main
begin

declare [[ML_catch_all = true]]

ML \<open>
(* ---------- reporting helpers ---------- *)

fun pp ctxt t =
  Print_Mode.setmp []
    (fn () => XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt t))) ()

fun vstr t =
  let
    val vs = rev (Term.add_vars t [])
    val tvs = rev (Term.add_tvars t [])
    fun v ((n, i), _) = n ^ "." ^ string_of_int i
  in "vars=[" ^ commas (map v vs) ^ "] tvars=[" ^ commas (map v tvs) ^ "]" end

fun refused inner outer th =
  Term.exists_subterm (fn Free (x, _) => Variable.is_newly_fixed inner outer x | _ => false)
                      (Thm.prop_of th)

fun probe name outer inner stmt th =
  let
    val th_ex = singleton (Proof_Context.export inner outer) th
    val p_thm = Thm.prop_of th_ex
    val t_ex = singleton (Variable.export_terms inner outer) stmt
    val t_ex_a =
      singleton (Variable.export_terms inner outer) (Assumption.export_term inner outer stmt)
  in
    writeln (cat_lines
     ["== CASE " ^ name,
      "  maxidx inner=" ^ string_of_int (Variable.maxidx_of inner) ^
        " outer=" ^ string_of_int (Variable.maxidx_of outer),
      "  stmt            : " ^ pp outer stmt,
      "  thm as proved   : " ^ pp outer (Thm.prop_of th) ^
        "   [hyps: " ^ commas (map (pp outer) (Thm.hyps_of th)) ^ "]",
      "  THM  exported   : " ^ pp outer p_thm ^ "   " ^ vstr p_thm,
      "  TERM exported   : " ^ pp outer t_ex ^ "   " ^ vstr t_ex,
      "  TERM exp (+asm) : " ^ pp outer t_ex_a,
      "  aconv term/thm      : " ^ (if t_ex aconv p_thm then "YES" else "NO"),
      "  aconv term+asm/thm  : " ^ (if t_ex_a aconv p_thm then "YES" else "NO"),
      "  export_aux_lemma    : " ^ (if refused inner outer th then "REFUSES (returns NONE)"
                                    else "exports")])
  end

fun run name f =
  (f () handle exn =>
    if Exn.is_interrupt exn then Exn.reraise exn
    else writeln ("== CASE " ^ name ^ " RAISED: " ^ Runtime.exn_message exn))
\<close>

ML \<open>
val outer0 = Proof_Context.init_global \<^theory>;

(* ---------- (F) inner = outer, no outer parameters ---------- *)
run "F" (fn () =>
let
  val stmt = \<^prop>\<open>(1::nat) + 0 = 1\<close>
  val th = Goal.prove outer0 [] [] stmt (fn {context = c, ...} => simp_tac c 1)
in probe "F  inner = outer, stmt has no outer parameter" outer0 outer0 stmt th end);

(* ---------- (A) outer !!x, genuine inner (unused fix) ---------- *)
run "A" (fn () =>
let
  val outer = outer0
  val inner = snd (Variable.add_fixes ["unused"] outer)
  val stmt = \<^prop>\<open>\<And>x::nat. x + 0 = x\<close>
  val th = Goal.prove inner [] [] stmt (fn {context = c, ...} => simp_tac c 1)
in probe "A  outer !!x, inner adds an unrelated fix" outer inner stmt th end);

(* ---------- (A2) outer !!x, inner = outer (identity boundary) ---------- *)
run "A2" (fn () =>
let
  val stmt = \<^prop>\<open>\<And>x::nat. x + 0 = x\<close>
  val th = Goal.prove outer0 [] [] stmt (fn {context = c, ...} => simp_tac c 1)
in probe "A2 outer !!x, inner = outer" outer0 outer0 stmt th end);

(* ---------- (B) type variable declared only in inner ---------- *)
run "B" (fn () =>
let
  val a = TFree ("'a", \<^sort>\<open>type\<close>)
  val stmt =
    Logic.all (Free ("x", a)) (HOLogic.mk_Trueprop (HOLogic.mk_eq (Free ("x", a), Free ("x", a))))
  val outer = outer0
  val inner = Variable.declare_typ a outer
  val th = Goal.prove inner [] [] stmt (fn {context = c, ...} => resolve_tac c @{thms refl} 1)
in probe "B  type variable 'a only in inner" outer inner stmt th end);

(* ---------- (C) Free fixed only in inner ---------- *)
run "C" (fn () =>
let
  val outer = outer0
  val ([y], inner) = Variable.add_fixes ["y"] outer
  val yt = Free (y, \<^typ>\<open>nat\<close>)
  val stmt =
    HOLogic.mk_Trueprop (HOLogic.mk_eq (\<^Const>\<open>plus \<^Type>\<open>nat\<close>\<close> $ yt $ \<^term>\<open>0::nat\<close>, yt))
  val th = Goal.prove inner [] [] stmt (fn {context = c, ...} => simp_tac c 1)
in probe "C  Free y fixed only in inner" outer inner stmt th end);

(* ---------- (D) theorem depending on an inner assumption ---------- *)
run "D" (fn () =>
let
  val ([q], outer) = Variable.add_fixes ["Q"] outer0
  val qt = Free (q, \<^typ>\<open>bool\<close>)
  val ct = Thm.cterm_of outer (HOLogic.mk_Trueprop qt)
  val ([prem], inner) = Assumption.add_assumes [ct] outer
  val th = @{thm conjI} OF [prem, @{thm TrueI}]
  val stmt = Thm.prop_of th
in probe "D  inner assumption Q, thm = Q & True" outer inner stmt th end);

(* ---------- (E) statement not in hhf normal form ---------- *)
run "E" (fn () =>
let
  val stmt = \<^prop>\<open>True \<Longrightarrow> (\<And>x::nat. x = x)\<close>
  val inner = snd (Variable.add_fixes ["unused"] outer0)
  val th = Goal.prove inner [] [] stmt (fn {context = c, ...} => simp_tac c 1)
in probe "E  stmt = True ==> (!!x. x = x), not hhf normal" outer0 inner stmt th end);

(* ---------- (G) inner context with a raised maxidx ---------- *)
run "G" (fn () =>
let
  val outer = outer0
  val inner = outer |> Variable.declare_maxidx 7 |> snd o Variable.add_fixes ["unused"]
  val stmt = \<^prop>\<open>\<And>x::nat. x + 0 = x\<close>
  val th = Goal.prove inner [] [] stmt (fn {context = c, ...} => simp_tac c 1)
in probe "G  as A but maxidx of inner raised to 7" outer inner stmt th end);

(* ---------- (H) a hyp blocks generalisation of a type variable ---------- *)
run "H" (fn () =>
let
  val a = TFree ("'b", \<^sort>\<open>type\<close>)
  val ([w], outer) = Variable.add_fixes ["w"] outer0
  val wt = Free (w, a)
  val outer' = Variable.declare_typ a outer
  val ct = Thm.cterm_of outer' (HOLogic.mk_Trueprop (HOLogic.mk_eq (wt, wt)))
  val ([prem], inner) = Assumption.add_assumes [ct] outer'
  val stmt = HOLogic.mk_Trueprop (HOLogic.mk_eq (wt, wt))
in probe "H  hyp mentions Free w :: 'b, w still fixed in outer" outer inner stmt prem end);

(* ---------- (H2) the blocking Free occurs ONLY in the hyp, not in stmt ---------- *)
run "H2" (fn () =>
let
  val a = TFree ("'c", \<^sort>\<open>type\<close>)
  val ([w], outer) = Variable.add_fixes ["v"] outer0
  val wt = Free (w, a)
  val outer' = Variable.declare_typ a outer
  val ct = Thm.cterm_of outer' (HOLogic.mk_Trueprop (HOLogic.mk_eq (wt, wt)))
  val (_, inner) = Assumption.add_assumes [ct] outer'
  val stmt =
    Logic.all (Free ("x", a)) (HOLogic.mk_Trueprop (HOLogic.mk_eq (Free ("x", a), Free ("x", a))))
  val th = Thm.weaken ct (Goal.prove inner [] [] stmt (fn {context = c, ...} => resolve_tac c @{thms refl} 1))
in probe "H2 hyp carries 'c via a Free that stmt does not mention" outer inner stmt th end);

(* ---------- (I) a custom Assumption.export, like phi's block frame:
                 thm part discharges and rewrites, term part is the identity ---------- *)
run "I" (fn () =>
let
  val ([q], outer) = Variable.add_fixes ["Q"] outer0
  val qt = Free (q, \<^typ>\<open>bool\<close>)
  val tagged = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_not qt))   (* the "tag": ~ ~ Q *)
  val ct = Thm.cterm_of outer tagged
  val my_export : Assumption.export = fn _ => fn asms =>
    (fn th => fold_rev (fn A => fn th =>
        if not (member (op aconv) (Thm.hyps_of th) (Thm.term_of A)) then th
        else Thm.implies_intr A th
             |> Conv.fconv_rule (Conv.implies_conv
                  (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm not_not[THEN eq_reflection]}))
                  Conv.all_conv))
        asms th,
     I)
  val ([prem], inner) = Assumption.add_assms my_export [ct] outer
  val th = @{thm conjI} OF [prem RS @{thm notnotD}, @{thm TrueI}]
  val stmt = Thm.prop_of th
in probe "I  custom export (phi block-frame shape): discharge + rewrite premise" outer inner stmt th
end);

(* ---------- (J) the outer !!. is present at export time (not created by Goal.prove) ---------- *)
run "J" (fn () =>
let
  val outer = outer0
  val ([y], inner) = Variable.add_fixes ["y"] outer
  val yt = Free (y, \<^typ>\<open>nat\<close>)
  val body =
    HOLogic.mk_Trueprop (HOLogic.mk_eq (\<^Const>\<open>plus \<^Type>\<open>nat\<close>\<close> $ yt $ \<^term>\<open>0::nat\<close>, yt))
  val th0 = Goal.prove inner [] [] body (fn {context = c, ...} => simp_tac c 1)
  val th = Thm.forall_intr (Thm.cterm_of inner yt) th0     (* prop = !!y. y + 0 = y *)
  val stmt = Thm.prop_of th
in probe "J  thm's prop really is !!y. y + 0 = y at the boundary" outer inner stmt th end);

(* ---------- (J2) as J, but the INNER context has maxidx 7: which index does gen_all use? --- *)
run "J2" (fn () =>
let
  val outer = outer0
  val ([y], inner) = Variable.add_fixes ["y"] (Variable.declare_maxidx 7 outer)
  val yt = Free (y, \<^typ>\<open>nat\<close>)
  val body =
    HOLogic.mk_Trueprop (HOLogic.mk_eq (\<^Const>\<open>plus \<^Type>\<open>nat\<close>\<close> $ yt $ \<^term>\<open>0::nat\<close>, yt))
  val th0 = Goal.prove inner [] [] body (fn {context = c, ...} => simp_tac c 1)
  val th = Thm.forall_intr (Thm.cterm_of inner yt) th0
  val stmt = Thm.prop_of th
in probe "J2 as J but maxidx of inner = 7" outer inner stmt th end);

(* ---------- (K) re-association of  A ==> (!!x. B x)  at export time ---------- *)
run "K" (fn () =>
let
  val outer = outer0
  val ([y], inner) = Variable.add_fixes ["y"] outer
  val yt = Free (y, \<^typ>\<open>nat\<close>)
  val body =
    HOLogic.mk_Trueprop (HOLogic.mk_eq (\<^Const>\<open>plus \<^Type>\<open>nat\<close>\<close> $ yt $ \<^term>\<open>0::nat\<close>, yt))
  val th0 = Goal.prove inner [] [] body (fn {context = c, ...} => simp_tac c 1)
  val th = Thm.implies_intr (Thm.cterm_of inner \<^prop>\<open>True\<close>)
             (Thm.forall_intr (Thm.cterm_of inner yt) th0)  (* True ==> (!!y. y + 0 = y) *)
  val stmt = Thm.prop_of th
in probe "K  thm's prop = True ==> (!!y. y + 0 = y) at the boundary" outer inner stmt th end);

(* ---------- (Z) what guard_cache actually stores: canonical_form ---------- *)
run "Z" (fn () =>
let
  fun canonical_form ctxt0 th =
    let val th1 = Raw_Simplifier.norm_hhf_protect ctxt0 th
        val pinned = fold Term.add_tfree_names (Thm.hyps_of th1) []
        val tfrees = subtract (op =) pinned (Term.add_tfree_names (Thm.prop_of th1) [])
     in th1
     |> Thm.generalize (Names.make_set tfrees, Names.empty) (Thm.maxidx_of th1 + 1)
     |> Drule.zero_var_indexes
    end
  val a = TFree ("'a", \<^sort>\<open>type\<close>)
  val ctxt = Variable.declare_typ a outer0
  val stmt = Logic.all (Free ("x", a))
               (HOLogic.mk_Trueprop (HOLogic.mk_eq (Free ("x", a), Free ("x", a))))
  val th = Goal.prove ctxt [] [] stmt (fn {context = c, ...} => resolve_tac c @{thms refl} 1)
  val th' = canonical_form ctxt th
in
  writeln (cat_lines
   ["== CASE Z  canonical_form (what add_lemma stores), no export involved",
    "  stmt             : " ^ pp ctxt stmt,
    "  canonical_form th: " ^ pp ctxt (Thm.prop_of th') ^ "   " ^ vstr (Thm.prop_of th'),
    "  aconv            : " ^ (if stmt aconv Thm.prop_of th' then "YES" else "NO")])
end);
\<close>

end
