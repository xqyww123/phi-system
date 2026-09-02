(*The port from more_thm.ML:add_axiom had lost the TYPE half of the
  varification Theory.add_axiom performs on storage, so every polymorphic
  declaration crashed; add_debt_axiom's recovery chain restores it.
  Propositions entering add_debt_axiom must be closed: no schematic variables
  (Sign.no_vars) and no free term variables (the entry check below).*)

signature DEBT_AXIOM = sig

val add_debt_axiom : Proof.context -> binding (*name of the debt axiom*) * term (*its proposition*)
                                   -> theory -> ( string (*full name of the debt*)
                                                * thm (*the debt axiom*)) * theory
val add_debt_axiom_global : binding * term -> theory -> (string * thm) * theory

val debt_axiomatization: (binding * typ option * mixfix) list ->
    (binding * typ option * mixfix) list -> term list ->
    (Attrib.binding * term) list -> theory -> (term list * thm list) * theory
val debt_axiomatization_cmd: (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list -> string list ->
    (Attrib.binding * string) list -> theory -> (term list * thm list) * theory

val discharge : ( string (*full name of the debt to discharge*)
                * thm (*a theorem certifying the axiom debt, which first-order matches the debt AND
                        its derivation does not depend on ANY debt axiom including those have been
                        discharged.*)
                ) list -> theory -> theory
val discharge_cmd : ((xstring * Position.T) * (Facts.ref * Token.src list)) list
                 -> theory -> theory

val instantiate_type : string -> string -> binding * Token.src list
                    -> binding -> binding -> theory -> (string * thm * thm) * theory
val instantiate_type_cmd : (binding * Token.src list) *
                            (((xstring * Position.T) * (xstring * Position.T)) *
                              (binding * binding) option)
                                -> theory -> theory

val debts : theory -> term Symtab.table
val is_debt : theory -> term (*a proposition*) -> bool
  (*does the proposition match an UNDISCHARGED debt axiom?  Both sides
    are compared in the ledger normal form with outer !!-parameters
    generalized -- so a debt is recognized both as declared and as the
    Spec_Rules export path stores it -- up to renaming of schematic
    variables (Pattern.equiv, as in Thm.equiv_thm).  An INSTANCE of a
    debt is not the debt and does not match.  Total: never raises on
    schematic input.  Discharged debts no longer match.*)
val list_debts : theory -> unit

end

structure Debt_Axiom : DEBT_AXIOM = struct

(*Copied and modified from more_thm.ML:add_axiom; the sort-recovery
  substitution is built lazily in ledger_form, so the matching path stays
  total.*)
fun stripped_sorts t =
  let
    val tfrees = build_rev (Term.add_tfrees t);
    val tfrees' = map (fn a => (a, [])) (Name.variant_list [] (map #1 tfrees));
    val strip = map (apply2 TFree) (tfrees ~~ tfrees');
    val t' = Term.map_types (Term.map_atyps (perhaps (AList.lookup (op =) strip))) t;
  in (tfrees, tfrees', strip, t') end;

(*devarify type schematics injectively (index folded into the name);
  identity on the declaration path, where Sign.no_vars has excluded
  schematics.  No Isabelle surface syntax can write a dot into a
  type-variable name, so the dotted name cannot collide with a real
  TFree; only an ML-constructed term could.*)
fun devarifyT t = t |> Term.map_types (Term.map_atyps
      (fn TVar ((a, i), S) => TFree (a ^ "." ^ string_of_int i, S) | A => A))

(*the ledger normal form of a proposition (the recorded shape), plus what
  the recorder needs to rebuild the user-facing theorem.  recover and
  of_sorts are closures: only the declaration path consumes them, and the
  matching path, which discards them, must not pay for them -- nor, for
  recover, risk the TYPE exception its certification can raise.*)
fun ledger_form thy prop =
  let
    val prop = devarifyT prop
    val (tfrees, tfrees', strip, prop') = stripped_sorts prop
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip
  in {recover = fn () =>
        map2 (fn (a', S') => fn (a, S) =>
          (((a', 0), S'), Thm.global_ctyp_of thy (TVar ((a, 0), S)))) tfrees' tfrees,
      of_sorts = fn ctxt =>
        maps (fn (T as TFree (_, S), _) => Thm.of_sort (Thm.ctyp_of ctxt T, S)) strip,
      prop = Logic.list_implies (maps Logic.mk_of_sort constraints, prop')}
  end

(*term-level mirror of Variable.gen_all (variable.ML:510): outer
  !!-parameters, as Drule.outer_params delivers them (names already made
  distinct), become schematic Vars at one fresh index*)
fun gen_all_term t =
  let
    val idx = Term.maxidx_of_term t + 1
    val vars = map (fn (a, T) => Var ((a, idx), T)) (Drule.outer_params t)
  in Term.subst_bounds (rev vars, Term.strip_all_body t) end

(*what both sides of the comparison are reduced to: the ledger normal form,
  HHF-normalized, outer !!-params generalized -- mirroring what the
  export did to the consumer's copy -- and type frees varified*)
fun match_form thy prop =
  #prop (ledger_form thy prop)
  |> Drule.norm_hhf thy
  |> gen_all_term
  |> Logic.varify_types_global

fun is_debt thy t =
  let val u = match_form thy t
  in Symtab.exists (fn (_, ax) => Pattern.equiv thy (u, match_form thy ax))
       (Debt_Axiom_Kernel.debts thy)
  end

(*Copied and modified from more_thm.ML:add_axiom*)
fun add_debt_axiom ctxt (b, prop) thy =
  let
    val _ = Sign.no_vars ctxt prop;
    val _ = null (Term.add_frees prop [])
      orelse error ("add_debt_axiom: free term variables in " ^
                    Syntax.string_of_term ctxt prop);
    val form = ledger_form thy prop;
    val axm_name = Sign.full_name thy b;
    val (axm', thy') =
      Debt_Axiom_Kernel.axiomize (axm_name, Thm.global_cterm_of thy (#prop form)) thy;
    val thm =
      axm'
      |> Thm.varifyT_global
         (*restores the TYPE half of the varification Theory.add_axiom
           performs on storage (theory.ML:237) and the oracle backend
           skips; the chain below is the verbatim more_thm.ML:add_axiom
           recovery and assumes schematic input.  The term half
           (Free -> Var) stays out of scope: both creators close term
           variables (Logic.close_prop); the entry check above rejects
           the rest loudly.  Identity on monomorphic axioms.*)
      |> Thm.instantiate (TVars.make (#recover form ()), Vars.empty)
      |> Thm.unvarify_global thy'
      |> fold Thm.elim_implies (#of_sorts form ctxt);
  in ((axm_name, thm), thy') end;

fun add_debt_axiom_global arg thy = add_debt_axiom (Syntax.init_pretty_global thy) arg thy;


(*Copied and modified from the implementation of the command axiomatization.*)
fun gen_axioms prep_stmt prep_att raw_decls raw_fixes raw_prems raw_concls thy =
  let
    (*specification*)
    val ({vars, propss = [prems, concls], ...} : Proof_Context.stmt, vars_ctxt) =
      Proof_Context.init_global thy
      |> prep_stmt (raw_decls @ raw_fixes) ((map o map) (rpair []) [raw_prems, map snd raw_concls]);
    val (decls, fixes) = chop (length raw_decls) vars;

    val frees =
      rev ((fold o fold) (Variable.add_frees vars_ctxt) [prems, concls] [])
      |> map (fn (x, T) => (x, Free (x, T)));
    val close = Logic.close_prop (map #2 fixes @ frees) prems;
    val specs =
      map ((apsnd o map) (prep_att vars_ctxt) o fst) raw_concls ~~ map close concls;

    val spec_name =
      Binding.conglomerate (if null decls then map (#1 o #1) specs else map (#1 o #1) decls);


    (*consts*)
    val (consts, consts_thy) = thy
      |> fold_map (fn ((b, _, mx), (_, t)) => Sign.declare_const_global ((b, Term.type_of t), mx)) decls;
    val subst = Term.subst_atomic (map (#2 o #2) decls ~~ consts);

    (*axioms*)
    val (axioms, axioms_thy) =
      (specs, consts_thy) |-> fold_map (fn ((b, atts), prop) =>
        add_debt_axiom_global (b, subst prop) #>> (fn (_, th) => ((b, atts), [([th], [])])));

    (*facts*)
    val (facts, facts_lthy) = axioms_thy
      |> Named_Target.theory_init
      |> Spec_Rules.add spec_name Spec_Rules.Unknown consts (maps (maps #1 o #2) axioms)
      |> Local_Theory.notes axioms;

  in ((consts, map (the_single o #2) facts), Local_Theory.exit_global facts_lthy) end;

val debt_axiomatization = gen_axioms Proof_Context.cert_stmt (K I);
val debt_axiomatization_cmd = gen_axioms Proof_Context.read_stmt Attrib.check_src;


(** Discharge **)

val discharge = Debt_Axiom_Kernel.discharge

(*the subgoal-directed closing step: read the residual OFCLASS
  obligation off the subgoal, rebuild its type with the sorts the
  subgoal's own OFCLASS hypotheses grant, and reflect the
  class-order/arity fact through Thm.of_class -- the real
  Sign.of_sort check, a genuine PClass proof, no trust added --
  internalized by the same unconstrainT the goal and the certificate
  went through.  Works uniformly for obligations on debt variables,
  composite types, and ground types; a rule manufactured for subgoal
  i can only apply to subgoal i; depth one, no recursion.  The
  handles wrap rule CONSTRUCTION only (reflection declined: not an
  OFCLASS subgoal, or Sign.of_sort refuses) -- the subgoal is then
  left open for the caller to display; interrupts are not among the
  caught constructors and always propagate.*)
fun ofclass_close_tac ctxt = SUBGOAL (fn (sg, i) =>
  let
    val thy = Proof_Context.theory_of ctxt
    val concl = Logic.strip_assums_concl sg
    val hyps = Logic.strip_assums_hyp sg
    val cs = map_filter (try Logic.dest_of_class) hyps
    fun sort_of a = map snd (filter (fn (T, _) => T = TFree (a, [])) cs)
    val (T, c) = Logic.dest_of_class concl
    val T' = T |> Term.map_atyps
          (fn TFree (a, []) => TVar ((a, 0), sort_of a) | A => A)
    val rule = Thm.unconstrainT (Thm.of_class (Thm.global_ctyp_of thy T', c))
  in Tactic.solve_tac ctxt [rule] i end
  handle TERM _ => no_tac | THM _ => no_tac | TYPE _ => no_tac)

fun discharge_cmd ax_certs thy =
  let
    val ax_names = map (Global_Theory.check_fact thy o fst) ax_certs
    val _ =
      (case duplicates (op =) ax_names of
        [] => ()
      | N :: _ => error (quote N ^ " is named twice in one discharge"))
    val ctxt = Proof_Context.init_global thy

    (*total where Facts.string_of_ref alone is not (it raises Fail on
      literal facts, facts.ML:112); an attributes-only certificate has no
      name of its own, so the fallback names the debt-name position --
      when the front end renders positions at all; the attribute list is
      deliberately not printed*)
    fun string_of_certificate _ (Facts.Fact s, _) = "literal fact " ^ quote s
      | string_of_certificate pos (r, _) =
          (case Facts.string_of_ref r of
            "" =>
              (case Position.here pos of
                "" => "the given certificate"
              | s => "the certificate given at" ^ s)
          | s => s)
    fun err_discharge N pos C msg =
      error ("discharge_debt_axiom: discharging " ^ quote N ^ " by " ^
             string_of_certificate pos C ^ " failed:\n" ^ msg)

    val debts_due =
      ax_names ~~ ax_certs |> map (fn (N, ((_, pos), C)) =>
        (case Symtab.lookup (Debt_Axiom_Kernel.debts thy) N of
          SOME ax => (N, pos, C, Thm.global_cterm_of thy ax)
        | NONE => error (N ^ " is not an undischarged debt axiom")))

    val certs = debts_due |> map (fn (N, pos, C, goal_ct) =>
      (let
         val rules = map (Thm.unconstrainT o Thm.varifyT_global)
                         (Attrib.eval_thms ctxt [C])
           (*unconstrainT mirrors the ledger normal form up to
             type-variable renaming; varifyT_global first makes its
             no-fixed-type-variables precondition hold unconditionally
             (identity on global facts)*)
       in
         Goal.prove_internal ctxt [] goal_ct
           (K (HEADGOAL (TRY o Tactic.ares_tac ctxt rules)
               THEN ALLGOALS (TRY o (Tactic.assume_tac ctxt
                      ORELSE' ofclass_close_tac ctxt))))
       end
       (*ERROR/THM/TYPE only -- a catch-all would swallow interrupts unless
         it re-raised them explicitly; the caught messages are already
         user-facing (e.g. goal.ML's "Proof failed." display)*)
       handle ERROR msg => err_discharge N pos C msg
            | THM (msg, _, _) => err_discharge N pos C msg
            | TYPE (msg, _, _) => err_discharge N pos C msg))
  in Debt_Axiom_Kernel.discharge (ax_names ~~ certs) thy
  handle Fail "dep" =>
         error "Some of the given certification theorems are based on axiomized debts!"
       | Fail "cert" =>
         error "Some of the given certification theorems fails to match the debt!"
  end


(** Instantiate Type **)

(*N  : full name of the type T to be instantiated
  N' : full name of the type T' that T instantiates to
  RB : binding of the Rep, i.e., the injector from T to T'
  AB : binding of the Abs, i.e., the projector from T' to T
  axB: binding of the bijection axiom.
*)
fun instantiate_type N N' (axB,attr) RB AB thy =
  let val n = Sign.arity_number thy N
      val ty_args = map (fn a => TFree (a, Sign.defaultS thy)) (Name.invent Name.context Name.aT n)
      val (T,T') = (Type (N, ty_args), Type (N', ty_args))
      val thy01 = Sign.qualified_path true axB thy
      val (RN,AN,axN) = (Sign.full_name thy01 RB, Sign.full_name thy01 AB, Sign.full_name thy01 axB)
      val thy1 = thy01
            |> Sign.add_consts [(RB, T --> T', NoSyn), (AB, T' --> T, NoSyn)]
            |> Debt_Axiom_Kernel.instantiate_type N N' axB RN AN
            |> Sign.parent_path
      val axs = Thm.axiom thy1 axN
            |> Conjunction.elim_conjunctions
      val (R,A) = (Const (RN, T --> T'), Const (AN, T' --> T))
      val thy2 = Spec_Rules.add_global axB Spec_Rules.Unknown [R,A] axs thy1
      val ((axN,[ax1,ax2]), thy3) = Global_Theory.note_thms ""
            ((axB, map (Attrib.attribute_cmd_global thy2) attr), map (rpair [] o single) axs) thy2
  in ((axN,ax1,ax2), thy3)
  end

fun instantiate_type_cmd (binding, ((T,T'),RB_AB)) thy =
  let
    val pos = Binding.pos_of (fst binding)
    val (RB,AB) = the_default (Binding.make ("prj", pos), Binding.make ("inj", pos)) RB_AB
    val ((N,rep),_)  = Type.check_decl (Context.Theory thy) (Sign.tsig_of thy) T
    val _ = Context_Position.reports_global thy rep
    val ((N',rep),_) = Type.check_decl (Context.Theory thy) (Sign.tsig_of thy) T'
    val _ = Context_Position.reports_global thy rep
  in thy
  |> instantiate_type N N' binding RB AB |> snd
  end

(** List Obligations **)

val debts = Debt_Axiom_Kernel.debts
fun list_debts thy =
  let open Pretty
    val debts = Symtab.dest (Debt_Axiom_Kernel.debts thy)
  in
    writeln (chunks (
      block [if null debts
             then str "Good job! No debt axiom is recorded."
             else block [str (string_of_int (length debts)),
                         str (if length debts = 1 then " axiom debt is recorded:"
                              else " axiom debts are recorded:")]]
   :: map (fn (N,TH) => item [chunks [block [str N, str " : "],
                                      Syntax.pretty_term_global thy TH]]) debts
    ))
  end


(*** Commands ***)

val axiomatization =
  Parse.and_list1 (Parse_Spec.thm_name ":" -- Parse.prop) --
  Parse_Spec.if_assumes -- Parse.for_fixes >> (fn ((a, b), c) => (c, b, a));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>debt_axiomatization\<close>
    "axiomatic constant specification with records in debt so that can be discharged later"
    (( axiomatization >> (pair [])
    || (Scan.optional Parse.vars [] --
       Scan.optional (Parse.where_ |-- Parse.!!! axiomatization) ([], [], [])))
      >> (fn (a, (b, c, d)) => Toplevel.theory (#2 o debt_axiomatization_cmd a b c d)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>discharge_debt_axiom\<close> "discharge debt axioms"
    (Parse.and_list1 (Parse.name_position --| \<^keyword>\<open>:\<close> -- Parse.thm)
    >> (Toplevel.theory o discharge_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_debt_axiom\<close> "list current debt axioms"
    (Scan.succeed (Toplevel.theory (fn thy => (list_debts thy; thy))))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>unspecified_type\<close>
    "declare a type that can be specified later"
    (Parse.type_args -- Parse.binding -- Parse.opt_mixfix
      >> (fn ((args, a), mx) =>
          Typedecl.typedecl {final = false} (a, map (rpair dummyS) args, mx) #> snd))

val _ = Outer_Syntax.command \<^command_keyword>\<open>specify_type\<close>
    "define an unspecified type T to be another type T'\
    \so that there is a bijection between T and T'"
    (Parse_Spec.thm_name ":" -- ((Parse.name_position --| \<^keyword>\<open>=\<close> -- Parse.name_position)
   -- Scan.option (\<^keyword>\<open>morphisms\<close> |-- Parse.binding -- Parse.binding))
    >> (Toplevel.theory o instantiate_type_cmd))

end