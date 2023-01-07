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
val list_debts : theory -> unit

end

structure Debt_Axiom : DEBT_AXIOM = struct

fun stripped_sorts thy t =
  let
    val tfrees = build_rev (Term.add_tfrees t);
    val tfrees' = map (fn a => (a, [])) (Name.variant_list [] (map #1 tfrees));
    val recover =
      map2 (fn (a', S') => fn (a, S) => (((a', 0), S'), Thm.global_ctyp_of thy (TVar ((a, 0), S))))
        tfrees' tfrees;
    val strip = map (apply2 TFree) (tfrees ~~ tfrees');
    val t' = Term.map_types (Term.map_atyps (perhaps (AList.lookup (op =) strip))) t;
  in (strip, recover, t') end;

(*Copied and modified from more_thm.ML:add_axiom*)
fun add_debt_axiom ctxt (b, prop) thy =
  let
    val _ = Sign.no_vars ctxt prop;
    val (strip, recover, prop') = stripped_sorts thy prop;
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
    val of_sorts = maps (fn (T as TFree (_, S), _) => Thm.of_sort (Thm.ctyp_of ctxt T, S)) strip;

    val axm_name = Sign.full_name thy b;
    val axm_term = Logic.list_implies (maps Logic.mk_of_sort constraints, prop')
          |> Thm.global_cterm_of thy
    val (axm', thy') = Debt_Axiom_Kernel.axiomize (axm_name, axm_term) thy
    
    val thm =
      Thm.instantiate (TVars.make recover, Vars.empty) axm'
      |> Thm.unvarify_global thy'
      |> fold Thm.elim_implies of_sorts;
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
fun discharge_cmd ax_certs thy =
  let
    val ax_names = map (Global_Theory.check_fact thy o fst) ax_certs
    val ctxt = Proof_Context.init_global thy
    val goal = map (fn N => case Symtab.lookup (Debt_Axiom_Kernel.debts thy) N
                              of SOME ax => Thm.global_cterm_of thy ax
                                         |> Goal.prove_internal ctxt []
                               | _ => error (N ^ " is not an undischarged debt axiom")) ax_names
    val ctxt = Proof_Context.init_global thy
    val certs = map2 (fn (_,C) => fn goal =>
                  goal (K (Tactic.ares_tac ctxt (Attrib.eval_thms ctxt [C]) 1))
                ) ax_certs goal
  in Debt_Axiom_Kernel.discharge (ax_names ~~ certs) thy 
  handle Fail "dep" =>
         error "Some of the given certification theorems are based on axiomized debts!"
       | Fail "cert" =>
         error "Some of the given certification theorems fails to match the debt!"
       | Fail "unex" =>
         error "Some of the debts to discharge does not exist!"
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
             else block [str (string_of_int (length debts)), str " axiom debts are recorded:"]]
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