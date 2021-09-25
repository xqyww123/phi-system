signature NU_OBTAIN = sig
  val obtain: binding -> (binding * typ option * mixfix) list ->
    (binding * typ option * mixfix) list -> (term * term list) list list ->
    ((Thm.binding * attribute list) * (term * term list) list) list ->
    bool -> Proof.state -> Proof.state
  val obtain_cmd: binding -> (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list -> (string * string list) list list ->
    ((Attrib.binding * Token.src list) * (string * string list) list) list ->
    bool -> Proof.state -> Proof.state
  val choose: (binding * typ option * mixfix) list -> term list -> 
    bool -> Proof.state -> Proof.state
  val choose_cmd: (binding * string option * mixfix) list -> string list -> 
    bool -> Proof.state -> Proof.state
end
structure NuObtain : NU_OBTAIN = struct
fun eliminate_term ctxt xs tm =
  let
    val vs = map (dest_Free o Thm.term_of) xs;
    val bads = Term.fold_aterms (fn t as Free v =>
      if member (op =) vs v then insert (op aconv) t else I | _ => I) tm [];
    val _ = null bads orelse
      error ("Result contains obtained parameters: " ^
        space_implode " " (map (Syntax.string_of_term ctxt) bads));
  in tm end;

fun eliminate ctxt rule xs As thm =
  let
    val _ = eliminate_term ctxt xs (Thm.full_prop_of thm);
    val _ = Object_Logic.is_judgment ctxt (Thm.concl_of thm) orelse
      error "Conclusion in obtained context must be object-logic judgment"

    val ((_, [thm']), ctxt') = Variable.import true [thm] ctxt;
    val prems = Drule.strip_imp_prems (Thm.cprop_of thm');
  in
    ((Drule.implies_elim_list thm' (map Thm.assume prems)
        |> Drule.implies_intr_list (map (Drule.norm_hhf_cterm ctxt') As)
        |> Drule.forall_intr_list xs)
      COMP rule)
    |> Drule.implies_intr_list prems
    |> singleton (Variable.export ctxt' ctxt)
  end;

(* fun eliminate_nusys ctx id xs As th =
  NuBasics.holrule (eliminate ctx
    (NuBasics.elim_SPEC th |> #2 |> NuBasics.internal_fact_by_id id) xs As #> @{print}) th *)
fun eliminate_nusys ctx rule xs As th =
  eliminate ctx (NuBasics.export_codeblocks
    (Thm.chyps_of th |> filter (can NuBasics.dest_codeblock_c)) rule) xs As th
  handle e => raise (@{print} e)
fun obtain_export ctxt rule xs _ As =
  (eliminate_nusys ctxt rule xs As, eliminate_term ctxt xs)


(* result declaration *)

fun case_names (obtains: ('typ, 'term) Element.obtain list) =
  obtains |> map_index (fn (i, (b, _)) =>
    if Binding.is_empty b then string_of_int (i + 1) else Name_Space.base_name b);

fun obtains_attributes obtains =
  [Rule_Cases.consumes (~ (length obtains)), Rule_Cases.case_names (case_names obtains)];

fun obtains_attribs obtains =
  [Attrib.consumes (~ (length obtains)), Attrib.case_names (case_names obtains)];


(* obtain thesis *)

fun obtain_thesis ctxt =
  let
    val ([x], ctxt') =
      Proof_Context.add_fixes [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)] ctxt;
    val t = Object_Logic.fixed_judgment ctxt x;
    val v = dest_Free (Object_Logic.drop_judgment ctxt t);
  in ((v, t), ctxt') end;


(* obtain clauses *)

local

val mk_all_external = Logic.all_constraint o Variable.default_type;

fun mk_all_internal ctxt (y, z) t =
  let
    val T =
      (case AList.lookup (op =) (Term.add_frees t []) z of
        SOME T => T
      | NONE => the_default dummyT (Variable.default_type ctxt z));
  in Logic.all_const T $ Term.lambda_name (y, Free (z, T)) t end;

fun prepare_clause prep_var parse_prop mk_all ctxt thesis raw_vars raw_props =
  let
    val ((xs', vars), ctxt') = ctxt
      |> fold_map prep_var raw_vars
      |-> (fn vars => Proof_Context.add_fixes vars ##>> pair vars);
    val xs = map (Variable.check_name o #1) vars;
  in
    Logic.list_implies (map (parse_prop ctxt') raw_props, thesis)
    |> fold_rev (mk_all ctxt') (xs ~~ xs')
  end;

fun prepare_obtains prep_clause check_terms
    ctxt thesis (raw_obtains: ('typ, 'term) Element.obtain list) =
  let
    val clauses = raw_obtains
      |> map (fn (_, (raw_vars, raw_props)) => prep_clause ctxt thesis raw_vars raw_props)
      |> check_terms ctxt;
  in map fst raw_obtains ~~ clauses end;

val parse_clause = prepare_clause Proof_Context.read_var Syntax.parse_prop mk_all_external;
val cert_clause = prepare_clause Proof_Context.cert_var (K I) mk_all_internal;

in

val read_obtains = prepare_obtains parse_clause Syntax.check_terms;
val cert_obtains = prepare_obtains cert_clause (K I);
val parse_obtains = prepare_obtains parse_clause (K I);

end;

(** obtain: augmented context based on generalized existence rule **)

(*
  obtain (a) x where "A x" <proof> \<equiv>

  have thesis if a [intro?]: "\<And>x. A x \<Longrightarrow> thesis" for thesis
    apply (insert that)
    <proof>
  fix x assm <<obtain_export>> "A x"
*)

fun print_results int = Proof_Display.print_results int (Position.thread_data ())

local
fun gen_obtain prep_stmt prep_att that_binding raw_decls raw_fixes raw_prems raw_concls int state =
  let
    val _ = Proof.assert_forward_or_chain state;

    val ((_, thesis), thesis_ctxt) = obtain_thesis (Proof.context_of state);

    val ({vars, propss, binds, result_binds, ...}, params_ctxt) =
      prep_stmt (raw_decls @ raw_fixes) (raw_prems @ map #2 raw_concls) thesis_ctxt;
    val (decls, fixes) = chop (length raw_decls) vars ||> map #2;
    val (premss, conclss) = chop (length raw_prems) propss;
    val propss' = (map o map) (Logic.close_prop fixes (flat premss)) conclss;

    val that_prop =
      Logic.list_rename_params (map (#1 o #2) decls)
        (fold_rev (Logic.all o #2 o #2) decls (Logic.list_implies (flat propss', thesis)));

    val cparams = map (Thm.cterm_of params_ctxt o #2 o #2) decls;
    val prep_att = map (prep_att params_ctxt)
    fun apply_attr ctx attr = map (fn th => (Thm.proof_attributes attr th ctx |> #1))
    val attr_immediate = map (fn ((_, raw_atts'), _) => prep_att raw_atts') raw_concls
    val attr_delayed = map (fn (((b, raw_atts), _), _) => (b,prep_att raw_atts)) raw_concls
    val asms = map (map (rpair []) #> pair Binding.empty_atts) propss';

    val specthm = Proof.the_fact state
    fun after_qed (result_ctxt, results) state' =
      let open NuBasics
        val ctx0 = Proof.context_of state'
        val [rule] = Proof_Context.export result_ctxt ctx0 (flat results)
        val asm_thms = 
          map (map (Thm.assume o Thm.cterm_of ctx0)) propss'
            |> map2 (apply_attr result_ctxt) attr_immediate
            |> (fn ths => attr_delayed ~~ ths);
        (* val (id,specthm) = specthm |> intro_interal_fact_spec rule *)
      in
        state'
        |> Proof.fix (map #1 decls)
        |> Proof.map_context (fold (Variable.bind_term o apsnd (Logic.close_term fixes)) binds)
        |> Proof.assm (obtain_export params_ctxt rule cparams) [] [] asms
        |> Proof.map_context_result (NuSys.declare_facts asm_thms specthm)
        |-> Proof.set_facts o single
      end;
  in
    state
    |> NuToplevel.setup_proof (print_results int) Proof_Context.mode_default false "\<nu>lemma"
        NONE after_qed [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)]
        [((that_binding, [Context_Rules.intro_query NONE]), [(that_prop, [])])]
        [[(thesis, [])]]
    |-> Proof.refine_insert
    |> Proof.map_context (fold Variable.bind_term result_binds)
  end;
in

val obtain = gen_obtain Proof_Context.cert_stmt (K I);
val obtain_cmd = gen_obtain Proof_Context.read_stmt Attrib.attribute_cmd;

end;

local
val exE = @{thm exE} and ExTy_strip = @{thm NuPrim.ExTyp_strip}
and CodeBlock_unabbrev = @{thm NuPrim.CodeBlock_unabbrev}
and CodeBlock_abbrev = @{thm NuPrim.CodeBlock_abbrev}
fun expand_exE ctx th =
  (th RS exE) |>
    Tactic.rule_by_tactic ctx (REPEAT (Tactic.eresolve_tac ctx [exE] 1))
fun match_vars ctx ret [] [] [] = rev ret
  | match_vars ctx ret insts' [] (x::insts) =
      error "unequalled length of instantiations and quantifiers"
  | match_vars ctx ret insts' (quant::vars) [] =
      error ("quantifier "^(Syntax.string_of_term ctx quant)^" is not been instantiated")
  | match_vars ctx ret insts' (quant::vars) ((v,x)::insts) =
      if v = quant
      then match_vars ctx (x::ret) [] vars (insts' @ insts)
      else match_vars ctx ret ((v,x)::insts') (quant::vars) insts
fun trim_var_name name =
  if String.isSuffix "__" name
  then String.substring (name, 0, String.size name - 2)
  else name
val trim_var = dest_Free #> apfst trim_var_name #> Free
fun gen_choose prep_stmt raw_decls raw_insts int stat =
  let open NuBasics NuHelp HOLogic
    val ctx = Proof.context_of stat
    val (focus,facts) = Proof.the_fact stat |> elim_SPEC
    val (org_vars, org_body) = prop_of focus |> dest_Trueprop |>
      (fn x => case x of (Const ("NuPrim.CurrentConstruction", ty) $ p $ T) =>
        case strip_named_binder "NuPrim.ExTyp" T of (vars, body) =>
          (map snd vars, (Const ("NuPrim.CurrentConstruction", ty) $ p $ body)))
    val t1 = ((Thm.assume (current_codeblock focus)) COMP CodeBlock_unabbrev) 
    val t2 = ((Thm.assume (current_codeblock focus)) COMP CodeBlock_abbrev)
    val focus = Raw_Simplifier.rewrite_rule ctx [ExTy_strip] focus

    (* val focus = Simplifier.asm_simplify
          (fold Simplifier.add_simp [ExTy_strip, CodeBlock_unabbrev] ctx)
          (disch_current_codeblock focus) |> @{print} *)
    val fix_lst = fix_frees_lst Position.none org_vars
    val (_,ctx_fixed) = Proof_Context.add_fixes fix_lst ctx
    val org_vars' = map (free_to_fix ctx_fixed) org_vars
    val ({vars=decl_vars,propss=[insts],binds=[],result_binds=[],...}, params_ctx) =
      prep_stmt raw_decls [map (rpair []) raw_insts]  ctx_fixed
    val insts = map (dest_eq o dest_Trueprop) insts |> match_vars params_ctx [] [] org_vars'
    val inst_body = subst_free (org_vars ~~ insts) org_body

    val goal = inst_body |> list_mk_binder "HOL.Ex" (map (#2 o #2) decl_vars |> rev)
          |> mk_Trueprop |> Syntax.check_term params_ctx
    val that_vars = map dest_Free org_vars' |> map Free
           (*|> Variable.variant_frees params_ctx [] |> map Free |> @{print} *)
    val that_prop = mk_Trueprop (subst_free (org_vars ~~ that_vars) org_body)
    val cparams = map (Thm.cterm_of params_ctx o #2 o #2) decl_vars;

    val focus_ex = expand_exE params_ctx focus
    val specthm'_term = mk_Trueprop (subst_free [Logic.dest_equals (prop_of t1)] inst_body)
    val specthm' = intro_SPEC 
        (Thm.assume (Thm.cterm_of params_ctx specthm'_term)
          |> Raw_Simplifier.rewrite_rule params_ctx [t2]
        , facts)
    fun after_qed (result_ctxt, results) state' =
      let open NuBasics
        val ctx' = Proof.context_of state'
        val [rule] = Proof_Context.export result_ctxt ctx' (flat results)
        val rule = rule
              |> Drule.forall_intr_list (map (Thm.cterm_of params_ctx) that_vars)
        val rule = (rule COMP focus_ex) |> Raw_Simplifier.rewrite_rule ctx' [t1]
              |> expand_exE ctx'
        (* val (id,specthm) = specthm |> intro_interal_fact_spec rule *)
      in
        state'
        |> Proof.fix (map #1 decl_vars)
        |> Proof.assm (obtain_export params_ctx rule cparams) [] []
            [(Binding.empty_atts, [(specthm'_term,[])])]
        |> Proof.set_facts [specthm']
      end;
  in
    stat
    |> NuToplevel.setup_proof (print_results int) Proof_Context.mode_default false "\<nu>lemma"
        NONE after_qed [] [(Binding.empty_atts, [(that_prop, [])])]
        [[(goal, [])]]
    |-> Proof.refine_insert
  end;
in
val choose = gen_choose Proof_Context.cert_stmt
val choose_cmd = gen_choose Proof_Context.read_stmt
end

end

