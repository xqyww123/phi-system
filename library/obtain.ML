signature NU_OBTAIN = sig
  val choose : binding list -> Proof.state -> Proof.state
  val auto_choose : Proof.state -> Proof.state
end
structure NuObtain : NU_OBTAIN = struct
fun eliminate_term ctxt xs thm =
  let open NuBasics
    val tm = Thm.prop_of thm
    val vs = map (dest_Free o Thm.term_of) xs;
    val bads = Term.fold_aterms (fn t as Free v =>
      if member (op =) vs v then insert (op aconv) t else I | _ => I) tm [];
  in
    if null bads then thm
    else let
      val typing' = dest_current_nu thm
            |> list_mk_binder @{const_name ExSet} bads
            |> Syntax.check_term ctxt |> cterm_of ctxt
    in
      NuSys.cast_completely ctxt typing' thm
    end
  end;

fun eliminate ctxt rule xs As thm =
  let
    val thm = eliminate_term ctxt xs thm
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

fun eliminate_nusys ctx rule xs As th =
  eliminate ctx rule xs As th
  handle e => Exn.reraise (@{print} e)
fun obtain_export ctxt rule xs _ As = (eliminate_nusys ctxt rule xs As, I)

local
fun expand_exE ctx th =
  (th RS @{thm exE}) |>
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
in

fun choose inst_names stat =
  let open NuBasics NuHelp HOLogic Term
    val major = NuBasics.the_nu_fact stat
    val ctx = Proof.context_of stat
    fun map_name_result f b c =
          (f (Binding.name_of b) c) |>> (fn s => Binding.map_name (K s) b)
    val (inst_names,_) =
      fold_map (map_name_result Name.variant) inst_names (Name.make_context [])
    val ExTyp_strip = Proof_Context.get_thm ctx "local.\<phi>ExTyp_strip"
    val major = Raw_Simplifier.rewrite_rule ctx ExTyp_strip major
    val (vars,body) = prop_of major |> dest_Trueprop |> strip_binder_raw "HOL.Ex"
    val var_tys = map snd vars
    val (inst_names, stat) =
          Proof.map_context_result (Proof_Context.add_fixes
            (map (fn (ty,nam) => (nam, SOME ty, NoSyn)) (var_tys~~inst_names))
          ) stat
    val insts = map Free (inst_names ~~ var_tys)
    val ctx = Proof.context_of stat
    val meta'_term = mk_Trueprop (subst_bounds (rev insts, body))
                        |> Thm.cterm_of ctx
    val meta' = Thm.assume  meta'_term
    val rule = expand_exE ctx major
    val cinsts = map (Thm.cterm_of ctx) insts;
  in
    stat |> Proof.map_context
              (Assumption.add_assms (obtain_export ctx rule cinsts) [meta'_term] #> snd)
         |> NuBasics.set_nu_fact meta'
  end

fun auto_choose stat =
  let
    val vars = NuBasics.dest_current_nu (NuBasics.the_nu_fact stat)
          |> NuHelp.strip_binder_vars @{const_name ExSet}
          |> map (Binding.name o NuBasics.normlize_name o fst)
  in
    choose vars stat
  end

end
end

