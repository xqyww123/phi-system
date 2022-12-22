signature NU_OBTAIN = sig
  val choose : binding list -> Proof.state -> Proof.state
  val auto_choose : Proof.state -> Proof.state
end

structure NuObtain : NU_OBTAIN = struct

fun eliminate_term ctxt xs thm =
  let open NuBasics PhiSyntax NuHelp
    val tm = Thm.prop_of thm
    val vs = map (dest_Free o Thm.term_of) xs;
    fun collect tm = Term.fold_aterms (fn t as Free v =>
                        if member (op =) vs v then insert (op =) v else I | _ => I) tm []
    val bads = collect tm;
  in
    if null bads then thm
    else case Thm.prop_of thm
      of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>\<phi>spec.CurrentConstruction\<close>, _)
                              $ _ $ _ $ _ $ _ $ _ $ _)
      => let
        val rule = Proof_Context.get_thm ctxt "introduce_Ex"
        fun generalize x thm =
          case Thm.prop_of thm
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>\<phi>spec.CurrentConstruction\<close>, _)
                                    $ _ $ _ $ _ $ _ $ _ $ P)
            => thm RS Drule.infer_instantiate ctxt [(("S",0), Thm.cterm_of ctxt (absfree x P))] rule
        in fold_rev generalize bads thm
        end
      |  \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>\<phi>spec.PendingConstruction\<close>, _)
                                  $ _ $ _ $ _ $ _ $ _ $ Q $ E)
      => let
        val bad_Q = collect Q
        val bad_E = collect E
        val rule_Q = Proof_Context.get_thm ctxt "introduce_Ex_pending"
        val rule_E = Proof_Context.get_thm ctxt "introduce_Ex_pending_E"
        fun generalize_Q x thm =
          case Thm.prop_of thm
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>\<phi>spec.PendingConstruction\<close>, _)
                                    $ _ $ _ $ _ $ _ $ _ $ Q $ _)
            => thm RS Drule.infer_instantiate ctxt
                          [(("Q",0), Thm.cterm_of ctxt (absfree x Q))] rule_Q
        fun generalize_E x thm =
          case Thm.prop_of thm
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>\<phi>spec.PendingConstruction\<close>, _)
                                    $ _ $ _ $ _ $ _ $ _ $ _ $ E)
            => thm RS Drule.infer_instantiate ctxt
                          [(("E",0), Thm.cterm_of ctxt (absfree x E))] rule_E
        in fold_rev generalize_E bad_E (fold_rev generalize_Q bad_Q thm)
        end
      | _ => raise THM (
          "General Elimination fails because locally fixed variables(s) occurs in the sequent",
          0, thm :: map Drule.mk_term xs
        )
  end;

fun eliminate ctxt rule xs As thm'' =
  let
    val thm = eliminate_term ctxt xs thm''
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

fun eliminate_nusys ctxt rule xs As th =
  eliminate ctxt rule xs As th
  handle e => Exn.reraise (@{print} e)
fun obtain_export ctxt rule xs _ As = (eliminate_nusys ctxt rule xs As, I)

local
fun expand_exE ctxt th =
  (th RS @{thm exE}) |>
    Tactic.rule_by_tactic ctxt (REPEAT (Tactic.eresolve_tac ctxt [exE] 1))
fun match_vars ctxt ret [] [] [] = rev ret
  | match_vars ctxt ret insts' [] (x::insts) =
      error "unequalled length of instantiations and quantifiers"
  | match_vars ctxt ret insts' (quant::vars) [] =
      error ("quantifier "^(Syntax.string_of_term ctxt quant)^" is not been instantiated")
  | match_vars ctxt ret insts' (quant::vars) ((v,x)::insts) =
      if v = quant
      then match_vars ctxt (x::ret) [] vars (insts' @ insts)
      else match_vars ctxt ret ((v,x)::insts') (quant::vars) insts
fun trim_var_name name =
  if String.isSuffix "__" name
  then String.substring (name, 0, String.size name - 2)
  else name
val trim_var = dest_Free #> apfst trim_var_name #> Free
in


fun choose inst_names stat =
  let open NuBasics NuHelp HOLogic Term Conv
    val major = NuBasics.the_nu_fact stat
    val ctxt = Proof.context_of stat
    val N = length inst_names
    val ExTyp_strip = Proof_Context.get_thm ctxt "local.\<phi>ExTyp_strip"
    fun exBI_strip 0 = all_conv
      | exBI_strip N = rewr_conv ExTyp_strip then_conv binder_conv (K (exBI_strip (N-1))) ctxt
    val major = fconv_rule (arg_conv (exBI_strip N)) major
    val (vars,body) = Thm.prop_of major |> dest_Trueprop |> strip_binder_raw "HOL.Ex"
    val var_tys = map snd vars
    val (inst_names, stat) =
          Proof.map_context_result (Proof_Context.add_fixes
            (map (fn (ty,nam) => (nam, SOME ty, NoSyn)) (var_tys~~inst_names))
          ) stat
    val insts = map Free (inst_names ~~ var_tys)
    val ctxt = Proof.context_of stat
    val meta'_term = mk_Trueprop (subst_bounds (rev insts, body))
                        |> Thm.cterm_of ctxt
    val meta' = Thm.assume  meta'_term
    val rule = expand_exE ctxt major
    val cinsts = map (Thm.cterm_of ctxt) insts;
  in
    stat |> Proof.map_context
              (Assumption.add_assms (obtain_export ctxt rule cinsts) [meta'_term] #> snd)
         |> NuBasics.set_nu_fact meta'
  end


fun auto_choose stat =
  let
    val var_names = PhiSyntax.dest_current_nu (NuBasics.the_nu_fact stat)
          |> NuHelp.strip_binder_vars @{const_name ExSet}
          |> map (Name.clean o fst)
    val (var_names', _) =
      fold_map Name.variant var_names (Variable.names_of (Proof.context_of stat))
(* Binding.name o  *)
    val _ = tracing ("Automatically fixing existential variable(s) "
                     ^ String.concatWith ", " var_names'
                     ^ ". You may want to disable automatic behavior by '!!', "
                     ^ "or use '\<exists> <names>' to fix them by explicit names.")
  in
    choose (map Binding.name var_names') stat
  end

end
end

