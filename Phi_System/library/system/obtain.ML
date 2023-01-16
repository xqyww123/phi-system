(* FILE: library/system/obtain.ML
   AUTHOR: Qiyuan Xu

   Existential elimination in the IDE-CP.
*)

signature NU_OBTAIN = sig
  val choose : binding list -> Proof.state -> Proof.state
  val auto_choose : Proof.state -> Proof.state
  val enable_auto : bool Config.T
end

structure NuObtain : NU_OBTAIN = struct

fun eliminate_term ctxt xs thm =
  let open Phi_Envir Phi_Syntax Phi_Help
    val tm = Thm.prop_of thm
    val mode = Phi_Working_Mode.working_mode_on1 ctxt tm
    val vs = map (dest_Free o Thm.term_of) xs;
    fun collect vs tm = Term.fold_aterms (fn t as Free v =>
                        if member (op =) vs v then insert (op =) v else I | _ => I) tm []
    val bads = collect vs tm
  in #introduce_existence mode bads (ctxt, thm) |> snd
  end

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
  let open Phi_Envir Phi_Help HOLogic Term Conv
    val major = Phi_Envir.the_state_sequent stat
    val ctxt = Proof.context_of stat
    val N = length inst_names
    val ExTyp_strip = @{thms \<phi>ExTyp_strip \<phi>ExTyp_strip_imp}
    fun exBI_strip 0 _ = all_conv
      | exBI_strip 1 _ = rewrs_conv ExTyp_strip
      | exBI_strip N ctxt = rewrs_conv ExTyp_strip
                  then_conv binder_conv (exBI_strip (N-1) o snd) ctxt
    val major = fconv_rule (arg_conv (exBI_strip N ctxt)) major
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
         |> Phi_Envir.set_state_sequent meta'
  end

val enable_auto = Attrib.setup_config_bool \<^binding>\<open>\<phi>auto_\<exists>fix\<close> (K true)

fun auto_choose stat =
  let
    val ctxt = Proof.context_of stat
    val sequent = Phi_Envir.the_state_sequent stat
    val mode = Phi_Working_Mode.working_mode_on1 ctxt (Thm.concl_of sequent)
    val var_names = #spec_of mode (Thm.concl_of sequent)
          |> Phi_Help.strip_binder_vars @{const_name ExSet}
          |> map (Name.clean o fst)
    val (var_names', _) =
      fold_map Name.variant var_names (Variable.names_of (Proof.context_of stat))
(* Binding.name o  *)
    val _ = tracing ("Automatically fixing existential variable(s) \<open>"
             ^ String.concatWith ", " var_names'
             ^ "\<close>.\nYou may want to disable automatic behavior temporarily by '!!', \
               \or use '\<exists> <names>' to fix them by explicit names.\n\
               \If it bothers you, you may disable the feature permanently by setting \
               \\<phi>auto_\<exists>fix to false, like \<open>note [[\<phi>auto_\<exists>fix = false]]\<close>.")
  in
    choose (map Binding.name var_names') stat
  end

end
end

