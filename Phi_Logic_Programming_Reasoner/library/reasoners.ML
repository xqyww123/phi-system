signature PHI_REASONERS = sig

  include PHI_REASONERS

  exception Automation_Fail of (Proof.context * thm) option
  val error_message : (Proof.context * thm) option -> string

  type contraction_mode = bool * bool * int
  (*contraction_mode = (collect_premises, conv_all, conv_schematic)

    collect_premises: if collect premises into the reported proof oblgiation
    conv_all: if convert all meta-all into hol-all inside the reported obligation
    conv_schematic: if replace feasible schematic variables by existential quantified variables.
      0: do not generate existence in obligations, leaving them schematic variables
      1: generate existence in obligations
      2: generate existence in obligations and apply a special patch on them to enhance the automation
         of Isabelle for solving them (using introduction rules)
      ~1: take \<open>Config.get existential_obligation\<close>
  *)
  val collect_obligation_premises : contraction_mode -> Proof.context -> thm -> thm

  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
  val wrap': (Proof.context -> thm -> thm option) -> (context_state -> context_state option)
  val wrap'': (Proof.context -> thm -> thm) -> (context_state -> context_state)

  val auto_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val auto_obligation_solver' : (Proof.context -> thm -> thm) (*failure callback*)
                              -> Proof.context -> thm -> thm
  val auto_obligation_solver1 : Proof.context -> thm -> thm

  val safer_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val safer_obligation_solver': (Proof.context -> thm -> thm) (*failure callback*)
                              -> Proof.context -> thm -> thm
  val safer_obligation_solver1: Proof.context -> thm -> thm


  (*defer the leading antecedent to the nearest obligation and call the contract*)
  val defer_antecedent : (Proof.context -> thm -> thm) (*contract*)
                                 -> Proof.context -> thm -> thm Seq.seq
  val defer_obligation_tac : contraction_mode -> Proof.context -> thm -> thm Seq.seq
  val has_obligations_tag : thm -> bool

  structure Tactic_Configures : HOOKS (*You can alter auxiliary facts, tactics, and configure the
      context before applying either the automatic solving*)

  (* Premise Extraction from arbitrary antecedent *)
  type pattern = term
  val extract_prem  : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm option
  val extract_prems : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm list
  val extract_prems_rewr : Context.generic (*the context used to fetch the extractions*)
                        -> Proof.context -> cterm -> thm option option
  val is_syntactic_premise : term -> bool

  (* Simplifications that uses the extracted premises.
     The boolean: use_origin. if not use_origin, drops the original premises
     and only remains the extracted premises.*)
  val asm_simplify : bool -> Proof.context -> thm -> thm
  val asm_lr_simplify : bool -> Proof.context -> thm -> thm
  val asm_simp_tac : bool -> Proof.context -> int -> tactic
  val asm_lr_simp_tac : bool -> Proof.context -> int -> tactic
  val asm_rewrite : bool -> Proof.context -> conv
  val asm_lr_rewrite : bool -> Proof.context -> conv

  (*structure Is_Premise_of_Obligation : HANDLERS
      (*Tell me what antecedents are considered premise of a proof obligation to be reported,
        and what are not so that to be ignored.*)*)
  (*val is_premise_of_obligation : (*Context.generic ->*) term -> bool*)

  (*structure Local_Premises_of_Obligation : NAMED_THMS
      (*You can add any facts to be reported as premises of a proof obligation*)*)

end


structure Phi_Reasoners : PHI_REASONERS = struct
open Thm Term Phi_Reasoners

(** Preliminary **)

exception Automation_Fail of (Proof.context * thm) option

fun error_message err =
      Pretty.string_of (Pretty.chunks (
        Pretty.str "Fail to solve the proof obligation automatically" ::
        (case err of SOME (ctxt, sequent) =>
            (case Thm.prems_of sequent
               of (x::_)
                    => [Syntax.pretty_term ctxt x]
                | _ => [])
                   | NONE => [])
      ))



fun wrap tac (ctxt,thm) = tac ctxt thm |> Seq.map (pair ctxt)
fun wrap' tac (ctxt,thm) = tac ctxt thm |> Option.map (pair ctxt)
fun wrap'' tac (ctxt,thm) = tac ctxt thm |> pair ctxt

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty))) *)

val aux_thms = Useful_Thms.get


(* Simple Simplification of Obligations Before Exporting *)
(*to see if it can be reduced to some trivial form like \<open>A = ?x\<close>*)

val conv_LRHS_heads = [\<^const_name>\<open>id\<close>, \<^const_name>\<open>fst\<close>, \<^const_name>\<open>snd\<close>]
fun conv_LRHS ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>id\<close>, _) $ _ =>
          Conv.rewr_conv @{thm' Fun.id_apply[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>fst\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' Product_Type.fst_conv[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>snd\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' Product_Type.snd_conv[folded atomize_eq]} ctm
     | _ => raise CTERM ("conv_LRHS", [ctm])

fun need_conv_LRHS tm =
  case Term.head_of tm of Const(N, _) => member (op =) conv_LRHS_heads N
                        | _ => false

fun simple_simp ctxt sequent =
  case PLPR_Syntax.dest_premise_tag (major_prem_of sequent)
    of (_, Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y) =>
         if need_conv_LRHS X orelse need_conv_LRHS Y
         then Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn _ =>
                 Conv.arg_conv (Conv.arg_conv (
                      HOLogic.eq_conv (Conv.repeat_conv conv_LRHS) (Conv.repeat_conv conv_LRHS)))
                 ) ctxt
              ) 1 sequent
         else sequent
     | _ => sequent


(*** Tactics ***)

(** Tactic Configures **)
(*depreciate?*)

datatype solver_mode = Agressive_Solver (*the auto method*) | Safe_Solver (*by clarsimp*)

structure Tactic_Configures = Hooks (
  type arg = solver_mode
  type state = thm list (*aux thms*) * tactic * Proof.context
)

fun apply ctxt tactic  mode =
  HEADGOAL (SOLVED' (K
    (#2 (Tactic_Configures.invoke_until_success (Context.Proof ctxt)
          (fn mode => fn (aux,tac,ctxt) =>
              ([], tactic (ctxt,tac,aux,mode), ctxt)) mode (aux_thms ctxt, all_tac, ctxt)))))

(** Tactic Template **)

structure Very_Safe_Oblg_Simp_SS = Simpset(
  val initial_ss = Simpset_Configure.Minimal_SS_configure (fn ctxt =>
                      ctxt addsimps @{thms' HOL.simp_thms})
  val binding = NONE
  val attribute = NONE
  val comment = "Very safe rewrite rules normalizing proof obligations"
  val post_merging = I
)

fun oblg_template f ctxt th00 = Seq.make (fn () =>
  let val th01 = case PLPR_Syntax.dest_premise_tag_opt (major_prem_of th00)
                   of SOME _ => th00
                    | NONE => @{thm' Premise_D[where mode=default]} RS th00
      val th = simple_simp ctxt (Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                  HOLogic.Trueprop_conv (Conv.arg_conv (
                    Simplifier.rewrite (Very_Safe_Oblg_Simp_SS.equip ctxt)))
               ) ctxt) 1 th01)
   in case PLPR_Syntax.dest_premise_tag (major_prem_of th)
        of (_, Const (\<^const_name>\<open>True\<close>, _)) =>
                SOME (@{thm Premise_True} RS th, Seq.empty)
         | (_, Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ B) =>
              if is_Var (Term.head_of A) orelse is_Var (Term.head_of B)
              then SOME (@{thm Premise_refl} RS th, Seq.empty)
              else f ctxt th
         | _ => f ctxt th
  end)


(*** Auxiliaries ***)

(*protects the remaining goals and only attack the first one*)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude

(*Wrap a context tactic of type `Proof.context -> thm -> thm Seq.seq` to the
  transition between states, of type `Proof.context * thm -> Proof.context * thm`.
  *This wrap only adopts the first result of applying the tactic, and drops other alternatives.*
  The original seq-based tactics are not affected by this.

  Because reasoners in the file only attack the first antecedent and solves it totally or fails,
  this short-cut makes differences only when the antecedent to be solved has some schematic variables
  to be instantiated during the tactic application.

  The semantics of schematic variables in auto_obligation_solver and safer_obligation_solver is,
  any possible instantiation is acceptable.

  If the schematic variables are not able to be chosen arbitrarily, additional mechanisms have
  to be applied previously.*)
fun context_tactic_to_state_transition tac fail ctxt sequent =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => th'
     | NONE => fail ctxt sequent

(*fun context_tactic_to_state_transition_opt tac (ctxt, sequent) =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => SOME (ctxt, th')
     | NONE => NONE *)

(*** Obligation Extraction ***)

(** Premise Extraction **)

(*Given any antecedent, if we can extract abstract pure facts that can help to solve the target
  proof obligation?*)
(*Convention: the rule of premise extraction has form \<open>A \<equiv> Premise \<and> A\<close>*)
type pattern = term

fun is_syntactic_premise (Const(\<^const_name>\<open>Premise\<close>, _) $ M $ _) = is_syntactic_premise M
  | is_syntactic_premise (Const(\<^const_name>\<open>default\<close>, _)) = true
  | is_syntactic_premise (Const(\<^const_name>\<open>MODE_SIMP\<close>, _)) = true
  | is_syntactic_premise (Const(\<^const_name>\<open>MODE_COLLECT\<close>, _)) = true
  | is_syntactic_premise (Abs (_,_,X)) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise _ = false

fun gen_extract_prems_rewr ctxt =
  let val thy = Context.theory_of ctxt
      val reasoners = Phi_Reasoner.reasoners ctxt
      fun quick_check ctm =
        let val idx = Thm.maxidx_of_cterm ctm + 1
            fun has_extraction_obj tm =
                  exists (fn (prio, _, _, _) => prio > 9)
                    (Phi_Reasoner.get_reasoners' thy reasoners
                        (\<^Const>\<open>Extract_Premise\<close> $ (HOLogic.Trueprop $ tm) $ Var(("_", idx), TVar(("_", idx), []))))
      
            fun qchk_obj (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) =
                  qchk_obj A orelse qchk_obj B
              | qchk_obj (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ A $ B) =
                  qchk_obj A orelse qchk_obj B
              | qchk_obj (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = qchk_obj X
              | qchk_obj (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, _, X)) = qchk_obj X
              | qchk_obj (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = qchk_obj (Term.incr_boundvars 1 X $ Bound 0)
              | qchk_obj tm = has_extraction_obj tm
      
            fun check (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = check X
              | check (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = check X
              | check (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = check (Term.incr_boundvars 1 X $ Bound 0)
              | check (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = qchk_obj X
              | check _ = false
         in check (Thm.term_of ctm)
        end

      fun extract' ctxt ctm =
        let val vP = Thm.var (("P", 0), \<^ctyp>\<open>bool\<close>)
            val is_prop = case Thm.typ_of_cterm ctm
                            of Type(\<^type_name>\<open>prop\<close>, _) => true
                             | Type(\<^type_name>\<open>bool\<close>, _) => false
                             | _ => raise CTERM ("extract_prems_rewr: must be a prop or a boolean", [ctm])
            val ((_, [ctm'embedded]), ctxt') = Variable.import false [Drule.mk_term ctm] ctxt
            val ctm't = Drule.dest_term ctm'embedded
            val ctm' = if is_prop then ctm't else Thm.apply \<^cterm>\<open>Trueprop\<close> ctm't
         in Thm.apply (Thm.apply \<^cterm>\<open>Extract_Premise\<close> ctm') vP
         |> Goal.init
         |> Phi_Reasoner.reason NONE NONE ctxt
         |> Option.map (fn th =>
              (Goal.conclude th RS
                (if is_prop then @{lemma \<open>PROP Extract_Premise P Q \<Longrightarrow> PROP P \<equiv> (Q &&& PROP P)\<close>
                                      by (unfold Extract_Premise_def, (rule, rule conjunctionI),
                                          simp, simp, simp add: conjunction_imp)}
                            else @{lemma \<open>PROP Extract_Premise (Trueprop P) Q \<Longrightarrow> P \<equiv> (Q \<and> P)\<close>
                                      by (unfold Extract_Premise_def atomize_eq, blast)}))
              |> singleton (Variable.export ctxt' ctxt))
        end

   in (quick_check,
   fn ctxt => fn ctm =>
   if is_syntactic_premise (Thm.term_of ctm)
   then SOME NONE
   else if quick_check ctm
   then Option.map SOME (extract' ctxt ctm)
   else NONE)
  end

fun extract_prems_rewr ctxt = snd (gen_extract_prems_rewr ctxt)

fun extract_prem ctxt strip =
  let val ctxt' = Context.proof_of ctxt
      val (qchk, conv) = gen_extract_prems_rewr ctxt
   in fn thm =>
   if is_syntactic_premise (Thm.prop_of thm)
   then SOME (if strip
              then (Raw_Simplifier.norm_hhf ctxt' thm) RS' (ctxt', @{thm' Premise_D})
              else thm)
   else if qchk (Thm.cprop_of thm)
        then let val thm = Raw_Simplifier.norm_hhf ctxt' thm
              in (case conv ctxt' (Thm.cprop_of thm)
                    of SOME NONE => SOME (if strip
                                          then thm RS' (ctxt', @{thm' Premise_D})
                                          else thm)
                     | SOME (SOME rule) => SOME (
                         (fst (Conjunction.elim (Conv.fconv_rule (Conv.rewr_conv rule) thm)))
                           |> not strip ? (fn th => th RS' (ctxt', @{thm' Premise_I[where mode=MODE_SIMP]})))
                     | NONE => NONE)
             end
   else NONE
  end

fun extract_prems ctxt strip thm =
  let fun simp th =
        case Thm.concl_of th
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =>
                simp (Conv.fconv_rule (Conv.rewr_conv @{thm' atomize_all[symmetric]}) th)
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                simp (Thm.forall_elim_var (Thm.maxidx_of th) th)
           | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
                maps simp (PLPR_Syntax.elim_ant_sequence_or_HOL_conj th)
           | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _) =>
                maps simp (PLPR_Syntax.elim_ant_sequence_or_HOL_conj th)
           | _ => [th]
   in the_default [] (Option.map simp (extract_prem ctxt strip thm))
  end


(*structure Is_Premise_of_Obligation = Handlers ( type arg = term; type ret = bool )
structure Local_Premises_of_Obligation = Named_Thms (
  val name = \<^binding>\<open>__local_premise_of_obligation__\<close>
  val description = "Facts inside will be added as premises into proof obligations"
)*)

(*
fun is_premise_of_obligation ctxt =
  let val ivk = Is_Premise_of_Obligation.invoke ctxt
      fun default (Const(\<^const_name>\<open>Premise\<close>, _) $ M $ _) = default M
        | default (Const(\<^const_name>\<open>default\<close>, _)) = true
        | default (Const(\<^const_name>\<open>MODE_SIMP\<close>, _)) = true
        | default (Abs (_,_,X)) = default X
        | default (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = default X
        | default (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = default X
        | default (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = default X
        | default (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = default X
        | default (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = default X
        | default _ = false
   in fn tm => case ivk tm
    of SOME ret => ret
     | NONE => default tm
  end
*)

(** Applications of the Premise Extraction **)


(* if not use_origin, drops the original premises and only remains the extracted premises. *)
fun gen_simplify simp use_origin ctxt =
  let val extract = extract_prems (Context.Proof ctxt) true
      val extract' = if use_origin then (fn th => th :: extract th)
                     else extract
      val sctxt = Simplifier.set_mksimps (fn ctxt =>
                      maps (Simpdata.mksimps Simpdata.mksimps_pairs ctxt)
                    o extract') ctxt
   in simp sctxt
  end

val asm_simplify = gen_simplify Simplifier.asm_simplify
val asm_lr_simplify = gen_simplify Simplifier.asm_lr_simplify
val asm_simp_tac = gen_simplify Simplifier.asm_simp_tac
val asm_lr_simp_tac = gen_simplify Simplifier.asm_lr_simp_tac
val asm_rewrite = gen_simplify Simplifier.asm_rewrite
val asm_lr_rewrite = gen_simplify Simplifier.asm_lr_rewrite

(** Obligation Extraction **)

val contract_premise_imp =
    @{lemma \<open>(P \<Longrightarrow> PROP Waste \<Longrightarrow> Premise mode G) \<equiv> (PROP Waste \<Longrightarrow> Premise mode (P \<longrightarrow> G))\<close>
            by (rule, (simp add: Premise_def)+)}
val contract_premise_imp' =
    @{lemma \<open>(P &&& PROP A \<Longrightarrow> PROP Waste \<Longrightarrow> Premise mode G) \<equiv> (PROP A &&& PROP Waste \<Longrightarrow> Premise mode (P \<longrightarrow> G))\<close>
            by (rule, (simp add: Premise_def conjunction_imp)+)}

(*the term must be beta-eta normalized*)
fun obligation_collect ctxt filter =
  let fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
                Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _
               =>(case filter ctxt (Thm.dest_arg1 ctm)
                    of SOME NONE => (*A normal premises using the normal rule*)
                         (Conv.implies_conv
                            (Phi_Conv.atomize_conv ctxt then_conv
                             Raw_Simplifier.rewrite ctxt true @{thms' Premise_def[where mode=default]
                                                                      Premise_def[where mode=MODE_SIMP]})
                            conv then_conv
                          Conv.rewr_conv contract_premise_imp) ctm
                     | SOME (SOME rule) => (*Not a direct premise but still has something can be extracted
                                             so we apply the given rule to extract*)
                         (Conv.implies_conv (Conv.rewr_conv rule) conv then_conv
                          Conv.rewr_conv contract_premise_imp') ctm
                     | NONE => (*Just waste*)
                         (Conv.arg_conv conv then_conv
                          Conv.rewr_conv @{thm' conjunction_imp[symmetric]}) ctm)
           | _ => raise CTERM ("unexpected proof obligation form", [ctm])
   in conv
  end

(* REMOVE THIS WHEN NO BUG
fun obligation_collect ctxt filter ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
    case Thm.term_of ctm
      of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
            Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
       | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ Pr $ _
           => if filter Pr
              then (Conv.implies_conv
                      (Phi_Conv.atomize_conv ctxt then_conv
                       Raw_Simplifier.rewrite ctxt true @{thms' Premise_def[where mode=default]
                                                                Premise_def[where mode=MODE_SIMP]})
                      (obligation_collect ctxt filter) then_conv
                    Conv.rewr_conv @{thm' contract_premise_imp}) ctm
              else (Conv.arg_conv (obligation_collect ctxt filter) then_conv
                    Conv.rewr_conv @{thm' conjunction_imp[symmetric]}) ctm
       | _ => raise CTERM ("unexpected proof obligation form", [ctm])
  ) ctm
*)

fun obligation_conv_all ctxt ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
        (Phi_Conv.meta_all_conv (obligation_conv_all o snd) ctxt then_conv
          Conv.rewr_conv @{thm contract_premise_all}) ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
          Conv.all_conv ctm
     | _ => raise CTERM ("internal bug 6733574a-42dc-4592-a08e-ddc223bb6b94", [ctm])
  ) ctm

fun obligation_intro_Ex_conv conv_schematic ctxt thm0 =
  let val thm = Phi_Help.beta_eta_contract thm0
             |> (fn th => if null (Thm.tpairs_of th) then th
                          else case Seq.chop 2 (Thm.flexflex_rule (SOME ctxt) th)
                                 of ([th'], _) => th'
                                  | _ => th (*fails to solving flex-flex*))
      fun dest' (\<^Const>\<open>Pure.imp\<close> $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (
                      Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ P)) $ Q) = (P,Q)
        | dest' tm = raise TERM ("obligation_intro_Ex", [tm])
      fun dest ctm = dest' (Thm.term_of ctm)
      (*fun dest_c ctm =
            (dest ctm; (Thm.dest_arg (Thm.dest_arg1 ctm), Thm.dest_arg ctm))*)

      val (P,Q) = dest (Thm.cprop_of thm)
      val vars = Term.add_vars Q []
              |> fold (fn (A,B) => Term.add_vars A o Term.add_vars B) (Thm.tpairs_of thm)
      fun collect_var ret (Var v) = if member (op =) vars v then ret
                                    else insert (op =) v ret
        | collect_var ret (A $ B) = collect_var (collect_var ret A) B
        | collect_var ret (Abs(_,_,X)) = collect_var ret X
        | collect_var ret _ = ret
      val vars' = collect_var [] P
                |> map (fn (N,T) => Thm.var (N, Thm.ctyp_of ctxt T))
      val mode = conv_schematic = 2
      val contract_Ex_rule = if mode then @{thm' contract_intro_sp_Ex}
                                     else @{thm' contract_intro_Ex}
   (* val mv_Ex_All = if mode then Phi_Conv.move_sp_Ex_inside_All_recursive
                              else Phi_Conv.move_Ex_inside_All_recursive
      val mv_Ex_Disj = if mode then Phi_Conv.move_sp_Ex_downto_Disj_recursive
                               else Phi_Conv.move_Ex_downto_Disj_recursive *)
      fun intro_Ex v thm =
            Conv.fconv_rule (
                Conv.rewr_conv contract_Ex_rule then_conv (
                if mode
                then Phi_Conv.leading_antecedent_conv (
                    PLPR_Syntax.premise_tag_conv (
                      (fn ctm => Phi_Conv.move_sp_Ex_inside (K Conv.all_conv) ctxt ctm)
                      (*mv_Ex_All (fn _ => mv_Ex_Disj Conv.all_conv) ctxt*) )
                  )
                else Conv.all_conv)
            ) (Thm.forall_intr v thm)
   in fold intro_Ex vars' thm
  end

type contraction_mode = bool * bool * int
fun chk_option ctxt (a,b,~1) = (a,b,Config.get ctxt existential_obligation)
  | chk_option _ option = option

(*the leading antecedent must be beta-eta normalized*)
fun collect_obligation_premises option ctxt thm = let open Conv
  val (collect_premises,conv_all,conv_schematic) = chk_option ctxt option
  val filter = extract_prems_rewr (Context.Proof ctxt)
  val rule1 = gconv_rule (Phi_Conv.meta_alls_conv (fn ctxt => 
                (if collect_premises then obligation_collect ctxt filter
                                     else Conv.all_conv) then_conv
                rewr_conv @{thm Pure.prop_def[symmetric]}) ctxt
              ) 1 thm

  (*val rule2 = if collect_premises
              then case Local_Premises_of_Obligation.get ctxt
                of [] => rule1
                 | L => let val fact = map (Conv.fconv_rule (Object_Logic.atomize ctxt)) L
                                    |> foldl1 (uncurry (HOLogic.conj_intr ctxt))
                         in fact RS (@{thm' contract_add_additional_prems} RS rule1)
                        end
              else rule1*)

  fun drop_wastes thm =
    case Thm.major_prem_of thm
      of Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X => (
          case X of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _
                      => drop_wastes (@{thm' contract_drop_waste} RS thm)
                  | _ => @{thm' contract_drop_waste_end} RS thm)
       | _ => error "BUG nhtCAsmjS+Oj4YsI8qtXQw"

   in drop_wastes rule1
   |> conv_all ? gconv_rule (obligation_conv_all ctxt) 1
   |> conv_schematic > 0 ? obligation_intro_Ex_conv conv_schematic ctxt
  end

(*Config.get ctxt existential_obligation*)

(*the leading antecedent must be beta-eta normalized*)
fun contract_obligations mode ctxt thm = thm
    |> collect_obligation_premises mode ctxt
    |> Conv.fconv_rule (Conv.rewr_conv @{thm contract_obligations})

fun find_obligations_tag thm = tl (Thm.prems_of thm)
      |> find_index (fn tm =>
            case tm of (_ $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _)) => true
                     | _ => false)
fun has_obligations_tag thm = find_obligations_tag thm <> ~1

fun defer_antecedent contract = oblg_template (fn ctxt => fn thm =>
  let val idx = find_obligations_tag thm
  in if idx = ~1
     then error ("Fail to defer a proof obligation: an \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> antecedent is not found.")
     else Thm.permute_prems 1 idx thm
      |> contract ctxt
      |> Thm.permute_prems 0 (~idx)
      |> (fn X => SOME (X, Seq.empty))
  end)

val defer_obligation_tac = defer_antecedent o contract_obligations

(*** Premise tac ***)

(*fun intro_all_leading_ex i thm =
  if i > Thm.nprems_of thm
  then thm
  else case Logic.concl_of_goal (Thm.prop_of thm) i
         of _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
              intro_all_leading_ex i (@{thm' conjI} RSN (i, thm))
          | _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ _ ) =>
              intro_all_leading_ex i (@{thm' exI} RSN (i, thm))
          | _ => intro_all_leading_ex (i+1) thm*)

(*Attack antecedents @{term "Premise mode P"} using the classical auto tactic.
It is the default tactic in the system intended to solve simple proof obligations.*)
val auto_obligation_solver = oblg_template (fn ctxt => fn th =>
      head_only (apply ctxt (fn (ctxt,pre,aux,_) =>
          pre THEN HEADGOAL (Method.insert_tac ctxt aux)
              THEN Clasimp.auto_tac ctxt) Agressive_Solver)
                (@{thm' Premise_I} RS th)
       |> Seq.pull)

val auto_obligation_solver' = context_tactic_to_state_transition auto_obligation_solver

fun auto_obligation_solver1 ctxt sequent =  (
        Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>auto\<close> method...",
            Syntax.pretty_term ctxt (Thm.major_prem_of sequent),
            Pretty.block (Pretty.here \<^here>)
        ]);
        auto_obligation_solver' (fn _ =>
          raise Automation_Fail (SOME (ctxt,sequent))
          (*error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt Goal
            ])) *)
        ) ctxt sequent
     )


(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
val safer_obligation_solver = oblg_template (fn ctxt => fn th =>
      let val th'1 = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
          val th' = @{thm' Premise_I} RS th'1
       in apply ctxt (fn (ctxt,pre,aux,_) =>
             pre THEN HEADGOAL (fn s => fn x => Clasimp.clarsimp_tac (ctxt addsimps aux) s x)) Safe_Solver th'
       |> Seq.pull
      end)

val safer_obligation_solver' = context_tactic_to_state_transition safer_obligation_solver

fun safer_obligation_solver1 ctxt sequent =
  safer_obligation_solver' (fn _ =>
    error (Pretty.string_of (Pretty.chunks [
        Pretty.str "Fail to solve the proof obligation automatically:",
        Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
  ]))) (ctxt addsimps @{thms Premise_def}) sequent
(*case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ Goal) => (
        (*Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>clarsimp\<close> method...",
            Syntax.pretty_term ctxt Goal,
            Pretty.block (Pretty.here \<^here>)
        ]); *)
        safer_obligation_solver' (fn _ =>
          error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
        ]))) (ctxt addsimps @{thms Premise_def}) sequent
     )
     | _ => raise THM ("auto_obligation_solver1: The leading antecedent of the given sequent \
              \is not a proof obligation.", 1, [sequent])*)



(*fun declare_local_assume_reasoners sequent i *)

end
