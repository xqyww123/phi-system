signature PHI_REASONERS = sig

  include PHI_REASONERS

  type schm_by_ex = int
  (*whether to replace schematic variables by existential quantified variables if feasible.
      0: do not generate existence in obligations, leaving them schematic variables, so this feature
         is disabled at all.
      1: generate existences in obligations, which are given at the beginning the obligations.
      2: generate existences in obligations and try to push them over (\<longrightarrow>, \<and>) to the bottom.
         This pushing is done by the mechanism of special existences (\<exists>\<^sup>\<phi>\<^sup>-\<^sup>L\<^sup>P\<^sup>R).
      ~1: take \<open>Config.get existential_obligation\<close> *)

  type contraction_mode = bool * bool * schm_by_ex
  (*contraction_mode = (collect_premises, conv_all, schm_by_ex)

    collect_premises: whether to collect premises into the reported proof oblgiation
    conv_all: whether to convert all meta-all into hol-all inside the reported obligation *)

  val collect_obligation_premises : contraction_mode -> Proof.context -> thm
                                 -> int (*number of new conditions introduced*) * thm
  val obligation_intro_Ex_conv : schm_by_ex -> Proof.context -> thm -> thm

  val auto_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val auto_obligation_solver' : (Proof.context -> thm -> thm) (*failure callback*)
                              -> Proof.context -> thm -> thm
  val auto_obligation_solver1 : Proof.context -> thm -> thm

  val guard_condition_solver : {can_inst: bool} -> Proof.context -> thm -> thm Seq.seq
      (*The annotation of \<open>case_split\<close> is supported*)
  val guard_condition_solver': {can_inst: bool}
                             -> (Proof.context -> thm -> thm) (*failure callback*)
                             -> Proof.context -> thm -> thm
  val guard_condition_solver1: {can_inst: bool} -> Proof.context -> thm -> thm

  val safe_obligation_solver : {can_inst: bool} -> Proof.context -> thm -> thm Seq.seq
      (*The annotation of \<open>case_split\<close> is supported*)
  val safe_obligation_solver': {can_inst: bool}
                             -> (Proof.context -> thm -> thm) (*failure callback*)
                             -> Proof.context -> thm -> thm
  val safe_obligation_solver1: {can_inst: bool} -> Proof.context -> thm -> thm


  (*defer the leading antecedent to the nearest obligation and call the contract*)
  val defer_obligation : {can_inst:bool, fix_level:int}
                      -> (Proof.context -> thm -> thm) (*contract*)
                      -> Proof.context -> thm -> thm Seq.seq
  val defer_obligation_tac : {can_inst:bool, fix_level:int}
                          -> contraction_mode
                          -> Proof.context -> thm -> thm Seq.seq
  val augment_conditions : thm list -> Proof.context -> thm -> thm
        (*augmenting conditions to the leading proof obligations*)
  val has_obligations_tag : thm -> bool


  structure Tactic_Configures : HOOKS (*You can alter auxiliary facts, tactics, and configure the
      context before applying either the automatic solving*)

(*  val extract_prem  : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm option
  val extract_prems : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm list
  val extract_prems_rewr : Proof.context -> cterm -> thm option option*)
  val is_syntactic_premise : term -> bool

  (*(* Simplifications that uses the extracted premises.
     The boolean: use_origin. if not use_origin, drops the original premises
     and only remains the extracted premises.*)*)
  val asm_simplify : bool -> Proof.context -> thm -> thm
  val asm_lr_simplify : bool -> Proof.context -> thm -> thm
  val full_simplify : bool -> Proof.context -> thm -> thm
  val asm_simp_tac : bool -> Proof.context -> int -> tactic
  val asm_lr_simp_tac : bool -> Proof.context -> int -> tactic
  val asm_rewrite : bool -> Proof.context -> conv
  val asm_lr_rewrite : bool -> Proof.context -> conv
  val asm_full_rewrite : bool -> Proof.context -> conv

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


(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty))) *)

val aux_thms = Useful_Thms.get


(* Simple Simplification of Obligations Before Exporting *)
(*to see if it can be reduced to some trivial form like \<open>A = ?x\<close>*)

(*
val conv_LRHS_heads = [\<^const_name>\<open>id\<close>, \<^const_name>\<open>fst\<close>, \<^const_name>\<open>snd\<close>]
fun conv_LRHS ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>id\<close>, _) $ _ =>
          Conv.rewr_conv @{thm' Fun.id_apply[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>fst\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' Product_Type.fst_conv[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>snd\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' Product_Type.snd_conv[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' prod.case[folded atomize_eq]} ctm
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
*)

(*** Tactics ***)

(** Tactic Configures **)
(*depreciate?*)

datatype solver_mode = Agressive_Solver (*the auto method*) | Safe_Solver (*by clarsimp*)

structure Tactic_Configures = Hooks (
  type arg = solver_mode
  type state = thm list (*aux thms*) * tactic * Proof.context
)

fun apply_tac ctxt tactic mode =
  HEADGOAL (SOLVED' (fn i => fn th =>
    let val tac = #2 (Tactic_Configures.invoke_until_success (Context.Proof ctxt)
          (fn mode => fn (aux,tac,ctxt) =>
              ([], tactic (ctxt,tac,aux,mode), ctxt)) mode (aux_thms ctxt, all_tac, ctxt))
     in tac th
    end ))

(*
(** Tactic Template **)

structure Very_Safe_Oblg_Simp_SS = Simpset(
  val initial_ss = Simpset_Configure.Minimal_SS_configure (fn ctxt =>
                      ctxt addsimps @{thms' HOL.simp_thms})
  val binding = NONE
  val attribute = NONE
  val comment = "Very safe rewrite rules normalizing proof obligations"
  val post_merging = I
)*)

(** Annot of Fixing **)

fun annot_of_fixing ret (Const(\<^const_name>\<open>LPR_ctrl\<close>, _) $ X) = Term.add_vars X ret
  | annot_of_fixing ret (A $ B) = annot_of_fixing (annot_of_fixing ret A) B
  | annot_of_fixing ret (Abs (_,_,X)) = annot_of_fixing ret X
  | annot_of_fixing ret _ = ret

(*Eliminating unknown variables as early as possible is essential for the performance of solving
proof obligations. It seems that Isabelle is not very good at eliminating existentially quantified
variables (to which unknown variables will be instantiate) and fails sometimes even for naive instantiation.
Therefore, we use sophisticated instantiation strategy here involving different levels of
computational complexity to instantiate them as early as possible.*)

fun mk_boolean_inst (Var v) b ret = Vars.add (v, if b then Phi_Help.True else Phi_Help.False) ret
  | mk_boolean_inst (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) b ret
      = mk_boolean_inst B b (mk_boolean_inst A b ret)
  | mk_boolean_inst (Const(\<^const_name>\<open>HOL.Not\<close>, _) $ A) b ret
      = mk_boolean_inst A (not b) ret
  | mk_boolean_inst (Const(\<^const_name>\<open>id\<close>, _) $ X) b ret
      = mk_boolean_inst X b ret
  | mk_boolean_inst _ _ _ = raise Match

(*it is unsafe to instantiate any functional unknown variable because you don't know how
  the function would be and it may be even not unique. For example, \<open>?x a b = True\<close>, you
  may think the instantiation would be \<open>\<lambda>_ _. True\<close> but it actually can also be \<open>\<lambda>a b. a = b\<close>
  when \<open>a = b\<close>.

  However, even if it is unsafe, it works in most of cases and our simplifier tactics are already
  unsafe. The unsafe instantiation is still acceptable once users can use tags to prevent aggressive
  instantiation.

  TODO: I don't know if we should re-enable IEUV but I believe the procedure of IEUV should be hard-coded
    in the fast_inst below.
*)

fun is_var' vars x =
  case Term.strip_comb x
    of (Var (v,_), args) => forall (fn Bound _ => true | _ => false) args andalso
                            not (member (op =) vars v)
     | _ => false

fun fast_inst can_inst th =
  let val vars = fold (Term.add_var_names) (Logic.strip_assums_hyp (hd (Thm.prems_of th))) []
   in case (can_inst, PLPR_Syntax.may_dest_premise_tag (major_prem_of th))
   of (_, Const (\<^const_name>\<open>True\<close>, _)) =>
            SOME (@{thm' Premise_True} RS th, Seq.empty)
     | (true, Const(\<^const_name>\<open>HOL.Not\<close>, _) $ X) =>
         (SOME (Thm.instantiate (TVars.empty, mk_boolean_inst (Phi_Help.beta_eta_contract_term X) false Vars.empty) th,
                Seq.empty)
          handle Match => NONE)
     | (true, Const(\<^const_name>\<open>HOL.conj\<close>, _)
                    $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y)
                    $ _) =>
         if is_var' vars X orelse is_var' vars Y
         then (SOME (@{lemma' \<open>Premise mode P \<Longrightarrow> Premise mode (x = x \<and> P)\<close>
                     by (simp add: Premise_def)} RS th, Seq.empty)
               handle THM _ => NONE)
         else NONE
     | (true, X as Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
         (SOME (Thm.instantiate (TVars.empty, mk_boolean_inst (Phi_Help.beta_eta_contract_term X) false Vars.empty) th,
                Seq.empty)
          handle Match => NONE)
     | (true, Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y) =>
         (*solves the equation by unification once single resolution*)
         (*TODO, BUG: ant \<open>fst (fst x, undefined) = fst ?x\<close> results in single unification \<open>x <- (fst x, undefined)\<close>*)
         if is_var' vars X orelse is_var' vars Y
         then (SOME (@{lemma' \<open>Premise mode (x = x)\<close> by (simp add: Premise_def)} RS th, Seq.empty)
               handle THM _ => NONE)
         else NONE
     | (true, X) =>
          if is_Var (Term.head_of X)
          then SOME (@{thm' Premise_True} RS th, Seq.empty)
          else NONE
     | _ => NONE
  end

(*slow but powerfull and flexible*)
fun LPR_inst ctxt th = ( (*TODO: strengthen fast_inst*)
  (*if Term.is_schematic (Thm.major_prem_of th)
  then (
    Phi_Reasoner.info_print ctxt 3 (fn () => "Phi_Reasoners.LPR_inst") ;
    Phi_Reasoner.reason NONE (SOME 1) ctxt
                        (@{lemma' \<open> \<g>\<u>\<a>\<r>\<d> IEUV Any False P P' \<and>\<^sub>\<r> Literal_Boolean Any
                                \<Longrightarrow> Premise mode P'
                                \<Longrightarrow> Premise mode P \<close>
                               by (simp add: IEUV_def \<r>Guard_def Ant_Seq_def)
                          } RS' (ctxt, th)) )
  else*) NONE
)

(*fix_level = 0 for no fix
            | 1 for fixing the conditions of the leading antecedent only but leaves variables
                    in the conclusion of the leading antecedent free
            | 2 for fixing variables in the entire leading antecedent*)
fun oblg_template report_time {can_inst, fix_level} f ctxt th00 = Seq.make (fn () =>
  PLPR_Statistics.measure_time_of_proof_evaluation' report_time ctxt (fn () =>
  let val th01 = case PLPR_Syntax.dest_premise_tag_opt (major_prem_of th00)
                   of SOME _ => th00
                    | NONE => @{thm' Premise_D[where mode=default]} RS th00
      val th = Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
              PLPR_Syntax.premise_tag_conv (K true) (Simplifier.full_rewrite ctxt)) ctxt) 1 th01
   in case Thm.major_prem_of th
   of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) =>
        SOME (@{thm' TrueI} RS' (ctxt, th), Seq.empty)
    | _ => case fast_inst can_inst th
   of SOME ret => SOME ret
    | _ => let (* simple_simp ctxt (Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (Conv.arg_conv (
                  Simplifier.rewrite (Very_Safe_Oblg_Simp_SS.equip ctxt)))
             ) ctxt) 1 th01) *)

      val (_,prems,concl) = Phi_Help.leading_antecedent (Thm.prop_of th)
      val annotated_fixs = annot_of_fixing [] concl
      val fixing_targets = map Var (
             case fix_level
               of 1 => merge (op =) (subtract (op =) (add_vars concl []) (fold add_vars prems []),
                                     annotated_fixs)
                | 2 => add_vars (Phi_Help.leading_antecedent' th) annotated_fixs
                | _ => annotated_fixs )

      val (ctxt', th2, instc) =
            if null fixing_targets then (ctxt, th, (TVars.empty, Vars.empty))
            else let val (inst, ctxt') = Variable.import_inst false fixing_targets ctxt
                     val instc = Phi_Help.certify_vars (Context.Proof ctxt') inst
                  in (ctxt', Thm.instantiate instc th, instc)
                 end
                    
   in (case fast_inst can_inst th2
   of SOME ret => SOME ret
    | NONE => (
      case LPR_inst ctxt' th2
        of SOME ret => f ctxt' ret
         | _ => f ctxt' th2))
   |> not (null fixing_targets) ? Option.map (fn (th, seq') =>
        let val f = singleton (Variable.export_inst (Phi_Help.uncertify_vars instc))
         in (f th, Seq.map f seq')
        end)
  end end) ())


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

  The semantics of schematic variables in auto_obligation_solver and guard_condition_solver is,
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


(** Case Split **)

fun case_split_by_annotations term =
  let fun insrt x splits = if Term.is_open x then splits else insert (op aconv) x splits
      fun parse_split (Const(N, Type("fun", [T,_])) $ X) splits =
            if N = \<^const_name>\<open>case_split\<close> orelse N = \<^const_name>\<open>LPR_ctrl\<close>
            then (case (T,X)
              of (\<^Type>\<open>prod _ _\<close>, Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) => splits
               | (\<^Type>\<open>prod _ _\<close>, x) => insrt x splits
               | (\<^Type>\<open>bool\<close>, Const(\<^const_name>\<open>True\<close>, _)) => splits
               | (\<^Type>\<open>bool\<close>, Const(\<^const_name>\<open>False\<close>, _)) => splits
               | (\<^Type>\<open>bool\<close>, x) => insrt x splits
               | (\<^Type>\<open>sum _ _\<close>, Const(\<^const_name>\<open>Inl\<close>, _) $ _) => splits
               | (\<^Type>\<open>sum _ _\<close>, Const(\<^const_name>\<open>Inr\<close>, _) $ _) => splits
               | (\<^Type>\<open>sum _ _\<close>, x) => insrt x splits
               | _ => insrt X splits)
            else parse_split X splits
       | parse_split (A $ B) splits = parse_split B (parse_split A splits)
       | parse_split (Abs (_, _, X)) splits = parse_split X splits
       | parse_split _ splits = splits
   in case parse_split term []
   of [] => K (K all_tac)
    | L => fn ctxt => fn goal => fn st =>
                  foldl1 (op THEN_ALL_NEW)
                         (map (fn tm => DETERM o Induct.cases_tac ctxt true [[SOME tm]] NONE []) L) goal st
  end

fun case_split_by_annotations_leading_subgoal ctxt goal th =
      case_split_by_annotations (Phi_Help.leading_antecedent' th) ctxt goal th
  

(*** Obligation Extraction ***)

(** Premise Extraction **)

(*Given any antecedent, if we can extract abstract pure facts that can help to solve the target
  proof obligation?*)
(*Convention: the rule of premise extraction has form \<open>A \<equiv> Premise \<and> A\<close>*)
type pattern = term

fun is_syntactic_premise_mode \<^const_name>\<open>MODE_GUARD\<close> = true
  | is_syntactic_premise_mode \<^const_name>\<open>NO_INST\<close> = true
  | is_syntactic_premise_mode \<^const_name>\<open>MODE_COLLECT\<close> = true
  | is_syntactic_premise_mode \<^const_name>\<open>default\<close> = true
  | is_syntactic_premise_mode _ = false

fun is_syntactic_premise (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(M, _) $ _) = is_syntactic_premise_mode M
  | is_syntactic_premise (Abs (_,_,X)) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise _ = false

fun strip_premise_tag ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ _ =>
        Conv.try_conv (Conv.rewrs_conv @{thms' Premise_def}) ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
        Conv.arg_conv (strip_premise_tag ctxt) ctm
     | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (strip_premise_tag ctxt)) (strip_premise_tag ctxt) ctm
     | Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
        Phi_Conv.hol_all_conv (strip_premise_tag o snd) ctxt ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (strip_premise_tag ctxt)) (strip_premise_tag ctxt) ctm
     | Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (strip_premise_tag ctxt)) (strip_premise_tag ctxt) ctm
     | _ => Conv.all_conv ctm

(*
fun extract_prem ctxt strip =
  let val ctxt' = Context.proof_of ctxt
   in fn thm =>
   if is_syntactic_premise (Thm.prop_of thm)
   then SOME (if strip
              then (Raw_Simplifier.norm_hhf ctxt' thm)
                |> Conv.fconv_rule (strip_premise_tag ctxt')
              else thm)
   else (*if qchk [] (Thm.prop_of thm)
        then let val thm = Raw_Simplifier.norm_hhf ctxt' thm
              in (case conv ctxt' (Thm.cprop_of thm)
                    of SOME NONE => SOME (if strip
                                          then Conv.fconv_rule (strip_premise_tag ctxt') thm
                                          else thm)
                     | SOME (SOME rule) => SOME (
                         (Thm.equal_elim rule thm RS' (ctxt', conjunct1))
                           |> not strip ? (fn th => th RS' (ctxt', @{thm' Premise_I[where mode=MODE_GUARD]})))
                     | NONE => NONE)
             end
   else*) NONE
  end
*)

fun extract_prems thm =
  let fun extract th =
        case Thm.concl_of th
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ XX => (
              case XX
                of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
                    extract (Conv.fconv_rule (Conv.rewr_conv @{thm' atomize_all[symmetric]}) th)
                 | Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _ =>
                    extract (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' \<r>Guard_def})) th)
                 | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
                    maps extract (PLPR_Syntax.elim_ant_sequence_or_HOL_conj th)
                 | Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _ =>
                    maps extract (PLPR_Syntax.elim_ant_sequence_or_HOL_conj th)
                 | Const(\<^const_name>\<open>Premise\<close>, _) $ Const (M, _) $ _ =>
                    if is_syntactic_premise_mode M
                    then [Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' Premise_def})) th]
                    else []
                 | _ => []
             )
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                extract (Thm.forall_elim_var (Thm.maxidx_of th+1) th)
           | _ => []
   in extract thm
  end


(** Applications of the Premise Extraction **)


(* if not use_origin, drops the original premises and only remains the extracted premises. *)
fun gen_simplify simp use_origin ctxt =
  let val extract = extract_prems
      val extract' = if use_origin
                     then (fn th => th :: extract th)
                     else (fn th => case extract th of [] => [th] | L => L)
      val sctxt = Simplifier.set_mksimps (fn ctxt =>
                      maps (Simpdata.mksimps Simpdata.mksimps_pairs ctxt)
                    o extract') ctxt
   in simp sctxt
  end

val asm_simplify = gen_simplify Simplifier.asm_simplify
val asm_lr_simplify = gen_simplify Simplifier.asm_lr_simplify
val full_simplify = gen_simplify Simplifier.full_simplify
val asm_simp_tac = gen_simplify Simplifier.asm_simp_tac
val asm_lr_simp_tac = gen_simplify Simplifier.asm_lr_simp_tac
val asm_rewrite = gen_simplify Simplifier.asm_rewrite
val asm_lr_rewrite = gen_simplify Simplifier.asm_lr_rewrite
val asm_full_rewrite = gen_simplify Simplifier.asm_full_rewrite

(** Obligation Extraction **)

val contract_premise_imp =
    @{lemma \<open>(P \<Longrightarrow> PROP Waste \<Longrightarrow> Premise mode G) \<equiv> (PROP Waste \<Longrightarrow> Premise mode (P \<longrightarrow> G))\<close>
            by (rule, (simp add: Premise_def)+)}

(*the term must be beta-eta normalized*)
fun obligation_collect counter ctxt =
  let fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
                Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ A $ _
               =>(if is_syntactic_premise A
                  then (counter := !counter + 1;
                         (Conv.implies_conv
                            (Phi_Conv.atomize_conv ctxt then_conv
                             strip_premise_tag ctxt)
                            conv then_conv
                          Conv.rewr_conv contract_premise_imp) ctm)
                  else (Conv.arg_conv conv then_conv
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
                                                                Premise_def[where mode=MODE_GUARD]})
                      (obligation_collect ctxt filter) then_conv
                    Conv.rewr_conv @{thm' contract_premise_imp}) ctm
              else (Conv.arg_conv (obligation_collect ctxt filter) then_conv
                    Conv.rewr_conv @{thm' conjunction_imp[symmetric]}) ctm
       | _ => raise CTERM ("unexpected proof obligation form", [ctm])
  ) ctm
*)

type schm_by_ex = int
type contraction_mode = bool * bool * schm_by_ex

fun chk_schm_by_ex ctxt ~1 = Config.get ctxt existential_obligation
  | chk_schm_by_ex _ i = i

fun chk_option ctxt (a,b,~1) = (a,b,Config.get ctxt existential_obligation)
  | chk_option _ option = option


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

fun obligation_intro_Ex_conv' conv_schematic ctxt thm0 =
  let val thm = Phi_Help.beta_eta_contract thm0
             |> (fn th => if null (Thm.tpairs_of th) then th
                          else case Seq.chop 2 (Thm.flexflex_rule (SOME ctxt) th)
                                 of ([th'], _) => th'
                                  | _ => th (*fails to solve flex-flex pairs*))
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
                    PLPR_Syntax.premise_tag_conv (K true) (
                      (Phi_Conv.move_sp_Ex_inside (K (
                                    Conv.fun_conv (Conv.rewr_conv @{thm' special_Ex_def}))) ctxt)
                      (*mv_Ex_All (fn _ => mv_Ex_Disj Conv.all_conv) ctxt*) )
                  )
                else Conv.all_conv)
            ) (Thm.forall_intr v thm)
   in fold intro_Ex vars' thm
  end

fun obligation_intro_Ex_conv conv_schematic ctxt thm =
  obligation_intro_Ex_conv' (chk_schm_by_ex ctxt conv_schematic) ctxt thm

fun augment_conditions conds ctxt sequent =
  let val _ = if can (PLPR_Syntax.dest_premise_tag o HOLogic.dest_Trueprop o Phi_Help.leading_antecedent') sequent
              then () else raise THM ("must be leaded by a bare premise antecedent quantified by no \
                                      \HHF conditions nor universal variables", 1, [sequent])
      val conds = map (Phi_Conv.atomize ctxt o Thm.forall_intr_vars) conds
   in sequent
   |> fold (fn cond => fn th =>
        Thm.implies_elim
          \<^instantiate>\<open>cond = \<open>Thm.dest_arg (Thm.cconcl_of cond)\<close> and
                      mode = \<open>Thm.dest_arg1 (Thm.dest_arg (Thm.dest_arg1 (Thm.cprop_of th)))\<close> and
                      P = \<open>Thm.dest_arg (Thm.dest_arg (Thm.dest_arg1 (Thm.cprop_of th)))\<close>
                        in lemma \<open>cond \<Longrightarrow> Premise mode (cond \<longrightarrow> P) \<Longrightarrow> Premise mode P\<close>
                              by (unfold Premise_def, blast)\<close>
          cond RS th) conds
  end

(*the leading antecedent must be beta-eta normalized*)
fun collect_obligation_premises option ctxt thm = let open Conv
  val (collect_premises,conv_all,conv_schematic) = chk_option ctxt option
  val new_cond = Unsynchronized.ref 0
  val rule1 = gconv_rule (Phi_Conv.meta_alls_conv (fn ctxt => 
                (if collect_premises then obligation_collect new_cond ctxt
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
                  | _ => @{lemma' \<open> PROP P \<Longrightarrow> PROP Pure.prop P \<close> by (unfold Pure.prop_def)} RS thm)
       | _ => error "BUG nhtCAsmjS+Oj4YsI8qtXQw"

   in drop_wastes rule1
   |> conv_all ? gconv_rule (obligation_conv_all ctxt) 1
   |> conv_schematic > 0 ? obligation_intro_Ex_conv' conv_schematic ctxt
   |> pair (!new_cond)
  end

(*Config.get ctxt existential_obligation*)

(*the leading antecedent must be beta-eta normalized*)
fun contract_obligations mode ctxt thm = thm
    |> collect_obligation_premises mode ctxt |> snd
    |> Conv.fconv_rule (Conv.rewr_conv @{thm contract_obligations})

fun find_obligations_tag thm = tl (Thm.prems_of thm)
      |> find_index (fn tm =>
            case tm of (_ $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _)) => true
                     | _ => false)
fun has_obligations_tag thm = find_obligations_tag thm <> ~1

fun defer_obligation cfg contract = oblg_template false cfg (fn ctxt => fn thm =>
  let val idx = find_obligations_tag thm
  in if idx = ~1
     then error ("Fail to defer a proof obligation: an \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> antecedent is not found.")
     else Thm.permute_prems 1 idx thm
      |> contract ctxt
      |> Thm.permute_prems 0 (~idx)
      |> (fn X => SOME (X, Seq.empty))
  end)

fun defer_obligation_tac cfg contr_mode =
      defer_obligation cfg (contract_obligations contr_mode)

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
val auto_obligation_solver = oblg_template true {can_inst=true, fix_level=0} (fn ctxt => fn th =>
      let val (_, th'1) = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
          val th' = @{thm' Premise_I} RS th'1
       in th'
       |> head_only (apply_tac ctxt (fn (ctxt,pre,aux,_) =>
          pre THEN HEADGOAL (Method.insert_tac ctxt aux)
              THEN Clasimp.auto_tac ctxt) Agressive_Solver)
       |> Seq.pull
      end)

val auto_obligation_solver' = context_tactic_to_state_transition auto_obligation_solver

fun auto_obligation_solver1 ctxt sequent =  (
        Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>auto\<close> method...",
            Syntax.pretty_term ctxt (Thm.major_prem_of sequent),
            Pretty.block (Pretty.here \<^here>)
        ]);
        auto_obligation_solver' (fn _ =>
          raise Automation_Fail (fn () =>
                  Pretty.para "Fail to solve the proof obligation automatically" ::
                  (case Thm.prems_of sequent
                     of (x::_)
                          => [Syntax.pretty_term ctxt x]
                      | _ => []))
          (*error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt Goal
            ])) *)
        ) ctxt sequent
     )

fun norm_tac tac th = Seq.make (fn () => Seq.pull (tac th))

fun timed_seq time s =
  Seq.make (fn () => 
    Timeout.apply time Seq.pull s
      handle Timeout.TIMEOUT _ => NONE )

fun timed_tac time tac th = timed_seq time (tac th)

fun timed1_tac time t' tac th =
  let val s = tac th
   in Seq.make (fn () =>
      Timeout.apply time Seq.pull s
      handle Timeout.TIMEOUT t'' =>
        if t'' > t' then raise Timeout.TIMEOUT t'' else NONE )
  end

fun quick_cut i th =
  case Logic.strip_assums_concl (Logic.nth_prem (i, Thm.prop_of th))
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>False\<close>, _) => Seq.empty
     | _ => Seq.single th

fun slow_step_tac' ctxt =
  Classical.appWrappers ctxt
    (Classical.instp_step_tac ctxt APPEND' Classical.unsafe_step_tac ctxt);

fun nodup_depth_tac ctxt m i st =
  SELECT_GOAL
    (Classical.safe_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (nodup_depth_tac ctxt m 1),
        Classical.inst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (slow_step_tac' ctxt 1 THEN DEPTH_SOLVE (nodup_depth_tac ctxt (m - 1) 1)))) i st;

fun auto_search_tac ctxt =
  let
    val ctxt = Context_Position.set_visible false ctxt
    fun main_tac i =
        CHANGED (nodup_depth_tac (addss ctxt) 10 i)
  in
    norm_tac ((
      TRY (Classical.safe_tac ctxt) THEN
      REPEAT_DETERM (FIRSTGOAL main_tac) THEN
      TRY (Classical.safe_tac (addSss ctxt)) THEN
      prune_params_tac ctxt)
      #> Seq.take 1 )
  end;


(*
fun auto_search1_tac ctxt t th =
  norm_tac (auto_search_tac ctxt t) th
    |> Seq.take 1 *)

fun dest_all ct used =
  (case Thm.term_of ct of
    Const ("Pure.all", _) $ Abs (x, _, _) =>
      let
        val (x', used') = Name.variant x used;
        val (v, ct') = Thm.dest_abs_fresh x' (Thm.dest_arg ct);
      in SOME ((x, Thm.ctyp_of_cterm v), (ct', used')) end
  | _ => NONE)

val negation = \<^cterm>\<open>Not\<close>

fun prove_or_rebute can_inst ctxt ctxt0 =
  let val search = auto_search_tac ctxt
   in timed_tac (Time.fromMilliseconds 30) search ORELSE
  (fn th =>
    let exception Unsupported
        val goals = Thm.cprems_of th
        val fail = Seq.make (fn () => (
              List.app (fn goal =>
                Phi_Reasoner.warn_pretty (Context.Proof ctxt) 1 (fn () => let open Pretty in
                  chunks (
                    [block (text "Fail to prove or falisfy the following guard condition"),
                    Goal_Display.pretty_a_goal ctxt (Thm.term_of goal),
                    block (text "We assume the conditions do not hold and this assumption can cause reasoning failure.")]
                    )
                end)) goals
              ; NONE))
     in let
        exception Falsified
        fun conv_goal used ctm =
          case Thm.term_of ctm  
            of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                  let val (f,a) = Thm.dest_comb ctm
                   in Thm.apply f (conv_goal used a)
                  end
             | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (x,_,_) =>
                  let val (q,b) = Thm.dest_comb ctm
                      val (x', used') = Name.variant x used;
                      val (v, b') = Thm.dest_abs_fresh x' b
                   in Thm.apply q (Thm.lambda v (conv_goal used' b'))
                  end
             | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
                  let val (c,b) = Thm.dest_comb ctm
                   in Thm.apply c (Thm.apply negation b)
                  end
             | _ => raise Unsupported
        val goals = map (fn goal =>
                      Goal.init (conv_goal (Term.declare_term_frees (Thm.term_of goal) Name.context) goal)
                    ) goals
        val goals = if can_inst
                    then Variable.import false goals ctxt |> #1 |> #2
                    else Variable.export ctxt ctxt0 goals
        val falsify = Seq.make (fn () =>
            if exists (fn goal =>
              case Seq.pull (search goal)
                of SOME (ret, _) => Thm.no_prems ret
                 | _ => false ) goals
            then raise Falsified
            else NONE
          )
     in Seq.make (fn () => Seq.pull (
            timed_seq (Time.fromMilliseconds 30) falsify ORELSE0
            timed_seq (Time.fromMilliseconds 250) (search th) ORELSE0
            timed_seq (Time.fromMilliseconds 100) falsify ORELSE0
            fail )
          handle Falsified => NONE)
    end handle Unsupported =>
      timed_tac (Time.fromMilliseconds 300) (auto_search_tac ctxt) th ORELSE0
      fail
    end)
  end

  


(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
fun guard_condition_solver {can_inst} ctxt0 th0 =
  let fun is_guard_mode (Const(\<^const_name>\<open>MODE_GUARD\<close>, _)) = true
        | is_guard_mode (Const(\<^const_name>\<open>NO_INST\<close>, _)) = true
        | is_guard_mode _ = false
      fun is_false (Const(\<^const_name>\<open>Premise\<close>, _) $ mode $ Const(\<^const_name>\<open>False\<close>, _))
            = is_guard_mode mode
        | is_false (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_false X
        | is_false _ = false
      val is_F = is_false (Thm.major_prem_of th0)

   in oblg_template true {can_inst = can_inst, fix_level= if can_inst then 1 else 2 }
  (fn ctxt => fn th =>
      let (*val (new_conds, th'1) = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
          val th' = @{thm' Premise_I} RS th'1*)
          val th' = th
          fun auto_tac ctxt =
                ALLGOALS (Simplifier.asm_full_simp_tac ctxt THEN_ALL_NEW quick_cut) THEN
                (if is_F
                 then timed_tac (Time.fromMilliseconds 250) (auto_search_tac ctxt)
                 else prove_or_rebute can_inst ctxt ctxt0)
                (* (timed_tac (Time.fromMilliseconds 300) (auto_search_tac ctxt)) *)
        (*fun clarsimp_tac ctxt =
                Simplifier.asm_full_simp_tac (Guess_Instantiate.add_guess_inst_solver ctxt) THEN_ALL_NEW
             (*For some reason I don't know, some goals rely on unsafe tactics even when no variables occur 
               (if can_inst then Simplifier.asm_full_simp_tac ctxt
                            else Simplifier.safe_asm_full_simp_tac ctxt) THEN_ALL_NEW *)
                (fn i => fn th => timed_tac (Time.fromMilliseconds 300) (Classical.fast_tac (addSss ctxt) i) th)
          fun clarsimp'_tac ctxt =
                Simplifier.asm_full_simp_tac ctxt THEN_ALL_NEW
                (fn i => fn th => timed_tac (Time.fromMilliseconds 300) (Classical.fast_tac (addss ctxt) i) th)
          fun force_tac ctxt =
                Classical.clarify_tac ctxt THEN_ALL_NEW
                Simplifier.asm_full_simp_tac ctxt THEN_ALL_NEW
                (fn i => fn th => timed_tac (Time.fromMilliseconds 300) (Classical.first_best_tac (addss ctxt) i) th) *)
       in
        apply_tac ctxt (fn (ctxt,pre,aux,_) => fn thtt => thtt |> (quick_cut 1 THEN (head_only (
             pre (*THEN REPEAT_DETERM_N new_conds (HEADGOAL (resolve_tac ctxt @{thms' impI}))*)
                 THEN HEADGOAL (
                              case_split_by_annotations_leading_subgoal ctxt 
                 THEN_ALL_NEW Method.insert_tac ctxt aux
                 ) THEN auto_tac (Guess_Instantiate.add_guess_inst_solver ctxt addsimps @{thms' Premise_def})
               (* THEN_ALL_NEW (fn s => fn x => clarsimp_tac (ctxt addsimps @{thms' Premise_def}) s x) ) *)
               (*THEN_ALL_NEW (fn s => fn x => Clasimp.fast_force_tac
                      (Guess_Instantiate.add_guess_inst_solver ctxt addsimps @{thms' Premise_def}) s x)*) )
               ))
              |> Seq.take 1 ) Safe_Solver th'
       |> Seq.take 1
       |> Seq.pull
      end) ctxt0 th0
  end

val guard_condition_solver' = context_tactic_to_state_transition o guard_condition_solver

fun guard_condition_solver1 can_inst ctxt sequent =
  guard_condition_solver' can_inst (fn _ =>
    error (Pretty.string_of (Pretty.chunks [
        Pretty.str "Fail to solve the proof obligation automatically:",
        Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
  ]))) ctxt sequent

fun safe_obligation_solver {can_inst} ctxt0 =
        oblg_template true {can_inst = can_inst, fix_level= if can_inst then 1 else 2 }
  (fn ctxt => fn th =>
      let val th' = th
          fun clarsimp_tac ctxt =
                Simplifier.asm_full_simp_tac (Guess_Instantiate.add_guess_inst_solver ctxt) THEN_ALL_NEW
                (fn i => fn th => Classical.clarify_tac (addSss ctxt) i th)
       in
        apply_tac ctxt (fn (ctxt,pre,aux,_) => fn thtt => thtt |> (quick_cut 1 THEN (
             pre (*THEN REPEAT_DETERM_N new_conds (HEADGOAL (resolve_tac ctxt @{thms' impI}))*)
                 THEN HEADGOAL (
                              case_split_by_annotations_leading_subgoal ctxt 
                 THEN_ALL_NEW Method.insert_tac ctxt aux
                 THEN_ALL_NEW (fn s => fn x => clarsimp_tac (ctxt addsimps @{thms' Premise_def}) s x) )
               (*THEN_ALL_NEW (fn s => fn x => Clasimp.fast_force_tac
                      (Guess_Instantiate.add_guess_inst_solver ctxt addsimps @{thms' Premise_def}) s x)*) )
               )
              |> Seq.take 1 ) Safe_Solver th'
       |> Seq.take 1
       |> Seq.pull
      end)
  (Phi_Safe_Simps.equip ctxt0)

val safe_obligation_solver' = context_tactic_to_state_transition o safe_obligation_solver

fun safe_obligation_solver1 can_inst ctxt sequent =
  safe_obligation_solver' can_inst (fn _ =>
    error (Pretty.string_of (Pretty.chunks [
        Pretty.str "Fail to solve the proof obligation automatically:",
        Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
  ]))) ctxt sequent

(*case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ Goal) => (
        (*Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>clarsimp\<close> method...",
            Syntax.pretty_term ctxt Goal,
            Pretty.block (Pretty.here \<^here>)
        ]); *)
        guard_condition_solver' (fn _ =>
          error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
        ]))) (ctxt addsimps @{thms Premise_def}) sequent
     )
     | _ => raise THM ("auto_obligation_solver1: The leading antecedent of the given sequent \
              \is not a proof obligation.", 1, [sequent])*)



(*fun declare_local_assume_reasoners sequent i *)




end
