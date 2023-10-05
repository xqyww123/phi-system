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
      2: generate existence in obligations and apply_tac a special patch on them to enhance the automation
         of Isabelle for solving them (using introduction rules)
      ~1: take \<open>Config.get existential_obligation\<close>
  *)
  val collect_obligation_premises : contraction_mode -> Proof.context -> thm
                                 -> int (*number of new conditions introduced*) * thm

  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
  val wrap': (Proof.context -> thm -> thm option) -> (context_state -> context_state option)
  val wrap'': (Proof.context -> thm -> thm) -> (context_state -> context_state)

  val auto_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val auto_obligation_solver' : (Proof.context -> thm -> thm) (*failure callback*)
                              -> Proof.context -> thm -> thm
  val auto_obligation_solver1 : Proof.context -> thm -> thm

  val safer_obligation_solver : {can_inst: bool} -> Proof.context -> thm -> thm Seq.seq
      (*The annotation of \<open>case_split\<close> is supported*)
  val safer_obligation_solver': {can_inst: bool}
                             -> (Proof.context -> thm -> thm) (*failure callback*)
                             -> Proof.context -> thm -> thm
  val safer_obligation_solver1: {can_inst: bool} -> Proof.context -> thm -> thm


  (*defer the leading antecedent to the nearest obligation and call the contract*)
  val defer_antecedent : (Proof.context -> thm -> thm) (*contract*)
                                 -> Proof.context -> thm -> thm Seq.seq
  val defer_obligation_tac : contraction_mode -> Proof.context -> thm -> thm Seq.seq
  val augment_conditions : thm list -> Proof.context -> thm -> thm
        (*augmenting conditions to the leading proof obligations*)
  val has_obligations_tag : thm -> bool


  structure Tactic_Configures : HOOKS (*You can alter auxiliary facts, tactics, and configure the
      context before applying either the automatic solving*)

  (* Premise Extraction from arbitrary antecedent *)
  type pattern = term
  datatype extraction = Extract_Rule of thm (*of form \<open>P \<equiv> premise \<and> waste\<close>*)
                      | Extract_Fun of pattern * (Proof.context -> cterm -> thm option)

  val add_premise_extractions : extraction list -> Context.generic -> Context.generic
      (*users should also call derive_extracting_rules to add corresponded \<phi>-LPR rules extracting pure facts*)
  val add_premise_extraction_rules : thm list -> Context.generic -> Context.generic
  val del_premise_extractions : extraction list -> Context.generic -> Context.generic
  val derive_extracting_rules : Position.T -> extraction -> Context.generic -> Context.generic
  val extract_prem  : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm option
  val extract_prems : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm list
  val extract_prems_rewr : Context.generic (*the context used to fetch the extractions*)
                        -> Proof.context -> cterm -> thm option option
  val is_syntactic_premise : term -> bool

  (*(* Simplifications that uses the extracted premises.
     The boolean: use_origin. if not use_origin, drops the original premises
     and only remains the extracted premises.*)*)
  val asm_simplify : bool -> Proof.context -> thm -> thm
  val asm_lr_simplify : bool -> Proof.context -> thm -> thm
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

(*fix_level = 0 for no fix
            | 1 for fixing the conditions of the leading antecedent only but leaves variables
                    in the conclusion of the leading antecedent free
            | 2 for fixing variables in the entire leading antecedent*)
fun oblg_template {can_inst, fix_level} f ctxt th00 = Seq.make (fn () =>
  let val th01 = case PLPR_Syntax.dest_premise_tag_opt (major_prem_of th00)
                   of SOME _ => th00
                    | NONE => @{thm' Premise_D[where mode=default]} RS th00

      val th = Conv.gconv_rule (Simplifier.full_rewrite ctxt) 1 th01
   in case Thm.major_prem_of th
   of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) =>
        SOME (@{thm' TrueI} RS' (ctxt, th), Seq.empty)
    | _ => let
            (* simple_simp ctxt (Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (Conv.arg_conv (
                  Simplifier.rewrite (Very_Safe_Oblg_Simp_SS.equip ctxt)))
             ) ctxt) 1 th01) *)

      val fixing_targets = case fix_level
                             of 1 => #2 (Phi_Help.leading_antecedent (Thm.prop_of th))
                              | 2 => [Phi_Help.leading_antecedent' th]
                              | _ => []

      val (ctxt', th, instc) =
            if null fixing_targets then (ctxt, th, (TVars.empty, Vars.empty))
            else let val (inst, ctxt') = Variable.import_inst false fixing_targets ctxt
                     val instc = Phi_Help.certify_vars (Context.Proof ctxt') inst
                  in (ctxt', Thm.instantiate instc th01, instc)
                 end

      fun mk_boolean_inst (Var v) b ret = Vars.add (v, if b then \<^cterm>\<open>True\<close> else \<^cterm>\<open>False\<close>) ret
        | mk_boolean_inst (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) b ret
            = mk_boolean_inst B b (mk_boolean_inst A b ret)
        | mk_boolean_inst (Const(\<^const_name>\<open>HOL.Not\<close>, _) $ A) b ret
            = mk_boolean_inst A (not b) ret
        | mk_boolean_inst (Const(\<^const_name>\<open>id\<close>, _) $ X) b ret
            = mk_boolean_inst X b ret
        | mk_boolean_inst _ _ _ = raise Match
                    
   in(case (can_inst, PLPR_Syntax.dest_premise_tag (major_prem_of th))
        of (_, (_, Const (\<^const_name>\<open>True\<close>, _))) =>
                SOME (@{thm' Premise_True} RS th, Seq.empty)
         | (true, (_, Var _)) =>
                SOME (@{thm' Premise_True} RS th, Seq.empty)
         | (true, (_, Const(\<^const_name>\<open>HOL.Not\<close>, _) $ X)) =>
             (let val th' = Thm.instantiate (TVars.empty,
                                mk_boolean_inst (Phi_Help.beta_eta_contract_term X) false Vars.empty) th
               in f ctxt' th'
              end handle Match => f ctxt' th)
         | (true, (_, Const(\<^const_name>\<open>HOL.conj\<close>, _)
                        $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _)
                        $ _)) =>
             (SOME (@{lemma' \<open>Premise mode P \<Longrightarrow> Premise mode (x = x \<and> P)\<close>
                         by (simp add: Premise_def)} RS th, Seq.empty)
              handle THM _ => f ctxt' th)
         | (true, (_, X as Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _)) =>
             (let val th' = Thm.instantiate (TVars.empty,
                                mk_boolean_inst (Phi_Help.beta_eta_contract_term X) false Vars.empty) th
               in f ctxt' th'
              end handle Match => f ctxt' th)
         | (true, (_, Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _)) =>
             (*solves the equation by unification once single resolution*)
             (SOME (@{lemma' \<open>Premise mode (x = x)\<close> by (simp add: Premise_def)} RS th, Seq.empty)
              handle THM _ => f ctxt' th)
         | _ => f ctxt' th)
   |> not (null fixing_targets) ? Option.map (fn (th, seq') =>
        let val f = singleton (Variable.export_inst (Phi_Help.uncertify_vars instc))
         in (f th, Seq.map f seq')
        end)
  end end)


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


(*** Case Split ***)

fun case_split_by_annotations term =
  let fun insrt x splits = if Term.is_open x then splits else insert (op aconv) x splits
      fun parse_split (\<^Const_>\<open>case_split T\<close> $ X) splits =
           (case (T,X)
              of (\<^Type>\<open>prod _ _\<close>, Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) => splits
               | (\<^Type>\<open>prod _ _\<close>, x) => insrt x splits
               | (\<^Type>\<open>bool\<close>, Const(\<^const_name>\<open>True\<close>, _)) => splits
               | (\<^Type>\<open>bool\<close>, Const(\<^const_name>\<open>False\<close>, _)) => splits
               | (\<^Type>\<open>bool\<close>, x) => insrt x splits
               | (\<^Type>\<open>sum _ _\<close>, Const(\<^const_name>\<open>Inl\<close>, _) $ _) => splits
               | (\<^Type>\<open>sum _ _\<close>, Const(\<^const_name>\<open>Inr\<close>, _) $ _) => splits
               | (\<^Type>\<open>sum _ _\<close>, x) => insrt x splits
               | _ => insrt X splits)
       | parse_split (A $ B) splits = parse_split B (parse_split A splits)
       | parse_split (Abs (_, _, X)) splits = parse_split X splits
       | parse_split _ splits = splits
   in case parse_split term []
   of [] => K (K all_tac)
    | L => fn ctxt => foldl1 (op THEN_ALL_NEW)
                             (map (fn tm => Induct.cases_tac ctxt true [[SOME tm]] NONE []) L)
  end

fun case_split_by_annotations_first_subgoal ctxt goal th =
      case_split_by_annotations (Phi_Help.leading_antecedent' th) ctxt goal th
  

(*** Obligation Extraction ***)

(** Premise Extraction **)

(*Given any antecedent, if we can extract abstract pure facts that can help to solve the target
  proof obligation?*)
(*Convention: the rule of premise extraction has form \<open>A \<equiv> Premise \<and> A\<close>*)
type pattern = term
datatype extraction = Extract_Rule of thm | Extract_Fun of pattern * (Proof.context -> cterm -> thm option)

fun extraction_eq (Extract_Rule tha, Extract_Rule thb) = Thm.eq_thm_prop (tha, thb)
  | extraction_eq (Extract_Fun fa, Extract_Fun fb) = pointer_eq (fa, fb)
  | extraction_eq _ = false

structure Premise_Extraction = Generic_Data (
  type T = extraction Net.net
  val empty = Net.empty
  val merge = Net.merge extraction_eq
)

fun pattern_of_rule th =
  case Thm.prop_of th
    of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ X $ _ => X
     | _ => raise THM ("Bad rule of premise extraction", 0, [th])

fun chk_pattern ctxt tm =
  let val ty = Term.fastype_of tm
      open Pretty
   in if ty <> \<^Type>\<open>bool\<close>
   then error (string_of (chunks [
     paragraph ( text "The premise extraction should bind on"
               @ [Context.cases Syntax.pretty_typ_global Syntax.pretty_typ ctxt HOLogic.boolT,
                  brk 1, str "instead of", brk 1,
                  Context.cases Syntax.pretty_typ_global Syntax.pretty_typ ctxt ty]),
     Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
   ]))
   else (case tm
     of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
          error (string_of (chunks [
              para "The premise extraction cannot bind on HOL conjunction",
              Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
          ]))
      | _ => tm)
  end

fun chk_extraction ctxt (Extract_Rule rule) =
      let open Pretty
          fun err msg = error (string_of (chunks [
                            paragraph (text "Bad rule of premise extraction:" @ [brk 1] @ text msg),
                            Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt rule
                         ]))
       in case Thm.prop_of rule
       of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
              Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _)) =>
                  (chk_pattern ctxt X, Extract_Rule (rule RS @{thm' eq_reflection}))
        | Const(\<^const_name>\<open>Pure.eq\<close>, _) $ X $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
                  (chk_pattern ctxt X, Extract_Rule rule)
        | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
               err "cannot have premises"
        | _ => err "malformed rule, must of form \<open>A \<equiv> Prem \<and> A'\<close> where Prem is the extracted premise"
      end
  | chk_extraction ctxt (Extract_Fun (pat, f)) = (chk_pattern ctxt pat, Extract_Fun (pat, f))

val convert_prem_extr_to_AEIF = @{lemma' \<open>A \<equiv> B \<and> C \<Longrightarrow> A \<longrightarrow> B @action \<A>EIF\<close>
                                     by (unfold Action_Tag_def, blast)}

fun derive_extracting_rules pos (Extract_Rule rule) ctxt =
      Phi_Reasoner.add_rule pos Phi_Reasoner.TO_BE_OVERRIDE @{reasoner_group %derived_\<A>EIF_from_premis_extraction}
                            ([],[]) NONE
                            [rule RS (Thm.transfer'' ctxt convert_prem_extr_to_AEIF)] ctxt
  | derive_extracting_rules pos (Extract_Fun (pat, f)) ctxt =
      Phi_Reasoner.add {name = Free("Derived_Premise_Extraction", Term.dummyT) $ pat,
                        pos = pos,
                        group = snd (@{reasoner_group %derived_\<A>EIF_from_premis_extraction}),
                        mode = Phi_Reasoner.TO_BE_OVERRIDE,
                        pattern = [(HOLogic.Trueprop $ (\<^Const>\<open>Action_Tag\<close>
                                                          $ (\<^Const>\<open>HOL.implies\<close> $ pat $ Var(("P", maxidx_of_term pat), \<^Type>\<open>bool\<close>))
                                                          $ \<^Const>\<open>\<A>EIF\<close>),
                                    @{priority %derived_\<A>EIF_from_premis_extraction})],
                        blacklist = [],
                        tactic = Phi_Reasoner.Tac_ML (fn (_, (ctxt,sequent)) => Seq.make (fn () =>
                          let val ctm = Thm.dest_arg1 (Thm.cprop_of sequent) (*dest_implies*)
                                     |> Thm.dest_arg (*dest_Trueprop*)
                                     |> Thm.dest_arg1 (*dest Action_Tag \<A>EIF*)
                                     |> Thm.dest_arg1 (*dest \<longrightarrow>*)
                           in f ctxt ctm
                           |> Option.map (fn ret => ((ctxt, convert_prem_extr_to_AEIF RS ret), Seq.empty))
                          end))} ctxt

fun del_derived_extracting_rules rule ctxt =
  Phi_Reasoner.del_reasoners (Phi_Reasoner.the_default_pattern_of ctxt (Thm.concl_of rule))
                             (fn r => case #tactic r of Phi_Reasoner.Tac_Rule [(_, rule')] => Thm.eq_thm (rule',rule)
                                                      | _ => false) ctxt

fun add_premise_extractions [] ctxt = ctxt
  | add_premise_extractions extrs ctxt =
      Premise_Extraction.map (fold (
        Net.insert_term_safe extraction_eq o chk_extraction ctxt
      ) extrs) ctxt

val add_premise_extraction_rules = add_premise_extractions o map Extract_Rule

fun del_premise_extractions extrs ctxt =
  Premise_Extraction.map (fold (Net.delete_term_safe extraction_eq o chk_extraction ctxt) extrs) ctxt

val del_premise_extraction_rules = del_premise_extractions o map Extract_Rule

fun add_del add del = Scan.lift (Args.add |-- Phi_Help.pos_parser "\<phi>premise_extraction" >> add
                                || Args.del >> K del
                                || Phi_Help.pos_parser "\<phi>premise_extraction" >> add);
val premise_extraction =
      add_del (fn pos => Thm.declaration_attribute (fn rule =>
                        add_premise_extraction_rules [rule]
                     #> derive_extracting_rules pos (Extract_Rule rule)))
              (Thm.declaration_attribute (fn rule =>
                        del_premise_extraction_rules [rule]
                     #> del_derived_extracting_rules rule))

val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>premise_extraction\<close> premise_extraction
                      "Declare rewrite rules to extract premises augmenting the proof obligation")

fun is_syntactic_premise (Const(\<^const_name>\<open>Premise\<close>, _) $ M $ _) = is_syntactic_premise M
  | is_syntactic_premise (Const(\<^const_name>\<open>default\<close>, _)) = true
  | is_syntactic_premise (Const(\<^const_name>\<open>MODE_GUARD\<close>, _)) = true
  | is_syntactic_premise (Const(\<^const_name>\<open>NO_INST\<close>, _)) = true
  | is_syntactic_premise (Const(\<^const_name>\<open>MODE_COLLECT\<close>, _)) = true
  | is_syntactic_premise (Abs (_,_,X)) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise _ = false

(*TODO: merge the \<phi>-LPR based extraction given in git tag PLPR-based-Premise-Extraction
        which gives a quick way to extend the extraction universally but heavily and slowly.*)
fun gen_extract_prems_rewr ctxt =
  let val net = Premise_Extraction.get ctxt
      val thy = Context.theory_of ctxt

      fun match_extraction bv_tys tm =
            Net.match_term net tm
              |> filter (fn Extract_Rule rule => Pattern_Translation.does_match_term thy bv_tys (pattern_of_rule rule, tm)
                          | Extract_Fun (pat, _) => Pattern_Translation.does_match_term thy bv_tys (pat, tm))

      fun apply_extraction ctxt ctm =
        match_extraction [] (Thm.term_of ctm)
         |> map_filter (fn Extract_Rule rule => SOME (Conv.rewr_conv rule ctm)
                         | Extract_Fun (_, f) => f ctxt ctm)
         |> (fn [] => NONE
              | [th] => SOME th
              | L => SOME (foldr1 (fn (tha,thb) =>
                        thb RS' (ctxt,
                        tha RS' (ctxt,
                        @{lemma' \<open>A \<equiv> P1 \<and> W1 \<Longrightarrow> A \<equiv> P2 \<and> W2 \<Longrightarrow> A \<equiv> (P1 \<and> P2) \<and> (W1 \<and> W2)\<close>
                            by (simp add: atomize_eq, blast)}
                     ))) L))

      fun qchk_obj bv_tys (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) =
            qchk_obj bv_tys A orelse qchk_obj bv_tys B
        | qchk_obj bv_tys (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ A $ B) =
            qchk_obj bv_tys A orelse qchk_obj bv_tys B
        | qchk_obj bv_tys (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ X) = qchk_obj bv_tys X
        | qchk_obj bv_tys (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, T, X)) = qchk_obj (T::bv_tys) X
        | qchk_obj bv_tys (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = qchk_obj bv_tys (Term.incr_boundvars 1 X $ Bound 0)
        | qchk_obj bv_tys tm = not (null (match_extraction bv_tys tm))

      fun quick_check bv_tys (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = quick_check bv_tys X
        | quick_check bv_tys (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, T, X)) = quick_check (T::bv_tys) X
        | quick_check bv_tys (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = quick_check bv_tys (Term.incr_boundvars 1 X $ Bound 0)
        | quick_check bv_tys (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = qchk_obj bv_tys X
        | quick_check _ _ = false

      exception Not_Meet
    (*fun wrap C ctm = case C ctm of SOME ret => ret | NONE => raise Not_Meet*)

      fun extract ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _ =>
               let val eq1 = Conv.fun_conv (Conv.fun_conv (Conv.rewr_conv @{thm' Ant_Seq_def})) ctm
                in extract ctxt (Thm.rhs_of eq1)
                |> Option.map (Thm.transitive eq1)
               end
           | Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
               (SOME ((Phi_Conv.hol_all_conv (fn (_, ctxt) => fn ctm =>
                          case extract ctxt ctm
                            of SOME ret => ret
                             | NONE => raise Not_Meet
                       ) ctxt then_conv
                       Conv.rewr_conv @{thm' all_conj_distrib[folded atomize_eq]}) ctm)
                handle Not_Meet => NONE)
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
               (case (extract ctxt (Thm.dest_arg1 ctm), extract ctxt (Thm.dest_arg ctm))
                  of (SOME ruleA, SOME ruleB) =>
                      let val merge = @{lemma' \<open>A \<equiv> Pa \<and> A' \<Longrightarrow> B \<equiv> Pb \<and> B' \<Longrightarrow> A \<and> B \<equiv> (Pa \<and> Pb) \<and> (A' \<and> B')\<close>
                                          by (simp add: atomize_eq, blast)} (*TODO: optimize! replace the RS!*)
                       in SOME (ruleB RS' (ctxt, ruleA RS' (ctxt, merge)))
                      end
                   | (SOME ruleA, NONE) =>
                      let val idx = Thm.maxidx_of_cterm ctm + 1
                          val merge = @{lemma' \<open>A \<equiv> Pa \<and> A' \<Longrightarrow> A \<and> B \<equiv> Pa \<and> (A' \<and> B)\<close>
                                          by (simp add: atomize_eq)}
                                   |> Thm.incr_indexes idx
                                   |> Thm.instantiate (TVars.empty, Vars.make [((("B",idx),\<^Type>\<open>bool\<close>), Thm.dest_arg ctm)])
                       in SOME (ruleA RS' (ctxt, merge))
                      end
                   | (NONE, SOME ruleB) =>
                      let val idx = Thm.maxidx_of_cterm ctm + 1
                          val merge = @{lemma' \<open>B \<equiv> Pb \<and> B' \<Longrightarrow> A \<and> B \<equiv> Pb \<and> (A \<and> B')\<close>
                                          by (simp add: atomize_eq, blast)}
                                   |> Thm.incr_indexes idx
                                   |> Thm.instantiate (TVars.empty, Vars.make [((("A",idx),\<^Type>\<open>bool\<close>), Thm.dest_arg1 ctm)])
                       in SOME (ruleB RS' (ctxt, merge))
                      end
                   | (NONE, NONE) => NONE)
           | Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _ =>
               extract ctxt (Thm.dest_arg ctm)
                |> Option.map (fn ret => (Conv.rewr_conv @{thm' \<r>Guard_def} then_conv (K ret)) ctm)
           | _ => apply_extraction ctxt ctm


      fun simp_tag ctxt = Raw_Simplifier.rewrite ctxt true @{thms' Premise_def[where mode=default]
                                                                   Premise_def[where mode=MODE_GUARD]}

      fun extract' ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>HOL.Trueprop\<close>, _) $ _ =>
              (case extract ctxt (Thm.dest_arg ctm)
                 of SOME rule => Conv.arg_conv (K rule) ctm
                  | NONE => raise Not_Meet)
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
              (Conv.implies_conv (Phi_Conv.atomize_conv ctxt then_conv simp_tag ctxt) (extract' ctxt) then_conv
               Conv.rewr_conv @{lemma' \<open>(A \<Longrightarrow> P \<and> W) \<equiv> Trueprop ((A \<longrightarrow> P) \<and> (A \<longrightarrow> W))\<close>
                                  by (unfold atomize_imp, rule, blast, blast)}) ctm
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, _) =>
              (Phi_Conv.meta_all_conv (extract' o snd) ctxt then_conv
               Conv.rewr_conv @{lemma' \<open>(\<And>c. P c \<and> W c) \<equiv> Trueprop (All P \<and> All W)\<close>
                                  by (unfold atomize_all, rule, blast, blast)}) ctm
           | _ => raise Not_Meet
   in (quick_check,
   fn ctxt => fn ctm =>
   if is_syntactic_premise (Thm.term_of ctm)
   then SOME NONE
   else if quick_check [] (Thm.term_of ctm)
   then SOME (SOME (extract' ctxt ctm))
        handle Not_Meet => NONE
   else NONE)
  end

fun extract_prems_rewr ctxt = snd (gen_extract_prems_rewr ctxt)

fun strip_premise_tag ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ _ =>
        Conv.try_conv (Conv.rewrs_conv @{thms' Premise_def[where mode=default]
                                               Premise_def[where mode=MODE_GUARD]}) ctm
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

fun extract_prem ctxt strip =
  let val ctxt' = Context.proof_of ctxt
      val (qchk, conv) = gen_extract_prems_rewr ctxt
   in fn thm =>
   if is_syntactic_premise (Thm.prop_of thm)
   then SOME (if strip
              then (Raw_Simplifier.norm_hhf ctxt' thm)
                |> Conv.fconv_rule (strip_premise_tag ctxt')
              else thm)
   else if qchk [] (Thm.prop_of thm)
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
   else NONE
  end

fun extract_prems ctxt strip thm =
  let fun simp th =
        case Thm.concl_of th
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =>
                simp (Conv.fconv_rule (Conv.rewr_conv @{thm' atomize_all[symmetric]}) th)
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                simp (Thm.forall_elim_var (Thm.maxidx_of th+1) th)
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
        | default (Const(\<^const_name>\<open>MODE_GUARD\<close>, _)) = true
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
val asm_simp_tac = gen_simplify Simplifier.asm_simp_tac
val asm_lr_simp_tac = gen_simplify Simplifier.asm_lr_simp_tac
val asm_rewrite = gen_simplify Simplifier.asm_rewrite
val asm_lr_rewrite = gen_simplify Simplifier.asm_lr_rewrite
val asm_full_rewrite = gen_simplify Simplifier.asm_full_rewrite

(** Obligation Extraction **)

val contract_premise_imp =
    @{lemma \<open>(P \<Longrightarrow> PROP Waste \<Longrightarrow> Premise mode G) \<equiv> (PROP Waste \<Longrightarrow> Premise mode (P \<longrightarrow> G))\<close>
            by (rule, (simp add: Premise_def)+)}
val contract_premise_imp' =
    @{lemma \<open>(P \<and> A \<Longrightarrow> PROP Waste \<Longrightarrow> Premise mode G) \<equiv> (A &&& PROP Waste \<Longrightarrow> Premise mode (P \<longrightarrow> G))\<close>
            by (rule, (simp add: Premise_def conjunction_imp)+)}

(*the term must be beta-eta normalized*)
fun obligation_collect counter ctxt filter =
  let fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
                Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _
               =>(case filter ctxt (Thm.dest_arg1 ctm)
                    of SOME NONE => (*A normal premises using the normal rule*)
                        (counter := !counter + 1;
                         (Conv.implies_conv
                            (Phi_Conv.atomize_conv ctxt then_conv
                             strip_premise_tag ctxt)
                            conv then_conv
                          Conv.rewr_conv contract_premise_imp) ctm)
                     | SOME (SOME rule) => (*Not a direct premise but still has something can be extracted
                                             so we apply_tac the given rule to extract*)
                        (counter := !counter + 1;
                         (Conv.implies_conv (Conv.rewr_conv rule) conv then_conv
                          Conv.rewr_conv contract_premise_imp') ctm)
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
                                                                Premise_def[where mode=MODE_GUARD]})
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
  val filter = extract_prems_rewr (Context.Proof ctxt)
  val new_cond = Unsynchronized.ref 0
  val rule1 = gconv_rule (Phi_Conv.meta_alls_conv (fn ctxt => 
                (if collect_premises then obligation_collect new_cond ctxt filter
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
   |> conv_schematic > 0 ? obligation_intro_Ex_conv conv_schematic ctxt
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

fun defer_antecedent contract = oblg_template {can_inst=true, fix_level=0} (fn ctxt => fn thm =>
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
val auto_obligation_solver = oblg_template {can_inst=true, fix_level=0} (fn ctxt => fn th =>
      let val (new_conds, th'1) = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
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
          raise Automation_Fail (SOME (ctxt,sequent))
          (*error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt Goal
            ])) *)
        ) ctxt sequent
     )


(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
fun safer_obligation_solver {can_inst} = oblg_template {can_inst = can_inst,
                                                        fix_level= if can_inst then 1 else 0
                                                        (*it is zero because we will never use tactics
                                                          that instantiate some variable ever.*) }
  (fn ctxt => fn th =>
      let val (new_conds, th'1) = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
          val th' = @{thm' Premise_I} RS th'1
          fun clarsimp_tac ctxt =
               (if can_inst then Simplifier.asm_full_simp_tac ctxt
                            else Simplifier.safe_asm_full_simp_tac ctxt) THEN_ALL_NEW
                Classical.clarify_tac (addSss ctxt)
       in apply_tac ctxt (fn (ctxt,pre,aux,_) =>
             pre THEN REPEAT_DETERM_N new_conds (HEADGOAL (resolve_tac ctxt @{thms' impI}))
                 THEN HEADGOAL (
                              case_split_by_annotations_first_subgoal ctxt 
                 THEN_ALL_NEW Method.insert_tac ctxt aux
                 THEN_ALL_NEW (fn s => fn x => clarsimp_tac ctxt s x))
               ) Safe_Solver th'
       |> Seq.pull
      end)

val safer_obligation_solver' = context_tactic_to_state_transition o safer_obligation_solver

fun safer_obligation_solver1 can_inst ctxt sequent =
  safer_obligation_solver' can_inst (fn _ =>
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
