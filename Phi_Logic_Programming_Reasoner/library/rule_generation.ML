(* AUTHOR: Qiyuan Xu

This file provides a framework of template instantiation of reasoning rules, where a template is
a rule with antecedents as the template parameters and argument rules can be given from which
we compose instances by resolution between the arguments and the parameters.
Instance rules can be declared as a \<phi>-LPR reasoning rule or with any attributes as indicated by the
template.

The file provides an attribute \<open>\<phi>reason_generator\<close> declaring a template of a single parameter as its
leading antecedent. Later, when the system of property database is built, property-based template
as an instance of multi-parameter template will be provided (carried out by attribute \<open>\<phi>reason_template\<close>)
which supports multi-properties as its parameters and instantiating the template once
sufficient properties are registered to the database.
*)

signature PLPR_RULE_GEN = sig

exception Generation_Fail of Phi_Reasoner.info_level * (unit -> Pretty.T list)

structure Template_Inst_SS : SIMPSET (*simpset for generating reasoning rules*)
structure Template_Inst_SS_Post_Merging : HOOKS

datatype instantiation_action =
            Reasonig_Rule of (Phi_Reasoner.mode' * Reasoner_Group.group option) * Phi_Reasoner.patterns_and_excepts
          | Attributes of Token.src list
          | No_Action

type binding_template = indexname list * binding
                       (*^ variables that will be instantiated to certain lambda terms, and the binding will
                      by qualified by the short-names of the heading constants of the lambda terms, which
                      comprises the final binding of the instance lemma.*)

type rule_generation_pass = (thm -> thm list) * Position.T * Proof.context -> thm -> thm list

type template = (Position.T * thm (*template*))
              * (rule_generation_pass * Phi_Reasoner.rule_pass) option
              * instantiation_action
              * binding_template option

val trim_action : instantiation_action -> instantiation_action
val pattern_of : instantiation_action -> term list option

val invoke_action : Position.T (*the position where the instantiation happens*) *
                    Phi_Reasoner.rule_pass option (*only effective for actions of Reasonig_Rule*)
                -> instantiation_action
                -> thm list -> Context.generic -> Context.generic

val pass_generated_rule : {simp: bool,
                           masks: IN_Arg.mask list option (*can be None by default*),
                           rule_pos: (Position.T (*template position*) *
                                      Position.T (*position of instantiation*) *
                                      binding option (*name of the instantiation*))}
                       -> Proof.context -> thm -> thm

type instantiation = Position.T (*where the instantiation happens*)
                   * Envir.env  (*unifiers between parameters and arguments*)
                   * (Position.T * thm) option list

(* Controller *)

val enable_reason_generator : bool Config.T
val trace : int Config.T

(* Controlling Simplification of Generated Rules *)

val simp_timeout : int Config.T (*in milliseconds*)

structure Simp_Reorient : PROOF_DATA

val default_reorient : Proof.context -> term list -> term -> term -> bool
val default_mk_eq_True : Proof.context -> thm -> thm option
val default_mk_sym : Proof.context -> thm -> thm option

val asm_lr_simplify : {simp_concl: bool} -> Proof.context -> thm -> thm

(* Main Entry *)
val invoke_generation : template -> instantiation -> Context.generic -> Context.generic

(* Syntax Parsers *)

val parse_pass : Context.generic -> Input.source option -> (rule_generation_pass * Phi_Reasoner.rule_pass) option
val parse_action : Phi_Reasoner.mode' * Reasoner_Group.group option * Phi_Reasoner.patterns_and_excepts * Token.src list option
                -> instantiation_action
val parse_binding_template : Context.generic -> thm -> (string * Position.T) option -> binding_template option

(* Internal Interfaces *)
val rule_template_pass__sender : (rule_generation_pass * Phi_Reasoner.rule_pass) option Unsynchronized.ref

end

structure PLPR_Rule_Gen : PLPR_RULE_GEN = struct

structure Template_Inst_SS_Post_Merging = Hooks (
  type arg = unit
  type state = Proof.context
)

type TT = Phi_Reasoner.pattern

structure Template_Inst_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>simp_for_\<phi>LPR_rule_generation\<close>
  val comment = "Rules simplifying the reasoning rules instantiated from templates."
  val attribute = NONE
  fun post_merging ctxt = ctxt
        |> Simplifier.del_cong @{thm' if_weak_cong}
        |> Simplifier.add_cong @{thm' if_cong}
        |> Template_Inst_SS_Post_Merging.invoke (Context.Proof ctxt) ()
)

datatype instantiation_action =
            Reasonig_Rule of (Phi_Reasoner.mode' * Reasoner_Group.group option) *
                             ( (Phi_Reasoner.pattern * priority option) list * Phi_Reasoner.pattern list )
          | Attributes of Token.src list
          | No_Action

type rule_generation_pass = (thm -> thm list) * Position.T * Proof.context -> thm -> thm list

type binding_template = indexname list * binding
                       (*^ variables that will be instantiated to certain lambda terms, and the binding will
                      by qualified by the short-names of the heading constants of the lambda terms, which
                      comprises the final binding of the instance lemma.*)

type template = (Position.T * thm (*template*))
              * (rule_generation_pass * Phi_Reasoner.rule_pass) option
              * instantiation_action
              * binding_template option

type instantiation = Position.T (*where the instantiation happens*)
                   * Envir.env  (*unifiers between parameters and arguments*)
                   * (Position.T * thm) option list


fun trim_action (X as Reasonig_Rule _) = X
  | trim_action (Attributes srcs) = Attributes (map (map Token.trim_context) srcs)
  | trim_action No_Action = No_Action

fun trim_template ((pos,tem),pass,act,bind) = ((pos, Thm.trim_context tem), pass, trim_action act, bind)

val enable_reason_generator = Attrib.setup_config_bool \<^binding>\<open>\<phi>reason_enable_generator\<close> (K true)

fun pattern_of (Reasonig_Rule (_, (pats, _))) = SOME (map fst pats)
  | pattern_of (Attributes _) = NONE
  | pattern_of No_Action = NONE

fun invoke_action (template_pos, pass) action rules' ctxt =
  (case action
     of (Reasonig_Rule ((mode, priority), (pats, blacklists))) =>
        let val (rules', (mode', priority'), (pats', blacklists'), guard', ctxt) =
                case pass of SOME ps => ps template_pos (rules', (mode, priority), (pats, blacklists), NONE, ctxt)
                           | NONE => (rules', (mode, priority), (pats, blacklists), NONE, ctxt)
         in Phi_Reasoner.add_rules (map (fn rule =>
                      ([rule], template_pos, mode', priority', pats', blacklists', guard') ) rules') ctxt
        end
      | (Attributes attrs) =>
        let fun app attr = uncurry (Thm.apply_attribute (
                              Context.cases Attrib.attribute_global Attrib.attribute ctxt attr))
         in fold (curry (snd o fold app attrs)) rules' ctxt
        end
      | No_Action => ctxt
  )

exception Generation_Fail of Phi_Reasoner.info_level * (unit -> Pretty.T list)

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes

val trace = Attrib.setup_config_int \<^binding>\<open>\<phi>trace_template_inst\<close> (K 0);

fun SIMP_conv C =
  let fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>SIMP\<close>, _) $ _ => Conv.arg_conv (C ctxt) ctm
           | _ => Conv.sub_conv conv ctxt ctm
   in conv
  end

fun mk_simp_rule ctxt =
  let fun mk rule =
        case Thm.concl_of rule
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =>  
                mk (rule RS' (ctxt, @{thm' spec})) (*TODO: names of the variables*)
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                Thm.forall_elim_vars (Thm.maxidx_of rule) (Simplifier.norm_hhf ctxt rule)
                  |> mk
           | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ v) =>
                if is_Var (Term.head_of v)
                then (rule RS' (ctxt, @{lemma' \<open> (case (x,y) of (a,b) \<Rightarrow> P a b) \<Longrightarrow> P x y\<close>
                                           by simp}) (*TODO: names of the variables*))
                       |> mk
                else [rule] (*TODO: case split*)
           | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ball\<close>, _) $ _ $ _) =>
                mk (rule RS' (ctxt, @{thm' bspec})) (*TODO: names of the variables*)
           | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
                mk (rule RS' (ctxt, @{thm' conjunct1})) @ mk (rule RS' (ctxt, @{thm' conjunct2}))
           | _ => [rule]
   in mk
  end

(* Simplification stolen from Isabelle *)

local
fun rewrite_rule_extra_vars prems elhs erhs =
  let
    val elhss = elhs :: prems;
    val tvars = TVars.build (fold TVars.add_tvars elhss);
    val vars = Vars.build (fold Vars.add_vars elhss);
  in
    erhs |> Term.exists_type (Term.exists_subtype
      (fn TVar v => not (TVars.defined tvars v) | _ => false)) orelse
    erhs |> Term.exists_subterm
      (fn Var v => not (Vars.defined vars v) | _ => false)
  end

in

fun default_reorient ctxt prems lhs rhs =
  rewrite_rule_extra_vars prems lhs rhs
    orelse
  is_Var (head_of lhs)
    orelse
(* turns t = x around, which causes a headache if x is a local variable -
   usually it is very useful :-(
  is_Free rhs andalso not(is_Free lhs) andalso not(Logic.occs(rhs,lhs))
  andalso not(exists_subterm is_Var lhs)
    orelse
*)
  exists (fn t => Logic.occs (lhs, t)) (rhs :: prems)
    orelse
  null prems andalso Pattern.matches (Proof_Context.theory_of ctxt) (lhs, rhs)
    (*the condition "null prems" is necessary because conditional rewrites
      with extra variables in the conditions may terminate although
      the rhs is an instance of the lhs; example: ?m < ?n \<Longrightarrow> f ?n \<equiv> f ?m *)
    orelse
  is_Const lhs andalso not (is_Const rhs);

fun default_mk_eq_True (_: Proof.context) r =
  SOME (HOLogic.mk_obj_eq r RS @{thm Eq_TrueI}) handle Thm.THM _ => NONE;

fun default_mk_sym _ th = SOME (th RS Drule.symmetric_thm);

structure Simp_Reorient = Proof_Data (
  type T = (Proof.context -> term list -> term -> term -> bool)
         * (Proof.context -> thm -> thm option)
         * (Proof.context -> thm -> thm option)
  val init = K (default_reorient, default_mk_eq_True, default_mk_sym)
)
end

local

val vars_set = Vars.build o Vars.add_vars;

fun vperm (Var _, Var _) = true
  | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
  | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
  | vperm (t, u) = (t = u);

fun var_perm (t, u) = vperm (t, u) andalso Vars.eq_set (apply2 vars_set (t, u));

fun decomp_simp thm =
  let
    val prop = Thm.prop_of thm;
    val prems = Logic.strip_imp_prems prop;
    val concl = Drule.strip_imp_concl (Thm.cprop_of thm);
    val (lhs, rhs) = Thm.dest_equals concl handle TERM _ =>
      raise Raw_Simplifier.SIMPLIFIER ("Rewrite rule not a meta-equality", [thm]);
    val elhs = Thm.dest_arg (Thm.cprop_of (Thm.eta_conversion lhs));
    val erhs = Envir.eta_contract (Thm.term_of rhs);
    val perm =
      var_perm (Thm.term_of elhs, erhs) andalso
      not (Thm.term_of elhs aconv erhs) andalso
      not (is_Var (Thm.term_of elhs));
  in (prems, Thm.term_of lhs, elhs, Thm.term_of rhs, perm) end;

fun mk_eq_True mk_eq_True ctxt (thm, name) =
  case mk_eq_True ctxt thm
    of NONE => []
     | SOME eq_True =>
        let val (_, lhs, elhs, _, _) = decomp_simp eq_True;
        in [{thm = eq_True, name = name, lhs = lhs, elhs = elhs, perm = false}] end

fun rewrite_rule_extra_vars prems elhs erhs =
  let
    val elhss = elhs :: prems;
    val tvars = TVars.build (fold TVars.add_tvars elhss);
    val vars = Vars.build (fold Vars.add_vars elhss);
  in
    erhs |> Term.exists_type (Term.exists_subtype
      (fn TVar v => not (TVars.defined tvars v) | _ => false)) orelse
    erhs |> Term.exists_subterm
      (fn Var v => not (Vars.defined vars v) | _ => false)
  end;

fun rrule_eq_True meT ctxt thm name lhs elhs rhs thm2 =
  let val rrule = {thm = thm, name = name, lhs = lhs, elhs = elhs, perm = false} in
    if rewrite_rule_extra_vars [] lhs rhs then
      mk_eq_True meT ctxt (thm2, name) @ [rrule]
    else [rrule]
  end;


fun orient_rrule (reorient,meT,mk_sym) ctxt (thm, name) =
  let
    val (prems, lhs, elhs, rhs, perm) = decomp_simp thm;
  in
    if perm then [{thm = thm, name = name, lhs = lhs, elhs = elhs, perm = true}]
    else if reorient ctxt prems lhs rhs then
      if reorient ctxt prems rhs lhs
      then mk_eq_True meT ctxt (thm, name)
      else
        (case mk_sym ctxt thm of
          NONE => []
        | SOME thm' =>
            let val (_, lhs', elhs', rhs', _) = decomp_simp thm'
            in rrule_eq_True meT ctxt thm' name lhs' elhs' rhs' thm end)
    else rrule_eq_True meT ctxt thm name lhs elhs rhs thm
  end

fun extract_rews ctxt thms =
  let val mk = Simplifier.mksimps
  in maps (fn thm => map (rpair (Thm.get_name_hint thm)) (mk ctxt thm)) thms
  end;

fun extract_safe_rrules cfg ctxt thm =
  maps (map #thm o orient_rrule cfg ctxt) (extract_rews ctxt [thm]);

in

val simp_timeout = Config.declare_int ("\<phi>LPR.rule_gen.timeout", \<^here>) (K 100)

fun asm_lr_simplify {simp_concl} ctxt rule0 =
  let val reorient_cfg = Simp_Reorient.get ctxt
      fun pass_premises (i, hyps, rule, ctxt) =
        if Thm.no_prems rule
        then (hyps,
              if simp_concl then Conv.fconv_rule (Simplifier.rewrite ctxt) rule
                            else if Term.exists_Const (fn (\<^const_name>\<open>SIMP\<close>, _) => true
                                                        | _ => false) (Thm.prop_of rule)
                            then Conv.fconv_rule (SIMP_conv Simplifier.rewrite ctxt) rule
                            else rule,
              ctxt)
        else let val rule'1 = Conv.gconv_rule (Phi_Reasoners.asm_lr_rewrite false ctxt) 1 rule
                 val cprem = Thm.cprem_of rule'1 1
         in case Thm.term_of cprem
         of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) =>
            pass_premises (i+1, hyps, Conv.fconv_rule (Conv.rewr_conv @{thm' True_implies_equals}) rule'1, ctxt)
          | prem_tm => let
                 val _ = if Term.exists_Const (fn (\<^const_name>\<open>SIMP\<close>, _) => true
                                                | _ => false) prem_tm
                         then raise THM ("SIMP tag can only occur in conclusion", i, [rule0])
                         else ()
                 val (lprem, ctxt) = Thm.assume_hyps cprem ctxt
                 val facts = the_default [] (Phi_Reasoners.extract_implied_fact {wrap_all=false} ctxt lprem)
                          |> maps (mk_simp_rule ctxt)
                          |> maps (extract_safe_rrules reorient_cfg ctxt)
                 val ctxt = ctxt addsimps facts
                 val rule'2 = Thm.implies_elim rule'1 lprem
         in pass_premises (i+1, cprem::hyps, rule'2, ctxt)
        end end
      val ((_, [rule']), ctxt') = Variable.import false [rule0] ctxt
      val (hyps, rule, _) = pass_premises (1, [], rule', ctxt')
   in fold Thm.implies_intr hyps rule
   |> Thm.transfer' ctxt'
  end

fun asm_lr_simplify' {simp_concl,timeout,rule_pos=(template_pos,inst_pos,binding)} ctxt rule0 =
  Timeout.apply timeout (asm_lr_simplify {simp_concl=simp_concl} ctxt) rule0
  handle Timeout.TIMEOUT _ => (
    raise Generation_Fail (0, fn () =>
      let open Pretty
       in [block ( text "Simplification for" @ [brk 1]
                 @ (case binding of SOME B => [Binding.pretty B] | _ => text "an instantiation")
                 @ [brk 1] @ here inst_pos @ [brk 1]
                 @ text "of template" @ [brk 1] @ here template_pos
                 @ [brk 1] @ text "timeouts" )]
      end)
    )

end

(*simplify the generated rule except the conclusion by default, unless a part of the conclusion has
  been annotated by \<open>NO_SIMP\<close> (i.e., \<open>NO_SIMP\<close> occurs in the conclusion)*)
fun pass_generated_rule {simp, masks, rule_pos} ctxt rule =
  let (*val rule'1 = case Thm.concl_of rule
                     of Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ _ => rule
                      | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ _) => rule
                      | X => if exists_Const (fn (\<^const_name>\<open>NO_SIMP\<close>, _) => true | _ => false) X
                             then rule
                             else rule RS' (ctxt, @{thm' NO_SIMP'_I})*)
      val rule'1 = rule
      val ctxt's = Template_Inst_SS.enhance ctxt

      fun trim_tag (Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ X) = SOME (the_default X (trim_tag X))
        | trim_tag (Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ X) = SOME (the_default X (trim_tag X))
        | trim_tag (A $ B) = (case (trim_tag A, trim_tag B)
                                of (NONE, NONE) => NONE
                                 | (A', B') => SOME (the_default A A' $ the_default B B'))
        | trim_tag (Abs (N,Ty,X)) = trim_tag X
                                 |> Option.map (fn X' => Abs (N, Ty, X'))
        | trim_tag _ = NONE

      fun simplify' rule'1 = 
        let val ((_, [rule'2]), ctxt'1) = Variable.import false [rule'1] ctxt's
         in rule'2
          |> simp ? ( Simplification_Protect.protect ctxt'1
                   #> asm_lr_simplify' {simp_concl=false,
                                        timeout=Time.fromMilliseconds (Config.get ctxt'1 simp_timeout),
                                        rule_pos=rule_pos}
                      ctxt'1
                      (*Phi_Reasoners.asm_lr_simplify true ctxt's*)
                   #> Simplification_Protect.unprotect ctxt'1 )
          |> singleton (Variable.export ctxt'1 ctxt)
          |> Phi_Help.unique_flexflex ctxt
        end
      fun simplify rule'1 =
        let val rule'3 = (simp ? simplify') rule'1

            val concl  = snd (PLPR_Syntax.strip_embedded_patterns (Thm.concl_of rule'3))
            val concl' = the_default concl (trim_tag concl)

            val masks' = case masks of SOME M => if null M
                                                 then IN_Arg.default_mask_of (Context.Proof ctxt) concl'
                                                 else M
                                     | NONE => IN_Arg.default_mask_of (Context.Proof ctxt) concl'
            val inargs = IN_Arg.parse_mask masks' concl'
         in case Phi_Help.instantiate_higher_order_schematic_var_for_rule' (~1, inargs) ctxt rule'3
              of SOME th => (simp ? simplify) th
               | NONE => rule'3
        end

   in simplify rule'1
   |> Simplifier.rewrite_rule ctxt @{thms' NO_SIMP_def NO_SIMP'_def SIMP_def}
   |> PLPR_Syntax.merge_guards {merge_cond=true} ctxt
   |> normalize
  end

fun short_name_of_leading_const (Abs (_,_,X)) = short_name_of_leading_const X
  | short_name_of_leading_const (X $ _) = short_name_of_leading_const X
  | short_name_of_leading_const (Const (N, _)) = Long_Name.base_name N
  | short_name_of_leading_const (Free (N, _)) = N
  | short_name_of_leading_const _ = raise Match

fun invoke_generation ((template_pos, template), pass, action, bind) (pos, env, positioned_props) ctxt =
     (let val ctxt' = Context.proof_of ctxt
                   |> Config.put Phi_Reasoner_solve_obligation_and_no_defer 1
                   |> Config.put Phi_Reasoner.trace (Config.get_generic ctxt trace)
          fun fold_pad _ 0 _ x = x
            | fold_pad f n [] x = fold_pad f (n-1) [] (f NONE x)
            | fold_pad f n (h::L) x = fold_pad f (n-1) L (f h x)
          val _ = case bind of SOME (_,b) => if Binding.name_of b = "module_mapper\<^sub>d\<^sub>a\<^sub>_\<^sub>b\<^sub>c" then () else ()
                             | _ => ()

          val rule'1 = (0, Thm.transfer' ctxt' template)
                    |> fold_pad (fn positioned_prop'' => fn (i, thm) =>
                        let (*datatype mode = Reason | Oblg | Normal*)
                            val prop'' = Option.map snd positioned_prop''
                            
                            fun parse_position (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) data = parse_position X data
                              | parse_position (Const(\<^const_name>\<open>Action_Tag\<close>, _)
                                                  $ X
                                                  $ (Const(\<^const_name>\<open>\<A>_template_reason\<close>, _) $ text))
                                               data
                                 = (case parse_position X data of (_, prop, thm) =>
                                      (SOME text, prop, @{thm' Action_Tag_I} RSN (i+1, thm)) )
                              | parse_position (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _) (LPR, prop, thm)
                                 = (case prop
                                      of SOME propx =>
                                          (LPR, SOME (PLPR_Syntax.guardize {merge_cond=true} ctxt' (Thm.nprems_of propx) propx),
                                           @{thm' \<r>Guard_I} RSN (i+1, thm))
                                       | _ => (LPR, prop, thm))
                              | parse_position (\<^Const>\<open>Pure.term \<^Type>\<open>prop\<close>\<close> $ X) data
                                 = (case parse_position X data of (LPR, prop, thm) =>
                                      (LPR, Option.map (Drule.mk_term o Thm.cconcl_of o Thm.transfer'' ctxt) prop, thm) )
                              | parse_position (\<^Const>\<open>Pure.term \<^Type>\<open>bool\<close>\<close> $ X) data
                                 = (case parse_position X data of (LPR, prop, thm) =>
                                      (LPR, Option.map (Drule.mk_term o PLPR_Syntax.dest_Trueprop_c o Thm.cconcl_of o Thm.transfer'' ctxt) prop, thm) )
                              | parse_position _ data = data

                            val (is_reasoning_goal, prop', thm'1) =
                                  parse_position (Logic.strip_assums_concl (Logic.nth_prem (i+1, Thm.prop_of thm)))
                                                 (NONE, prop'', thm)

                            val (delt,thm'2) = (case prop'
                                                  of SOME prop => ((Thm.nprems_of prop, prop RSN' (ctxt', i+1, thm'1))
                                                       handle THM _ => let open Pretty in
                                                          raise Generation_Fail (3, fn () =>
                                                            [block (text "unification fails in instantiating the" @
                                                                   [brk 1, str (string_of_int (i+1)), str "th", brk 1] @
                                                                   text "antecedent of the template" @ [brk 1] @ here pos),
                                                             item [str "template:", brk 1, Thm.pretty_thm ctxt' thm'1],
                                                             item [str "property:", brk 1, Thm.pretty_thm ctxt' prop]])
                                                        end)
                                                   | NONE => (1, thm'1))
                            val thm'3 =
                                 case is_reasoning_goal
                                   of SOME err_term =>
                                      thm'2 |> Thm.permute_prems 0 i
                                            |> Phi_Reasoner.reason NONE (SOME delt)
                                                                   (Config.map Phi_Reasoner.trace (fn i=>i-1) ctxt')
                                            |> (fn SOME th => th
                                                 | NONE =>
                                                    let open Pretty
                                                     in case err_term
                                                     of Const(\<^const_name>\<open>Some\<close>, _) $ text =>
                                                          raise Generation_Fail (0, fn () =>
                                                            [Text_Encoding.decode_text_pretty ctxt' text])
                                                      | Const(\<^const_name>\<open>undefined\<close>, _) =>
                                                          raise Generation_Fail (0, fn () => 
                                                            [para "fail to reason a compulsory antecedent",
                                                             Syntax.pretty_term ctxt' (Logic.nth_prem (i+1, Thm.prop_of thm'2))])
                                                      | Const(\<^const_name>\<open>None\<close>, _) =>
                                                          raise Generation_Fail (3, fn () => 
                                                            [para "fail to reason a compulsory antecedent",
                                                             Syntax.pretty_term ctxt' (Logic.nth_prem (i+1, Thm.prop_of thm'2))])
                                                      | X => raise TERM("Unrecognizable error text", [X])
                                                    end)
                                            |> Thm.permute_prems 0 (~i)
                                  (*| Oblg => Conv.gconv_rule (
                                                Raw_Simplifier.rewrite ctxt' false @{thms' \<A>_template_condition_def}
                                             ) (i+1) thm'2*)
                                    | _ => thm'2
                         in (if is_some is_reasoning_goal then i else i + delt, thm'3)
                        end) (Thm.nprems_of template) positioned_props
                    |> snd
                    |> Phi_Help.beta_eta_contract

          val binding = Option.map (fn (vs, b') =>
                  let val facts = Context.cases Global_Theory.facts_of Proof_Context.facts_of ctxt
                      fun varify_binding i b =
                        let val b' = if i = 0 then b else Binding.suffix_name ("\<^sub>" ^ string_of_int i) b
                            val iname = Context.cases Sign.full_name Proof_Context.full_name ctxt b'
                         in if Facts.defined facts iname
                            then varify_binding (i+1) b
                            else b'
                        end
                      fun err () = error (let open Pretty in string_of (chunks [
                                    block (text "The binding target" @ [brk 1] @
                                           maps (fn v => [Syntax.pretty_term ctxt' (Var (v, dummyT)), brk 1, str "/", brk 1]) vs @
                                           text "is not instantaited to any constant \<phi>-type,"),
                                    block (text "in template" @
                                           [brk 1, Thm.pretty_thm ctxt' template])
                                 ]) end)
                      val Envir.Envir {tenv, ...} = env
                      val qualify = fold_rev (fn v =>
                            case Vartab.lookup tenv v
                              of SOME (_, tm) => Binding.qualify true (short_name_of_leading_const tm handle Match => err ())
                               | NONE => err ()) vs
                   in varify_binding 0 (qualify b')
                  end
                ) bind

          val pattern = pattern_of action
          val rules' = case pass
             of SOME (ps, _) =>
                ps (single o pass_generated_rule {simp=true, masks=pattern, rule_pos=(template_pos, pos, binding)}
                                                 ctxt', pos, ctxt') rule'1
              | NONE =>
                single (pass_generated_rule {simp=true, masks=pattern, rule_pos=(template_pos, pos, binding)}
                                            ctxt' rule'1)
          val rules'' = map (snd o PLPR_Syntax.elim_embedded_patterns) rules'

       in if null rules' then ctxt
       else (
       Phi_Reasoner.info_pretty ctxt' 1 (fn () => let open Pretty in
         chunks ([paragraph (text "Instantiate reasoning template" @ [brk 1] @
                             (case binding of SOME b => [Binding.pretty b, brk 1] | _ => []) @
                             here template_pos)] @
                 (case action of Reasonig_Rule _ => []
                     | Attributes _ => map (fn rule => item [Thm.pretty_thm ctxt' rule]) rules'
                     | No_Action => []))
         end) ;
       invoke_action (template_pos, Option.map snd pass) action rules' ctxt
   |> (case binding of NONE => I
          | SOME b =>
                perhaps (try (Context.mapping (snd o Global_Theory.note_thms "" ((b, []), [(rules'',[])]))
                                              (snd o Proof_Context.note_thms "" ((b, []), [(rules'',[])]))))
                        (*It is not a Local_Theory.note here because the instantiation usually happens
                          inside an attribute and when a locale is interpreted, the attribute will be replayed.*)
                        (*I want to support lazy instantiation, but, to provide this, the Proof.context
                          has to be involved in the closure and that would consume a lot of memory.
                          Perhaps we could use the mechanism of dynamic fact, I am not sure which is better,
                          some test is required.*)
      )
    ) end
      handle Generation_Fail (lev, prt) => (
        Phi_Reasoner.warn_pretty ctxt lev (fn () => let open Pretty in
          chunks (
              [block (text "During instantiating" @ [brk 1] @
                (case bind of NONE => text "a template"
                            | SOME (_, b) => [Binding.pretty b]) @ [brk 1] @ here template_pos @ [str ","])]
            @ prt ())
          end) ;
        ctxt))


val rule_template_pass__sender : (rule_generation_pass * Phi_Reasoner.rule_pass) option Unsynchronized.ref
      = Unsynchronized.ref NONE
val rule_template_pass__sender_locker = Synchronized.var "rule_template_pass__sender_locker" ()


(*
val parser = Scan.option (Scan.lift (Args.$$$ "pass" |-- \<^keyword>\<open>:\<close> |-- Parse.ML_source))
          -- Scan.option Attrib.attribs*)
fun parse_pass ctxt =
  Option.map (fn src =>
    let val _ = Synchronized.change rule_template_pass__sender_locker (fn () => (
                  ML_Context.expression (Input.pos_of src)
                    (ML_Lex.read "PLPR_Rule_Gen.rule_template_pass__sender := SOME (" @
                     ML_Lex.read_source src @
                     ML_Lex.read ")")
                    ctxt;
                  ()))
        val pass = the (!rule_template_pass__sender)
        val _ = rule_template_pass__sender := NONE
     in pass
    end)

fun parse_action (mode, prio_group, pats, attribs) =
  case (attribs, prio_group, pats)
    of (SOME (attrs as _ :: _), NONE, ([], [])) => Attributes attrs
     | (SOME [], NONE, ([], [])) => No_Action
     | (SOME _, _, _) =>
        error "Prioirty and binding patterns are senseless and not allowed to\
              \ be given once the attributes are given."
     | (NONE, _, _) =>
        Reasonig_Rule ((mode, prio_group), pats)

fun parse_binding_template ctxt template raw_binding =
  let val ctxt' = Context.proof_of ctxt
      val (_, ctxt_parse) = Variable.import true [template] ctxt'

      val read_terms = Variable.export_terms ctxt_parse ctxt' o Syntax.read_terms ctxt_parse

      fun chk_binding_target (Var (v,_)) = v
        | chk_binding_target X =
              error (let open Pretty in string_of (
                    block (text "The binding of the template instances must binds to a \
                                \variable in the template that will be instantaited to to \<phi>-type.\
                                \ However, the given binding target is not a variable," @
                           [brk 1, Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt X])
                  ) end)
      val binding = Option.map (fn (long_name, pos) =>
                      let val (qualifiers, name) = Phi_Help.split_last (Long_Name.explode long_name)
                       in (map chk_binding_target (read_terms qualifiers), Binding.make (name, pos))
                      end
                    ) raw_binding
   in binding
  end


fun setup_rule_generation_pass template' ctxt =
  let val template = trim_template template'
      val rule = #2 (#1 template)
      val pass_id = Thm.prop_of rule

      val (qvars, _, mprem) = Phi_Help.leading_antecedent (Thm.prop_of rule)
      val idx = maxidx_of_term mprem + 1
      val qfix = map_index (fn (i, (N, T)) => Var((N,i+idx),T)) qvars
      val pattern = subst_bounds (rev qfix, mprem)
      val pidx = idx + length qfix

      fun pass ins_pos (data as (rules, mode, pats, guard, ctxt) : Phi_Reasoner.pass_data) =
        if Config.get_generic ctxt enable_reason_generator
        then let
            val args = map_filter (fn r =>
                        let val concl = Logic.incr_indexes ([],[],pidx) (Thm.concl_of r)
                            val cidx = maxidx_of_term concl
                         in case Seq.chop 2 (Unify.hounifiers (ctxt, Envir.empty cidx, [(concl, pattern)]))
                         of ([(env', _)], _) => SOME (env', (ins_pos, r))
                          | ([_,_], _) => (Phi_Reasoner.warn_pretty ctxt 2 (fn () => let open Pretty in
                                            chunks [para "Failed to instantiate a template due to multi-resolution",
                                                    block [str "Template: ", Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt rule],
                                                    block [str "Argument: ", Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt r]]
                                           end) ; NONE)
                          | _ => NONE
                        end) rules
            val ctxt' = fold (fn (env, r) => invoke_generation template (ins_pos, env, [SOME r])) args ctxt
         in (rules, mode, pats, guard, ctxt')
        end
        else data

      val _ = Phi_Reasoner.info_pretty_generic ctxt 1 (fn () => let open Pretty in
                chunks [para "Registered \<phi>-LPR generator binding on pattern",
                        item [Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt pattern]]
              end)
   in Phi_Reasoner.add_pass (pass_id, pattern, pass) ctxt
  end


val _ = Theory.setup (
  let fun rule_attribute f (x, th) =
              if Thm.is_free_dummy th
              then (NONE, NONE)
              else (SOME x, SOME (f x th))
   in Attrib.setup \<^binding>\<open>\<phi>simplify_reasoning_rule\<close> (
      Scan.succeed (rule_attribute (
          pass_generated_rule {simp=true, masks=NONE, rule_pos=(Position.none, Position.none, NONE)}
        o Context.proof_of)))
    "Simplify a reasoning rule, using the same process as that in template instantiation.\n\
    \The conclusion of the rule is remained untouched and any antecedents are simplified and reduced\
    \if possible. \<open>NO_SIMP\<close> tag is recognized and supresses the simplification on the protected terms."

   #> Attrib.setup \<^binding>\<open>\<phi>reason_generator\<close> (
      Phi_Reasoner.attr_syntax
        (Scan.option (Scan.lift (Args.$$$ "name" |-- Parse.position Parse.long_ident))
         -- Scan.option (Scan.lift (Args.$$$ "pass" |-- \<^keyword>\<open>:\<close> |-- Parse.ML_source))
         -- Scan.option Attrib.attribs)
        (fn (pos, mode, prio_group, ((raw_binding, pass_src), attribs), pats, guard) =>
        Thm.declaration_attribute (fn thm => fn ctxt =>
          let val binding = parse_binding_template ctxt thm raw_binding

              val _ = case guard of NONE => ()
                         | _ => error "No guard is allowed here"

              val pass = parse_pass ctxt pass_src
              val action = parse_action (mode, prio_group, pats, attribs)

              val template = ((pos, thm), pass, action, binding)
           in setup_rule_generation_pass template ctxt
          end))
      ) "declaring a template of a single parameter as its leading antecedent. \
        \The instantiation invokes any time a registered reasoning rule matching the first antecedent, \
        \yielding a new reasoning rule (or as declared by the given attribute) "
  end
)


end