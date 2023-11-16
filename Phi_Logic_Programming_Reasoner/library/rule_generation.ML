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

val pass_generated_rule : {simp: bool, masks: IN_Arg.mask list option (*can be None by default*)}
                       -> Proof.context -> thm -> thm

type instantiation = Position.T (*where the instantiation happens*)
                   * Envir.env  (*unifiers between parameters and arguments*)
                   * (Position.T * thm) option list

(* Controller *)

val enable_reason_generator : bool Config.T

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

val _ = Phi_Reasoners.extract_implied_fact

fun asm_lr_simplify {simp_concl} ctxt rule =
  let val ((_, [rule']), ctxt') = Variable.import false [rule] ctxt
      fun pass_premises (rule, ctxt) =
        if Thm.no_prems rule
        then (if simp_concl then Conv.fconv_rule (Simplifier.rewrite ctxt) rule
                            else rule,
              ctxt)
        else let val rule = Conv.gconv_rule (Simplifier.rewrite ctxt) 1 rule
                 val cprem = Thm.cprem_of rule 1
                 val ([lprem], ctxt) = Assumption.add_assms Assumption.presume_export [cprem] ctxt
                 val facts = the_default [] (Phi_Reasoners.extract_implied_fact {wrap_all=false} ctxt' lprem)
                 val ctxt = ctxt addsimps facts
                 val rule = Thm.implies_elim rule lprem
         in (rule, ctxt)
        end
      val (rule, ctxt') = pass_premises (rule', ctxt')
   in Assumption.export ctxt' ctxt rule
  end

(*simplify the generated rule except the conclusion by default, unless a part of the conclusion has
  been annotated by \<open>NO_SIMP\<close> (i.e., \<open>NO_SIMP\<close> occurs in the conclusion)*)
fun pass_generated_rule {simp, masks} ctxt rule =
  let val rule'1 = case Thm.concl_of rule
                     of Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ _ => rule
                      | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ _) => rule
                      | X => if exists_Const (fn (\<^const_name>\<open>NO_SIMP\<close>, _) => true | _ => false) X
                             then rule
                             else rule RS' (ctxt, @{thm' NO_SIMP'_I})
      val ((_, [rule'2]), ctxt'1) = Variable.import false [rule'1] ctxt
      val ctxt's = Template_Inst_SS.enhance ctxt'1
      val rule'3 = rule'2
                |> simp ? ( Simplification_Protect.protect ctxt's
                         #> Phi_Reasoners.asm_lr_simplify true ctxt's
                         #> Simplification_Protect.unprotect ctxt's )
                |> singleton (Variable.export ctxt'1 ctxt)
                |> Phi_Help.unique_flexflex ctxt

      fun trim_tag (Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ X) = SOME (the_default X (trim_tag X))
        | trim_tag (Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ X) = SOME (the_default X (trim_tag X))
        | trim_tag (A $ B) = (case (trim_tag A, trim_tag B)
                                of (NONE, NONE) => NONE
                                 | (A', B') => SOME (the_default A A' $ the_default B B'))
        | trim_tag (Abs (N,Ty,X)) = trim_tag X
                                 |> Option.map (fn X' => Abs (N, Ty, X'))
        | trim_tag _ = NONE
      val concl = snd (PLPR_Syntax.strip_embedded_patterns (Thm.concl_of rule'3))
      val concl' = the_default concl (trim_tag concl)

      val masks' = case masks of SOME M => if null M
                                           then IN_Arg.default_mask_of (Context.Proof ctxt) concl'
                                           else M
                               | NONE => IN_Arg.default_mask_of (Context.Proof ctxt) concl'
      val inargs = IN_Arg.parse_mask masks' concl'

   in (case Phi_Help.instantiate_higher_order_schematic_var_for_rule' (~1, inargs) ctxt rule'3
         of SOME th => simplify ctxt th
          | NONE => rule'3)
   |> Simplifier.rewrite_rule ctxt @{thms' NO_SIMP_def NO_SIMP'_def template_NO_SIMP_USE_def}
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
          fun fold_pad _ 0 _ x = x
            | fold_pad f n [] x = fold_pad f (n-1) [] (f NONE x)
            | fold_pad f n (h::L) x = fold_pad f (n-1) L (f h x)
          val _ = case bind of SOME (_,b) => if Binding.name_of b = "ToA_mapper" then () else ()
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
          val pattern = pattern_of action
          val rules' = case pass of SOME (ps, _) => ps (single o pass_generated_rule {simp=true, masks=pattern} ctxt', pos, ctxt') rule'1
                                  | NONE => single (pass_generated_rule {simp=true, masks=pattern} ctxt' rule'1)
          val rules'' = map (snd o PLPR_Syntax.elim_embedded_patterns) rules'

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
      Scan.succeed (rule_attribute (pass_generated_rule {simp=true, masks=NONE} o Context.proof_of)))
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