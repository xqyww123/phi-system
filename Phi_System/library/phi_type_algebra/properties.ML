(*
\<^item> Storage of properties.
\<^item> Deriving rules from property-conditioned templates
*)

signature PHI_TYPE_TEMPLATE_PROPERTIES = sig

(*** Algebraic Properties ***)

type property_pattern = term (*pattern of the property*)

val check_property : theory -> property_pattern -> property_pattern option
                     (*returns normalized form if it is a registered property*)
val assert_property_kind : theory -> property_pattern -> property_pattern
val add_property_kinds : term list -> theory -> theory

val lookup_property_match : Context.generic -> property_pattern -> (Position.T * thm) list
val lookup_property_unify : Context.generic -> property_pattern -> (Position.T * thm) list
val add_property : Position.T * thm -> Context.generic -> Context.generic
(*val list_functors : Context.generic -> term list*)

val adding_property : bool Config.T (*controlling if automatically for any new reasoning rules,
  register to the property DB and invoking the related automation*)

structure Template_Inst_SS : SIMPSET (*simpset for generating reasoning rules*)
structure Template_Inst_SS_Post_Merging : HOOKS

(*** The Framework for Automation based on Algebraic Property ***)

(** Types **)

datatype instantiation_action =
            Reasonig_Rule of (Phi_Reasoner.mode * (priority * Reasoner_Group.name option)) *
                             ( (Phi_Reasoner.pattern * priority option) list * Phi_Reasoner.pattern list )
          | Attributes of Token.src list
          | No_Action

type parameters = property_pattern option list (*corresponding to the premises of the template rule
          one to one respectively, and being NONE if the premise in the corresponded position is
          not a property for instantiating*)
type instance_binding = indexname list * binding
                        (*^b a variable that will be instantiated to a \<phi>-type, and the binding will
                          by qualified by the short-name of the heading constant of the \<phi>-type*)

type rule_generation_pass = (thm -> thm list) (*default generation process*)
                          * Position.T (*where the template is instantiated*)
                          * Proof.context
                         -> thm -> thm list

val no_rule_generation_pass : rule_generation_pass

type free_template_action =
        Position.T (*Position where the instantiation happens*) *
        ( Envir.env (*unifier for the template parameters and instantiating properties*) *
          (Position.T * thm (*property*)) option list )
     -> Context.generic -> Context.generic

datatype template_action =
            Instantiate_Rule of thm * (rule_generation_pass * Phi_Reasoner.rule_pass) option *
                                instantiation_action * instance_binding option
          | Free_Action of free_template_action (*accept Automation_Fail*)

type template = parameters * Position.T (*position of the template*) * template_action

(** Basic Operations: Add, List, Invoke **)

val add_template : bool (*if to invoke on the existing instantiations if any*)
                -> template -> Context.generic -> Context.generic
val list_templates : Context.generic -> template list

type template_argument = Position.T (*position of the property*) * thm (*property*)
val invoke_template : template -> template_argument -> Context.generic -> Context.generic
val invoke_automations_on_property : template_argument -> Context.generic -> Context.generic
    (*invokes any template depending on the given property and of all dependencies satisfied*)

(** Auxiliaries **)

val pretty_template : Context.generic -> template -> Pretty.T
val pretty_templates : Context.generic -> (priority * template) Ord_List.T Symtab.table -> Pretty.T

(* The default process simplifying a freshly instantiated rule *)
val default_simplify : term list option (*pattern used in Phi_Reasoner.instantiate_higher_order_schematic_var_for_rule_guess
                            can be None by default*)
                    -> Proof.context -> thm -> thm

(*** Internal Interfaces ***)

val rule_template_pass__sender : (rule_generation_pass * Phi_Reasoner.rule_pass) option Unsynchronized.ref

end

structure Phi_Type_Template_Properties : PHI_TYPE_TEMPLATE_PROPERTIES = struct

exception Automation_Fail = Phi_Type_Algebra.Automation_Fail

type property_pattern = term

(*** Algebraic Property & Automation ***)

(** Property Kind **)

structure Property_Kinds = Theory_Data (
  type T = term Net.net (*proposition form, with Trueprop*)
  val empty = Net.empty
  val merge = Net.merge (op aconv)
)

fun trim_modifiers (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = HOLogic.Trueprop $ trim_modifiers X
  | trim_modifiers (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ Const(\<^const_name>\<open>\<A>_template_reason\<close>, _))
      = trim_modifiers X
  | trim_modifiers (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ X) = trim_modifiers X
  | trim_modifiers X = X

fun check_property thy =
  let val kinds = Property_Kinds.get thy
   in fn X => let val X = trim_modifiers X
               in if exists (fn pat => Pattern.matches thy (pat, X))
                            (Net.match_term kinds X)
                  then SOME X
                  else NONE
              end
  end

fun err_not_a_property_kind thy k = let open Pretty in
      error (string_of (
        block ([Syntax.pretty_term_global thy k, brk 1] @
               text "is not a known \<phi>-type property. Please use ML function \
                    \\<open>Phi_Type_Algebra.add_property_kind\<close> to register it.")))
    end

fun assert_property_kind thy =
  let val chk = check_property thy
   in fn k => case chk k
                of SOME x => x
                 | NONE => err_not_a_property_kind thy k
  end

(** Property DB **)

type free_template_action = Position.T (*Position where the instantiation happens*) *
                            ( Envir.env (*unifier for the template parameters and instantiating properties*) *
                              (Position.T * thm (*property*)) option list )
                         -> Context.generic -> Context.generic

type parameters = property_pattern option list
type instance_binding = indexname list * binding
                        (*^b a variable that will be instantiated to a \<phi>-type, and the binding will
                          by qualified by the short-name of the heading constant of the \<phi>-type*)

type rule_generation_pass = (thm -> thm list) * Position.T * Proof.context -> thm -> thm list

fun no_rule_generation_pass (default, _, _) = default

datatype instantiation_action =
            Reasonig_Rule of (Phi_Reasoner.mode * (priority * Reasoner_Group.name option)) *
                             ( (Phi_Reasoner.pattern * priority option) list * Phi_Reasoner.pattern list )
          | Attributes of Token.src list
          | No_Action

datatype template_action =
            Instantiate_Rule of thm * (rule_generation_pass * Phi_Reasoner.rule_pass) option *
                                instantiation_action * instance_binding option
          | Free_Action of free_template_action

type template = parameters * Position.T * template_action
type template_argument = Position.T (*position of the property*) * thm (*property*)

fun property_eq ((_,th1),(_,th2)) = Thm.eq_thm_prop (th1,th2)

structure Properties = Generic_Data (
  type T = (Position.T * thm) Net.net (*proposition form*)
  val empty = Net.empty
  val merge = Net.merge property_eq
)

fun template_eq ((s1,_,_),(s2,_,_)) = s1 = s2

structure Templates = Generic_Data (
  type T = (serial * property_pattern * template) Net.net (*key: every parameter of a temlpate*)
                     (*convention, the property_pattern only contains schematic variables of negative indexes*)
  val empty = Net.empty
  val merge = Net.merge template_eq
)

val list_templates = Templates.get #> Net.content #> distinct template_eq #> map #3

fun pretty_template ctxt ((params, pos, action) : template) =
  let open Pretty
   in chunks (
        (case action of Instantiate_Rule (rule, _, _, b) =>
                [block ([str "Template", brk 1] @
                        the_default [] (Option.map (single o Binding.pretty o snd) b) @
                        here pos @
                        [brk 1, Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt rule]) ]
            | Free_Action _ =>
                [block ([para "ML automation", brk 1] @ here pos)]) @
        [para "depending on:"] @
        map (fn NONE => item [str "_"]
              | SOME param => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt param]) params
     )
  end

fun pretty_templates ctxt (table : (priority * template) Ord_List.T Symtab.table) =
  let val templates = Symtab.fold (fold (insert pointer_eq o snd) o snd) table []
      open Pretty
   in chunks (map (item o single o pretty_template ctxt) templates)
  end

(*
fun check_termplate ((params, pos, act) : template) : template =
  let val idx = fold (fn SOME param => Term.maxidx_term param | _ => I) params ~1
   in if idx >= 0 then (map (Option.map (Logic.incr_indexes ([],[],1-idx))) params, pos, act)
                  else (params, pos, act)
  end
*)

fun trim_template ((params, pos, act) : template) : template =
  (params, pos,
  case act of Instantiate_Rule (rule, pass, inst, b) =>
                Instantiate_Rule (Thm.trim_context rule, pass,
                  (case inst of Reasonig_Rule _ => inst
                              | Attributes srcs => Attributes (map (map Token.trim_context) srcs)
                              | No_Action => No_Action), b)
            | Free_Action act => Free_Action act)

(*
fun close_phitype_operator phityp =
  let val i = maxidx_of_term phityp + 1
   in case Term.binder_types (Term.fastype_of phityp)
   of [] => phityp
    | L => fold_index (fn (j,Ty) => fn Tm => Tm $ Var(("x",i+j), Ty)) L phityp
  end*)

(*fun net_encode_phityp phityp = Const("F", dummyT) $ phityp*)

(*fun get_property_name thm =
  if Thm.is_dummy thm then ""
  else fst (Term.dest_Const (Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of thm))))*)

fun lookup_property_match ctxt pattern =
  Net.match_term (Properties.get ctxt) pattern
   |> filter (fn (_, th) => Pattern.matches (Context.theory_of ctxt) (pattern, Thm.concl_of th))

fun lookup_property_unify' ctxt additions env pattern =
  let val Envir.Envir {maxidx, tenv, tyenv} = env
   in (additions @ Net.unify_term (Properties.get ctxt) pattern)
   |> map_filter (fn (pos, th) =>
        let val concl = Thm.concl_of th
                     |> maxidx >= 0 ? Logic.incr_indexes ([], [], maxidx+1)
            val cidx = if maxidx >= 0 then Thm.maxidx_of th + maxidx + 1 else Thm.maxidx_of th
            val env' = Envir.Envir {maxidx = cidx, tenv=tenv, tyenv=tyenv}
         in case Seq.pull (Unify.hounifiers (ctxt, env', [(pattern, concl)]))
         of SOME env => SOME (Seq.map fst (uncurry Seq.cons env), (pos, th))
          | NONE => NONE
        end)
  end

fun lookup_property_unify ctxt pattern =
      lookup_property_unify' ctxt [] (Envir.empty (Term.maxidx_of_term pattern)) pattern
        |> map snd

(* Invoke template instantiation *)

structure Template_Inst_SS_Post_Merging = Hooks (
  type arg = unit
  type state = Proof.context
)

structure Template_Inst_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>simp_for_\<phi>TA_rule_generation\<close>
  val comment = "Rules simplifying the reasoning rules instantiated from templates."
  val attribute = NONE
  fun post_merging ctxt = ctxt
        |> Simplifier.del_cong @{thm' if_weak_cong}
        |> Simplifier.add_cong @{thm' if_cong}
        |> Template_Inst_SS_Post_Merging.invoke (Context.Proof ctxt) ()
)

fun instantiations_of_parameters get_property ctxt params =
  let fun ext i param (env, props) =
             get_property env param
          |> map_filter (fn (envs, property) =>
                    case Seq.chop 2 envs
                      of ([env], _) => SOME (env, property :: props)
                       | ([], _) => NONE
                       | (env :: _ , _) => (
                             Phi_Reasoner.warn_pretty ctxt 2 (fn () => let open Pretty in
                                block (text "Multi-unififers in instantiating the" @ [brk 1,
                                       str (string_of_int i ^ "th"), brk 1] @
                                       text "parameter of a template. We only preserve the \
                                            \first unifier for performance consideration.")
                             end)
                           ; SOME (env, property :: props)
                         ))
      fun cross _ ret [] = map (apsnd rev) ret
        | cross i ret (param :: params) = cross (i+1) (maps (ext i param) ret) params
      val init_idx = fold (fn SOME p => Term.maxidx_term p | NONE => I) params ~1
   in case params
   of [] => []
    | (param :: params') =>
        cross 0 (ext 1 param (Envir.empty init_idx, [])) params'
  end

fun existing_instantiations_of_parameters ctxt =
      instantiations_of_parameters
          (fn env => (fn SOME p => map (apsnd SOME) (lookup_property_unify' ctxt [] env p)
                       | NONE => [(Seq.single env, NONE)])) ctxt

fun check_dependencies params action (pos,property) ctxt =
  let exception Dep
      val didx = fold (fn SOME p => Term.maxidx_term p | _ => I) params ~1
      val prop_concl = Thm.concl_of property
                    |> didx >= 0 ? Logic.incr_indexes ([],[],didx+1)
      val eidx = Thm.maxidx_of property + (if didx >= 0 then didx + 1 else 0)
   in(if not (Thm.is_dummy property) andalso exists (
            fn SOME param =>
                is_some (Seq.pull (Unify.hounifiers (ctxt, Envir.empty eidx, [(param, prop_concl)])))
             | NONE => false) params
      then let fun get_property env (SOME p) = map (apsnd SOME) (lookup_property_unify' ctxt [(pos,property)] env p)
                 | get_property env NONE = [(Seq.single env, NONE)]
               val ruless = instantiations_of_parameters get_property ctxt params
                         |> filter (exists (fn SOME (_, th) => pointer_eq (th, property) | _ => false) o snd)
            in fold (fn rules => fn ctxt =>
                          action (pos,rules) ctxt
                          handle Automation_Fail msg =>
                            let open Pretty
                                val msg' = msg ()
                             in if null msg' then ()
                                else warning (string_of (chunks (str "Automation Fail:" :: msg'))) ;
                              ctxt
                            end
                    ) ruless ctxt
           end
      else ctxt)
      handle Dep => ctxt
  end

fun short_name_of_tyop (Abs (_,_,X)) = short_name_of_tyop X
  | short_name_of_tyop (X $ _) = short_name_of_tyop X
  | short_name_of_tyop (Const (N, _)) = Long_Name.base_name N
  | short_name_of_tyop (Free (N, _)) = N
  | short_name_of_tyop _ = raise Match

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes

fun default_simplify pattern ctxt rule =
  let val rule'1 = case Thm.concl_of rule
                     of Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ _ => rule
                      | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ _) => rule
                      | _ => rule RS' (ctxt, @{thm' NO_SIMP'_I})
      val ((_, [rule'2]), ctxt'1) = Variable.import false [rule'1] ctxt
      val ctxt's = Template_Inst_SS.enhance ctxt'1
                |> Simplifier.del_cong @{thm' HOL.if_weak_cong}
      val rule'3 = rule'2
                |> Simplification_Protect.protect ctxt's
                |> Phi_Reasoners.asm_lr_simplify true ctxt's
                |> Simplification_Protect.unprotect ctxt's
                |> singleton (Variable.export ctxt'1 ctxt)
                |> Phi_Help.unique_flexflex ctxt
   in (case Phi_Help.instantiate_higher_order_schematic_var_for_rule_guess' (~1, the_default [] pattern) ctxt rule'3
         of SOME th => simplify ctxt th
          | NONE => rule'3)
   |> Simplifier.rewrite_rule ctxt @{thms' NO_SIMP_def NO_SIMP'_def template_NO_SIMP_USE_def}
   |> PLPR_Syntax.merge_guards ctxt
   |> normalize
  end


fun invoke_template_action template_pos (Instantiate_Rule (template, pass, action, bind))
                           (pos, (env, positioned_props)) ctxt =
     (let val ctxt' = Context.proof_of ctxt
                   |> Config.put Phi_Reasoner_solve_obligation_and_no_defer 1
          fun fold_pad _ 0 _ x = x
            | fold_pad f n [] x = fold_pad f (n-1) [] (f NONE x)
            | fold_pad f n (h::L) x = fold_pad f (n-1) L (f h x)
          val rule'1 = (0, Thm.transfer' ctxt' template)
                    |> fold_pad (fn positioned_prop'' => fn (i, thm) =>
                        let (*datatype mode = Reason | Oblg | Normal*)
                            val prop'' = Option.map snd positioned_prop''
                            val (is_reasoning_goal, prop', thm'1) =
                                  case Logic.strip_assums_concl (Logic.nth_prem (i+1, Thm.prop_of thm))
                                    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                          Const(\<^const_name>\<open>Action_Tag\<close>, _)
                                              $ _
                                              $ Const(\<^const_name>\<open>\<A>_template_reason\<close>, _)) =>
                                            (true, prop'', @{thm' Action_Tag_I} RSN (i+1, thm))
                                     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _) =>
                                        (case prop'' of SOME prop' =>
                                                (false,
                                                 SOME (PLPR_Syntax.guardize ctxt' (Thm.nprems_of prop') prop'),
                                                 @{thm' \<r>Guard_I} RSN (i+1, thm))
                                            | _ => (false, prop'', thm)
                                            )
                                   (*| Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                          Const(\<^const_name>\<open>Premise\<close>, _)
                                              $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _)
                                              $ P) =>
                                        if exists_subterm (fn (Const(\<^const_name>\<open>\<A>_template_condition\<close>, _)) => true
                                                            | _ => false) P
                                        then Oblg
                                        else Normal*)
                                     | _ => (false, prop'', thm)
                            val (delt,thm'2) = (case prop'
                                                  of SOME prop => ((Thm.nprems_of prop, prop RSN' (ctxt', i+1, thm'1))
                                                       handle THM _ => let open Pretty in
                                                          raise Automation_Fail (fn () =>
                                                            [block (text "Unification fails in instantiating the" @
                                                                   [brk 1, str (string_of_int (i+1)), str "th", brk 1] @
                                                                   text "antecedent of the template" @ [brk 1] @ here pos),
                                                             item [str "template:", brk 1, Thm.pretty_thm ctxt' thm'1],
                                                             item [str "property:", brk 1, Thm.pretty_thm ctxt' prop]])
                                                        end)
                                                   | NONE => (1, thm'1))
                            val thm'3 =
                                 if is_reasoning_goal
                                 then thm'2 |> Thm.permute_prems 0 i
                                            |> Phi_Reasoner.reason NONE (SOME delt)
                                                                   (Config.map Phi_Reasoner.trace (fn i=>i-1) ctxt')
                                            |> (fn SOME th => th
                                                 | NONE => raise Automation_Fail (fn () =>
                                                    let open Pretty
                                                     in [para "Fail to reason a compulsory antecedent",
                                                         Syntax.pretty_term ctxt' (Logic.nth_prem (i+1, Thm.prop_of thm'2))]
                                                    end))
                                            |> Thm.permute_prems 0 (~i)
                                  (*| Oblg => Conv.gconv_rule (
                                                Raw_Simplifier.rewrite ctxt' false @{thms' \<A>_template_condition_def}
                                             ) (i+1) thm'2*)
                                 else thm'2
                         in (if is_reasoning_goal then i else i + delt, thm'3)
                        end) (Thm.nprems_of template) positioned_props
                    |> snd
                    |> Phi_Help.beta_eta_contract
          val pattern = (case action
                           of Reasonig_Rule (_, (pats, _)) => SOME (map fst pats)
                            | Attributes _ => NONE
                            | No_Action => NONE)
          val rules' = case pass of SOME (ps, _) => ps (single o default_simplify pattern ctxt', pos, ctxt') rule'1
                                  | NONE => single (default_simplify pattern ctxt' rule'1)

          val binding = Option.map (fn (vs, b') =>
                  let val facts = Context.cases Global_Theory.facts_of Proof_Context.facts_of ctxt
                      fun varify_binding i b =
                        let val b' = if i = 0 then b else Binding.suffix_name ("_" ^ string_of_int i) b
                            val iname = Context.cases Sign.full_name Proof_Context.full_name ctxt b'
                         in if Facts.defined facts iname
                            then varify_binding (i+1) b
                            else b
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
                              of SOME (_, tm) => Binding.qualify true (short_name_of_tyop tm handle Match => err ())
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
      (case action
         of Reasonig_Rule ((mode, priority), (pats, blacklists)) =>
            let val (rules', (mode', priority'), (pats', blacklists'), guard', ctxt) =
                    case pass of SOME (_, ps) => ps template_pos (rules', (mode, priority), (pats, blacklists), NONE, ctxt)
                               | NONE => (rules', (mode, priority), (pats, blacklists), NONE, ctxt)
             in Phi_Reasoner.add_rules (map (fn rule =>
                          ([rule], template_pos, mode', priority', pats', blacklists', guard') ) rules') ctxt
            end
          | Attributes attrs =>
              let fun app attr = uncurry (Thm.apply_attribute (Attrib.attribute ctxt' attr))
               in fold (curry (snd o fold app attrs)) rules' ctxt
              end
          | No_Action => ctxt)
   |> (case binding of NONE => I
          | SOME b =>
                perhaps (try (Context.mapping (snd o Global_Theory.note_thms "" ((b, []), [(rules',[])]))
                                              (snd o Proof_Context.note_thms "" ((b, []), [(rules',[])]))))
                        (*It is not a Local_Theory.note here because the instantiation usually happens
                          inside an attribute and when a locale is interpreted, the attribute will be replayed.*)
                        (*I want to support lazy instantiation, but, to provide this, the Proof.context
                          has to be involved in the closure and that would consume a lot of memory.
                          Perhaps we could use the mechanism of dynamic fact, I am not sure which is better,
                          some test is required.*)
      )
    ) end
      handle Automation_Fail prt => (
        Phi_Reasoner.warn_pretty ctxt 2 (Pretty.chunks o prt) ;
        ctxt))
  | invoke_template_action _ (Free_Action action) arg ctxt = action arg ctxt
      handle Automation_Fail prt => (
        Phi_Reasoner.warn_pretty ctxt 2 (Pretty.chunks o prt) ;
        ctxt)

fun invoke_template ((deps, pos, action) : template) =
      check_dependencies deps (invoke_template_action pos action)

fun add_template invoke_on_existing_instantiations (template : template) ctxt =
  let val _ = Phi_Reasoner.info_pretty_generic ctxt 1 (fn () => let open Pretty
               in chunks (str "Registered reasoning rule template depending on " ::
                    map (fn NONE => item [str "_"]
                          | SOME pp => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt pp])
                        (#1 template))
              end)

      fun invk_on_existing_instantiations ctxt =
        let val existing_ins = existing_instantiations_of_parameters ctxt (#1 template)
         in fold (fn (env,rules) => invoke_template_action (#2 template)
                                                           (#3 template)
                                                           (#2 template, (env, rules))
                 ) existing_ins ctxt
        end
      val template' = trim_template template
      val id = serial ()
      val thy = Context.theory_of ctxt
      fun negatize_param param =
            let val idx = maxidx_of_term param
             in if idx >= 0 then Logic.incr_indexes ([],[],~1-idx) param else param
            end

      val compact_deps = map_filter I (#1 template)
      val ty_frees = fold (fold_types Term.declare_typ_names) compact_deps Name.context
      val tm_frees = fold Term.declare_term_frees compact_deps Name.context
      val ty_vars = fold Term.add_tvars compact_deps []
      val tm_vars = fold Term.add_vars compact_deps []
      val (ty_fixes_names, _) = fold_map Name.variant (map (fst o fst) ty_vars) ty_frees
      val (tm_fixes_names, _) = fold_map Name.variant (map (fst o fst) tm_vars) tm_frees
      val tm_fixes = Vartab.build (fold2 (fn (N,Ty) => fn fix => Vartab.update_new (N, (Ty, Free (fix, Ty)))) tm_vars tm_fixes_names)
      val ty_fixes = Vartab.build (fold2 (fn (N,S) => fn fix => Vartab.update_new (N, (S, TFree (fix, S)))) ty_vars ty_fixes_names)
      fun tm_fixes_of tm = Vartab.build (fold (fn (N,_) => Vartab.update_new (the (Vartab.lookup_key tm_fixes N))) (Term.add_vars tm []))
      fun ty_fixes_of tm = Vartab.build (fold (fn (N,_) => Vartab.update_new (the (Vartab.lookup_key ty_fixes N))) (Term.add_tvars tm []))
      val compact_deps = filter (fn dep => forall (fn d =>
              pointer_eq (d,dep) orelse
              not (can (Pattern.match thy (d, dep)) (ty_fixes_of dep, tm_fixes_of dep))
            ) compact_deps
          ) compact_deps
      |> @{print}

   in ctxt
   |> Templates.map (
        fold (fn param => Net.insert_term_safe template_eq (param, (id, negatize_param param, template'))
        ) compact_deps
      )
   |> invoke_on_existing_instantiations ? invk_on_existing_instantiations
  end

fun invoke_automations_on_property (pos, property) ctxt =
  let val idx = Thm.maxidx_of property
      val prop_concl = Thm.concl_of property
   in Net.unify_term (Templates.get ctxt) prop_concl
   |> filter (fn (_,param,_) =>
        is_some (Seq.pull (Unify.hounifiers (ctxt, Envir.empty idx, [(param, prop_concl)]))))
   |> distinct template_eq
   |> (fn templates =>
        fold (fn (_,_,template) => invoke_template template (pos, property)) templates ctxt)
  end

(*fun list_functors ctxt =
  Net.unify_term (Properties.get ctxt) (net_encode_phityp (Var(("uu",0),TVar(("'uu",0),[]))))
    |> map (fn (tm,_,_) => Logic.incr_indexes ([],[],1) tm)*)

(* fun is_a_registered_functor_i thy net the_functor =
  let val key = net_encode_phityp the_functor
   in Net.match_term net key
        |> exists (fn (pat, _) => Pattern.matches thy (pat, the_functor))
  end *)

val adding_property = Attrib.setup_config_bool \<^binding>\<open>\<phi>adding_property\<close> (K true)

fun add_property (pos,property) ctxt =
  let val thy = Context.theory_of ctxt
      val prop_concl = Thm.concl_of property
      (*val key_phityp = net_encode_phityp phityp'*)
      exception SKIP
      fun chk_clashes ctxt =
        let val net = Properties.get ctxt
            val clashes = Net.unify_term net prop_concl
                       |> filter (fn (_, prop') => Pattern.matches thy (prop_concl, Thm.concl_of prop')
                                            orelse Pattern.matches thy (Thm.concl_of prop', prop_concl))
         in if null clashes then ctxt
            else let open Pretty
                 val ctxt' = Context.proof_of ctxt
             in warning (string_of (chunks (
                  [block (text "The given property either covers or is covered by other existing properties."),
                   block (text "Given property:" @ [brk 1,
                          Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt property]),
                   block [str "Clashes", brk 1,
                          chunks (map (fn (pos,rule) => block (
                                     here pos @ [Syntax.pretty_term ctxt' (Thm.prop_of rule)]
                                   )) clashes)],
                   para "We prohibit redundancy of \<phi>-type properties as the redundancy \
                       \would be multiplied by template instantiation.\n\
                       \No automation will be invoked on this.\n\
                       \Instead, you should provide the most general rule and, if you want, \
                       \specialized (branched) reasoning on its antecedents."]
                 ))) ;
                raise SKIP
            end
        end
   in ctxt
   |> chk_clashes
   |> invoke_automations_on_property (pos, property)
   |> Properties.map (Net.insert_term property_eq (prop_concl, (pos, Thm.trim_context property)))
                    (*|> insert_term false (key_phityp, (phityp',pos,Drule.dummy_thm))*)
   handle SKIP => ctxt
 (* handle Net.INSERT => let open Pretty
      val term = Context.cases Syntax.pretty_term_global Syntax.pretty_term
       in error (string_of (chunks [
              block [str "On functor ", term ctxt the_functor,
                     str ", the following property has already been registered"],
              term ctxt (Thm.concl_of property)
            ]))
      end *)
 end

fun add_property_kinds ks thy =
  let fun add_prop k pos rules ctxt =
        let val thy = Context.theory_of ctxt
            val rules' = filter (fn rule => Pattern.matches thy (k, Thm.concl_of rule)) rules
         in fold (curry add_property pos) rules' ctxt
        end
   in thy
   |> Property_Kinds.map (fold ((fn k =>
        Net.insert_term (Pattern.equiv thy) (k, k)) o trim_modifiers) ks)
   |> Context.theory_map (fold (fn k =>
        let val k' = trim_modifiers k
            val name = Term.term_name (Term.head_of k')
         in Phi_Reasoner.add_pass ("\<phi>type-operator$" ^ name, k,
              fn pos => fn (rules, mode, pats, guard, ctxt) =>
                           (rules, mode, pats, guard,
                            if Config.get_generic ctxt adding_property
                            then add_prop k pos rules ctxt
                            else ctxt))
        end
      ) ks)
  end


fun setup_rule_generation (template_pos,(raw_dependencies,pass),(b,gen)) rule0 ctxt =
  let val thy = Context.theory_of ctxt
      val rule = normalize rule0
      val is_prop = check_property thy
      fun get_prop_kinds (TM::L) =
           let val base = case get_prop_kinds L of [NONE] => [] | L => L
            in is_prop TM :: base
           end
        | get_prop_kinds [] = []
      val prop_kinds = case raw_dependencies
                         of SOME deps => List.map (Option.map (assert_property_kind thy)) deps
                          | NONE => let val prems = map Phi_Help.strip_meta_hhf (Thm.prems_of rule)
                                        val used = Term.add_frees (Thm.prop_of rule) [] |> map fst
                                        val fixes = burrow (map Free o burrow_fst (Name.variant_list used o map (prefix "%"))) (map #1 prems)
                                        val prems' = map2 (fn (_,_,x) => fn fixes => subst_bounds (rev fixes, x)) prems fixes
                                        val inst = Phi_Help.instantiate_higher_order_var [] prems'
                                        val prems'1 = map ( Term_Subst.instantiate (TVars.empty, inst)
                                                         #> Phi_Help.beta_eta_contract_term ) prems'
                                     in get_prop_kinds prems'1
                                    end
      val template = (prop_kinds, template_pos, Instantiate_Rule (rule, pass, gen, b))
   in ctxt
   |> add_template true template
  end

(** Interfaces for Automation over Property **)

val rule_template_pass__sender : (rule_generation_pass * Phi_Reasoner.rule_pass) option Unsynchronized.ref
      = Unsynchronized.ref NONE
val rule_template_pass__sender_locker = Synchronized.var "rule_template_pass__sender_locker" ()


val _ = Theory.setup (

  Attrib.setup \<^binding>\<open>\<phi>type_property\<close> (Scan.succeed (Thm.declaration_attribute (curry add_property Position.none)))
    "Declare a \<phi>-type property that will be used to instantiate automation"

#>Attrib.setup \<^binding>\<open>\<phi>reason_template\<close> (
    Phi_Reasoner.attr_syntax
      (Scan.option (Scan.lift (Args.$$$ "name" |-- Parse.position Parse.long_ident))
       -- Scan.lift (Scan.option (
             \<^keyword>\<open>requires\<close> |--
                (Parse.and_list (Scan.repeat (  Args.$$$ "_" >> K NONE
                                             || Parse.term >> SOME)) >> flat)))
       -- Scan.option (Scan.lift (Args.$$$ "pass" |-- \<^keyword>\<open>:\<close> |-- Parse.ML_source))
       -- Scan.option Attrib.attribs)
      (fn (pos, mode, (priority, group), (((raw_binding, raw_dependencies), pass_src),attribs), pats, guard) =>
        Thm.declaration_attribute (fn thm => fn ctxt =>
          let val ctxt' = Context.proof_of ctxt
              val (_, ctxt_parse) = Variable.import true [thm] ctxt'
              val read_props = Variable.export_terms ctxt_parse ctxt' o
                               Syntax.read_props (Proof_Context.set_mode Proof_Context.mode_pattern ctxt_parse)
              val read_terms = Variable.export_terms ctxt_parse ctxt' o
                               Syntax.read_terms ctxt_parse
              val dependencies = Option.map (burrow_options read_props) raw_dependencies
              fun chk_binding_target (Var (v,_)) = v
                | chk_binding_target X =
                      error (let open Pretty in string_of (
                            block (text "The binding of the template instances must binds to a \
                                        \variable in the template that will be instantaited to to \<phi>-type.\
                                        \ However, the given binding target is not a variable," @
                                   [brk 1, Syntax.pretty_term ctxt' X])
                          ) end)
                    
              val binding = Option.map (fn (long_name, pos) =>
                      let val (qualifiers, name) = Phi_Help.split_last (Long_Name.explode long_name)
                       in (map chk_binding_target (read_terms qualifiers), Binding.make (name, pos))
                      end
                    ) raw_binding

              val _ = case guard of NONE => ()
                         | _ => error "No guard is allowed here"
              val pass = Option.map (fn src =>
                    let val _ = Synchronized.change rule_template_pass__sender_locker (fn () => (
                                  ML_Context.expression (Input.pos_of src)
                                    (ML_Lex.read "Phi_Type_Template_Properties.rule_template_pass__sender := SOME (" @
                                     ML_Lex.read_source src @
                                     ML_Lex.read ")")
                                    ctxt;
                                  ()))
                        val pass = the (!rule_template_pass__sender)
                        val _ = rule_template_pass__sender := NONE
                     in pass
                    end
                  ) pass_src
              val gen = case (attribs, priority, pats)
                          of (SOME (attrs as _ :: _), 100, ([], [])) => Attributes attrs
                                (*100 is the default priority of \<phi>-LPR. Here we use it to trickily mean
                                  an explicit priority is not given*)
                           | (SOME [], 100, ([], [])) => No_Action
                           | (SOME _, _, _) =>
                              error "Prioirty and binding patterns are senseless and not allowed to\
                                    \ be given once the attributes are given."
                           | (NONE, _, _) =>
                              Reasonig_Rule ((mode, (priority,group)), pats)
           in setup_rule_generation (pos,(dependencies,pass),(binding,gen)) thm ctxt
          end)
      ))
  "declare a \<phi>reasoning rule template which will be instantiated automatically when the depended \
  \properties are given for a \<phi>-type (operator).\n\
  \The properties must be in the leading antecedents and must be about an identical \<phi>-type \
  \(of potential different type instantiations so therefore be represented by different fixed free variables).\n\
  \It is able to parse the depended properties from the leading antecedents greedily for all possible, \
  \and may caputre more dependencies than the expected. If so, you can specify the exact dependency \
  \explicilty by [[\<phi>reason_template requires \<open>dependencies\<close>]]"

#> let fun rule_attribute f (x, th) =
            if Thm.is_free_dummy th
            then (NONE, NONE)
            else (SOME x, SOME (f x th))
 in Attrib.setup \<^binding>\<open>\<phi>simplify_reasoning_rule\<close> (
    Scan.succeed (rule_attribute (default_simplify NONE o Context.proof_of)))
  "Simplify a reasoning rule, using the same process as that in template instantiation.\n\
  \The conclusion of the rule is remained untouched and any antecedents are simplified and reduced\
  \if possible. \<open>NO_SIMP\<close> tag is recognized and supresses the simplification on the protected terms."
end
)


end 

