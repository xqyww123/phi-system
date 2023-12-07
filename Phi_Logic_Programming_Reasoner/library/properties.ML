(*
\<^item> Storage of properties.
\<^item> Deriving rules from property-conditioned templates
*)

signature PHI_TYPE_TEMPLATE_PROPERTIES = sig

(*** Algebraic Properties ***)

type property_pattern = term (*pattern of the property, of type Pure.prop*)
type property_pattern_i = term

val check_property : theory -> property_pattern -> property_pattern_i option
                     (*returns normalized form if it is a registered property*)
val assert_property_pattern : theory -> property_pattern -> property_pattern_i
val add_property_kinds : term list -> theory -> theory

val lookup_properties_match : Context.generic -> property_pattern_i -> (Position.T * thm) list
val lookup_properties_unify : Context.generic -> property_pattern_i -> (Position.T * thm) list
val add_property_instance : Position.T * thm -> Context.generic -> Context.generic
(*val list_functors : Context.generic -> term list*)

val invoking_instantiations : bool Config.T (*provides a controller to temporarily disable
  instantiations of templates that are invoked when property instances are given.*)
val adding_property : bool Config.T (*controls if for any new reasoning rules registered to \<phi>-LPR,
  automatically checking whether the rule matches certain known form of properties and
  if so registering it as an instance of the property and invoking the related automation (if the
  `invoking_instantiations` is turned on)*)

(*** The Framework for Automation based on Algebraic Property ***)

(** Types **)

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
                                PLPR_Rule_Gen.instantiation_action * instance_binding option
          | Free_Action of free_template_action (*accept Automation_Fail*)

type template = parameters * Position.T (*position of the template*) * template_action

(** Basic Operations: Add, List, Invoke **)

val add_template : bool (*if to invoke on the existing instantiations if any*)
                -> template -> Context.generic -> Context.generic
val list_templates : Context.generic -> template list

type template_argument = Position.T (*position of the property*) * thm (*property*)
val invoke_template : template -> template_argument -> Context.generic -> Context.generic
val invoke_instantiations_on_property : template_argument -> Context.generic -> Context.generic
    (*invokes any template depending on the given property and of all dependencies satisfied*)

(** Auxiliaries **)

val pretty_template : Context.generic -> template -> Pretty.T
val pretty_templates : Context.generic -> (priority * template) Ord_List.T Symtab.table -> Pretty.T

(*** Developer Tools ***)

(*Debugging use only*)
val assert_derived_properties : theory -> (thm * term) list -> unit

end

structure PLPR_Template_Properties : PHI_TYPE_TEMPLATE_PROPERTIES = struct

exception Automation_Fail = PLPR_Rule_Gen.Generation_Fail

type property_pattern = term
type property_pattern_i = term

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
                    \\<open>Phi_Type.add_property_kind\<close> to register it.")))
    end

fun assert_property_pattern thy =
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

datatype template_action =
            Instantiate_Rule of thm * (rule_generation_pass * Phi_Reasoner.rule_pass) option *
                                PLPR_Rule_Gen.instantiation_action * instance_binding option
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
                Instantiate_Rule (Thm.trim_context rule, pass, PLPR_Rule_Gen.trim_action inst, b)
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

fun lookup_properties_match ctxt =
  let val properties = Properties.get ctxt
   in fn pattern =>
      Net.match_term properties pattern
   |> filter (fn (_, th) => Pattern.matches (Context.theory_of ctxt) (pattern, Thm.concl_of th))
  end

(*no transfer*)
fun lookup_property_unify' ctxt =
  let val properties = Properties.get ctxt
   in fn additions => fn env => fn pattern =>
  let val Envir.Envir {maxidx, tenv, tyenv} = env
      val filter = map_filter (fn (pos, th) =>
                      let val concl = Thm.concl_of th
                                   |> maxidx >= 0 ? Logic.incr_indexes ([], [], maxidx+1)
                          val cidx = if maxidx >= 0 then Thm.maxidx_of th + maxidx + 1 else Thm.maxidx_of th
                          val env' = Envir.Envir {maxidx = cidx, tenv=tenv, tyenv=tyenv}
                       in case Seq.pull (Unify.hounifiers (ctxt, env', [(pattern, concl)]))
                       of SOME env => SOME (Seq.map fst (uncurry Seq.cons env), (pos,th))
                        | NONE => NONE
                      end)
   in union (pointer_eq o apply2 (snd o snd))
            (filter additions)
            (filter (Net.unify_term properties pattern))
  end
  end

fun lookup_properties_unify ctxt =
  let val lookup = lookup_property_unify' ctxt
      val thy = Context.theory_of ctxt
   in fn pattern =>
      lookup [] (Envir.empty (Term.maxidx_of_term pattern)) pattern
        |> map (snd #> apsnd (Thm.transfer thy))
  end

(* Invoke template instantiation *)

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
            fn SOME param => Term.could_unify (param, prop_concl)
             | NONE => false) params
      then let val lookup = lookup_property_unify' ctxt
               fun get_property env (SOME p) = map (apsnd SOME) (lookup [(pos,property)] env p)
                 | get_property env NONE = [(Seq.single env, NONE)]
               val ruless = instantiations_of_parameters get_property ctxt params
                         |> filter (exists (fn SOME (_, th) => pointer_eq (th, property) | _ => false) o snd)
            in fold (fn rules => fn ctxt =>
                          action (pos,rules) ctxt
                          handle Automation_Fail (lev, msg) =>
                            let open Pretty
                                val msg' = msg ()
                             in if null msg' then ()
                                else Phi_Reasoner.warn_pretty ctxt lev (fn () => (chunks (str "Automation Fail:" :: msg'))) ;
                              ctxt
                            end
                    ) ruless ctxt
           end
      else ctxt)
      handle Dep => ctxt
  end

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes

fun invoke_template_action template_pos (Instantiate_Rule (template, pass, action, bind))
                           (pos, (env, positioned_props)) ctxt =
      PLPR_Rule_Gen.invoke_generation ((template_pos, template), pass, action, bind)
                                      (pos, env, positioned_props) ctxt
  | invoke_template_action template_pos (Free_Action action) arg ctxt = (
      Phi_Reasoner.info_pretty_generic ctxt 1 (fn () => let open Pretty in
          block (text "invoking free template" @ [brk 1] @ here template_pos)
        end) ;
      action (apsnd (apsnd (map (Option.map (apsnd (Thm.transfer (Context.theory_of ctxt)))))) arg) ctxt
      handle Automation_Fail (lev, prt) => (
        Phi_Reasoner.warn_pretty ctxt lev (Pretty.chunks o prt) ;
        ctxt)
      )

fun invoke_template ((deps, pos, action) : template) =
( case action of Instantiate_Rule (_, _, _, SOME (_, b)) =>
    if Binding.name_of b = "module_mapper\<^sub>d\<^sub>a\<^sub>_\<^sub>b" then () else () (*debug usage*)
    | _ => ();

  check_dependencies deps (invoke_template_action pos action)

)

fun add_template invoke_on_existing_instantiations (template : template) ctxt =
  let val _ = Phi_Reasoner.info_pretty_generic ctxt 1 (fn () => let open Pretty
               in chunks (str "Registering reasoning rule template depending on " ::
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

   in ctxt
   |> Templates.map (
        fold (fn param => Net.insert_term_safe template_eq (param, (id, negatize_param param, template'))
        ) compact_deps
      )
   |> invoke_on_existing_instantiations ? invk_on_existing_instantiations
  end

fun invoke_instantiations_on_property (pos, property) ctxt =
  let val prop_concl = Thm.concl_of property
      val templates = Templates.get ctxt
   in Net.unify_term templates prop_concl
   |> filter (fn (_,param,_) => Term.could_unify (param, prop_concl))
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
val invoking_instantiations = Attrib.setup_config_bool \<^binding>\<open>\<phi>invoking_property_instantiation\<close> (K true)

fun add_property_instance (pos,property) ctxt =
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
      val property = Thm.trim_context property
   in ctxt
   |> chk_clashes
   |> Properties.map (Net.insert_term property_eq (prop_concl, (pos, property)))
                    (*|> insert_term false (key_phityp, (phityp',pos,Drule.dummy_thm))*)
   |> Config.get_generic ctxt invoking_instantiations ? invoke_instantiations_on_property (pos, property)
      (*Note: must ensure the property theorem inserted into the Net Data must be pointer-equal to
        the one sent to \<open>invoke_instantiations_on_property\<close>*)
                    
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
         in fold (curry add_property_instance pos) rules' ctxt
        end
   in thy
   |> Property_Kinds.map (fold ((fn k =>
        Net.insert_term (Pattern.equiv thy) (k, k)) o trim_modifiers) ks)
   |> Context.theory_map (fold (fn k =>
        let val k' = case trim_modifiers k
                       of Const(\<^const_name>\<open>Pure.term\<close>, _) $ X => X
                        | X => X
            val name = case Term.head_of k'
                         of Const(N,_) => N
                          | _ => error "Bad Property: must be a predicate"
         in Phi_Reasoner.add_pass (Const("property$" ^ name, TFree("",[])), k,
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
      fun trim_Pure_term (\<^Const>\<open>Pure.term \<^Type>\<open>prop\<close>\<close> $ X) = X
        | trim_Pure_term (\<^Const>\<open>Pure.term \<^Type>\<open>bool\<close>\<close> $ X) = HOLogic.Trueprop $ X
        | trim_Pure_term X = X
      fun get_prop_kinds (TM::L) =
           let val base = case get_prop_kinds L of [NONE] => [] | L => L
            in is_prop (trim_Pure_term TM) :: base
           end
        | get_prop_kinds [] = []
      val prop_kinds = case raw_dependencies
                         of SOME deps => List.map (Option.map (assert_property_pattern thy)) deps
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


val _ = Theory.setup (

  Attrib.setup \<^binding>\<open>\<phi>type_property\<close> (Scan.succeed (Thm.declaration_attribute (curry add_property_instance Position.none)))
    "Declare a \<phi>-type property that will be used to instantiate automation"

#>Attrib.setup \<^binding>\<open>\<phi>reason_template\<close> (
    Phi_Reasoner.attr_syntax
      (Scan.option (Scan.lift (Args.$$$ "name" |-- Scan.option \<^keyword>\<open>:\<close> |-- Parse.position Parse.long_ident))
       -- Scan.lift (Scan.option (
             \<^keyword>\<open>requires\<close> |--
                (Parse.and_list (Scan.repeat (  Args.$$$ "_" >> K NONE
                                             || Parse.term >> SOME)) >> flat)))
       -- Scan.option (Scan.lift (Args.$$$ "pass" |-- \<^keyword>\<open>:\<close> |-- Parse.ML_source))
       -- Scan.option Attrib.attribs)
      (fn (pos, mode, prio_group, (((raw_binding, raw_dependencies), pass_src),attribs), pats, guard) =>
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
              val pass = PLPR_Rule_Gen.parse_pass ctxt pass_src
              val gen = PLPR_Rule_Gen.parse_action (mode, prio_group, pats, attribs)
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
)


(** Developer Tools **)

fun assert_derived_properties thy th_prop_pairs =
  List.app (fn (th, prop) =>
    if Pattern.equiv thy (Thm.prop_of th, prop) then ()
    else let open Pretty in
      error (string_of (chunks [
        para "The derived property",
        Thm.pretty_thm_global thy th,
        para "fails to meet the desired assertion",
        Syntax.pretty_term_global thy prop
      ]))
    end
  ) th_prop_pairs

end

val assert_derived_properties = PLPR_Template_Properties.assert_derived_properties

