(*
\<^item> Storage of properties.
\<^item> Deriving rules from property-conditioned templates
*)

signature PHI_TYPE_TEMPLATE_PROPERTIES = sig

(* Algebraic Properties *)

type property_name = string

val is_a_kind_of_property : theory -> property_name -> bool
val assert_property_kind : theory -> property_name -> unit
val add_property_kind : property_name -> (term -> term) -> theory -> theory

val lookup_property_exact : Context.generic -> term (*pattern of the \<phi>-type or type operator*)
                         -> property_name -> (term * Position.T * thm) list
val lookup_property_match : Context.generic -> term (*same as the above*)
                         -> property_name -> (term * Position.T * thm) list
val lookup_property_unify : Context.generic -> term (*same as the above*) -> property_name -> (term * Position.T * thm) list
val add_property : term * Position.T * thm -> Context.generic -> Context.generic
(*val list_functors : Context.generic -> term list*)

val adding_property : bool Config.T (*controlling if automatically for any new reasoning rules,
  register to the property DB and invoking the related automation*)

structure Template_Inst_SS : SIMPSET (*simpset for generating reasoning rules*)

(* The Framework for Automation based on Algebraic Property *)

datatype instantiation_action =
            Reasonig_Rule of (Phi_Reasoner.mode * priority) *
                             ( (Phi_Reasoner.pattern * priority option) list * Phi_Reasoner.pattern list )
          | Attributes of Token.src list

type dependencies = property_name option list (*corresponding to the premises of the template rule
          one to one respectively, and being NONE if the premise in the corresponded position is
          not a property for instantiating*)

type rule_generation_pass = (thm -> thm list) (*default generation process*)
                          * Position.T (*where the template is instantiated*)
                          * Proof.context
                         -> thm -> thm list

type free_template_action =
        term (*\<phi>-type (operator)*) * Position.T * thm (*properties*) option list -> Context.generic -> Context.generic

datatype template_action =
            Instantiate_Rule of thm * rule_generation_pass option *
                                instantiation_action * Binding.binding option
          | Free_Action of free_template_action (*accept Automation_Fail*)

type template = dependencies * Position.T * template_action

val add_template : bool (*if to invoke on the existing instantiations if any*)
                -> priority * template -> Context.generic -> Context.generic
val list_templates : Context.generic -> (priority * template) Ord_List.T Symtab.table

val pretty_template : Context.generic -> template -> Pretty.T
val pretty_templates : Context.generic -> (priority * template) Ord_List.T Symtab.table -> Pretty.T

type template_argument = term (*\<phi>-type (operator)*) * Position.T * thm (*property*)
val invoke_template : template -> template_argument -> Context.generic -> Context.generic
val invoke_automations_on_property : template_argument -> Context.generic -> Context.generic
    (*invokes any template depending on the given property and of all dependencies satisfied*)

(* Internal Interfaces *)

val rule_template_pass__sender : rule_generation_pass option Unsynchronized.ref

end

structure Phi_Type_Template_Properties : PHI_TYPE_TEMPLATE_PROPERTIES = struct

exception Automation_Fail = Phi_Type_Algebra.Automation_Fail

type property_name = string

(*** Algebraic Property & Automation ***)

(** Property Kind **)

structure Property_Kinds = Theory_Data (
  type T = (term -> term (*extract the type operator from the property spec*)) Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun is_a_kind_of_property thy k = Symtab.defined (Property_Kinds.get thy) k

fun err_not_a_property_kind k =
      error (k ^ " is not a known \<phi>-type property. Please use ML function \
                 \\<open>Phi_Type_Algebra.add_property_kind\<close> to register it.")

fun assert_property_kind thy k =
      if is_a_kind_of_property thy k then () else err_not_a_property_kind k

fun extract_type_operator_from_property thy k = Symtab.lookup (Property_Kinds.get thy) k
fun extract_type_operator_from_property1 thy k =
      case extract_type_operator_from_property thy k of SOME ret => ret
         | NONE => err_not_a_property_kind k

(** Property DB **)

type free_template_action = term (*\<phi>-type (operator)*) * Position.T * thm (*property*) option list
                         -> Context.generic -> Context.generic

type dependencies = property_name option list

type rule_generation_pass = (thm -> thm list) * Position.T * Proof.context -> thm -> thm list

datatype instantiation_action =
            Reasonig_Rule of (Phi_Reasoner.mode * priority) *
                             ( (Phi_Reasoner.pattern * priority option) list * Phi_Reasoner.pattern list )
          | Attributes of Token.src list

datatype template_action =
            Instantiate_Rule of thm * rule_generation_pass option *
                                instantiation_action * Binding.binding option
          | Free_Action of free_template_action

type template = dependencies * Position.T * template_action
type template_argument = term (*\<phi>-type (operator)*) * Position.T * thm (*property*)

fun property_eq ((t1,_,th1),(t2,_,th2)) = (t1 aconv t2) andalso Thm.eq_thm_prop (th1,th2)

structure Properties = Generic_Data (
  type T = (term (*\<phi>type*) * Position.T * thm) Net.net 
  val empty = Net.empty
  val merge = Net.merge property_eq
)

fun prop_table_order k ((p1,_),(p2,_)) = if p1 = p2 then raise Symtab.DUP k else int_ord (p1,p2)

structure Property_Templates = Generic_Data (
  type T = (priority * template) Ord_List.T Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (fn k => uncurry (Ord_List.union (prop_table_order k)))
)

val list_templates = Property_Templates.get 

fun pretty_template ctxt ((deps, pos, action) : template) =
  let open Pretty
   in chunks (
        (case action of Instantiate_Rule (rule, _, _, b) =>
                [block ([str "Template", brk 1] @
                        the_default [] (Option.map (single o Binding.pretty) b) @
                        here pos @
                        [brk 1, Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt rule]) ]
            | Free_Action _ =>
                [block ([para "ML automation", brk 1] @ here pos)]) @
        [para "depending on:"] @
        map (fn NONE => item [str "_"]
              | SOME dep => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt
                                                (Const(dep, Term.dummyT))]) deps
     )
  end

fun pretty_templates ctxt (table : (priority * template) Ord_List.T Symtab.table) =
  let val templates = Symtab.fold (fold (insert pointer_eq o snd) o snd) table []
      open Pretty
   in chunks (map (item o single o pretty_template ctxt) templates)
  end

fun trim_template ((deps, pos, act) : template) : template =
  (deps, pos,
  case act of Instantiate_Rule (rule, pass, inst, b) =>
                Instantiate_Rule (Thm.trim_context rule, pass,
                  (case inst of Reasonig_Rule _ => inst
                              | Attributes srcs => Attributes (map Token.trim_context_src srcs)), b)
            | Free_Action act => Free_Action act)

fun close_phitype_operator phityp =
  let val i = maxidx_of_term phityp + 1
   in case Term.binder_types (Term.fastype_of phityp)
   of [] => phityp
    | L => fold_index (fn (j,Ty) => fn Tm => Tm $ Var(("x",i+j), Ty)) L phityp
  end

fun net_encode_property_key (phityp, property_name) =
  Const("P", dummyT) $ close_phitype_operator phityp $ Const(property_name, dummyT)

(*fun net_encode_phityp phityp = Const("F", dummyT) $ phityp*)

fun get_property_name thm =
  if Thm.is_dummy thm then ""
  else fst (Term.dest_Const (Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of thm))))

fun lookup_property_exact ctxt phityp0 property_name =
  let val thy = Context.theory_of ctxt
      val phityp = Phi_Help.beta_eta_contract_term (close_phitype_operator phityp0)
   in Net.match_term (Properties.get ctxt) (net_encode_property_key (phityp, property_name))
      |> filter (fn (tm, _, _) => Pattern.equiv thy (tm, phityp))
  end

fun lookup_property_match ctxt phityp0 property_name =
  let val phityp = Phi_Help.beta_eta_contract_term (close_phitype_operator phityp0)
   in Net.match_term (Properties.get ctxt) (net_encode_property_key (phityp, property_name))
   |> filter (fn (tm, _, _) => Pattern.matches (Context.theory_of ctxt) (tm, phityp))
  end

fun lookup_property_unify ctxt phityp0 property_name =
  let val phityp = Phi_Help.beta_eta_contract_term (close_phitype_operator phityp0)
   in Net.unify_term (Properties.get ctxt) (net_encode_property_key (phityp, property_name))
   |> filter (fn (tm, _, _) => case Seq.pull (Unify.hounifiers (ctxt, Envir.init, [(tm, phityp)]))
                                 of SOME _ => true
                                  | NONE => false)
  end

(* Invoke template instantiation *)

structure Template_Inst_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>simp_for_\<phi>TA_rule_generation\<close>
  val comment = "Rules simplifying the reasoning rules instantiated from templates."
  val attribute = NONE
)

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes

fun check_dependencies deps action (the_functor0,pos,property) ctxt =
  let exception Dep
      val the_functor = Phi_Help.beta_eta_contract_term the_functor0
      val prop_name = get_property_name property
   in(if Thm.is_dummy property orelse member (op =) deps (SOME prop_name)
      then let fun cross_map _ [] = []
                 | cross_map f [h] = map single (f h)
                 | cross_map f (h::L) = let val L' = cross_map f L
                                         in maps (fn L'' => map (fn x => x :: L'') (f h)) L'
                                        end
               val get_rules = cross_map (
                    fn NONE => [NONE]
                     | SOME dep =>
                        if dep = "" then [SOME Drule.asm_rl]
                        else if dep = prop_name then [SOME property]
                        else case map (SOME o #3) (lookup_property_unify ctxt the_functor dep)
                          of [] => raise Dep
                           | L => L
                    )
               val ruless = get_rules deps
            in fold (fn rules => fn ctxt =>
                          action (the_functor,pos,rules) ctxt
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

fun invoke_template_action template_pos (Instantiate_Rule (template, pass, action, bind))
                           (tyop, pos, props) ctxt =
     (let val ctxt' = Context.proof_of ctxt
                   |> Config.put Phi_Reasoner_solve_obligation_and_no_defer 1
          fun fold_pad _ 0 _ x = x
            | fold_pad f n [] x = fold_pad f (n-1) [] (f NONE x)
            | fold_pad f n (h::L) x = fold_pad f (n-1) L (f h x)
          val rule'1 = (0, Thm.transfer' ctxt' template)
                    |> fold_pad (fn prop' => fn (i, thm) =>
                        let datatype mode = Reason | Oblg | Normal
                            val mode =
                                  case Logic.nth_prem (i+1, Thm.prop_of thm)
                                    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                          Const(\<^const_name>\<open>Action_Tag\<close>, _)
                                              $ _
                                              $ Const(\<^const_name>\<open>\<A>_template_reason\<close>, _)) => Reason
                                     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                          Const(\<^const_name>\<open>Premise\<close>, _)
                                              $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _)
                                              $ P) =>
                                        if exists_subterm (fn (Const(\<^const_name>\<open>\<A>_template_condition\<close>, _)) => true
                                                            | _ => false) P
                                        then Oblg
                                        else Normal
                                     | _ => Normal
                            val thm'1 = if mode = Reason
                                        then @{thm' Action_Tag_I} RSN (i+1, thm)
                                        else thm
                            val (delt,thm'2) = (case prop'
                                                  of SOME prop => ((Thm.nprems_of prop, prop RSN (i+1, thm'1))
                                                       handle THM _ => let open Pretty in
                                                          raise Automation_Fail (fn () =>
                                                            [block (text "Unification fails in instantiating the" @
                                                                   [brk 1, str (string_of_int (i+1)), str "th", brk 1] @
                                                                   text "antecedent of the template" @ [brk 1] @ here pos),
                                                             item [str "template:", brk 1, Thm.pretty_thm ctxt' thm'1],
                                                             item [str "property:", brk 1, Thm.pretty_thm ctxt' prop]])
                                                        end)
                                                   | NONE => (1, thm'1))
                            val thm'3 = case mode
                                  of Reason =>
                                      thm'2 |> Thm.permute_prems 0 i
                                            |> Phi_Reasoner.reason (SOME delt) true ctxt'
                                            |> (fn SOME th => th
                                                 | NONE => raise Automation_Fail (fn () =>
                                                    let open Pretty
                                                     in [para "Fail to reason a compulsory antecedent",
                                                         Syntax.pretty_term ctxt' (Logic.nth_prem (i+1, Thm.prop_of thm'2))]
                                                    end))
                                            |> Thm.permute_prems 0 (~i)
                                   | Oblg => Conv.gconv_rule (
                                                Raw_Simplifier.rewrite ctxt' false @{thms' \<A>_template_condition_def}
                                             ) 1 thm'2
                                   | _ => thm'2
                         in (if mode = Reason then i else i + delt, thm'3)
                        end) (Thm.nprems_of template) props
                    |> snd
                    |> Phi_Help.beta_eta_contract
          fun simplify ctxt rule =
                let val ((_, [rule'1]), ctxt'1) = Variable.import false [rule] ctxt
                    val ctxt's = Template_Inst_SS.enhance ctxt'1
                              |> Simplifier.del_cong @{thm' HOL.if_weak_cong}
                 in singleton (Variable.export ctxt'1 ctxt)
                      (  rule'1
                      |> Simplification_Protect.protect ctxt's
                      |> Phi_Reasoners.asm_lr_simplify true ctxt's
                      |> Simplification_Protect.unprotect ctxt's )
                end
          fun default_generation rule'1 =
            let val rule'2 = rule'1
                          (*|> do_reason*)
                          |> simplify ctxt'
                          |> Phi_Help.unique_flexflex ctxt'
             in (case Phi_Help.instantiate_higher_order_schematic_var' ~1 ctxt' rule'2
                     of SOME th => simplify ctxt' th
                      | NONE => rule'2)
                   |> Simplifier.rewrite_rule ctxt' @{thms' NO_SIMP_def}
                   |> normalize
                   |> single
            end
          val rules' = case pass of SOME ps => ps (default_generation, pos, ctxt') rule'1
                                  | NONE => default_generation rule'1
       in if null rules' then ctxt
       else (
       Phi_Reasoner.info_pretty ctxt' 1 (fn () => let open Pretty in
         chunks ([paragraph (text "Instantiate reasoning template" @ [brk 1] @
                             here template_pos)] @
                 (case action of Reasonig_Rule _ => []
                     | Attributes _ => map (fn rule => item [Thm.pretty_thm ctxt' rule]) rules'))
         end) ;
      (case action
         of Reasonig_Rule ((mode, priority), (pats, blacklists)) =>
              Phi_Reasoner.add_rules (map (fn rule =>
                          ([rule], template_pos, mode, priority, pats, blacklists, NONE) ) rules') ctxt
          | Attributes attrs =>
              let fun app attr = uncurry (Thm.apply_attribute (Attrib.attribute ctxt' attr))
               in fold (curry (snd o fold app attrs)) rules' ctxt
              end)
    |> (case bind of NONE => I
           | SOME b' =>
              let val facts = Context.cases Global_Theory.facts_of Proof_Context.facts_of ctxt
                  fun varify_binding i b =
                    let val b' = if i = 0 then b else Binding.suffix_name ("_" ^ string_of_int i) b
                        val iname = Context.cases Sign.full_name Proof_Context.full_name ctxt b'
                     in if Facts.defined facts iname
                        then varify_binding (i+1) b
                        else b
                    end
                  val b = varify_binding 0 (Binding.qualify true (short_name_of_tyop tyop) b')
               in perhaps (try (Context.mapping (snd o Global_Theory.note_thms "" ((b, []), [(rules',[])]))
                                                (snd o Proof_Context.note_thms "" ((b, []), [(rules',[])]))))
              end handle Match => I) )
      end
      handle Automation_Fail prt => (
        Phi_Reasoner.warn_pretty ctxt 2 (Pretty.chunks o prt) ;
        ctxt))
  | invoke_template_action _ (Free_Action action) triple ctxt = action triple ctxt
      handle Automation_Fail prt => (
        Phi_Reasoner.warn_pretty ctxt 2 (Pretty.chunks o prt) ;
        ctxt)

fun invoke_template ((deps, pos, action) : template) =
      check_dependencies deps (invoke_template_action pos action)

fun add_template invoke_on_existing_instantiations (priority, (template : template)) ctxt =
  let val _ = Phi_Reasoner.info_pretty_generic ctxt 1 (fn () => let open Pretty
                  val consts = Context.cases Sign.consts_of Proof_Context.consts_of ctxt
               in chunks (str "Registered reasoning rule template depending on " ::
                    map (fn NONE => item [str "_"]
                          | SOME pk =>
                               pk |> Consts.the_const consts |> Const
                                  |> Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt
                                  |> single |> item) (#1 template))
              end)

      fun invk_on_existing_instantiations ctxt =
        let val properties = Properties.get ctxt
            val existing_rules = map (Option.map (fn pk =>
                    Net.unify_term properties (net_encode_property_key (Var(("uu",0),TVar(("uu",0),[])), pk))
                  )) (#1 template)
            fun cross_product (SOME aa) bb =
                  maps (fn (ta,_,ra) =>
                      map_filter (fn (tb,rb) =>
                        case try (Pattern.unify ctxt (ta, Logic.incr_indexes ([],[],1) tb)) Envir.init
                          of SOME e => SOME (Envir.norm_term e ta, SOME ra :: rb)
                           | NONE   => NONE
                      ) bb
                  ) aa
              | cross_product NONE bb = map (apsnd (fn rb => NONE :: rb)) bb
            fun mk_existing_ins prev [] = []
              | mk_existing_ins prev (NONE::L) = mk_existing_ins (NONE::prev) L
              | mk_existing_ins prev (SOME h :: L) =
                    fold cross_product L (map (fn (tm,_,rule) => (tm, SOME rule :: prev)) h)
            val existing_ins = mk_existing_ins [] existing_rules
         in fold (fn (f,rules) => invoke_template_action (#2 template)
                                                         (#3 template)
                                                         (f, #2 template, rev rules)
                 ) existing_ins ctxt
        end
      val dependencies' = distinct (op =) (map_filter I (#1 template))
      val template' = trim_template template
   in ctxt
   |> Property_Templates.map (
        fold (fn prop_kind =>
          Symtab.map_default (prop_kind,[])
              (Ord_List.insert (prop_table_order prop_kind) (priority, template'))
        ) dependencies'
      )
   |> invoke_on_existing_instantiations ? invk_on_existing_instantiations
  end

fun invoke_automations_on_property phityp ctxt =
  let val prop_kind = get_property_name (#3 phityp)
   in case Symtab.lookup (Property_Templates.get ctxt) prop_kind
   of NONE => ctxt
    | SOME L => fold (fn (_,template) => invoke_template template phityp) L ctxt
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

fun add_property (phityp0,pos,property) ctxt =
  let val thy = Context.theory_of ctxt
      val phityp' = phityp0
                  |> Envir.beta_eta_contract
                  |> close_phitype_operator
                  |> Term.map_aterms ( (fn Var ((N,i),T) => Var ((N,~i-1),T) | T => T)
                                    #> map_types (map_type_tvar (fn ((N,i),S) => TVar ((N,~i-1),S))))
      val property_name = get_property_name property
      val key = net_encode_property_key (phityp', property_name)
      (*val key_phityp = net_encode_phityp phityp'*)
      exception SKIP
      fun insert_term (k''', (k,pos,v)) net =
        let val clashes = Net.unify_term net k'''
                       |> filter (fn (k', _, _) => Pattern.matches thy (k',k) orelse Pattern.matches thy (k,k'))
            val _ = if null clashes then ()
                    else let open Pretty
                        val ctxt' = Context.proof_of ctxt
                     in warning (string_of (chunks (
                           block [str "The property ", str property_name, str " of \<phi>-type ",
                                  Syntax.pretty_term ctxt' phityp0,
                                  str " either covers or is covered by other existing rules."] ::
                           str "We prohibit redundancy of \<phi>-type properties because it causes \
                               \a great amount of redundancy in the generated reasoning rules.\n\
                               \No automation will be invoked on this.\n\
                               \Instead, you should provide the most general rule and, if you want, \
                               \specialized (branched) reasoning on its antecedents." ::
                           map (fn (_,pos,rule) => block (
                               here pos @ [Syntax.pretty_term ctxt' (Thm.prop_of rule)]
                             )) clashes
                         ))) ;
                        raise SKIP
                    end
         in Net.insert_term property_eq (k''', (k,pos,v)) net
        end
   in ctxt
    |> Properties.map (insert_term (key, (phityp', pos, Thm.trim_context property)))
                    (*|> insert_term false (key_phityp, (phityp',pos,Drule.dummy_thm))*)
    |> invoke_automations_on_property (phityp0, pos, property)
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

fun add_property' pos property ctxt =
  let val thy = Context.theory_of ctxt
      val prop_spec = HOLogic.dest_Trueprop (Thm.concl_of property)
      val type_operator =
            case Term.strip_comb prop_spec
              of (Const(N, _), _)
                   => extract_type_operator_from_property1 thy N prop_spec
               | _ => error "The theorem is not a valid \<phi>-type property."
   in add_property (type_operator,pos,property) ctxt
  end

fun add_property_kind k extract thy =
  let val ty = case Sign.const_type thy k
                 of SOME T => T
                  | NONE => error (k ^ " is not a constant")
      fun mk_term ret i (Type ("fun", [T, U])) =
            mk_term (ret $ Var ((string_of_int i, 0),T)) (i+1) U
        | mk_term ret _ _ = ret
      val pat = HOLogic.Trueprop $ mk_term (Const(k,ty)) 0 ty
      fun add_prop pos rules ctxt =
        let val rules' =
              filter (fn rule => case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of rule))
                                   of Const (k', _) => k = k'
                                    | _ => false) rules
         in fold (add_property' pos) rules' ctxt
        end
   in thy
   |> Property_Kinds.map (Symtab.update_new (k, extract))
   |> Context.theory_map (
        Phi_Reasoner.add_pass ("\<phi>type-operator$" ^ k, pat,
          fn pos => fn (rules, mode, pats, guard, ctxt) =>
                       (rules, mode, pats, guard,
                        if Config.get_generic ctxt adding_property
                        then add_prop pos rules ctxt
                        else ctxt)))
  end


fun setup_rule_generation (template_pos,(raw_dependencies,pass),(b,gen)) rule0 ctxt =
  let val thy = Context.theory_of ctxt
      val rule = normalize rule0
      fun get_prop_kinds (TM::L) =
           let val base = case get_prop_kinds L of [NONE] => [] | L => L
               fun dest (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest X
                 | dest (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ Const(\<^const_name>\<open>\<A>_template_reason\<close>, _)) = dest X
                 | dest X = X
            in case Term.head_of (dest TM)
            of Const (k, _) => if is_a_kind_of_property thy k then SOME k :: base else NONE :: base
             | _ => NONE :: base
           end
        | get_prop_kinds [] = []
      val prop_kinds = case raw_dependencies
                         of SOME deps => (List.app (fn SOME dep => assert_property_kind thy dep
                                                     | NONE => ()) deps ;
                                          deps)
                          | NONE => get_prop_kinds (Thm.prems_of rule)
      val template = (prop_kinds, template_pos, Instantiate_Rule (rule, pass, gen, b))
   in ctxt
   |> add_template true (serial (), template)
  end

(** Interfaces for Automation over Property **)

val rule_template_pass__sender : rule_generation_pass option Unsynchronized.ref
      = Unsynchronized.ref NONE
val rule_template_pass__sender_locker = Synchronized.var "rule_template_pass__sender_locker" ()


val _ = Theory.setup (

  Attrib.setup \<^binding>\<open>\<phi>type_property\<close> (Scan.succeed (Thm.declaration_attribute (add_property' Position.none)))
    "Declare a \<phi>-type property that will be used to instantiate automation"

#>Attrib.setup \<^binding>\<open>\<phi>reason_template\<close> (
    Phi_Reasoner.attr_syntax
      (Scan.option (Scan.lift (Args.$$$ "name" |-- Parse.binding))
       -- Scan.option (
            Scan.lift (\<^keyword>\<open>requires\<close>) |--
                (Parse.and_list' (Scan.repeat ( Scan.lift (Args.$$$ "_") >> K NONE
                                             || Args.const {proper=true,strict=true} >> SOME)) >> flat))
       -- Scan.option (Scan.lift (Args.$$$ "pass" |-- \<^keyword>\<open>:\<close> |-- Parse.ML_source))
       -- Attrib.opt_attribs)
      (fn (pos, mode, priority, (((bind, dependencies), pass_src),attribs), pats, guard) =>
        Thm.declaration_attribute (fn thm => fn ctxt =>
          let val _ = case guard of NONE => ()
                         | _ => error "No guard is allowed here"
              val pass = Option.map (fn src =>
                    let val _ = Synchronized.change rule_template_pass__sender_locker (fn () => (
                                  ML_Context.expression (Input.pos_of src)
                                    (ML_Lex.read "Phi_Type_Template_Properties.rule_template_pass__sender := SOME ((" @
                                     ML_Lex.read_source src @
                                     ML_Lex.read ") : Phi_Type_Template_Properties.rule_generation_pass)")
                                    ctxt;
                                  ()))
                        val pass = the (!rule_template_pass__sender)
                        val _ = rule_template_pass__sender := NONE
                     in pass
                    end
                  ) pass_src
              val gen = case (attribs, priority, pats)
                          of (attrs as _ :: _, 100, ([], [])) => Attributes attrs
                           | (_ :: _, _, _) =>
                              error "Prioirty and binding patterns are senseless and not allowed to\
                                    \ be given once the attributes are given."
                           | ([], _, _) =>
                              Reasonig_Rule ((mode, priority), pats)
           in setup_rule_generation (pos,(dependencies,pass),(bind,gen)) thm ctxt
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


end 

