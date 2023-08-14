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

structure Template_Inst_SS : SIMPSET (*simpset for generating reasoning rules*)

(* The Framework for Automation based on Algebraic Property *)

type template_automation =
        term (*\<phi>-type (operator)*) * Position.T * thm (*properties*) list -> Context.generic -> Context.generic
val add_template_automation : priority * property_name list (*dependended properties*)
                              -> template_automation
                              -> Context.generic -> Context.generic
val invoke_automations_on_property : term * Position.T * thm -> Context.generic -> Context.generic

(* Internal Interfaces *)

type rule_generation_pass = property_name option list (*corresponding to the premises respectively,
                                                        being NONE if the premise in the position is
                                                        not a property for instantiating*)
                          * (thm -> thm list) (*default generation process*)
                          * Position.T (*where the template is instantiated*)
                          * Proof.context
                         -> thm -> thm list
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

type template_automation_i = term (*\<phi>-type (operator)*) * Position.T * thm (*the property that invokes the automation*)
                             -> Context.generic -> Context.generic

type template_automation = term (*\<phi>-type (operator)*) * Position.T * thm (*property*) list
                           -> Context.generic -> Context.generic

fun property_eq ((t1,_,th1),(t2,_,th2)) = (t1 aconv t2) andalso Thm.eq_thm_prop (th1,th2)

structure Properties = Generic_Data (
  type T = (term (*\<phi>type*) * Position.T * thm) Net.net 
  val empty = Net.empty
  val merge = Net.merge property_eq
)

fun prop_table_order k ((p1,_),(p2,_)) = if p1 = p2 then raise Symtab.DUP k else int_ord (p1,p2)

structure Automation_on_Property = Generic_Data (
  type T = (priority * template_automation_i) Ord_List.T Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (fn k => uncurry (Ord_List.union (prop_table_order k)))
)

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
  fst (Term.dest_Const (Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of thm))))

fun lookup_property_exact ctxt phityp0 property_name =
  let val thy = Context.theory_of ctxt
      val phityp = close_phitype_operator phityp0
   in Net.match_term (Properties.get ctxt) (net_encode_property_key (phityp, property_name))
      |> filter (fn (tm, _, _) => Pattern.equiv thy (tm, phityp))
  end

fun lookup_property_match ctxt phityp0 property_name =
  let val phityp = close_phitype_operator phityp0
   in Net.match_term (Properties.get ctxt) (net_encode_property_key (phityp, property_name))
   |> filter (fn (tm, _, _) => Pattern.matches (Context.theory_of ctxt) (tm, phityp))
  end

fun lookup_property_unify ctxt phityp0 property_name =
  let val phityp = close_phitype_operator phityp0
   in Net.unify_term (Properties.get ctxt) (net_encode_property_key (phityp, property_name))
   |> filter (fn (tm, _, _) => can (Pattern.unify ctxt (tm, phityp)) Envir.init)
  end

fun invoke_automations_on_property phityp ctxt =
  let val prop_kind = get_property_name (#3 phityp)
   in case Symtab.lookup (Automation_on_Property.get ctxt) prop_kind
   of NONE => ctxt
    | SOME L => fold (fn (_,s) => s phityp) L ctxt
  end

(*fun list_functors ctxt =
  Net.unify_term (Properties.get ctxt) (net_encode_phityp (Var(("uu",0),TVar(("'uu",0),[]))))
    |> map (fn (tm,_,_) => Logic.incr_indexes ([],[],1) tm)*)

(* fun is_a_registered_functor_i thy net the_functor =
  let val key = net_encode_phityp the_functor
   in Net.match_term net key
        |> exists (fn (pat, _) => Pattern.matches thy (pat, the_functor))
  end *)

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
    |> Properties.map (insert_term (key, (phityp', pos, property)))
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
                       (rules, mode, pats, guard, add_prop pos rules ctxt)))
  end

fun toplevel_property_auto deps automation (the_functor,pos,property) ctxt =
  let exception Dep
      val prop_name = get_property_name property
   in(if Thm.is_dummy property orelse member (op =) deps prop_name
      then let fun cross_map _ [] = []
                 | cross_map f [h] = map single (f h)
                 | cross_map f (h::L) = let val L' = cross_map f L
                                         in maps (fn L'' => map (fn x => x :: L'') (f h)) L'
                                        end
               val get_rules = cross_map (fn dep =>
                      case if dep = prop_name
                           then [property]
                           else map #3 (lookup_property_unify ctxt the_functor dep)
                        of [] => raise Dep
                         | L => L
                    )
               val ruless = get_rules deps
            in fold (fn rules => fn ctxt =>
                          automation (the_functor,pos,rules) ctxt
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

fun add_template_automation (priority, prop_kinds) automation =
  fold (fn prop_kind =>
      Automation_on_Property.map (Symtab.map_default (prop_kind,[])
          (Ord_List.insert (prop_table_order prop_kind) (priority, toplevel_property_auto prop_kinds automation)))
    ) (distinct (op =) prop_kinds)


structure Template_Inst_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>simp_for_\<phi>TA_rule_generation\<close>
  val comment = "Rules simplifying the reasoning rules instantiated from templates."
  val attribute = NONE
)

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes

type rule_generation_pass
      = property_name option list * (thm -> thm list) * Position.T * Proof.context -> thm -> thm list
val rule_template_pass__sender : rule_generation_pass option Unsynchronized.ref
      = Unsynchronized.ref NONE
val rule_template_pass__sender_locker = Synchronized.var "rule_template_pass__sender_locker" ()

type pattern = term
datatype generation_by = Reasonig_Rule of priority * ((pattern * priority option) list * pattern list)
                       | Attributes of Thm.attribute list
fun setup_rule_generation (template_pos,mode,(raw_dependences,pass),gen) rule0 ctxt =
  let val thy = Context.theory_of ctxt
      val rule = normalize rule0
      fun get_prop_kinds (TM::L) =
           let val base = case get_prop_kinds L of [NONE] => [] | L => L
            in case try (Term.head_of o HOLogic.dest_Trueprop) TM
            of SOME (Const (k, _)) =>
                  if is_a_kind_of_property thy k then SOME k :: base else NONE :: base
             | _ => NONE :: base
           end
        | get_prop_kinds [] = []
      val prop_kinds = case raw_dependences
                         of SOME deps => (List.app (fn SOME dep => assert_property_kind thy dep
                                                     | _ => ()) deps ;
                                          deps)
                          | NONE => get_prop_kinds (Thm.prems_of rule)
      val prop_kinds' = map_filter I prop_kinds
      val _ = Phi_Reasoner.info_pretty_generic ctxt 1 (fn () => let open Pretty
                  val consts = Context.cases Sign.consts_of Proof_Context.consts_of ctxt
               in chunks (str "Installing \<phi>reasoning rule template depended on " ::
                    map (fn SOME pk =>
                              pk |> Consts.the_const consts |> Const
                                 |> Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt
                                 |> single |> item
                          | NONE => item [str "_"]) prop_kinds)
              end)

      exception Inst_Fail
      fun impl (_, pos, props) ctxt =
            let val ctxt' = Context.proof_of ctxt
              (*fun do_reason rule =
                      if exists (fn _ $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => true | _ => false)
                                (Thm.prems_of rule)
                      then let val protect_num = fold (fn th => fn N => N + Thm.nprems_of th) props 0
                            in case Phi_Reasoner.reason NONE true ctxt' (Thm.permute_prems 0 protect_num rule)
                                 of SOME ret => Thm.permute_prems 0 (~protect_num) ret
                                  | NONE => error "Rule Generation fails"
                           end
                      else rule*)
                fun simplify ctxt rules =
                      let val ((_,rules'1), ctxt'1) = Variable.import false rules ctxt
                          val ctxt's = Template_Inst_SS.enhance ctxt'1
                                    |> Simplifier.del_cong @{thm' HOL.if_weak_cong}
                       in Variable.export ctxt'1 ctxt
                            (map ( Simplification_Protect.protect ctxt's
                                #> Phi_Reasoners.asm_lr_simplify true ctxt's
                                #> Simplification_Protect.unprotect ctxt's) rules'1)
                      end
                val props' = burrow_options (K props) prop_kinds
                          |> map (fn SOME X => X | NONE => Drule.asm_rl)
                val rule'1 = Phi_Help.beta_eta_contract (rule OF props')
                      handle THM _ => let open Pretty in
                          Phi_Reasoner.info_pretty ctxt' 2 (fn () =>
                            chunks (block (str "Mismatch in instantiating a reasoning rule " :: here pos) ::
                              item [Thm.pretty_thm ctxt' rule] ::
                              map (fn rule => item [Thm.pretty_thm ctxt' rule]) props
                            )) ;
                          raise Inst_Fail
                        end
                fun default_generation rule'1 =
                  let val rule'2 = rule'1
                                (*|> do_reason*)
                                |> singleton (simplify ctxt') 
                      val rule' = rule'2
                                |> Phi_Help.unique_flexflex (SOME ctxt')
                                |> Phi_Help.instantiate_higher_order_schematic_var ~1 ctxt'
                                |> singleton (simplify ctxt') 
                                |> normalize
                   in [rule']
                  end
                val rules' = case pass of SOME ps => ps (prop_kinds, default_generation, pos, ctxt') rule'1
                                        | NONE => default_generation rule'1
             in if null rules' then ctxt
             else (Phi_Reasoner.info_pretty ctxt' 1 (fn () => let open Pretty in
                             paragraph (text "Instantiate template rule for \<phi>-type operator" @
                                        here template_pos)
                             end) ;
                   case gen
                     of Reasonig_Rule (priority, (pats, blacklists)) =>
                          Phi_Reasoner.add_rules (map (fn rule =>
                            ([rule], pos, mode, priority, pats, blacklists, NONE) ) rules') ctxt
                      | Attributes attrs =>
                          let fun app attr = uncurry (Thm.apply_attribute attr)
                           in fold (curry (snd o fold app attrs)) rules' ctxt
                          end)
            end
            handle Inst_Fail => ctxt

      val properties = Properties.get ctxt
      val existing_rules = map (fn pk =>
              Net.unify_term properties (net_encode_property_key (Var(("uu",0),TVar(("uu",0),[])), pk))
            ) prop_kinds'
      fun cross_product aa bb =
            maps (fn (ta,_,ra) =>
              map_filter (fn (tb,rb) =>
                case try (Pattern.unify ctxt (ta, Logic.incr_indexes ([],[],1) tb)) Envir.init
                  of SOME e => SOME (Envir.norm_term e ta, ra::rb)
                   | NONE   => NONE
              ) bb
            ) aa
      val existing_ins =
        if null existing_rules
        then []
        else let val init = map (fn (tm,_,rule) => (tm, [rule])) (hd existing_rules)
              in fold cross_product (tl existing_rules) init
             end
   in ctxt
   |> add_template_automation (serial (), prop_kinds') impl
   |> fold (fn (f,rules) => impl (f, template_pos, rev rules)) existing_ins
  end

(** Interfaces for Automation over Property **)

val _ = Theory.setup (

  Attrib.setup \<^binding>\<open>\<phi>type_property\<close> (Scan.succeed (Thm.declaration_attribute (add_property' Position.none)))
    "Declare a \<phi>-type property that will be used to instantiate automation"
                        
#>Attrib.setup \<^binding>\<open>\<phi>reason_template\<close> (
    Phi_Reasoner.attr_syntax
      (Scan.option (
          Scan.lift (\<^keyword>\<open>requires\<close>) |--
              (Parse.and_list' (Scan.repeat ( Scan.lift (Args.$$$ "_") >> K NONE
                                           || Args.const {proper=true,strict=true} >> SOME)) >> flat))
       -- Scan.option (Scan.lift (Args.$$$ "pass" |-- \<^keyword>\<open>:\<close> |-- Parse.ML_source))
       -- Attrib.opt_attribs)
      (fn (pos, mode, priority, ((dependences, pass_src),attribs), pats, guard) =>
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
                          of (attrs as _ :: _, 100, ([], [])) =>
                              Attributes (map (Context.cases Attrib.attribute_cmd_global Attrib.attribute_cmd ctxt) attrs)
                           | (_ :: _, _, _) =>
                              error "Prioirty and binding patterns are senseless and not allowed to\
                                    \ be given once the attributes are given."
                           | ([], _, _) =>
                              Reasonig_Rule (priority, pats)
           in setup_rule_generation (pos,mode,(dependences,pass),gen) thm ctxt
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

