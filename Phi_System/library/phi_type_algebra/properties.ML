(*
\<^item> Storage of properties.
\<^item> Deriving rules from property-conditioned templates
*)

signature PHI_TYPE_ALGEBRA = sig

include PHI_TYPE_ALGEBRA

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

structure Gen_Rule_SS : SIMPSET (*simpset for generating reasoning rules*)

(* The Framework for Automation based on Algebraic Property *)

type automation_on_property =
        term (*type operator*) * thm (*property*) -> Context.generic -> Context.generic
val add_automation_on_property : priority * property_name list (*bindings*) -> automation_on_property -> Context.generic -> Context.generic
val invoke_automations_on_property : term * thm -> Context.generic -> Context.generic
val property_dependent_setup : property_name list * property_name list -> (thm list -> automation_on_property) -> automation_on_property

(* Internal Interfaces *)

type rule_generation_pass = property_name list * (thm -> thm list) * Proof.context -> thm -> thm list
val rule_template_pass__sender : rule_generation_pass option Unsynchronized.ref

end

structure Phi_Type_Algebra : PHI_TYPE_ALGEBRA = struct

open Phi_Type_Algebra

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

type automation_on_property = term (*\<phi>-type or type operator*) * thm (*property*) -> Context.generic -> Context.generic

fun property_eq ((t1,_,th1),(t2,_,th2)) = (t1 aconv t2) andalso Thm.eq_thm_prop (th1,th2)

structure Properties = Generic_Data (
  type T = (term (*\<phi>type*) * Position.T * thm) Net.net 
  val empty = Net.empty
  val merge = Net.merge property_eq
)

fun prop_table_order k ((p1,_),(p2,_)) = if p1 = p2 then raise Symtab.DUP k else int_ord (p1,p2)

structure Automation_on_Property = Generic_Data (
  type T = (priority * automation_on_property) Ord_List.T Symtab.table
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
  let val prop_kind = get_property_name (snd phityp)
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
      fun insert_term (k''', (k,pos,v)) net =
        let val clashes = Net.unify_term net k'''
                       |> filter (fn (k', _, _) => Pattern.matches thy (k',k) orelse Pattern.matches thy (k,k'))
            val _ = if null clashes then ()
                    else let open Pretty
                        val ctxt' = Context.proof_of ctxt
                     in error (string_of (chunks (
                           block [str "The property ", str property_name, str " of \<phi>-type ",
                                  Syntax.pretty_term ctxt' phityp0,
                                  str " either covers or is covered by other existing rules."] ::
                           str "We prohibit redundancy of \<phi>-type properties because it causes \
                               \a great amount of redundancy in the generated reasoning rules. \
                               \Instead, you should provide the most general rule and, if you want, \
                               \specialized (branched) reasoning on its antecedents." ::
                           map (fn (_,pos,rule) => block (
                               here pos @ [Syntax.pretty_term ctxt' (Thm.prop_of rule)]
                             )) clashes
                         )))
                    end
         in Net.insert_term property_eq (k''', (k,pos,v)) net
        end
   in ctxt
    |> Properties.map (insert_term (key, (phityp', pos, property)))
                    (*|> insert_term false (key_phityp, (phityp',pos,Drule.dummy_thm))*)
    |> invoke_automations_on_property (phityp0,property)
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

fun add_automation_on_property (priority, prop_kinds) automation =
  fold (fn prop_kind =>
      Automation_on_Property.map (@{print} o Symtab.map_default (prop_kind,[])
          (Ord_List.insert (prop_table_order prop_kind) (priority, automation)))
    ) (distinct (op =) prop_kinds)

(*no_rule_deps are still dependences required to activate the automation,
  but their rules are not required to be and will not be passed to the automation*)
fun property_dependent_setup (deps,no_rule_deps) automation (the_functor,property) ctxt =
  let exception Dep
      val prop_name = get_property_name property
   in(if Thm.is_dummy property orelse member (op =) deps prop_name
                               orelse member (op =) no_rule_deps prop_name
      then let fun get_rules deps = map (fn dep =>
                      case lookup_property_unify ctxt the_functor dep
                        of [(_,_,x)] => x
                         | [] => raise Dep
                         | ((_,_,x)::_) => (warning ("multiple property instances match " ^ Syntax.string_of_term (Context.proof_of ctxt) the_functor); x)
                    ) deps
               val rules = get_rules deps
               val _ = get_rules no_rule_deps
            in automation rules (the_functor,property) ctxt
           end
      else ctxt)
      handle Dep => ctxt
  end


structure Gen_Rule_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>simp_for_\<phi>TA_rule_generation\<close>
  val comment = "Rules simplifying the generated \<phi>functor reasoning rules."
)

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes

type rule_generation_pass = property_name list * (thm -> thm list) * Proof.context -> thm -> thm list
val rule_template_pass__sender : rule_generation_pass option Unsynchronized.ref
      = Unsynchronized.ref NONE
val rule_template_pass__sender_locker = Synchronized.var "rule_template_pass__sender_locker" ()

fun setup_rule_generation (pos,mode,priority,(additional_props,pass),pats,guard) rule0 ctxt =
  let val thy = Context.theory_of ctxt
      val rule = normalize rule0
      fun get_prop_kinds (TM::L) =
           (case try (Term.head_of o HOLogic.dest_Trueprop) TM
              of SOME (Const (k, _)) =>
                    if is_a_kind_of_property thy k
                    then k :: get_prop_kinds L
                    else []
               | _ => [])
        | get_prop_kinds [] = []
      val prop_kinds = get_prop_kinds (Thm.prems_of rule)
      val _ = List.app (assert_property_kind thy) additional_props
      exception Inst_Fail
      fun impl props _ ctxt =
            let val ctxt' = Context.proof_of ctxt
                fun do_reason rule =
                      if exists (fn _ $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => true | _ => false)
                                (Thm.prems_of rule)
                      then let val protect_num = fold (fn th => fn N => N + Thm.nprems_of th) props 0
                            in case Phi_Reasoner.reason NONE true ctxt' (Thm.permute_prems 0 protect_num rule)
                                 of SOME ret => Thm.permute_prems 0 (~protect_num) ret
                                  | NONE => error "Rule Generation fails"
                           end
                      else rule
                fun simplify ctxt rules =
                      let val ((_,rules'1), ctxt'1) = Variable.import false rules ctxt
                          val ctxt's = Gen_Rule_SS.enhance ctxt'1
                                    |> Simplifier.del_cong @{thm' HOL.if_weak_cong}
                       in Variable.export ctxt'1 ctxt
                            (map ( Simplification_Protect.protect ctxt's
                                #> Simplifier.asm_lr_simplify ctxt's
                                #> Simplification_Protect.unprotect ctxt's) rules'1)
                      end
                val rule'1 = (rule OF props)
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
                                |> do_reason
                                |> singleton (simplify ctxt') 
                      val rule' = rule'2
                                |> Thm.flexflex_rule (SOME ctxt')
                                |> Seq.chop 2
                                |> (fn ([], _) => error ("During rule generation: fail to solve flex-flex pairs\n"^
                                                          Thm.string_of_thm ctxt' rule'2)
                                     | ([x], _) => x
                                     | ((x::_), _) => (warning ("Multiple solution of flex-flex pair! Take the first one.\n"^
                                                          Thm.string_of_thm ctxt' rule'2); x))
                                |> Phi_Help.instantiate_higher_order_schematic_var ~1 ctxt'
                                |> singleton (simplify ctxt') 
                                |> normalize
                   in [rule']
                  end
                val rules' = case pass of SOME ps => ps (prop_kinds, default_generation, ctxt') rule'1
                                        | NONE => default_generation rule'1
             in if null rules' then ctxt
             else (Phi_Reasoner.info_print ctxt' 1 (fn () =>
                                "Instantiate reasoning rule for \<phi>-type operator ") ;
                   Phi_Reasoner.add_rules (
                      map (fn rule => ([rule], pos, mode, priority, fst pats, snd pats, NONE) ) rules') ctxt)
            end
            handle Inst_Fail => ctxt
      val automation = property_dependent_setup (prop_kinds, additional_props) impl

      val properties = Properties.get ctxt
      val existing_rules = map (fn pk =>
              Net.unify_term properties (net_encode_property_key (Var(("uu",0),TVar(("uu",0),[])), pk))
            ) prop_kinds
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
   |> add_automation_on_property (serial (), prop_kinds) automation
   |> fold (fn (f,rules) => impl (rev rules) (f,Drule.dummy_thm)) existing_ins
  end

(** Interfaces for Automation over Property **)

val _ = Theory.setup (

  Attrib.setup \<^binding>\<open>\<phi>type_property\<close> (Scan.succeed (Thm.declaration_attribute (add_property' Position.none)))
    "Declare a \<phi>-type property that will be used to instantiate automation"

#>Attrib.setup \<^binding>\<open>\<phi>reason_template\<close> (
    Phi_Reasoner.attr_syntax
      (Scan.optional (
          Scan.lift (\<^keyword>\<open>requires\<close>) |-- (Parse.and_list' (Scan.repeat (Args.const {proper=true,strict=true})) >> flat)) [] --
       Scan.option (Scan.lift (Args.$$$ "pass" |-- \<^keyword>\<open>:\<close> |-- Parse.ML_source)))
      (fn (pos, mode, priority, (additional_props, pass_src), pats, guard) =>
        Thm.declaration_attribute (fn thm => fn ctxt =>
          let val pass = Option.map (fn src =>
                    let val _ = Synchronized.change rule_template_pass__sender_locker (fn () => (
                                  ML_Context.expression (Input.pos_of src)
                                    (ML_Lex.read "Phi_Type_Algebra.rule_template_pass__sender := SOME ((" @
                                     ML_Lex.read_source src @
                                     ML_Lex.read ") : Phi_Type_Algebra.rule_generation_pass)")
                                    ctxt;
                                  ()))
                        val pass = the (!rule_template_pass__sender)
                        val _ = rule_template_pass__sender := NONE
                     in pass
                    end
                  ) pass_src
           in setup_rule_generation (pos,mode,priority,(additional_props,pass),pats,guard) thm ctxt
          end)
      )) ""
)


end 

