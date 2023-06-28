(*
FILE: Phi_System/library/tools/functor_detect.ML
AUTHOR: Qiyuan Xu

Given a term of a \<phi>-type which is an application of a functor with an argument,
it is undecidable by higher-order lambda pattern match to get the functor and the argument from it.
The file provides ML code enabling users to register rewrites or ML codes to extract the functor
from terms matching certain patterns.

It also implements a simple fallback heuristic that works when the term is a sequence
of lambda applications \<open>H $ A1 $ A2 $ A3\<close> and the head is a constant, and it assumes the argument
is the last operand i.e. the A3.
*)

signature PHI_TYPE_ALGEBRA = sig

(* Detect Type Operator from a Lambda Application *)

structure Detection_Rewr : PATTERN_REWRITE

val detect_type_operator  : int -> Proof.context -> term -> term list option
val detect_type_operator1 : int -> Proof.context -> term -> term list

(* Algebraic Property *)

type property_name = string

val is_a_kind_of_property : theory -> property_name -> bool
val add_property_kind : property_name -> (term -> term) -> theory -> theory

val lookup_property_exact : Context.generic -> term (*pattern of the type operator*) -> property_name -> thm option
val lookup_property_match : Context.generic -> term -> property_name -> (term * Position.T * thm) list
val lookup_property_unify : Context.generic -> term -> property_name -> (term * Position.T * thm) list
val add_property : term * Position.T * thm -> Context.generic -> Context.generic
val list_functors : Context.generic -> term list

(* Automation based on Algebraic Property *)

type automation_on_property =
        term (*type operator*) * thm (*property*) -> Context.generic -> Context.generic
val add_automation_on_property : priority -> automation_on_property -> Context.generic -> Context.generic
val invoke_automations_on_property : term * thm -> Context.generic -> Context.generic
val property_dependent_setup : string list -> (thm list -> automation_on_property) -> automation_on_property

(* \<phi>-Type Definition \& Infos *)

datatype def = DIRECT_DEF of (term (*lhs*) * (string (*def_name*) * thm (*def*)))
             | WFREC_DEF  of string (*const name*) * Function.info

type phi_type = {
  term: term (*of most general type*),
  pos : Position.T,
  proof_id: Phi_Cache_DB.proof_id,
  equations: thm list (*unfolding the term*),
  ind: thm,
    (*inductively destructive transformation, of form
     has_R: ... \<Longrightarrow> ?P.0 a b c x \<longrightarrow> (?R.0 * x : T a b c \<longrightarrow> ?Y.0 and ?Q.0)  (*only available for sep-magma*)
     full:  ... \<Longrightarrow> ?P.0 a b c x \<longrightarrow> (x : T a b c \<longrightarrow> ?Y.0 a b c x and ?Q.0 a b c x)
     dom_only: ... \<Longrightarrow> ?P.0 a b c x \<longrightarrow> (x : T a b c \<longrightarrow> ?Y.0 and ?Q.0) *)
  intro_ToA: thm list (*introduction transformations*),
  is_recursive: bool,
  is_impredicative: bool (*to be supported*)
} (*rules and terms inside must be zero-indexed*)

val map_phi_type : (term -> term) * (thm list -> thm list) -> phi_type -> phi_type
val fold_phi_type : (term -> 'a -> 'a) * (thm -> 'a -> 'a) -> phi_type -> 'a -> 'a

val morphism_phi_type : morphism -> phi_type -> phi_type
val instantiate_phi : (typ TVars.table * term Vars.table) * (ctyp TVars.table * cterm Vars.table)
                   -> phi_type -> phi_type
val phi_trim_context : phi_type -> phi_type
val phi_transfer : theory -> phi_type -> phi_type
val phi_maxidx_of : phi_type -> int -> int


type algebra_hints = term list

val get_type_info : Context.generic -> string (*const name*) -> phi_type option
val add_type : def * Position.T * algebra_hints -> generic_theory -> phi_type * generic_theory

type automation_on_def = phi_type * algebra_hints -> generic_theory -> generic_theory
val add_automation_on_def : priority -> automation_on_def -> Context.generic -> Context.generic

(* Tools *)

(*Find the most general instantiation of the given type to meet the given sort*)
val lift_type_sort : theory -> typ * sort -> Type.tyenv

(*make inductively destruction rule.*)
val mk_ind_dest_ToA : Proof.context -> phi_type -> (term (*x*) * term (*T*) -> term) -> thm
val mk_ind_dest_ToA_internal : Proof.context -> phi_type -> term -> thm

val fix_phi_type : bool -> phi_type -> Proof.context ->
        (typ TVars.table * term Vars.table) *
        (ctyp TVars.table * cterm Vars.table) * phi_type *
        Proof.context

val fix_phi_term_params : term -> Proof.context ->
        (term * term * typ * typ list * typ) * Proof.context

val raw_term_name_typ : term -> string * typ
val dest_parameterized_phi_ty : typ -> typ list (*reserved!*) * typ * typ

end


(**** Implementation ****)

structure Phi_Type_Algebra : PHI_TYPE_ALGEBRA = struct

type property_name = string

(*** Detect Functor from a lambda application ***)

structure Detection_Rewr = Pattern_Translation (
  val parse_pattern = Syntax.parse_term
  val check_pattern = Syntax.check_terms
  val multi_translation_err_msg = "Cannot determine which is the functor and which is the argument\
        \ in the given term. Two rules are conflict!"
)

fun detect_type_operator arity ctxt term =
  case Detection_Rewr.translate (Context.Proof ctxt) term
    of [] => let val (hT, args) = Term.strip_comb term
                 val N = length args - arity
              in if is_Const hT andalso not (is_Const term) andalso N >= 0
                 then SOME ( Term.list_comb (hT, take N args) :: drop N args)
                 else NONE
             end
     | L => (if length L = arity + 1
             then SOME L
             else error ("Expect " ^ string_of_int arity ^ "-arity functor, but the configured\
                         \ rule returns " ^ string_of_int (length L) ^ "-arity."))

fun detect_type_operator1 arity ctxt term =
  case detect_type_operator arity ctxt term
    of SOME ret => ret
     | NONE => error ("Fail to detect the functor part and the argument part from term\n"^
                      Syntax.string_of_term ctxt term)

(*** Algebraic Property & Automation ***)

(** Property Kind **)

structure Property_Kinds = Theory_Data (
  type T = (term -> term (*extract the functor from the property spec*)) Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun is_a_kind_of_property thy k = Symtab.defined (Property_Kinds.get thy) k
fun extract_functor_from_property_spec thy k = Symtab.lookup (Property_Kinds.get thy) k

(** Property DB **)

type automation_on_property = term (*functor*) * thm (*property*) -> Context.generic -> Context.generic

fun property_eq ((t1,_,th1),(t2,_,th2)) = (t1 aconv t2) andalso Thm.eq_thm_prop (th1,th2)
(* fun property_eq' thy ((t1,th1),(t2,th2)) = (t1 aconv t2) andalso Thm.equiv_thm thy (th1,th2) *)

structure Properties = Generic_Data (
  type T = (term (*functor*) * Position.T * thm) Net.net 
  val empty = Net.empty
  val merge = Net.merge property_eq
)

structure Automation_on_Property = Generic_Data (
  type T = automation_on_property PriorityTab.table
  val empty = PriorityTab.empty
  val merge = PriorityTab.merge (K false)
)

fun encode_property_key (the_functor,property_name) =
  Const("P", dummyT) $ the_functor $ Const(property_name, dummyT)

fun encode_functor the_functor = Const("F", dummyT) $ the_functor

fun get_property_name thm =
  fst (Term.dest_Const (Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of thm))))

fun lookup_property_exact ctxt the_functor property_name =
  let val thy = Context.theory_of ctxt
   in Net.match_term (Properties.get ctxt) (encode_property_key (the_functor, property_name))
      |> filter (fn (tm, _, _) => Pattern.equiv thy (tm, the_functor))
      |> (fn ((_,_,x)::_) => SOME x
           | [] => NONE)
  end

fun lookup_property_match ctxt the_functor property_name =
  Net.match_term (Properties.get ctxt) (encode_property_key (the_functor, property_name))
    |> filter (fn (tm, _, _) => Pattern.matches (Context.theory_of ctxt) (tm, the_functor))

fun lookup_property_unify ctxt the_functor property_name =
  Net.unify_term (Properties.get ctxt) (encode_property_key (the_functor, property_name))
    |> filter (fn (tm, _, _) => can (Pattern.unify ctxt (tm, the_functor)) Envir.init)

fun invoke_automations_on_property the_functor_and_property ctxt =
  PriorityTab.fold (fn (_,s) => s the_functor_and_property) (Automation_on_Property.get ctxt) ctxt

fun list_functors ctxt =
  Net.unify_term (Properties.get ctxt) (encode_functor (Var(("uu",0),TVar(("'uu",0),[]))))
    |> map (fn (tm,_,_) => Logic.incr_indexes ([],[],1) tm)

(* fun is_a_registered_functor_i thy net the_functor =
  let val key = encode_functor the_functor
   in Net.match_term net key
        |> exists (fn (pat, _) => Pattern.matches thy (pat, the_functor))
  end *)

fun add_property (the_functor,pos,property) ctxt =
  let val thy = Context.theory_of ctxt
      val the_functor'' = the_functor
                  |> Envir.beta_eta_contract
                  |> Term_Subst.zero_var_indexes 
      val the_functor' = the_functor''
                  |> Logic.incr_indexes ([],[],~1)
      val property_name = get_property_name property
      val key = encode_property_key (the_functor', property_name)
      val key_functor = encode_functor the_functor'
      fun insert_term warn (k''', (k,pos,v)) net =
        let val super = Net.match_term net k'''
                      |> filter (fn (k', _, _) => Pattern.matches thy (k',k))
         in if null super
            then net
                  |> Net.delete_term_safe (fn ((),(k',pos,rule)) =>
                        let val ret = Pattern.matches thy (k,k')
                         in if ret andalso warn
                            then (warning ("The property overrides an existing property rule!" ^
                                    Position.here pos ^ "\n" ^ Thm.string_of_thm (Context.proof_of ctxt) rule)
                               ; true)
                            else ret
                        end) (k''',())
                  |> Net.insert_term property_eq (k''', (k,pos,v))
            else (
              if warn
              then
                let open Pretty
                    val ctxt' = Context.proof_of ctxt
                 in error (string_of (chunks (
                       block [str "The property ", str property_name, str " of functor ",
                              Syntax.pretty_term ctxt' the_functor,
                              str " has been covered by existing rules"] ::
                       map (fn (_,pos,rule) => block (
                           here pos @ [Syntax.pretty_term ctxt' (Thm.prop_of rule)]
                         )) super
                     )))
                end
              else ()
            ; net)
        end
   in ctxt
    |> Properties.map (fn net => net
                    |> insert_term true (key, (the_functor',pos,property))
                    |> insert_term false (key_functor, (the_functor',pos,Drule.dummy_thm)))
    |> invoke_automations_on_property (the_functor,property)
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
      val the_functor =
            case Term.strip_comb prop_spec
              of (Const(N, _), _) =>
                 (case extract_functor_from_property_spec thy N
                    of SOME extract => extract prop_spec
                     | _ => error (N ^ " is not a known functor property. Please use ML function \
                                       \\<open>Phi_Type_Algebra.add_property_kind\<close> to register it.") )
               | _ => error "The theorem is not a valid functor property."
   in add_property (the_functor,pos,property) ctxt
  end

fun add_automation_on_property priority automation ctxt =
  Automation_on_Property.map (PriorityTab.update_new (
      (priority, Context.theory_long_name (Context.theory_of ctxt)), automation)) ctxt

fun property_dependent_setup deps automation (the_functor,property) ctxt =
  let exception Dep
   in(if Thm.is_dummy property orelse member (op =) deps (get_property_name property)
      then let val rules = map (fn dep =>
                  case lookup_property_match ctxt the_functor dep
                    of [(_,_,x)] => x
                     | [] => raise Dep
                     | ((_,_,x)::_) => (warning ("multiple match for " ^ Syntax.string_of_term (Context.proof_of ctxt) the_functor); x)
                ) deps
            in automation rules (the_functor,property) ctxt
           end
      else ctxt)
      handle Dep => ctxt
  end

fun add_property_kind k extract thy =
  let val ty = case Sign.const_type thy k
                 of SOME T => T
                  | NONE => error (k ^ " is not a declared constant")
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
        Phi_Reasoner.add_pass ("\<phi>functor$" ^ k, pat, fn pos => fn (rules, pats, guard, ctxt) =>
          (rules, pats, guard, add_prop pos rules ctxt)))
  end


structure Gen_Rule_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = \<^binding>\<open>simp_for_rule_generation\<close>
  val comment = "Rules simplifying the generated \<phi>functor reasoning rules."
)

fun setup_rule_generation (pos,mode,priority,pats,guard) rule ctxt =
  let val thy = Context.theory_of ctxt
      fun get_prop_kinds (TM::L) =
           (case try (Term.head_of o HOLogic.dest_Trueprop) TM
              of SOME (Const (k, _)) =>
                    if is_a_kind_of_property thy k
                    then k :: get_prop_kinds L
                    else []
               | _ => [])
        | get_prop_kinds [] = []
      val prop_kinds = get_prop_kinds (Thm.prems_of rule)
      fun impl props (the_functor, _) ctxt =
            let val ctxt' = Context.proof_of ctxt
                fun do_reason rule =
                      if exists (fn _ $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => true | _ => false)
                                (Thm.prems_of rule)
                      then let val protect_num = fold (fn th => fn N => N + Thm.nprems_of th) props 0
                            in case Phi_Reasoner.reason NONE (ctxt', Thm.permute_prems 0 protect_num rule)
                                 of SOME (_, ret) => Thm.permute_prems 0 (~protect_num) ret
                                  | NONE => error "Rule Generation fails"
                           end
                      else rule
                fun simplify ctxt rules =
                      let val ((_,rules'1), ctxt'1) = Variable.import false rules ctxt
                          val ctxt's = Gen_Rule_SS.enhance ctxt'1
                       in Variable.export ctxt'1 ctxt
                            (map (Simplifier.asm_lr_simplify ctxt's) rules'1)
                      end
                val rule'2 = (rule OF props)
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
                          |> Phi_Reasoner.beta_eta_contract
                          |> Drule.zero_var_indexes
                val _ = Phi_Reasoner.info_pretty ctxt' 0 (fn () => let open Pretty in
                          item [chunks [
                            block [str "Instantiate reasoning rule for functor ",
                                   Syntax.pretty_term ctxt' (Logic.incr_indexes ([],[],1) the_functor)],
                            Syntax.pretty_term ctxt' (Thm.prop_of rule')
                          ]] end)
             in Phi_Reasoner.add_intro_rule pos mode priority pats guard [rule'] ctxt
            end
      val automation = property_dependent_setup prop_kinds impl

      val properties = Properties.get ctxt
      val existing_rules = map (fn pk =>
              Net.unify_term properties (encode_property_key (Var(("uu",0),TVar(("uu",0),[])), pk))
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
   |> add_automation_on_property (serial ()) automation
   |> fold (fn (f,rules) => impl (rev rules) (f,Drule.dummy_thm)) existing_ins
  end

(** Interfaces for Automation over Property **)

val _ = Theory.setup (

  Attrib.setup \<^binding>\<open>\<phi>functor_property\<close> (Scan.succeed (Thm.declaration_attribute (add_property' Position.none)))
    "Declare a functor property that will be used to instantiate automation"

#>Attrib.setup \<^binding>\<open>\<phi>reason_functor_template\<close> (
    Phi_Reasoner.attribute_parser_for_reasoning_rule (
      fn (((((pos, (mode,priority)), additional_rules), action), pats), guard) =>
        let val _ = if null additional_rules then ()
                    else error "Bad syntax of \<phi>reason_functor"
            val _ = case action of NONE => ()
                                 | _ => error "Bad syntax of \<phi>reason_functor"
         in Thm.declaration_attribute (setup_rule_generation (pos,mode,priority,pats,guard))
        end)) ""
)


(*** \<phi>-Type Definition \& Infos ***)

datatype def = DIRECT_DEF of (term (*lhs*) * (string (*def_name*) * thm (*def*)))
             | WFREC_DEF  of string * Function.info

type phi_type = {
  term: term (*of most general type*),
  pos : Position.T,
  proof_id: Phi_Cache_DB.proof_id,
  equations: thm list (*unfolding the term*),
  ind: thm,
  intro_ToA: thm list (*introduction transformations*),
  is_recursive: bool,
  is_impredicative: bool (*to be supported*)
}

fun map_phi_type (mtm,mth) (phi : phi_type) =
  {
    term = mtm (#term phi),
    pos = #pos phi,
    proof_id = #proof_id phi,
    equations = mth (#equations phi),
    ind = singleton mth (#ind phi),
    intro_ToA = mth (#intro_ToA phi),
    is_recursive = #is_recursive phi,
    is_impredicative = #is_impredicative phi
  } : phi_type

fun fold_phi_type (fold_tm, fold_thm) (phi : phi_type) x = x
  |> fold_tm (#term phi)
  |> fold fold_thm (#equations phi)
  |> fold_thm (#ind phi)
  |> fold fold_thm (#intro_ToA phi)

fun morphism_phi_type m = map_phi_type (Morphism.term m, Morphism.fact m)
val phi_trim_context = map_phi_type (I, map (Thm.trim_context))
fun phi_transfer thy = map_phi_type (I, map (Thm.transfer thy))
val phi_maxidx_of = fold_phi_type (Term.maxidx_term, Thm.maxidx_thm)

type algebra_hints = term list
type automation_on_def = phi_type * algebra_hints -> generic_theory -> generic_theory

structure Phi_Types = Generic_Data (
  type T = phi_type Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

structure Automation_on_Def = Generic_Data (
  type T = automation_on_def PriorityTab.table
  val empty = PriorityTab.empty
  val merge = PriorityTab.merge (K false)
)

fun get_type_info ctxt k =
      Option.map (phi_transfer (Context.theory_of ctxt)) (Symtab.lookup (Phi_Types.get ctxt) k)

fun add_automation_on_def priority automation ctxt =
  Automation_on_Def.map (PriorityTab.update_new (
      (priority, Context.theory_long_name (Context.theory_of ctxt)), automation)) ctxt

fun invoke_automations_on_def phi_type_and_hints ctxt =
  PriorityTab.fold (fn (_,s) => s phi_type_and_hints) (Automation_on_Def.get ctxt) ctxt


(** Impl of Basic Conversions **)

fun conv_def_to_equaltion ctxt def =
  case Thm.concl_of def
    of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ =>
        conv_def_to_equaltion ctxt
          (Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv Object_Logic.atomize ctxt) def)
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
         Const(\<^const_name>\<open>HOL.eq\<close>, Type(\<^type_name>\<open>fun\<close>, [Ty,_])) $ LHS $ RHS) =>
       (case Ty
          of \<^Type>\<open>fun _ \<open>\<^Type>\<open>set _\<close>\<close>\<close> =>
              let val concl = Thm.dest_arg (Thm.cconcl_of def)
                  val T = Thm.dest_arg1 concl
                  val U = Thm.dest_arg  concl
                  val cty = Thm.ctyp_of_cterm T
                  val ty_a = Thm.dest_ctyp0 cty
                  val ty_b = Thm.dest_ctyp0 (Thm.dest_ctyp1 cty)
                  val rule = Thm.instantiate (TVars.make [((("'a",0),\<^sort>\<open>type\<close>),ty_a),
                                                          ((("'b",0),\<^sort>\<open>type\<close>),ty_b)],
                                              Vars.make [((("T",0),Thm.typ_of_cterm T),T),
                                                         ((("U",0),Thm.typ_of_cterm U),U)])
                             (case RHS of Abs _ => @{thm \<phi>Type_conv_eq_1}
                                        | _ => @{thm \<phi>Type_conv_eq_2})
               in Thm.bicompose NONE {flatten=false,match=true,incremented=true}
                                     (false, def, Thm.nprems_of def) 1 rule
               |> Seq.hd
              end
           | \<^Type>\<open>set _\<close> => (
                case LHS of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => def
                          | _ $ _ => Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv (fn ctxt =>
                                        HOLogic.Trueprop_conv (HOLogic.eq_conv
                                          (fn ctm =>
                                            let val T = Thm.dest_fun ctm
                                                val x = Thm.dest_arg ctm
                                                val (b,a) = Phi_Syntax.dest_phi_type_ty_c (Thm.ctyp_of_cterm T)
                                                val rule = Thm.instantiate
                                                              (TVars.make [((("'b",0),\<^sort>\<open>type\<close>),b),
                                                                           ((("'a",0),\<^sort>\<open>type\<close>),a)],
                                                               Vars.make [((("T",0),Thm.typ_of_cterm T),T),
                                                                          ((("x",0),Thm.typ_of_cterm x),x)])
                                                              @{thm \<phi>Type_def[symmetric, folded atomize_eq]}
                                             in Conv.rewr_conv rule ctm
                                            end)
                                          Conv.all_conv)
                                     ) ctxt) def
                          | _ => raise THM ("Not a \<phi>-type definition", 0, [def]))
           | _ => raise THM ("Not a \<phi>-type definition", 0, [def]))
     | _ => raise THM ("Not a \<phi>-type definition", 0, [def])

val add_premise_tag = Phi_Helper_Conv.recursive_premises_conv (fn ctxt => fn ctm =>
      case Thm.term_of ctm
        of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Imply\<close>, _) $ _ $ _ $ _) =>
              Conv.all_conv ctm
         | Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
            (case Term.head_of X
               of Var _ => Conv.all_conv ctm
                | _ => HOLogic.Trueprop_conv (PLPR_Syntax.add_premise_tag_conv \<^cterm>\<open>default\<close>) ctm)
         | _ => Conv.all_conv ctm)

(* fun mk_parameterized (arg_tys, x_ty) (name,T) =
  let val arity = length arg_tys
   in (fold_index (fn (i,_) => fn X => X $ Bound (arity-i)) arg_tys
          (Var ((name,0), rev arg_tys ---> x_ty --> T)))
       $ Bound 0
  end

  fun bool_term name = Var((name,0), HOLogic.boolT)
  fun BI_term name = Var((name,0),\<^Type>\<open>set model_ty\<close>)
  fun parameterized_BI name = mk_parameterized name \<^Type>\<open>set model_ty\<close>
*)

fun raw_term_name_typ (Const N_T) = N_T
  | raw_term_name_typ (Free N_T) = N_T
  | raw_term_name_typ _ = error "Internal bug"

fun lift_type_sort thy (ty,sort) =
  let val idx = Term.maxidx_of_typ ty
   in if Sign.of_sort thy (ty, sort)
      then Vartab.empty
      else let val (env0,_) =
                     Sign.typ_unify thy
                           (ty, TVar(("_", idx), sort))
                           (Vartab.empty, idx)
               val env = Vartab.map (fn N => (fn (S, TVar(_,S')) => (S, TVar(N,S'))
                                               | X => if N = ("_", 1) then X
                                                      else error "Internal bug 8bb59e49-9b57-48bc-b310-9da3b8f5ff7f"))
                         (Vartab.delete ("_", idx) env0)
                in env
               end
           handle Type.TUNIFY => raise TYPE ("fail to unify the type to separation magma", [ty], [])
  end

fun mk_ind_dest_ToA_internal ctxt (phi : phi_type) prop0 = (*not tested*)
  let val typ = Term.fastype_of (#term phi)
      fun parse_typ args \<^Type>\<open>fun x \<open>\<^Type>\<open>set a\<close>\<close>\<close> = (args, x, a)
        | parse_typ args \<^Type>\<open>fun a r\<close> = parse_typ (a::args) r
        | parse_typ _ _ = error "Internal bug"
      val (rev_arg_tys, x_ty, _) = parse_typ [] typ

      val prop = prop0
              |> (fn X => Abs("",x_ty,X))
              |> fold (fn T => fn X => Abs("",T,X)) rev_arg_tys
      val prop_var = (case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of (#ind phi)))
                        of Var v => v
                         | _ => error "Bad induction rule")
   in Thm.instantiate (TVars.empty, Vars.make [(prop_var, Thm.cterm_of ctxt prop)]) (#ind phi)
        |> Phi_Help.beta_eta_contract
  end

fun mk_ind_dest_ToA ctxt phi gen_prop = (*not tested*)
  let val typ = Term.fastype_of (#term phi)
      fun parse_typ args \<^Type>\<open>fun x \<open>\<^Type>\<open>set a\<close>\<close>\<close> = (args, x, a)
        | parse_typ args \<^Type>\<open>fun a r\<close> = parse_typ (a::args) r
        | parse_typ _ _ = error "Internal bug"
      val (rev_arg_tys, x_ty, model_ty) = parse_typ [] typ
      val x_term = Bound 0
      val arity = length rev_arg_tys
      val T_term = fold_index (fn (i,_) => fn X => X $ Bound (arity-i)) rev_arg_tys (#term phi)

      val prop = gen_prop (x_term, T_term)
              |> (fn X => Abs("",x_ty,X))
              |> fold (fn T => fn X => Abs("",T,X)) rev_arg_tys
      val prop_var = (case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of (#ind phi)))
                        of Var v => v
                         | _ => error "Bad induction rule")
   in Thm.instantiate (TVars.empty, Vars.make [(prop_var, Thm.cterm_of ctxt prop)]) (#ind phi)
        |> Phi_Help.beta_eta_contract
  end

fun chk_zero_index_thm thm =
  if Thm.maxidx_of thm <= 0
  then thm
  else error "Internal bug: not zero-indexed!"

fun chk_zero_index_term term =
  if Term.maxidx_of_term term <= 0
  then term
  else error "Internal bug: not zero-indexed!"

fun add_type (def, pos, hints) generic =
  let val ctxt = Context.proof_of generic
      val (idx,(name_ty,term)) =
           (case def of DIRECT_DEF (lhs, _) =>
                          (case Term.head_of lhs of X as Const name_ty => (~1, (name_ty, X))
                                                  | X as Free name_ty => (~1, (name_ty, X))
                                                  | _ => error "Bad definition: not a const")
                      | WFREC_DEF (name, info) =>
                          case get_index (fn X as Const (name', ty) =>
                                                if name = name' then SOME ((name', ty), X) else NONE
                                           | X as Free (name', ty) =>
                                                if name = name' then SOME ((name', ty), X) else NONE
                                           | _ => NONE) (#fs info)
                            of SOME idx_name_X => idx_name_X
                             | _ => error "Bad Function.info, the expected function is not\
                                          \ given inside.")
      fun filter_relevant_eqs name =
            filter (fn eq =>
              case Thm.concl_of eq
                of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                      Const(\<^const_name>\<open>HOL.eq\<close>, _) $ LHS $ _)
                    => (case Term.head_of LHS
                          of Const(N',_) => N' = name
                           | Free(N',_) => N' = name
                           | _ => false)
                 | Const(\<^const_name>\<open>Pure.eq\<close>, _) $ LHS $ _ =>
                       (case Term.head_of LHS
                          of Const(N',_) => N' = name
                           | Free(N',_) => N' = name
                           | _ => false)
                 | _ => false)
      val eqs = (case def of DIRECT_DEF (_, (_, eq)) => [eq]
                    | WFREC_DEF (name, info) =>
                        (case #simps info
                           of SOME eqs => filter_relevant_eqs name eqs
                            | NONE => (warning "Termination of the definition is not proven. \
                                               \Use partial simplification and induction rules.";
                                       filter_relevant_eqs name (#psimps info))))
              |> map (conv_def_to_equaltion ctxt
                   #> Phi_Help.beta_eta_contract)

      val is_recursive = exists (fn eq =>
            case Thm.concl_of eq
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ RHS)
                  => exists_subterm (fn Const (N',_) => N' = fst name_ty
                                      | Free (N',_) => N' = fst name_ty
                                      | _ => false) RHS
               | _ => error "Internal bug #fc2042c3-0c46-4ae5-a66e-9697639068a0") eqs

      val ind =
            (case def
               of DIRECT_DEF _ =>
                  let val eq = hd eqs
                      val LHS = Thm.dest_arg (Thm.cconcl_of eq) |> Thm.dest_arg1
                      val x = Thm.dest_arg1 LHS
                      fun mk_P ctm =
                        case Thm.term_of ctm
                          of _ $ _ => Thm.apply (mk_P (Thm.dest_fun ctm)) (Thm.dest_arg ctm)
                           | _ => let val P_ty = (binder_types (Thm.typ_of_cterm ctm) ---> \<^typ>\<open>bool\<close>)
                                              |> Thm.ctyp_of ctxt
                                      val i = Thm.maxidx_of_cterm ctm + 1
                                   in Thm.var (("P",i), P_ty)
                                  end
                      val T_x = Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.apply (mk_P (Thm.dest_arg LHS)) x)
                   in Thm.trivial T_x
                   |> Drule.zero_var_indexes
                  end
                | WFREC_DEF (_, info) =>
                    (case #inducts info
                       of SOME rules => List.nth (rules, idx)
                        | _ => List.nth (#pinducts info, idx))
            )
            |> Conv.fconv_rule (add_premise_tag ctxt)
            |> Phi_Help.beta_eta_contract

      val intro_ToA = map (fn eq => (eq RS @{thm \<phi>intro_transformation})
                                 |> Conv.fconv_rule (add_premise_tag ctxt)
                                 |> Drule.zero_var_indexes
                                 |> Phi_Help.beta_eta_contract) eqs

      val proof_id =
        case term of Const _ => fst name_ty
           | Free _ =>
              Context.cases Sign.full_name Local_Theory.full_name generic (Binding.name (fst name_ty))

      val phi_type = {
            term = chk_zero_index_term term,
            pos = pos,
            proof_id = proof_id,
            equations = map chk_zero_index_thm eqs,
            ind = chk_zero_index_thm ind,
            intro_ToA = map chk_zero_index_thm intro_ToA,
            is_recursive = is_recursive,
            is_impredicative = false
          } : phi_type
   in generic
   |> Context.mapping
        (Context.theory_map (Phi_Types.map (Symtab.update_new (fst name_ty, phi_trim_context phi_type))))
        (Local_Theory.declaration {syntax=false, pervasive=false} (fn m =>
          Phi_Types.map (Symtab.update_new (fst (raw_term_name_typ (Morphism.term m term)),
                                            morphism_phi_type m (phi_trim_context phi_type)))))
   |> Phi_Help.generic_theory_mapping (fn m =>
        Phi_Reasoner.add_intro_rules (map (fn rule =>
            ([Morphism.thm m rule], pos, Phi_Reasoner.TO_BE_OVERRIDE, 40, [], [], NONE)
        ) intro_ToA))
   |> Context.mapping (Context_Position.set_visible_global false)
                      (Context_Position.set_visible false)
   |> invoke_automations_on_def (phi_type, hints)
   |> Context_Position.restore_visible_generic generic
   |> pair phi_type
  end

(** Interface **)

(*fun theory_map_result f = apsnd Context.the_theory o f o Context.Theory;*)

fun dest_parameterized_phi_ty' args \<^Type>\<open>fun x \<open>\<^Type>\<open>set c\<close>\<close>\<close> = (args, x, c)
  | dest_parameterized_phi_ty' args \<^Type>\<open>fun a T\<close> = dest_parameterized_phi_ty' (a::args) T
  | dest_parameterized_phi_ty' _ T = raise TYPE ("not a phi-type",[T],[])

val dest_parameterized_phi_ty = dest_parameterized_phi_ty' []

fun fix_phi_term_params phi_term ctxt =
  let val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of phi_term)
      val arg_tys = rev rev_arg_tys
      val arg_names' = Name.invent (Variable.names_of ctxt) "A" (length arg_tys)
      val [x_name'] = Name.invent (Variable.names_of ctxt) "x" 1
      val (x_name::arg_names, ctxt') = Variable.add_fixes (x_name' :: arg_names') ctxt
      val args = map2 (fn N => fn T => Free(N,T)) arg_names arg_tys
      val x_term = Free(x_name, x_ty)
      val T_term = fold (fn a => fn X => X $ a) args phi_term
      val ctxt'2 = fold Variable.declare_constraints (x_term :: args) ctxt'
   in ((x_term, T_term, x_ty, arg_tys, model_ty), ctxt'2)
  end

fun instantiate_phi (inst,inst') =
      map_phi_type (Term_Subst.instantiate inst, map (Thm.instantiate inst'))

fun fix_phi_type is_open (phi0 : phi_type) ctxt0 =
  let val (inst, ctxt) = Variable.import_inst is_open [#term phi0] ctxt0
      val inst' = (TVars.map (K (Thm.ctyp_of ctxt)) (#1 inst),
                   Vars.map (K (Thm.cterm_of ctxt)) (#2 inst))
      val phi = instantiate_phi (inst,inst') phi0
   in (inst, inst', phi, ctxt)
  end


local

fun check_algebra_hints ctxt const hints =
  let val ctxt'0 = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
      val ((_, T_term', _, _, _), ctxt') = fix_phi_term_params const ctxt'0
      val T_term = singleton (Variable.export_terms ctxt' ctxt) T_term'
                |> Term.map_types (K Term.dummyT)
      fun get_arity ret \<^Type>\<open>fun a T\<close> = get_arity (a::ret) T
        | get_arity ret \<^Type>\<open>bool\<close> = ret
        | get_arity _ _ = error "The given hint is not an algebraic property."
      fun head_of (Const("_type_constraint_", _) $ X) = head_of X
        | head_of (X $ _) = head_of X
        | head_of X = X
      val hints_arity = map (fn hint =>
            get_arity [] (Sign.the_const_type (Proof_Context.theory_of ctxt')
                                             (fst (raw_term_name_typ (head_of hint))))) hints
      fun pad_term arity (\<^Const>\<open>Pure.imp\<close> $ LHS $ X) =
            \<^Const>\<open>Pure.imp\<close> $ LHS $ pad_term arity X
        | pad_term arity (\<^Const>\<open>Trueprop\<close> $ X) =
            pad_term arity X
        | pad_term arity term =
            let val i = Term.maxidx_of_term term + 1
                val k = Term.maxidx_of_term T_term + 1
                fun trim \<^Type>\<open>fun _ \<open>T as \<^Type>\<open>fun _ _\<close>\<close>\<close> (X $ _) = trim T X
                  | trim _ X = X
                fun pad _ [] X = X
                  | pad j (T::tys) X =
                      pad (i+1) tys X $ trim T (Logic.incr_indexes ([],[], i+j*k) T_term)
                fun pass ar (X as (Const("_type_constraint_", _) $ _)) = pad 0 ar X
                  | pass (_::ar) (X $ Y) = pass ar X $ Y
                  | pass ar X = pad 0 ar X                
             in \<^Const>\<open>Trueprop\<close> $ pass arity term
            end
   in Syntax.check_props ctxt'0 (map2 pad_term hints_arity hints)
  end

(*make (x : T) \<equiv> ...  to T x \<equiv> ...*)
val dirty_syntax_hack =
  let fun rewrite ((H as Const (\<^const_name>\<open>Pure.imp\<close>, _)) $ L $ R) =
            H $ L $ rewrite R
        | rewrite ((H as Const (\<^const_name>\<open>Pure.all\<close>, _)) $ Abs(N,T,X)) =
            H $ Abs(N,T, rewrite X)
        | rewrite ((H as Const (\<^const_name>\<open>Trueprop\<close>, _)) $ X) = H $ rewrite X
        | rewrite ((H as Const (\<^const_name>\<open>HOL.eq\<close>, _)) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T) $ R) =
            H $ (T $ x) $ R
        | rewrite ((H as Const (\<^const_name>\<open>Pure.eq\<close>, _)) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T) $ R) =
            H $ (T $ x) $ R
        | rewrite X = X
   in map rewrite
  end


local open Function_Lib
open Function_Common
open Function_Fun

fun is_phi_type \<^Type>\<open>fun _ \<open>\<^Type>\<open>set _\<close>\<close>\<close> = true
  | is_phi_type \<^Type>\<open>fun _ T\<close> = is_phi_type T
  | is_phi_type _ = false

fun gen_add_fun pos raw_hints add (generic : generic_theory) =
  let
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
    fun prove_termination lthy =
      Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy) lthy
      handle ERROR s =>
        raise (ERROR (s ^ "\n\
          \Fail to show the termination automatically. \
          \May use command \<open>\<phi>type_definition\<close> to prove the termination manually"))
    val (info, generic'1) = add pat_completeness_auto generic
    val const = find_first (is_phi_type o Term.fastype_of) (#fs info)
              |> (fn SOME x => x
                   | NONE => error "No \<phi>-type is defined.")
    val ctxt'1 = Context.proof_of generic'1
    val hints = check_algebra_hints ctxt'1 const (map (Syntax.parse_term ctxt'1) raw_hints)
   in generic'1
   |> Context.mapping_result (
        Named_Target.theory_map_result (Function_Common.transform_function_data) prove_termination
      ) prove_termination
   |-> (fn info => add_type (WFREC_DEF (fst (raw_term_name_typ const), info), pos, hints) #> snd)
  end

fun add_function_cmd a b c tac int lthy = lthy
  |> Context.proof_map (
        Syntax_Phases.term_check 99 "a dirty hack for rewriting the non-standard \<phi>-type definition"
          (K dirty_syntax_hack))
  |> Function.add_function_cmd a b c tac int

in

(* fun add_fun a b c = gen_add_fun (Function.add_function a b c) *)
fun add_fun_cmd a b c hints int generic =
  let val ctxt = Context.proof_of generic
   in gen_add_fun (Binding.pos_of (#1 (hd a))) hints
                  (fn tac =>
                      Context.mapping_result
                        (Named_Target.theory_map_result Function_Common.transform_function_data
                                                        (add_function_cmd a b c tac int))
                        (add_function_cmd a b c tac int)) generic
  end

end


val algebra_hints = Scan.repeat (\<^keyword>\<open>subj\<close> |-- Parse.term)

val def_by_fun = (Function_Common.function_parser Function_Fun.fun_config -- algebra_hints
      >> (fn ((config, (fixes, specs)), algebras) => add_fun_cmd fixes specs config algebras))

val def_by_function = (Function_Common.function_parser Function_Common.default_config
      >> (fn (config, (fixes, specs)) => Function.function_cmd fixes specs config))

fun my_definition decl params prems spec int lthy = lthy
  |> Context.proof_map (
        Syntax_Phases.term_check 99 "a dirty hack for rewriting the non-standard \<phi>-type definition"
          (K dirty_syntax_hack))
  |> Specification.definition_cmd decl params prems spec int

val def_direct = (Scan.option Parse_Spec.constdecl -- Parse.position (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes -- algebra_hints
        -- (Scan.option \<^keyword>\<open>|\<close> >> (fn SOME _ => Scan.fail () | _ => ()))
   >> (fn (((((decl, (spec, pos)), prems), params), hints), _) => fn int =>
        Context.mapping_result
          (Named_Target.theory_map_result (fn m => fn (tm, (name, def)) =>
                    (Morphism.term m tm, (name, Morphism.thm m def)))
                (my_definition decl params prems spec int))
          (my_definition decl params prems spec int)
           #> (fn (def, generic) =>
                let val ctxt = Context.proof_of generic
                 in add_type (DIRECT_DEF def, pos,
                              check_algebra_hints ctxt (fst def) (map (Syntax.parse_term ctxt) hints))
                         generic
                 |> snd
                end)
        ))
in
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<phi>type_def\<close> "define \<phi>-types"
          ((def_direct || def_by_fun) >> (fn f =>
              Toplevel.theory' (fn int => Context.theory_map (f int)) Toplevel.no_presentation))
end

end
