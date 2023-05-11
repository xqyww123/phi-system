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
  const: term (*of most general type*),
  pos : Position.T,
  proof_id: Phi_Cache_DB.proof_id,
  equations: thm list (*unfolding the term*),
  ind_ToA: thm option * thm (*inductively destructive transformation, of form
                   ... \<Longrightarrow> P a b c x \<longrightarrow> (R * x : T a b c \<longrightarrow> Y)  (*only available for sep-magma*)
               and ... \<Longrightarrow> P a b c x \<longrightarrow> (x : T a b c \<longrightarrow> Y) *),
  intro_ToA: thm list (*introduction transformations*),
  is_recursive: bool,
  is_impredicative: bool (*to be supported*)
}

val morphism_phi_type : morphism -> phi_type -> phi_type

type algebra_hints = term list

val get_type_info : Context.generic -> string (*const name*) -> phi_type option
val add_type : def * Position.T * algebra_hints -> generic_theory -> phi_type * generic_theory

type automation_on_def = phi_type * algebra_hints -> generic_theory -> generic_theory
val add_automation_on_def : priority -> automation_on_def -> Context.generic -> Context.generic

(* Tools *)

val fix_phi_type : bool -> term -> Proof.context -> (term * term * term * typ * typ) * Proof.context
val raw_term_name : term -> string

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
fun property_eq' thy ((t1,th1),(t2,th2)) = (t1 aconv t2) andalso Thm.equiv_thm thy (th1,th2)

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

fun is_a_registered_functor_i thy net the_functor =
  let val key = encode_functor the_functor
   in Net.match_term net key
        |> exists (fn (pat, _) => Pattern.matches thy (pat, the_functor))
  end

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
  const: term (*of most general type*),
  pos : Position.T,
  proof_id: Phi_Cache_DB.proof_id,
  equations: thm list (*unfolding the term*),
  ind_ToA: thm option * thm (*inductively destructive transformations*),
  intro_ToA: thm list (*introduction transformations*),
  is_recursive: bool,
  is_impredicative: bool (*to be supported*)
}

fun morphism_phi_type m (phi : phi_type) =
  {
    const = Morphism.term m (#const phi),
    pos = #pos phi,
    proof_id = #proof_id phi,
    equations = Morphism.fact m (#equations phi),
    ind_ToA = (Option.map (Morphism.thm m) (fst (#ind_ToA phi)), Morphism.thm m (snd (#ind_ToA phi))),
    intro_ToA = Morphism.fact m (#intro_ToA phi),
    is_recursive = #is_recursive phi,
    is_impredicative = #is_impredicative phi
  } : phi_type

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

val get_type_info = Symtab.lookup o Phi_Types.get

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
          of \<^Type>\<open>fun _ \<open>\<^Type>\<open>set _\<close>\<close>\<close> => (
                case RHS of Abs _ => def RS @{thm \<phi>Type_conv_eq_1}
                          | _ => def RS @{thm \<phi>Type_conv_eq_2})
           | \<^Type>\<open>set _\<close> => (
                case LHS of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => def
                          | _ $ _ => Conv.fconv_rule (Phi_Helper_Conv.hhf_concl_conv (fn ctxt =>
                                        HOLogic.Trueprop_conv (HOLogic.eq_conv
                                          (fn ctm =>
                                            Conv.rewr_conv (Drule.infer_instantiate ctxt
                                                [(("T",0),Thm.dest_fun ctm),
                                                 (("x",0),Thm.dest_arg ctm)]
                                                @{thm \<phi>Type_def[symmetric, folded atomize_eq]}) ctm)
                                          Conv.all_conv)
                                     ) ctxt) def)
           | _ => raise THM ("Not a \<phi>-type definition", 0, [def]))
     | _ => raise THM ("Not a \<phi>-type definition", 0, [def])

val induct_template = (\<^schematic_cterm>\<open>\<lambda>X::?'a::{sep_disj,times} set. (?R * X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?Q)\<close>,
                       \<^schematic_cterm>\<open>\<lambda>X::?'a set. (X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?Q)\<close>)

fun add_premise_tag ctm =
      if not (can Phi_Syntax.dest_implication (Thm.term_of ctm))
      then PLPR_Syntax.add_premise_tag_conv \<^cterm>\<open>default\<close> ctm
      else Conv.all_conv ctm

fun Trueprop_conv C ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
        HOLogic.Trueprop_conv C ctm
     | _ => C ctm

val add_premise_tag2 =
      Phi_Helper_Conv.premises_conv
        (fn ctxt => Trueprop_conv (fn ctm =>
          case Thm.term_of ctm
            of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
                  Phi_Helper_Conv.premises_conv (K add_premise_tag) (K Conv.all_conv) ctxt ctm
             | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
                  Phi_Helper_Conv.premises_conv (K add_premise_tag) (K Conv.all_conv) ctxt ctm
             | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                  Phi_Helper_Conv.premises_conv (K (Trueprop_conv add_premise_tag)) (K Conv.all_conv) ctxt ctm
             | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                  Phi_Helper_Conv.premises_conv (K (Trueprop_conv add_premise_tag)) (K Conv.all_conv) ctxt ctm
             | _ => Trueprop_conv add_premise_tag ctm
        ))
        (K Conv.all_conv)

fun unified_cterm_app f x =
  (Drule.mk_term x RS (Drule.mk_term f RS @{thm unified_cterm_app}))
    |> Drule.dest_term

fun set_the_P_in_ind_from_direct_def has_R ctxt ind =
  let val imp = Thm.dest_arg (Thm.dest_arg (Thm.cconcl_of ind)) |> Thm.dest_fun
      val U = Thm.dest_arg imp
      val x_T = imp |> Thm.dest_fun |> Thm.dest_arg |> has_R ? Thm.dest_arg
      val x = Thm.dest_arg1 x_T
      fun mk_P_typ \<^Type>\<open>set _\<close> = \<^typ>\<open>bool\<close>
        | mk_P_typ \<^Type>\<open>fun x T\<close> = x --> mk_P_typ T
      fun mk_P ctm =
        case try Thm.dest_comb ctm
          of SOME (f,x) => Thm.apply (mk_P f) x
           | NONE => Thm.var (("P",0), Thm.ctyp_of ctxt (mk_P_typ (Thm.typ_of_cterm ctm)))
      val P = Thm.apply (mk_P (Thm.dest_arg x_T)) x
   in Thm.instantiate (TVars.empty, Vars.make [((("P",0),\<^typ>\<open>bool\<close>),P)]) ind
  end

fun mk_ind_dest_ToA ctxt (const_name,typ) eqs ind = (*not tested*)
  let fun parse_typ args \<^Type>\<open>fun x \<open>\<^Type>\<open>set a\<close>\<close>\<close> = (args, x, a)
        | parse_typ args \<^Type>\<open>fun a r\<close> = parse_typ (a::args) r
      val (arg_tys, x_ty, model_ty) = parse_typ [] typ
      val arity = length arg_tys
      val term_T = fold_index (fn (i,_) => fn X => X $ Bound (arity-i)) arg_tys (Const(const_name,typ))
      val term_P = fold_index (fn (i,_) => fn X => X $ Bound (arity-i)) arg_tys
                      (Var (("P",0), arg_tys ---> x_ty --> \<^typ>\<open>bool\<close>)) $ Bound 0
      val term_xT = Abs("", x_ty, \<^Const>\<open>implies\<close> $ term_P
                                                 $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ term_T))
      val goal = Abs ("", \<^Type>\<open>fun \<^Type>\<open>set model_ty\<close> \<^Type>\<open>bool\<close>\<close>,
                    fold (fn T => fn X => Abs("",T,X)) arg_tys term_xT)
               |> Thm.cterm_of ctxt
      val prop_var = (case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of ind))
                        of Var v => v
                         | _ => error "Bad induction rule")
      val sctxt = clear_simpset ctxt addsimps eqs
      val dest1 = try (unified_cterm_app goal) (fst induct_template)
                |> Option.map (fn fx =>
                    Thm.instantiate (TVars.empty, Vars.make [(prop_var, fx)]) ind
                      |> Conv.fconv_rule (Conv.prems_conv ~1 (Simplifier.asm_rewrite sctxt)
                              then_conv add_premise_tag2 ctxt))
      val dest2 = Thm.instantiate (TVars.empty,
                      Vars.make [(prop_var, Thm.apply goal (snd induct_template))]) ind
                |> Conv.fconv_rule (Conv.prems_conv ~1 (Simplifier.asm_rewrite sctxt)
                        then_conv add_premise_tag2 ctxt)
   in (dest1,dest2)
  end

fun raw_term_name (Const (N,_)) = N
  | raw_term_name (Free (N,_)) = N

fun add_type (def, pos, hints) generic =
  let val ctxt = Context.proof_of generic
      val (idx,(name_ty,const)) =
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
              |> map (conv_def_to_equaltion ctxt)
      val is_recursive = exists (fn eq =>
            case Thm.concl_of eq
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ RHS)
                  => exists_subterm (fn Const (N',_) => N' = fst name_ty
                                      | Free (N',_) => N' = fst name_ty
                                      | _ => false) RHS
               | _ => error "Internal bug #fc2042c3-0c46-4ae5-a66e-9697639068a0") eqs

      val ind_ToA =
            (case def
               of DIRECT_DEF _ =>
                  let val eq = Thm.incr_indexes 1 (hd eqs)
                   in (try (fn rule => eq RS rule) @{thm \<phi>inductive_destruction_rule_from_direct_definition}
                        |> Option.map (Conv.fconv_rule (add_premise_tag2 ctxt)
                              #> set_the_P_in_ind_from_direct_def true ctxt),
                       (eq RS @{thm \<phi>inductive_destruction_rule_from_direct_definition'})
                        |> Conv.fconv_rule (add_premise_tag2 ctxt)
                        |> set_the_P_in_ind_from_direct_def false ctxt)
                  end
                | WFREC_DEF (_, info) =>
                    (case #inducts info
                       of SOME rules => mk_ind_dest_ToA ctxt name_ty eqs (List.nth (rules, idx))
                        | _ => mk_ind_dest_ToA ctxt name_ty eqs (List.nth (#pinducts info, idx)))
            )

      val intro_ToA = map (fn eq => (eq RS @{thm \<phi>intro_transformation})
                                 |> Conv.fconv_rule (add_premise_tag2 ctxt)) eqs

      val proof_id =
        case const of Const _ => fst name_ty
           | Free _ =>
              Context.cases Sign.full_name Local_Theory.full_name generic (Binding.name (fst name_ty))

      val phi_type = {
            const = const,
            pos = pos,
            proof_id = proof_id,
            equations = eqs,
            ind_ToA = ind_ToA,
            intro_ToA = intro_ToA,
            is_recursive = is_recursive,
            is_impredicative = false
          } : phi_type
   in generic
   |> Context.mapping
        (Context.theory_map (Phi_Types.map (Symtab.update_new (fst name_ty, phi_type))))
        (Local_Theory.declaration {syntax=false, pervasive=false} (fn m =>
          Phi_Types.map (Symtab.update_new (raw_term_name (Morphism.term m const),
                                            morphism_phi_type m phi_type))))
   |> Phi_Help.generic_theory_mapping (fn m =>
        Phi_Reasoner.add_intro_rules (map (fn rule =>
            ([Morphism.thm m rule], pos, Phi_Reasoner.TO_BE_OVERRIDE, 40, [], [], NONE)
        ) intro_ToA))
   |> invoke_automations_on_def (phi_type, hints)
   |> pair phi_type
  end

(** Interface **)

fun theory_map_result f = apsnd Context.the_theory o f o Context.Theory;


fun fix_phi_type is_open const0 ctxt0 =
  let val ([const],ctxt) = Variable.import_terms is_open [const0] ctxt0
      fun collect_types args \<^Type>\<open>fun x \<open>\<^Type>\<open>set c\<close>\<close>\<close> = (args, x, c)
        | collect_types args \<^Type>\<open>fun a T\<close> = collect_types (a::args) T
        | collect_types args T = raise TYPE ("not a phi-type",[T],[])
      val (arg_tys, x_ty, c_ty) = collect_types [] (Term.fastype_of const)
      val arg_names' = Name.invent (Variable.names_of ctxt) "A" (length arg_tys)
      val [x_name'] = Name.invent (Variable.names_of ctxt) "x" 1
      val (x_name::arg_names, ctxt') = Variable.add_fixes (x_name' :: arg_names') ctxt
      val args = map2 (fn N => fn T => Free(N,T)) arg_names arg_tys
      val x_term = Free(x_name, x_ty)
      val ctxt'2 = fold Variable.declare_constraints (x_term :: args) ctxt'
   in ((x_term, fold_rev (fn a => fn X => X $ a) args const, const, x_ty, c_ty), ctxt'2)
  end

local

fun check_algebra_hints ctxt const hints =
  let val ctxt'0 = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
      val ((_, T_term', _, _, _), ctxt') = fix_phi_type false const ctxt'0
      val T_term = singleton (Variable.export_terms ctxt' ctxt) T_term'
      fun get_arity ret \<^Type>\<open>fun _ T\<close> = get_arity (ret+1) T
        | get_arity ret \<^Type>\<open>bool\<close> = ret
        | get_arity _ _ = error "The given hint is not an algebraic property."
      fun head_of (Const("_type_constraint_", _) $ X) = head_of X
        | head_of (X $ _) = head_of X
        | head_of X = X
      val hints_arity = map (fn hint =>
            get_arity 0 (Sign.the_const_type (Proof_Context.theory_of ctxt')
                                             (raw_term_name (head_of hint)))) hints
      fun pad_term arity term =
        let fun term_arity ret (Const("_type_constraint_", _) $ X) = term_arity ret X
              | term_arity ret (X $ _) = term_arity (ret+1) X
              | term_arity ret _ = ret
            val d = arity - term_arity 0 term
            val _ = if d < 0 then error "Internal bug 3bc2ce92-edce-427a-a401-24152b11bc81"
                             else ()
         in funpow d (fn X => X $ Logic.incr_indexes ([],[], Term.maxidx_of_term X + 1) T_term) term
        end
   in Syntax.check_terms ctxt'0 (map2 pad_term hints_arity hints)
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
    val hints = check_algebra_hints (Context.proof_of generic) const raw_hints
   in generic'1
   |> Context.mapping_result (Named_Target.theory_map_result (K I) prove_termination) prove_termination
   |-> (fn info => add_type (WFREC_DEF (raw_term_name const, info), pos, hints) #> snd)
  end

in

(* fun add_fun a b c = gen_add_fun (Function.add_function a b c) *)
fun add_fun_cmd a b c hints int generic =
  let val ctxt = Context.proof_of generic
   in gen_add_fun (Binding.pos_of (#1 (hd a)))
                  (map (Syntax.parse_term ctxt) hints)
                  (fn tac =>
                      Context.mapping_result
                        (Named_Target.theory_map_result (K I) (Function.add_function_cmd a b c tac int))
                        (Function.add_function_cmd a b c tac int)) generic
  end

end


val algebra_hints = Scan.repeat (\<^keyword>\<open>is\<close> |-- Parse.term)

val def_by_fun = (Function_Common.function_parser Function_Fun.fun_config -- algebra_hints
      >> (fn ((config, (fixes, specs)), algebras) => add_fun_cmd fixes specs config algebras))

val def_by_function = (Function_Common.function_parser Function_Common.default_config
      >> (fn (config, (fixes, specs)) => Function.function_cmd fixes specs config))

val def_direct = (Scan.option Parse_Spec.constdecl -- Parse.position (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes -- algebra_hints
   >> (fn ((((decl, (spec, pos)), prems), params), hints) => fn int =>
        Context.mapping_result
          (Named_Target.theory_map_result (fn m => fn (tm, (name, def)) =>
                    (Morphism.term m tm, (name, Morphism.thm m def)))
                (Specification.definition_cmd decl params prems spec int))
          (Specification.definition_cmd decl params prems spec int)
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
