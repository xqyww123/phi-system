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

signature PHI_TYPE = sig

include PHI_TYPE


(** \<phi>-Type Definition \& Infos **)

datatype def = DIRECT_DEF of thm (*def*) | WFREC_DEF  of Function.info
datatype parameter_equality = PE_Synt | PE_Guard | PE_Proof

type parameter_info = {
  name: string option (*not always given*),
  mutating: bool option, (*if the parameter mutates throughout the (recursive) definition.
                           we are not always able to check if a parameter mutates from definition*)
  equality: parameter_equality (*Two \<phi>-types \<open>T a\<^sub>1 \<cdots> a\<^sub>n\<close> and \<open>T a\<^sub>1' \<cdots> a\<^sub>n'\<close> are *)
}

type phi_type = {
  name: binding,
  term: term (*of most general type and schematic variables*),
  params: parameter_info list (*the default name of the parameters. note the abstract object is not considered as a parameter*),
  cterm: thm (*TERM <the_cterm>*),
  pos : Position.T,
  equations: thm list (*definitional equations, in HOL.eq*),
  type_equations: thm option list,
                  (*the equations are given between BI assertions, \<open>x : T = y : U\<close>.
                    Here the type equations are given between types, \<open>T = U\<close>.
                    However, depending on definitions, not all \<phi>-types have such equations.*)
  cases: thm option,
  ind: thm option,
    (*inductively destructive transformation, of form
     has_R: ... \<Longrightarrow> ?P.0 a b c x \<longrightarrow> (?R.0 * x : T a b c \<longrightarrow> ?Y.0 and ?Q.0)  (*only available for sep-magma*)
     full:  ... \<Longrightarrow> ?P.0 a b c x \<longrightarrow> (x : T a b c \<longrightarrow> ?Y.0 a b c x and ?Q.0 a b c x)
     dom_only: ... \<Longrightarrow> ?P.0 a b c x \<longrightarrow> (x : T a b c \<longrightarrow> ?Y.0 and ?Q.0) *)
  intro_reasoning: thm list (*introduction transformations*),
  is_recursive: bool,
  is_impredicative: bool (*to be supported*)
} (*rules and terms inside must be zero-indexed*)

val map_phi_type : (binding -> binding) * (term -> term) * (thm list -> thm list) -> phi_type -> phi_type
val fold_phi_type : (term -> 'a -> 'a) * (thm -> 'a -> 'a) -> phi_type -> 'a -> 'a
val has_mutating_params : phi_type -> bool
val may_has_mutating_params : phi_type -> bool
val parameters_of : phi_type -> (parameter_info * typ) list
val parameters_and_typs_of : phi_type -> (parameter_info * typ) list * typ (*abstract typ*) * typ (*concrete typ*)

val morphism_phi_type : morphism -> phi_type -> phi_type
val instantiate_phi : (ctyp TVars.table * cterm Vars.table)
                   -> phi_type -> phi_type
val phi_trim_context : phi_type -> phi_type
val phi_transfer : theory -> phi_type -> phi_type
val maxidx_of_phi : phi_type -> int -> int

type hint = term

val get_type_info : Context.generic -> term -> phi_type option

(** Property Deriver from \<phi>-Type Definition **)
type priority = int
type deriver_name = string
type is_weak = bool
type quiet = bool (*report nothing even when fail*)
(*type deriving_ctxt = Proof.context (*the context used for deriving rules, which may be prepared
                                     specially with user configurations*)*)
type derive = phi_type -> local_theory -> local_theory
type arbi_ind_args = term list (*free variables that will be generalized before induction,
                                           apply (induct arbitrary: <NAMES OF THOSE VARIABLES>) *)
type deriving_instruction = (hint * arbi_ind_args) option
                          * Reasoner_Group.group option
                          * Position.T
                          * Method.text option               (*tactic hints*)
                          * (thm list * attribute list) list (*notes*)
                          * Bundle.name list
type deriver = {
  priority: priority,
  dependences: (deriver_name * is_weak) list,
      (*a weak dependency is invoked in quiet mode, meaning no error will be reported on failure,
        and not activated when any hint is given to the deriver depending on the weak dependency.
        Once users give an annotation, every implicit behavior is revoked, and this is the only
        way to revoke the implicit behavior.
        Users may declare a weak dependency by append a question mark after the dependency name.*)
  derive: quiet * Position.T (*where does the deriving happen*) -> deriving_instruction list -> derive
}

val get_deriver : Context.generic -> deriver_name -> deriver
val check_deriver : Context.generic -> xstring * Position.T -> deriver_name * deriver
val deriver_name_space : Context.generic -> deriver Name_Space.table
val define_deriver : binding -> deriver -> local_theory -> string * local_theory
val define_deriver_global : binding -> deriver -> theory -> string * theory

type pattern = term
val bind_derivers_on_patterns : (pattern * deriver_name) list -> Context.generic -> Context.generic
val match_deriver : Context.generic -> hint -> (deriver_name * deriver) option
exception Unknown_Hint of term
val match_deriver1 : Context.generic -> hint -> deriver_name * deriver

structure Derivings : TABLE
type derivings = (deriving_instruction list * deriver * is_weak * Position.T) Derivings.table
val add_deriving : deriving_instruction list * (deriver_name * deriver) * Position.T -> derivings -> derivings
val add_deriving_from_hint : Context.generic -> deriving_instruction -> derivings -> derivings

val add_deriver_dependences : Position.T -> bool -> Context.generic -> (deriver_name * is_weak) list -> derivings -> derivings
val complete_deriver_dependences : Context.generic -> derivings -> derivings

val derive_properties : derivings * Bundle.name list -> phi_type -> local_theory -> local_theory
    (*no need to call it manually. It is invoked by `add_type` *)
val under_deriving_ctxt : bool Config.T

structure Deriving_Hooks : HOOKS
type deriving_hook = phi_type -> derivings * local_theory -> derivings * local_theory

(* Derived Properties *)

val lookup_derived_properties : Context.generic -> phi_type -> string (*name*) -> thm list list
      (*the name is not necessarily the name of the deriver as a deriver can derive multiple
        properties. It is the name that is sent by the deriver when it calls `register_derived_properties`.*)
val register_derived_properties : phi_type -> string * int * Position.T -> thm list -> local_theory -> local_theory
      (*It will also bind in Isabelle the properties to names <phi_type_name.property_names\<^sub>i>
        for the i-th property each.*)
val print_derived_properties : Context.generic -> string * int * Position.T -> Pretty.T list -> unit

val note_properties' : bool (*true for no_atp*) -> string -> (binding * thm list) list -> local_theory -> local_theory
val note_properties  : bool (*true for no_atp*) -> phi_type -> (binding * thm list) list -> local_theory -> local_theory
val note_properties_s: bool (*true for no_atp*) -> phi_type -> (bstring * thm list) list -> local_theory -> local_theory

val local_note_properties' : string -> (binding * thm list) list -> Context.generic -> Context.generic
val local_note_properties  : phi_type -> (binding * thm list) list -> Context.generic -> Context.generic
val local_note_properties_s: phi_type -> (bstring * thm list) list -> Context.generic -> Context.generic

val suffix_name_by_index : int -> string -> string

(* Syntax *)

type deriving_ast
val deriving_parser : deriving_ast list parser
val check_deriving_ast : Context.generic -> deriving_ast list -> derivings


(** Define \<phi>-Type and invoke derivings **)

structure Defining_Phi_Type : HOOKS (*invoked before any deriving*)
val add_type : {no_auto: bool}
            -> binding * term * def * Position.T
             * derivings
             * Bundle.name list
             * parameter_equality option list option
            -> local_theory -> phi_type * local_theory

val override_ind_rule : term * thm -> Context.generic -> Context.generic

(** Tools **)

val is_term_of_phi : phi_type -> term -> bool (*ignores type*)
val assert_Type_Opr : typ -> unit
val assert_first_parameter_is_type : typ -> unit
    (*note the T below is a \<phi>-type parameter*)
val separate_tyopr_and_its_typ_param : bv_typs -> term (*F(T)*) -> (term (*T*) * term (*F*)) Seq.seq
val separate_tyopr_and_its_non_parameterized_typ_param : bv_typs -> term (*F(T)*) -> (term (*T*) * term (*F*)) Seq.seq
val separate_tyopr_and_its_non_parameterized_typ_param_safe : bv_typs -> term (*F(T)*) -> (term (*T*) * term (*F*)) Seq.seq
val separate_tyopr_and_its_non_parameterized_typ_params : bvs -> term (*F(T\<^sub>1,T\<^sub>2,...)*) -> term list (*T\<^sub>1,T\<^sub>2,...*) * term (*F*)
val separate_tyopr_and_its_typ_params : bvs -> term (*F(T\<^sub>1,T\<^sub>2,...)*) -> term list (*T\<^sub>1,T\<^sub>2,...*) * term (*F*)
val separate_tyopr_and_its_typ_param_safe : bv_typs -> term (*F(T)*) -> (term (*T*) * term (*F*)) Seq.seq
val separate_module_tyopr : bv_typs -> term (*F\<^sub>c(T)*) -> (term (*T*) * term (*c*) * term (*F*)) option
val separate_scalar_tyopr : bv_typs -> term (*F\<^sub>c(T)*) -> (term option (*T*) * term (*c*) * term (*F*)) option

val def_contains_satisfaction : phi_type -> bool

(*make inductively destruction rule.*)
val mk_ind_dest_ToA : Proof.context -> phi_type -> (term (*x*) * term (*T*) -> term) -> thm
val mk_ind_dest_ToA_internal : Proof.context -> phi_type -> term -> thm

val is_phi_type_fixed : phi_type -> bool

val fix_phi_type : bool -> phi_type -> Proof.context ->
        (ctyp TVars.table * cterm Vars.table) * phi_type *
        Proof.context

val fix_phi_term_params : phi_type -> Proof.context -> (term * term) * Proof.context
        (*only fix the terms but no types*)

(* Auxiliaries *)

val open_proof_ctxt : Bundle.name list -> Proof.context -> Proof.context

(*for mutating params {p\<^sub>i}
 \<open>  condition p\<^sub>1 = p\<^sub>1'
\<Longrightarrow> condition p\<^sub>2 = p\<^sub>2'
\<Longrightarrow> \<dots>
\<Longrightarrow> condition p\<^sub>n = p\<^sub>n'
\<Longrightarrow> T p\<^sub>1 p\<^sub>2 \<dots> p\<^sub>n = T p\<^sub>1' p\<^sub>2' \<dots> p\<^sub>n' \<close>
*)
val mk_mutating_param_eq : Proof.context -> term (*mode of condition equation*) -> phi_type -> thm

(* Internal Technical stuffs *)

val ML_sender : (quiet * Position.T -> deriving_instruction list -> derive) option Unsynchronized.ref

(* Suggest some property should be derived *)

val chk_deriving_or_derived : string * string -> phi_type -> derivings * Proof.context -> bool
val suggest_property_should_be_derived : (Proof.context -> phi_type -> (string * string) option)
                                      -> (Proof.context -> phi_type -> unit)
                                      -> deriving_hook

(** Controllers **)

(*val search_CSTR_rules : bool Config.T*)
  (*if to enable branched searching in the reasoning of MAKE and OPEN for different definition equantions
    used to construct or destruct \<phi>-types*)

end


(**** Implementation ****)

structure Phi_Type : PHI_TYPE = struct

open Phi_Type

(** Library **)

fun open_proof_ctxt bundles ctxt = ctxt
    |> not (null bundles) ? (
          Config.put Phi_Reasoner.ignore_dup_reasoner true
       #> Bundle.includes bundles
       #> Config.restore Phi_Reasoner.ignore_dup_reasoner ctxt)
    |> Config.put augment_ToA_by_implication true

(*** \<phi>-Type Definition \& Infos ***)

val introN = "intro"
val intro_reasoningN = "intro_reasoning" (*rules for reasoning*)
val intro_reasoning_R_N = "intro_reasoning\<^sub>R"
val intro_mapN = "intro_map"
val elimN = "elim"
val elim_reasoningN = "elim_reasoning"
val elim_mapN = "elim_map"
val unfoldN = "unfold"
val unfold_valN = "unfold_val"
val expansionN = "expansion"
(* val open_abstractionN = "open_abstraction" *)

datatype def = DIRECT_DEF of thm (*def*)
             | WFREC_DEF  of Function.info

datatype parameter_equality = PE_Synt | PE_Guard | PE_Proof

type parameter_info = {
  name: string option,
  mutating: bool option, (*if the parameter mutates throughout the (recursive) definition.
                           we are not always able to check if a parameter mutates from definition*)
  equality: parameter_equality
}

type phi_type = {
  name: binding,
  term: term (*of most general type*),
  params: parameter_info list, (*the abstract object is not considered a parameter*)
  cterm: thm,
  pos : Position.T,
  equations: thm list (*unfolding the term*),
  type_equations: thm option list,
  ind: thm option,
  cases: thm option,
  intro_reasoning: thm list (*introduction transformations*),
  is_recursive: bool,
  is_impredicative: bool (*to be supported*)
}

fun has_mutating_params phi =
  exists ((fn SOME true => true | _ => false) o #mutating) (#params phi)

fun may_has_mutating_params phi =
  exists ((fn SOME false => false | _ => true) o #mutating) (#params phi)

fun map_phi_type (mb,mtm,mth) (phi : phi_type) =
  {
    name = mb (#name phi),
    term = mtm (#term phi),
    params = #params phi,
    cterm = singleton mth (#cterm phi),
    pos = #pos phi,
    equations = mth (#equations phi),
    type_equations = burrow_options mth (#type_equations phi),
    ind = Option.map (singleton mth) (#ind phi),
    cases = Option.map (singleton mth) (#cases phi),
    intro_reasoning = mth (#intro_reasoning phi),
    is_recursive = #is_recursive phi,
    is_impredicative = #is_impredicative phi
  } : phi_type

fun set_ind ind (phi : phi_type) =
  {
    name = #name phi,
    term = #term phi,
    params = #params phi,
    cterm = #cterm phi,
    pos = #pos phi,
    equations = #equations phi,
    type_equations = #type_equations phi,
    ind = SOME ind,
    cases = #cases phi,
    intro_reasoning = #intro_reasoning phi,
    is_recursive = #is_recursive phi,
    is_impredicative = #is_impredicative phi
  } : phi_type

fun fold_phi_type (fold_tm, fold_thm) (phi : phi_type) x = x
  |> fold_tm (#term phi)
  |> fold fold_thm (#equations phi)
  |> (case #ind phi of SOME i => fold_thm i | _ => I)
  |> fold fold_thm (#intro_reasoning phi)

fun morphism_phi_type m = map_phi_type (Morphism.binding m, Morphism.term m, Morphism.fact m)
val phi_trim_context = map_phi_type (I, I, map (Thm.trim_context))
fun phi_transfer thy = map_phi_type (I, I, map (Thm.transfer thy))
val maxidx_of_phi = fold_phi_type (Term.maxidx_term, Thm.maxidx_thm)

type hint = term

fun phi_typ_binding_eq (phi1, phi2) = #name phi1 = #name phi2
fun phi_typ_term_eq (phi1, phi2) = #term phi1 = #term phi2
fun phi_typ_term_equiv thy (phi1, phi2) = Pattern.equiv thy (#term phi1, #term phi2)

structure Phi_Types = Generic_Data (
  type T = phi_type Net.net
  val empty = Net.empty
  val merge = Net.merge phi_typ_binding_eq
)

fun get_type_info ctxt term =
      Option.map (phi_transfer (Context.theory_of ctxt))
                 (Net.match_term (Phi_Types.get ctxt) term
                    |> filter (curry (Pattern.equiv (Context.theory_of ctxt)) term o #term)
                    |> try hd)

fun override_ind_rule (term, ind) ctxt =
  Phi_Types.map (fn net =>
    let val phis = Net.match_term net term
                |> filter (curry (Pattern.equiv (Context.theory_of ctxt)) term o #term)
        val phis' = map (set_ind (Thm.trim_context ind)) phis
     in net
     |> fold (fn phi => Net.delete_term phi_typ_term_eq (#term phi, phi)) phis
     |> fold (fn phi => Net.insert_term phi_typ_term_eq (#term phi, phi)) phis
    end) ctxt

(*
fun add_automation_on_def priority automation ctxt =
  Automation_on_Def.map (PriorityTab.update_new (
      (priority, Context.theory_long_name (Context.theory_of ctxt)), automation)) ctxt

fun invoke_automations_on_def (phi,hints) ctxt =
  case PriorityTab.fold (fn (_,s) => s phi) (Automation_on_Def.get ctxt) (hints, ctxt)
    of ([], ctxt') => ctxt'
     | (hints, ctxt') => let open Pretty in
          error (string_of (chunks (
            (str "Do not know how to derive the properties:") ::
            map (fn H =>
              item [Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt' H]
            ) hints)))
       end
*)

(** Pretty Printer **)

local open Pretty in
fun pretty_parameter_equality PE_Synt  = keyword2 "id"
  | pretty_parameter_equality PE_Guard = keyword2 "guard"
  | pretty_parameter_equality PE_Proof = keyword2 "obligation"

end

(** Impl of Basic Conversions **)

val add_premise_tag = Phi_Conv.recursive_premises_conv (fn _ => fn ctm =>
      case Thm.term_of ctm
        of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _) =>
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
  | raw_term_name_typ X = raise TERM ("Not a Const nor Free", [X])

val raw_term_name = fst o raw_term_name_typ o Term.head_of

fun mk_ind_dest_ToA_internal ctxt (phi : phi_type) prop0 =
  let val typ = Term.fastype_of (#term phi)
      fun parse_typ args \<^Type>\<open>fun x \<open>\<^Type>\<open>set a\<close>\<close>\<close> = (args, x, a)
        | parse_typ args \<^Type>\<open>fun a r\<close> = parse_typ (a::args) r
        | parse_typ _ _ = error "Internal bug"
      val (rev_arg_tys, x_ty, _) = parse_typ [] typ

      val prop = prop0
              |> (fn X => Abs("",x_ty,X))
              |> fold (fn T => fn X => Abs("",T,X)) rev_arg_tys
      val prop_var = (case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of (the (#ind phi))))
                        of Var v => v
                         | _ => error "Bad induction rule")
   in Thm.instantiate (TVars.empty, Vars.make [(prop_var, Thm.cterm_of ctxt prop)]) (the (#ind phi))
        |> Phi_Help.beta_eta_contract
  end

fun mk_ind_dest_ToA ctxt phi gen_prop =
  let val typ = Term.fastype_of (#term phi)
      fun parse_typ args \<^Type>\<open>fun x \<open>\<^Type>\<open>set a\<close>\<close>\<close> = (args, x, a)
        | parse_typ args \<^Type>\<open>fun a r\<close> = parse_typ (a::args) r
        | parse_typ _ _ = error "Internal bug"
      val (rev_arg_tys, x_ty, _) = parse_typ [] typ
      val x_term = Bound 0
      val arity = length rev_arg_tys
      val T_term = fold_index (fn (i,_) => fn X => X $ Bound (arity-i)) rev_arg_tys (#term phi)

      val prop = gen_prop (x_term, T_term)
              |> (fn X => Abs("",x_ty,X))
              |> fold (fn T => fn X => Abs("",T,X)) rev_arg_tys
      val idx = Term.maxidx_of_term prop + 1
      val ind = Thm.incr_indexes idx (the (#ind phi))
      val prop_var = (case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of ind))
                        of Var (v,_) => v
                         | _ => error "Bad induction rule")
   in Drule.infer_instantiate ctxt [(prop_var, Thm.cterm_of ctxt prop)] ind
        |> Phi_Help.beta_eta_contract
  end

(** Tools **)

fun def_contains_satisfaction phi =
  let val contains_sat = Term.exists_subterm (fn Const(\<^const_name>\<open>Satisfaction\<close>, _) => true
                                               | _ => false)
      fun phi_contains_sat (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = phi_contains_sat X
        | phi_contains_sat (Abs(_,_,X)) = phi_contains_sat X
        | phi_contains_sat (Const(\<^const_name>\<open>Subjection\<close>, _) $ A $ P) = contains_sat P orelse phi_contains_sat A
        | phi_contains_sat _ = false
      fun eq_contains_sat (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = eq_contains_sat X
        | eq_contains_sat (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ X) = phi_contains_sat X
        | eq_contains_sat (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ X) = phi_contains_sat X
        | eq_contains_sat (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = eq_contains_sat X
        | eq_contains_sat X = raise TERM ("def_contains_satisfaction", [X])
   in exists (eq_contains_sat o Thm.prop_of) (#equations phi)
  end

fun parameters_of phi = #params phi ~~ rev (#1 (dest_parameterized_phi_ty (Term.fastype_of (#term phi))))
fun parameters_and_typs_of (phi:phi_type) =
  let val (rev_atys, x_ty, m_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
   in (#params phi ~~ rev rev_atys, x_ty, m_ty)
  end

fun fix_phi_term_params phi ctxt =
  let val (params, x_ty, _) = parameters_and_typs_of phi
      val (x_name :: param_names, ctxt') =
              Variable.variant_fixes (
                  "x" :: map (the_default "A" o #name o fst) params) ctxt
      val param_terms = map2 (fn N => fn (_,T) => Free(N,T)) param_names params
      val x_term = Free(x_name, x_ty)
      val T_term = fold (fn a => fn X => X $ a) param_terms (#term phi)
   in ((x_term, T_term), ctxt')
  end

(*** Deriving Properties ***)

(** Data Types **)

type priority = int
type deriver_name = string
type derive = phi_type -> local_theory -> local_theory
type arbi_ind_args = term list (*free variables that will be generalized before induction*)
type deriving_instruction = (hint * arbi_ind_args) option
                          * (Phi_Reasoner.priority * Reasoner_Group.name option) option
                          * Position.T
                          * Method.text option
                          * (thm list * attribute list) list (*notes*)
                          * Bundle.name list
type is_weak = bool
type quiet = bool
type deriver = {
  priority: priority,
  dependences: (deriver_name * is_weak) list,
  derive: quiet * Position.T -> deriving_instruction list -> derive
}

structure Derivers = Generic_Data (
  type T = deriver Name_Space.table
  val empty = Name_Space.empty_table "\<phi>deriver"
  val merge = Name_Space.merge_tables
)

structure Derivings = Table (type key = priority * deriver_name; val ord = prod_ord int_ord string_ord)
type derivings = (deriving_instruction list * deriver * is_weak * Position.T) Derivings.table

type pattern = term
structure Deriver_Bindings = Generic_Data (
  type T = (pattern * deriver_name) Net.net
  val empty = Net.empty
  val merge = Net.merge (op =)
)

type deriving_hook = phi_type -> derivings * local_theory -> derivings * local_theory
structure Deriving_Hooks = Hooks (
  type arg = phi_type
  type state = derivings * local_theory
)

fun chk_deriver ctxt (derv : deriver) =
  let val names = Derivers.get ctxt
   in #dependences derv
   |> map (Name_Space.get names o fst)
   |> forall (fn der' => #priority derv > #priority der')
   |> (fn true => derv
        | false => error "The priority of the deriver must be larger than its dependences.")
  end

val deriver_name_space = Derivers.get
val get_deriver = Name_Space.get o Derivers.get
val deriver_ops = { get_data = Derivers.get, put_data = Derivers.put }

fun define_deriver bind derv ctxt =
      Entity.define deriver_ops bind (chk_deriver (Context.Proof ctxt) derv) ctxt
fun define_deriver_global bind derv ctxt =
      Entity.define_global deriver_ops bind (chk_deriver (Context.Theory ctxt) derv) ctxt

fun check_deriver ctxt = Name_Space.check ctxt (Derivers.get ctxt)

fun bind_derivers_on_patterns pat_derivers =
  Deriver_Bindings.map (fold (fn (pat, deriver) =>
      let val pat' = Envir.beta_eta_contract pat
       in Net.insert_term (op =) (pat', (pat', deriver))
      end
    ) pat_derivers)

fun match_deriver ctxt term =
  let val net = Deriver_Bindings.get ctxt
      val thy = Context.theory_of ctxt
   in Net.match_term net term
   |> map_filter (fn (pat, deriver) =>
        if Pattern.matches thy (pat, term)
        then SOME (deriver, get_deriver ctxt deriver)
        else NONE)
   |> sort (fn (a,b) => int_ord (#priority (snd b), #priority (snd a)))
   |> (fn [] => NONE
        | (h :: _) => SOME h)
  end

exception Unknown_Hint of term
fun match_deriver1 ctxt term =
  case match_deriver ctxt term
    of SOME ret => ret
     | NONE => raise Unknown_Hint term

fun add_deriving (hints : deriving_instruction list, (derv_name, derv), pos) (dervs : derivings)=
  Derivings.map_default ((#priority derv, derv_name), ([], derv, false, pos))
                        (fn (hints', der', _, pos) => (hints @ hints', der', false, pos)) dervs

fun add_deriving_from_hint ctxt (derv_instr as (SOME (hint, _),_,pos,_,_,_)) (ders : derivings) =
  add_deriving ([derv_instr], match_deriver1 ctxt (Logic.strip_imp_concl hint), pos) ders

fun add_deriver_dependences _ _ _ [] dervs = dervs
  | add_deriver_dependences pos count_weak ctxt deps dervs =
      let val derivers = deriver_name_space ctxt
          fun add [] dervs = dervs
            | add ((dep,is_weak)::remain_deps) dervs =
                if is_weak andalso not count_weak
                then dervs
                else let val derv = Name_Space.get derivers dep
                         val key = (#priority derv, dep)
                      in(case Derivings.lookup dervs key
                      of SOME (hints, deriver, is_weak', pos) =>
                            if is_weak' = (is_weak' andalso is_weak)
                            then dervs
                            else Derivings.update (key, (hints, deriver, is_weak' andalso is_weak, pos)) dervs
                                    |> add (#dependences derv)
                       | NONE => Derivings.update_new (key, ([], derv, is_weak, pos)) dervs
                                    |> add (#dependences derv)
                       ) |> add remain_deps
                     end
       in add deps dervs
      end

fun complete_deriver_dependences ctxt dervs =
  Derivings.fold (fn (_,(hints,derv,_,pos)) =>
      add_deriver_dependences pos (forall (is_none o #1) hints) ctxt (#dependences derv)) dervs dervs

val _ = Theory.setup (
  ML_Antiquotation.value \<^binding>\<open>\<phi>deriver\<close>
    (Scan.peek (fn ctxt => Parse.name_position >> (fn name =>
        check_deriver ctxt name
          |> apsnd #priority
          |> ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_int )))
)

(** Deriving **)

val under_deriving_ctxt = Attrib.setup_config_bool \<^binding>\<open>under_\<phi>deriving\<close> (K false)

fun err_derive ctxt prop_name msg hints = let open Pretty in
      error (string_of (chunks (
        block [str "Fail to derive the property ", str prop_name] ::
        msg @
        (if null hints
         then [para "The guessed property may be wrong, and you may provide the \
                    \desired property form by \<open>deriving \<open>the property you want\<close>\<close>."]
         else []) @
        (case Phi_Reasoners.failure_reasons_of ctxt
           of [] => []
            | L => para "There are some potential reasons for the failure" :: L)
      )))
      end

fun derive_properties (dervs:derivings, bundles) phityp (thy:local_theory) =
  let val level = Local_Theory.level thy
      val dervs = complete_deriver_dependences (Context.Proof thy) dervs
      fun setup ctxt = ctxt
            |> Context.proof_map (
                  Phi_Reasoner.start_collecting_reasoners (the (snd @{reasoner_group %all_derived_rules})))
            |> Context_Position.set_visible false
            |> open_proof_ctxt bundles
            |> Config.put under_deriving_ctxt true
            |> Phi_Reasoners.report_failure_reason []
   in thy
   |> Local_Theory.map_contexts (fn i => if i >= level - 1 then setup else I)
   |> pair dervs
   |> Deriving_Hooks.invoke (Context.Proof thy) phityp
   |> (fn (dervs, thy) =>
     let val dervs = complete_deriver_dependences (Context.Proof thy) dervs
      in thy
   |> Derivings.fold (fn ((_,name),(hints,derv,is_weak,pos)) => fn lthy =>
          lthy |> snd o Local_Theory.begin_nested
               |> Context_Position.set_visible false
               |> #derive derv (is_weak, pos) hints phityp
               |> Local_Theory.end_nested
          handle Automation_Fail msg => err_derive lthy name (msg ()) hints
       ) dervs
     end)
(*TODO: un-setup*)
    (*|> Context.proof_map (
          Phi_Reasoner.stop_collecting_reasoners (the (snd @{reasoner_group %all_derived_rules})))*)
  end

(** Derived Properties **)

val dp_eq = eq_pair3 (op aconv) (op =) (eq_list pointer_eq)
structure Derived_Properties = Generic_Data (
  type T = (term (*phityp*) * int (*index*) * thm list) Net.net
  val empty = Net.empty
  val merge = Net.merge dp_eq
)

fun lookup_derived_properties ctxt phi name =
  Net.match_term (Derived_Properties.get ctxt) (Const(name, dummyT) $ #term phi)
    |> map_filter (fn (_ $ tm, _, th) =>
          if Pattern.equiv (Context.theory_of ctxt) (tm, #term phi)
          then SOME th
          else NONE)

fun short_name_of_tyop (Abs (_,_,X)) = short_name_of_tyop X
  | short_name_of_tyop (X $ _) = short_name_of_tyop X
  | short_name_of_tyop (Const (N, _)) = Long_Name.base_name N
  | short_name_of_tyop (Free (N, _)) = N
  | short_name_of_tyop X = raise TERM ("Not a \<phi>-type term", [X])

val no_atp_attrs = map (Attrib.attribute_global \<^theory>) @{attributes [no_atp]}
fun note_properties' no_atp prefix notes =
  let val qualify = Binding.qualify true prefix
   in fold (fn (b,Th) =>
        snd o Local_Theory.note ((qualify b, if no_atp then @{attributes [no_atp]} else []), Th)
      ) notes
  end

fun local_note_properties' prefix notes ctxt =
  let val facts = Context.cases Global_Theory.facts_of Proof_Context.facts_of ctxt
      fun varify_binding i b =
        let val b' = if i = 0 then b else Binding.suffix_name ("_" ^ string_of_int i) b
            val iname = Context.cases Sign.full_name Proof_Context.full_name ctxt b'
         in if Facts.defined facts iname
            then varify_binding (i+1) b
            else b
        end
      val notes' = map (fn (b',rules') =>
            let val b = varify_binding 0 (Binding.qualify true prefix b')
             in ((b, []), [(rules',[])])
            end) notes
   in Context.mapping (fold (snd oo Global_Theory.note_thms "") notes')
                      (fold (snd oo Proof_Context.note_thms "") notes') ctxt
  end

fun note_properties no_atp (phi : phi_type) = note_properties' no_atp (Binding.name_of (#name phi))
fun note_properties_s no_atp phi notes =
      note_properties no_atp phi (map (fn (N,th) => (Binding.make (N, #pos phi), th)) notes)

fun local_note_properties (phi : phi_type) = local_note_properties' (Binding.name_of (#name phi))
fun local_note_properties_s phi notes =
      local_note_properties phi (map (fn (N,th) => (Binding.make (N, #pos phi), th)) notes)


fun suffix_name_by_index ind name =
      if ind = 0 then name else suffix ("\<^sub>" ^ string_of_int ind) name

fun add_derived_properties phi (name, pos) ths ctxt =
  let val ind = length (lookup_derived_properties ctxt phi name)
      val key = Const(name, dummyT) $ (#term phi)
   in Derived_Properties.map (Net.insert_term dp_eq (key, (key, ind, ths))) ctxt
  end

fun print_derived_properties ctxt (name, ind, pos) pps =
  Phi_Reasoner.info_pretty_generic ctxt ~1 (fn () =>
    let open Pretty
     in block [str (suffix_name_by_index ind name), brk 1,
               chunks (map (fn p => item [p]) pps)]
    end)

fun register_derived_properties phi (name, ind, pos) ths thy =
  let val ind' = length (lookup_derived_properties (Context.Proof thy) phi name)
      val _ = if ind' = ind then () else error "Bad Index"
      val _ = print_derived_properties (Context.Proof thy)
                                       (name, ind, pos) (map (Thm.pretty_thm thy) ths)
   in Local_Theory.declaration {syntax=false,pervasive=false, pos=pos} (fn m =>
        let val key = Const(name, dummyT) $ Morphism.term m (#term phi)
            val ths' = Morphism.fact m ths
         in Derived_Properties.map (Net.insert_term dp_eq (key, (key, ind, ths')))
        end) thy
  end

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>type_property\<close>
  (Phi_Reasoner.attr_syntax
    (Args.const {proper = false, strict = false} -- Scan.lift Parse.name)
    (fn (pos, mode, raw_group, (const, prop_name), pats, guard) =>
      Thm.declaration_attribute (fn rule => fn ctxt =>
        let val group = SOME (the_default @{reasoner_group %\<phi>TA_property} raw_group)
            val ctxt_parse = Context.proof_of ctxt
            val term = Proof_Context.read_term_pattern ctxt_parse const
            val phi = case get_type_info ctxt term
                  of SOME phi => phi
                   | NONE => error ("No \<phi>-type named "^ Syntax.string_of_term ctxt_parse term ^ " found")
         in ctxt
         |> add_derived_properties phi (prop_name, pos) [rule]
         |> Phi_Reasoner.add_rule pos mode group pats guard [rule] 
        end)))
  "declares \<phi>type properties"

)

(** Simple Checkers **)

(* Suggest some property should be derived *)

fun chk_deriving_or_derived (deriver_name, prop_name) (phi_type : phi_type) (derving, ctxt) =
  let val (deriver_name, deriver) = check_deriver (Context.Proof ctxt) (deriver_name, Position.none)
   in Derivings.defined derving (#priority deriver, deriver_name) orelse
      not (null (lookup_derived_properties (Context.Proof ctxt) phi_type prop_name))
  end

fun suggest_property_should_be_derived P warn (phi_type : phi_type) (derving, lthy) =
  case P lthy phi_type
    of SOME (deriver_name, prop_name) => (
        if chk_deriving_or_derived (deriver_name, prop_name) phi_type (derving, lthy)
        then ()
        else warn lthy phi_type ;
        (derving, lthy) )
     | _ => (derving, lthy)


(** Syntax **)

datatype deriving_ast' = Derv_By_Name of xstring * Position.T
                       | Derv_By_Term of ((string * Position.T) * string list (*arbi_ind_args*)) * Reasoner_Group.priority_syntax option
type deriving_ast = deriving_ast'
                  * (Facts.ref * Token.src list) list (*notes*)
                  * (xstring * Position.T) list (*bundles used only in the deriving*)
                  * Method.text_range option (*tactic hint*)

val deriving_name = Parse.position (
        Parse.group (fn () => "name") (Parse.short_ident || Parse.long_ident))
val one_deriving = deriving_name >> Derv_By_Name
                || (Parse.position Parse.term -- Scan.option (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>)
                      >> (fn (t,g) => Derv_By_Term ((t,[]),g)))

fun set_ast_aia aia (Derv_By_Name x)
      = if null aia then Derv_By_Name x
                    else error "bad 'arbitrary' clause: no term annotation is given"
  | set_ast_aia aia (Derv_By_Term ((tm,_), gp))
      = Derv_By_Term ((tm,aia), gp)

val deriving_parser : deriving_ast list parser = Scan.repeat (
        \<^keyword>\<open>deriving\<close> |-- Parse.and_list (
            one_deriving --
            Scan.optional (\<^keyword>\<open>notes\<close> |-- Parse.thms1) [] --
            Scan.optional (\<^keyword>\<open>opening\<close> |-- Scan.repeat1 Parse.name_position) [] --
            Scan.optional (\<^keyword>\<open>(\<close> |-- Args.$$$ "arbitrary" |-- \<^keyword>\<open>:\<close> |-- Scan.repeat1 Parse.term --| \<^keyword>\<open>)\<close>) [] --
            Scan.option (\<^keyword>\<open>(\<close> |-- Args.$$$ "tactic" |-- \<^keyword>\<open>:\<close> |-- Method.parser 0 --| \<^keyword>\<open>)\<close>)
        >> (fn ((((a,b),c),d),e) => (set_ast_aia d a,b,c,e)))
      ) >> flat

(*
fun check_property_hint ctxt phi_typ_const hint =
  let val ctxt'0 = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
      val ((x_term, T_term'), ctxt'1) = fix_phi_term_params phi_typ_const ctxt'0
      val ctxt' = fold Variable.declare_constraints [x_term,T_term'] ctxt'1
      val T_term = singleton (Variable.export_terms ctxt' ctxt) T_term'
                |> Term.map_types (K Term.dummyT)
      fun get_arity ret \<^Type>\<open>fun a T\<close> = get_arity (a::ret) T
        | get_arity ret \<^Type>\<open>bool\<close> = ret
        | get_arity _ _ = error "The given hint is not an algebraic property."
      fun head_of (Const("_type_constraint_", _) $ X) = head_of X
        | head_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = head_of X
        | head_of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = head_of X
        | head_of (X $ _) = head_of X
        | head_of X = X
      val hint_arity = get_arity [] (Sign.the_const_type (Proof_Context.theory_of ctxt')
                                    (fst (raw_term_name_typ (head_of hint))))
      fun pad_term arity ((H as Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _) $ X) =
            H $ pad_term arity X
        | pad_term arity (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) =
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
      val props = Syntax.check_props ctxt'0 [pad_term hint_arity hint]
      val ctxt'1 = fold Variable.add_fixes_implicit props (Variable.set_body false ctxt'0)
   in hd (Variable.export_terms ctxt'1 ctxt props)
  end*)

fun check_deriving_ast ctxt (derv_ast : deriving_ast list) =
  let val ctxt_parse = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of ctxt)
      val thy = Context.theory_of ctxt
      fun chk_text text = ( Method.report text ; Method.check_text ctxt_parse (fst text))
      val chk_bundles = map (Bundle.check ctxt_parse)
      val chk_notes = map (apfst (Proof_Context.get_fact ctxt_parse) #>
                           apsnd (map (Attrib.attribute_cmd ctxt_parse)))
   in Derivings.empty
   |> fold_rev (
        fn (Derv_By_Name name, notes, bundle, text) =>
            add_deriving ([(NONE, NONE, snd name, Option.map chk_text text, chk_notes notes, chk_bundles bundle)],
                          check_deriver ctxt name, snd name)
         | (Derv_By_Term (((term, pos), arbi_ind_args), raw_group), notes, bundle, text) =>
            let val term' = Syntax.parse_prop ctxt_parse term
                         |> Syntax.check_prop ctxt_parse
                         |> Envir.beta_eta_contract
                         |> Phi_Help.refine_sorts_of_tm thy
                val ctxt'1 = Variable.add_fixes_implicit term' (Variable.set_body false ctxt_parse)
                          |> Variable.declare_term term'
                val aia'0 = map (Syntax.parse_term ctxt'1) arbi_ind_args
                       |> Syntax.check_terms ctxt'1
                val (term'1::aia'1) = Variable.export_terms ctxt'1 ctxt_parse (term'::aia'0)
                val group = Option.map (Reasoner_Group.check_group true (Context.Proof ctxt'1)) raw_group
             in add_deriving_from_hint ctxt (SOME (term'1,aia'1), group, pos, Option.map chk_text text,
                                             chk_notes notes, chk_bundles bundle)
            end
       ) derv_ast
   handle Unknown_Hint term =>
      error (Pretty.string_of (Pretty.chunks [
          Pretty.para "Do not know how to derive from the given hint. There is no known deriver for it.",
          Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt term
        ]))
  end

(** Interfaces for Derivers **)

val ML_sender_locker = Synchronized.var "\<phi>TA.ML_sender_locker" ()
val ML_sender : (quiet * Position.T -> deriving_instruction list -> derive) option Unsynchronized.ref
  = Unsynchronized.ref NONE

val dependences_parse = Scan.optional (\<^keyword>\<open>requires\<close> |--
                            Parse.and_list (Scan.repeat (deriving_name -- Scan.optional (\<^keyword>\<open>?\<close> >> K true) false)) >> flat) []
val patterns_parse = Scan.optional (\<^keyword>\<open>for\<close> |-- \<^keyword>\<open>(\<close> |-- Parse.enum "|" Parse.term --| \<^keyword>\<open>)\<close> ) []
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<phi>property_deriver\<close>
          "declare deriver deriving properties when defining a \<phi>-type"
    (Parse.binding -- Parse.int -- patterns_parse -- dependences_parse-- (Scan.option (\<^keyword>\<open>=\<close> |-- Parse.ML_source))
 >> (fn ((((name,priority),raw_binding_terms),deps),ML') => Toplevel.theory (fn thy =>
   let 
       val derive =
            case ML' of SOME ML =>
                let val expr = ML_Lex.read "Phi_Type.ML_sender := SOME (" @
                               ML_Lex.read_source ML @
                               ML_Lex.read ")"
                 in Synchronized.change_result ML_sender_locker (fn () => let
                      val _ = ML_Context.expression (Input.pos_of ML) expr (Context.Theory thy)
                      val ret = the (!ML_sender)
                       in (ret, ML_sender := NONE)
                      end)
                end
              | NONE => K (K (K I))
       val deriver = {
          priority = priority,
          dependences = map (apfst (fst o check_deriver (Context.Theory thy))) deps,
          derive = derive
        } : deriver
       val ctxt_parser = Proof_Context.set_mode Proof_Context.mode_pattern (Proof_Context.init_global thy)
       val binding_props = map (Syntax.parse_prop ctxt_parser) raw_binding_terms
                        |> Syntax.check_props ctxt_parser
    in define_deriver_global name deriver thy
    |-> (fn der_name => Context.theory_map (
              bind_derivers_on_patterns (map (rpair der_name) binding_props)))
   end
   )))

(** Parameter Equality **)

structure Default_Equality = Type_Pattern_Store (struct
  type T = parameter_equality
  val eq = (op =)
  val export = K (K I)
end)

fun default_eq_of ctxt typ =
  case Default_Equality.get_uniq ctxt typ
    of NONE => if Phi_Syntax.is_phi_type_ty typ then PE_Synt else PE_Guard
     | SOME ret  => #4 ret


val parameter_equality = Args.$$$ "guard"  >> K PE_Guard
                      || Args.$$$ "id" >> K PE_Synt
                      || Args.$$$ "obligation"  >> K PE_Proof

val parameter_equality' = Scan.option (
      \<^keyword>\<open>parameter_equality\<close> |-- \<^keyword>\<open>(\<close> |--
        Parse.list1 (parameter_equality >> SOME || Args.$$$ "_"  >> K NONE) --| \<^keyword>\<open>)\<close> )

val _ = Theory.setup (
      Default_Equality.setup_decl_attr \<^binding>\<open>\<phi>parameter_default_equality\<close>
          parameter_equality parameter_equality
          (apfst o Syntax.read_typ)
          "declaring the default equality of \<phi>-type parameters under a certain type"
(*
   #> Default_Equality.setup_decl_ML_attr \<^binding>\<open>\<phi>parameter_default_equality_ML\<close>
          Syntax.read_typ
          "declaring the default equality of \<phi>-type parameters under a certain type" *)
)

(** Ad-hoc derivation **)

(*
val to_cond_rewr = @{lemma \<open>
        (A \<equiv> B) \<equiv> Trueprop (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = B)
  \<close> by (simp add: atomize_eq Premise_def) }
*)

val rule_refl1 = @{lemma \<open>
        T \<equiv> U
    \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U @tag \<T>\<P>
  \<close> by (simp add: Action_Tag_def transformation_refl) }

val rule_refl_WR = @{lemma \<open>
        T \<equiv> T'
    \<Longrightarrow> x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x, unspec) \<Ztypecolon> (T' \<^emph> U) \<^emph>[False] \<top>\<^sub>\<phi> @tag \<T>\<P>'
  \<close> by (simp add: Action_Tag_def transformation_refl) }

fun gen_refl_Tr term ctxt cong =
  if Thm.no_prems cong
  then []
  else let
      val (rev_param_tys, x, m_ty) = Phi_Syntax.dest_parameterized_phi_ty (fastype_of term)
      val param_tys = rev rev_param_tys
      val idx = maxidx_of_term term + 1
      val idx = idx + idx
      val T = fold_index (fn (i,ty) => fn X => X $ Var(("A",idx+i), ty))
                         param_tys term
      val idx = idx + length rev_param_tys
      val U = fold_index (fn (i,ty) => fn X => X $ Var(("A",idx+i), ty))
                         param_tys term
      val idx = idx + length rev_param_tys
      val (a,b) = (TVar(("a", idx), \<^sort>\<open>sep_magma\<close>), TVar(("b", idx), \<^sort>\<open>sep_magma\<close>))

      val cong = cong

      fun mk_pat x T y U tag =
        \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close>
            $ (\<^Const>\<open>Transformation m_ty\<close>
                $ (\<^Const>\<open>\<phi>Type x m_ty\<close> $ Var (("x",idx),x) $ T)
                $ (\<^Const>\<open>\<phi>Type y m_ty\<close> $ Var (("var_y",idx),y) $ U)
                $ Var (("P",idx), \<^Type>\<open>bool\<close>) )
            $ tag)

   in (@{reasoner_group %ToA_derv_unify_refl},
       mk_pat x T x U \<^Const>\<open>\<T>\<P>\<close>,
       cong RS' (ctxt, rule_refl1)) ::
      ( [(@{reasoner_group %ToA_derv_unify_refl},
          mk_pat \<^Type>\<open>prod x a\<close> (\<^Const>\<open>Cond_\<phi>Prod x m_ty a\<close> $ T
                                    $ Var(("C\<^sub>W",idx),\<^Type>\<open>bool\<close>)
                                    $ Var(("W",idx), Phi_Syntax.mk_phi_type_ty (m_ty, a)))
                \<^Type>\<open>prod x b\<close> (\<^Const>\<open>Cond_\<phi>Prod x m_ty b\<close> $ U
                                    $ Var(("C\<^sub>R",idx),\<^Type>\<open>bool\<close>)
                                    $ Var(("R",idx), Phi_Syntax.mk_phi_type_ty (m_ty, b)))
                \<^Const>\<open>\<T>\<P>'\<close>,
         cong RS' (ctxt, rule_refl_WR))]
        handle THM _ => [] )
  end

(*** \<phi>-Type Definition ***)

(** Tools **)

fun identical_name (Const(N, _), Const(N', _)) = N = N'
  | identical_name (Free(N, _), Free(N', _)) = N = N'
  | identical_name (Var(N, _), Var(N', _)) = N = N'
  | identical_name (A $ B, A' $ B') = identical_name (A,B) andalso identical_name (A',B')
  | identical_name (Abs (_, _, X), Abs (_, _, X')) = identical_name (X, X')
  | identical_name (Bound i, Bound i') = i = i'
  | identical_name _ = false

fun is_term_of_phi phi term = identical_name (Term.head_of (#term phi), term)

fun assert_Type_Opr ty =
  if Phi_Syntax.is_nonnull_Type_Opr ty then ()
  else raise Automation_Fail (fn () => [Pretty.str "Not a \<phi>-type operator!"])

fun is_first_parameter_a_type ty =
  case dest_parameterized_phi_ty ty
    of ([],_,_) => false
     | (ty' :: _,_,_) => (
  (case dest_parameterized_phi_ty ty'
    of ([],_,_) => true
     | _ => false)
  handle TYPE _ => false)

fun assert_first_parameter_is_type ty =
  if is_first_parameter_a_type ty then ()
  else raise Automation_Fail (fn () => [Pretty.str "Not a \<phi>-type operator!"])

local

datatype prev = Arg of term | Abst of string * typ
fun assemble (Arg a) X = X $ a
  | assemble (Abst (N,ty)) X = Abs (N, ty, X)

fun name_of (Free (N,_)) = N
  | name_of (Var ((N,_),_)) = N
  | name_of _ = "A"

in

(*in the reversed order*)
fun gen_separate_tyopr_and_its_typ_param chk bvtys FT_term =
  let fun split (lv, prevs, bvtys) (F $ T) =
            if chk (bvtys, T)
            then Seq.make (fn () =>
                 F
              |> not (null prevs) ? (fn F =>
                      (F $ Bound lv)
                   |> fold assemble prevs 
                   |> (fn X => Abs("T", Term.fastype_of1 (bvtys, T), X)))
              |> (fn X => SOME ((T, X), split (lv, Arg T :: prevs, bvtys) F)))
            else split (lv, Arg T :: prevs, bvtys) F
        | split (lv, prevs, bvtys) (Abs (N,ty,X)) = split (lv+1, Abst (N,ty)::prevs, ty::bvtys) X
        | split _ _ = Seq.empty
   in split (0, [], bvtys) (Phi_Help.beta_eta_contract_term FT_term)
  end

fun gen_separate_tyopr_and_its_typ_params chk bvs =
  let fun split (lv, bvs, Ts, prevs) (F $ T) =
            if chk (bvs, T)
            then split (lv, (name_of T, Term.fastype_of T)::bvs, T :: Ts, Arg (Bound (lv + length bvs)) :: prevs) F
            else split (lv, bvs, Ts, Arg T :: prevs) F
        | split (lv, bvs, Ts, prevs) (Abs (N,ty,X)) = split (lv+1, bvs, Ts, Abst (N,ty)::prevs) X
        | split (_, bvs, Ts, prevs) X = fold assemble prevs X
                                     |> fold (fn (N,T) => fn X => Abs (N,T,X)) bvs
                                     |> Phi_Help.beta_eta_contract_term
                                     |> pair Ts
   in split (0, bvs, [], [])
  end

end

val separate_tyopr_and_its_typ_param_safe =
  gen_separate_tyopr_and_its_typ_param (can dest_parameterized_phi_ty o Term.fastype_of1)

val separate_tyopr_and_its_non_parameterized_typ_params =
  gen_separate_tyopr_and_its_typ_params (Phi_Syntax.is_non_parameterized_phityp o Term.fastype_of1 o apfst (map snd))

val separate_tyopr_and_its_typ_params =
  gen_separate_tyopr_and_its_typ_params (can dest_parameterized_phi_ty o Term.fastype_of1 o apfst (map snd))

val separate_tyopr_and_its_non_parameterized_typ_param_safe =
  gen_separate_tyopr_and_its_typ_param (Phi_Syntax.is_non_parameterized_phityp o Term.fastype_of1)


fun separate_module_tyopr bvtys tm =
  case tm of F $ c $ T => if can dest_parameterized_phi_ty (Term.fastype_of1 (bvtys, T)) andalso
                             not (can dest_parameterized_phi_ty (Term.fastype_of1 (bvtys, c)))
                          then SOME (T, c, F)
                          else NONE
           | _ => NONE

fun separate_scalar_tyopr bvtys tm =
  case tm of F $ c $ T =>
              let val ty_c = Term.fastype_of1 (bvtys, c)
                  val ty_T = Term.fastype_of1 (bvtys, T)
               in if can dest_parameterized_phi_ty ty_T andalso
                     not (can dest_parameterized_phi_ty ty_c)
                  then SOME (SOME T, c, Phi_Help.beta_eta_contract_term (
                                  Abs ("\<s>", ty_c, Term.incr_boundvars 1 F $ Bound 0 $ Term.incr_boundvars 1 T)))
                  else NONE
              end
           | F $ c => if can dest_parameterized_phi_ty (Term.fastype_of1 (bvtys, c))
                      then NONE
                      else SOME (NONE, c, F)
           | _ => NONE

(*
fun separate_tyop_semimodule_and_its_non_parameterized bvtys tm =
     gen_separate_tyopr_and_its_typ_param (Phi_Syntax.is_non_parameterized_phityp o Term.fastype_of1) bvtys tm
  |> maps (fn (T, Fc) =>
        gen_separate_tyopr_and_its_typ_param (K true) bvtys Fc
          |> map (fn (c, F) => (T, c, F)))
*)

fun warn_separate_type_operator f bvtys FT_term =
  case Seq.pull (f bvtys FT_term)
    of NONE => raise Automation_Fail (fn () => let open Pretty in
                  [block [str "Fail to parse", brk 1,
                          str (Term.term_name (Term.head_of FT_term)),
                          str "as a type operator."]]
               end)
     | SOME (h,L) => Seq.cons h L

val separate_tyopr_and_its_typ_param =
      warn_separate_type_operator separate_tyopr_and_its_typ_param_safe
val separate_tyopr_and_its_non_parameterized_typ_param =
      warn_separate_type_operator separate_tyopr_and_its_non_parameterized_typ_param_safe

fun chk_zero_index_thm thm =
  if Thm.maxidx_of thm <= 0
  then thm
  else error "Internal bug: not zero-indexed!"

fun chk_zero_index_term term =
  if Term.maxidx_of_term term <= 0
  then term
  else error "Internal bug: not zero-indexed!"

fun normalize th = th
  |> Phi_Help.beta_eta_contract
  |> Drule.zero_var_indexes



   





(*val search_CSTR_rules = Config.declare_bool ("search_CSTR_rules", \<^here>) (K false)*)

(** Main **)

structure Defining_Phi_Type = Hooks(
  type arg = phi_type
  type state = local_theory
)

val refine_typeq = @{lemma \<open>(\<And>x. (x \<Ztypecolon> T) = (x \<Ztypecolon> U)) \<Longrightarrow> T = U\<close> by (rule \<phi>Type_eqI, simp)}

fun LHS_of (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ LHS $ _) = LHS
  | LHS_of (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ LHS $ _) = LHS
  | LHS_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = LHS_of X
  | LHS_of (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = LHS_of X
  | LHS_of X = raise TERM ("Not an equation", [X])

(*for mutating params {p\<^sub>i}
 \<open>  condition p\<^sub>1 = p\<^sub>1'
\<Longrightarrow> condition p\<^sub>2 = p\<^sub>2'
\<Longrightarrow> \<dots>
\<Longrightarrow> condition p\<^sub>n = p\<^sub>n'
\<Longrightarrow> T p\<^sub>1 p\<^sub>2 \<dots> p\<^sub>n = T p\<^sub>1' p\<^sub>2' \<dots> p\<^sub>n' \<close>
*)
fun mk_mutating_param_eq ctxt mode phi =
  let val params = #params phi
      val (rev_param_tys, x_ty, m_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val param_tys = rev rev_param_tys
      val i = maxidx_of_term (#term phi) + 1
      val pp's = map_index (fn (d, param) =>
                  let val name = the_default "A" (#name (#1 param))
                      val can_be_mutating = case #mutating (#1 param)
                                              of SOME false => false
                                               | _ => true
                   in (Var((name, i+d+d), #2 param),
                       if can_be_mutating then SOME (Var((name, i+d+d+1), #2 param)) else NONE)
                  end) (params ~~ param_tys)

      val T = list_comb (#term phi, map #1 pp's)
      val T'= list_comb (#term phi, map (fn (_, SOME x) => x | (x, _) => x) pp's)
      val base_eq = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.eq \<open>mk_phi_type_ty (m_ty, x_ty)\<close>\<close> $ T $ T')
      val prem_eqs = map_filter (fn (_, NONE) => NONE
                        | (p, SOME p') => SOME (\<^Const>\<open>Trueprop\<close> $ (
                              \<^Const>\<open>Premise\<close> $ mode $ (
                                \<^Const>\<open>HOL.eq \<open>Term.fastype_of p\<close>\<close> $ p $ p')))) pp's
      val goal = fold_rev (fn P => fn X => \<^Const>\<open>Pure.imp\<close> $ P $ X) prem_eqs base_eq
              |> Thm.cterm_of ctxt
              |> Goal.init
      val ((_, [goal']), ctxt') = Variable.import false [goal] ctxt
   in case Seq.pull (Simplifier.safe_asm_lr_simp_tac (
                        Simplifier.clear_simpset ctxt addsimps @{thms' Premise_def}) 1 goal')
   of SOME (ret, _) =>
          if Thm.no_prems ret
          then singleton (Variable.export ctxt' ctxt) (Goal.conclude ret)
          else error "BUG OOcP1KyCRTmJj4WTzbQWrA"
    | NONE => error "BUG OOcP1KyCRTmJj4WTzbQWrA"
  end

(*ctxt: the context used to derive properties*)
(*term: the term of the phi type, can be parameterized by fixed free variables like those in locales *)
fun add_type {no_auto} (binding, term, def, pos, dervs, bundles, equality) thy =
  let val ctxt = open_proof_ctxt bundles thy delsimps @{thms' One_nat_def}
      val term = chk_zero_index_term term

      fun match_head head (term as f $ _) = Term.aconv_untyped (head, term) orelse match_head head f
        | match_head head term = Term.aconv_untyped (head, term)

      fun get_idx_in_def_eqs lhs =
            case find_index (fn (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T) => match_head term (T $ x)
                              | X => match_head term X) lhs
              of ~1 => error ("The given term " ^ Syntax.string_of_term ctxt term ^ " \
                              \is not defined inside the given definition")
               | i => i

      val idx_in_def_eqs =
           (case def of DIRECT_DEF eq => get_idx_in_def_eqs [LHS_of (Thm.concl_of eq)]
                      | WFREC_DEF info => get_idx_in_def_eqs (#fs info))

      fun filter_relevant_eqs term = filter (match_head term o LHS_of o Thm.concl_of)
      val eqs = (case def of DIRECT_DEF eq => [eq]
                    | WFREC_DEF info =>
                        (case #simps info
                           of SOME eqs => filter_relevant_eqs term eqs
                            | NONE => (warning "Termination of the definition is not proven. \
                                               \Use partial simplification and induction rules.";
                                       filter_relevant_eqs term (#psimps info))))
              |> map (conv_def_to_equation ctxt
                   #> normalize)
      val _ = if null eqs then error "At least one definitional equation has to be given" else ()
      val tagged_eqs = map (Conv.fconv_rule (add_premise_tag ctxt)) eqs

      val typeqs = map (fn eq => SOME (eq RS refine_typeq) handle THM _ => NONE) eqs

      val fixed_num = length (snd (strip_comb term))
      val param_names = map (fn eq =>
                          case LHS_of (Thm.concl_of eq)
                            of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T =>
                                  map (fn Var ((N,_),Ty) => SOME N
                                        | Free (N,_) => SOME N
                                        | _ => NONE)
                                      (List.drop (snd (strip_comb T), fixed_num))
                             | _ => error "BUG") eqs
                      |> foldl1 (uncurry (map2 (curry merge_options)))

      val (rev_param_tys, x_ty, m_ty) = Phi_Syntax.dest_parameterized_phi_ty (fastype_of term)
            (*case LHS_of (Thm.concl_of (hd eqs))
               of Const(\<^const_name>\<open>\<phi>Type\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun ty _\<close>\<close>) $ _ $ _
                    => Phi_Syntax.dest_parameterized_phi_ty ty
                | _ => error "BUG" *)
      val param_tys = rev rev_param_tys

      val tagged_eqs_in_type =
            if no_auto then [] else
            map (try (Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
              HOLogic.Trueprop_conv (Conv.arg_conv (fn ctm =>
                Phi_Conv.embed_BI_assertion_into_phi_type ctxt ctm
                handle CTERM (s, ctms) => (
                warning (Pretty.string_of (Pretty.chunks (
                    Pretty.str s :: map (Syntax.pretty_term ctxt o Thm.term_of) ctms
                    @ [Pretty.str "As a consequence, fail to generate some of the \<open>open_abstraction\<close>\
                                  \ \<open>make_abstraction\<close> \<open>elim_SE\<close> rules"]
                  )));
                  raise CTERM (s, ctms)
              )))) ctxt
            ))) tagged_eqs

      val is_recursive = exists (fn eq =>
            case Thm.concl_of eq
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ RHS)
                  => exists_subterm (match_head term) RHS
               | _ => error "Internal bug #fc2042c3-0c46-4ae5-a66e-9697639068a0") eqs

      val mutating_params = map (fn _ => Unsynchronized.ref (SOME false)) param_names
      val _ = List.app (fn eq =>
            case Thm.concl_of eq
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ LHS $ RHS)
                  => let val (head, params) = case LHS
                                                of (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) => Term.strip_comb T
                                                 | _ => error "BUG"
                         val params = List.drop (params, fixed_num)
                         fun chk (X as _ $ _) =
                              let val (head', params') = Term.strip_comb X
                                  fun chk_eq (param :: params) (param' :: params') (ret :: rets) = (
                                        if param = param' then () else ret := SOME true ;
                                        chk_eq params params' rets
                                      )
                                    | chk_eq [] [] [] = ()
                                    | chk_eq (_ :: params) [] (ret :: rets) = (
                                        ret := NONE ;
                                        chk_eq params [] rets
                                      )
                               in if identical_name (head, head')
                                  then let val params' = List.drop (params', fixed_num)
                                        in (chk_eq params params' mutating_params ; List.app chk params')
                                       end
                                  else (List.app chk params')
                              end
                           | chk (Abs(_,_,X)) = chk X
                           | chk _ = ()
                      in chk RHS
                     end
               | _ => error "Internal bug #fc2042c3-0c46-4ae5-a66e-9697639068a0"
            ) eqs

      val mutating_params = map (op !) mutating_params
      val _ = if exists (fn SOME true => true | _ => false) mutating_params
              then warning (Pretty.string_of (Pretty.para
                     "You are defining a recursive \<phi>-type of mutating parameters : \
                     \the parameters varify throughout the recursion. The current version of \
                     \\<phi>type derivers supports it poorly. When the parameters vary, computations\
                     \ on the parameters are introduced inevitably, bringing various syntactic \
                     \expressions of the parameters. However, parameter is a \
                     \part of \<phi>-type where syntactic form is significant in guiding the reasoning,\
                     \ so no simplification will be applied to evaluate the computation and to\
                     \ relate two different syntactical forms of an identical \<phi>-type, may causing\
                     \ the deriver fails to apply the correct rule as it fails to recognize syntacitc\
                     \ variants of the \<phi>-type. \
                     \ Instead, we suggest to split the mutating-parameterized definition into\
                     \ two where the first one is recursive with all the parameters in the object\
                     \ side and the second is non-recursive and moves the parameters from the object\
                     \ side to the right place."))
              else ()

      val _ = case equality
                of SOME vars =>
                    if length vars = length param_tys then ()
                    else error "Incorrect number of parameter variabilities, which must equal the number of the \<phi>-type parameters"
                 | _ => ()

      val default_eq_of = default_eq_of (Context.Proof ctxt)
      val equality = case equality
              of SOME vars =>
                   map2 (fn SOME v => K v
                          | NONE => default_eq_of) vars param_tys
               | _ => let val eqs = map default_eq_of param_tys
                          val _ = Phi_Reasoner.info_pretty ctxt ~1 (fn () => let open Pretty in
                                    block ([str "Inferred", brk 1, keyword1 "parameter_equality", brk 1, str "("] @
                                           commas (map pretty_parameter_equality eqs) @ [str ")"])
                                  end)
                       in eqs
                      end

      val params = map3 (fn name => fn mut => fn var =>
                     {name=name, mutating=mut, equality=var}
                   ) param_names mutating_params equality
      
      val cong =
        let val (param_names, ctxt') =
              Variable.variant_fixes (map (the_default "A" o #name) params) ctxt
            fun filter [] [] = []
              | filter (PE_Synt :: P) (_ :: names) = filter P names
              | filter (_ :: P) (name :: names) = name :: filter P names
            val (param_names', ctxt') =
              Variable.variant_fixes (filter equality param_names) ctxt'
            fun burrow [] [] [] = []
              | burrow (PE_Synt  :: P) (name :: names) names' = name  :: burrow P names names'
              | burrow (_ :: P) (_ :: names) (name' :: names') = name' :: burrow P names names'
            val param_names' = burrow equality param_names param_names'
            val params  = map Free (param_names  ~~ param_tys)
            val params' = map Free (param_names' ~~ param_tys)

            fun mk_conds [] [] [] = []
              | mk_conds (PE_Guard :: P) (param :: params) (param' :: params')
                  = HOLogic.Trueprop $ (
                      \<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_GUARD\<close> $ (\<^Const>\<open>HOL.eq \<open>fastype_of param\<close>\<close> $ param $ param')
                    ) :: mk_conds P params params'
              | mk_conds (PE_Proof :: P) (param :: params) (param' :: params')
                  = HOLogic.Trueprop $ (
                      \<^Const>\<open>Premise\<close> $ \<^Const>\<open>default\<close> $ (\<^Const>\<open>HOL.eq \<open>fastype_of param\<close>\<close> $ param $ param')
                    ) :: mk_conds P params params'
              | mk_conds (PE_Synt :: P) (_ :: params) (_ :: params')
                  = mk_conds P params params'
            val conds = mk_conds equality params params'

            val LHS = fold (fn param => fn X => X $ param) params  term
            val RHS = fold (fn param => fn X => X $ param) params' term
            val concl = \<^Const>\<open>Pure.eq \<open>fastype_of LHS\<close>\<close> $ LHS $ RHS
            val goal = fold_rev (fn cond => fn X => \<^Const>\<open>Pure.imp\<close> $ cond $ X) conds concl
            val ([goal], ctxt') = Variable.import_terms false [goal] ctxt'
         in Thm.cterm_of ctxt' goal
         |> Goal.init
         |> Conv.gconv_rule (
              Phi_Conv.hhf_conv (fn _ => HOLogic.Trueprop_conv (Conv.rewr_conv @{thm Premise_def}))
                                (K Conv.all_conv) ctxt
            ) 1
         |> SINGLE (SOLVED' (Simplifier.asm_simp_tac (Simplifier.clear_simpset ctxt')) 1)
         |> (fn SOME ret => Goal.conclude ret
                         |> singleton (Variable.export ctxt' ctxt)
              | NONE => error "BUG")
        end
      val refl_Tr = gen_refl_Tr term ctxt cong


      val ind =(case def
                  of DIRECT_DEF _ => NONE
                   | WFREC_DEF info =>
                        case #inducts info
                          of SOME rules => SOME (List.nth (rules, idx_in_def_eqs))
                           | _ => SOME (List.nth (#pinducts info, idx_in_def_eqs)))
               |> Option.map ( Conv.fconv_rule (add_premise_tag ctxt)
                            #> Phi_Help.beta_eta_contract
                            #> Drule.zero_var_indexes )

      val cases =
            case def
              of DIRECT_DEF _ => NONE
               | WFREC_DEF info => SOME (List.nth (#cases info, idx_in_def_eqs))
      (*I am a fool
      val cases_ToA = mk_cases_rule eqs mk_cases_ToA cases_origin term ctxt
      val cases_VS = SOME (mk_cases_rule eqs mk_cases_shift cases_origin term ctxt)
                     handle Unavailable => NONE*)

      val idxes = List.tabulate (length tagged_eqs_in_type, fn i =>
                      Thm.cterm_of ctxt (HOLogic.mk_number \<^Type>\<open>nat\<close> i))
      val tagged_eqs_in_type_idx = map_index I tagged_eqs_in_type
      fun gen_from_eqs rule f eq =
            map (fn eq => (eq RS' (ctxt, rule))
                       |> f
                       |> normalize) eq

      fun gen_from_tagged_eq_in_type g f rule = map_filter (fn (i,th) => Option.mapPartial (
                fn eq => (eq RS' (ctxt, g i rule))
                            |> f i
                            |> normalize
                            |> SOME
                         handle THM _ => NONE
                ) th) tagged_eqs_in_type_idx

      fun gen_from_tagged_2eq_in_type g f rule = map_filter (fn (i,th) => Option.mapPartial (
                fn eq => (eq RS' (ctxt, eq RS' (ctxt, g i rule)))
                            |> f i
                            |> normalize
                            |> SOME
                         handle THM _ => NONE
                ) th) tagged_eqs_in_type_idx

    (*fun LHS_obj_is_var thm =
        case Thm.concl_of thm
          of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _) $ _) => is_Var x
           | _ => error ("BUG: the generated equations is malformed")*)

      val intro_ToA = if no_auto then [] else gen_from_eqs @{thm' \<phi>intro_transformation} I tagged_eqs
      val intro_reasoning   = if no_auto then [] else gen_from_eqs @{thm' \<phi>intro_reasoning_transformation} I tagged_eqs
      val intro_reasoning_R = if no_auto then [] else gen_from_eqs @{thm' \<phi>intro'_reasoning_transformation} I tagged_eqs
                                                      handle THM _ => [] (*in case of not a separation magma*)
      val intro'R_reasoning = if no_auto then [] else
            map2 (normalize oo (
              fn eq => (fn SOME tyeq => tyeq RS' (ctxt, @{thm' \<phi>intro'_reasoning_transformation_ty})
                         | NONE      =>   eq RS' (ctxt, @{thm' \<phi>intro'_reasoning_transformation}))
            )) tagged_eqs tagged_eqs_in_type
            handle THM _ => [] (*in case of not a separation magma*)
      val intro_map = if no_auto then [] else gen_from_tagged_2eq_in_type (K I) (K I) @{thm' \<phi>intro_ToA_Mapper_template_SE}
                                           |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1)

      val elim_ToA = if no_auto then [] else gen_from_eqs @{thm' \<phi>elim_transformation} I tagged_eqs
      val elim_reasoning = if no_auto then [] else gen_from_eqs @{thm' \<phi>elim_reasoning_transformation} I tagged_eqs
      val elim'SE_ToA = if no_auto then [] else gen_from_tagged_eq_in_type (K I) (K I) @{thm' \<phi>elim'SEi_transformation}
                                             |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1)
      val elim_map = if no_auto then [] else gen_from_tagged_2eq_in_type (K I) (K I) @{thm' \<phi>elim_ToA_Mapper_template_SE}
                                          |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1)

      val expansions = gen_from_eqs @{thm' \<phi>gen_expansion}
                           (Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                                  Conv.arg_conv (Simplifier.rewrite (
                                      Phi_Expansions.enhance (Simplifier.clear_simpset ctxt)))
                                ) ctxt)) tagged_eqs
      val unfold_vals = gen_from_tagged_eq_in_type (K I) (K I) @{thm' \<phi>unfold_val}

      fun mk_open_abstraction inst_i =
            gen_from_tagged_eq_in_type
                (if inst_i then (fn i => Drule.infer_instantiate ctxt [(("i",0), nth idxes i)])
                           else K I)
                (K I)
                (*(K (Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                  HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                      Phi_Syntax.transformation_conv Conv.all_conv
                          (fn ctm => Simplifier.rewrite (Gen_Open_Abstraction_SS.equip ctxt) ctm)
                          Conv.all_conv))) ctxt)))*)

      val open_abstraction = if no_auto then [] else mk_open_abstraction false @{thm' \<phi>open_abstraction_infer}
      val open_abstraction_sp = if no_auto then [] else mk_open_abstraction true @{thm' \<phi>open_abstraction_specified}

      fun gen_from_eqs_set_idx rule f eq =
            map_index (fn (i,eq) =>
                (eq RS' (ctxt, Drule.infer_instantiate ctxt [(("i",0), nth idxes i)] rule))
                   |> f
                   |> normalize) eq
      val gen_from_tagged_eq_in_type_set_idx =
            gen_from_tagged_eq_in_type (fn i => Drule.infer_instantiate ctxt [(("i",0), nth idxes i)])
                                       (K I)

      val open_abstraction_ToA = if no_auto then [] else
                                  gen_from_eqs @{thm' \<phi>open_abstraction_ToA_infer} I tagged_eqs
                               @ (gen_from_eqs @{thm' \<phi>open_abstraction_ToA_R_infer} I tagged_eqs
                                  handle THM _ => [])
                               @ (gen_from_tagged_eq_in_type (K I) (K I) @{thm' \<phi>open_abstraction_ToA_W_infer}
                                    |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1))

      val open_abstraction_ToA_sp = if no_auto then [] else
                                  gen_from_eqs_set_idx @{thm' \<phi>open_abstraction_ToA_specified} I tagged_eqs
                               @ (gen_from_eqs_set_idx @{thm' \<phi>open_abstraction_ToA_R_specified} I tagged_eqs
                                  handle THM _ => [])
                               @ (gen_from_tagged_eq_in_type_set_idx @{thm' \<phi>open_abstraction_ToA_W_specified}
                                    |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1))

      val make_abstraction = if no_auto then [] else
                              gen_from_eqs @{thm' \<phi>make_abstraction_infer} I tagged_eqs
                           @ (gen_from_eqs @{thm' \<phi>make_abstraction'R_infer} I tagged_eqs
                              handle THM _ => [])
                           @ (gen_from_tagged_eq_in_type (K I) (K I) @{thm' \<phi>make_abstraction'Rt_infer}
                                    |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1))
      val make_abstraction_sp = if no_auto then [] else
                                 gen_from_eqs_set_idx @{thm' \<phi>make_abstraction_specified} I tagged_eqs
                              @ (gen_from_eqs_set_idx @{thm' \<phi>make_abstraction'R_specified} I tagged_eqs
                                 handle THM _ => [])
                              @ (gen_from_tagged_eq_in_type_set_idx @{thm' \<phi>make_abstraction'Rt_specified}
                                    |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1))
    (*val make_Identity_Element_E = if no_auto then [] else
                                    (gen_from_eqs @{thm' \<phi>make_Identity_Element\<^sub>E} I tagged_eqs
                                     handle THM _ => [] (*the concrete algebra can be non-unital*))*)

      val phi_type = {
            name = binding,
            term = term,
            params = params,
            cterm = Drule.mk_term (Thm.cterm_of ctxt term),
            pos = pos,
            equations = map chk_zero_index_thm eqs,
            type_equations = typeqs,
            ind = Option.map chk_zero_index_thm ind,
            cases = cases,
            intro_reasoning = map chk_zero_index_thm intro_reasoning,
            is_recursive = is_recursive,
            is_impredicative = false
          } : phi_type
   in thy
   |> Context.proof_map (
        Phi_Reasoner.start_collecting_reasoners (the (snd @{reasoner_group %all_derived_rules})))
   |> Local_Theory.declaration {syntax=false, pervasive=false, pos=pos} (fn m => fn ctxt =>
        let val phi = morphism_phi_type m (phi_trim_context phi_type)
         in ctxt
         |> Phi_Types.map (Net.insert_term (phi_typ_term_equiv (Context.theory_of ctxt))
                                           (term, phi))
        end)
   |> Local_Theory.declaration {syntax=false, pervasive=false, pos=pos} (fn m =>
        let val expns = Morphism.fact m expansions
            fun add_rules mode priority rules =
                  Phi_Reasoner.add_rules (map (fn rule =>
                      ([Morphism.thm m rule], pos, mode, SOME priority, [], [], NONE)) rules)
          (*fun add_rules_G mode priority G rules =
                  Phi_Reasoner.add_rules (map (fn rule =>
                      ([Morphism.thm m rule], pos, mode, SOME priority, [], [], SOME G)) rules)*)
         in fn ctxt => ctxt
         |> not no_auto ? (fn ctxt => ctxt
             |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
             |> add_rules Phi_Reasoner.TO_BE_OVERRIDE' @{reasoner_group %To_ToA_derived_OPEN} open_abstraction
             |> add_rules Phi_Reasoner.TO_BE_OVERRIDE' @{reasoner_group %To_ToA_derived_OPEN+5} open_abstraction_sp
             |> add_rules Phi_Reasoner.TO_BE_OVERRIDE' @{reasoner_group %ToA_make_\<phi>type_derived-10} make_abstraction
             |> add_rules Phi_Reasoner.TO_BE_OVERRIDE' @{reasoner_group %ToA_make_\<phi>type_derived} make_abstraction_sp
           (*|> not (null make_Identity_Element_E) ?
                add_rules Phi_Reasoner.TO_BE_OVERRIDE' @{reasoner_group %derived_identity_element} make_Identity_Element_E *)
             |> Config.put_generic phi_allow_source_object_to_be_not_variable true
             |> add_rules Phi_Reasoner.TO_BE_OVERRIDE' @{reasoner_group %ToA_open_\<phi>type_derived-10} open_abstraction_ToA
             |> add_rules Phi_Reasoner.TO_BE_OVERRIDE' @{reasoner_group %ToA_open_\<phi>type_derived} open_abstraction_ToA_sp
                              (*(fn (ctxt, _) => Config.get ctxt search_CSTR_rules)*)
             |> Config.restore_generic phi_allow_source_object_to_be_not_variable ctxt
             |> Phi_Reasoner.add_rules (map (fn (group,pat,refl) =>
                  ([Morphism.thm m refl], pos, Phi_Reasoner.TO_BE_OVERRIDE', SOME group, [(pat,NONE)], [], NONE)) refl_Tr)
             |> Config.map_generic Phi_Reasoner.trace (fn i=>i+1)
       ) |> Phi_Expansions.add_simps expns
         |> Simplifier.map_ss (fn ctxt => ctxt addsimps expns)
       end)
   |> note_properties_s false phi_type (
        (* (case open_abstraction of SOME x => [(open_abstractionN, x)] | _ => []) @ *)
        (if null unfold_vals then [] else [(unfold_valN, unfold_vals)])
        @ [(unfoldN, eqs), (expansionN, expansions)])
   |> (if no_auto then I
       else note_properties_s true phi_type 
            [(introN, intro_ToA), (intro_reasoningN, intro_reasoning @ intro'R_reasoning), (intro_reasoning_R_N, intro_reasoning_R),
             (elimN, elim_ToA), (elim_reasoningN, elim_reasoning @ elim'SE_ToA),
             (intro_mapN, intro_map), (elim_mapN, elim_map)])
   |> not no_auto ? ( fn thy' => thy'
       |> Context_Position.set_visible false
       |> Defining_Phi_Type.invoke (Context.Proof thy') phi_type
       |> derive_properties (dervs, bundles) phi_type
       |> Context_Position.restore_visible thy
 ) |> Context.proof_map (
        Phi_Reasoner.stop_collecting_reasoners (the (snd @{reasoner_group %all_derived_rules}))
 ) |> pair phi_type
  end

fun prep_deriving_and_bundles raw_bundles raw_derv ctxt =
  let val bundles = map (Bundle.check ctxt) raw_bundles
      val ctxt'1 = open_proof_ctxt bundles ctxt
      val dervs = check_deriving_ast (Context.Proof ctxt'1) raw_derv
   in (dervs, bundles)
  end

fun add_type_i {no_auto} (name, term, def, pos, raw_derv, raw_bundles, variabilities) thy =
  let val (dervs, bundles) = prep_deriving_and_bundles raw_bundles raw_derv thy
      val (term, def) = case def of DIRECT_DEF def =>
            let val cterm = Drule.mk_term (Thm.cterm_of thy term)
                val [cterm, def] = Drule.zero_var_indexes_list [cterm, def]
             in (Thm.term_of (Drule.dest_term cterm), DIRECT_DEF def)
            end
                                  | def => (term, def)
      val level = Local_Theory.level thy
   in thy
   |> Local_Theory.map_contexts (fn i =>
        if i >= level - 1 then Config.map Phi_Reasoner.trace (fn i=>i-1) else I)
   |> add_type {no_auto=no_auto} (name, term, def, pos, dervs, bundles, variabilities)
   |> apsnd (Local_Theory.map_contexts (fn i =>
        if i >= level - 1 then Config.map Phi_Reasoner.trace (fn i=>i+1) else I))
  end

(** Interface **)

(*fun theory_map_result f = apsnd Context.the_theory o f o Context.Theory;*)

fun instantiate_phi inst' =
  let val inst = (TVars.map (K Thm.typ_of) (#1 inst'),
                  Vars.map (K Thm.term_of) (#2 inst'))
   in map_phi_type (I, Term_Subst.instantiate inst, map (Thm.instantiate inst'))
  end

fun is_phi_type_fixed phi = null (Term.add_tvars (#term phi) [])

fun fix_phi_type is_open (phi0 : phi_type) ctxt0 =
  let val (inst, ctxt) = Variable.import_inst is_open [#term phi0] ctxt0
      val inst' = (TVars.map (K (Thm.ctyp_of ctxt)) (#1 inst),
                   Vars.map (K (Thm.cterm_of ctxt)) (#2 inst))
      val phi = instantiate_phi inst' phi0
   in (inst', phi, ctxt)
  end

val bundle_parser = Scan.optional (\<^keyword>\<open>opening\<close> |-- Scan.repeat1 Parse.name_position) []

local



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

fun gen_add_fun bs raw_derv raw_bundles variabilities add (thy : local_theory) =
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
   in thy
   |> snd o Local_Theory.begin_nested
   |> add pat_completeness_auto
   |> prove_termination
   |> Local_Theory.end_nested_result Function_Common.transform_function_data
   |-> (fn info =>
     let val (const, name) = find_first (is_phi_type o Term.fastype_of o fst) (#fs info ~~ bs)
              |> (fn SOME x => x
                   | NONE => error "No \<phi>-type is defined.")
      in add_type_i {no_auto=false}
                    (name, const, WFREC_DEF info, Binding.pos_of name, raw_derv, raw_bundles, variabilities) #> snd
     end)
  end

fun add_function_cmd a b c tac int lthy = lthy
  |> Context.proof_map (
        Syntax_Phases.term_check 99 "a dirty hack for rewriting the non-standard \<phi>-type definition"
          (K dirty_syntax_hack))
  |> Function.add_function_cmd a b c tac int

in

(* fun add_fun a b c = gen_add_fun (Function.add_function a b c) *)
fun add_fun_cmd a b c raw_derv raw_bundles var int generic =
  gen_add_fun (map #1 a) raw_derv raw_bundles var
      (fn tac => snd o add_function_cmd a b c tac int) generic

end

fun let_phityp_deriving_cmd (((raw_const_name, pos), raw_bundles), raw_derv) thy =
  let val term = Proof_Context.read_term_pattern thy raw_const_name
      val phi = case get_type_info (Context.Proof thy) term
                  of SOME phi => phi
                   | NONE => error ("No \<phi>-type named "^ Syntax.string_of_term thy term ^ " found")
   in derive_properties (prep_deriving_and_bundles raw_bundles raw_derv thy) phi thy
  end

val def_by_fun = (Function_Common.function_parser Function_Fun.fun_config
               -- parameter_equality'
               -- bundle_parser
               -- deriving_parser
      >> (fn ((((config, (fixes, specs)), vars), raw_bundles), raw_dervs) =>
                add_fun_cmd fixes specs config raw_dervs raw_bundles vars))

val def_by_function = (Function_Common.function_parser Function_Common.default_config
      >> (fn (config, (fixes, specs)) => Function.function_cmd fixes specs config))

fun my_definition decl params prems spec int lthy = lthy
  |> Context.proof_map (
        Syntax_Phases.term_check 99 "a dirty hack for rewriting the non-standard \<phi>-type definition"
          (K dirty_syntax_hack))
  |> Specification.definition_cmd decl params prems spec int
  |> (fn ((term, (_, def)), lthy) => ([Drule.mk_term (Thm.cterm_of lthy term), def], lthy))

val def_direct = (Scan.option Parse_Spec.constdecl -- Parse.position (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes
        -- parameter_equality'
        -- bundle_parser
        -- deriving_parser
        -- (Scan.option \<^keyword>\<open>|\<close> >> (fn SOME _ => Scan.fail () | _ => ())) (*to distinguish with the `def_by_fun` syntax*)
   >> (fn (((((((decl, (spec, pos)), prems), params), vars), raw_bundles), raw_dervs), _) => fn int => fn lthy =>
        lthy
         |> snd o Local_Theory.begin_nested
         |> my_definition decl params prems spec int
         |> Local_Theory.end_nested_result Morphism.fact
         |> (fn ([def_term', def_eq], generic) =>
              let val def_term = Thm.term_of (Drule.dest_term def_term')
                  val name = case decl of SOME (name, _, _) => name
                                        | NONE => Binding.make (Term.term_name def_term, pos)
               in add_type_i {no_auto=false} (name, def_term, DIRECT_DEF def_eq, pos,
                                              raw_dervs, raw_bundles, vars) generic |> snd
              end)
         ))
in
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>type_def\<close> "define \<phi>-types"
          ((def_direct || def_by_fun) >> (fn f =>
            f false
            (*Context.mapping
                  (  Sign.new_group
                  #> Context.theory_map (f false)
                  #> Sign.reset_group)
                  (  Context.proof_map (f false) ) *)
            ))

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>let_\<phi>type\<close> "derive properties of existing \<phi>-types"
          ((Parse.position Parse.const -- bundle_parser -- deriving_parser)
            >> let_phityp_deriving_cmd)

end

end

signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

type deriving_instruction = Phi_Type.deriving_instruction

val constrain_antecedents : term (*condition*) -> term (*antecedents*) -> term list (*enhanced*)
      (*provides conditions to the given antecedents, e.g,
        cond, ant, to \<open>cond \<longrightarrow> ant\<close>,
        \<open>condition C\<close>, \<open>condition Ant\<close>, to \<open>condition (C \<longrightarrow> Ant)\<close>
        \<open>condition C\<close>, \<open>\<forall>x. condition Ant x\<close>, to \<open>\<forall>x. condition (C \<longrightarrow> Ant x)\<close>*)
val constrain_antecedents_by_boolean : term -> term -> term list

val forall_qualify : typ -> term -> term
val exists_qualify : typ -> term -> term

val simplified_forall_qualify : Proof.context -> typ -> term -> term
val simplified_exists_qualify : Proof.context -> typ -> term -> term

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra_Derivers

type deriving_instruction = Phi_Type.deriving_instruction

fun constrain_antecedents (Const(\<^const_name>\<open>True\<close>, _)) = PLPR_Syntax.dest_ant_sequence_or_HOL_conj
  | constrain_antecedents (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_GUARD\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _))
      = PLPR_Syntax.dest_ant_sequence_or_HOL_conj
  | constrain_antecedents cond =
      let fun is_premise_tag (Const(\<^const_name>\<open>default\<close>, _)) = true
            | is_premise_tag (Const(\<^const_name>\<open>MODE_GUARD\<close>, _)) = true
            | is_premise_tag _ = false
          fun constrain (\<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, X)) = \<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, constrain X)
            | constrain (\<^Const>\<open>HOL.All t\<close> $ X) = \<^Const>\<open>HOL.All t\<close> $ Abs ("_", t, constrain (Term.incr_boundvars 1 X $ Bound 0))
            | constrain (X as (H as Const(\<^const_name>\<open>Premise\<close>, _) $ tag) $ P) =
                (case cond of Const(\<^const_name>\<open>Premise\<close>, _) $ tag' $ C =>
                                if is_premise_tag tag andalso is_premise_tag tag'
                                then H $ (\<^Const>\<open>HOL.implies\<close> $ C $ P)
                                else \<^Const>\<open>HOL.implies\<close> $ cond $ X
                            | _ => \<^Const>\<open>HOL.implies\<close> $ cond $ X)
            | constrain X = \<^Const>\<open>HOL.implies\<close> $ cond $ X
       in map constrain o PLPR_Syntax.dest_ant_sequence_or_HOL_conj
      end

fun constrain_antecedents_by_boolean cond =
      constrain_antecedents (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_GUARD\<close> $ cond)

fun forall_qualify ty (X as Abs (_, _, B)) =
      if Term.loose_bvar1 (B, 0) then \<^Const>\<open>HOL.All ty\<close> $ X else Term.incr_boundvars ~1 B
  | forall_qualify ty X = \<^Const>\<open>HOL.All ty\<close> $ X

fun exists_qualify ty (X as Abs (_, _, B)) =
      if Term.loose_bvar1 (B, 0) then \<^Const>\<open>HOL.Ex ty\<close> $ X else Term.incr_boundvars ~1 B
  | exists_qualify ty X = \<^Const>\<open>HOL.Ex ty\<close> $ X

fun simp_term ctxt tm =
  Drule.mk_term (Thm.cterm_of ctxt tm)
    |> Simplifier.simplify ctxt
    |> Drule.dest_term
    |> Thm.term_of

fun simplified_forall_qualify ctxt ty X = simp_term ctxt (forall_qualify ty X)
fun simplified_exists_qualify ctxt ty X = simp_term ctxt (exists_qualify ty X)

end

type phi_type = Phi_Type.phi_type

