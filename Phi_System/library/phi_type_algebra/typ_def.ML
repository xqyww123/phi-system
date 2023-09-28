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

include PHI_TYPE_ALGEBRA


(** \<phi>-Type Definition \& Infos **)

datatype def = DIRECT_DEF of (term (*lhs of the def*) * (string (*def_name*) * thm (*def*)))
             | WFREC_DEF  of string (*const name*) * Function.info

type parameter_info = {
  name: string option (*not always given*),
  mutating: bool option (*if the parameter mutates throughout the (recursive) definition.
                          we are not always able to check if a parameter mutates from definition*)
}

type phi_type = {
  term: term (*of most general type and schematic variables. always be a constant or a fixed free*),
  params: parameter_info list (*the default name of the parameters. note the abstract object is not considered as a parameter*),
  cterm: thm (*TERM <the_cterm>*),
  pos : Position.T,
  proof_id: Phi_Cache_DB.proof_id,
  equations: thm list (*unfolding the term*),
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

val map_phi_type : (term -> term) * (thm list -> thm list) -> phi_type -> phi_type
val fold_phi_type : (term -> 'a -> 'a) * (thm -> 'a -> 'a) -> phi_type -> 'a -> 'a
val may_mutating_params : phi_type -> bool
val parameters_of : phi_type -> (parameter_info * typ) list
val parameters_and_typs_of : phi_type -> (parameter_info * typ) list (*reversed!*) * typ (*abstract typ*) * typ (*concrete typ*)

val morphism_phi_type : morphism -> phi_type -> phi_type
val instantiate_phi : (ctyp TVars.table * cterm Vars.table)
                   -> phi_type -> phi_type
val phi_trim_context : phi_type -> phi_type
val phi_transfer : theory -> phi_type -> phi_type
val phi_maxidx_of : phi_type -> int -> int

type hint = term

val get_type_info : Context.generic -> string (*const name*) -> phi_type option

(** Property Deriver from \<phi>-Type Definition **)
type priority = int
type deriver_name = string
type is_weak = bool
type quiet = bool (*report nothing even when fail*)
type deriving_ctxt = Proof.context (*the context used for deriving rules, which may be prepared
                                     specially with user configurations*)
type derive = deriving_ctxt -> phi_type -> generic_theory -> generic_theory
type deriving_instruction = hint * (Phi_Reasoner.priority * Reasoner_Group.name option) option
type deriver = {
  priority: priority,
  dependences: (deriver_name * is_weak) list,
      (*a weak dependency is invoked in quiet mode, meaning no error will be reported on failure,
        and not activated when any hint is given to the deriver depending on the weak dependency.
        Once users give an annotation, every implicit behavior is revoked, and this is the only
        way to revoke the implicit behavior.
        Users may declare a weak dependency by append a question mark after the dependency name.*)
  derive: quiet -> deriving_instruction list -> derive
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
type derivings = (deriving_instruction list * deriver * is_weak) Derivings.table
val add_deriving : deriving_instruction list * (deriver_name * deriver) -> derivings -> derivings
val add_deriving_from_hint : Context.generic -> deriving_instruction -> derivings -> derivings

val add_deriver_dependences : bool -> Context.generic -> (deriver_name * is_weak) list -> derivings -> derivings
val complete_deriver_dependences : Context.generic -> derivings -> derivings

val report_potential_failure_reason : (unit -> Pretty.T) list -> unit
(*no need to call it manually. It is invoked by `add_type` *)
val derive_properties : derivings * Bundle.name list -> phi_type -> generic_theory -> generic_theory

(* Derived Properties *)

val lookup_derived_properties : Context.generic -> phi_type -> string (*name*) -> thm list list
      (*the name is not necessarily the name of the deriver as a deriver can derive multiple
        properties. It is the name that is sent by the deriver when it calls `register_derived_properties`.*)
val register_derived_properties : phi_type -> string * int -> thm list -> generic_theory -> generic_theory
      (*It will also bind in Isabelle the properties to names <phi_type_name.property_names\<^sub>i>
        for the i-th property each.*)
val note_properties' : term -> (binding * thm list) list -> generic_theory -> generic_theory
val note_properties  : phi_type -> (binding * thm list) list -> generic_theory -> generic_theory
val note_properties_s: phi_type -> (bstring * thm list) list -> generic_theory -> generic_theory

val local_note_properties' : term -> (binding * thm list) list -> Context.generic -> Context.generic
val local_note_properties  : phi_type -> (binding * thm list) list -> Context.generic -> Context.generic
val local_note_properties_s: phi_type -> (bstring * thm list) list -> Context.generic -> Context.generic

val suffix_name_by_index : int -> string -> string

(* Syntax *)

type deriving_ast
val deriving_parser : deriving_ast list parser
val check_deriving_ast : Context.generic -> deriving_ast list -> derivings


(** Define \<phi>-Type and invoke derivings **)

structure Defining_Phi_Type : HOOKS (*invoked before any deriving*)
val add_type : def * Position.T * derivings * Bundle.name list -> generic_theory -> phi_type * generic_theory

val override_ind_rule : string * thm -> Context.generic -> Context.generic

(** Tools **)

val is_phi_head : phi_type -> term -> bool (*ignores type*)
val is_Type_Opr : typ -> bool
val is_non_parameterized_phityp : typ -> bool
val assert_Type_Opr : typ -> unit
val assert_first_parameter_is_type : typ -> unit
    (*note the T below is a \<phi>-type parameter*)
val separate_type_operator_and_its_parameter : term (*F(T)*) -> (term (*T*) * term (*F*)) list
val separate_type_operator_and_its_non_parameterized_parameter : term (*F(T)*) -> (term (*T*) * term (*F*)) list
val separate_type_operator_and_its_parameter_safe : term (*F(T)*) -> (term (*T*) * term (*F*)) list
val separate_type_operator_and_its_non_parameterized_parameter_safe : term (*F(T)*) -> (term (*T*) * term (*F*)) list
val separate_tyop_semimodule_and_its_non_parameterized : term (*F\<^sub>c(T)*) -> (term (*T*) * term (*c*) * term (*F*)) list

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

val raw_term_name_typ : term -> string * typ
(*depreciated*)
val dest_parameterized_phi_ty : typ -> typ list (*reserved!*) * typ (*x*) * typ (*concrete*)

(* Auxiliaries *)

val open_proof_ctxt : Bundle.name list -> Context.generic -> Proof.context

(* Internal Technical stuffs *)

val ML_sender : (quiet -> deriving_instruction list -> derive) option Unsynchronized.ref

end


(**** Implementation ****)

structure Phi_Type_Algebra : PHI_TYPE_ALGEBRA = struct

open Phi_Type_Algebra

(** Library **)

fun open_proof_ctxt bundles generic =
  Context.proof_of generic
    |> not (null bundles) ? Bundle.includes bundles

(*** \<phi>-Type Definition \& Infos ***)

val introN = "intro"
val intro_reasoningN = "intro_reasoning" (*rules for reasoning*)
val intro_reasoning_R_N = "intro_reasoning\<^sub>R"
val elimN = "elim"
val elim_reasoningN = "elim_reasoning"
val unfoldN = "unfold"
val expansionN = "expansion"
(* val open_abstractionN = "open_abstraction" *)

datatype def = DIRECT_DEF of (term (*lhs*) * (string (*def_name*) * thm (*def*)))
             | WFREC_DEF  of string * Function.info

type parameter_info = {
  name: string option,
  mutating: bool option (*if the parameter mutates throughout the (recursive) definition.
                          we are not always able to check if a parameter mutates from definition*)
}

type phi_type = {
  term: term (*of most general type*),
  params: parameter_info list, (*the abstract object is not considered a parameter*)
  cterm: thm,
  pos : Position.T,
  proof_id: Phi_Cache_DB.proof_id,
  equations: thm list (*unfolding the term*),
  type_equations: thm option list,
  ind: thm option,
  cases: thm option,
  intro_reasoning: thm list (*introduction transformations*),
  is_recursive: bool,
  is_impredicative: bool (*to be supported*)
}

fun may_mutating_params phi =
  exists ((fn SOME true => true | _ => false) o #mutating) (#params phi)

fun map_phi_type (mtm,mth) (phi : phi_type) =
  {
    term = mtm (#term phi),
    params = #params phi,
    cterm = singleton mth (#cterm phi),
    pos = #pos phi,
    proof_id = #proof_id phi,
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
    term = #term phi,
    params = #params phi,
    cterm = #cterm phi,
    pos = #pos phi,
    proof_id = #proof_id phi,
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

fun morphism_phi_type m = map_phi_type (Morphism.term m, Morphism.fact m)
val phi_trim_context = map_phi_type (I, map (Thm.trim_context))
fun phi_transfer thy = map_phi_type (I, map (Thm.transfer thy))
val phi_maxidx_of = fold_phi_type (Term.maxidx_term, Thm.maxidx_thm)

type hint = term

structure Phi_Types = Generic_Data (
  type T = phi_type Symtab.table (*key: name of constant*)
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun get_type_info ctxt k =
      Option.map (phi_transfer (Context.theory_of ctxt)) (Symtab.lookup (Phi_Types.get ctxt) k)

fun override_ind_rule (name, ind) =
  Phi_Types.map (Symtab.map_entry name (set_ind (Thm.trim_context ind)))

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


(** Impl of Basic Conversions **)

val add_premise_tag = Phi_Conv.recursive_premises_conv (fn ctxt => fn ctm =>
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

fun mk_ind_dest_ToA_internal ctxt (phi : phi_type) prop0 = (*not tested*)
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
      val (rev_arg_tys, x_ty, model_ty) = parse_typ [] typ
      val x_term = Bound 0
      val arity = length rev_arg_tys
      val T_term = fold_index (fn (i,_) => fn X => X $ Bound (arity-i)) rev_arg_tys (#term phi)

      val prop = gen_prop (x_term, T_term)
              |> (fn X => Abs("",x_ty,X))
              |> fold (fn T => fn X => Abs("",T,X)) rev_arg_tys
      val idx = Term.maxidx_of_term prop + 1
      val ind = Thm.incr_indexes idx (the (#ind phi))
      val prop_var = (case Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of ind))
                        of Var v => v
                         | _ => error "Bad induction rule")
   in Thm.instantiate (TVars.empty, Vars.make [(prop_var, Thm.cterm_of ctxt prop)]) ind
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

fun dest_parameterized_phi_ty' args \<^Type>\<open>fun x \<open>\<^Type>\<open>set c\<close>\<close>\<close> = (args, x, c)
  | dest_parameterized_phi_ty' args \<^Type>\<open>fun a T\<close> = dest_parameterized_phi_ty' (a::args) T
  | dest_parameterized_phi_ty' _ T = raise TYPE ("not a phi-type",[T],[])

val dest_parameterized_phi_ty = dest_parameterized_phi_ty' []

fun parameters_of phi = #params phi ~~ rev (#1 (dest_parameterized_phi_ty (Term.fastype_of (#term phi))))
fun parameters_and_typs_of phi =
  let val (rev_atys, x_ty, m_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
   in (#params phi ~~ rev rev_atys, x_ty, m_ty)
  end

fun fix_phi_term_params phi ctxt =
  let val (params, x_ty, model_ty) = parameters_and_typs_of phi
      val (x_name :: param_names, ctxt') =
              Variable.variant_fixes ("x" :: map (the_default "A" o #name o fst) params) ctxt
      val param_terms = map2 (fn N => fn (_,T) => Free(N,T)) param_names params
      val x_term = Free(x_name, x_ty)
      val T_term = fold (fn a => fn X => X $ a) param_terms (#term phi)
   in ((x_term, T_term), ctxt')
  end

(*** Deriving Properties ***)

type priority = int
type deriver_name = string
type deriving_ctxt = Proof.context
type derive = deriving_ctxt -> phi_type -> generic_theory -> generic_theory
type deriving_instruction = hint * (Phi_Reasoner.priority * Reasoner_Group.name option) option
type is_weak = bool
type quiet = bool
type deriver = {
  priority: priority,
  dependences: (deriver_name * is_weak) list,
  derive: quiet -> deriving_instruction list -> derive
}

structure Derivers = Generic_Data (
  type T = deriver Name_Space.table
  val empty = Name_Space.empty_table "\<phi>deriver"
  val merge = Name_Space.merge_tables
)

structure Derivings = Table (type key = priority * deriver_name; val ord = prod_ord int_ord string_ord)
type derivings = (deriving_instruction list * deriver * is_weak) Derivings.table

type pattern = term
structure Deriver_Bindings = Generic_Data (
  type T = (pattern * deriver_name) Net.net
  val empty = Net.empty
  val merge = Net.merge (op =)
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

fun add_deriving (hints : deriving_instruction list, (derv_name, derv)) dervs =
  Derivings.map_default ((#priority derv, derv_name), ([],derv, false))
                        (fn (hints', der', _) => (hints @ hints', der', false)) dervs

fun add_deriving_from_hint ctxt (hint,group) ders =
  add_deriving ([(hint,group)], match_deriver1 ctxt (Logic.strip_imp_concl hint)) ders

fun add_deriver_dependences _ _ [] dervs = dervs
  | add_deriver_dependences count_weak ctxt deps dervs =
      let val derivers = deriver_name_space ctxt
          fun add [] dervs = dervs
            | add ((dep,is_weak)::remain_deps) dervs =
                if is_weak andalso not count_weak
                then dervs
                else let val derv = Name_Space.get derivers dep
                         val key = (#priority derv, dep)
                      in(case Derivings.lookup dervs key
                      of SOME (hints, deriver, is_weak') =>
                            if is_weak' = (is_weak' andalso is_weak)
                            then dervs
                            else Derivings.update (key, (hints, deriver, is_weak' andalso is_weak)) dervs
                                    |> add (#dependences derv)
                       | NONE => Derivings.update_new (key, ([], derv, is_weak)) dervs
                                    |> add (#dependences derv)
                       ) |> add remain_deps
                     end
       in add deps dervs
      end

fun complete_deriver_dependences ctxt dervs =
  Derivings.fold (fn (_,(hints,derv,_)) =>
      add_deriver_dependences (null hints) ctxt (#dependences derv)) dervs dervs

(* Deriving *)

val reason_of_deriving_fails : (unit -> Pretty.T) list Thread_Data.var = Thread_Data.var ()

fun err_derive prop_name msg hints = let open Pretty in
      error (string_of (chunks (
        block [str "Fail to derive the property ", str prop_name] ::
        msg @
        (if null hints
         then [para "The guessed property may be wrong, and you may provide the \
                    \desired property form by \<open>deriving \<open>the property you want\<close>\<close>."]
         else []) @
        (case Thread_Data.get reason_of_deriving_fails
           of SOME (reasons as _ :: _) =>
                para "There are some potential reasons for the failure" ::
                map (fn g => item [g ()]) reasons
            | _ => [])
      )))
      end

fun report_potential_failure_reason G =
  case Thread_Data.get reason_of_deriving_fails
    of SOME L => Thread_Data.put reason_of_deriving_fails (SOME (G @ L))
     | NONE => ()

fun derive_properties (dervs, bundles) phityp thy = thy
  |> Context.mapping (Context_Position.set_visible_global false)
                     (Context_Position.set_visible false)
  |> Derivings.fold (fn ((_,name),(hints,derv,is_weak)) => fn thy'goal =>
      let val _ = Thread_Data.put reason_of_deriving_fails (SOME [])
          val ctxt_derv = Context.proof_of thy'goal
                       |> Bundle.includes bundles
       in #derive derv is_weak hints ctxt_derv phityp thy'goal
          handle Automation_Fail msg => err_derive name (msg ()) hints
      end
     ) dervs
  |> Context_Position.restore_visible_generic thy

(* Derived Properties *)

structure Derived_Properties = Generic_Data (
  type T = thm list list Symreltab.table
  val empty = Symreltab.empty
  val merge = Symreltab.join (K (merge pointer_eq))
)

fun lookup_derived_properties ctxt phi name =
  case Symreltab.lookup (Derived_Properties.get ctxt) (fst (raw_term_name_typ (#term phi)), name)
    of SOME ret => ret
     | NONE => []

fun short_name_of_tyop (Abs (_,_,X)) = short_name_of_tyop X
  | short_name_of_tyop (X $ _) = short_name_of_tyop X
  | short_name_of_tyop (Const (N, _)) = Long_Name.base_name N
  | short_name_of_tyop (Free (N, _)) = N
  | short_name_of_tyop X = raise TERM ("Not a \<phi>-type term", [X])

fun note_properties' phityp_term notes =
  let val short_name = short_name_of_tyop phityp_term
      val qualify = Binding.qualify true short_name
   in Context.mapping (fold (fn (b,Th) => snd o Global_Theory.note_thms "" ((qualify b, []), [(Th,[])])) notes)
                      (fold (fn (b,Th) => snd o Local_Theory.note ((qualify b, []), Th)) notes)
  end

fun local_note_properties' phityp_term notes ctxt =
  let val facts = Context.cases Global_Theory.facts_of Proof_Context.facts_of ctxt
      fun varify_binding i b =
        let val b' = if i = 0 then b else Binding.suffix_name ("_" ^ string_of_int i) b
            val iname = Context.cases Sign.full_name Proof_Context.full_name ctxt b'
         in if Facts.defined facts iname
            then varify_binding (i+1) b
            else b
        end
      val notes' = map (fn (b',rules') =>
            let val b = varify_binding 0 (Binding.qualify true (short_name_of_tyop phityp_term) b')
             in ((b, []), [(rules',[])])
            end) notes
   in Context.mapping (fold (snd oo Global_Theory.note_thms "") notes')
                      (fold (snd oo Proof_Context.note_thms "") notes') ctxt
  end

fun note_properties (phi : phi_type) = note_properties' (#term phi)
fun note_properties_s (phi : phi_type) notes =
      note_properties' (#term phi) (map (fn (N,th) => (Binding.make (N, #pos phi), th)) notes)

fun local_note_properties (phi : phi_type) = local_note_properties' (#term phi)
fun local_note_properties_s (phi : phi_type) notes =
      local_note_properties' (#term phi) (map (fn (N,th) => (Binding.make (N, #pos phi), th)) notes)


fun suffix_name_by_index ind name =
      if ind = 0 then name else suffix ("\<^sub>" ^ string_of_int ind) name

fun register_derived_properties phi (name, ind) ths thy =
  let val ind' = length (lookup_derived_properties thy phi name)
      val _ = if ind' = ind then () else error "Bad Index"
      val _ = Phi_Reasoner.info_pretty_generic thy 0 (fn () =>
              let open Pretty
               in block [str (suffix_name_by_index ind name), brk 1,
                         chunks (map (fn th => item [Context.cases Thm.pretty_thm_global Thm.pretty_thm thy th]) ths)]
              end)
   in Phi_Help.generic_theory_mapping (fn m =>
        let val key = fst (raw_term_name_typ (Morphism.term m (#term phi)))
         in Derived_Properties.map (Symreltab.map_default ((key, name), []) (fn L => ths :: L))
        end) thy
  end

(* Syntax *)

datatype deriving_ast = Derv_By_Name of xstring * Position.T
                      | Derv_By_Term of string * Reasoner_Group.priority_syntax option

val deriving_name = Parse.position (
        Parse.group (fn () => "name") (Parse.short_ident || Parse.long_ident))
val one_deriving = deriving_name >> Derv_By_Name
                || (Parse.term -- Scan.option (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>) >> Derv_By_Term)
val deriving_parser = Scan.repeat (
        \<^keyword>\<open>deriving\<close> |-- Parse.and_list one_deriving
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

fun check_deriving_ast ctxt derv_ast =
  let val ctxt_parse = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of ctxt)
      val thy = Context.theory_of ctxt
   in Derivings.empty
   |> fold_rev (
        fn Derv_By_Name name => add_deriving ([], check_deriver ctxt name)
         | Derv_By_Term (term, raw_group) =>
            let val term' = Syntax.parse_prop ctxt_parse term
                         |> Syntax.check_prop ctxt_parse
                         |> Envir.beta_eta_contract
                         |> Phi_Help.refine_sorts_of_tm thy
                val ctxt'1 = fold Variable.add_fixes_implicit [term'] (Variable.set_body false ctxt_parse)
                val term'1 = singleton (Variable.export_terms ctxt'1 ctxt_parse) term'
                val group = Option.map (Reasoner_Group.check_priority true (Context.Proof ctxt'1)) raw_group
             in add_deriving_from_hint ctxt (term'1, group)
            end
       ) derv_ast
   |> complete_deriver_dependences ctxt
   handle Unknown_Hint term =>
      error (Pretty.string_of (Pretty.chunks [
          Pretty.para "Do not know how to derive from the given hint. There is no known deriver for it.",
          Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt term
        ]))
  end

(* Interface for Deriver *)

val ML_sender_locker = Synchronized.var "\<phi>TA.ML_sender_locker" ()
val ML_sender : (quiet -> deriving_instruction list -> derive) option Unsynchronized.ref
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
                let val expr = ML_Lex.read "Phi_Type_Algebra.ML_sender := SOME (" @
                               ML_Lex.read_source ML @
                               ML_Lex.read ")"
                 in Synchronized.change_result ML_sender_locker (fn () => let
                      val _ = ML_Context.expression (Input.pos_of ML) expr (Context.Theory thy)
                      val ret = the (!ML_sender)
                       in (ret, ML_sender := NONE)
                      end)
                end
              | NONE => K (K (K (K I)))
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


(*** \<phi>-Type Definition Part II ***)

(** Tools **)

fun is_the_same_const_or_free (Const(N, _), Const(N', _)) = N = N'
  | is_the_same_const_or_free (Free(N, _), Free(N', _)) = N = N'
  | is_the_same_const_or_free _ = false

fun is_phi_head phi term = is_the_same_const_or_free (#term phi, term)

fun is_Type_Opr ty =
  case dest_parameterized_phi_ty ty
    of ([],_,_) => false
     | (args,_,_) => exists (can dest_parameterized_phi_ty) args

fun assert_Type_Opr ty =
  if is_Type_Opr ty then ()
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

fun gen_separate_type_operator_and_its_non_parameter chk FT_term =
  let datatype prev = Arg of term | Abst of string * typ
      fun assemble (Arg a) X = X $ a
        | assemble (Abst (N,ty)) X = Abs (N, ty, X)
      fun split (lv, prevs) (F $ T) =
            if can Term.fastype_of T andalso chk T
            then F
              |> not (null prevs) ? (fn F =>
                      (F $ Bound lv)
                   |> fold assemble prevs 
                   |> (fn X => Abs("T", Term.fastype_of T, X)))
              |> (fn X => (T, X) :: split (lv, Arg T :: prevs) F )
            else split (lv, Arg T :: prevs) F
        | split (lv, prevs) (Abs (N,ty,X)) = split (lv+1, Abst (N,ty)::prevs) X
        | split _ _ = []
   in split (0, []) (Phi_Help.beta_eta_contract_term FT_term)
  end

val separate_type_operator_and_its_parameter_safe =
  gen_separate_type_operator_and_its_non_parameter (can dest_parameterized_phi_ty o Term.fastype_of)

fun is_non_parameterized_phityp typ =
  case try dest_parameterized_phi_ty typ
    of SOME ([],_,_) => true
     | _ => false

val separate_type_operator_and_its_non_parameterized_parameter_safe =
  gen_separate_type_operator_and_its_non_parameter (is_non_parameterized_phityp o Term.fastype_of)

fun separate_tyop_semimodule_and_its_non_parameterized tm = tm
  |> gen_separate_type_operator_and_its_non_parameter (is_non_parameterized_phityp o Term.fastype_of)
  |> maps (fn (T, Fc) =>
        gen_separate_type_operator_and_its_non_parameter (K true) Fc
          |> map (fn (c, F) => (T, c, F)))


fun warn_separate_type_operator f FT_term =
  case f FT_term
    of [] => raise Automation_Fail (fn () => let open Pretty in
                [block [str "Fail to parse", brk 1,
                        str (Term.term_name (Term.head_of FT_term)),
                        str "as a type operator."]]
             end)
     | ret => ret

val separate_type_operator_and_its_parameter =
      warn_separate_type_operator separate_type_operator_and_its_parameter_safe
val separate_type_operator_and_its_non_parameterized_parameter =
      warn_separate_type_operator separate_type_operator_and_its_non_parameterized_parameter_safe

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

(** Main **)

structure Defining_Phi_Type = Hooks(
  type arg = phi_type
  type state = generic_theory
)

val refine_typeq = @{lemma \<open>(\<And>x. (x \<Ztypecolon> T) = (x \<Ztypecolon> U)) \<Longrightarrow> T = U\<close> by (rule \<phi>Type_eqI, simp)}

fun LHS_of (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ LHS $ _) = LHS
  | LHS_of (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ LHS $ _) = LHS
  | LHS_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = LHS_of X
  | LHS_of (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = LHS_of X
  | LHS_of X = raise TERM ("Not an equation", [X])

(*ctxt: the context used to derive properties*)
fun add_type (def, pos, dervs, bundles) thy =
  let val ctxt = Context.proof_of thy
              |> Bundle.includes bundles
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
              case Term.head_of (LHS_of (Thm.concl_of eq))
                of Const(N',_) => N' = name
                 | Free (N',_) => N' = name
                 | _ => false)
      val eqs = (case def of DIRECT_DEF (_, (_, eq)) => [eq]
                    | WFREC_DEF (name, info) =>
                        (case #simps info
                           of SOME eqs => filter_relevant_eqs name eqs
                            | NONE => (warning "Termination of the definition is not proven. \
                                               \Use partial simplification and induction rules.";
                                       filter_relevant_eqs name (#psimps info))))
              |> map (conv_def_to_equation ctxt
                   #> normalize)
      val tagged_eqs = map (Conv.fconv_rule (add_premise_tag ctxt)) eqs

      val typeqs = map (fn eq => SOME (eq RS refine_typeq) handle THM _ => NONE) eqs

      val param_names = map (fn eq =>
                          case LHS_of (Thm.concl_of eq)
                            of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T =>
                                  map (fn Var ((N,_),_) => SOME N | Free (N,_) => SOME N | _ => NONE)
                                      (snd (strip_comb T))
                             | _ => error "BUG") eqs
                     |> foldl1 (uncurry (map2 (curry merge_options)))

      val tagged_eqs_in_type = map (try (Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
              HOLogic.Trueprop_conv (Conv.arg_conv (fn ctm =>
                Phi_Conv.embed_BI_assertion_into_phi_type ctxt ctm
                handle CTERM (s, ctms) => (
                warning (Pretty.string_of (Pretty.chunks (
                    Pretty.str s :: map (Syntax.pretty_term ctxt o Thm.term_of) ctms
                    @ [Pretty.str "As a consequence, fail to generate the \<open>open_abstraction\<close> \<open>elim_SE\<close> lemmas"]
                  )));
                  raise CTERM (s, ctms)
              )))) ctxt
            ))) tagged_eqs

      val is_recursive = exists (fn eq =>
            case Thm.concl_of eq
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ RHS)
                  => exists_subterm (fn Const (N',_) => N' = fst name_ty
                                      | Free (N',_) => N' = fst name_ty
                                      | _ => false) RHS
               | _ => error "Internal bug #fc2042c3-0c46-4ae5-a66e-9697639068a0") eqs

      val mutating_params = map (fn _ => Unsynchronized.ref (SOME false)) param_names
      val _ = List.app (fn eq =>
            case Thm.concl_of eq
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ LHS $ RHS)
                  => let val (head, params) = case LHS
                                                of (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) => Term.strip_comb T
                                                 | _ => error "BUG"
                         val arity = length params
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
                               in if is_the_same_const_or_free (head, head')
                                  then (chk_eq params params' mutating_params ; List.app chk params')
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

      val params = map2 (fn name => fn mut =>
                     {name=name, mutating=mut}
                   ) param_names mutating_params

      val ind =(case def
                  of DIRECT_DEF _ => NONE
                   | WFREC_DEF (_, info) =>
                        case #inducts info
                          of SOME rules => SOME (List.nth (rules, idx))
                           | _ => SOME (List.nth (#pinducts info, idx)))
               |> Option.map ( Conv.fconv_rule (add_premise_tag ctxt)
                            #> Phi_Help.beta_eta_contract )

      val cases =
            case def
              of DIRECT_DEF _ => NONE
               | WFREC_DEF (_, info) => SOME (List.nth (#cases info, idx))
      (*I am a fool
      val cases_ToA = mk_cases_rule eqs mk_cases_ToA cases_origin term ctxt
      val cases_VS = SOME (mk_cases_rule eqs mk_cases_shift cases_origin term ctxt)
                     handle Unavailable => NONE*)

      fun gen_from_eqs rule f eq =
            map (fn eq => (eq RS' (ctxt, rule))
                       |> f
                       |> normalize) eq
      fun gen_from_tagged_eq_in_type f rule = map_filter (Option.mapPartial (
                fn eq => (eq RS' (ctxt, rule))
                            |> f
                            |> normalize
                            |> SOME
                         handle THM _ => NONE
                )) tagged_eqs_in_type

    (*fun LHS_obj_is_var thm =
        case Thm.concl_of thm
          of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _) $ _) => is_Var x
           | _ => error ("BUG: the generated equations is malformed")*)

      val intro_ToA = gen_from_eqs @{thm' \<phi>intro_transformation} I tagged_eqs
      val intro_reasoning   = gen_from_eqs @{thm' \<phi>intro_reasoning_transformation} I tagged_eqs
      val intro_reasoning_R = gen_from_eqs @{thm' \<phi>intro'_reasoning_transformation} I tagged_eqs
                              handle THM _ => [] (*in case of not a separation magma*)
      val intro'R_reasoning = map2 (normalize oo (
              fn eq => (fn SOME tyeq => tyeq RS' (ctxt, @{thm' \<phi>intro'_reasoning_transformation_ty})
                         | NONE      =>   eq RS' (ctxt, @{thm' \<phi>intro'_reasoning_transformation}))
            )) tagged_eqs tagged_eqs_in_type
            handle THM _ => [] (*in case of not a separation magma*)
      val elim_ToA = gen_from_eqs @{thm' \<phi>elim_transformation} I tagged_eqs
      val elim_reasoning = gen_from_eqs @{thm' \<phi>elim_reasoning_transformation} I tagged_eqs
      val elim'SE_ToA = gen_from_tagged_eq_in_type I @{thm' \<phi>elim'SEi_transformation}
                     |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1)
      val expansions = gen_from_eqs @{thm' \<phi>gen_expansion}
                           (Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                                  Conv.arg_conv (Simplifier.rewrite (
                                      Phi_Expansions.enhance (Simplifier.clear_simpset ctxt)))
                                ) ctxt)) tagged_eqs

      val open_abstraction = gen_from_tagged_eq_in_type
                (Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                  HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                      Phi_Syntax.transformation_conv Conv.all_conv
                          (fn ctm => Simplifier.rewrite (Gen_Open_Abstraction_SS.equip ctxt) ctm)
                          Conv.all_conv))) ctxt))
                @{thm' \<phi>open_abstraction}

      val open_abstraction_ToA = gen_from_eqs @{thm' \<phi>open_abstraction_ToA} I tagged_eqs
                               @ (gen_from_eqs @{thm' \<phi>open_abstraction_ToA_R} I tagged_eqs
                                  handle THM _ => [])
                               @ (gen_from_tagged_eq_in_type I @{thm' \<phi>open_abstraction_ToA_W}
                                    |> map (Conv.gconv_rule (Simplifier.rewrite ctxt) 1))

      val make_abstraction = gen_from_eqs @{thm' \<phi>make_abstraction} I tagged_eqs
                           @ (gen_from_eqs @{thm' \<phi>make_abstraction'R} I tagged_eqs
                              handle THM _ => [])
      val make_abstraction_eq = gen_from_eqs @{thm' \<phi>make_abstraction'eq} I tagged_eqs
                              @ (gen_from_eqs @{thm' \<phi>make_abstraction'R'eq} I tagged_eqs
                                 handle THM _ => [])
      val make_Identity_Element_E = gen_from_eqs @{thm' \<phi>make_Identity_Element\<^sub>E} I tagged_eqs

      val proof_id =
        case term of Const _ => fst name_ty
           | Free _ =>
              Context.cases Sign.full_name Local_Theory.full_name thy (Binding.name (fst name_ty))

      val the_term = chk_zero_index_term term
      val _ = case the_term of Const _ => ()
                 | _ => raise TERM ("Must be a constant", [the_term])
      val phi_type = {
            term = the_term,
            params = params,
            cterm = Drule.mk_term (Thm.cterm_of ctxt the_term),
            pos = pos,
            proof_id = proof_id,
            equations = map chk_zero_index_thm eqs,
            type_equations = typeqs,
            ind = Option.map chk_zero_index_thm ind,
            cases = cases,
            intro_reasoning = map chk_zero_index_thm intro_reasoning,
            is_recursive = is_recursive,
            is_impredicative = false
          } : phi_type
   in thy
   |> Context.mapping
        (Context.theory_map (Phi_Types.map (Symtab.update_new (fst name_ty, phi_trim_context phi_type))))
        (Local_Theory.declaration {syntax=false, pervasive=false, pos=pos} (fn m =>
          Phi_Types.map (Symtab.update_new (fst (raw_term_name_typ (Morphism.term m term)),
                                            morphism_phi_type m (phi_trim_context phi_type)))))
   |> Phi_Help.generic_theory_mapping (fn m =>
        let val expns = Morphism.fact m expansions
            fun add_rules mode priority rules =
                  Phi_Reasoner.add_rules (map (fn rule =>
                      ([Morphism.thm m rule], pos, mode, priority, [], [], NONE)) rules)
         in fn ctxt => ctxt
         |> add_rules Phi_Reasoner.TO_BE_OVERRIDE @{reasoner_group %To_ToA_derived_OPEN} (Morphism.fact m open_abstraction)
         |> add_rules Phi_Reasoner.TO_BE_OVERRIDE @{reasoner_group %ToA_make_\<phi>type_derived} (Morphism.fact m make_abstraction)
         |> add_rules Phi_Reasoner.TO_BE_OVERRIDE @{reasoner_group %ToA_make_\<phi>type_derived-10} (Morphism.fact m make_abstraction_eq)
         |> add_rules Phi_Reasoner.TO_BE_OVERRIDE @{reasoner_group %derived_identity_element} (Morphism.fact m make_Identity_Element_E)
         |> Config.put_generic phi_allow_source_object_to_be_not_variable true
         |> add_rules Phi_Reasoner.TO_BE_OVERRIDE @{reasoner_group %ToA_open_\<phi>type_derived} (Morphism.fact m open_abstraction_ToA)
         |> Config.restore_generic phi_allow_source_object_to_be_not_variable ctxt
         |> Phi_Expansions.add_simps expns
         |> Simplifier.map_ss (fn ctxt => ctxt addsimps expns)
       end)
   |> note_properties_s phi_type (
        (* (case open_abstraction of SOME x => [(open_abstractionN, x)] | _ => []) @ *)
        [(unfoldN, eqs), (introN, intro_ToA),
         (intro_reasoningN, intro_reasoning @ intro'R_reasoning), (intro_reasoning_R_N, intro_reasoning_R),
         (elimN, elim_ToA), (elim_reasoningN, elim_reasoning @ elim'SE_ToA),
         (expansionN, expansions)])
   |> Context.mapping (Context_Position.set_visible_global false)
                      (Context_Position.set_visible false)
   |> Defining_Phi_Type.invoke (Context.Proof ctxt) phi_type
   |> derive_properties (dervs, bundles) phi_type
   |> Context_Position.restore_visible_generic thy
   |> pair phi_type
  end

fun prep_deriving_and_bundles raw_bundles raw_derv ctxt =
  let val bundles = map (Bundle.check ctxt) raw_bundles
      val ctxt'1 = Bundle.includes bundles ctxt
      val dervs = check_deriving_ast (Context.Proof ctxt'1) raw_derv
   in (dervs, bundles)
  end

fun add_type_i (def, pos, raw_derv, raw_bundles) thy =
  let val (dervs, bundles) = prep_deriving_and_bundles raw_bundles raw_derv (Context.proof_of thy)
   in add_type (def, pos, dervs, bundles) thy
  end

(** Interface **)

(*fun theory_map_result f = apsnd Context.the_theory o f o Context.Theory;*)

fun instantiate_phi inst' =
  let val inst = (TVars.map (K Thm.typ_of) (#1 inst'),
                  Vars.map (K Thm.term_of) (#2 inst'))
   in map_phi_type (Term_Subst.instantiate inst, map (Thm.instantiate inst'))
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

fun gen_add_fun pos raw_derv raw_bundles add (thy : generic_theory) =
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
    val (info, thy'1) = add pat_completeness_auto thy
    val const = find_first (is_phi_type o Term.fastype_of) (#fs info)
              |> (fn SOME x => x
                   | NONE => error "No \<phi>-type is defined.")
   in thy'1
   |> Context.mapping_result (
        Named_Target.theory_map_result (Function_Common.transform_function_data) prove_termination
      ) prove_termination
   |-> (fn info => add_type_i (WFREC_DEF (fst (raw_term_name_typ const), info), pos, raw_derv, raw_bundles) #> snd)
  end

fun add_function_cmd a b c tac int lthy = lthy
  |> Context.proof_map (
        Syntax_Phases.term_check 99 "a dirty hack for rewriting the non-standard \<phi>-type definition"
          (K dirty_syntax_hack))
  |> Function.add_function_cmd a b c tac int

in

(* fun add_fun a b c = gen_add_fun (Function.add_function a b c) *)
fun add_fun_cmd a b c raw_derv raw_bundles int generic =
  gen_add_fun (Binding.pos_of (#1 (hd a))) raw_derv raw_bundles
    (fn tac =>
        Context.mapping_result
          (Named_Target.theory_map_result Function_Common.transform_function_data
                                          (add_function_cmd a b c tac int))
          (add_function_cmd a b c tac int)) generic

end

fun let_phityp_deriving_cmd (((raw_const_name, pos), raw_bundles), raw_derv) thy =
  let val ctxt = Context.proof_of thy
      val Const (const_name, _) = Proof_Context.read_const {proper=false, strict=false} ctxt raw_const_name
      val phi = case get_type_info thy const_name
                  of SOME phi => phi
                   | NONE => error ("No \<phi>-type named "^ const_name ^ " found")
   in derive_properties (prep_deriving_and_bundles raw_bundles raw_derv ctxt) phi thy
  end


val def_by_fun = (Function_Common.function_parser Function_Fun.fun_config
               -- bundle_parser
               -- deriving_parser
      >> (fn (((config, (fixes, specs)), raw_bundles), raw_dervs) =>
                add_fun_cmd fixes specs config raw_dervs raw_bundles))

val def_by_function = (Function_Common.function_parser Function_Common.default_config
      >> (fn (config, (fixes, specs)) => Function.function_cmd fixes specs config))

fun my_definition decl params prems spec int lthy = lthy
  |> Context.proof_map (
        Syntax_Phases.term_check 99 "a dirty hack for rewriting the non-standard \<phi>-type definition"
          (K dirty_syntax_hack))
  |> Specification.definition_cmd decl params prems spec int

val def_direct = (Scan.option Parse_Spec.constdecl -- Parse.position (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes
        -- bundle_parser
        -- deriving_parser
        -- (Scan.option \<^keyword>\<open>|\<close> >> (fn SOME _ => Scan.fail () | _ => ())) (*to distinguish with the `def_by_fun` syntax*)
   >> (fn ((((((decl, (spec, pos)), prems), params), raw_bundles), raw_dervs), _) => fn int =>
        Context.mapping_result
          (Named_Target.theory_map_result (fn m => fn (tm, (name, def)) =>
                    (Morphism.term m tm, (name, Morphism.thm m def)))
                (my_definition decl params prems spec int))
          (my_definition decl params prems spec int)
           #> (fn (def, generic) =>
                add_type_i (DIRECT_DEF def, pos, raw_dervs, raw_bundles) generic |> snd)
        ))
in
val _ = Outer_Syntax.command \<^command_keyword>\<open>\<phi>type_def\<close> "define \<phi>-types"
          ((def_direct || def_by_fun) >> (fn f =>
              Toplevel.theory' (fn int => Context.theory_map (f int)) NONE))

val _ = Outer_Syntax.command \<^command_keyword>\<open>let_\<phi>type\<close> "derive properties of existing \<phi>-types"
          ((Parse.position Parse.const -- bundle_parser -- deriving_parser)
            >> (fn const_deriving =>
              Toplevel.theory (Context.theory_map (let_phityp_deriving_cmd const_deriving))))

end

end

signature PHI_TYPE_ALGEBRA_DERIVERS = sig

type deriving_instruction = Phi_Type_Algebra.deriving_instruction

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

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct

type deriving_instruction = Phi_Type_Algebra.deriving_instruction

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

