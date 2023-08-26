signature PHI_TYPE_ALGEBRA_DERIVERS = sig

(*** A common framework to build derivers fast ***)

type induct_inst_params = term option list
(*parameters of the phi-type in the *reversed* order with the abstract object prepended to the begining,
  i.e., induct_inst_params[0] is the abstract object, induct_inst_params[i] is the $(n-i)$th parameter
  is there are $n$ parameters in total.
  all must be free variables.
  they are used to instantiate the induction rule.
  If certain parameter is not a fixed free variable in the goal (e.g.,
  represented by a universally quantified variable), preserve its place
  and set it to None.
  The first element must be the abstract object or None.*)

(** Component: unify_hint **)

type hint = term
type parse_hint = Phi_Type_Algebra.deriving_ctxt -> Phi_Type_Algebra.phi_type ->  hint -> typ (*of the phi-typ const*) * induct_inst_params * hint

(* Common choices of the unification *)

val malformed_hint : Phi_Type_Algebra.deriving_ctxt -> term -> (unit -> Pretty.T list) -> 'a
val parse_parameters_of_phi_type : term -> term option list
(*default parsing*)
val parse_hint : (term -> term) (*extract the phi-type part from the hint. can be either the type assertion,
                                  the type itself, or the type operator*)
              -> parse_hint

(** Component: guess_property **)

type guess_property =
        Phi_Type_Algebra.phi_type ->
        Proof.context ->
        ( term list (*antecedents*)
        * term (*conclusion*)
        * induct_inst_params
        * Phi_Type_Algebra.phi_type * Proof.context ) Seq.seq

(*If user gives no hint, we need to guess the property to be reasoned.
  The `guess_property` may guess the abstract operator from the logic type of the abstract
  object (e.g. by Bounded Natural Functor) or by any other means. It can also instantiate any logic
  types in `x \<Ztypecolon> T` and the `phi_type`, maybe into a smaller sort (e.g. from \<open>?'a::type\<close> to \<open>?'a::one\<close>).
  It can return terms containing schematic variables, and there is no requirement on the index.
*)

(* Guess from BNF *)

val guess_operator :
        (Proof.context * typ list * typ list * eBNF_Info.eBNF -> (term * Proof.context) Seq.seq)
            (*make the operator and configure any necessary reasoning like adding simplification rules *)
     -> (typ -> bool) (*check if the type is alive meaning if it is to guess the operator for it recursively*)
     -> (typ -> Proof.context -> term * Proof.context) (*if the type is not alive, make the operator for this type*)
     -> (typ -> Proof.context -> (term * Proof.context) Seq.seq) (*make the operator for an atom type*)
     -> Proof.context -> (typ * term) list (*known operators and their types*)
     -> typ (*target type*) -> (term * Proof.context) Seq.seq

val guess_set_opr : Proof.context -> typ (*container type*) -> typ (*the target element type*)
                                  -> (term * Proof.context) Seq.seq
val guess_self_rel : Proof.context -> (typ * term) list (*known operators*)
                                   -> typ (*container type*) -> (term * Proof.context) Seq.seq
val guess_predicate : Proof.context -> (typ * term) list (*known predicates*) -> typ -> (term * Proof.context) Seq.seq
val guess_rel_mapper : (typ * typ -> term (*dead_opr*)) -> (typ -> typ) (*f*) -> Proof.context ->
                            typ (*container type*) -> typ (*the target element type*) ->
                            (term * Proof.context) Seq.seq
         (*return the relation mapper from the container type T to f(T), which maps the inner element
              of type U to f(U)*)
val guess_func_mapper : (typ -> typ) (*f*) ->
      Proof.context -> typ (*container*) -> typ (*the target element*) -> (term * Proof.context) Seq.seq
val guess_pred_mapper : Proof.context ->
      typ (*container*) -> typ (*the target element*) -> (term * Proof.context) Seq.seq

val zip_typ : Context.generic -> typ * typ -> typ
  (* zip(T(a1,int,U(a3),W(nat,a4)) , T(b1,int,U(b3),W(nat,b4))) = T(a1*b1, int, U(a3*b3), W(nat,a4*b4))
     The zip only zips type variables (either fixed or schematic).*)
val unzip_typ : Context.generic -> typ -> typ * typ
  (*The inverse function of zip_typ*)
val guess_zip_guided : bool (*true for zip, false for unzip*) ->
                       typ * typ (*the target element types*) ->
                       typ * typ (*container types*) ->
                       Proof.context -> ( term (*domain constraining the arguments of the zip or the unzip*)
                                        * term (*the zip or the unzip*))
                                        * Proof.context

val make_forall_quantified_property : (typ (*x_ty*) * typ (*model_ty*) * term (*x*) * term (*T*) -> term (*the property*))
                                   -> term (*the \<phi>-type operator*)
                                   -> term
val make_forall_quantified_property_for_parameters_of_a_phi_type :
        (typ (*x_ty*) * typ (*model_ty*) * term (*x*) * term (*T*) -> term (*the property*))
     -> term -> term list

(** Load Simpset **)

(*The simplification that unfolds the recursive \<phi>-types and derives induction-hypothetic ToAs,
  uses a specific simpset instead of the default global to prevent over-simplification.
  The reasoning should only load the simplification rules of the used object operators (mapper or predicator etc).
  Bellow they are loaders of the operators.
*)

val load_ss : bool (*set*) * bool (*pred*) * bool (*rel*) * bool (*map*) * bool (*zip*)
           -> eBNF_Info.eBNF -> Proof.context -> Proof.context

val load_simpset : term list -> Proof.context -> Proof.context
  (*Given any object expressions, it parses the object operators used inside,
    and load the related simplification settings*)


(** A framework for deriving properties **)

type ind_conv = (Proof.context -> Phi_Type_Algebra.phi_type -> thm -> thm)
type reasoning = Proof.context -> thm -> thm
type subgoal_configure = (int list (*quant_interps*) * ind_conv) option (*If not given, no induction will be applied*)
                       * (Phi_Type_Algebra.phi_type -> reasoning)
type solver = Phi_Type_Algebra.phi_type * Proof.context * thm -> thm option

(*Main Entry Point*)
val deriving_framework :
      string (*property name used in proof cache and Isabelle binding*)
    * parse_hint
    * (term -> term list) (*extract_oprs_from_hint*)
    * guess_property
    * thm (*rule*)
    * subgoal_configure list
    * solver
    * (Phi_Type_Algebra.phi_type * Proof.context -> thm -> thm) (*final simplification*)
   -> Phi_Type_Algebra.phi_type -> term option -> Proof.context -> thm Seq.seq

(* Besides the parameters explained above,
  extract_oprs_from_hint allows user to indicate what are the mapper, predicator or other operators in
  the given hint, so that we can load reasoning configures like simplification sets binding on the
  operators (e.g., the simplification rules of the related BNF)

  `rule` is a PLPR reasoning rule describing how to derive the target property in detail, in the following form,
  ` ( <the leading antecedent is the one to which induction applies> \<Longrightarrow>
      <some optional antecedents, but no induction will be applied on them> \<Longrightarrow>
      \<r>Success (*terminates the deriving successfully*)
    ) (*repeats as a deriving can invole multiple subgoals*) \<Longrightarrow>
    \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True (*stores the generated proof obligations*) \<Longrightarrow>
    <derived property>`

  A deriving may contain multiple subgoals, and for each subgoal, a configure describes it.
  The configure consists of an optional induction description and a reasoning description.
  It provides supports for applying induction at most once for each goal, but more induction
  can be applied manually.

  Induction description:

  The leading antecedent can be universally quantified by \<And>, the parameter `quant_interps` decides
    how to interpret the quantified variables in a *reversed* order.
  For the last $i$th variable (actually $i$ is the variable's de brujin index),
    quant_interps[i] = 0 means to interpret the variable as the abstract object and therefore the
        induction can destruct it according to the induction rule in the phi_type
    quant_interps[i] = j means to interpret the variable as the j-th parameter of the \<phi>-type
    quant_interps[i] = ~1 means to interpret it as a fixed variable

  `ind_conv` : applies conversion and simplification on the induction rule.
  If not given, no induction will be applied.
  The default_ind_conv parses the induction hypotheses and conclusions, and supports to apply different
    conversion on them.
*)

val default_ind_conv : (Proof.context -> Phi_Type_Algebra.phi_type -> conv) (*converting induction hypotheses*) *
                       (Proof.context -> Phi_Type_Algebra.phi_type -> conv) (*converting subgoals of the induction*)
                    -> ind_conv

(*To use `default_ind_conv`, you must tag the leading antecedent of the `rule` by `\<phi>TA_ind_target`,
  or else `default_ind_conv` cannot find which one is the induction hypothesis,
  see @{thm \<phi>TA_SH\<^sub>I_rule} as an example.*)

(** Reasoning **)
(*`reasoning` specifies how to solve the reasoning goals in detail.*)

type varifier = Subgoal.focus -> term -> (term list * (term list -> term)) option
type reasoning_configure = Subgoal.focus * thm -> thm list * Proof.context -> thm list * thm list * thm list * Proof.context
val varify_all_vars : varifier

type reasoner = Proof.context -> thm -> thm
val default_reasoning :
        bool (*to split the goals when they contain HOL.disj in antecedents, no matter if the conclusion
               contains schematic variables. it is false by default*) ->
        reasoning_configure -> varifier -> reasoner -> reasoning
(*It is a general framework using \<phi>-LPR and Isar subgoal tool.
  Because it uses Isar subgoal, it fixes all schematic variables. Users may expect the reasoning
  to infer some schematic variables. If so, `varifier` is used.
  Given a term, `varifier` returns the subterms that should be schematic variables, and
                a function substituting schematic variables for those subterms.

  `reasoning_configure` parse the role of local premises.
  It receives the subgoal context, local premises, local sequent, and should classify the local premises
  into three sorts, pure conditions, rewrites and reasoners respectively.
*)

val exhaustive_PLPR_reasoner : int option -> (int -> term -> unit) (*chk*) -> reasoner (*TODO: supports chk*)
val exhaustive_PLPR_reasoner_by_rule : thm -> (int -> term -> unit) (*chk*) -> reasoner
  (*The chk may check if the ith argument of the target reasoning goal is in a good form and
    raises warning if not*)

(* Default Reasoning Configure *)

val default_reasoning_configure : Phi_Reasoners.extraction list -> reasoning_configure
(*classify local premises by syntactic tags. allows to extract additional local condition
  by Phi_Reasoners.extraction.

  It also recognizes premises tagged by \<phi>TA_pure_facts and \<phi>TA_conditioned_ToA_template.
  \<phi>TA_conditioned_ToA_template rules are conditioned by pure propositions.
  collects pure facts tagged \<phi>TA_pure_facts, to derive the condition of the \<phi>TA_conditioned_ToA_template rules,
  and therefore to instantiate possible ToA rules from \<phi>TA_conditioned_ToA_template rules.
*)

(** Solver **)

(*The `solver` optionally solves the proof obligation. It can return NONE to fallback to the
  default Auto_Sledgehammer solver.

  When the object operators are given by the hint, the proof obligations should contain no
    undetermined schematic variable and Auto_Sledgehammer is good in this case.
  When no hint is given, a deriver can provide a solver that infers the object operators
    and perhaps call the fallback sledgehammer solver after it.
*)

val oblg_solver : string -> Proof.context -> thm -> thm (*the default Sledgehammer solver*)


(** A framework of deriver **)

datatype hint_mode = ACCEPT_NO_HINT | ACCEPT_ONE_HINT | ACCEPT_ANY_HINTS | REQUIRE_ONE_HINT | REQUIRE_HINTS
datatype multiple_call = ONLY_ONCE | ONLY_ONCE_IF_NO_HINT | MULTIPLE_TIMES

type quiet = bool
val deriver_framework : hint_mode * multiple_call * string (*name*)
                     -> (int (*the times that the deriver has been invoked*) * string (*name suffixed by the time*)
                          -> hint option
                          -> Phi_Type_Algebra.deriving_ctxt
                          -> Phi_Type_Algebra.phi_type
                          -> generic_theory
                          -> thm list (*derived rule*) * generic_theory)
                     -> quiet
                     -> hint list
                     -> Phi_Type_Algebra.derive
(*This simple framework handles the issue of invoking a deriver by multiple times,
  and also checks if the proper number of hints are given.
  Then it calls the given diver for each hint one by one, or call it by NONE is no hint is given.

  When the deriver is invoked more than once, the name is suffixed by an index to differentiate the
  binding of the resulted rule among the callings.

  The derived rule will be stored into \<phi>-Type library but I will not bind it into the Isabelle environment.

  If `quiet` is turned on, no error will be printed and it returns silently with doing nothing,
  even when the deriver raises Automation_Fail.
*)

val deriver_framework_no_hints : multiple_call * string (*name*)
                     -> (string (*name*)
                          -> Phi_Type_Algebra.deriving_ctxt
                          -> Phi_Type_Algebra.phi_type
                          -> generic_theory
                          -> thm list (*derived rule*) * generic_theory)
                     -> quiet
                     -> Phi_Type_Algebra.derive

(** Misc Tools **)

exception Automation_Fail of (unit -> Pretty.T list)
structure Expansion : SIMPSET (*The standard simpset for deriving*)

(*
val accept : (hint option -> Phi_Type_Algebra.derive) -> hint list -> Phi_Type_Algebra.derive
val accept_one : string (*name for printing*) ->
      (hint option -> Phi_Type_Algebra.derive) ->
       hint list -> Phi_Type_Algebra.derive
    (*wraps and checks if the user gives at most one hint*)
*)

val chk_unfolded : Context.generic -> Phi_Type_Algebra.phi_type -> term -> unit
val chk_unfolded': Proof.context -> Phi_Type_Algebra.phi_type -> term -> unit
val conv_chk_unfolded : Phi_Type_Algebra.phi_type -> Proof.context -> conv
      (*roughly check if a phi-type expression is expanded, and warn if not*)

val chk_abstract_object_quantified : (term -> term option) (*get the abstract object*)
                                  -> Proof.context -> term -> term

val lift_types_sort : theory -> (typ * sort) list -> typ TVars.table

end

(**** Implementation ****)

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra

type induct_inst_params = term option list
type guess_property =
        Phi_Type_Algebra.phi_type ->
        Proof.context ->
        (term list * term * term option list * Phi_Type_Algebra.phi_type * Proof.context ) Seq.seq

(** Simplification Rules unfolding the constrains and conditions **)

structure Type_specific_Simps = Generic_Data (
  type T = thm Net.net
  val empty = Net.empty
  val merge = Net.merge pointer_eq
)

exception Parse_Fail of string list

fun parse_which_type_for_the_rule rule =
  let val exclude = [\<^type_name>\<open>bool\<close>, \<^type_name>\<open>nat\<close>, \<^type_name>\<open>int\<close>, \<^type_name>\<open>prop\<close>, \<^type_name>\<open>fun\<close>, \<^type_name>\<open>set\<close>]
      fun fold_type_const f =
        let fun fld (Type (Tname, Targs)) x = fold fld Targs (f Tname x)
              | fld _ x = x
         in fld
        end
      fun add_tyconst tm = fold_types (fold_type_const (fn Tname =>
              if member (op =) exclude Tname then I else insert (op =) Tname)) tm []
      val tyconsts = add_tyconst (Thm.concl_of rule)
   in case tyconsts
   of [tycon] => tycon
    | L => raise Parse_Fail L
  end

fun add_type_specific_simp (Tname, rules) ctxt =
  Type_specific_Simps.map (fold (fn rule =>
      Net.insert_term (Thm.equiv_thm (Context.theory_of ctxt))
                      (Const(Tname, Term.dummyT) $ Thm.prop_of rule,
                       rule)
      ) rules) ctxt

fun del_type_specific_simp (Tname, rules) ctxt =
  Type_specific_Simps.map (fold (fn rule =>
      Net.delete_term_safe (Thm.equiv_thm (Context.theory_of ctxt))
                           (Const(Tname, Term.dummyT) $ Thm.prop_of rule,
                            rule)
      ) rules) ctxt

fun get_type_specific_simp ctxt Tname =
  Net.unify_term (Type_specific_Simps.get ctxt) (Const(Tname, Term.dummyT) $ Var (("",0),TVar(("",0),[])))

structure Simps = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>deriver_simp\<close>
  val comment = "Simplification rules that derivers use to simplify the guessed or infered properties."
  val attribute = NONE
)

structure Expansion = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>\<phi>constraint_expansion\<close>
  val comment = "Rules unfolding constraints and conditions in property deriving of \<phi>-type algebra.\n\
                \Basically, simplification rules for object operators including mappers, relators, \
                \predicators of the abstract algebra of \<phi>-types"
  val attribute = SOME (fn add => fn del =>
    let fun gen (opr1, opr2) =
          (fn SOME "" => opr1
            | NONE => Thm.declaration_attribute (fn th => let open Pretty in
                          opr2 (@{print} (parse_which_type_for_the_rule th), [th])
                        handle Parse_Fail [] => error (string_of (
                                  para "You are declaring a simp rule applying locally only on\
                                       \ certain specific type. The type is not given and I \
                                       \failed to parse it from the given rule. Please \
                                       \indicate it explicitly by [\<phi>constraint_expansion for <the type>].\
                                       \ Otherwise, maybe you want the rule to be applied everywhere \
                                       \globally. If so, declare [\<phi>constraint_expansion global]."))
                             | Parse_Fail L => error (string_of (chunks (
                                  para "You are declaring a simp rule applying locally only on\
                                       \ certain specific type. The type is not given and I \
                                       \tried to parse it from the given rule but I cannot \
                                       \determine which type you prefer from the candidates below." ::
                                  map (fn N => item [str N]) L @
                                 [para "Please indicate it explicitly by [\<phi>constraint_expansion for <the type>].\
                                       \ Otherwise, maybe you want the rule to be applied everywhere \
                                       \globally. If so, declare [\<phi>constraint_expansion global]."]
                                  )))
                        end)
            | SOME Tname => Thm.declaration_attribute (fn th => opr2 (Tname, [th])))
        val add' = gen (add, add_type_specific_simp)
        val del' = gen (del, del_type_specific_simp)
     in Scan.lift (Args.add >> K add' || Args.del >> K del' || Scan.succeed add')
          -- (  Scan.lift (Args.$$$ "global") >> K (SOME "")
             || Scan.lift \<^keyword>\<open>for\<close> |-- Args.type_name {proper=true, strict=true} >> SOME
             || Scan.succeed NONE)
     >> (fn (attr, target) => attr target)
    end)
)

(*
local
  fun is_atom (Bound _) = true
      | is_atom (Free _) = true
      | is_atom (Var _) = true
      | is_atom _ = false
in val eq_simproc = Simplifier.make_simproc \<^context> "Phi_Type_Algebra.eq" {
    lhss = [\<^pattern>\<open>_ = _\<close>],
    proc = fn _ => fn ctxt => fn ctm =>
      case Thm.term_of ctm
        of _ (*eq*) $ LHS $ RHS =>
            if is_atom RHS andalso not (is_atom LHS)
            then SOME (Conv.rewr_conv (Thm.transfer' ctxt @{thm' eq_commute[folded atomize_eq]}) ctm)
            else NONE
         | _ => NONE
  }
end *)

val _ = Theory.setup (Context.theory_map (

  Expansion.map (fn ctxt =>
    (ctxt addsimprocs [\<^simproc>\<open>HOL.defined_Ex\<close>, \<^simproc>\<open>Set.defined_All\<close>, \<^simproc>\<open>ExSet_expand_quantifier\<close>,
                       \<^simproc>\<open>HOL.defined_All\<close>(*, eq_simproc*), \<^simproc>\<open>NO_MATCH\<close>,
                       \<^simproc>\<open>Funcomp_Lambda\<close>])
      |> Simplifier.add_cong @{thm imp_cong[folded atomize_eq]}
      |> Simplifier.add_cong @{thm HOL.conj_cong})
          (*Because of this cong, the order of the conjunction is significant!*)
))

(** Guess Abstract Operators from BNF **)

type quasi_BNF = {}
datatype eBNF = BNF of BNF_Def.bnf | qBNF of quasi_BNF

(* Library *)

fun extract_hhf (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = extract_hhf X
  | extract_hhf (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = extract_hhf X
  | extract_hhf (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = extract_hhf X
  | extract_hhf X = Envir.beta_eta_contract X

(* fun permute_seq (s::L) =
      Seq.maps (fn s' => permute_seq L |> Seq.map (fn L' => s'::L')) s
  | permute_seq [] = Seq.single [] *)

fun gen_guess_operator mk_term is_live mk_operator_for_dead atom_opr =
  let fun guess_operator' ctxt known_oprs x_ty =
        case map_filter (fn (ty', term) => if ty' = x_ty then SOME term else NONE)
                        known_oprs
          of [] => (
            case x_ty
              of Type(Tname, Targs) =>
                 if Sign.arity_number (Proof_Context.theory_of ctxt) Tname = 0
                 then Seq.single (mk_operator_for_dead x_ty ctxt)
                 else
                   let val bnf = eBNF_Info.get_bnf1 (Context.Proof ctxt) Tname
                       val (D,L) = eBNF_Info.classify_bnf_dead_live bnf Targs
                    in mk_term (ctxt, D, L, bnf)
                    |> Seq.maps (fn (head,ctxt') =>
                        let fun mk_params ctxt (ty::L) =
                                  (if not (AList.defined (op =) known_oprs ty) orelse is_live ty
                                   then guess_operator' ctxt known_oprs ty
                                   else Seq.single (mk_operator_for_dead ty ctxt))
                                    |> Seq.maps (fn (opr, ctxt') =>
                                          mk_params ctxt' L
                                            |> Seq.map (fn (oprs, ctxt'') => (opr::oprs, ctxt'')))
                              | mk_params ctxt [] = Seq.single ([], ctxt)
                         in mk_params ctxt' L
                         |> Seq.map (fn (params', ctxt'3) =>
                              (fold (fn p => fn X => X $ p) params' head, ctxt'3))
                        end)
                   end
               | _ => atom_opr x_ty ctxt)
           | L => Seq.of_list L
               |> Seq.map (rpair ctxt)
   in guess_operator'
  end

fun guess_operator mk_term is_live mk_operator_for_dead atom_opr =
  let fun guess ctxt known_oprs x_ty =
            Seq.make (fn () =>
              case Seq.pull (gen_guess_operator mk_term is_live mk_operator_for_dead atom_opr ctxt known_oprs x_ty)
                of NONE => (warning ("Fail to guess the abstract operator for type "
                                    ^ Syntax.string_of_typ ctxt x_ty) ;
                            NONE)
                 | some => some )
   in guess
  end

fun add_global_simps thms ctxt = ctxt
  |> Expansion.add_simps' thms
  |> (fn ctxt => ctxt addsimps thms)

fun proof_map_result f ctxt = f (Context.Proof ctxt) |> apsnd (Context.proof_of)

fun load_ss (set,pred,rel,map,zip) bnf ctxt = 
  let fun more_rule flag gen (rules, ctxt) =
            if flag then (case gen ctxt of (rule, ctxt) => (rule :: rules, ctxt)) else (rules, ctxt)
      fun more_rules flag gen (rules, ctxt) =
            if flag then (case gen ctxt of (rule, ctxt) => (rule @ rules, ctxt)) else (rules, ctxt)
      val (additional, ctxt) = ([], ctxt)
            |> more_rules rel (proof_map_result (eBNF_Info.relator_on_const_true bnf))
   in ctxt
   |> Expansion.add_simps' ( eBNF_Info.simps_of_ctr_safe bnf
                       @ (if set then eBNF_Info.simps_of_set_safe bnf else [])
                       @ (if pred then eBNF_Info.simps_of_pred_safe bnf else [])
                       @ (if rel then eBNF_Info.simps_of_rel_safe bnf else [])
                       @ (if map then eBNF_Info.simps_of_map_safe bnf else [])
                       @ (if zip then eBNF_Info.simps_of_zip_safe bnf else [])
                       @ get_type_specific_simp (Context.Proof ctxt) (eBNF_Info.Tname_of bnf)
                       @ additional)
   |> add_global_simps ( (if pred then eBNF_Info.global_simps_of_pred_safe bnf else [])
                       @ (if rel then eBNF_Info.global_simps_of_rel_safe bnf else [])
                       @ (if map then eBNF_Info.global_simps_of_map_safe bnf else []))
  end


(* Set *)

(*ty: container type*)
fun guess_set_opr ctxt ty element_ty =
  if ty = element_ty
  then Seq.single (Abs("",ty, \<^Const>\<open>insert ty\<close> $ Bound 0 $ \<^Const>\<open>bot \<^Type>\<open>set ty\<close>\<close>), ctxt)
  else case ty
         of Type(Tname, Targs) =>
                let val bnf = eBNF_Info.get_bnf1 (Context.Proof ctxt) Tname
                    val (D,L) = eBNF_Info.classify_bnf_dead_live bnf Targs
                    val N = length (eBNF_Info.sets_of_bnf bnf)
                    val tys1 = List.tabulate (N, K D)
                    val tys2 = List.tabulate (N, K L)
                    val sets = eBNF_Info.mk_sets_of_bnf tys1 tys2 bnf
                    val ctxt' = ctxt addsimps ( eBNF_Info.simps_of_set_safe bnf
                                              @ eBNF_Info.simps_of_ctr_safe bnf)
                 in Seq.of_list sets
                 |> Seq.maps (fn s =>
                      case Term.fastype_of s
                        of \<^Type>\<open>fun _ \<^Type>\<open>set x\<close>\<close> =>
                              if x = element_ty
                              then Seq.single (s, ctxt')
                              else guess_set_opr ctxt' x element_ty
                                     |> Seq.map (fn (s',ctxt'') =>
                                          (Abs("", ty, \<^Const>\<open>Set.bind x element_ty\<close> $ (s $ Bound 0) $ s'), ctxt''))
                         | _ => error "Internal bug f07de235-2838-4483-b2f9-b0cce6d06676")
                end
          | _ => Seq.empty

(* Relator *)

(*the relation between terms in the same type*)
val guess_self_rel =
  let fun mk_term (ctxt, D, L, bnf) =
        let val ctxt' = ctxt addsimps ( eBNF_Info.simps_of_rel_safe bnf
                                      @ eBNF_Info.simps_of_ctr_safe bnf)
                     |> add_global_simps (eBNF_Info.global_simps_of_rel bnf)
         in Seq.single (eBNF_Info.mk_rel_of_bnf D L L bnf, ctxt')
        end
      val is_live = K true
      fun mk_operator_for_dead _ _ = error "Internal bug"
      fun atom_opr ty ctxt =
            Seq.single (Abs("", ty, Abs("", ty, \<^Const>\<open>True\<close>)), ctxt)
   in guess_operator mk_term is_live mk_operator_for_dead atom_opr
  end

(* Predicator *)

val guess_predicate =
  let fun mk_term (ctxt, D, L, bnf) =
        let val ctxt' = load_ss (false,true,false,false,false) bnf ctxt
         in Seq.single (eBNF_Info.mk_pred_of_bnf D L bnf, ctxt')
        end
      val is_live = K true
      fun mk_operator_for_dead ty ctxt = (Abs("", ty, \<^Const>\<open>True\<close>), ctxt)
      fun atom_opr ty ctxt = Seq.single (mk_operator_for_dead ty ctxt)
   in guess_operator mk_term is_live mk_operator_for_dead atom_opr
  end

(* Mapper *)

(*ty: container_ty
  dead_opr: the relation for dead type parameters (including those are not the target element type)*)
fun guess_rel_mapper dead_opr target_ty ctxt ty element_ty =
  let val [g'] = Name.invent (Variable.names_of ctxt) "g" 1
      val ([g], ctxt') = Variable.add_fixes [g'] ctxt
      val element_ty' = target_ty element_ty
      val g_ty = element_ty --> element_ty' --> HOLogic.boolT
      val g_term = Free(g, g_ty)
      val known_rels = [(element_ty, g_term)]
      fun mk_term (ctxt, D, L, bnf) =
        let val ctxt' = load_ss (false,false,true,true,false) bnf ctxt
         in Seq.single (eBNF_Info.mk_rel_of_bnf D L (map target_ty L) bnf, ctxt')
        end
      val is_live = Term.exists_subtype (fn ty' => ty' = element_ty)
      fun mk_operator_for_dead typ ctxt = (\<^Const>\<open>HOL.eq typ\<close>, ctxt)
      fun mk_dead_opr ty ctxt = Seq.single (dead_opr (ty, target_ty ty), ctxt)
   in guess_operator mk_term is_live mk_operator_for_dead mk_dead_opr ctxt' known_rels ty
   |> Seq.map (fn (rel_term', ctxt) =>
        (Abs("", g_ty, Term.abstract_over (g_term, rel_term')), ctxt))
  end

fun guess_func_mapper target_ty ctxt ty element_ty =
  let val [g'] = Name.invent (Variable.names_of ctxt) "g" 1
      val ([g], ctxt') = Variable.add_fixes [g'] ctxt
      val element_ty' = target_ty element_ty
      val g_ty = element_ty --> element_ty'
      val g_term = Free(g, g_ty)
      val known_mappers = [(element_ty, g_term)]
      fun mk_term (ctxt, D, L, bnf) =
        let val ctxt' = load_ss (false,false,false,true,false) bnf ctxt
         in Seq.single (eBNF_Info.mk_map_of_bnf D L (map target_ty L) bnf, ctxt')
        end
      val is_live = Term.exists_subtype (fn ty' => ty' = element_ty)
      fun mk_operator_for_dead typ ctxt = (Abs("", typ, Bound 0), ctxt)
      fun atom_opr ty ctxt = Seq.single (mk_operator_for_dead ty ctxt)
   in guess_operator mk_term is_live mk_operator_for_dead atom_opr ctxt' known_mappers ty
   |> Seq.map (fn (map_term', ctxt) =>
        (Abs("", g_ty, Term.abstract_over (g_term, map_term')), ctxt))
  end

fun guess_pred_mapper ctxt ty element_ty =
  let val [g'] = Name.invent (Variable.names_of ctxt) "g" 1
      val ([g], ctxt') = Variable.add_fixes [g'] ctxt
      val g_ty = element_ty --> HOLogic.boolT
      val g_term = Free(g, g_ty)
      val known_mappers = [(element_ty, g_term)]
      fun mk_term (ctxt, D, L, bnf) =
        let val ctxt' = load_ss (false,true,false,false,false) bnf ctxt
         in Seq.single (eBNF_Info.mk_pred_of_bnf D L bnf, ctxt')
        end
      val is_live = Term.exists_subtype (fn ty' => ty' = element_ty)
      fun mk_operator_for_dead typ ctxt = (Abs("", typ, \<^Const>\<open>True\<close>), ctxt)
      fun atom_opr ty ctxt = Seq.single (mk_operator_for_dead ty ctxt)
   in guess_operator mk_term is_live mk_operator_for_dead atom_opr ctxt' known_mappers ty
   |> Seq.map (fn (map_term', ctxt) =>
        (Abs("", g_ty, Term.abstract_over (g_term, map_term')), ctxt))
  end

(* Zip \& Unzip *)

fun unzip_typ _ (\<^Type>\<open>prod \<open>a as TFree _\<close> \<open>b as TFree _\<close>\<close>) = (a,b)
  | unzip_typ _ (\<^Type>\<open>prod \<open>a as TVar _\<close> \<open>b as TVar _\<close>\<close>) = (a,b)
  | unzip_typ ctxt (Type(Tname, Targs)) =
      let val bnf = eBNF_Info.get_bnf1 ctxt Tname
          val (deads,lives) = eBNF_Info.classify_bnf_dead_live bnf Targs
          val lives' = map (unzip_typ ctxt) lives
                    |> split_list
       in (Type (Tname,eBNF_Info.burrow_bnf_dead_live bnf (deads, fst lives')),
           Type (Tname,eBNF_Info.burrow_bnf_dead_live bnf (deads, snd lives')))
      end

fun zip_typ _ ((a as TFree _), (b as TFree _)) = \<^Type>\<open>prod a b\<close>
  | zip_typ _ ((a as TVar _), (b as TVar _)) = \<^Type>\<open>prod a b\<close>
  | zip_typ ctxt (Type(Tname, Targs), Type(Tname', Targs')) =
      let val _ = if Tname = Tname' then () else raise TYPE ("zip_typ", [], [])
          val bnf = eBNF_Info.get_bnf1 ctxt Tname
          val (deads,lives) = eBNF_Info.classify_bnf_dead_live bnf Targs
          val (deads',lives') = eBNF_Info.classify_bnf_dead_live bnf Targs'
          val _ = if deads = deads' then () else raise TYPE ("zip_typ", [], [])
          val lives_merge = map2 (fn t1 => fn t2 => zip_typ ctxt (t1,t2)) lives lives'
          val Targs_merge = eBNF_Info.burrow_bnf_dead_live bnf (deads, lives_merge)
       in Type (Tname, Targs_merge)
      end

fun occur_subtyp T T' =
  if T = T' then true
  else case T' of Type (_, args) => exists (occur_subtyp T) args
                | _ => false

(*flag=true for zip, flag=false for unzip*)
fun guess_zip_guided flag (target,target') (T,T') ctxt =
  let val occur = occur_subtyp target T
      val occur' = occur_subtyp target' T'
   in if occur andalso occur'
      then if T = target andalso T' = target'
      then ((Abs("x", T, Abs("y", T', \<^Const>\<open>True\<close>)),
             Abs("x", \<^Type>\<open>prod T T'\<close>, Bound 0)),
           ctxt)
      else case (T,T')
             of (Type(Tname, Targs), Type(Tname', Targs')) =>
                let val _ = if Tname = Tname' then () else raise TYPE ("guess_zip", [], [])
                    val bnf = eBNF_Info.get_bnf1 (Context.Proof ctxt) Tname
                    val (deads,lives) = eBNF_Info.classify_bnf_dead_live bnf Targs
                    val (deads',lives') = eBNF_Info.classify_bnf_dead_live bnf Targs'
                    val _ = if deads = deads' then () else raise TYPE ("guess_zip", [], [])
                    val fp_more = case BNF_FP_Sugar_More.get_fp_more (Context.Proof ctxt) Tname
                                    of SOME x => x
                                     | NONE => raise Automation_Fail (fn () =>
                                                  [Pretty.block [Pretty.str "Fail to guess the zip operator for type ",
                                                                 Pretty.str Tname]])
                    val zip = (if flag then BNF_FP_Sugar_More.mk_zip
                                       else BNF_FP_Sugar_More.mk_unzip) deads lives lives' fp_more
                    val ctxt'' = load_ss (false,false,true,true,true) bnf ctxt
                    val (args, ctxt') = ctxt''
                          |> fold_map (guess_zip_guided flag (target,target'))
                                      (lives ~~ lives')
                    val map_tys = map (fn (_,z) => case Term.fastype_of z
                                                     of \<^Type>\<open>fun a b\<close> => (a,b)) args
                                |> split_list
                    val mp = eBNF_Info.mk_map_of_bnf deads (fst map_tys) (snd map_tys) bnf
                    val rl = eBNF_Info.mk_rel_of_bnf deads lives lives' bnf
                    val mp' = Term.list_comb (mp, map snd args)
                 in((Term.list_comb (rl, map fst args),
                     Abs("x", domain_type (Term.fastype_of (if flag then zip else mp')),
                              if flag then mp' $ (zip $ Bound 0)
                                      else zip $ (mp' $ Bound 0))),
                    ctxt')
                end
              | _ => error "Internal bug #928dccd3-7497-4f2c-867c-4b7407fcfdef"
      else if not occur andalso not occur'
        then if T = T'
          then ((\<^Const>\<open>HOL.eq T\<close>, \<^Const>\<open>fst T T\<close>), ctxt)
          else error "Only the target can vary in guided guess_zip"
        else error "Internal bug #a1dd0817-f55a-468e-ba79-95183f145380"
  end

(* DO NOT REMOVE, still good and maybe useful, but not maintained
fun guess_zip flag (*(target,target')*) (Type(Tname, Targs), Type(Tname', Targs')) ctxt =
      let val _ = if Tname = Tname' then () else raise TYPE ("guess_zip", [], [])
          val bnf = eBNF_Info.get_bnf1 (Context.Proof ctxt) Tname
          val (deads,lives) = eBNF_Info.classify_bnf_dead_live bnf Targs
          val (deads',lives') = eBNF_Info.classify_bnf_dead_live bnf Targs'
          val _ = if deads = deads' then () else raise TYPE ("guess_zip", [], [])
          val fp_more = case BNF_FP_Sugar_More.get_fp_more (Context.Proof ctxt) Tname
                          of SOME x => x
                           | NONE => raise Automation_Fail ("Fail to guess the zip operator for type " ^ Tname)
          val zip = (if flag then BNF_FP_Sugar_More.mk_zip
                             else BNF_FP_Sugar_More.mk_unzip) deads lives lives' fp_more
          val (args, ctxt') = ctxt addsimps eBNF_Info.simps_of_ctr_safe bnf
                  |> fold_map (guess_zip flag) (lives ~~ lives')
          val map_tys = map (fn z => case Term.fastype_of z
                                       of \<^Type>\<open>fun a b\<close> => (a,b)) args
                      |> split_list
          val mp = eBNF_Info.mk_map_of_bnf deads (fst map_tys) (snd map_tys) bnf
       in (Abs("x", domain_type (Term.fastype_of zip),
                    Term.list_comb (mp, args) $ (zip $ Bound 0)),
           ctxt')
      end
  | guess_zip _ ((a as TFree _), (b as TFree _)) ctxt = (Abs("x", \<^Type>\<open>prod a b\<close>, Bound 0), ctxt)
  | guess_zip _ ((a as TVar _), (b as TVar _)) ctxt = (Abs("x", \<^Type>\<open>prod a b\<close>, Bound 0), ctxt)
  | guess_zip _ (a,b) _ = raise TYPE ("guess_zip", [a,b], [])
*)

(* load simpset *)

fun const_eq const_name (Const(N, _)) = const_name = N
  | const_eq _ _ = false

fun mp f x = case f x of SOME y => SOME (y, x) | _ => NONE

fun load_rel (const_name, ty) ctxt =
  let fun parse_typ \<^Type>\<open>fun \<open>Type(N, _)\<close> \<^Type>\<open>fun \<open>Type(N',_)\<close> \<^Type>\<open>bool\<close>\<close>\<close> =
            if N <> N' then NONE
            else eBNF_Info.get_bnf (Context.Proof ctxt) N
              |> Option.mapPartial (mp eBNF_Info.rel_of_bnf_safe)
              |> Option.mapPartial (fn (C, bnf) =>
                   if const_eq const_name C
                   then SOME (load_ss (false,false,true,true,false) bnf ctxt)
                   else NONE)
        | parse_typ \<^Type>\<open>fun \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close>\<close> T\<close> = parse_typ T
        | parse_typ _ = NONE
   in parse_typ ty
  end

(*CN: const name*)
fun load_set (CN, \<^Type>\<open>fun \<open>Type(N,_)\<close> \<^Type>\<open>set _\<close>\<close>) ctxt =
      eBNF_Info.get_bnf (Context.Proof ctxt) N
        |> Option.mapPartial (mp eBNF_Info.sets_of_bnf_safe)
        |> Option.mapPartial (fn (C, bnf) =>
            if exists (const_eq CN) C
            then SOME (load_ss (true,false,false,false,false) bnf ctxt)
            else NONE)
  | load_set _ _ = NONE

fun load_predicate (CN, \<^Type>\<open>fun \<open>Type(N,_)\<close> \<^Type>\<open>bool\<close>\<close>) ctxt =
      eBNF_Info.get_bnf (Context.Proof ctxt) N
        |> Option.mapPartial (mp eBNF_Info.pred_of_bnf_safe)
        |> Option.mapPartial (fn (C, bnf) =>
            if const_eq CN C
            then SOME (load_ss (false,true,false,false,false) bnf ctxt)
            else NONE)
  | load_predicate (CN, \<^Type>\<open>fun \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close> T\<close>) ctxt = load_predicate (CN, T) ctxt
  | load_predicate _ _ = NONE

fun load_map (CN, \<^Type>\<open>fun \<open>Type(N,_)\<close> \<open>T as Type(N',_)\<close>\<close>) ctxt =
      if N = "fun"
      then load_map (CN, T) ctxt
      else if N = N'
      then eBNF_Info.get_bnf (Context.Proof ctxt) N
        |> Option.mapPartial (mp eBNF_Info.map_of_bnf_safe)
        |> Option.mapPartial (fn (C, bnf) =>
              if const_eq CN C
              then SOME (load_ss (false,false,false,true,false) bnf ctxt)
              else load_map (CN, T) ctxt)
      else load_map (CN, T) ctxt
  | load_map (CN, \<^Type>\<open>fun \<^Type>\<open>fun _ _\<close> T\<close>) ctxt = load_map (CN, T) ctxt
  | load_map _ _ = NONE

fun load_unzip (CN, \<^Type>\<open>fun \<open>T2 as Type(N'', ts3)\<close> \<^Type>\<open>prod \<open>Type(N,ts1)\<close> \<open>Type(N',ts2)\<close>\<close>\<close>) ctxt =
      let fun chk_ts (t1::ts1) (t2::ts2) (\<^Type>\<open>prod a b\<close>::ts3) =
                a = t1 andalso b = t2 andalso chk_ts ts1 ts2 ts3
            | chk_ts [] [] [] = true
            | chk_ts _ _ _ = false
       in if N = N'' andalso N = N' andalso chk_ts ts1 ts2 ts3
          then eBNF_Info.get_bnf (Context.Proof ctxt) N
            |> Option.mapPartial (mp eBNF_Info.fp_more_of)
            |> Option.mapPartial (fn (fp_more, bnf) =>
                  if const_eq CN (#unzip fp_more)
                  then SOME (load_ss (false,false,true,true,true) bnf ctxt)
                  else load_unzip (CN, T2) ctxt)
          else load_unzip (CN, T2) ctxt
      end
  | load_unzip (CN, \<^Type>\<open>fun _ T2\<close>) ctxt = load_unzip (CN, T2) ctxt
  | load_unzip _ _ = NONE

fun load_zip (CN, \<^Type>\<open>fun \<^Type>\<open>prod \<open>Type(N,ts1)\<close> \<open>Type(N',ts2)\<close>\<close> \<open>T2 as Type(N'', ts3)\<close>\<close>) ctxt =
      let fun chk_ts (t1::ts1) (t2::ts2) (\<^Type>\<open>prod a b\<close>::ts3) =
                a = t1 andalso b = t2 andalso chk_ts ts1 ts2 ts3
            | chk_ts [] [] [] = true
            | chk_ts _ _ _ = false
       in if N = N'' andalso N = N' andalso chk_ts ts1 ts2 ts3
          then eBNF_Info.get_bnf (Context.Proof ctxt) N
            |> Option.mapPartial (mp eBNF_Info.fp_more_of)
            |> Option.mapPartial (fn (fp_more, bnf) =>
                  if const_eq CN (#zip fp_more)
                  then SOME (load_ss (false,false,true,true,true) bnf ctxt)
                  else load_zip (CN, T2) ctxt)
          else load_zip (CN, T2) ctxt
      end
  | load_zip (CN, \<^Type>\<open>fun _ T2\<close>) ctxt = load_zip (CN, T2) ctxt
  | load_zip _ _ = NONE

fun load_const C ctxt =
  the_default ctxt (get_first (fn ld => ld C ctxt)
      [load_rel, load_set, load_predicate, load_map, load_unzip, load_zip])

val add_consts' = fold_aterms (fn Const c => insert (op = o apply2 fst) c | _ => I);
fun load_simpset tms ctxt = fold load_const (fold add_consts' tms []) ctxt



(** Deriver Framework **)

datatype hint_mode = ACCEPT_NO_HINT | ACCEPT_ONE_HINT | ACCEPT_ANY_HINTS | REQUIRE_ONE_HINT | REQUIRE_HINTS
datatype multiple_call = ONLY_ONCE | ONLY_ONCE_IF_NO_HINT | MULTIPLE_TIMES

type quiet = bool

fun deriver_framework (hint_mode, multiple_call, name) deriver
                      quiet hints ctxt_derv phi thy =
  let val ind = length (lookup_derived_properties thy phi name)
      val _ = let open Pretty in
          case (multiple_call, ind, hints)
            of (_, 0, _) => ()
             | (ONLY_ONCE, _, _) => raise Automation_Fail (fn () => [
                  paragraph (str "deriver " :: brk 1 :: str name :: brk 1 :: text "can only be invoked once")
                ])
             | (ONLY_ONCE_IF_NO_HINT, _, []) => raise Automation_Fail (fn () => [
                  paragraph (str name :: brk 1 :: text "has already derived the hint-less case.\
                             \ Please provide the desired form of the rule if you want to derive more.")
                ])
             | _ => ()
          end
      val _ = let open Pretty in
          case (hint_mode, hints)
            of (ACCEPT_NO_HINT, _ :: _) => raise Automation_Fail (fn () =>
                  paragraph (str name :: brk 1 :: text "accepts no hint, but given") ::
                  map (fn H => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term thy H]) hints
                )
             | (ACCEPT_ONE_HINT, _ :: _ :: _) => raise Automation_Fail (fn () =>
                  paragraph (str name :: brk 1 :: text "accepts at most one hint, but more hints are given") ::
                  map (fn H => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term thy H]) hints
                )
             | (REQUIRE_ONE_HINT, []) => raise Automation_Fail (fn () => [
                  paragraph (str name :: brk 1 :: text "requires exact one hint, but no hint is given")
                ])
             | (REQUIRE_ONE_HINT, _ :: _ :: _) => raise Automation_Fail (fn () =>
                  paragraph (str name :: brk 1 :: text "requires exact one hint, but more hints are given") ::
                  map (fn H => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term thy H]) hints
                )
             | (REQUIRE_HINTS, []) => raise Automation_Fail (fn () => [
                  paragraph (str name :: brk 1 :: text "requires some hint(s), but no hint is given")
                ])
             | _ => ()
          end
      fun invoke (i,H) thy =
        let val iname = suffix_name_by_index (i+ind) name
         in deriver (i+ind, iname) H ctxt_derv phi thy
         |-> register_derived_properties phi (name, i+ind)
        end
   in (case hints
   of [] => invoke (ind, NONE) thy
    |  L => fold_index invoke (map SOME L) thy)
  end
  handle (ex as Automation_Fail _) => if quiet then thy else Exn.reraise ex

fun deriver_framework_no_hints (mcall, name) deriver quiet =
  deriver_framework (ACCEPT_NO_HINT, mcall, name) (fn (_,name) => fn _ => deriver name) quiet []

(*
fun accept gen [] phityp thy = gen NONE phityp thy
  | accept gen Hs phityp thy = fold (fn H => gen (SOME H) phityp) Hs thy

fun accept_one _ gen [] phityp thy = gen NONE phityp thy
  | accept_one _ gen [H] phityp thy = gen (SOME H) phityp thy
  | accept_one prop_name _ hints _ thy =
      let open Pretty
       in error (string_of (chunks (
            block [str prop_name, str " only derives one reasoning rule, but multiple hints are given"] ::
            map (fn H => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term thy H]) hints)))
      end*)

(*depreciated:*)
local

fun is_the_hint prop_name (\<^Const>\<open>Trueprop\<close> $ X) = is_the_hint prop_name X
  | is_the_hint prop_name (\<^Const>\<open>Pure.imp\<close> $ _ $ X) = is_the_hint prop_name X
  | is_the_hint prop_name X = (case Term.head_of X
                                 of Const(N',_) => N' = prop_name
                                  | _ => false)

fun is_deriving_hint prop_name (\<^Const>\<open>Pure.term _\<close> $ Const(N',_)) = N' = prop_name
  | is_deriving_hint _ _ = false

fun err_derive prop_name =
      error ("Fail to derive the property " ^ prop_name)

fun err_prove hint thy =
      error ("Fail to derive the given property:\n" ^
      Context.cases Syntax.string_of_term_global Syntax.string_of_term thy hint)

in

fun select_one_hint prop_name action (hints,thy) =
  case (filter (is_the_hint prop_name) hints, filter (is_deriving_hint prop_name) hints)
    of ([hint], []) => (
          (filter_out (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints,
           action (SOME hint) thy)
          handle Automation_Fail msg => err_prove hint thy msg)
     | ([], [_]) => (
          (filter_out (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints,
           action NONE thy)
          (* handle Automation_Fail => err_derive prop_name *))
     | ([], []) => (hints, thy)
     | _ => error ("More than one hint of "^ prop_name ^ " are given!")

fun select_hints prop_name action (hints,thy) =
  case (filter (is_the_hint prop_name) hints, filter (is_deriving_hint prop_name) hints)
    of ([], []) => (hints, thy)
     | ([], [_]) => (
          (filter_out (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints,
           action NONE thy)
          handle Automation_Fail msg => err_derive prop_name msg)
     | ([], _) => error ("It is enough to just give me one hint to derive "^ prop_name)
     | (hints, _) => (
          filter_out (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints,
          fold (fn hint => action (SOME hint)
                handle Automation_Fail msg => err_prove hint thy msg)
               hints thy)

fun chk_no_hints prop_name (hints, thy) =
  case filter (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints
    of [] => (hints, thy)
     | _ => error ("Property " ^ prop_name ^ " is not supported on the \<phi>-type.")

end

(** Automation Framework **)

(* Default Obligation Solver *)

type solver = Phi_Type_Algebra.phi_type * Proof.context * thm -> thm option

fun oblg_solver proof_id ctxt sequent =
  (*case Thm.major_prem_of sequent
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
          Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _) =>*)
   let val ctxt'' = Expansion.equip ctxt
                 |> Simplifier.del_cong @{thm HOL.conj_cong}
       val sequent'1 = Phi_Reasoners.asm_lr_simp_tac true ctxt'' 1 sequent
                    |> Seq.hd
                    (*|> @{print}*)
    in Phi_Sledgehammer_Solver.auto (SOME proof_id) (ctxt addsimps Expansion.simp_rules ctxt, sequent'1)
          |> (fn th => case Thm.major_prem_of th
                         of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Premise\<close> $ _ $ \<^Const>\<open>True\<close>) =>
                              @{thm' Premise_True} RS th
                          | \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> =>
                              @{thm' TrueI} RS th
                          | _ => th)
  end
     (*| _ => sequent*)

(* The Framework *)

(*quants: an array telling how to interpret the quantified variables in the first antecedent of the rule.
  It is used in generating the induction rule.
  quants[i] = 0 means interpret the variable as the abstract object
  quants[i] = i means interpret the variable as the i-th parameter of the \<phi>-type
  quants[i] = ~1 means interpret it as a fixed variable
  Note the quants is reversed against the quantified variables*)
fun deriving_framework (name,parse_hint,extract_oprs_from_hint,guess_property,rule,subgoal_reasonings,solver,simp)
                      (phi0 : phi_type) hint ctxt0 =
  let (*val (inst,inst',phi,ctxt01) = fix_phi_type true phi0 ctxt0*)
      (*val ((x_term0, T_term0), ctxt01) = fix_phi_term_params (#term phi0) ctxt0*)
   in (case hint of SOME H0 =>
              let (*val idx = Phi_Type_Algebra.phi_maxidx_of phi0 ~1 + 1
                  val H = Logic.incr_indexes ([],[],idx) H0*)
                  val thy = Proof_Context.theory_of ctxt0
                  val (typ_of_phi0, parameters0, H01) = parse_hint ctxt0 phi0 H0

                  val (inst0, ctxt) = Variable.import_inst true [H01] ctxt0
                  val typ_of_phi = Term_Subst.instantiateT (fst inst0) typ_of_phi0
                  val parameters = map (Option.map (Term_Subst.instantiate inst0)) parameters0
                  val H = Term_Subst.instantiate inst0 H01

                  val inst = (Sign.typ_match thy (Term.fastype_of (#term phi0), typ_of_phi) Vartab.empty
                              handle Type.TYPE_MATCH => raise Automation_Fail (fn () =>
                                        let open Pretty in
                                          [str "Invalid Hint", Syntax.pretty_term ctxt H]
                                        end))
                          |> Phi_Help.subst_tyenv
                          |> Phi_Help.certify_tyvars (Context.Proof ctxt)

                  val phi = Phi_Type_Algebra.instantiate_phi (inst, Vars.empty) phi0

                  val oprs = extract_oprs_from_hint (extract_hhf H)
                  val ctxt = load_simpset oprs ctxt

               in Seq.single (Logic.strip_imp_prems H, Logic.strip_imp_concl H, parameters, phi, ctxt)
              end
           | _ => guess_property phi0 ctxt0)
   |> Seq.map (fn (ants01, property01, phi_typ_parameters01, phi01, ctxt01) => 
  let val (ants, property, phi_typ_parameters, phi, ctxt) =
        if is_phi_type_fixed phi01
        then (ants01, property01, phi_typ_parameters01, phi01, ctxt01)
        else let val (inst, phi, ctxt) = fix_phi_type true phi01 ctxt01
                 val subst = Term_Subst.instantiate (Phi_Help.uncertify_vars inst)
              in (map subst ants01, subst property01, map (Option.map subst) phi_typ_parameters01, phi, ctxt)
             end
      val phityp_arity = length (Term.binder_types (Term.fastype_of (#term phi)))
      val _ = if phityp_arity = length phi_typ_parameters then ()
              else error "Bad Argument: phi_typ_parameters"

      fun chk_ant (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = X
        | chk_ant X = case Term.fastype_of X
                        of \<^Type>\<open>bool\<close> => X
                         | _ => error ("Fail to atomize an antecedent:\n" ^
                                       Syntax.string_of_term ctxt X)
      val ant = map (chk_ant o Object_Logic.atomize_term ctxt) ants
             |> Phi_Help.list_mk_conj
      val inst_rule = (Pattern.match (Proof_Context.theory_of ctxt) (Thm.concl_of rule, property)
                                     (Vartab.empty, Vartab.empty)
                       handle Pattern.MATCH =>
                          raise Automation_Fail (let open Pretty in fn () =>
                                  [str "The given property does not match the reasoning rule",
                                   item [str "property: ", Syntax.pretty_term ctxt property],
                                   item [str "rule: ", Syntax.pretty_term ctxt (Thm.concl_of rule)]]
                            end))
                   |> apsnd (Vartab.update_new (("Ant",0), (\<^typ>\<open>bool\<close>, ant)))
                   |> Phi_Help.subst_env
                   |> Phi_Help.certify_vars (Context.Proof ctxt)
      val rule' = Thm.instantiate inst_rule rule
      
      fun apply_induction NONE rule' = rule'
        | apply_induction (SOME (quants, ind_conv)) rule' =
            let val free_tabel = Symtab.build (fold_index (fn (i, SOME (Free (N,_))) => Symtab.update_new (N,i)
                                                            | (_, SOME (Bound _)) => I
                                                            | (_, NONE) => I
                                                            | _ => I)
                                                          phi_typ_parameters)
                fun mk_ind_prop lev lambs (X $ Y) = mk_ind_prop lev lambs X $ mk_ind_prop lev lambs Y
                  | mk_ind_prop lev lambs (Bound i) =
                      if i < lev then Bound i else
                     (case try List.nth (quants, i-lev)
                        of NONE => error "The rule contains unspecified quantified variable"
                         | SOME j => if j = ~1
                                     then (case List.nth (lambs, i) of (N,T) => Var((N,1),T)) (*the ind rule is zero-indexed*)
                                     else Bound (lev+j))
                  | mk_ind_prop lev lambs (Abs (N,T,X)) =
                        Abs (N,T, mk_ind_prop (lev+1) ((N,T)::lambs) X)
                  | mk_ind_prop lev _ (Free (N,T)) =
                     (case Symtab.lookup free_tabel N
                        of SOME i => Bound (lev + i)
                         | NONE => Free (N,T))
                  | mk_ind_prop _ _ X = X
          
                val (lambs, _, rule_concl) = Phi_Help.strip_meta_hhf (Phi_Help.leading_antecedent' rule')
                val ind_prop = mk_ind_prop 0 (rev lambs) (HOLogic.dest_Trueprop rule_concl)
                val ind = Phi_Type_Algebra.mk_ind_dest_ToA ctxt phi (K ind_prop)
          
                val ((inst,[rule't]), ctxt't) = Variable.import true [rule'] ctxt
                val ind't = Thm.instantiate inst ind
             in (ind't RS Goal.protect 1 rule't)
             |> ind_conv ctxt phi
             |> Goal.conclude
             |> singleton (Variable.export ctxt't ctxt) 
            end

      val rule'3 = fold (fn (ind_config,reasoning) => fn rule' =>
              reasoning phi ctxt (apply_induction ind_config rule')
            ) subgoal_reasonings rule'

      val rule'4 =(case solver (phi, ctxt, rule'3)
                     of SOME ret => ret
                      | NONE => oblg_solver (#proof_id phi ^ "/" ^ name) ctxt rule'3)
                |> simp (phi, Simps.enhance ctxt)
                |> Conv.fconv_rule (
                      Phi_Conv.expand_aggregated_imps_hol 
                          (Phi_Conv.hol_alls_to_meta_alls (K Conv.all_conv) ctxt)
                          Conv.all_conv)
                |> singleton (Proof_Context.export ctxt ctxt0)

   in rule'4
   |> Thm.solve_constraints
   |> Phi_Help.unique_flexflex ctxt0
  end)
  end

(* Default Hint Parser *)

fun malformed_hint ctxt hint msg =
  raise Automation_Fail (let open Pretty in fn () =>
          [str "Malformed Hint",
           Syntax.pretty_term ctxt hint] @
          msg ()
    end)


type hint = term
type parse_hint = Proof.context -> phi_type -> hint -> typ (*of the phi-typ const*) * induct_inst_params * hint

fun parse_parameters_of_phi_type phity =
  map SOME (rev (snd (Term.strip_comb (Phi_Help.beta_eta_contract_term phity))))

fun parse_hint extract_phityp ctxt phi hint =
  let val phity = (case extract_phityp (extract_hhf hint)
                     of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T => T $ x
                      | X => X)
                  handle Match => malformed_hint ctxt hint (K [])
      val (phiconst, params) =
              fold (fn _ => fn X => X $ Term.dummy) (Term.binder_types (Term.fastype_of phity)) phity
           |> Phi_Help.beta_eta_contract_term
           |> Term.strip_comb
           |> apsnd (rev #> map (fn tm => if tm = Term.dummy then NONE else SOME tm))
      val _ = if is_phi_term phi phiconst then ()
              else malformed_hint ctxt hint (fn () => let open Pretty in
                  [block (text "It specifies a irrelavent \<phi>-type" @
                          [brk 1, Syntax.pretty_term ctxt phiconst, brk 1] @
                          text "instead of the defining \<phi>-type.")]
                end)
   in (Term.fastype_of phiconst, params, hint)
  end


(* Default Conversion of the Induction Rule *)

type ind_conv = (Proof.context -> Phi_Type_Algebra.phi_type -> thm -> thm)

fun default_ind_conv (conv_IH, conv_CL) ctxt (phi:phi_type) =
  Conv.fconv_rule (Phi_Conv.hhf_conv (fn ctxt => fn ctm =>
    case Logic.strip_assums_concl (Thm.term_of ctm)
      of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ (\<^Const>\<open>\<phi>TA_ind_target\<close> $ _)) => (
            Phi_Conv.hhf_conv (fn ctxt => fn ctm =>
              case Thm.term_of ctm
                of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ (\<^Const>\<open>\<phi>TA_ind_target\<close> $ _))
                    => conv_IH ctxt phi ctm
                 | _ => Conv.all_conv ctm
            ) (fn ctxt => fn ctm =>
              case Thm.term_of ctm
                of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ (\<^Const>\<open>\<phi>TA_ind_target\<close> $ _))
                    => conv_CL ctxt phi ctm
                 | _ => Conv.all_conv ctm)
            ctxt ctm)
       | _ => Conv.all_conv ctm
    ) (K Conv.all_conv) ctxt)

(* Abstract Constraint Guided Reasoning *)

fun is_TA_IH_ToA (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ \<^Const>\<open>\<phi>TA_conditioned_ToA_template\<close>)) = true
  | is_TA_IH_ToA _ = false

fun timed_chop timeout n xq =
  if n <= (0 : int) then ([], xq)
  else
    (case Timeout.apply timeout Seq.pull xq of
      NONE => ([], xq)
    | SOME (x, xq') => apfst (Basics.cons x) (timed_chop timeout (n - 1) xq'))
    handle Timeout.TIMEOUT _ => ([], Seq.empty)

fun instantiate_ToA (pure_info,ctxt) ToA =
  case Thm.concl_of ToA
    of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ \<^Const>\<open>\<phi>TA_conditioned_ToA_template\<close>)
        => let
          val (i,target_prem) =
                case get_index (fn ctm =>
                        if Phi_Syntax.is_action_of (fn Const (\<^const_name>\<open>\<phi>TA_pure_facts\<close>, _) => true
                                                     | _ => false)
                           (Thm.term_of ctm)
                        then SOME ctm
                        else NONE)
                      (Thm.cprems_of ToA)
                  of SOME xx => xx
                   | NONE => error "Bad Configuration: an induction hypothesis is declared with \<phi>TA_conditioned_ToA_template\
                                   \ but has no antecedent tagged with \<phi>TA_pure_facts"
          (* Gosh, I forget why I trace those instantiations...
          val vars = Drule.add_vars_cterm target_prem Cterms.empty
          val prem' = Cterms.fold ( curry Conjunction.mk_conjunction
                                  o Thm.cprop_of o Drule.mk_term
                                  o fst) vars target_prem*)
          fun elim_conj ret thm =
                case Thm.prop_of thm
                  of Const(\<^const_name>\<open>Pure.conjunction\<close>, _) $ _ $ _ =>
                        let val (L,R) = Conjunction.elim thm
                         in elim_conj (L::ret) R
                        end
                   | _ => (ret, thm)
          fun simplify_distinct ctxt ths =
                map (elim_conj []) ths
                  |> distinct (fn ((thsa,_),(thsb,_)) =>
                                  eq_list (Thm.equiv_thm (Proof_Context.theory_of ctxt)) (thsa, thsb))
                  |> map snd
          val insts = Goal.init target_prem
                  |>((*REPEAT_DETERM_N (Cterms.size vars) (
                        resolve_tac ctxt [Conjunction.conjunctionI] 1 THEN
                        resolve_tac ctxt [Drule.termI] 1)
                     THEN*) resolve_tac ctxt @{thms' Action_Tag_I} 1
                     THEN Method.insert_tac ctxt [pure_info] 1)
                  |> Seq.hd
                  (*|> @{print}
                  |> Simplifier.full_simp_tac (Expansion.equip ctxt') 1 |> Seq.hd
                  |> @{print} *)
                  |> Clasimp.fast_force_tac (Expansion.equip ctxt) 1
                  |> timed_chop (Time.fromMilliseconds 50) 21 |> fst
                  |> map Goal.conclude
                  |> simplify_distinct ctxt
                  |> maps (fn th => let val th' = th RSN (i+1,ToA)
                                        val th2 = th' RS' (ctxt, @{thm' Action_Tag_D})
                                        (*fun rewr_pat (\<^Const>\<open>Trueprop\<close> $ (\<^Const_>\<open>Transformation ty\<close> $ X $ Y $ _)) =
                                              (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Transformation ty\<close> $ X $ Y
                                                  $ Var(("P", Term.maxidx_term X (Term.maxidx_term Y ~1) + 1), \<^Type>\<open>bool\<close>))) *)
                                        val ToA1 = th2 RS' (ctxt, @{thm' mk_ToA_rule})
                                        val ToA2 = th2 RS' (ctxt, @{thm' mk_ToA_rule'})
                                     in [ToA1, ToA2]
                                    end)
          val _ = if null insts 
                  then report_potential_failure_reason (let open Pretty in [
                          fn () => chunks [para "I fail to derive any instantiation of the induction-hypothetic reasoning rule",
                                           indent 2 (Thm.pretty_thm ctxt ToA),
                                           para "because I fail to derive its premise",
                                           indent 2 (Syntax.pretty_term ctxt (Thm.term_of target_prem)),
                                           para "from the contextual condition",
                                           indent 2 (Thm.pretty_thm ctxt pure_info),
                                           para "Perhaps, the propositions are not sufficiently simplified. You may\
                                                \ need to add necessary rules by declaring [\<phi>constraint_expansion], or \
                                                \even configure the BNF settings by ML \<open>BNF_FP_Sugar_More.add_fp_more\<close> "]
                       ] end)
                  else if length insts > 20
                  then warning "I find more than 20 instantiations which is very abnormal.\
                               \ I only take the first 20 instantiations."
                  else ()
         in insts
        end
     | _ => []

fun extract_rewr ctxt th =
  case Thm.prop_of th
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _
          $ (Const(\<^const_name>\<open>HOL.eq\<close>, \<^Type>\<open>fun Ty _\<close>) $ _ $ _)) =>
        if can Phi_Syntax.dest_phi_type_ty Ty
        then SOME ((th RS' (ctxt, @{thm' Premise_D})) RS' (ctxt, @{thm' eq_reflection}))
        else NONE
     | _ => NONE

fun varify_subgoal mk ctxt focus sequent =
  let val LHS = Thm.major_prem_of sequent
   in case mk focus LHS of SOME (LHSS, gen_RHSS) =>
      let val is_schm_LHSS = map (fn tm =>
                Vars.exists (fn (_, ctm) => tm aconv Thm.term_of ctm)
                            (snd (#schematics focus))) LHSS
          val real_LHSS = map_filter (fn (b,c) => if b then SOME c else NONE) (is_schm_LHSS ~~ LHSS)
          val rvar_names = Name.invent (Variable.names_of ctxt) "schm" (length real_LHSS)
          val ctxt' = Variable.add_fixes_direct rvar_names ctxt
          val rvars = map2 (fn N => fn T => Free (N, Term.fastype_of T)) rvar_names real_LHSS
          fun mk_fake_rvars (b::bs) l1 (o2::l2) = if b then hd l1 :: mk_fake_rvars bs (tl l1) l2
                                                       else    o2 :: mk_fake_rvars bs l1 l2
            | mk_fake_rvars [] _ _ = []
          val fake_rvars = mk_fake_rvars is_schm_LHSS rvars LHSS
          val eqs = map2 (fn l => fn r => \<^Const>\<open>Pure.eq \<open>Term.fastype_of r\<close>\<close> $ l $ r) real_LHSS rvars
          val rule = \<^Const>\<open>Pure.imp\<close> $ gen_RHSS fake_rvars $ LHS
                  |> fold (fn eq => fn X => \<^Const>\<open>Pure.imp\<close> $ eq $ X) eqs
                  |> Thm.cterm_of ctxt
                  |> Goal.init
                  |> Raw_Simplifier.rewrite_goals_rule ctxt []
                  |> Thm.assumption (SOME ctxt) 1
                  |> Seq.hd
                  |> Goal.conclude
                  |> Thm.permute_prems 0 ~1
                  |> singleton (Variable.export ctxt' ctxt)
      in Goal.protect 1 (rule RS sequent)
     end
        | NONE => Goal.protect 1 sequent
  end

val varify_subgoal_finale0 = Goal.conclude

fun varify_subgoal_finale sequent =
  Phi_Help.repeat (fn th => @{thm' Pure.reflexive} RS th) sequent

fun varify_all_vars (focus : Subgoal.focus) tm =
  let val frees = snd (#schematics focus)
               |> Vars.dest
               |> map (Thm.term_of o snd)
   in SOME (frees, fn frees' =>
              Term_Subst.instantiate_frees (TFrees.empty,
                                            Frees.make (map2 (fn Free a => fn b => (a,b)) frees frees')) tm)
  end

type reasoning = Proof.context -> thm -> thm
type subgoal_configure = (int list (*quant_interps*) * ind_conv) option (*If not given, no induction will be applied*)
                       * (Phi_Type_Algebra.phi_type -> reasoning)
type varifier = Subgoal.focus -> term -> (term list * (term list -> term)) option
type reasoner = Proof.context -> thm -> thm
type extract_pure_prems = Proof.context -> thm -> thm list
type reasoning_configure = Subgoal.focus * thm -> thm list * Proof.context -> thm list * thm list * thm list * Proof.context

fun default_reasoning_configure extractions
                                (focus:Subgoal.focus, lsequent) (local_prems,ctxt) =
  let val is_pure_fact = Phi_Syntax.is_action_of (
                          fn Const(\<^const_name>\<open>\<phi>TA_pure_facts\<close>, _) => true
                           | _ => false
                        ) o Thm.concl_of
      val is_ToA_template = Phi_Syntax.is_action_of (
                          fn Const(\<^const_name>\<open>\<phi>TA_conditioned_ToA_template\<close>, _) => true
                           | _ => false
                        ) o Thm.concl_of
      val pure_facts = filter is_pure_fact local_prems
                    |> map (fn th => th RS' (ctxt, @{thm' Action_Tag_D}))
      val ToAs = filter is_ToA_template local_prems
              |> maps (instantiate_ToA (Thm.transfer' ctxt (Phi_Help.conj_intros ctxt pure_facts), ctxt))
      val pure_fact' = map (fn th => th RS' (ctxt, @{thm' Premise_I[where mode=MODE_SIMP]})) pure_facts

      val local_prems = pure_fact' @ filter_out (fn x => is_pure_fact x orelse is_ToA_template x) local_prems

      val extract_prem = Phi_Reasoners.extract_prem (
              Phi_Reasoners.add_premise_extractions extractions (Context.Proof ctxt)) false
      val prem_ants = map_filter extract_prem local_prems
(*maps (fn th =>
            case extract_prems ctxt th
              of [] => if is_real_Premise (Thm.concl_of th) then [th] else []
               | some => some
            ) local_prems*)
      val rewrs = map_filter (extract_rewr ctxt) local_prems
      val ants = filter_out (Phi_Reasoners.is_syntactic_premise o Thm.concl_of) local_prems
   in (prem_ants, rewrs, ToAs @ ants, ctxt)
  end

fun default_reasoning always_diverge_disj configure varify reasoner =
let fun has_disj_ants th =
      let val no_schematic_in_concl = Thm.maxidx_of_cterm (Thm.cconcl_of th) = ~1
          fun give rule =
                if always_diverge_disj orelse no_schematic_in_concl
                then SOME rule else NONE
          fun chk (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk X
            | chk (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ _ $ _) = give @{thm' disjE}
            | chk (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ _ $ _) $ _)
                = give @{lemma \<open> P \<or> Q @action A \<Longrightarrow> (P @action A \<Longrightarrow> C) \<Longrightarrow> (Q @action A \<Longrightarrow> C) \<Longrightarrow> C \<close>
                            by (unfold Action_Tag_def Orelse_shortcut_def, blast)}
            | chk (Const(\<^const_name>\<open>Orelse_shortcut\<close>, _) $ _ $ _)
                = give @{thm' disjE[folded Orelse_shortcut_def]}
            | chk (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ (Const(\<^const_name>\<open>Orelse_shortcut\<close>, _) $ _ $ _) $ _)
                = give @{lemma \<open> P \<or>\<^sub>c\<^sub>u\<^sub>t Q @action A \<Longrightarrow> (P @action A \<Longrightarrow> C) \<Longrightarrow> (Q @action A \<Longrightarrow> C) \<Longrightarrow> C \<close>
                            by (unfold Action_Tag_def Orelse_shortcut_def, blast)}
            | chk _ = NONE
       in get_first chk (#2 (Phi_Help.strip_meta_hhf (fst (Logic.dest_implies (Thm.prop_of th)))))
      end

fun reasoning ctxt0 sequent0 =
  case Thm.major_prem_of sequent0
    of _ (*Trueprop*) $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => @{thm' \<r>Success_I} RS sequent0
     | _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =>
              reasoning ctxt0 (@{thm' allI} RS sequent0)
     | _ =>
  case has_disj_ants sequent0
    of SOME erule =>
       Seq.hd (Thm.biresolution (SOME ctxt0) true [(true, erule)] 1 sequent0)
        |> reasoning ctxt0
    | _ => let
      val sequent = sequent0
                 (*|> (fn th => @{thm' impI} RS th
                              handle THM _ => Method.insert_tac ctxt0 [Thm.transfer' ctxt0 @{thm' TrueI}] 1 th
                                           |> Seq.hd)*)
      val (focus, lsequent'0) = Subgoal.focus ctxt0 1 NONE sequent
      val ctxt = #context focus
      val lsequent = varify_subgoal varify ctxt focus lsequent'0

      val is_out_ant = Phi_Syntax.is_action_of (
                          fn Const(\<^const_name>\<open>\<phi>TA_ANT\<close>, _) => true
                           | _ => false
                        ) o Thm.concl_of
      val out_ants = filter is_out_ant (#prems focus)
      val local_prems' = filter_out is_out_ant (#prems focus)

      fun elim_out_ants th =
        case get_index (fn P => find_first (fn A => P aconv (Thm.prop_of A)) out_ants) (Thm.prems_of th)
          of SOME (i, A) => Seq.hd (Thm.biresolution NONE true [(false, A)] (i+1) th)
                              |> elim_out_ants
           | NONE => th
      val local_prems'1 = map elim_out_ants local_prems'

      fun pass_out_ant ant = (ant RS' (ctxt, @{thm' Action_Tag_D}))
            |> Phi_Help.conj_elims
            |> map ( Thm.forall_elim_vars (Thm.maxidx_of lsequent)
                   o Phi_Help.repeat (fn th => th RS' (ctxt, @{thm' spec})))

      fun pass_prem th =
        case Thm.concl_of th
          of Const(\<^const_name>\<open>Pure.conjunction\<close>, _) $ _ $ _ =>
              maps pass_prem [th RS' (ctxt, @{thm' Pure.conjunctionD1}),
                              th RS' (ctxt, @{thm' Pure.conjunctionD2})]
           | _ => [th]

      val local_prems = (maps pass_out_ant out_ants @ local_prems'1)
                     |> maps pass_prem

      val (prem_ants, rewrs, reasoner_ants', ctxt) = configure (focus, lsequent) (local_prems, ctxt)
      val reasoner_ants = reasoner_ants'
            |> map ( Object_Logic.rulify ctxt
                  #> Simplifier.rewrite_rule ctxt rewrs
                  #> Phi_Help.instantiate_higher_order_schematic_var ~2 ctxt )

      val ctxt'' = ctxt
            |> Context.proof_map (Phi_Reasoner.add_rules (
                  map (fn rule => ([rule], Position.none, Phi_Reasoner.NORMAL_MODE, 200, [], [], NONE)) reasoner_ants)
            (* #> Phi_Reasoner.add_rules (map (fn (pat,rule) =>
                    ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [(pat,NONE)], [], NONE)) ToAs) *))

      val lsequent' = lsequent
                    |> Simplifier.rewrite_goals_rule ctxt rewrs
                    |> ALLGOALS (Method.insert_tac ctxt'' prem_ants)
                    |> Seq.hd
                    |> reasoner ctxt''
                    |> varify_subgoal_finale0

      (*val lsequent'' = fold PLPR_Syntax.provide_premise_condition prem_ants lsequent'*)

   in Subgoal.retrofit ctxt'' ctxt0 (#params focus) (#asms focus) 1 lsequent' sequent
   |> Seq.hd
   |> Phi_Reasoners.defer_obligation_tac (false, true, ~1) ctxt
   |> Seq.hd
   |> varify_subgoal_finale
   |> reasoning ctxt
  end
in fn ctxt => fn th => th
    |> Simplifier.norm_hhf ctxt
    |> Conv.gconv_rule (Simplifier.full_rewrite (
          clear_simpset ctxt addsimps
            (@{thms' HOL.simp_thms(31)[folded atomize_eq]
                   HOL.simp_thms(31)[folded atomize_eq Orelse_shortcut_def]}
           @ @{lemma \<open>P \<or> FAIL text \<equiv> P\<close> \<open>P \<or>\<^sub>c\<^sub>u\<^sub>t FAIL text \<equiv> P\<close>
                     \<open>P \<or> TRACE_FAIL text \<equiv> P\<close> \<open>P \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL text \<equiv> P\<close>
                  by (unfold FAIL_def Orelse_shortcut_def TRACE_FAIL_def, simp_all)})
       )) 1
    |> reasoning (Config.map Phi_Reasoner.trace (fn i=>i-1) ctxt)
end

fun chk_unfolded ctxt (phi : phi_type) term =
  let val (N,_) = raw_term_name_typ (#term phi)
      fun is_atom (Bound _) = true
        | is_atom (Free _) = true
        | is_atom (Var _) = true
        | is_atom _ = false
      fun chk (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = chk X
        | chk (Abs(_,_,X)) = chk X
        | chk (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T) = is_atom x andalso chk T
        | chk (Const(\<^const_name>\<open>\<phi>Auto_Prod\<close>, _) $ A $ B) = chk A andalso chk B
        | chk (Const(N',_)) = N = N'
        | chk (Free(N',_)) = N = N'
        | chk (X $ _) = chk X
        | chk _ = false
   in if chk term
      then report_potential_failure_reason (let open Pretty in [fn () => 
              chunks [str "The phi-type is not unfolded by simplification and inductive destruction.",
                      Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt term]
            ] end)
      else ()
  end

fun chk_unfolded' ctxt = chk_unfolded (Context.Proof ctxt)

fun conv_chk_unfolded (phi : phi_type) ctxt ctm =
      (chk_unfolded' ctxt phi (Thm.term_of ctm); Conv.all_conv ctm)

fun exhaustive_PLPR_reasoner num chk_unfolds ctxt sequent =
  let fun chk (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = chk X
        | chk X = let val (_, args) = Term.strip_comb X
                      fun app_index _ [] = ()
                        | app_index i (h::L) = (chk_unfolds i h ; app_index (i+1) L)
                   in app_index 0 args
                  end
   in chk (Thm.major_prem_of sequent) ;
   case PLPR_Exhaustive.reason_exhaustively num (ctxt, sequent)
     of SOME th => th
      | NONE => raise Automation_Fail (fn () => [Pretty.str "\<phi>-LPR reasoning fails"])
  end

fun exhaustive_PLPR_reasoner_by_rule rule chk_unfolds ctxt sequent =
  exhaustive_PLPR_reasoner (SOME (Thm.nprems_of rule)) chk_unfolds ctxt
                           (rule RS sequent)

(** Other Tools **)

fun make_forall_quantified_property mk phi =
  let val (rev_args_ty, x_ty, m_ty) = dest_parameterized_phi_ty (Term.fastype_of phi)
      val arity = length rev_args_ty
      val T = fold_index (fn (i,_) => fn X => X $ Bound (arity - i)) rev_args_ty phi
   in (HOLogic.all_const x_ty $ Abs ("x", x_ty, mk (x_ty, m_ty, Bound 0, T)))
   |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs ("a", ty, X)) rev_args_ty
  end

fun make_forall_quantified_property_for_parameters_of_a_phi_type mk (F $ T) =
     (case try (make_forall_quantified_property mk) T
        of SOME ret => ret :: make_forall_quantified_property_for_parameters_of_a_phi_type mk F
         | NONE => make_forall_quantified_property_for_parameters_of_a_phi_type mk F)
  | make_forall_quantified_property_for_parameters_of_a_phi_type _ _ = []

fun chk_abstract_object_quantified get_x ctxt hint =
  let fun get_x' (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = get_x' X
        | get_x' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = get_x' X
        | get_x' (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = get_x' X
        | get_x' (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = get_x' X
        | get_x' (Abs(_, _, X)) = get_x' X
        | get_x' X = get_x X

      fun err (N,Ty,v) hint = let open Pretty in
          raise Automation_Fail (fn () =>
          case Logic.strip_assums_concl hint
            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
                    [para "The abstract object must be universally quantified, e.g.,",
                     Syntax.pretty_term ctxt (\<^Const>\<open>Trueprop\<close> $
                        (HOLogic.all_const Ty $ Abs(N,Ty, Phi_Help.abstract_over (v, X))))]
             | _ => [para "The abstract object must be universally quantified"]
          )
        end
                 
   in case get_x' hint
   of SOME (X as Free (N,Ty)) => err (N,Ty,X) hint
    | SOME (X as Var ((N,_),Ty)) => err (N,Ty,X) hint
    | SOME (Bound _) => hint
    | NONE => hint
  end


fun lift_types_sort thy typ_sorts =
  Phi_Help.lift_types_sort thy typ_sorts
  handle Phi_Help.LIFT_FAIL (ty, sort) => raise Automation_Fail (let open Pretty in fn () =>
    [paragraph (text "Fail to constrain type " @
                [brk 1, Syntax.pretty_typ_global thy ty, brk 1] @
                text "by sort" @
                [brk 1, Syntax.pretty_sort_global thy sort])]
    end)


(* (** Misc **)

fun conv_eq_imp ctxt ctm =
  (Conv.rewr_conv @{thm imp_ex[folded atomize_eq]} then_conv
   Phi_Conv.hol_all_conv (conv_eq_imp o snd) ctxt) ctm
  handle CTERM _ => Conv.all_conv ctm
       | THM _ => Conv.all_conv ctm *)

(* fun gen_identity_element is_left hints phi thy =
  case hints of [] => gen_id_ele is_left phi NONE thy

fun gen_identity_element is_left phi hints_thy =
  select_one_hint (if is_left then \<^const_name>\<open>Identity_Element\<^sub>I\<close>
                              else \<^const_name>\<open>Identity_Element\<^sub>E\<close>)
                  (gen_id_ele is_left phi)
                  hints_thy *)

(*
(*** Install Automation ***)

val _ = Theory.setup (
  Phi_Type_Algebra.define_deriver_global \<^binding>\<open>Identity_Element\<^sub>I\<close> {
      priority = 100,
      dependences = [],
      derive = accept_one "Identity_Element\<^sub>I" (gen_id_ele true)
    } #-> (fn name => Context.theory_map (
      Phi_Type_Algebra.bind_derivers_on_patterns [(\<^pattern_prop>\<open>Identity_Element\<^sub>I _ _\<close>, name)]))
)*)

(* val _ = Theory.setup (Context.theory_map (
   Phi_Type_Algebra.add_automation_on_def 100 (gen_identity_element true)
#> Phi_Type_Algebra.add_automation_on_def 101 (gen_identity_element false)
#> Phi_Type_Algebra.add_automation_on_def 105 gen_obj_equal
#> Phi_Type_Algebra.add_automation_on_def 110 gen_TF
#> Phi_Type_Algebra.add_automation_on_def 120 (gen_SH true)
#> Phi_Type_Algebra.add_automation_on_def 121 (gen_SH false)
)) *)

end