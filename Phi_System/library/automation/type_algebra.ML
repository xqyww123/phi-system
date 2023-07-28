signature PHI_TYPE_ALGEBRA_DERIVERS = sig

(*** A common framework to build derivers fast ***)

(** Component: unify_hint **)

type hint = term
type unify_hint = (Proof.context -> hint (*property*) -> term (*fixed term x*) * term (*fixed term T*) -> ctyp TVars.table * cterm Vars.table)
  (*Given the `hint` and the `x \<Ztypecolon> T` that will be used in the reasoning, unify them two *)

(* Common choices of the unification *)

val hint_unify_general : (hint -> term (*x*) * term (*T*) -> (term * term) list (*pairs to be unified*)) -> unify_hint
val hint_unify_by_type : (term -> term) (*f*) -> unify_hint
      (*use `f` to extract the \<phi>-type part of the (conclusion part of the) property, then
        do the usual unification with the `T`*)
val hint_unify_by_type_operator : (term -> term) (*f*) -> unify_hint
      (*The `T` is a combination of a \<phi>-type operator `F` and its parameter `T'`, i.e. `T \<equiv> F T'`.
        The `F` is the part really matters, so use `f` to extract the \<phi>-type operator part
        of the (conclusion part of the) property, then do the usual unification about the `F`*)

(** Component: guess_property **)

type guess_property =
        term (*x*) * term (*T*) * Phi_Type_Algebra.phi_type ->
        Proof.context ->
        (term list (*antecedents*) * term (*conclusion*) * term (*x'*) * term (*T'*)
          * Phi_Type_Algebra.phi_type (*instantiated*) * Proof.context ) Seq.seq

(*If user gives no hint, we need to guess the property to be reasoned.
  Given `x \<Ztypecolon> T`, `guess_property` may guess the abstract operator from the logic type of the abstract
  object (e.g. by Bounded Natural Functor) or by any other means. It can also instantiate any logic
  types in `x \<Ztypecolon> T` and the `phi_type`, maybe into a smaller sort (e.g. from \<open>?'a::type\<close> to \<open>?'a::one\<close>).
  It can return terms containing schematic variables, and there is no requirement on the index.
*)

(* Guess from BNF *)

val load_simpset : term list -> Proof.context -> Proof.context
        (*Given an operator like a relation mapper, predicate mapper, a set or any other thing,
          load the simplification settings relating to the BNFs of the operator*)

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

(** The framework **)

type ind_conv = (Proof.context -> Phi_Type_Algebra.phi_type -> thm -> thm)
type reasoning = Proof.context -> thm -> thm
type solver = Phi_Type_Algebra.phi_type * Proof.context * thm -> thm option

val mk_rule_by_guess_or_hint :
      string (*name of the proof cache, e.g. "/object_equive"*)
    * unify_hint
    * (term -> term list) (*extract_oprs_from_hint*)
    * guess_property
    * thm (*rule*) * int list (*quant_interps*)
    * ind_conv option (*If not given, no induction will be applied*)
    * (Phi_Type_Algebra.phi_type -> reasoning)
    * solver
    * (Phi_Type_Algebra.phi_type * Proof.context -> thm -> thm) (*final simplification*)
   -> Phi_Type_Algebra.phi_type -> term option -> Proof.context -> thm Seq.seq

(*Besides the parameters already explained above, `rule` is a PLPR sequent giving a scheme about
  how to derive the target property in detail. It is in the bellow form,
  ` <the leading antecedent is the one to which induction applies> \<Longrightarrow>
    <some optional antecedents, but no induction will be applied on them> \<Longrightarrow>
    \<r>Success (*terminates the deriving successfully*) \<Longrightarrow>
    \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True (*stores the generated proof obligations*) \<Longrightarrow>
    <derived property>`
  The leading antecedent can be universally quantified (by \<And>), the parameter `quant_interps` decides
    how to interpret the quantified variables. For the *reserved* ith variable,
    quant_interps[i] = 0 means to interpret the variable as the abstract object and therefore the
        induction can destruct it according to the induction rule in the phi_type
    quant_interps[i] = i means to interpret the variable as the i-th parameter of the \<phi>-type
    quant_interps[i] = ~1 means to interpret it as a fixed variable*)

(*extract_oprs_from_hint allows user to indicate what are the mapper, predicator or other operators in
  the given hint, so that we can load reasoning configures like simplification sets binding on the
  operators (e.g., the simplification rules of the related BNF)*)

(*`ind_conv` : any conversion on the induction rule. If not given, no induction will be applied.
   A default option is the bellow*)

val default_ind_conv : (Proof.context -> Phi_Type_Algebra.phi_type -> conv) (*converting induction hypotheses*) *
                       (Proof.context -> Phi_Type_Algebra.phi_type -> conv) (*converting subgoals of the induction*)
                    -> ind_conv

(*To use `default_ind_conv`, you must tag the leading antecedent of the `rule` by `\<phi>TA_ind_target`,
  or else `default_ind_conv` cannot find which one is the induction hypothesis,
  see @{thm \<phi>TA_SHz_rule} as an example.*)

(*The `solver` optionally solves the proof obligation. It can return NONE to fallback to the
    default Auto_Sledgehammer solver.

  If the abstract operators are given by the hint, the proof obligations should contain no
    undetermined schematic variable so Auto_Sledgehammer is good to deal with them.
  However if a deriver wants to infer the abstract operators when no hint is given, it can provide
    a solver to instantiates the schematic variables.
*)

val oblg_solver : string -> Proof.context -> thm -> thm (*the default Sledgehammer solver*)

(** Reasoning **)
(*`reasoning` specifies how to solve the induction goals in detail.*)

type varifier = Subgoal.focus -> term -> (term list * (term list -> term)) option
type extract_pure_prems = Proof.context -> thm -> thm list

type PLPR_reasoner = Proof.context -> thm -> thm
val gen_abstract_constraint_guided_reasoning :
        bool (*if it can split the goals when they contain HOL.disj in antecedents, no matter if the conclusion
               contains schematic variables. is false by default*) ->
        varifier -> extract_pure_prems -> PLPR_reasoner -> reasoning
  (*It is a general framework using \<phi>-LPR and Isar subgoal tool.
    Because it uses Isar subgoal, it fixes all schematic variables. Users may expect the reasoning
    to infer some schematic variables. If so, `varifier` is used.
    Given a term, `varifier` returns the subterms that should be schematic variables, and
                  a function substituting schematic variables for those subterms.*)

val PLPR_reasoner : int option -> PLPR_reasoner
val ToA_reasoner : Phi_Type_Algebra.phi_type -> PLPR_reasoner (*reason using NToA*)

val extract_pure_prem_by_RS : thm list (*RS rules*) -> extract_pure_prems

(** Other Misc Tools **)

exception Automation_Fail of string
structure Simps : SIMPSET (*The standard simpset for deriving*)

val accept : string (*name for printing*) ->
      (int -> hint option -> Phi_Type_Algebra.derive) ->
       hint list -> Phi_Type_Algebra.derive
val accept_one : string (*name for printing*) ->
      (hint option -> Phi_Type_Algebra.derive) ->
       hint list -> Phi_Type_Algebra.derive
    (*wraps and checks if the user gives at most one hint*)

val chk_unfolded : Phi_Type_Algebra.phi_type -> term -> unit
val conv_chk_unfolded : Phi_Type_Algebra.phi_type -> conv
      (*roughly check if a phi-type expression is expanded, and warn if not*)

val quantifies_abstract_object : (term -> term option) (*get the abstract object*) -> (term -> term)

end

(**** Implementation ****)

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra

type guess_property =
        term (*x*) * term (*T*) * Phi_Type_Algebra.phi_type ->
        Proof.context ->
        (term list * term * term * term * Phi_Type_Algebra.phi_type * Proof.context ) Seq.seq

(* fun reason_fail msg = (warning msg; raise Automation_Fail) *)

structure Simps = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>\<phi>constraint_expansion\<close>
  val comment = "Rules to expand constraints and conditions in \<phi>-type algebra automation"
)

(*structure Normalize_ToA = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>\<phi>type_algebra_normalize_ToA_ss\<close>
  val comment = "Internal simplification set to normalize ToA in \<phi>-type algebra automation"
)*)

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
   (*Normalize_ToA.map (fn ctxt =>
    (ctxt addsimprocs [\<^simproc>\<open>HOL.defined_Ex\<close>, \<^simproc>\<open>Set.defined_All\<close>, \<^simproc>\<open>ExSet_expand_quantifier\<close>,
                       \<^simproc>\<open>HOL.defined_All\<close>(*, eq_simproc*), \<^simproc>\<open>NO_MATCH\<close>])
      |> Simplifier.add_cong @{thm imp_cong[folded atomize_eq]}
      |> Simplifier.add_cong @{thm HOL.conj_cong})
#>*)
  Simps.map (fn ctxt =>
    (ctxt addsimprocs [\<^simproc>\<open>HOL.defined_Ex\<close>, \<^simproc>\<open>Set.defined_All\<close>, \<^simproc>\<open>ExSet_expand_quantifier\<close>,
                       \<^simproc>\<open>HOL.defined_All\<close>(*, eq_simproc*), \<^simproc>\<open>NO_MATCH\<close>])
      |> Simplifier.add_cong @{thm imp_cong[folded atomize_eq]}
      |> Simplifier.add_cong @{thm HOL.conj_cong})
))

(** Guess Abstract Operators from BNF **)

type quasi_BNF = {}
datatype eBNF = BNF of BNF_Def.bnf | qBNF of quasi_BNF

(* Library *)


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

fun fp_sugar_of ctxt bnf =
  case BNF_Def.T_of_bnf bnf
    of Type(N, _) => BNF_FP_Def_Sugar.fp_sugar_of ctxt N
     | _ => NONE

fun add_global_simps thms ctxt = ctxt
  |> Simps.map' (fn ctxt => ctxt addsimps thms)
  |> (fn ctxt => ctxt addsimps thms)

(* Set *)

fun load_set_ss bnf ctxt = ctxt
  |> Simps.map' (fn ctxt => ctxt addsimps ( eBNF_Info.simps_of_set_safe bnf
                                          @ eBNF_Info.simps_of_ctr_safe bnf))

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

fun load_predicate_ss bnf ctxt = ctxt
   |> Simps.map' (fn ctxt => ctxt addsimps ( eBNF_Info.simps_of_pred_safe bnf
                                           @ eBNF_Info.simps_of_ctr_safe bnf))
   |> add_global_simps (eBNF_Info.global_simps_of_pred_safe bnf)

val guess_predicate =
  let fun mk_term (ctxt, D, L, bnf) =
        let val ctxt' = load_predicate_ss bnf ctxt
         in Seq.single (eBNF_Info.mk_pred_of_bnf D L bnf, ctxt')
        end
      val is_live = K true
      fun mk_operator_for_dead ty ctxt = (Abs("", ty, \<^Const>\<open>True\<close>), ctxt)
      fun atom_opr ty ctxt = Seq.single (mk_operator_for_dead ty ctxt)
   in guess_operator mk_term is_live mk_operator_for_dead atom_opr
  end

(* Mapper *)

fun load_rel_mapper_ss bnf ctxt = ctxt
     |> Simps.map' (fn ctxt => ctxt addsimps ( eBNF_Info.simps_of_rel_safe bnf
                                             @ eBNF_Info.simps_of_map_safe bnf
                                             @ eBNF_Info.simps_of_ctr_safe bnf))
     |> add_global_simps (eBNF_Info.global_simps_of_rel_safe bnf)

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
        let val ctxt' = load_rel_mapper_ss bnf ctxt
         in Seq.single (eBNF_Info.mk_rel_of_bnf D L (map target_ty L) bnf, ctxt')
        end
      val is_live = Term.exists_subtype (fn ty' => ty' = element_ty)
      fun mk_operator_for_dead typ ctxt = (\<^Const>\<open>HOL.eq typ\<close>, ctxt)
      fun mk_dead_opr ty ctxt = Seq.single (dead_opr (ty, target_ty ty), ctxt)
   in guess_operator mk_term is_live mk_operator_for_dead mk_dead_opr ctxt' known_rels ty
   |> Seq.map (fn (rel_term', ctxt) =>
        (Abs("", g_ty, Term.abstract_over (g_term, rel_term')), ctxt))
  end

fun load_mapper_ss bnf ctxt = ctxt
  |> Simps.map' (fn ctxt => ctxt addsimps ( eBNF_Info.simps_of_map_safe bnf
                                          @ eBNF_Info.simps_of_ctr_safe bnf)
                         |> add_global_simps (eBNF_Info.global_simps_of_map_safe bnf))

fun guess_func_mapper target_ty ctxt ty element_ty =
  let val [g'] = Name.invent (Variable.names_of ctxt) "g" 1
      val ([g], ctxt') = Variable.add_fixes [g'] ctxt
      val element_ty' = target_ty element_ty
      val g_ty = element_ty --> element_ty'
      val g_term = Free(g, g_ty)
      val known_mappers = [(element_ty, g_term)]
      fun mk_term (ctxt, D, L, bnf) =
        let val ctxt' = load_mapper_ss bnf ctxt
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
        let val ctxt' = load_predicate_ss bnf ctxt
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
                                     | NONE => raise Automation_Fail ("Fail to guess the zip operator for type " ^ Tname)
                    val zip = (if flag then BNF_FP_Sugar_More.mk_zip
                                       else BNF_FP_Sugar_More.mk_unzip) deads lives lives' fp_more
                    val ctxt'' = ctxt
                              |> Simps.map' (fn ctxt =>
                                    ctxt addsimps ((if flag then #zip_simps fp_more else #unzip_simps fp_more)
                                                @ eBNF_Info.simps_of_rel_safe bnf
                                                @ eBNF_Info.simps_of_map_safe bnf
                                                @ eBNF_Info.simps_of_ctr_safe bnf))
                              |> add_global_simps (eBNF_Info.global_simps_of_rel_safe bnf)
                    val (args, ctxt') = ctxt''
                          |> fold_map (guess_zip_guided flag (target,target'))
                                      (lives ~~ lives')
                    val map_tys = map (fn (_,z) => case Term.fastype_of z
                                                     of \<^Type>\<open>fun a b\<close> => (a,b)) args
                                |> split_list
                    val mp = eBNF_Info.mk_map_of_bnf deads (fst map_tys) (snd map_tys) bnf
                    val rl = eBNF_Info.mk_rel_of_bnf deads lives lives' bnf
                 in((Term.list_comb (rl, map fst args),
                     Abs("x", domain_type (Term.fastype_of zip),
                             if flag then Term.list_comb (mp, map snd args) $ (zip $ Bound 0)
                                     else zip $ (Term.list_comb (mp, map snd args) $ Bound 0))),
                    ctxt')
                end
              | _ => error "Internal bug #928dccd3-7497-4f2c-867c-4b7407fcfdef"
      else if not occur andalso not occur'
        then if T = T'
          then ((\<^Const>\<open>HOL.eq T\<close>, \<^Const>\<open>fst T T\<close>), ctxt)
          else error "Only the target can vary in guided guess_zip"
        else error "Internal bug #a1dd0817-f55a-468e-ba79-95183f145380"
  end

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
                   then SOME (load_rel_mapper_ss bnf ctxt)
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
            then SOME (load_set_ss bnf ctxt)
            else NONE)
  | load_set _ _ = NONE

fun load_predicate (CN, \<^Type>\<open>fun \<open>Type(N,_)\<close> \<^Type>\<open>bool\<close>\<close>) ctxt =
      eBNF_Info.get_bnf (Context.Proof ctxt) N
        |> Option.mapPartial (mp eBNF_Info.pred_of_bnf_safe)
        |> Option.mapPartial (fn (C, bnf) =>
            if const_eq CN C
            then SOME (load_predicate_ss bnf ctxt)
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
              then SOME (load_mapper_ss bnf ctxt)
              else load_map (CN, T) ctxt)
      else load_map (CN, T) ctxt
  | load_map (CN, \<^Type>\<open>fun \<^Type>\<open>fun _ _\<close> T\<close>) ctxt = load_map (CN, T) ctxt
  | load_map _ _ = NONE

fun load_zip (CN, \<^Type>\<open>fun \<open>Type(N,ts1)\<close> \<open>T2 as \<^Type>\<open>fun \<open>Type(N',ts2)\<close> \<open>Type(N'', ts3)\<close>\<close>\<close>\<close>) ctxt =
      let fun chk_ts (t1::ts1) (t2::ts2) (\<^Type>\<open>prod a b\<close>::ts3) =
                a = t1 andalso b = t2 andalso chk_ts ts1 ts2 ts3
            | chk_ts [] [] [] = true
            | chk_ts _ _ _ = false
       in if chk_ts ts1 ts2 ts3
          then case BNF_FP_Sugar_More.get_fp_more (Context.Proof ctxt) N
            of SOME fpm =>
                if const_eq CN (#zip fpm)
                then SOME (Simps.map' (fn ctxt =>
                              ctxt addsimps (#zip_simps fpm @ #unzip_simps fpm)
                           ) ctxt)
                else load_zip (CN, T2) ctxt
             | NONE => load_zip (CN, T2) ctxt
          else load_zip (CN, T2) ctxt
      end
  | load_zip (CN, \<^Type>\<open>fun _ T2\<close>) ctxt = load_zip (CN, T2) ctxt
  | load_zip _ _ = NONE

fun load_const C ctxt =
  the_default ctxt (get_first (fn ld => ld C ctxt) [load_rel, load_set, load_predicate, load_map])

val add_consts' = fold_aterms (fn Const c => insert (op = o apply2 fst) c | _ => I);
fun load_simpset tms ctxt = fold load_const (fold add_consts' tms []) ctxt



(** Select Hint **)

local open Pretty

fun err_derive prop_name msg has_hint =
      error ("Fail to derive the property " ^ prop_name ^
        (if msg = "" then "" else "\n" ^ msg) ^
        (if has_hint then ""
         else "\nThe guessed property may be wrong, and you may provide the \
              \desired property form by \<open>deriving \<open>the property you want\<close>\<close>."))

fun err_prove hint thy msg has_hint =
      error ("Fail to derive the given property:\n" ^
      Context.cases Syntax.string_of_term_global Syntax.string_of_term thy hint ^ "\n" ^
        (if msg = "" then "" else "\n" ^ msg) ^
        (if has_hint then ""
         else "\nThe guessed property may be wrong, and you may provide the \
              \desired property form by \<open>deriving \<open>the property you want\<close>\<close>."))

in

fun accept prop_name gen [] phityp thy = (gen 0 NONE phityp thy
         handle Automation_Fail msg => err_derive prop_name msg false)
  | accept _ gen Hs phityp thy = fold_index (fn (i, H) =>
            gen i (SOME H) phityp
            handle Automation_Fail msg => err_prove H thy msg true
         ) Hs thy

fun accept_one prop_name gen [] phityp thy = (gen NONE phityp thy
         handle Automation_Fail msg => err_derive prop_name msg false)
  | accept_one _ gen [H] phityp thy = (gen (SOME H) phityp thy
         handle Automation_Fail msg => err_prove H thy msg true)
  | accept_one prop_name _ hints _ thy =
         error (string_of (chunks (
           block [str prop_name, str " only derives one reasoning rule, but multiple hints are given"] ::
           map (fn H => item [Context.cases Syntax.pretty_term_global Syntax.pretty_term thy H]) hints)))
        

end

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
        Phi_Sledgehammer_Solver.auto (SOME proof_id) (ctxt, sequent)
          |> (fn th => case Thm.major_prem_of th
                         of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Premise\<close> $ _ $ \<^Const>\<open>True\<close>) =>
                              @{thm' Premise_True} RS th
                          | \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> =>
                              @{thm' TrueI} RS th
                          | _ => th)
     (*| _ => sequent*)

(* The Framework *)

(*quants: an array telling how to interpret the quantified variables in the first antecedent of the rule.
  It is used in generating the induction rule.
  quants[i] = 0 means interpret the variable as the abstract object
  quants[i] = i means interpret the variable as the i-th parameter of the \<phi>-type
  quants[i] = ~1 means interpret it as a fixed variable
  Note the quants is reversed against the quantified variables*)
fun mk_rule_by_guess_or_hint (name,unify_hint,extract_oprs_from_hint,guess_property,rule,quants,ind_conv_opt,reasoning,solver,simp)
                             (phi0 : phi_type) hint ctxt0 =
  let (*val (inst,inst',phi,ctxt01) = fix_phi_type true phi0 ctxt0*)
      val ((x_term0, T_term0), ctxt01) = fix_phi_term_params (#term phi0) ctxt0
   in (case hint of SOME H0 =>
              let val idx = Phi_Type_Algebra.phi_maxidx_of phi0 ~1 + 1
                  val H = Logic.incr_indexes ([],[],idx) H0
                  val inst01 = unify_hint ctxt01 H (x_term0, T_term0)
                  val phi01 = Phi_Type_Algebra.instantiate_phi inst01 phi0
                  val (inst, phi, ctxt) = fix_phi_type true phi01 ctxt01
                  val subst = Term_Subst.instantiate (Phi_Help.uncertify_vars inst01)
                           #> Term_Subst.instantiate (Phi_Help.uncertify_vars inst)
                  val (x_term0', T_term0', H0') = (subst x_term0, subst T_term0, subst H)
                  val ([x_term, T_term, H''], ctxt) =
                          Variable.import_terms true [x_term0', T_term0', H0'] ctxt

                  fun extract_oprs_from_hint' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = extract_oprs_from_hint' X
                    | extract_oprs_from_hint' (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = extract_oprs_from_hint' X
                    | extract_oprs_from_hint' X = extract_oprs_from_hint X
                  val oprs = extract_oprs_from_hint' (Logic.strip_imp_concl H'')
                  val ctxt = load_simpset oprs ctxt

               in Seq.single (Logic.strip_imp_prems H'', Logic.strip_imp_concl H'',
                              x_term, T_term, phi, ctxt)
              end
           | _ => guess_property (x_term0, T_term0, phi0) ctxt01)
   |> Seq.map (fn (ants01, property01, x_term01, T_term01, phi01, ctxt01) => 
  let val (ants, property, x_term, T_term, phi, ctxt) =
        if is_phi_type_fixed phi01
        then (ants01, property01, x_term01, T_term01, phi01, ctxt01)
        else let val (inst, phi, ctxt) = fix_phi_type true phi01 ctxt01
                 val subst = Term_Subst.instantiate (Phi_Help.uncertify_vars inst)
              in (map subst ants01, subst property01, subst x_term01, subst T_term01, phi, ctxt)
             end
      fun chk_ant (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = X
        | chk_ant X = case Term.fastype_of X
                        of \<^Type>\<open>bool\<close> => X
                         | _ => error ("Fail to atomize an antecedent:\n" ^
                                       Syntax.string_of_term ctxt X)
      val ant = map (chk_ant o Object_Logic.atomize_term ctxt) ants
             |> Phi_Help.list_mk_conj
      val inst_rule = Pattern.match (Proof_Context.theory_of ctxt) (Thm.concl_of rule, property)
                                    (Vartab.empty, Vartab.empty)
                   |> apsnd (Vartab.update_new (("Ant",0), (\<^typ>\<open>bool\<close>, ant)))
                   |> Phi_Help.subst_env
                   |> Phi_Help.certify_vars (Context.Proof ctxt)
      val rule' = Thm.instantiate inst_rule rule
      
      val rule'2 =
            case ind_conv_opt
              of NONE => rule'
               | SOME ind_conv =>
            let fun mk_free_table i ret (X $ Free (N,_)) =
                      mk_free_table (i+1) (Symtab.update_new ((N,i)) ret) X
                  | mk_free_table _ ret _ = ret
                val free_tabel = mk_free_table 0 Symtab.empty (T_term $ x_term)
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
             in singleton (Variable.export ctxt't ctxt) (ind_conv ctxt phi (ind't RS rule't))
            end

      val rule'3 = reasoning phi ctxt rule'2
      val rule'4 =(case solver (phi, ctxt, rule'3)
                     of SOME ret => ret
                      | NONE => oblg_solver (#proof_id phi ^ "/" ^ name) ctxt rule'3)
                |> simp (phi,ctxt)
                |> Conv.fconv_rule (
                      Phi_Conv.expand_aggregated_imps_hol 
                          (Phi_Conv.hol_alls_to_meta_alls (K Conv.all_conv) ctxt)
                          Conv.all_conv)
                |> singleton (Proof_Context.export ctxt ctxt0)
   in Phi_Reasoner.info_pretty ctxt 0 (fn () => let open Pretty in
        block [str name, str " : ", Thm.pretty_thm ctxt rule'4]
      end) ;
      rule'4
  end)
  end

(* Default Hint Unifier *)

local
fun extract_hhf (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = extract_hhf X
  | extract_hhf (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = extract_hhf X
  | extract_hhf (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = extract_hhf X
  | extract_hhf X = Envir.beta_eta_contract X
in

type hint = term
type unify_hint = (Proof.context -> hint -> term * term -> ctyp TVars.table * cterm Vars.table)

fun hint_unify_general extract_pairs ctxt hint (x', T') =
  Unify.smash_unifiers (Context.Proof ctxt)
                       (extract_pairs hint (x', T'))
                       Envir.init
    |> Seq.chop 2
    |> (fn ([], _) => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
         | ([Envir.Envir x], _) => Phi_Help.norm_env (#tyenv x, #tenv x)
                                |> Phi_Help.certify_vars (Context.Proof ctxt)
         | _ => error ("Multi-unification in hint: " ^ Syntax.string_of_term ctxt hint))
  handle TERM _ => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
       | Match  => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
    
fun hint_unify_by_type extract_type = hint_unify_general (fn hint => fn (_, T') =>
      [(extract_type (extract_hhf hint), T')])

fun hint_unify_by_type_operator extract_type_operator = hint_unify_general (fn hint => fn (_, T') =>
      let val i = Term.maxidx_of_term hint + 1
          val hint_tyop = extract_type_operator (extract_hhf hint)
          val v_ty = Term.domain_type (Term.fastype_of hint_tyop)
       in [(hint_tyop $ Var(("v",i),v_ty), T')]
      end)

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

fun is_TA_IH_ToA (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ \<^Const>\<open>\<phi>TA_IH_ToA\<close>)) = true
  | is_TA_IH_ToA _ = false

fun timed_chop timeout n xq =
  if n <= (0 : int) then ([], xq)
  else
    (case Timeout.apply timeout Seq.pull xq of
      NONE => ([], xq)
    | SOME (x, xq') => apfst (Basics.cons x) (timed_chop timeout (n - 1) xq'))
    handle Timeout.TIMEOUT _ => ([], Seq.empty)

fun instantiate_ToA (Ant,pure_info,ctxt) ToA =
  case Thm.concl_of ToA
    of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Action_Tag\<close> $ _ $ \<^Const>\<open>\<phi>TA_IH_ToA\<close>)
        => let
          val ToA' = Ant RS (Thm.permute_prems 0 ~2 ToA)
          val (prem, _) = Thm.dest_implies (Thm.cprop_of ToA')
          val vars = Drule.add_vars_cterm prem Cterms.empty
          val prem' = Cterms.fold ( curry Conjunction.mk_conjunction
                                  o Thm.cprop_of o Drule.mk_term
                                  o fst) vars prem
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
          val insts = Goal.init prem'
                  |>(REPEAT_DETERM_N (Cterms.size vars) (
                        resolve_tac ctxt [Conjunction.conjunctionI] 1 THEN
                        resolve_tac ctxt [Drule.termI] 1)
                     THEN Method.insert_tac ctxt [pure_info] 1)
                  |> Seq.hd
                  (*|> @{print}
                  |> Simplifier.full_simp_tac (Simps.equip ctxt') 1 |> Seq.hd
                  |> @{print} *)
                  |> Clasimp.fast_force_tac (Simps.equip ctxt) 1
                  |> timed_chop (Time.fromMilliseconds 50) 21 |> fst
                  |> map Goal.conclude
                  |> simplify_distinct ctxt
                  |> maps (fn th => let val th' = th RS ToA'
                                        val th2 = th' RS' (ctxt, @{thm' Action_Tag_D})
                                        (*fun rewr_pat (\<^Const>\<open>Trueprop\<close> $ (\<^Const_>\<open>Transformation ty\<close> $ X $ Y $ _)) =
                                              (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Transformation ty\<close> $ X $ Y
                                                  $ Var(("P", Term.maxidx_term X (Term.maxidx_term Y ~1) + 1), \<^Type>\<open>bool\<close>))) *)
                                        val ToA1 = th2 RS' (ctxt, @{thm' mk_ToA_rule})
                                        val ToA2 = th2 RS' (ctxt, @{thm' mk_ToA_rule'})
                                     in [ToA1, ToA2]
                                    end)
          val _ = if length insts > 20
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
      in rule RS sequent
     end
        | NONE => sequent
  end

fun varify_subgoal_finale sequent =
  Phi_Help.repeat (fn th => @{thm' Pure.reflexive} RS th) sequent

type reasoning = Proof.context -> thm -> thm
type varifier = Subgoal.focus -> term -> (term list * (term list -> term)) option
type PLPR_reasoner = Proof.context -> thm -> thm
type extract_pure_prems = Proof.context -> thm -> thm list

fun gen_abstract_constraint_guided_reasoning always_diverge_disj varify extract_prems reasoner =
let fun has_disj_ants th =
          exists (fn Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ _ $ _) => true
                   | _ => false)
                 (#2 (Phi_Help.strip_meta_hhf (fst (Logic.dest_implies (Thm.prop_of th)))))
    fun no_schematic_in_concl th = Thm.maxidx_of_cterm (Thm.cconcl_of th) = ~1

  fun abstract_constraint_guided_reasoning ctxt0 sequent0 =
  case Thm.major_prem_of sequent0
    of _ (*Trueprop*) $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => @{thm' \<r>Success_I} RS sequent0
     | _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =>
              abstract_constraint_guided_reasoning ctxt0 (@{thm' allI} RS sequent0)
     | _ =>
  if has_disj_ants sequent0 andalso (always_diverge_disj orelse no_schematic_in_concl sequent0)
  then Seq.hd (Thm.biresolution (SOME ctxt0) true [(true, @{thm' disjE})] 1 sequent0)
    |> abstract_constraint_guided_reasoning ctxt0
  else let
      val sequent = sequent0
                 |> (fn th => @{thm' impI} RS th
                              handle THM _ => Method.insert_tac ctxt0 [Thm.transfer' ctxt0 @{thm' TrueI}] 1 th
                                           |> Seq.hd)
      val (focus, lsequent'0) = Subgoal.focus ctxt0 1 NONE sequent
      val ctxt = #context focus
      val lsequent = varify_subgoal varify ctxt focus lsequent'0

      val len = length (#prems focus)
      val [Ant, pure_info] = List.drop (#prems focus, len - 2)

      val ToAs = maps (instantiate_ToA (Ant,pure_info,ctxt)) (List.take (#prems focus, len - 2))

      fun pass_conj_ants ant = ant
            |> Phi_Help.conj_elims ctxt
            |> map ( Thm.forall_elim_vars (Thm.maxidx_of lsequent)
                   o Phi_Help.repeat (fn th => th RS' (ctxt, @{thm' spec})))
      val ant'0 = List.nth (#prems focus, len - 2)
      fun pass_ind_ants ant =
        case Thm.prop_of ant
          of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ A $ _ =>
              if A aconv (Thm.prop_of ant'0)
              then ant'0 RS ant
              else ant
           | _ => ant
      val ants'1 = pass_conj_ants ant'0
                 @ map pass_ind_ants (List.take (#prems focus, len - 2))
      fun is_real_Premise (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_real_Premise X
        | is_real_Premise (Const(\<^const_name>\<open>All\<close>, _) $ X) = is_real_Premise X
        | is_real_Premise (Abs (_,_,X)) = is_real_Premise X
        | is_real_Premise (Const(\<^const_name>\<open>implies\<close>, _) $ _ $ X) = is_real_Premise X
        | is_real_Premise (Const(\<^const_name>\<open>Premise\<close>, _) $ X $ _) = is_real_Premise X
        | is_real_Premise (Const(\<^const_name>\<open>MODE_SIMP\<close>, _)) = true
        | is_real_Premise (Const(\<^const_name>\<open>default\<close>, _)) = true
        | is_real_Premise (Const(\<^const_name>\<open>MODE_COLLECT\<close>, _)) = true
        | is_real_Premise _ = false
      val prem_ants = maps (fn th =>
            case extract_prems ctxt th
              of [] => if is_real_Premise (Thm.concl_of th) then [th] else []
               | some => some
            ) ants'1
      val rewrs = map_filter (extract_rewr ctxt) ants'1
      val ants = filter ((fn term => not (is_real_Premise term) andalso not (is_TA_IH_ToA term))
                         o Thm.concl_of) ants'1
               @ ToAs
               |> map (Object_Logic.rulify ctxt
                    #> Simplifier.rewrite_rule ctxt rewrs
                    #> Phi_Help.instantiate_higher_order_schematic_var ~2 ctxt)

      val ctxt'' = ctxt
            |> Context.proof_map (Phi_Reasoner.add_intro_rules (
                  map (fn rule => ([rule], Position.none, Phi_Reasoner.NORMAL_MODE, 200, [], [], NONE)) ants)
            (* #> Phi_Reasoner.add_intro_rules (map (fn (pat,rule) =>
                    ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [(pat,NONE)], [], NONE)) ToAs) *))

      val lsequent' = lsequent
                    |> ALLGOALS (Method.insert_tac ctxt'' prem_ants)
                    |> Seq.hd
                    |> Simplifier.rewrite_goals_rule ctxt rewrs
                    |> reasoner ctxt''

      val lsequent'' = 
            if Thm.prop_of pure_info = \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close>
            then lsequent'
            else Conv.gconv_rule (PLPR_Syntax.premise_tag_conv (
                    Conv.rewr_conv (pure_info RS' (ctxt'', @{thm' conv_intro_premise})))) 1
                    lsequent'

   in Subgoal.retrofit ctxt'' ctxt0 (#params focus) (#asms focus) 1 lsequent'' sequent
   |> Seq.hd
   |> Phi_Reasoners.defer_obligation_tac (false, true, ~1) ctxt
   |> Seq.hd
   |> varify_subgoal_finale
   |> abstract_constraint_guided_reasoning ctxt
  end
in fn ctxt => abstract_constraint_guided_reasoning (Config.map Phi_Reasoner.trace (fn i=>i-1) ctxt)
end

fun chk_unfolded (phi : phi_type) term =
  let val (N,_) = raw_term_name_typ (#term phi)
      fun is_atom (Bound _) = true
        | is_atom (Free _) = true
        | is_atom (Var _) = true
        | is_atom _ = false
      fun chk (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = chk X
        | chk (Abs(_,_,X)) = chk X
        | chk (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T) = is_atom x andalso chk T
        | chk (Const(N',_)) = N = N'
        | chk (Free(N',_)) = N = N'
        | chk (X $ _) = chk X
        | chk _ = false
   in if chk term
      then warning "The phi-type is not unfolded by simplification and inductive destruction. \
                   \The reasoning may fail."
      else ()
  end

fun conv_chk_unfolded (phi : phi_type) ctm = (chk_unfolded phi (Thm.term_of ctm); Conv.all_conv ctm)

fun PLPR_reasoner num ctxt sequent =
  case PLPR_Exhaustive.reason_exhaustively num (ctxt, sequent)
    of SOME th => th
     | NONE => raise Automation_Fail "\<phi>-LPR reasoning fails"
   

fun ToA_reasoner phi ctxt sequent =
  let val sequent'1 = (case Thm.major_prem_of sequent
                         of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ _)
                              => (chk_unfolded phi X; chk_unfolded phi Y;
                                  @{thm' Action_Tag_D[where A = \<open>NToA\<close>]} RS sequent)
                          | _ => sequent)
   in PLPR_reasoner (SOME 1) ctxt sequent'1
  end

fun extract_pure_prem_by_RS rules ctxt thm =
  map_filter (fn rule =>
    try (fn x => thm RS' x) (ctxt, rule)
      |> Option.map (fn thm => thm
          |> Simplifier.rewrite_rule ctxt @{thms' Premise_def[where mode=default] Premise_def[where mode=MODE_SIMP]}
          |> Thm.forall_intr_vars
          |> Phi_Conv.atomize ctxt
          |> (fn th => th RS' (ctxt, @{thm' Premise_I[where mode=default]})))
  ) rules

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
  | make_forall_quantified_property_for_parameters_of_a_phi_type mk _ = []

fun quantifies_abstract_object get_x hint =
  let fun get_x' (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = get_x' X
        | get_x' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = get_x' X
        | get_x' (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = get_x' X
        | get_x' (Abs(_, _, X)) = get_x' X
        | get_x' X = get_x X

      fun lambda data (\<^Const>\<open>Pure.imp\<close> $ A $ B) =
            \<^Const>\<open>Pure.imp\<close> $ lambda data A $ lambda data B
        | lambda data (\<^Const>\<open>Pure.all ty\<close> $ X) = \<^Const>\<open>Pure.all ty\<close> $ lambda data X
        | lambda data (Abs(N,Ty,X)) = Abs(N,Ty, lambda data X)
        | lambda (N,Ty,v) (XX as (\<^Const>\<open>Trueprop\<close> $ X)) =
            if Term.exists_subterm (fn x => x = v) X
            then \<^Const>\<open>Trueprop\<close> $ (HOLogic.all_const Ty $ Abs(N,Ty, Phi_Help.abstract_over (v, X)))
            else XX
        | lambda _ X = X
                 
   in case get_x' hint
   of SOME (X as Free (N,Ty)) => lambda (N,Ty,X) hint
    | SOME (X as Var ((N,_),Ty)) => lambda (N,Ty,X) hint
    | SOME (Bound _) => hint
    | NONE => hint
  end



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