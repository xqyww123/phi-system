signature PHI_TYPE_ALGEBRA_TOOLS = sig

type hint = term
type unify_hint = (Proof.context * hint -> term (*property*) -> term (*fixed term x*) * term (*fixed term T*) -> Envir.env)
  (*Given the `property` and `x : T`, *)

val mk_rule_by_guess_or_hint :
      string (*name of the proof cache, e.g. "/object_equive"*)
    * unify_hint
    *
    (term * term * Phi_Type_Algebra.phi_type ->
       Proof.context ->
         (term * term * term * term *
          Phi_Type_Algebra.phi_type * Proof.context
         )
         Seq.seq)
    *
    int list *
    (Proof.context ->
       Phi_Type_Algebra.phi_type -> thm -> thm)
    *
    (Phi_Type_Algebra.phi_type ->
       Proof.context -> thm -> thm)
    *
    (Phi_Type_Algebra.phi_type * Proof.context * thm ->
       thm option)
    *
    (Phi_Type_Algebra.phi_type * Proof.context -> thm -> thm)
      ->
      thm ->
        Phi_Type_Algebra.phi_type ->
          term option -> Proof.context -> thm Seq.seq

(* Predefined Derivers *)

val identity_element_I : Phi_Type_Algebra.derive
val identity_element_E : Phi_Type_Algebra.derive
val object_equiv : Phi_Type_Algebra.derive
val transformation_functor : Phi_Type_Algebra.derive
val separation_homo_I : Phi_Type_Algebra.derive
val separation_homo_E : Phi_Type_Algebra.derive

end

(**** Implementation ****)

structure Phi_Type_Algebra_Tools : PHI_TYPE_ALGEBRA_TOOLS = struct
open Phi_Type_Algebra

(*** Library ***)

exception Automation_Fail

(* fun reason_fail msg = (warning msg; raise Automation_Fail) *)

structure Simps = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>\<phi>constraint_expansion\<close>
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

(* Library *)

fun classify_bnf_dead_live bnf tys =
  let val btys = snd (Term.dest_Type (BNF_Def.T_of_bnf bnf))
      val deads = BNF_Def.deads_of_bnf bnf
      fun classify (t::tys) (bt::btys) =
           (case classify tys btys
              of (D,L) => if member (op =) deads bt then (t::D, L) else (D, t::L))
        | classify [] [] = ([],[])
        | classify _ _ = raise ListPair.UnequalLengths
   in classify tys btys
  end

fun burrow_bnf_dead_live bnf deads_lives = 
  let val btys = snd (Term.dest_Type (BNF_Def.T_of_bnf bnf))
      val deads' = BNF_Def.deads_of_bnf bnf
      fun burrow (deads,lives) (bt::btys) =
            if member (op =) deads' bt then hd deads :: burrow (tl deads, lives) btys
                                       else hd lives :: burrow (deads, tl lives) btys
        | burrow ([],[]) [] = []
        | burrow _ _ = error "Internal bug: burrow_bnf_dead_live"
   in burrow deads_lives btys
  end

fun guess__get_bnf ctxt Tname =
  case BNF_Def.bnf_of ctxt Tname
    of NONE => (warning ("Type " ^ Tname ^ " is not a known BNF."); Seq.empty)
     | SOME bnf => Seq.single bnf

fun get_bnf ctxt Tname =
  case BNF_Def.bnf_of ctxt Tname
    of NONE => (warning ("Type " ^ Tname ^ " is not a known BNF."); raise Automation_Fail)
     | SOME bnf => bnf


(* fun permute_seq (s::L) =
      Seq.maps (fn s' => permute_seq L |> Seq.map (fn L' => s'::L')) s
  | permute_seq [] = Seq.single [] *)

fun guess_operator' ctxt mk_term known_oprs x_ty =
  case map_filter (fn (ty', term) => if ty' = x_ty then SOME term else NONE)
                  known_oprs
    of [] => (
      case x_ty
        of Type(Tname, Targs) =>
             guess__get_bnf ctxt Tname |> Seq.maps (fn bnf =>
             let val (D,L) = classify_bnf_dead_live bnf Targs
              in mk_term (ctxt, D, L, bnf)
              |> Seq.maps (fn (head,ctxt') =>
                  let fun mk_params ctxt (ty::L) =
                        guess_operator' ctxt mk_term known_oprs ty
                          |> Seq.maps (fn (opr, ctxt') =>
                                mk_params ctxt' L
                                  |> Seq.map (fn (oprs, ctxt'') => (opr::oprs, ctxt'')))
                        | mk_params ctxt [] = Seq.single ([], ctxt)
                   in mk_params ctxt' L
                   |> Seq.map (fn (params', ctxt'3) =>
                        (fold (fn p => fn X => X $ p) params' head, ctxt'3))
                  end)
             end)
         | _ => Seq.empty)
     | L => Seq.of_list L
         |> Seq.map (rpair ctxt)

fun guess_operator ctxt mk_term known_oprs x_ty =
  Seq.make (fn () =>
    case Seq.pull (guess_operator' ctxt mk_term known_oprs x_ty)
      of NONE => (warning ("Fail to guess the abstract operator for type " ^ Syntax.string_of_typ ctxt x_ty) ;
                  NONE)
       | some => some )

fun fp_sugar_of ctxt bnf =
  case BNF_Def.T_of_bnf bnf
    of Type(N, _) => BNF_FP_Def_Sugar.fp_sugar_of ctxt N
     | _ => NONE

fun ctr_sugar_simps (ctr : Ctr_Sugar.ctr_sugar) =
  #injects ctr @ #distincts ctr @ #case_thms ctr @ flat (#sel_thmss ctr)

fun simps_of_ctr_fp (fp : BNF_FP_Def_Sugar.fp_sugar) =
      ctr_sugar_simps (#ctr_sugar (#fp_ctr_sugar fp))

fun simps_of_map_fp (fp : BNF_FP_Def_Sugar.fp_sugar) =
      #map_thms (#fp_bnf_sugar fp)

fun simps_of_pred_fp (fp : BNF_FP_Def_Sugar.fp_sugar) =
      #pred_injects (#fp_bnf_sugar fp)

fun simps_of_rel_fp (fp : BNF_FP_Def_Sugar.fp_sugar) =
      #rel_distincts (#fp_bnf_sugar fp)
    @ #rel_injects (#fp_bnf_sugar fp)

fun global_simps_of_rel (bnf : BNF_Def.bnf) =
      [BNF_Def.rel_eq_of_bnf bnf]

fun simps_of_set (fp : BNF_FP_Def_Sugar.fp_sugar) =
      #set_thms (#fp_bnf_sugar fp)

fun add_global_simps thms ctxt = ctxt
  |> Simps.map' (fn ctxt => ctxt addsimps thms)
  |> (fn ctxt => ctxt addsimps thms)

(* Set *)

fun guess_set_opr ctxt ty element_ty =
  if ty = element_ty
  then Seq.single (Abs("",ty, \<^Const>\<open>insert ty\<close> $ Bound 0 $ \<^Const>\<open>bot \<^Type>\<open>set ty\<close>\<close>), ctxt)
  else case ty
         of Type(Tname, Targs) =>
              guess__get_bnf ctxt Tname |> Seq.maps (fn bnf =>
                let val (D,L) = classify_bnf_dead_live bnf Targs
                    val N = length (BNF_Def.sets_of_bnf bnf)
                    val tys1 = List.tabulate (N, K D)
                    val tys2 = List.tabulate (N, K L)
                    val sets = BNF_Def.mk_sets_of_bnf tys1 tys2 bnf
                    val bnf_fp = BNF_FP_Def_Sugar.fp_sugar_of ctxt Tname
                    val ctxt' = case bnf_fp of NONE => ctxt
                                   | SOME fp => Simps.map' (fn ctxt =>
                                        ctxt addsimps (simps_of_set fp @ simps_of_ctr_fp fp)
                                      ) ctxt
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
              )
          | _ => Seq.empty

(* Relator *)

fun guess_self_rel ctxt 
  = guess_operator ctxt (fn (ctxt, D, L, bnf) =>
      let val ctxt' = ctxt
                   |>(case fp_sugar_of ctxt bnf
                        of NONE => I
                         | SOME fp => Simps.map' (fn ctxt =>
                                        ctxt addsimps ( simps_of_rel_fp fp
                                                      @ simps_of_ctr_fp fp)))
                   |> add_global_simps (global_simps_of_rel bnf)
       in Seq.single (BNF_Def.mk_rel_of_bnf D L L bnf, ctxt')
      end)

fun guess_rel_mapper target_ty ctxt ty element_ty =
  let val [g'] = Name.invent (Variable.names_of ctxt) "g" 1
      val ([g], ctxt') = Variable.add_fixes [g'] ctxt
      val element_ty' = singleton target_ty element_ty
      val g_ty = element_ty --> element_ty' --> HOLogic.boolT
      val g_term = Free(g, g_ty)
      val known_rels = [(element_ty, g_term)]
   in guess_operator ctxt' (fn (ctxt, D, L, bnf) =>
        let val ctxt' = ctxt
                     |>(case fp_sugar_of ctxt bnf
                          of NONE => I
                           | SOME fp => Simps.map' (fn ctxt =>
                                ctxt addsimps ( simps_of_rel_fp fp @ simps_of_map_fp fp @ simps_of_ctr_fp fp)))
                     |> add_global_simps (global_simps_of_rel bnf)
         in Seq.single (BNF_Def.mk_rel_of_bnf D L (target_ty L) bnf, ctxt')
        end
      ) known_rels ty
   |> Seq.map (fn (rel_term', ctxt) =>
        (Abs("", g_ty, Term.abstract_over (g_term, rel_term')), ctxt))
  end

(* Zip \& Unzip *)

fun unzip_typ _ (\<^Type>\<open>prod \<open>a as TFree _\<close> \<open>b as TFree _\<close>\<close>) = (a,b)
  | unzip_typ _ (\<^Type>\<open>prod \<open>a as TVar _\<close> \<open>b as TVar _\<close>\<close>) = (a,b)
  | unzip_typ ctxt (Type(Tname, Targs)) =
      let val bnf = get_bnf ctxt Tname
          val (deads,lives) = classify_bnf_dead_live bnf Targs
          val lives' = map (unzip_typ ctxt) lives
                    |> split_list
       in (Type (Tname,burrow_bnf_dead_live bnf (deads, fst lives')),
           Type (Tname,burrow_bnf_dead_live bnf (deads, snd lives')))
      end

fun zip_typ _ ((a as TFree _), (b as TFree _)) = \<^Type>\<open>prod a b\<close>
  | zip_typ _ ((a as TVar _), (b as TVar _)) = \<^Type>\<open>prod a b\<close>
  | zip_typ ctxt (Type(Tname, Targs), Type(Tname', Targs')) =
      let val _ = if Tname = Tname' then () else raise TYPE ("zip_typ", [], [])
          val bnf = get_bnf ctxt Tname
          val (deads,lives) = classify_bnf_dead_live bnf Targs
          val (deads',lives') = classify_bnf_dead_live bnf Targs'
          val _ = if deads = deads' then () else raise TYPE ("zip_typ", [], [])
          val lives_merge = map2 (fn t1 => fn t2 => zip_typ ctxt (t1,t2)) lives lives'
          val Targs_merge = burrow_bnf_dead_live bnf (deads, lives_merge)
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
                    val bnf = get_bnf ctxt Tname
                    val (deads,lives) = classify_bnf_dead_live bnf Targs
                    val (deads',lives') = classify_bnf_dead_live bnf Targs'
                    val _ = if deads = deads' then () else raise TYPE ("guess_zip", [], [])
                    val fp_more = case BNF_FP_Sugar_More.get_fp_more (Context.Proof ctxt) Tname
                                    of SOME x => x | NONE => raise Automation_Fail
                    val zip = (if flag then BNF_FP_Sugar_More.mk_zip
                                       else BNF_FP_Sugar_More.mk_unzip) deads lives lives' fp_more
                    val ctxt'' = ctxt
                              |> (case fp_sugar_of ctxt bnf
                                    of NONE => I
                                     | SOME fp => Simps.map' (fn ctxt =>
                                            ctxt addsimps (
                                                (if flag then #zip_simps fp_more else #unzip_simps fp_more)
                                                @ simps_of_rel_fp fp @ simps_of_map_fp fp
                                                @ simps_of_ctr_fp fp)))
                              |> add_global_simps (global_simps_of_rel bnf)
                    val (args, ctxt') = ctxt''
                          |> fold_map (guess_zip_guided flag (target,target'))
                                      (lives ~~ lives')
                    val map_tys = map (fn (_,z) => case Term.fastype_of z
                                                     of \<^Type>\<open>fun a b\<close> => (a,b)) args
                                |> split_list
                    val mp = BNF_Def.mk_map_of_bnf deads (fst map_tys) (snd map_tys) bnf
                    val rl = BNF_Def.mk_rel_of_bnf deads lives lives' bnf
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
          val bnf = get_bnf ctxt Tname
          val (deads,lives) = classify_bnf_dead_live bnf Targs
          val (deads',lives') = classify_bnf_dead_live bnf Targs'
          val _ = if deads = deads' then () else raise TYPE ("guess_zip", [], [])
          val fp_more = case BNF_FP_Sugar_More.get_fp_more (Context.Proof ctxt) Tname
                          of SOME x => x | NONE => raise Automation_Fail
          val zip = (if flag then BNF_FP_Sugar_More.mk_zip
                             else BNF_FP_Sugar_More.mk_unzip) deads lives lives' fp_more
          val simps = (case Ctr_Sugar.ctr_sugar_of ctxt Tname
                                   of SOME cs => ctr_sugar_simps cs
                                    | _ => [])
          val (args, ctxt') = ctxt addsimps simps
                  |> fold_map (guess_zip flag) (lives ~~ lives')
          val map_tys = map (fn z => case Term.fastype_of z
                                       of \<^Type>\<open>fun a b\<close> => (a,b)) args
                      |> split_list
          val mp = BNF_Def.mk_map_of_bnf deads (fst map_tys) (snd map_tys) bnf
       in (Abs("x", domain_type (Term.fastype_of zip),
                    Term.list_comb (mp, args) $ (zip $ Bound 0)),
           ctxt')
      end
  | guess_zip _ ((a as TFree _), (b as TFree _)) ctxt = (Abs("x", \<^Type>\<open>prod a b\<close>, Bound 0), ctxt)
  | guess_zip _ ((a as TVar _), (b as TVar _)) ctxt = (Abs("x", \<^Type>\<open>prod a b\<close>, Bound 0), ctxt)
  | guess_zip _ (a,b) _ = raise TYPE ("guess_zip", [a,b], [])



(** Select Hint **)

local open Pretty

fun err_derive prop_name =
      error ("Fail to derive the property " ^ prop_name)

fun err_prove hint thy =
      error ("Fail to show the given property automatically:\n" ^
      Context.cases Syntax.string_of_term_global Syntax.string_of_term thy hint)

in

fun accept_one prop_name gen [] phityp thy = (gen NONE phityp thy
                    handle Automation_Fail => err_derive prop_name)
  | accept_one _ gen [H] phityp thy = (gen (SOME H) phityp thy
             handle Automation_Fail => err_prove H thy)
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
      error ("Fail to show the given property automatically:\n" ^
      Context.cases Syntax.string_of_term_global Syntax.string_of_term thy hint)

in

fun select_one_hint prop_name action (hints,thy) =
  case (filter (is_the_hint prop_name) hints, filter (is_deriving_hint prop_name) hints)
    of ([hint], []) => (
          (filter_out (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints,
           action (SOME hint) thy)
          handle Automation_Fail => err_prove hint thy)
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
          handle Automation_Fail => err_derive prop_name)
     | ([], _) => error ("It is enough to just give me one hint to derive "^ prop_name)
     | (hints, _) => (
          filter_out (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints,
          fold (fn hint => action (SOME hint)
                handle Automation_Fail => err_prove hint thy) hints thy)

fun chk_no_hints prop_name (hints, thy) =
  case filter (fn H => is_the_hint prop_name H orelse is_deriving_hint prop_name H) hints
    of [] => (hints, thy)
     | _ => error ("Property " ^ prop_name ^ " is not supported on the \<phi>-type.")

end

(** Automation Framework **)

(* Default Obligation Solver *)

fun oblg_solver proof_id ctxt sequent =
  Phi_Sledgehammer_Solver.auto (SOME proof_id) (ctxt, sequent)
    |> (fn th => case Thm.major_prem_of th
                   of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Premise\<close> $ _ $ \<^Const>\<open>True\<close>) =>
                        @{thm' Premise_True} RS th
                    | \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> =>
                        @{thm' TrueI} RS th
                    | _ => th)

(* The Framework *)

(*quants: an array telling how to interpret the quantified variables in the first antecedent of the rule.
  It is used in generating the induction rule.
  quants[i] = 0 means interpret the variable as the abstract object
  quants[i] = i means interpret the variable as the i-th parameter of the \<phi>-type
  quants[i] = ~1 means interpret it as a fixed variable
  Note the quants is reversed against the quantified variables*)
fun mk_rule_by_guess_or_hint (name,unify_hint,guess_property,quants,ind_conv,reasoning,solver,simp)
                             rule (phi0 : phi_type) hint ctxt0 =
  let (*val (inst,inst',phi,ctxt01) = fix_phi_type true phi0 ctxt0*)
      val ((x_term0, T_term0), ctxt01) = fix_phi_term_params (#term phi0) ctxt0
   in (case hint of SOME H0 =>
              let fun collect_ants (\<^Const>\<open>Pure.imp\<close> $ (\<^Const>\<open>Trueprop\<close> $ L) $ R) = L :: collect_ants R
                    | collect_ants (\<^Const>\<open>Trueprop\<close> $ _) = []
                    | collect_ants _ = error "Bad hint"
                  fun concl_of_hint (\<^Const>\<open>Pure.imp\<close> $ (\<^Const>\<open>Trueprop\<close> $ _) $ R) = concl_of_hint R
                    | concl_of_hint (X as \<^Const>\<open>Trueprop\<close> $ _) = X
                    | concl_of_hint _ = error "Bad hint"
                  val idx = Phi_Type_Algebra.phi_maxidx_of phi0 ~1 + 1
                  val H = Logic.incr_indexes ([],[],idx) H0
                  val Envir.Envir inst_hint = unify_hint (ctxt01, H) (concl_of_hint H) (x_term0, T_term0)
                  val inst01 = Phi_Help.env_to_table ctxt01 (#tyenv inst_hint, #tenv inst_hint)
                  val phi01 = Phi_Type_Algebra.instantiate_phi inst01 phi0
                  val (inst, phi, ctxt) = fix_phi_type true phi01 ctxt01
                  val subst = Term_Subst.instantiate (Phi_Help.table_no_c inst01)
                           #> Term_Subst.instantiate (Phi_Help.table_no_c inst)
                  val (x_term0', T_term0', H0') = (subst x_term0, subst T_term0, subst H)
                  val ([x_term, T_term, H''], ctxt) =
                          Variable.import_terms true [x_term0', T_term0', H0'] ctxt
               in Seq.single (Phi_Help.list_mk_conj (collect_ants H''), concl_of_hint H'',
                              x_term, T_term, phi, ctxt)
              end
           | _ => guess_property (x_term0, T_term0, phi0) ctxt01)
   |> Seq.map (fn (ant01, property01, x_term01, T_term01, phi01, ctxt01) => 
  let val (ant, property, x_term, T_term, phi, ctxt) =
        if is_phi_type_fixed phi01
        then (ant01, property01, x_term01, T_term01, phi01, ctxt01)
        else let val (inst, phi, ctxt) = fix_phi_type true phi01 ctxt01
                 val subst = Envir.subst_term (Phi_Help.table_to_env inst)
              in (subst ant01, subst property01, subst x_term01, subst T_term01, phi, ctxt)
             end
      val inst_rule = Pattern.match (Proof_Context.theory_of ctxt) (Thm.concl_of rule, property)
                                    (Vartab.empty, Vartab.empty)
                   |> apsnd (Vartab.update_new (("Ant",0), (\<^typ>\<open>bool\<close>, ant)))
                   |> Phi_Help.env_to_table ctxt
      val rule' = Thm.instantiate inst_rule rule
      
      fun mk_free_table i ret (X $ Free (N,_)) =
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
              |> ind_conv ctxt phi

      val ((inst,[rule't]), ctxt't) = Variable.import true [rule'] ctxt
      val ind't = Thm.instantiate inst ind
      val rule'2 = singleton (Variable.export ctxt't ctxt) (ind't RS rule't)

      val rule'3 = reasoning phi ctxt rule'2
      val rule'4 =(case solver (phi, ctxt, rule'3)
                     of SOME ret => ret
                      | NONE => oblg_solver (#proof_id phi ^ name) ctxt rule'3)
                |> simp (phi,ctxt)
                |> singleton (Proof_Context.export ctxt ctxt0)
   in Phi_Reasoner.info_pretty ctxt 0 (fn () => let open Pretty in
        block [str "Derived: ", Thm.pretty_thm ctxt rule'4]
      end) ;
      rule'4
  end)
  end

(* Default Hint Unifier *)

local
fun extract_hhf ext (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = extract_hhf ext X
  | extract_hhf ext (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = extract_hhf ext X
  | extract_hhf ext X = ext X
in

type hint = term
type unify_hint = (Proof.context * term -> term -> term * term -> Envir.env)

fun hint_unify_by_type extract_type (ctxt, hint) property (_, T') =
    ( Unify.smash_unifiers (Context.Proof ctxt) [(extract_hhf extract_type property, T')] Envir.init
        |> Seq.chop 2
        |> (fn ([], _) => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
             | ([x], _) => x
             | _ => error ("Multi-resolution in hint: " ^ Syntax.string_of_term ctxt hint))
      handle TERM _ => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
           | Match  => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
    )

fun hint_unify_by_type_operator extract_type_operator (ctxt, hint) property (_, F_term $ _) =
    ( Unify.smash_unifiers (Context.Proof ctxt)
                           [(extract_hhf extract_type_operator property, F_term)] Envir.init
        |> Seq.chop 2
        |> (fn ([], _) => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
             | ([x], _) => x
             | _ => error ("Multi-resolution in hint: " ^ Syntax.string_of_term ctxt hint))
      handle TERM _ => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
           | Match  => error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
    )
  | hint_unify_by_type_operator _ (ctxt, hint) _ _ = error ("Bad hint: " ^ Syntax.string_of_term ctxt hint)
end

(* Default Conversion of the Induction Rule *)

fun default_ind_conv (conv_IH, conv_CL) ctxt (phi:phi_type) =
  Conv.fconv_rule (Phi_Conv.hhf_conv (
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
          val prem = Thm.cprop_of ToA' |> Thm.dest_arg1
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
                                        (*fun rewr_pat (\<^Const>\<open>Trueprop\<close> $ (\<^Const_>\<open>Imply ty\<close> $ X $ Y $ _)) =
                                              (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Imply ty\<close> $ X $ Y
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

fun is_Premis (\<^Const>\<open>Premise\<close> $ _ $ _) = true
  | is_Premis (\<^Const>\<open>Trueprop\<close> $ X) = is_Premis X
  | is_Premis _ = false

fun extract_rewr ctxt th =
  case Thm.prop_of th
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _
          $ (Const(\<^const_name>\<open>HOL.eq\<close>, \<^Type>\<open>fun Ty _\<close>) $ _ $ _)) =>
        if can Phi_Syntax.dest_phi_type_ty Ty
        then SOME ((th RS' (ctxt, @{thm' Premise_D})) RS' (ctxt, @{thm' eq_reflection}))
        else NONE
     | _ => NONE

fun varify_subgoal mk ctxt sequent =
  let val LHS = Thm.major_prem_of sequent
   in case mk LHS of SOME (LHSS, gen_RHSS) =>
      let val rvar_names = Name.invent (Variable.names_of ctxt) "schm" (length LHSS)
          val ctxt' = Variable.add_fixes_direct rvar_names ctxt
          val rvars = map2 (fn N => fn T => Free (N, Term.fastype_of T)) rvar_names LHSS
          val eqs = map2 (fn l => fn r => \<^Const>\<open>Pure.eq \<open>Term.fastype_of r\<close>\<close> $ l $ r) LHSS rvars
          val rule = \<^Const>\<open>Pure.imp\<close> $ gen_RHSS rvars $ LHS
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

fun gen_abstract_constraint_guided_reasoning varify reasoner =
let fun abstract_constraint_guided_reasoning ctxt0 sequent0 =
  case Thm.major_prem_of sequent0
    of _ $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => @{thm' \<r>Success_I} RS sequent0
     | _ =>
  let val sequent = sequent0
                 |> Phi_Help.repeat (fn th => @{thm' allI} RS th)
                 |> (fn th => @{thm' impI} RS th
                              handle THM _ => Method.insert_tac ctxt0 [Thm.transfer' ctxt0 @{thm' TrueI}] 1 th
                                           |> Seq.hd)
      val (focus, lsequent'0) = Subgoal.focus ctxt0 1 NONE sequent
      val ctxt = #context focus
      val lsequent = varify_subgoal varify ctxt lsequent'0

      val len = length (#prems focus)
      val [Ant, pure_info] = List.drop (#prems focus, len - 2)

      val ToAs = maps (instantiate_ToA (Ant,pure_info,ctxt)) (List.take (#prems focus, len - 2))

      val ants'1 = Phi_Help.conj_elims ctxt (List.nth (#prems focus, len - 2))
                 @ List.take (#prems focus, len - 2)
      val prem_ants = filter (is_Premis o Thm.concl_of) ants'1
      val rewrs = map_filter (extract_rewr ctxt) ants'1
      val ants = filter ((fn term => not (is_Premis term) andalso not (is_TA_IH_ToA term))
                         o Thm.concl_of) ants'1
               @ ToAs
               |> map (Simplifier.rewrite_rule ctxt rewrs)

      val ctxt'' = ctxt
            |> Context.proof_map (Phi_Reasoner.add_intro_rules (
                  map (fn rule => ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [], [], NONE)) ants)
            (* #> Phi_Reasoner.add_intro_rules (map (fn (pat,rule) =>
                    ([rule], Position.none, Phi_Reasoner.NORMAL, 200, [(pat,NONE)], [], NONE)) ToAs) *))

      val lsequent' = lsequent
                    |> ALLGOALS (Method.insert_tac ctxt'' prem_ants)
                    |> Seq.hd
                    |> Simplifier.rewrite_goals_rule ctxt rewrs
                    |> reasoner ctxt''

      val lsequent'' = Conv.gconv_rule (PLPR_Syntax.premise_tag_conv (
                          Conv.rewr_conv (pure_info RS' (ctxt'', @{thm' conv_intro_premise})))) 1
                          lsequent'

   in Subgoal.retrofit ctxt'' ctxt0 (#params focus) (#asms focus) 1 lsequent'' sequent
   |> Seq.hd
   |> Phi_Reasoners.defer_obligation_tac ctxt
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
     | NONE => raise Automation_Fail
   

fun ToA_reasoner phi ctxt sequent =
  let val sequent'1 = (case Thm.major_prem_of sequent
                         of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Imply\<close>, _) $ X $ Y $ _)
                              => (chk_unfolded phi X; chk_unfolded phi Y;
                                  @{thm' Action_Tag_D[where A = \<open>ToSA\<close>]} RS sequent)
                          | _ => sequent)
   in PLPR_reasoner (SOME 1) ctxt sequent'1
  end

fun abstract_constraint_guided_reasoning varify phi ctxt =
      gen_abstract_constraint_guided_reasoning varify (ToA_reasoner phi) ctxt


(* (** Misc **)

fun conv_eq_imp ctxt ctm =
  (Conv.rewr_conv @{thm imp_ex[folded atomize_eq]} then_conv
   Phi_Conv.hol_all_conv (conv_eq_imp o snd) ctxt) ctm
  handle CTERM _ => Conv.all_conv ctm
       | THM _ => Conv.all_conv ctm *)

(*** Object Equivalence ***)

local

fun set_last_schematic_var ctxt rule0 =
  let val rule = Phi_Help.beta_eta_contract rule0
      val (t1,t2,tm) =
        case Thm.concl_of rule
          of _ (*Trueprop*) $ (_ (*Object_Equiv*) $ _ $ Abs (_, t1, Abs (_, t2, tm)))
              => (t1,t2,tm)
           | _ => error "Internal bug cb9504e4-7db1-45f8-b1f6-ec37a5b75105"
      fun get_the_last_var (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ X) = get_the_last_var X
        | get_the_last_var (Var v $ Bound 0 $ Bound 1) = (v, Abs("",t2,Abs("",t1,\<^term>\<open>True\<close>)))
        | get_the_last_var (Var v $ Bound 1 $ Bound 0) = (v, Abs("",t1,Abs("",t2,\<^term>\<open>True\<close>)))
        | get_the_last_var _ = error "Internal bug 6160c2ee-6448-4654-b017-237c879c33a3"
      val last_var = get_the_last_var tm |> apsnd (Thm.cterm_of ctxt)
   in Thm.instantiate (TVars.empty, Vars.make [last_var]) rule
  end

fun set_eq_when_it_is_constant_true ctxt rule0 =
  let val rule = Phi_Help.beta_eta_contract rule0
      val v = case Thm.concl_of rule
                of _ (*Trueprop*) $ (_ (*\<phi>Equal_Obj*) $ Var v $ _) => v
                 | _ => error "Internal bug 5d769e14-74ca-4afb-8d43-672e0afc5470"
      val P = case snd v
                of \<^Type>\<open>fun a \<open>\<^Type>\<open>fun b _\<close>\<close>\<close> => Abs("",a,Abs("",b,\<^term>\<open>True\<close>))
                 | _ => error "Internal bug a74fc08c-d9c1-4b19-99b2-4f18a07b31aa"
   in Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt P)]) rule
  end

(*must be beta-eta normalized*)
fun infer_eq ctxt rule =
  let fun is_free_bound lev (Abs(_,_,X)) = is_free_bound (lev+1) X
        | is_free_bound lev (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ X $ _) = is_free_bound lev X
        | is_free_bound lev (A $ B) = is_free_bound lev A andalso is_free_bound lev B
        | is_free_bound lev (Bound i) = (i = lev)
        | is_free_bound _ _ = true
      fun is_free_bound' (Abs(_,_,X)) = is_free_bound 0 X
        | is_free_bound' _ = true
   in (case Thm.major_prem_of rule
        of _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (
                  Const(\<^const_name>\<open>Ex\<close>, _) $ (Abs(_,_, Const(\<^const_name>\<open>All\<close>, _) $ _)) ) $ _) =>
            Conv.fconv_rule (Phi_Conv.leading_antecedent_conv (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (
                  HOLogic.conj_conv (Phi_Conv.move_Ex_inside_All ctxt) Conv.all_conv
              )) ctxt)) rule
            |> infer_eq ctxt
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (
                  Const(\<^const_name>\<open>Ex\<close>, _) $ (Abs(_,_, Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ )) ) $ _) =>
            Conv.fconv_rule (Phi_Conv.leading_antecedent_conv (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (
                  HOLogic.conj_conv (Conv.rewr_conv @{thm' HOL.ex_simps(6)[folded atomize_eq]}) Conv.all_conv
              )) ctxt)) rule
            |> infer_eq ctxt
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (Const(\<^const_name>\<open>All\<close>, _) $ X ) $ _) =>
            infer_eq ctxt (if is_free_bound' X
                           then @{thm' Object_Equiv_rule_move_all2} RS rule
                           else @{thm' Object_Equiv_rule_move_all} RS rule)
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>, _)) =>
            (@{thm Object_Equiv_rule_move_set_eq_end} RS (@{thm' simp_thms(21)[THEN iffD2]} RS rule))
              |> set_last_schematic_var ctxt
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
            infer_eq ctxt (@{thm' Object_Equiv_rule_move_set_eq} RS rule)
         | _ (*Trueprop*) $ Const(\<^const_name>\<open>True\<close>, _) =>
            (@{thm' TrueI} RS rule)
              |> set_eq_when_it_is_constant_true ctxt
         | _ => error "internal bug 7147bf3f-9e7d-4ffc-a40b-aa621a4fca21")
      handle THM _ => (
        warning ("Fail to infer the object equivelance from the obtained obligation\n" ^
                 Thm.string_of_thm ctxt rule);
        raise Automation_Fail
      )
  end


fun guess_property_obj_eq (x_Term, T_term, (phi:phi_type)) ctxt0 =
  let val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi)) 
      fun mk_Ants ctxt (Ty::rev_arg_tys) (eq::eq_names) ants param_eqs (T_term $ A) =
           (let val (rev_arg_tys_A, x_ty_A, model_ty_A) = dest_parameterized_phi_ty Ty
                val arity_A = length rev_arg_tys_A
                val typ = x_ty_A --> x_ty_A --> \<^typ>\<open>bool\<close>
                val ant = (Term.incr_bv (arity_A, 0, A))
                        |> fold_index (fn (i,_) => fn X => X $ Bound (arity_A-1-i)) rev_arg_tys_A          
                        |> (fn X => \<^Const>\<open>Object_Equiv x_ty_A model_ty_A\<close> $ X $ Free(eq, typ))
                        |> fold (fn T => fn X =>
                            Const(\<^const_name>\<open>All\<close>, (T --> HOLogic.boolT) --> HOLogic.boolT)
                              $ Abs("",T,X)
                           ) rev_arg_tys_A
             in mk_Ants ctxt rev_arg_tys eq_names (ant::ants)
                        ((x_ty_A, Free(eq, typ))::param_eqs) T_term
            end
            handle TYPE _ => (ants, param_eqs))
        | mk_Ants _ [] [] ants param_eqs _ = (ants, param_eqs)
        | mk_Ants _ _ _ _ _ _ = raise ListPair.UnequalLengths

      val arity = length rev_arg_tys
      val rev_eq_names' = Name.invent (Variable.names_of ctxt0) "eq" arity
      val (rev_eq_names, ctxt) = Variable.add_fixes rev_eq_names' ctxt0
      val (ants,param_eqs) = mk_Ants ctxt rev_arg_tys rev_eq_names [] [] T_term
      val ant = Phi_Help.list_mk_conj ants

      val eq_terms =
             if #is_recursive phi
             then guess_self_rel ctxt param_eqs x_ty
             else Seq.single (Var(("eq", 1), x_ty --> x_ty --> HOLogic.boolT), ctxt)
   in eq_terms
   |> Seq.map (fn (eq_term, ctxt') =>
        (ant, \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Object_Equiv x_ty model_ty\<close> $ T_term $ eq_term),
         x_Term, T_term, phi, ctxt'))
  end

fun OE_reasoning phi ctxt rule =
  let val ctxt' = Context.proof_map (Phi_Reasoner.add_pass (
            "\<phi>TA.OE", \<^pattern_prop>\<open>Object_Equiv _ _\<close>,
            fn _ => fn (rules, _, pats, guard, ctxt) =>
                       (rules, Phi_Reasoner.LOCAL_CUT, pats, guard, ctxt))) ctxt
   in abstract_constraint_guided_reasoning (K NONE) phi ctxt' rule
  end

fun gen_obj_equal' hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val unify_hint = hint_unify_by_type (fn (\<^Const>\<open>Object_Equiv _ _\<close> $ T' $ _) => T')
      val ind_conv = default_ind_conv (K (K (Conv.rewr_conv @{thm \<phi>TA_EO_rewr_IH})),
                       fn ctxt => fn _ => Conv.rewr_conv @{thm \<phi>TA_EO_rewr_C} then_conv
                            Conv.implies_concl_conv (
                              HOLogic.Trueprop_conv (
                              Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                            )))
      fun infer (phi, ctxt, rule) =
            if is_some hint0 orelse #is_recursive phi then NONE
            else (@{thm' Premise_I} RS rule)
                   |> Phi_Help.beta_eta_contract
                   |> infer_eq ctxt
                   |> SOME
      fun simp (phi, ctxt) = Conv.fconv_rule (Phi_Conv.hhf_concl_conv 
                                 (K (Conv.arg_conv (Conv.arg_conv (Simplifier.rewrite ctxt)))) ctxt)
      val rules = mk_rule_by_guess_or_hint ("/obj_equal", unify_hint, guess_property_obj_eq, [0],
                                            ind_conv, OE_reasoning, infer, simp)
                                     @{thm Object_Equiv_rule} phi0 hint0 ctxt0
   in Seq.chop 2 rules
   |> (fn ([], _) => raise Automation_Fail
        | ([rule'], _) => thy
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 40
                                              ([],[]) NONE [Morphism.thm m rule'])
            |> Phi_Type_Algebra.note_properties phi0 [("obj_eq", [rule'])]
        | (_,_) => (warning "More than one property instances are inferred.";
                        raise Automation_Fail))
  end

in

val object_equiv = accept_one "Object_Equiv" gen_obj_equal'

end

(*** Transformation Functor ***)

fun is_Type_Opr ty =
  (case dest_parameterized_phi_ty ty
     of ([],_,_) => false
      | ((arg_ty::_),_,_) => (
   case dest_parameterized_phi_ty arg_ty
     of ([],_,_) => true
      | _ => false)
   handle TYPE _ => false)

fun assert_Type_Opr prop_name ty =
  if is_Type_Opr ty then ()
  else error ("Fail to derive " ^ prop_name ^ " : Not a \<phi>-type operator!")

local

fun guess_property_TF (x_term, FT_term, phi) ctxt =
  let val (T_ty :: rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty T_ty
      val F_term = (case FT_term of F $ _ => F
                                  | _ => error "Internal bug: Not a Type Operator")

      val param_typs = Term.add_tfreesT element_ty []
      val (param_typs', ctxt'1) = Variable.invent_types (map snd param_typs) ctxt
                                |> apfst (map TFree)
      val inst_ty = TFrees.make (param_typs ~~ param_typs')
      val F'1_term = Term_Subst.instantiate_frees (inst_ty, Frees.empty) F_term
      
      val params = Term.add_frees F'1_term []      
      val (param_names', ctxt') = Variable.variant_fixes (map fst params) ctxt'1
      val params' = map2 (fn N => fn (_,T) => Free(N,T)) param_names' params
      val inst = Frees.make (params ~~ params')
      val F'_term = Term_Subst.instantiate_frees (TFrees.empty, inst) F'1_term

      val ant = map2 (fn (N,T) => fn p' => \<^Const>\<open>HOL.eq T\<close> $ Free(N,T) $ p') params params'
              |> Phi_Help.list_mk_conj
              |> (fn X => \<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_SIMP\<close> $ X)

      val TF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                       of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                           \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                          \<^Const>\<open>Transformation_Functor a b c d e f\<close> $ F_term $ F'_term
                        | _ => error "Internal bug")

   in guess_set_opr ctxt' x_ty element_ty
   |> Seq.maps (fn (D_term, ctxt'2) =>
        guess_rel_mapper (map (Term_Subst.instantiateT_frees inst_ty)) ctxt'2 x_ty element_ty
     |> Seq.map (fn (rel_mapper, ctxt'3) =>
          (ant, \<^Const>\<open>Trueprop\<close> $ (TF_head $ D_term $ rel_mapper),
           x_term, FT_term, phi, ctxt'3)))
  end


fun TF_reasoner ctxt sequent =
  case PLPR_Exhaustive.reason_exhaustively (SOME 2)
            (ctxt, @{thm' \<phi>TA_TF_rule_step} RS sequent)
    of SOME th => th
     | NONE => raise Automation_Fail

fun TF_reasoning _ ctxt =
      gen_abstract_constraint_guided_reasoning (K NONE) TF_reasoner ctxt

fun gen_TF hint0 (phi0 : phi_type) generic =
  let val _ = assert_Type_Opr "Transformation_Functor" (Term.fastype_of (#term phi0))
      val ctxt0 = Context.proof_of generic
      val unify_hint = hint_unify_by_type_operator (
              fn (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ F1 $ _ $ _ $ _) => F1)
      val ind_conv = default_ind_conv (K (K (Conv.rewr_conv @{thm \<phi>TA_TF_rewr})),
                        fn ctxt => fn phi =>
                          Conv.rewr_conv @{thm \<phi>TA_TF_rewr} then_conv
                            Conv.implies_concl_conv (Conv.implies_concl_conv (
                                  HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                              Phi_Syntax.implication_conv
                              (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)) then_conv
                               conv_chk_unfolded phi)
                              (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)) then_conv
                               conv_chk_unfolded phi)
                              Conv.all_conv)))))
      fun simp (phi, ctxt) =
            Conv.fconv_rule (
              Phi_Conv.hhf_concl_conv (K (
                  Conv.arg_conv (Conv.combination_conv
                    (Conv.arg_conv (Simplifier.rewrite ctxt))
                    (Simplifier.rewrite ctxt))
             )) ctxt)
      val rules = mk_rule_by_guess_or_hint ("/TF", unify_hint, guess_property_TF, [0,~1,~1,~1],
                                            ind_conv, TF_reasoning, K NONE, simp)
                                            @{thm \<phi>TA_TF_rule} phi0 hint0 ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail
        | SOME (rule', _) =>
          let fun set_prem_to_True rule =
                case Thm.prop_of rule
                  of _ (*Trueprop*) $ (_ $ Var v) =>
                      Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>True\<close>)]) rule
                   | _ => rule
              val locale_rule = (rule' RS' (ctxt0, @{thm' Transformation_Functor_L.intro}))
                              |> (fn th => case Thm.nprems_of th
                                             of 0 => set_prem_to_True th
                                              | 1 => Seq.hd (Thm.assumption (SOME ctxt0) 1 th)
                                              | _ => error "Internal bug")

              exception GIVE_UP
              fun setup_functional_TF cmd lthy =
                let val locale_rule_FTF = (@{thm' Functional_Transformation_Functor_axioms.intro}
                                              RS (locale_rule RS' (lthy, @{thm' Functional_Transformation_Functor.intro})))
                                        |> (SOLVED' (Clasimp.fast_force_tac lthy) 1
                                            THEN SOLVED' (Clasimp.fast_force_tac lthy) 1)
                                        |> Seq.pull
                                        |> (fn SOME (ret, _) => ret
                                             | NONE => raise GIVE_UP)
                    val ((_,[locale_rule_FTF']), _) = Variable.import true [locale_rule_FTF] lthy
                 in case Thm.concl_of locale_rule_FTF'
                      of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _)
                            $ Fa $ Fb $ D $ m $ Pr $ pm $ fm) =>
                    cmd ([(\<^locale>\<open>Transformation_Functor_L\<close>, ((Term.term_name (#term phi0), true),
                          (Expression.Positional [SOME Fa, SOME Fb, SOME D, SOME m,
                                                  SOME (case Pr of Var _ => \<^Const>\<open>True\<close> | _ => Pr),
                                                  SOME pm, SOME fm],
                           [])))], []) [] lthy
                      |> Proof.refine_primitive (fn _ => fn th => locale_rule_FTF' RS th)
                      |> Proof.global_done_proof
                end
                handle GIVE_UP => lthy
                
              fun setup_locale cmd lthy =
                let val ((_,[locale_rule']), _) = Variable.import true [locale_rule] lthy
                 in case Thm.concl_of locale_rule'
                      of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Transformation_Functor_L\<close>, _)
                            $ Fa $ Fb $ D $ m $ Pr) =>
                    cmd ([(\<^locale>\<open>Transformation_Functor_L\<close>, ((Term.term_name (#term phi0), true),
                          (Expression.Positional [SOME Fa, SOME Fb, SOME D, SOME m,
                                                  SOME (case Pr of Var _ => \<^Const>\<open>True\<close> | _ => Pr)],
                           [])))], []) [] lthy
                      |> Proof.refine_primitive (fn _ => fn th => locale_rule' RS th)
                      |> Proof.global_done_proof
                end
           in generic
           |> Phi_Type_Algebra.note_properties phi0 [("transformation_functor", [rule'])]
           |> Context.mapping (Named_Target.theory_map (setup_locale Interpretation.global_interpretation))
                              (setup_locale Interpretation.sublocale)
         (*|> Context.mapping (Named_Target.theory_map (setup_functional_TF Interpretation.global_interpretation))
                              (setup_functional_TF Interpretation.sublocale)*)
          end)
  end

in

val transformation_functor = accept_one "Transformation_Functor" gen_TF

end

(*** Separation Homo ***)

fun guess_property_SH flag (x_term0, FT_term0, (phi0:phi_type)) ctxt =
  let val (T_ty0 :: _, x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val ([],element_ty0, ele_model0) = dest_parameterized_phi_ty T_ty0
      val inst0  = Vartab.empty
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (model_ty0, \<^sort>\<open>sep_magma\<close>)
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (ele_model0, \<^sort>\<open>sep_magma\<close>)
                   handle TYPE _ => raise Automation_Fail
      val inst = Phi_Help.tyenv_to_tvars_table_no_c inst0
      val inst' = TVars.map (K (Thm.ctyp_of ctxt)) inst
      val phi = instantiate_phi (inst',Vars.empty) phi0
      val subst = Term_Subst.instantiate (inst, Vars.empty)
      val (x_term, FT_term) = (subst x_term0, subst FT_term0)

      val (T_ty :: _, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([], element_ty, _) = dest_parameterized_phi_ty T_ty

      val target = case element_ty
                     of \<^Type>\<open>prod a b\<close> => (a,b)
                      | _ => error "Internal bug #8522d8e9-57a1-4ad9-800e-1c1222fcabfc"
      val ((dom,zip), ctxt) = guess_zip_guided flag target (unzip_typ ctxt x_ty) ctxt
      val F_term = (case FT_term of F $ _ => F
                                  | _ => error "Internal bug: Not a Type Operator")

      fun subst_ty residue t =
            if t = element_ty then residue
            else case t
                   of Type(Tname, targs) => Type(Tname, map (subst_ty residue) targs)
                    | t' => t'

      val Fa = Term.map_types (subst_ty (fst target)) F_term
      val Fb = Term.map_types (subst_ty (snd target)) F_term
      val SH = (case (Term.fastype_of Fa, Term.fastype_of Fb)
                  of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                      \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                    (if flag
                     then \<^Const>\<open>Separation_Homo\<^sub>I a b c d e f x_ty\<close>
                       $ Fa $ Fb $ F_term
                       $ (\<^Const>\<open>Collect \<^Type>\<open>prod c f\<close>\<close> $ (\<^Const>\<open>case_prod c f \<^Type>\<open>bool\<close>\<close> $ dom))
                       $ zip
                     else \<^Const>\<open>Separation_Homo\<^sub>E a b c d e f x_ty\<close>
                       $ Fa $ Fb $ F_term $ zip)
                   | _ => error "Internal bug")
   in Seq.single (\<^Const>\<open>True\<close>, HOLogic.Trueprop $ SH,
                  x_term, FT_term, phi, ctxt)
  end

fun make_phi_for_pair ctxt0 (phi0 : phi_type) =
  let val (rev_ty_args, _, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val ([],element_ty,_) = dest_parameterized_phi_ty (hd rev_ty_args)
      val idx = phi_maxidx_of phi0 ~1 + 1
      val ty_x'dest = Term.add_tvarsT element_ty []
      val thy0 = Context.theory_of ctxt0
      val SS = map (Sign.arity_sorts thy0 \<^type_name>\<open>prod\<close> o snd) ty_x'dest
      val instTy = fold_index (fn (i, (K, [S1,S2])) =>
                      TVars.add (K, \<^Type>\<open>prod \<open>TVar(("xa",idx+i),S1)\<close> \<open>TVar(("xb",idx+i),S2)\<close>\<close>)
                   ) (ty_x'dest ~~ SS) TVars.empty
      val instTy'= TVars.map (K (Thm.global_ctyp_of thy0)) instTy
      val phi = instantiate_phi (instTy', Vars.empty) phi0
   in phi
  end

fun SHu_reasoner ctxt sequent =
  case PLPR_Exhaustive.reason_exhaustively (SOME 2)
            (ctxt, @{thm' \<phi>TA_SHu_rule_step} RS sequent)
    of SOME th => th
     | NONE => raise Automation_Fail

fun SH_reasoning is_intro phi ctxt =
      gen_abstract_constraint_guided_reasoning (K NONE) (fn ctxt => fn sequent => (
         (case Thm.major_prem_of sequent
            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Imply\<close>, _)
                        $ (Const(\<^const_name>\<open>times\<close>, _) $ X1 $ X2) $ _ $ _)
                 => (chk_unfolded phi X1; chk_unfolded phi X2)
             | _ => ()) ;
          if is_intro
          then ToA_reasoner phi ctxt sequent
          else SHu_reasoner ctxt sequent
      )) ctxt

fun gen_SH is_intro hint0 (phi0 : phi_type) generic =
  let val _ = assert_Type_Opr "Separation_Homo" (Term.fastype_of (#term phi0))
      val ctxt0 = Context.proof_of generic
      val phi0pr = make_phi_for_pair generic phi0
      val unify_hint_SH = hint_unify_by_type_operator (
            fn Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, _) $ _ $ _ $ F $ _ => F
             | Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, _) $ _ $ _ $ F $ _ => F
             | _ => raise TERM ("",[]))
      val ind_conv_z = default_ind_conv (
            fn ctxt => fn phi =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHz_rewr_IH}) then_conv
                Phi_Conv.meta_alls_conv (fn ctxt =>
                Conv.implies_concl_conv (Conv.implies_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                ) Conv.all_conv
               )) ctxt,
            fn ctxt => fn phi =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHz_rewr_C}) then_conv
                Conv.implies_concl_conv (
                  HOLogic.Trueprop_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                ))
            )
      val ind_conv_u = default_ind_conv (
            fn ctxt => fn phi =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHu_rewr_IH}),
            fn ctxt => fn phi =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHu_rewr_C}) then_conv
                Conv.implies_concl_conv (
                  HOLogic.Trueprop_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                ))
            )
      val ind_conv = if is_intro then ind_conv_z else ind_conv_u
      fun simp (phi, ctxt) =
            Conv.fconv_rule (
              Phi_Conv.hhf_concl_conv (K (
                  Conv.arg_conv (Conv.combination_conv
                    (Conv.arg_conv (Simplifier.rewrite ctxt))
                    (Simplifier.rewrite ctxt))
             )) ctxt)

      val rules = mk_rule_by_guess_or_hint (if is_intro then "/SHz" else "/SHu",
                                            unify_hint_SH, guess_property_SH is_intro, [0,~1,~1],
                                            ind_conv, SH_reasoning is_intro, K NONE, simp)
                                           (if is_intro then @{thm' \<phi>TA_SHz_rule} else @{thm' \<phi>TA_SHu_rule})
                                           phi0pr hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail
         | SOME (rule', _) => generic
             |> Phi_Type_Algebra.note_properties phi0
                    [(if is_intro then "sep_homo\<^sub>I" else "sep_homo\<^sub>E", [rule'])]
             |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.NORMAL 40 ([],[]) NONE
                                              [Morphism.thm m rule'])
  end

val separation_homo_I = accept_one "Separation_Homo\<^sub>I" (gen_SH true)
val separation_homo_E = accept_one "Separation_Homo\<^sub>E" (gen_SH false)

(*** Identity Element Intro \& Elim ***)

fun guess_id_ele (typ as TFree (_, S)) ctxt =
      if Sign.subsort (Proof_Context.theory_of ctxt) (S, \<^sort>\<open>one\<close>)
      then (TVars.empty, \<^Const>\<open>one_class.one typ\<close>, ctxt)
      else raise Automation_Fail
  | guess_id_ele (typ as TVar (_, S)) ctxt =
      let val env  = Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (typ, \<^sort>\<open>one\<close>) Vartab.empty
                     handle TYPE _ => raise Automation_Fail
          val inst = Phi_Help.tyenv_to_tvars_table ctxt env
          val typ' = Term_Subst.instantiateT (Phi_Help.ty_table_no_c inst) typ
       in (inst, \<^Const>\<open>one_class.one typ'\<close>, ctxt)
      end
  | guess_id_ele typ ctxt =
  let val ((inst, unit_simp) :: _, ctxt') =
            BNF_FP_Sugar_More.identity_element_unify typ (Context.Proof ctxt)
      val unit = case Thm.concl_of unit_simp
                   of _ (*Trueprop*) $ (_ (*eq*) $ LHS $ _) => LHS
   in (inst, unit,
       Context.the_proof (Simps.map (fn ctxt => ctxt addsimps [unit_simp]) ctxt'))
  end

fun guess_property_id_ele is_left (x_term0, T_term0, (phi0:phi_type)) ctxt =
  let val (_,x_ty0,model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val inst0  = Vartab.empty
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (x_ty0, \<^sort>\<open>one\<close>)
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (model_ty0, \<^sort>\<open>one\<close>)
                   handle TYPE _ => raise Automation_Fail
      val inst = Phi_Help.tyenv_to_tvars_table_no_c inst0
      val inst' = TVars.map (K (Thm.ctyp_of ctxt)) inst
      val phi01 = instantiate_phi (inst',Vars.empty) phi0
      val subst = Term_Subst.instantiate (inst, Vars.empty)
      val (x_term01, T_term01) = (subst x_term0, subst T_term0)

      val (_, x_ty01, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi01))
      val (inst01, unit, ctxt) = guess_id_ele x_ty01 ctxt
      val subst01 = Term_Subst.instantiate (Phi_Help.ty_table_no_c inst01, Vars.empty)
      val phi = instantiate_phi (inst01, Vars.empty) phi01
      val (x_term, T_term) = (subst01 x_term01, subst01 T_term01)

      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun mk_P ctxt = if is_left
                      then Variable.add_fixes (Name.invent (Variable.names_of ctxt) "P" 1) ctxt
                      else ([""], ctxt)
      val thy = Proof_Context.theory_of ctxt
      fun mk_Ants (Ty::rev_arg_tys) ants (T_term $ A) ctxt =
       (let val (rev_arg_tys_A, x_ty_A, model_ty_A) = dest_parameterized_phi_ty Ty
         in if Sign.of_sort thy (x_ty_A, \<^sort>\<open>one\<close>)
            then let
                  val arity_A = length rev_arg_tys_A
                  val ([P], ctxt') = mk_P ctxt
                  val xA = \<^Const>\<open>\<phi>Type x_ty_A model_ty_A\<close> $ \<^Const>\<open>one_class.one x_ty_A\<close> $ A
                  val ant = (Term.incr_bv (arity_A, 0, xA))
                          |> fold_index (fn (i,_) => fn X => X $ Bound (arity_A-1-i)) rev_arg_tys_A
                          |> (fn X => (if is_left then \<^Const>\<open>Identity_Element\<^sub>I model_ty_A\<close> $ X $ Free(P, HOLogic.boolT)
                                                  else \<^Const>\<open>Identity_Element\<^sub>E model_ty_A\<close> $ X))
                          |> fold (fn T => fn X =>
                                  Const(\<^const_name>\<open>All\<close>, (T --> HOLogic.boolT) --> HOLogic.boolT)
                                    $ Abs("",T,X)
                                 ) rev_arg_tys_A
               in mk_Ants rev_arg_tys (ant::ants) T_term ctxt'
              end
            else mk_Ants rev_arg_tys ants T_term ctxt
        end handle TYPE _ => mk_Ants rev_arg_tys ants T_term ctxt)
        | mk_Ants [] ants _ ctxt = (ants, ctxt)
        | mk_Ants _ _ _ _ = raise ListPair.UnequalLengths
      val (ants, ctxt) = mk_Ants rev_arg_tys [] T_term ctxt
      val ant = Phi_Help.list_mk_conj ants
      val xT = \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ unit $ T_term
   in Seq.single (ant, \<^Const>\<open>Trueprop\<close> $ (
        (if is_left then \<^Const>\<open>Identity_Element\<^sub>I model_ty\<close> $ xT $ Var(("P", 0), HOLogic.boolT)
                    else \<^Const>\<open>Identity_Element\<^sub>E model_ty\<close> $ xT)),
        x_term, T_term, phi,
        ctxt)
  end

fun gen_id_ele is_left hint0 (phi0 : phi_type) generic =
  let val ctxt0 = Context.proof_of generic 
      val name = if is_left then "1L" else "1R"
      val unify_hint_U = hint_unify_by_type (
            fn Const(\<^const_name>\<open>Identity_Element\<^sub>I\<close>, _) $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ T) $ _ => T
             | Const(\<^const_name>\<open>Identity_Element\<^sub>E\<close>, _) $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ T) => T
             | _ => raise TERM ("",[]))
      val ind_conv = default_ind_conv (K (K Conv.all_conv),
                       fn ctxt => fn _ =>
                            HOLogic.Trueprop_conv (Conv.rewr_conv @{thm Action_Tag_def}) then_conv
                            Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0)))
      val varify_subgoal = if is_left
            then (fn Trueprop $ (Identity_Element $ S $ P) =>
                        SOME ([P], fn [P'] => Trueprop $ (Identity_Element $ S $ P')))
            else K NONE
      fun reasoning _ = gen_abstract_constraint_guided_reasoning varify_subgoal (PLPR_reasoner (SOME 1))
      fun simp (phi, ctxt) = Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
            HOLogic.Trueprop_conv (
              if is_left
              then Conv.combination_conv (Conv.arg_conv (Simplifier.rewrite ctxt))
                                         (Simplifier.rewrite ctxt)
              else Conv.arg_conv (Simplifier.rewrite ctxt)
            )) ctxt)
      val rules = mk_rule_by_guess_or_hint (name, unify_hint_U, guess_property_id_ele is_left, [],
                                            ind_conv, reasoning, K NONE, simp)
                                           (if is_left then @{thm' \<phi>TA_1L_rule} else @{thm' \<phi>TA_1R_rule})
                                           phi0 hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail
         | SOME (rule', _) => generic
            |> Phi_Type_Algebra.note_properties phi0
                  [((if is_left then "identity_element\<^sub>I" else "identity_element\<^sub>E"), [rule'])]
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.NORMAL 40 ([],[]) NONE
                                              [Morphism.thm m rule'])
  end

val identity_element_I = accept_one "Identity_Element\<^sub>I" (gen_id_ele true)
val identity_element_E = accept_one "Identity_Element\<^sub>E" (gen_id_ele false)

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