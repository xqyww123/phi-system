signature eBNF_INFO = sig

type quasi_BNF = {
  T : typ,
  Tname : string,
  casex: term option,
  case_distribs: thm list,
  ctrs : term list,
  deads: typ list,
  lives: typ list, (*source type variables of map*)
  lives': typ list,(*target type variables of map*)
  sets : term list,
  set_thms : thm list,
  ctr_simps: thm list,
  rel: term,
  rel_simps: thm list, (*includes distinct rules, inject rules*)
  rel_eq: thm,
  pred: term,
  pred_injects: thm list,
  pred_simps: thm list,
  map: term,
  map_thms: thm list,
  map_disc_iffs: thm list,
  map_ident: thm,
  map_comp_of: thm,
  fp_more : BNF_FP_Sugar_More.fp_more option
}

type eBNF

val add_BNF : string * quasi_BNF -> Context.generic -> Context.generic

val get_bnf  : Context.generic -> string -> eBNF option
val get_bnf1 : Context.generic -> string -> eBNF

val deads_of_bnf : eBNF -> typ list
val lives_of_bnf : eBNF -> typ list
val tyargs_is_live_or_dead : eBNF -> bool list (*if tyargs_is_live_or_dead[i], the i-th type parameter is live*)
val classify_bnf_dead_live : eBNF -> typ list -> typ list * typ list (*classify the type parameters into dead and live
                                                                       as that in Isabelle BNF lib*)
val burrow_bnf_dead_live : eBNF -> typ list * typ list -> typ list (*the inverse function of classify_dead_live*)

val Tname_of : eBNF -> string
val T_of_bnf : eBNF -> typ
val ctrs_of : eBNF -> term list
val case_of : eBNF -> term option
val case_of1 : eBNF -> term
val sets_of_bnf : eBNF -> term list
val sets_of_bnf_safe : eBNF -> term list option
val rel_of_bnf : eBNF -> term
val rel_of_bnf_safe : eBNF -> term option
val pred_of_bnf : eBNF -> term
val pred_of_bnf_safe : eBNF -> term option
val map_of_bnf : eBNF -> term
val map_of_bnf_safe : eBNF -> term option
val fp_more_of : eBNF -> BNF_FP_Sugar_More.fp_more option
val mk_sets_of_bnf: typ list list -> typ list list -> eBNF -> term list
val mk_rel_of_bnf : typ list -> typ list -> typ list -> eBNF -> term
val mk_pred_of_bnf : typ list -> typ list -> eBNF -> term
val mk_map_of_bnf : typ list -> typ list -> typ list -> eBNF -> term

(* Simplification rules *)

val simps_of_ctr : eBNF -> thm list
val simps_of_ctr_safe : eBNF -> thm list

val simps_of_set : eBNF -> thm list
val simps_of_set_safe : eBNF -> thm list

val simps_of_rel : eBNF -> thm list
val simps_of_rel_safe : eBNF -> thm list

val global_simps_of_rel : Context.generic -> eBNF -> thm list
val global_simps_of_rel_safe : Context.generic -> eBNF -> thm list

val simps_of_pred : eBNF -> thm list
val simps_of_pred_safe : eBNF -> thm list

val simps_of_map : eBNF -> thm list
val simps_of_map_safe : eBNF -> thm list

val global_simps_of_map : eBNF -> thm list
val global_simps_of_map_safe : eBNF -> thm list

val global_simps_of_pred : eBNF -> thm list
val global_simps_of_pred_safe : eBNF -> thm list

val case_distribs_of : eBNF -> thm list
val case_distribs_of_safe : eBNF -> thm list

val simps_of_zip : eBNF -> thm list
val simps_of_zip_safe : eBNF -> thm list

(* Rules searched from DB *)

val export_cache : Context.generic -> Context.generic -> Context.generic

val identity_element : eBNF -> Context.generic -> thm list * Context.generic
val identity_element_match : typ -> Context.generic -> thm list * Context.generic
val identity_element_unify : typ -> Context.generic -> (ctyp TVars.table * thm) list * Context.generic

val relator_on_const_true : eBNF -> Context.generic -> thm list * Context.generic
val relator_on_const_true_match : typ -> Context.generic -> thm list * Context.generic
val relator_on_const_true_unify : typ -> Context.generic -> (ctyp TVars.table * thm) list * Context.generic

end

structure eBNF_Info : eBNF_INFO = struct

open Phi_Type

type quasi_BNF = {
  T : typ,
  Tname : string,
  casex: term option,
  case_distribs: thm list,
  ctrs : term list,
  deads: typ list,
  lives: typ list, (*source type variables of map*)
  lives': typ list,(*target type variables of map*)
  sets : term list,
  set_thms : thm list,
  ctr_simps: thm list,
  rel: term,
  rel_simps: thm list,
  rel_eq: thm,
  pred: term,
  pred_injects: thm list,
  pred_simps: thm list,
  map: term,
  map_thms: thm list,
  map_disc_iffs: thm list,
  map_ident: thm,
  map_comp_of: thm,
  fp_more : BNF_FP_Sugar_More.fp_more option
}

datatype eBNF =  BNF of string * BNF_Def.bnf option
                               * BNF_FP_Def_Sugar.fp_sugar option
                               * Ctr_Sugar.ctr_sugar option
                               * BNF_FP_Sugar_More.fp_more option
              | qBNF of quasi_BNF

(* Data *)

structure qBNFs = Generic_Data (
  type T = quasi_BNF Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun add_BNF (Tname, qbnf) =
      qBNFs.map (Symtab.update_new (Tname, qbnf))
   #> (case #fp_more qbnf
         of SOME fpm => BNF_FP_Sugar_More.add_fp_more (Tname, fpm)
          | NONE => I)

(*** Auxiliaries ***)

local open Pretty in

fun err_bnf Tname =
      raise Automation_Fail (fn () => [
              block [str "BNF info for type ", str Tname, str " is not found"],
              str "May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>"])

fun g_bnf (Tname, NONE, _, _, _) = err_bnf Tname
  | g_bnf (_, SOME bnf, _, _, _) = bnf

fun g_fp (Tname, _, NONE, _, _) =
      raise Automation_Fail (fn () => [
              block [str "BNF_FP for type ", str Tname, str " is not found."],
              str "May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>"])
  | g_fp (_, _, SOME fp, _, _) = fp

fun g_ctr (Tname, _, _, NONE, _) =
      raise Automation_Fail (fn () => [
              block [str "Constructor Info for type ", str Tname, str " is not found."],
              str "May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>"])
  | g_ctr (_, _, _, SOME ctr, _) = ctr


fun err_more_fp Tname =
      raise Automation_Fail (fn () => [block [str "extended BNF info is not found on type ", str Tname]])

fun fp_more_of (BNF (_, _,_,_,fpm)) = fpm
  | fp_more_of (qBNF bnf) = #fp_more bnf

end

(*** Basics ***)

(** Basic Info \& Interface **)

fun Tname_of (BNF (Tname, _, _, _, _)) = Tname
  | Tname_of (qBNF bnf) = #Tname bnf 

fun T_of_bnf (BNF (_, SOME bnf, _, _, _)) = BNF_Def.T_of_bnf bnf
  | T_of_bnf (BNF (_, _, SOME fp, _, _)) = #T fp
  | T_of_bnf (BNF (_, _, _, SOME ctr, _)) = #T ctr
  | T_of_bnf (qBNF bnf) = #T bnf
  | T_of_bnf (BNF (Tname, _, _, _, _)) = err_bnf Tname

fun deads_of_bnf (BNF bnf) = BNF_Def.deads_of_bnf (g_bnf bnf)
  | deads_of_bnf (qBNF bnf) = #deads bnf

fun lives_of_bnf (BNF bnf) = BNF_Def.lives_of_bnf (g_bnf bnf)
  | lives_of_bnf (qBNF bnf) = #lives bnf

fun tyargs_is_live_or_dead bnf =
  let val tys = snd (Term.dest_Type (T_of_bnf bnf))
      val deads = deads_of_bnf bnf
   in map (not o member (op =) deads) tys
  end

fun classify_bnf_dead_live bnf tys =
  let val btys = snd (Term.dest_Type (T_of_bnf bnf))
      val deads = deads_of_bnf bnf
      fun classify (t::tys) (bt::btys) =
           (case classify tys btys
              of (D,L) => if member (op =) deads bt then (t::D, L) else (D, t::L))
        | classify [] [] = ([],[])
        | classify _ _ = raise ListPair.UnequalLengths
   in classify tys btys
  end

fun burrow_bnf_dead_live bnf deads_lives = 
  let val btys = snd (Term.dest_Type (T_of_bnf bnf))
      val deads' = deads_of_bnf bnf
      fun burrow (deads,lives) (bt::btys) =
            if member (op =) deads' bt then hd deads :: burrow (tl deads, lives) btys
                                       else hd lives :: burrow (deads, tl lives) btys
        | burrow ([],[]) [] = []
        | burrow _ _ = error "Internal bug: burrow_bnf_dead_live"
   in burrow deads_lives btys
  end

fun get_bnf ctxt Tname =
  case Symtab.lookup (qBNFs.get ctxt) Tname
    of SOME qbnf => SOME (qBNF qbnf)
     | _ => (
  case (Context.cases BNF_Def.bnf_of_global BNF_Def.bnf_of ctxt Tname,
        Context.cases BNF_FP_Def_Sugar.fp_sugar_of_global BNF_FP_Def_Sugar.fp_sugar_of ctxt Tname,
        Context.cases Ctr_Sugar.ctr_sugar_of_global Ctr_Sugar.ctr_sugar_of ctxt Tname,
        BNF_FP_Sugar_More.get_fp_more ctxt Tname)
    of (NONE, NONE, NONE, NONE) => NONE
     | (a,b,c,d) => let
            val c' = case (b,c) of (_, SOME c') => SOME c'
                                 | (SOME b', _) => SOME (#ctr_sugar (#fp_ctr_sugar b'))
                                 | _ => NONE
         in SOME (BNF (Tname,a,b,c',d))
        end)

fun get_bnf1 ctxt Tname =
  case get_bnf ctxt Tname
    of SOME ret => ret
     | NONE => raise Automation_Fail (fn () => let open Pretty in
                  [block [str "Type ", str Tname, str " has no registered BNF info."],
                   str "May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>"]
                  end)

fun get_bnf_of_typ1 ctxt (Type (Tname, _)) = get_bnf1 ctxt Tname
  | get_bnf_of_typ1 _ T = raise TYPE ("Not a constant", [T], [])

(** BNF Operators **)

fun sets_of_bnf (BNF bnf) = BNF_Def.sets_of_bnf (g_bnf bnf)
  | sets_of_bnf (qBNF bnf) = #sets bnf
fun sets_of_bnf_safe bnf = SOME (sets_of_bnf bnf) handle Automation_Fail _ => NONE

fun mk_sets_of_bnf Dss Tss (BNF bnf) = BNF_Def.mk_sets_of_bnf Dss Tss (g_bnf bnf)
  | mk_sets_of_bnf Dss Tss (qBNF qbnf) =
      map2 (fn (Ds, Ts) => Term.subst_atomic_types
        ((#deads qbnf ~~ Ds) @ (#lives qbnf ~~ Ts))) (Dss ~~ Tss) (#sets qbnf)

fun rel_of_bnf (BNF bnf) = BNF_Def.rel_of_bnf (g_bnf bnf)
  | rel_of_bnf (qBNF bnf) = #rel bnf
fun rel_of_bnf_safe bnf = SOME (rel_of_bnf bnf) handle Automation_Fail _ => NONE

fun mk_rel_of_bnf Ds Ts Us (BNF bnf) = BNF_Def.mk_rel_of_bnf Ds Ts Us (g_bnf bnf)
  | mk_rel_of_bnf Ds Ts Us (qBNF bnf) =
      Term.subst_atomic_types
        ((#deads bnf ~~ Ds) @ (#lives bnf ~~ Ts) @ (#lives' bnf ~~ Us)) (#rel bnf)

fun pred_of_bnf (BNF bnf) = BNF_Def.pred_of_bnf (g_bnf bnf)
  | pred_of_bnf (qBNF bnf) = #pred bnf
fun pred_of_bnf_safe bnf = SOME (pred_of_bnf bnf) handle Automation_Fail _ => NONE

fun mk_pred_of_bnf Ds Ts (BNF bnf) = BNF_Def.mk_pred_of_bnf Ds Ts (g_bnf bnf)
  | mk_pred_of_bnf Ds Ts (qBNF bnf) =
      Term.subst_atomic_types
        ((#deads bnf ~~ Ds) @ (#lives bnf ~~ Ts)) (#pred bnf)

fun map_of_bnf (BNF bnf) = BNF_Def.map_of_bnf (g_bnf bnf)
  | map_of_bnf (qBNF bnf) = #map bnf
fun map_of_bnf_safe bnf = SOME (map_of_bnf bnf) handle Automation_Fail _ => NONE

fun mk_map_of_bnf Ds Ts Us (BNF bnf) = BNF_Def.mk_map_of_bnf Ds Ts Us (g_bnf bnf)
  | mk_map_of_bnf Ds Ts Us (qBNF bnf) =
      Term.subst_atomic_types
        ((#deads bnf ~~ Ds) @ (#lives bnf ~~ Ts) @ (#lives' bnf ~~ Us)) (#map bnf)

fun ctrs_of (BNF bnf) = #ctrs (g_ctr bnf)
  | ctrs_of (qBNF bnf)= #ctrs bnf

fun case_of (BNF bnf) = SOME (#casex (g_ctr bnf))
  | case_of (qBNF bnf)= #casex bnf

fun case_of1 bnf = case case_of bnf of SOME X => X | NONE =>
      raise Automation_Fail (fn () =>
              [Pretty.str "No case-split operator given for type ", Pretty.str (Tname_of bnf)])


(*** Search From DB ***)

(*BNF package and relatives do not always provide what all we need. We can search by pattern match
  from the data base of all lemmas in Isabelle. *)

structure Caches = Generic_Data (
  type T = (typ * thm) list Symreltab.table
  val empty = Symreltab.empty
  val merge = Symreltab.merge (K true)
)

fun export_cache from to = Caches.put (Caches.get from) to

fun gen_property inst kind get_bnf gen arg generic =
  let val thy = Context.theory_of generic
      val bnf = get_bnf generic arg
      val Tname = Tname_of bnf
      val mpf = map_filter (inst thy arg)
   in case Symreltab.lookup (Caches.get generic) (Tname,kind)
        of SOME ths =>
            (mpf (map (apsnd (Thm.transfer'' generic)) ths), generic)
         | NONE =>
            let val res = gen bnf generic
             in (mpf res, Caches.map (Symreltab.update_new ((Tname,kind), res)) generic)
            end
  end

fun no_inst _ _ (_, th) = SOME th

fun typ_inst_by_match thy tyb (tya, th) =
  Sign.typ_match thy (tya,tyb) Vartab.empty
   |> Phi_Help.subst_tyenv
   |> Phi_Help.certify_tyvars (Context.Theory thy)
   |> (fn inst => SOME (Thm.instantiate (inst, Vars.empty) th))
  handle Type.TYPE_MATCH => NONE

fun typ_inst_by_unify thy tyb (tya0,th0) =
  let val idx = Term.maxidx_of_typ tyb + 1
      val tya = Logic.incr_tvar idx tya0
      val th = Thm.incr_indexes idx th0
   in fst (Sign.typ_unify thy (tya,tyb) (Vartab.empty, Term.maxidx_of_typ tya + 1))
   |> Phi_Help.norm_tyenv
   |> Phi_Help.certify_tyvars (Context.Theory thy)
   |> (fn inst => SOME (inst, Thm.instantiate (inst, Vars.empty) th))
   handle Type.TUNIFY => NONE
  end

(* DO NOT REMOVE
fun chk_search_result1 ctxt pattern [] =
      error ("No existing theorems found for " ^ Syntax.string_of_term ctxt pattern)
  | chk_search_result1 _ _ [x] = [x]
  | chk_search_result1 ctxt pattern L = let open Pretty in
        error (string_of (chunks (
            block [str "More than one existing theorems found for ", Syntax.pretty_term ctxt pattern] ::
            map (fn th => item [Syntax.pretty_term ctxt (Thm.prop_of th)]) L
          )))
      end*)


fun mk_typ_of_sort thy (Tname,sort) =
  let val sorts = Sign.arity_sorts thy Tname sort
      val ty_args = map_index (fn (i,S) => TVar(("x",i),S)) sorts
   in Type(Tname, ty_args)
  end


(** Unit \<open>1 \<equiv> ?\<close> **)

fun made_of_ctrs ty chk_ctrs (Const(N, TY)) =
     (case body_type TY
        of Type (TN, _) => if TN = ty then chk_ctrs N else true
         | _ => true)
  | made_of_ctrs ty chk_ctrs (X $ Y) = made_of_ctrs ty chk_ctrs X andalso made_of_ctrs ty chk_ctrs Y
  | made_of_ctrs ty chk_ctrs (Abs(_,_,X)) = made_of_ctrs ty chk_ctrs X
  | made_of_ctrs _ _ _ = true

fun gen_unit_simps bnf ctxt0 =
  let val Tname = Tname_of bnf
      val ctxt = Context.proof_of ctxt0
      val ty = mk_typ_of_sort (Context.theory_of ctxt0) (Tname, \<^sort>\<open>one\<close>)
      val pattern = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.eq ty\<close> $ \<^Const>\<open>one_class.one ty\<close> $ Var(("uu",0),ty))
      val ctrs = fold (fn Const(N,_) => Symtab.insert_set N
                        | _ => I) (ctrs_of bnf) Symtab.empty
              |> Symtab.defined
   in Find_Theorems.find_theorems ctxt NONE NONE true [(true, Find_Theorems.Pattern pattern)]
   |> snd
   |> map_filter (fn (_, th) => case Thm.prop_of th
                                  of _ (*Trueprop*) $ (_ (*eq*) $ _ $ RHS) =>
                                      if made_of_ctrs Tname ctrs RHS
                                      then SOME th
                                      else NONE
                                   | _ => NONE)
   (*|> chk_search_result1 ctxt pattern*)
   |> map (fn th => case Thm.concl_of th
                      of _ (*Trueprop*) $ (_ (*eq*) $ LHS $ _) => (Term.fastype_of LHS, th)
                       | _ => error "BUG")
  end

val identity_element = gen_property no_inst "one" (K I) gen_unit_simps
val identity_element_match = gen_property typ_inst_by_match "one" get_bnf_of_typ1 gen_unit_simps
val identity_element_unify = gen_property typ_inst_by_unify "one" get_bnf_of_typ1 gen_unit_simps

(** Relator on Constant True **)

fun gen_relator_const_true bnf ctxt =
  let val rel = rel_of_bnf bnf
      fun drop_last2 L = List.take (L, length L - 2)
      val rel = rel
             |> fold (fn \<^Type>\<open>fun T \<^Type>\<open>fun U \<^Type>\<open>bool\<close>\<close>\<close> => fn X => X $ Abs ("_", T, Abs ("_", U, \<^Const>\<open>True\<close>)))
                     (drop_last2 (Term.binder_types (Term.fastype_of rel)))
      val rel_ty = Term.fastype_of rel
      val pattern = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.eq rel_ty\<close> $ rel $ Var (("exp", 0), rel_ty))
      val pattern'= \<^Const>\<open>Pure.eq rel_ty\<close> $ rel $ Var (("exp", 0), rel_ty)
   in ( snd (Find_Theorems.find_theorems (Context.proof_of ctxt) NONE NONE true
                                        [(true, Find_Theorems.Pattern pattern )])
      @ snd (Find_Theorems.find_theorems (Context.proof_of ctxt) NONE NONE true
                                        [(true, Find_Theorems.Pattern pattern')]))
   |> map (fn (_, th) => case Thm.concl_of th
                           of _ $ (Const(\<^const_name>\<open>HOL.eq\<close>, \<^Type>\<open>fun T _\<close>) $ _ $ _) => (T, th)
                            | Const(\<^const_name>\<open>Pure.eq\<close>, \<^Type>\<open>fun T _\<close>) $ _ $ _ => (T, th)
                            | _ => error "BUG")
  end


val relator_on_const_true = gen_property no_inst "relator_on_const_True" (K I) gen_relator_const_true
val relator_on_const_true_match =
      gen_property typ_inst_by_match "relator_on_const_True" get_bnf_of_typ1 gen_relator_const_true
val relator_on_const_true_unify =
      gen_property typ_inst_by_unify "relator_on_const_True" get_bnf_of_typ1 gen_unit_simps

(*** Simplification rules ***)

fun ctr_sugar_simps (ctr : Ctr_Sugar.ctr_sugar) =
  #injects ctr @ #distincts ctr @ #case_thms ctr @ flat (#sel_thmss ctr)

fun simps_of_ctr (BNF bnf) = ctr_sugar_simps (g_ctr bnf)
  | simps_of_ctr (qBNF bnf) = #ctr_simps bnf
fun simps_of_ctr_safe bnf = simps_of_ctr bnf handle Automation_Fail _ => []

fun simps_of_set (BNF bnf) = #set_thms (#fp_bnf_sugar (g_fp bnf))
  | simps_of_set (qBNF bnf) = #set_thms bnf
fun simps_of_set_safe bnf = simps_of_set bnf handle Automation_Fail _ => []

fun simps_of_rel (BNF bnf) = #rel_distincts (#fp_bnf_sugar (g_fp bnf))
                           @ #rel_injects (#fp_bnf_sugar (g_fp bnf))
  | simps_of_rel (qBNF bnf) = #rel_simps bnf
fun simps_of_rel_safe bnf = simps_of_rel bnf handle Automation_Fail _ => []

(*lemma
  \<open>(=) = (\<lambda>x y. y = x)\<close>
  by blast*)

(*converts arguments and leaves the head untouched*)
fun args_conv cv ctm =
  case Thm.term_of ctm of _ $ _ => Conv.combination_conv (args_conv cv) cv ctm
                        | _ => cv ctm

(*
fun myrewr_conv rule ct =
  let
    val rule1 = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule;
    val lhs = Thm.lhs_of rule1;
    val rule2 = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule1;
    val rule3 =
      Thm.instantiate (Thm.match (lhs, ct)) rule2
        handle Pattern.MATCH => raise CTERM ("rewr_conv", [lhs, ct]);
    val rule4 =
      if Thm.lhs_of rule3 aconvc ct then rule3
      else
        let val ceq = Thm.dest_fun2 (Thm.cprop_of rule3)
        in rule3 COMP Thm.trivial (Thm.mk_binop ceq ct (Thm.rhs_of rule3)) end;
  in Thm.transitive rule4 (Thm.beta_conversion true (Thm.rhs_of rule4)) end;
*)

val flip_eq = Phi_Conv.LHS_conv (args_conv (fn ctm =>
      case Thm.term_of ctm
        of Const(\<^const_name>\<open>HOL.eq\<close>, _) =>
              Conv.rewr_conv @{lemma' \<open>(=) \<equiv> (\<lambda>x y. y = x)\<close> by (unfold atomize_eq, blast)} ctm
         | _ => Conv.all_conv ctm))
fun flip_eq' th = Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of th) flip_eq) th


fun global_simps_of_rel ctxt (BNF bnf) =
        [ BNF_Def.rel_eq_of_bnf (g_bnf bnf),
          flip_eq' (Thm.transfer'' ctxt (BNF_Def.rel_eq_of_bnf (g_bnf bnf))) ]
  | global_simps_of_rel ctxt (qBNF bnf) =
        [ #rel_eq bnf, flip_eq' (Thm.transfer'' ctxt (#rel_eq bnf)) ]

fun global_simps_of_rel_safe ctxt bnf = global_simps_of_rel ctxt bnf handle Automation_Fail _ => []

fun simps_of_pred (BNF (_,bnf,fp,_,_)) =
        the_default [] (Option.map (#pred_injects o #fp_bnf_sugar) fp)
      @ the_default [] (Option.map (single o BNF_Def.pred_True_of_bnf) bnf)
  | simps_of_pred (qBNF bnf) = #pred_injects bnf @ #pred_simps bnf
val simps_of_pred_safe = simps_of_pred

fun simps_of_map (BNF bnf) = #map_thms (#fp_bnf_sugar (g_fp bnf))
                           @ #map_disc_iffs (#fp_bnf_sugar (g_fp bnf))
                           @ [BNF_Def.map_comp_of_bnf (g_bnf bnf)]
  | simps_of_map (qBNF bnf) = #map_thms bnf @ #map_disc_iffs bnf
                            @ [#map_comp_of bnf]

fun simps_of_map_safe x = simps_of_map x
                          handle Automation_Fail _ => []

fun global_simps_of_map (BNF bnf) = [BNF_Def.map_ident_of_bnf (g_bnf bnf)]
  | global_simps_of_map (qBNF bnf)= [#map_ident bnf]
fun global_simps_of_map_safe bnf = global_simps_of_map bnf handle Automation_Fail _ => []

fun global_simps_of_pred (BNF bnf) = [BNF_Def.pred_True_of_bnf (g_bnf bnf)]
  | global_simps_of_pred (qBNF bnf)= [#map_ident bnf]
fun global_simps_of_pred_safe bnf = global_simps_of_pred bnf handle Automation_Fail _ => []

fun case_distribs_of (BNF bnf) = #case_distribs (g_ctr bnf)
  | case_distribs_of (qBNF bnf) = #case_distribs bnf
fun case_distribs_of_safe bnf = case_distribs_of bnf handle Automation_Fail _ => []

fun simps_of_zip_safe bnf =
      case fp_more_of bnf of SOME more => #zip_simps more
         | NONE => []
fun simps_of_zip bnf =
      case fp_more_of bnf of SOME more => #zip_simps more
         | NONE => err_more_fp (Tname_of bnf)

end
