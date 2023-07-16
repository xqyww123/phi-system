signature eBNF_INFO = sig

type quasi_BNF = {
  T : typ,
  ctrs : term list,
  deads: typ list,
  lives: typ list, (*source type variables of map*)
  lives': typ list,(*target type variables of map*)
  sets : term list,
  set_thms : thm list,
  ctr_simps: thm list,
  rel: term,
  rel_distincts: thm list,
  rel_injects: thm list,
  rel_eq: thm,
  pred: term,
  pred_injects: thm list,
  pred_simps: thm list,
  map: term,
  map_thms: thm list,
  map_disc_iffs: thm list,
  map_ident: thm
}

type eBNF

val add_BNF : string * quasi_BNF -> Context.generic -> Context.generic

val get_bnf  : Context.generic -> string -> eBNF option
val get_bnf1 : Context.generic -> string -> eBNF

val classify_bnf_dead_live : eBNF -> typ list -> typ list * typ list (*classify the type parameters into dead and live
                                                                       as that in Isabelle BNF lib*)
val burrow_bnf_dead_live : eBNF -> typ list * typ list -> typ list (*the inverse function of classify_dead_live*)

val ctrs_of : eBNF -> term list
val sets_of_bnf : eBNF -> term list
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

val global_simps_of_rel : eBNF -> thm list
val global_simps_of_rel_safe : eBNF -> thm list

val simps_of_pred : eBNF -> thm list
val simps_of_pred_safe : eBNF -> thm list

val simps_of_map : eBNF -> thm list
val simps_of_map_safe : eBNF -> thm list

val global_simps_of_map : eBNF -> thm list
val global_simps_of_map_safe : eBNF -> thm list

val global_simps_of_pred : eBNF -> thm list
val global_simps_of_pred_safe : eBNF -> thm list

end

structure eBNF_Info : eBNF_INFO = struct

open Phi_Type_Algebra

type quasi_BNF = {
  T : typ,
  ctrs : term list,
  deads: typ list,
  lives: typ list, (*source type variables of map*)
  lives': typ list,(*target type variables of map*)
  sets : term list,
  set_thms : thm list,
  ctr_simps: thm list,
  rel: term,
  rel_distincts: thm list,
  rel_injects: thm list,
  rel_eq: thm,
  pred: term,
  pred_injects: thm list,
  pred_simps: thm list,
  map: term,
  map_thms: thm list,
  map_disc_iffs: thm list,
  map_ident: thm
}

datatype eBNF =  BNF of string * BNF_Def.bnf option
                               * BNF_FP_Def_Sugar.fp_sugar option
                               * Ctr_Sugar.ctr_sugar option
              | qBNF of quasi_BNF

(* Data *)

structure qBNFs = Generic_Data (
  type T = quasi_BNF Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

val add_BNF = qBNFs.map o Symtab.update_new

(* Library *)

fun g_bnf (Tname, NONE, _, _) =
      raise Automation_Fail ("BNF info for type " ^ Tname ^ " is not found.\n\
                             \May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>")
  | g_bnf (_, SOME bnf, _, _) = bnf

fun g_fp (Tname, _, NONE, _) =
      raise Automation_Fail ("BNF_FP for type " ^ Tname ^ " is not found.\n\
                             \May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>")
  | g_fp (_, _, SOME fp, _) = fp

fun g_ctr (Tname, _, _, NONE) =
      raise Automation_Fail ("Constructor Info for type " ^ Tname ^ " is not found.\n\
                             \May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>")
  | g_ctr (_, _, _, SOME ctr) = ctr

fun T_of_bnf (BNF bnf)  = BNF_Def.T_of_bnf (g_bnf bnf)
  | T_of_bnf (qBNF bnf) = #T bnf

fun deads_of_bnf (BNF bnf) = BNF_Def.deads_of_bnf (g_bnf bnf)
  | deads_of_bnf (qBNF bnf) = #deads bnf

fun lives_of_bnf (BNF bnf) = BNF_Def.lives_of_bnf (g_bnf bnf)
  | lives_of_bnf (qBNF bnf) = #lives bnf

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
        Context.cases Ctr_Sugar.ctr_sugar_of_global Ctr_Sugar.ctr_sugar_of ctxt Tname)
    of (NONE, NONE, NONE) => NONE
     | (a,b,c) => let
            val c' = case (b,c) of (_, SOME c') => SOME c'
                                 | (SOME b', _) => SOME (#ctr_sugar (#fp_ctr_sugar b'))
                                 | _ => NONE
         in SOME (BNF (Tname,a,b,c'))
        end)

fun get_bnf1 ctxt Tname =
  case get_bnf ctxt Tname
    of SOME ret => ret
     | NONE => raise Automation_Fail ("Type " ^ Tname ^ " is not a known BNF.\n\
                                      \May register the required infos using \<open>setup \<open>eBNF_Info.add_BNF data\<close>\<close>")


fun sets_of_bnf (BNF bnf) = BNF_Def.sets_of_bnf (g_bnf bnf)
  | sets_of_bnf (qBNF bnf) = #sets bnf

fun mk_sets_of_bnf Dss Tss (BNF bnf) = BNF_Def.mk_sets_of_bnf Dss Tss (g_bnf bnf)
  | mk_sets_of_bnf Dss Tss (qBNF qbnf) =
      map2 (fn (Ds, Ts) => Term.subst_atomic_types
        ((#deads qbnf ~~ Ds) @ (#lives qbnf ~~ Ts))) (Dss ~~ Tss) (#sets qbnf)

fun mk_rel_of_bnf Ds Ts Us (BNF bnf) = BNF_Def.mk_rel_of_bnf Ds Ts Us (g_bnf bnf)
  | mk_rel_of_bnf Ds Ts Us (qBNF bnf) =
      Term.subst_atomic_types
        ((#deads bnf ~~ Ds) @ (#lives bnf ~~ Ts) @ (#lives' bnf ~~ Us)) (#rel bnf)

fun mk_pred_of_bnf Ds Ts (BNF bnf) = BNF_Def.mk_pred_of_bnf Ds Ts (g_bnf bnf)
  | mk_pred_of_bnf Ds Ts (qBNF bnf) =
      Term.subst_atomic_types
        ((#deads bnf ~~ Ds) @ (#lives bnf ~~ Ts)) (#pred bnf)

fun mk_map_of_bnf Ds Ts Us (BNF bnf) = BNF_Def.mk_map_of_bnf Ds Ts Us (g_bnf bnf)
  | mk_map_of_bnf Ds Ts Us (qBNF bnf) =
      Term.subst_atomic_types
        ((#deads bnf ~~ Ds) @ (#lives bnf ~~ Ts) @ (#lives' bnf ~~ Us)) (#map bnf)

fun ctrs_of (BNF bnf) = #ctrs (g_ctr bnf)
  | ctrs_of (qBNF bnf)= #ctrs bnf


(* Simplification rules *)

fun ctr_sugar_simps (ctr : Ctr_Sugar.ctr_sugar) =
  #injects ctr @ #distincts ctr @ #case_thms ctr @ flat (#sel_thmss ctr)

fun simps_of_ctr (BNF bnf) = ctr_sugar_simps (g_ctr bnf)
  | simps_of_ctr (qBNF bnf) = #ctr_simps bnf

fun simps_of_ctr_safe (BNF (_,_,_,SOME c)) = ctr_sugar_simps c
  | simps_of_ctr_safe (BNF (_,_,_,NONE)) = []
  | simps_of_ctr_safe (qBNF bnf) = #ctr_simps bnf

fun simps_of_set (BNF bnf) = #set_thms (#fp_bnf_sugar (g_fp bnf))
  | simps_of_set (qBNF bnf) = #set_thms bnf

fun simps_of_set_safe (BNF (_,_,SOME fp,_)) = #set_thms (#fp_bnf_sugar fp)
  | simps_of_set_safe (BNF (_,_,NONE,_)) = []
  | simps_of_set_safe (qBNF bnf) = #set_thms bnf

fun simps_of_rel (BNF bnf) = #rel_distincts (#fp_bnf_sugar (g_fp bnf))
                           @ #rel_injects (#fp_bnf_sugar (g_fp bnf))
  | simps_of_rel (qBNF bnf) = #rel_distincts bnf @ #rel_injects bnf

fun simps_of_rel_safe (BNF (_,_,SOME fp,_)) = #rel_distincts (#fp_bnf_sugar fp)
                                            @ #rel_injects (#fp_bnf_sugar fp)
  | simps_of_rel_safe (BNF (_,_,NONE,_)) = []
  | simps_of_rel_safe (qBNF bnf) = #rel_distincts bnf @ #rel_injects bnf

fun global_simps_of_rel (BNF bnf) = [BNF_Def.rel_eq_of_bnf (g_bnf bnf)]
  | global_simps_of_rel (qBNF bnf)= [#rel_eq bnf]

fun global_simps_of_rel_safe (BNF (_,SOME bnf,_,_)) = [BNF_Def.rel_eq_of_bnf bnf]
  | global_simps_of_rel_safe (BNF (_,NONE,_,_)) = []
  | global_simps_of_rel_safe (qBNF bnf)= [#rel_eq bnf]

fun simps_of_pred (BNF bnf) = #pred_injects (#fp_bnf_sugar (g_fp bnf))
  | simps_of_pred (qBNF bnf) = #pred_injects bnf @ #pred_simps bnf

fun simps_of_pred_safe (BNF (_,_,SOME fp,_)) = #pred_injects (#fp_bnf_sugar fp)
  | simps_of_pred_safe (BNF (_,_,NONE,_)) = []
  | simps_of_pred_safe (qBNF bnf) = #pred_injects bnf

fun simps_of_map (BNF bnf) = #map_thms (#fp_bnf_sugar (g_fp bnf))
                           @ #map_disc_iffs (#fp_bnf_sugar (g_fp bnf))
  | simps_of_map (qBNF bnf) = #map_thms bnf @ #map_disc_iffs bnf

fun simps_of_map_safe (BNF (_,_,SOME fp,_)) = #map_thms (#fp_bnf_sugar fp)
                                            @ #map_disc_iffs (#fp_bnf_sugar fp)
  | simps_of_map_safe (BNF (_,_,NONE,_)) = []
  | simps_of_map_safe (qBNF bnf) = #map_thms bnf @ #map_disc_iffs bnf

fun global_simps_of_map (BNF bnf) = [BNF_Def.map_ident_of_bnf (g_bnf bnf)]
  | global_simps_of_map (qBNF bnf)= [#map_ident bnf]

fun global_simps_of_map_safe (BNF (_,SOME bnf,_,_)) = [BNF_Def.map_ident_of_bnf bnf]
  | global_simps_of_map_safe (BNF (_,NONE,_,_)) = []
  | global_simps_of_map_safe (qBNF bnf)= [#map_ident bnf]

fun global_simps_of_pred (BNF bnf) = [BNF_Def.pred_True_of_bnf (g_bnf bnf)]
  | global_simps_of_pred (qBNF bnf)= [#map_ident bnf]

fun global_simps_of_pred_safe (BNF (_,SOME bnf,_,_)) = [BNF_Def.pred_True_of_bnf bnf]
  | global_simps_of_pred_safe (BNF (_,NONE,_,_)) = []
  | global_simps_of_pred_safe (qBNF bnf)= [#map_ident bnf]


(*
fun mk_sets_of_bnf Dss Tss (BNF bnf) = BNF_Def.mk_sets_of_bnf Dss Tss
  | *)

(*val mk_sets_of_bnf: typ list list -> typ list list -> eBNF -> term list*)

(* fun permute_seq (s::L) =
      Seq.maps (fn s' => permute_seq L |> Seq.map (fn L' => s'::L')) s
  | permute_seq [] = Seq.single [] *)
(*
fun gen_guess_operator mk_term is_live mk_operator_for_dead atom_opr =
  let fun guess_operator' ctxt known_oprs x_ty =
        case map_filter (fn (ty', term) => if ty' = x_ty then SOME term else NONE)
                        known_oprs
          of [] => (
            case x_ty
              of Type(Tname, Targs) =>
                   let val bnf = get_bnf1 ctxt Tname
                       val (D,L) = classify_bnf_dead_live bnf Targs
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
                                    ^ Context.cases Syntax.string_of_typ_global Syntax.string_of_typ ctxt x_ty) ;
                            NONE)
                 | some => some )
   in guess
  end
*)

end
