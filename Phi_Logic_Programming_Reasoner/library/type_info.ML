signature TYPE_INFO = sig

type type_info = {
      name: string,
      properties: Type_Info_DB.properties,
      bnf:  BNF_Def.bnf option,
      fp_sugar: BNF_FP_Def_Sugar.fp_sugar option,
      ctr_sugar: Ctr_Sugar.ctr_sugar option
}

val get_info : {load_bnf: bool, load_bnf_fp: bool, load_ctr: bool}
            -> Context.generic -> string -> type_info option

val get_info1: {load_bnf: bool, load_bnf_fp: bool, load_ctr: bool}
            -> Context.generic -> string -> type_info

val deads_of_bnf : type_info -> typ list
val lives_of_bnf : type_info -> typ list
val tyargs_is_live_or_dead : type_info -> bool list (*if tyargs_is_live_or_dead[i], the i-th type parameter is live*)
val classify_bnf_dead_live : type_info -> typ list -> typ list * typ list (*classify the type parameters into dead and live
                                                                       as that in Isabelle BNF lib*)
val burrow_bnf_dead_live : type_info -> typ list * typ list -> typ list (*the inverse function of classify_dead_live*)

val Tname_of : type_info -> string
val T_of_bnf : type_info -> typ
val ctrs_of : type_info -> term list
val ctrs_of_safe : type_info -> term list option
val case_of : type_info -> term
val case_of_safe : type_info -> term option
val sel_of  : type_info -> term list list
val sel_of_safe : type_info -> term list list option
val mk_sels : type_info -> typ list -> term list list
val sets_of_bnf : type_info -> term list
val sets_of_bnf_safe : type_info -> term list option
val rel_of_bnf : type_info -> term
val rel_of_bnf_safe : type_info -> term option
val pred_of_bnf : type_info -> term
val pred_of_bnf_safe : type_info -> term option
val map_of_bnf : type_info -> term
val map_of_bnf_safe : type_info -> term option
val mk_sets_of_bnf: type_info -> typ list list -> typ list list -> term list
val mk_rel_of_bnf : type_info -> typ list -> typ list -> typ list -> term
val mk_pred_of_bnf : type_info -> typ list -> typ list -> term
val mk_map_of_bnf : type_info -> typ list -> typ list -> typ list -> term

(*Tools*)

val is_constructor : Context.generic -> PLPR_Pattern.bv_typs -> term -> bool
val is_selector    : Context.generic -> PLPR_Pattern.bv_typs -> term -> bool

end

structure Type_Info : TYPE_INFO = struct

type type_info = {
      name: string,
      properties: Type_Info_DB.properties,
      bnf:  BNF_Def.bnf option,
      fp_sugar: BNF_FP_Def_Sugar.fp_sugar option,
      ctr_sugar: Ctr_Sugar.ctr_sugar option
}


(*** Auxiliaries ***)

exception Automation_Fail = Phi_Reasoners.Automation_Fail
fun safe_try f x = SOME (f x) handle Automation_Fail _ => NONE

fun unavailable name prop_names (tyinfo:type_info) =
  let open Pretty
   in raise Automation_Fail (fn () =>
        [block ( [str name, brk 1] @ text "for type" @ [brk 1, str (#name tyinfo), brk 1]
               @ text "is not found. May register the absent infos using"),
         block [keyword1 "declare", brk 1, str "[[",
                Binding.pretty Type_Info_DB.type_property_attr_binding, brk 1,
                block (flat (
                  Library.separate [keyword2 "and", brk 1]
                                   (map (fn pname => [block [str pname, brk 1, str "=", brk 1, str "<some value>"]])
                                         prop_names))),
                str "]]"]])
  end

fun g_bnf names G2 G3 (tyinfo:type_info) =
  case G2 (#properties tyinfo)
    of SOME ret => ret
     | NONE => (case #bnf tyinfo of SOME bnf => G3 bnf
                   | NONE => unavailable "BNF info" names tyinfo)

fun g_ctr names G2 G3 (tyinfo:type_info) =
  case G2 (#properties tyinfo)
    of SOME ret => ret
     | NONE => (case #ctr_sugar tyinfo of SOME ctr => G3 ctr
                   | NONE => unavailable "Constructor info" names tyinfo)

fun g_fp names G2 G3 (tyinfo:type_info) =
  case G2 (#properties tyinfo)
    of SOME ret => ret
     | NONE => (case #fp_sugar tyinfo of SOME fp => G3 fp
                   | NONE => unavailable "BNF_FP" names tyinfo)


(*** Basics ***)

(** Basic Info \& Interface **)

local open Type_Info_DB in

fun Tname_of (eb:type_info) = #name eb

val T_of_bnf = g_bnf ["bnf_type"] (get_type "bnf_type") BNF_Def.T_of_bnf
val deads_of_bnf = g_bnf ["deads"] (get_types "deads") BNF_Def.deads_of_bnf
val lives_of_bnf = g_bnf ["lives"] (get_types "lives") BNF_Def.lives_of_bnf

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

fun get_info flags ctxt Tname : type_info option =
  case (if #load_bnf flags then Context.cases BNF_Def.bnf_of_global BNF_Def.bnf_of ctxt Tname else NONE,
        if #load_bnf_fp flags then Context.cases BNF_FP_Def_Sugar.fp_sugar_of_global BNF_FP_Def_Sugar.fp_sugar_of ctxt Tname else NONE,
        if #load_ctr flags then Context.cases Ctr_Sugar.ctr_sugar_of_global Ctr_Sugar.ctr_sugar_of ctxt Tname else NONE)
    of (NONE, NONE, NONE) => NONE
     | (a,b,c) => let
            val c' = case (b,c) of (_, SOME c') => SOME c'
                                 | (SOME b', _) => SOME (#ctr_sugar (#fp_ctr_sugar b'))
                                 | _ => NONE
         in SOME {name = Tname,
                  properties = Type_Info_DB.get_type_info ctxt Tname,
                  bnf = a, fp_sugar = b, ctr_sugar = c'}
        end

fun get_info1 flags ctxt Tname =
  case get_info flags ctxt Tname
    of SOME ret => ret
     | NONE => raise Automation_Fail (fn () => let open Pretty in
                  [block [str "Type ", str Tname, str " has no registered BNF info."],
                   str "May register the required infos using \<open>setup \<open>Type_Info.add_BNF data\<close>\<close>"]
                  end)

fun get_bnf_of_typ1 flags ctxt (Type (Tname, _)) = get_info1 flags ctxt Tname
  | get_bnf_of_typ1 _ _ T = raise TYPE ("Not a constant", [T], [])

(** BNF Operators **)

fun g_bnf_dl names G2 G3 tyinfo Ds Ts =
  g_bnf ("deads"::"lives"::names) (fn prop =>
    get_types "deads" prop |> Option.mapPartial (fn deads =>
    get_types "lives" prop |> Option.mapPartial (fn lives =>
    G2 prop |> Option.map (
      Term.subst_atomic_types ((deads ~~ Ds) @ (lives ~~ Ts))
    )))) (G3 Ds Ts) tyinfo

fun g_bnf_dl3 names G2 G3 tyinfo Ds Ts Us =
  g_bnf ("deads"::"lives"::"lives'"::names) (fn prop =>
    get_types "deads" prop |> Option.mapPartial (fn deads =>
    get_types "lives" prop |> Option.mapPartial (fn lives =>
    get_types "lives'" prop |> Option.mapPartial (fn lives' =>
    G2 prop |> Option.map (
      Term.subst_atomic_types ((deads ~~ Ds) @ (lives ~~ Ts) @ (lives' ~~ Us))
    ))))) (G3 Ds Ts Us) tyinfo

fun g_bnf_dls names G2 G3 tyinfo Dss Tss =
  g_bnf ("deads"::"lives"::names) (fn prop =>
    get_types "deads" prop |> Option.mapPartial (fn deads =>
    get_types "lives" prop |> Option.mapPartial (fn lives =>
    G2 prop |> Option.map (
      map2 (fn (Ds, Ts) =>
        Term.subst_atomic_types ((deads ~~ Ds) @ (lives ~~ Ts) )) (Dss ~~ Tss)
    )))) (G3 Dss Tss) tyinfo

val sets_of_bnf = g_bnf ["sets"] (get_terms "sets") BNF_Def.sets_of_bnf
val sets_of_bnf_safe = safe_try sets_of_bnf
val mk_sets_of_bnf = g_bnf_dls ["sets"] (get_terms "sets") BNF_Def.mk_sets_of_bnf

val rel_of_bnf = g_bnf ["rel"] (get_term "rel") BNF_Def.rel_of_bnf
val rel_of_bnf_safe = safe_try rel_of_bnf
val mk_rel_of_bnf = g_bnf_dl3 ["rel"] (get_term "rel") BNF_Def.mk_rel_of_bnf

val pred_of_bnf = g_bnf ["pred"] (get_term "pred") BNF_Def.pred_of_bnf
val pred_of_bnf_safe = safe_try pred_of_bnf
val mk_pred_of_bnf = g_bnf_dl ["pred"] (get_term "pred") BNF_Def.mk_pred_of_bnf

val map_of_bnf = g_bnf ["map"] (get_term "map") BNF_Def.map_of_bnf
val map_of_bnf_safe = safe_try map_of_bnf
val mk_map_of_bnf = g_bnf_dl3 ["map"] (get_term "map") BNF_Def.mk_map_of_bnf

val ctrs_of = g_ctr ["constructors"] (get_terms "constructors") #ctrs
val ctrs_of_safe = safe_try ctrs_of

val case_of = g_ctr ["case"] (get_term "case") #casex
val case_of_safe = safe_try case_of

val sel_of = g_ctr ["selectors"] (get_termss "selectors") #selss
val sel_of_safe = safe_try sel_of
fun mk_sels tyinfo =
  let val selss = sel_of tyinfo
      fun inst_sel tys tm =
        case Term.fastype_of tm
          of \<^Type>\<open>fun \<open>Type(_, tys')\<close> _\<close> => Term.subst_atomic_types (tys' ~~ tys) tm
           | _ => raise TERM ("Not a selector", [tm])
   in fn tys => map (map (inst_sel tys)) selss
  end

val _ = add_property_kinds [
          ("constructors", KTERMS), ("case", KTERM), ("selectors", KTERMSS),
          ("bnf_type", KTYPE), ("lives", KTYPES), ("deads", KTYPES),
          ("sets", KTERMS), ("rel", KTERM), ("pred", KTERM), ("map", KTERM)
        ]


end


(** Tools **)


fun is_constructor ctxt bvtys term =
  case Term.body_type (Term.fastype_of1 (bvtys, term))
    of Type (Tname, _) =>
         (case get_info {load_bnf=false, load_bnf_fp=false, load_ctr=true} ctxt Tname
            of SOME tyinfo => exists (fn ctr => Term.aconv_untyped (term, ctr))
                                     (these (ctrs_of_safe tyinfo))
             | NONE => false)
     | _ => false

fun is_selector ctxt bvtys term =
  case Term.fastype_of1 (bvtys, term)
    of \<^Type>\<open>fun \<open>Type (Tname, _)\<close> _\<close> =>
         (case get_info {load_bnf=false, load_bnf_fp=false, load_ctr=true} ctxt Tname
            of SOME tyinfo => exists (exists (fn sel => Term.aconv_untyped (term, sel)))
                                     (these (sel_of_safe tyinfo))
             | NONE => false)
     | _ => false


end
