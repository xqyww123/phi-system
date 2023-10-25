signature PHI_TYPE = sig
include PHI_TYPE

type arity = int list (*Gs, its length is the arity of F, its elements are the arity of each G*)

val parse_F_Gs_of_comm_typor_appl : Context.generic ->
        Pattern_Translation.bv_typs * term (*combination of F(G(T))*) -> (term (*F*) * term list (*Gs*)) list

val register_comm_tyoprs : (arity * Pattern_Translation.redex_residues) list ->
        Context.generic -> Context.generic
     (*redex: F (G\<^sub>1 T\<^sub>1\<^sub>1 \<dots> T\<^sub>1\<^sub>n) \<dots> (G\<^sub>m T\<^sub>m\<^sub>1 \<dots> T\<^sub>m\<^sub>n) \<longrightarrow>
       residues: F, G\<^sub>1, T\<^sub>1\<^sub>1, \<dots>, T\<^sub>1\<^sub>n, \<dots>, G\<^sub>m, T\<^sub>m\<^sub>1, \<dots>, T\<^sub>m\<^sub>n*)
     (*automatically invoked when any \<phi>-LPR rule is registered*)

val register_comm_tyoprs_rule_pass : arity * term -> Context.generic -> Context.generic
      (*see the examples below*)

(*
val commutative_rules : Context.generic -> term (*F*) * term list (*Gs*) -> (Position.T * thm) list

val are_commutative : Context.generic -> term * term list -> bool
val is_commutative : Context.generic -> term (*F*) -> int list (*available arities of F. empty means non-commutative*)

val comm_patterns : ((term (*pattern*) * term (*F*) * term list (*Gs*)) * int (*arity of F*)) list Unsynchronized.ref
*)

end

structure Phi_Type : PHI_TYPE = struct
open Phi_Type


type arity = int list (*Gs, its length is the arity of F, its elements are the arity of each G*)

val comm_tyoprs_eq = eq_pair (op =) (eq_pair (op aconv) (eq_list (op aconv)))

structure Comm_Tyoprs = Generic_Data (
  type T = (arity * Pattern_Translation.redex_residues) iNet.net
           (*redex: F (G\<^sub>1 T\<^sub>1\<^sub>1 \<dots> T\<^sub>1\<^sub>n) \<dots> (G\<^sub>m T\<^sub>m\<^sub>1 \<dots> T\<^sub>m\<^sub>n) \<longrightarrow>
             residues: F, G\<^sub>1, T\<^sub>1\<^sub>1, \<dots>, T\<^sub>1\<^sub>n, \<dots>, G\<^sub>m, T\<^sub>m\<^sub>1, \<dots>, T\<^sub>m\<^sub>n*)
  val empty = iNet.empty
  val merge = iNet.merge comm_tyoprs_eq
)

fun parse_F_Gs_of_comm_typor_appl ctxt =
  let val rewrites = Comm_Tyoprs.get ctxt
      val thy = Context.theory_of ctxt
      fun split [] [] = []
        | split (n::N) (G::Lg) = G :: split N (drop n Lg)
        | split _ _ = error "BUG: bad patterns"
   in fn (bvtys, F_G_T) =>
      iNet.match_term rewrites F_G_T
   |> map_filter (fn (arities, redex_residues) =>
        Pattern_Translation.rewrites thy bvtys redex_residues F_G_T
     |> Option.map (fn F::L => (F, split arities L)))
   |> distinct (eq_pair (op aconv) (eq_list (op aconv)))
  end

fun register_comm_tyoprs arity_redex_residues =
  Comm_Tyoprs.map (fold (fn a_r_r as (_,(comb,_)) =>
    iNet.insert_term comm_tyoprs_eq (comb,a_r_r)
  ) arity_redex_residues)

val pass_id_head = Const("tyopr_comm_pass", dummyT)
fun register_comm_tyoprs_rule_pass (arity,rewr) =
  let val (property::redex_residues) = Logic.dest_conjunction_list rewr
      val redex_residues' = map Logic.dest_term redex_residues
   in Phi_Reasoner.add_pass (pass_id_head $ rewr, property,
        fn _ => fn (rules, prio, pats, guard, ctxt) =>
          let val rewr = map (fn rule =>
                    let val env = Pattern.match (Context.theory_of ctxt) (property, Thm.concl_of rule) (Vartab.empty, Vartab.empty)
                        val (redex::residues) = map (Envir.subst_term env) redex_residues'
                     in (arity, (redex, residues))
                    end) rules
              val ctxt' = register_comm_tyoprs rewr ctxt
           in (rules, prio, pats, guard, ctxt')
          end)
  end

val _ = Theory.setup (Context.theory_map (
  fold register_comm_tyoprs_rule_pass
    [([1], \<^pattern_prop>\<open>Tyops_Commute ?F ?F' ?G ?G' ?T ?D ?r &&&
              TERM(?F (?G ?T)) &&& TERM(?F) &&& TERM(?G) &&& TERM(?T)\<close>),
     ([2], \<^pattern_prop>\<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&&
              TERM(?F (?G ?T ?U)) &&& TERM(?F) &&& TERM(?G) &&& TERM(?T) &&& TERM(?U)\<close>),
     ([1,1], \<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&&
              TERM(?G' (?F'\<^sub>T ?T) (?F'\<^sub>U ?U)) &&& TERM(?G') &&& TERM(?F'\<^sub>T) &&& TERM(?T) &&& TERM(?F'\<^sub>U) &&& TERM(?U)\<close>)]
))







(*
fun parse_raw_pattern raw =
  let val (pat::F::G) = Logic.dest_conjunction_list raw
   in (pat, F, G)
  end

val comm_patterns = Unsynchronized.ref (map (apfst parse_raw_pattern)
      [(\<^pattern_prop>\<open>Tyops_Commute ?F ?F' ?G ?G' ?T ?D ?r &&& TERM ?F &&& TERM ?G\<close>, 1),
       (\<^pattern_prop>\<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&& TERM ?F &&& TERM ?G\<close>, 1),
       (\<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&& TERM ?G' &&& TERM ?F'\<^sub>T &&& TERM ?F'\<^sub>U\<close>, 2)])

fun mk_comm_patterns thy (F,Gs) =
  map_filter (fn ((pat, F', Gs'),_) =>
    let val envir = fold (Pattern.match thy) ((F',F)::(Gs' ~~ Gs)) (Vartab.empty, Vartab.empty)
     in SOME (Envir.subst_term envir pat)
    end handle Pattern.MATCH => NONE
  ) (!comm_patterns)

fun mk_comm_patterns_F thy F =
  map_filter (fn ((pat, F', _), arity) =>
    let val envir = Pattern.match thy (F',F) (Vartab.empty, Vartab.empty)
     in SOME (Envir.subst_term envir pat, arity)
    end handle Pattern.MATCH => NONE
  ) (!comm_patterns)

fun commutative_rules ctxt =
  let val lookup = PLPR_Template_Properties.lookup_properties_match ctxt
      val chk_pat = PLPR_Template_Properties.assert_property_pattern (Context.theory_of ctxt)
   in fn (F,G) =>
  let val patterns = mk_comm_patterns (Context.theory_of ctxt) (F,G)
   in maps (lookup o chk_pat) patterns
  end
  end

fun commutative_rules_of_F ctxt =
  let val lookup = PLPR_Template_Properties.lookup_properties_match ctxt
      val chk_pat = PLPR_Template_Properties.assert_property_pattern (Context.theory_of ctxt)
   in fn F =>
  let val patterns = mk_comm_patterns_F (Context.theory_of ctxt) F
   in maps (fn (pat, arity) => lookup (chk_pat pat)
                            |> map (rpair arity)) patterns
  end
  end

fun are_commutative ctxt =
  let val rules = commutative_rules ctxt
   in fn (F,G) => not (null (rules (F,G)))
  end

fun is_commutative ctxt =
  let val rules = commutative_rules_of_F ctxt
   in fn F => distinct (op =) (map snd (rules F))
  end
*)

end
