signature PHI_REASONERS = sig

val pass_checks_priority : string (*name of the kind of the rules*)
                        -> int (*priority lower bound*)
                        -> Phi_Reasoner.rule_pass

end

structure Phi_Reasoners : PHI_REASONERS = struct

fun pass_checks_priority name prio = (fn pos => fn data =>
  case #2 (#2 data)
    of SOME (prio', _) =>
        if prio < prio'
        then data
        else error (let open Pretty in string_of (
                block (text "The priority of a" @
                       [brk 1, str (if name = "" then "reasoning" else name), brk 1] @
                       text "must be greater than" @
                       [brk 1, str (string_of_int prio), brk 1] @
                       here pos)
            )end)
     | NONE => data
  )

end

signature IN_ARG = sig

type mask = term
(*Masks are patterns that match the conclusion of the given rule, where the variables that are
  immutably instantiated (i.e., instantiated to the variable itself) are used to represent IN-argument.
  For example, given a rule of conclusion \<open>P ?x ?y ?z\<close>, a mask \<open>P _ ?y _\<close> indicates \<open>?y\<close> is the only
  IN-argument.
  The trick of this design is that, the default binding patterns of the rule in \<phi>-LPR reasoner, are
  usually such masks.
*)

val default_mask_of : Context.generic -> term -> mask list
val parse_mask : mask list -> term -> indexname list
 (* rule: Some_Predicate An_IN_Argument Some_Expression_for_OUT
    mask: Some_Predicate An_IN_Argument ?dummy_schematic_var
    In this case, all variables in the Some_Expression_for_OUT can be instantiated arbitrary,
    while An_IN_Argument should be fixed. *)

end

structure IN_Arg : IN_ARG = struct

type mask = term

fun default_mask_of ctxt concl =
  case Phi_Reasoner.the_default_pattern_of ctxt concl
    of [] => [concl]
     | L => L

fun parse_mask masks concl =
  let val _ = if null masks then error "masks cannot be null" else ()
      fun filter_inargs inargs (Var (v, _), Var (v', _)) =
            if fst v = fst v' then insert (op =) v inargs else inargs
        | filter_inargs inargs (_, Var _) = inargs
        | filter_inargs inargs (f $ x, f' $ x') = filter_inargs (filter_inargs inargs (x, x')) (f, f')
        | filter_inargs inargs (Abs (_, _, x), Abs (_, _, x')) = filter_inargs inargs (x, x')
        | filter_inargs inargs (Const (N, _), Const (N', _)) =
            if N = N' then inargs else raise Match
        | filter_inargs inargs (Free (N, _), Free (N', _)) =
            if N = N' then inargs else raise Match
        | filter_inargs inargs (Bound i, Bound j) =
            if i = j then inargs else raise Match
        | filter_inargs _ _ = raise Match
   in fold (fn X => fn inargs =>
        filter_inargs inargs (apply2 Phi_Help.beta_eta_contract_term
                                     (snd (PLPR_Syntax.strip_embedded_patterns concl), X))
        handle Match => inargs
      ) masks []
  end

end

signature PHI_HELP = sig
include PHI_HELP

   (* rule: Some_Predicate An_IN_Argument Some_Expression_for_OUT
      mask: Some_Predicate An_IN_Argument ?dummy_schematic_var
      In this case, all variables in the Some_Expression_for_OUT can be instantiated arbitrary,
      while An_IN_Argument should be fixed. *)
val instantiate_higher_order_schematic_var_for_rule_guess' :
      int (*N*) * IN_Arg.mask list ->
      Proof.context -> thm -> thm option (*returns none if no change*)
val instantiate_higher_order_schematic_var_for_rule_guess :
      int (*N*) * IN_Arg.mask list -> Proof.context -> thm -> thm

end

structure Phi_Help : PHI_HELP = struct
open Phi_Help

fun instantiate_higher_order_schematic_var_for_rule_guess' (N, masks) ctxt thm =
  case PLPR_Syntax.strip_embedded_patterns (Thm.concl_of thm)
    of ((_, _, []), _) =>
        let val masks' = if null masks then IN_Arg.default_mask_of (Context.Proof ctxt) (Thm.concl_of thm)
                                       else masks
         in instantiate_higher_order_schematic_var_for_rule'
              (N, IN_Arg.parse_mask masks' (Thm.concl_of thm)) ctxt thm
        end
     | ((_, _, inargs), _) =>
        instantiate_higher_order_schematic_var_for_rule' (N, inargs) ctxt thm

fun instantiate_higher_order_schematic_var_for_rule_guess data ctxt thm =
  the_default thm (instantiate_higher_order_schematic_var_for_rule_guess' data ctxt thm)

end