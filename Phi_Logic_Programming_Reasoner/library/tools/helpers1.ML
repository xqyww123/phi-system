signature PHI_REASONERS = sig

val pass_checks_priority : string (*name of the kind of the rules*)
                        -> int (*priority lower bound*)
                        -> Phi_Reasoner.rule_pass

end

structure Phi_Reasoners : PHI_REASONERS = struct

fun pass_checks_priority name prio = (fn pos => fn data =>
  if prio < #2 (#2 data)
  then data
  else error (let open Pretty in string_of (
          block (text "The priority of a" @
                 [brk 1, str (if name = "" then "reasoning" else name), brk 1] @
                 text "must be greater than" @
                 [brk 1, str (string_of_int prio), brk 1] @
                 here pos)
      )end)
  )

end

signature PHI_HELP = sig
include PHI_HELP


val guess_IN_arguments_of_a_rule : Context.generic -> term list (*pattern of the rule, can be nil,
                                                                  if so, use the default pattern registered in Phi_Reasoner*)
                                -> thm -> indexname list
  (*Of a rule, use default pattern that is registered in the \<phi>-LPR to guess its IN-arguments,
    as all the IN-arguments should be retained in the pattern while all OUT-arguments are replaced
    by a schematic variable.
    original rule: Some_Predicate An_IN_Argument Some_Expression_for_OUT
    pattern:       Some_Predicate An_IN_Argument ?dummy_schematic_var
    In this case, all variables in the Some_Expression_for_OUT can be instantiated arbitrary,
    while An_IN_Argument should be fixed.
*)

val instantiate_higher_order_schematic_var_for_rule_guess' :
      int (*N*) * term list (*optional patterns, can be []*) ->
      Proof.context -> thm -> thm option (*returns none if no change*)
val instantiate_higher_order_schematic_var_for_rule_guess :
      int (*N*) * term list -> Proof.context -> thm -> thm

end

structure Phi_Help : PHI_HELP = struct
open Phi_Help

fun guess_IN_arguments_of_a_rule ctxt patterns rule =
  let val concl = Thm.concl_of rule
      val default_patterns = case patterns
                               of [] => Phi_Reasoner.the_default_pattern_of ctxt concl
                                | L => L
      fun filter_inargs inargs (Var (v, _), Var (v', _)) =
            if fst v = fst v' then inargs else insert (op =) v inargs
        | filter_inargs inargs (_, Var _) = inargs
        | filter_inargs inargs (f $ x, f' $ x') = filter_inargs (filter_inargs inargs (x, x')) (f, f')
        | filter_inargs inargs (Abs (_, _, x), Abs (_, _, x')) = filter_inargs inargs (x, x')
        | filter_inargs inargs (Const (N, _), Const (N', _)) =
            if N = N' then inargs else raise Match
        | filter_inargs inargs (Free (N, _), Free (N', _)) =
            if N = N' then inargs else raise Match
        | filter_inargs _ _ = raise Match
   in fold (fn X => fn inargs => filter_inargs inargs (Thm.concl_of rule, X) handle Match => inargs)
           default_patterns []
  end

fun instantiate_higher_order_schematic_var_for_rule_guess' (N, patterns) ctxt thm =
  case PLPR_Syntax.elim_with_IN_arg thm
    of ([], thm) =>
        instantiate_higher_order_schematic_var_for_rule'
          (N, guess_IN_arguments_of_a_rule (Context.Proof ctxt) patterns thm) ctxt thm
     | (inargs, thm) =>
        instantiate_higher_order_schematic_var_for_rule' (N, inargs) ctxt thm

fun instantiate_higher_order_schematic_var_for_rule_guess data ctxt thm =
  the_default thm (instantiate_higher_order_schematic_var_for_rule_guess' data ctxt thm)

end