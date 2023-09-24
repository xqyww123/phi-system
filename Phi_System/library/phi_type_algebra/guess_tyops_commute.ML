signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val gen_Guess_Tyops_Commute : term * int -> guess_property (*intro*) * guess_property (*elim*)

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*F is fixed myself, G is the target
  Given \<open>F\<close>, generate derivers deriving \<open>Tyops_Commute F F' G G' T D r\<close>
  and \<open>Tyops_Commute G G' F F' T D r\<close> for given G
*)
fun gen_Guess_Tyops_Commute_framework (template_of_reasoning_goal, parsing_rule, F_arity, G_arity)
                                      F_term =
  Guess_Framework'
    ( template_of_reasoning_goal,
      fn (phi, ctxt) =>
        let val idx = phi_maxidx_of phi ~1 + 1
            val F_term' = Logic.incr_indexes ([], [], idx) F_term
            val (U_ty, x_ty, c_ty) = case dest_parameterized_phi_ty (Term.fastype_of (#term phi))
                                       of (U_ty :: _, x_ty, c_ty) => (U_ty, x_ty, c_ty)
                                        | _ => raise Automation_Fail (fn () => let open Pretty in
                                                  [block ([Syntax.pretty_term ctxt (#term phi), brk 1] @
                                                          text "is not a type operator")]
                                               end)
            val ((_, GU_term), ctxt) = fix_phi_term_params (#term phi) ctxt
            fun fail () = guess_fail ctxt phi (fn () => let open Pretty in
                            [block (text "Fail to parse the given \<phi>-type" @
                                    [brk 1, Syntax.pretty_term ctxt GU_term, brk 1] @
                                    text "as a type operator.")]
                          end)
            val G_term = case GU_term of G_term $ _ => G_term
                                       | _ => fail ()
         in ([("F", F_term'), ("G", G_term)], phi, ctxt)
        end,
      parsing_rule
    )

val gen_Guess_Tyops_Commute_I_1 = gen_Guess_Tyops_Commute_framework
      (\<^pattern_prop>\<open>Guess_Tyops_Commute True ?G ?G' ?F ?F'
                                        ?unfolded_G ?unfolded_G' (\<lambda>T x. x \<Ztypecolon> ?F T) (\<lambda>T x. x \<Ztypecolon> ?F' T)
                                        ?T ?D ?r ?ants ?conds\<close>,
       \<^pattern>\<open>(Guess_Tyops_Commute True ?G ?G' ?F ?F' ?unfolded_G ?unfolded_G' ?uF ?uF' ?T ?D ?r ?ants ?conds,
                Tyops_Commute ?G ?G' ?F ?F' ?T ?D ?r,
                ?G' _ _,
                ?conds,
                ?ants)\<close>,
       1, 1)

val gen_Guess_Tyops_Commute_E_1 = gen_Guess_Tyops_Commute_framework
      (\<^pattern_prop>\<open>Guess_Tyops_Commute False ?F ?F' ?G ?G'
                                        (\<lambda>T x. x \<Ztypecolon> ?F T) (\<lambda>T x. x \<Ztypecolon> ?F' T) ?unfolded_G ?unfolded_G'
                                        ?T ?D ?r ?ants ?conds\<close>,
       \<^pattern>\<open>(Guess_Tyops_Commute False ?F ?F' ?G ?G' ?uF ?uF' ?unfolded_G ?unfolded_G' ?T ?D ?r ?ants ?conds,
                Tyops_Commute ?F ?F' ?G ?G' ?T ?D ?r,
                ?G _ _,
                ?conds,
                ?ants)\<close>,
       1, 1)

val gen_Guess_Tyops_Commute_I_2_1 = gen_Guess_Tyops_Commute_framework
      (\<^pattern_prop>\<open>Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 False ?G ?G'\<^sub>T ?G'\<^sub>U ?F ?F'
                                          ?uG ?uG'\<^sub>T ?uG'\<^sub>U (\<lambda>T U x. x \<Ztypecolon> ?F T U) (\<lambda>T U x. x \<Ztypecolon> ?F' T U)
                                          ?T ?U ?D ?r ?ants ?conds\<close>,
       \<^pattern>\<open>(Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 False ?G ?G'\<^sub>T ?G'\<^sub>U ?F ?F' ?uG ?uG'\<^sub>T ?uG'\<^sub>U ?uF ?uF' ?T ?U ?D ?r ?ants ?conds,
                Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?G ?G'\<^sub>T ?G'\<^sub>U ?F ?F' ?T ?U ?D ?r,
                ?G _ _,
                ?conds,
                ?ants)\<close>,
       1, 1)

val gen_Guess_Tyops_Commute_E_2_1 = gen_Guess_Tyops_Commute_framework
      (\<^pattern_prop>\<open>Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1\<^sub>E ?G ?G'\<^sub>T ?G'\<^sub>U ?F ?F' ?unfolded_G ?unfolded_G\<^sub>T ?unfolded_G\<^sub>U ?T ?U ?D ?r ?ants ?conds\<close>,
       \<^pattern>\<open>(Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1\<^sub>E ?G ?G'\<^sub>T ?G'\<^sub>U ?F ?F' ?unfolded_G ?unfolded_G\<^sub>T ?unfolded_G\<^sub>U ?T ?U ?D ?r ?ants ?conds,
                Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?G ?G'\<^sub>T ?G'\<^sub>U ?F ?F' ?T ?U ?D ?r,
                ?G _ _,
                ?conds,
                ?ants)\<close>,
       1, 1)

fun gen_Guess_Tyops_Commute (F_term, 1) = (gen_Guess_Tyops_Commute_I_1 F_term, gen_Guess_Tyops_Commute_E_1 F_term)
  | gen_Guess_Tyops_Commute (F_term, 2) = (gen_Guess_Tyops_Commute_I_2_1 F_term, gen_Guess_Tyops_Commute_E_2_1 F_term)
  | gen_Guess_Tyops_Commute _ = error "Unsupported arity"
  

end