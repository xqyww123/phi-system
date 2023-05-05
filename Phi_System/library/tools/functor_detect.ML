(*
FILE: Phi_System/library/tools/functor_detect.ML
AUTHOR: Qiyuan Xu

Given a term of a \<phi>-type which is an application of a functor with an argument,
it is undecidable by higher-order lambda pattern match to get the functor and the argument from it.
The file provides ML code enabling users to register rewrites or ML codes to extract the functor
from terms matching certain patterns.

It also implements a simple fallback heuristic that works when the term is a sequence
of lambda applications \<open>H $ A1 $ A2 $ A3\<close> and the head is a constant, and it assumes the argument
is the last operand i.e. the A3.
*)

signature PHI_FUNCTOR_DETECT = sig

structure Rewr : PATTERN_REWRITE

val detect  : int -> Proof.context -> term -> term list option
val detect1 : int -> Proof.context -> term -> term list

end

structure Phi_Functor_Detect : PHI_FUNCTOR_DETECT = struct

structure Rewr = Pattern_Translation (
  val parse_pattern = Syntax.parse_term
  val check_pattern = Syntax.check_terms
  val multi_translation_err_msg = "Cannot determine which is the functor and which is the argument\
        \ in the given term. Two rules are conflict!"
)

fun detect arity ctxt term =
  case Rewr.translate (Context.Proof ctxt) term
    of [] => let val (hT, args) = Term.strip_comb term
                 val N = length args - arity
              in if is_Const hT andalso not (is_Const term) andalso N >= 0
                 then SOME ( Term.list_comb (hT, take N args) :: drop N args)
                 else NONE
             end
     | L => (if length L = arity + 1
             then SOME L
             else error ("Expect " ^ string_of_int arity ^ "-arity functor, but the configured\
                         \ rule returns " ^ string_of_int (length L) ^ "-arity."))

fun detect1 arity ctxt term =
  case detect arity ctxt term
    of SOME ret => ret
     | NONE => error ("Fail to detect the functor part and the argument part from term\n"^
                      Syntax.string_of_term ctxt term)

end