signature PLPR_SYNTAX = sig
include PLPR_SYNTAX

val dest_with_IN_arg : term -> indexname list * term
val elim_with_IN_arg : thm -> indexname list * thm

(* (*must be beta-eta normalized*)
val minimal_pattern_implied_by_IN_arg : indexname list -> term -> term
*)

end

structure PLPR_Syntax : PLPR_SYNTAX = struct
open PLPR_Syntax

fun dest_with_IN_arg tm =
  let fun dest ret (Const(\<^const_name>\<open>With_IN_Arg\<close>, _) $ P $ X) =
            (case X of Var v => dest (fst v :: ret) P
                     | _ => raise TERM ("An IN-argument must be a schematic variable", [tm]))
        | dest ret P = (ret, P)
   in dest [] tm
  end

fun elim_with_IN_arg thm =
  let val (inargs, _) = dest_with_IN_arg (Thm.concl_of thm)
   in (inargs, fold (fn _ => fn th => @{thm' With_IN_Arg_I} RS th) inargs thm)
  end

(* I dunno if we will enable this feature, it is not good and not really useful
(*must be beta-eta normalized*)
fun minimal_pattern_implied_by_IN_arg inargs term =
  let val idx = Unsynchronized.ref (Term.maxidx_of_term term)
      fun gen_var (btys, tm) = (idx := !idx + 1; Var (("_", !idx), Term.fastype_of1 (btys, tm)))
      exception Not_Occur
      fun gen btys tm = gen' btys tm handle Not_Occur => gen_var (btys, tm)
      and gen' btys (X as _ $ _) =
           (case Term.strip_comb X
              of (Var v, _) => if member (op =) inargs (fst v) then X else raise Not_Occur
               | (H, args) => let val args' = map (gen btys) args
                               in if exists (fn Var v => member (op =) inargs (fst v)
                                              | _ => true) args'
                                  then Term.list_comb (H, args')
                                  else gen_var (btys, X)
                              end)
        | gen' btys (Abs (_, ty, X)) = gen' (ty :: btys) X
        | gen' _ (Var v) = if member (op =) inargs (fst v) then Var v else raise Not_Occur
   in ()
  end*)

end