signature PLPR_GENERALIZED_ELIMINATION = sig
end

structure PLPR_Generalized_Elimination = struct

type reasoner = {name: term, pattern: term list, not_match: term list, tactic: (context_state -> context_state Seq.seq)}

fun last [] = raise Fail "last"
  | last [x] = x
  | last (h::ls) = last ls

fun get_GE_term cterm =
  let
    fun dest G cterm =
      case Thm.term_of cterm
        of Abs _ => (case Thm.dest_abs_global cterm
                       of (a,b) => dest (Term.term_name (Thm.term_of a) :: G) b)
         | Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => dest G (Thm.dest_arg cterm)
         | _ => Thm.generalize_cterm (Names.empty, Names.make_set G)
                                     (Thm.maxidx_of_cterm cterm + 1) cterm
   in dest [] cterm
  end

fun comp_n n th1 th2 =
  Thm.bicompose NONE {flatten = true, match = false, incremented = false} (false, th1, 0) n th2
  |> Seq.list_of |> distinct Thm.eq_thm
  |> (fn [th] => Thm.solve_constraints th | _ => raise THM ("COMP", n, [th1, th2]));


fun GE_reasoner raw_rule  =
let
  val rule = case Thm.concl_of raw_rule
    of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Ex\<close>, _) $ _) =>
        Seq.REPEAT (Thm.biresolution NONE false [(true, @{thm exE})] 1) raw_rule |> Seq.hd
     | _ => raw_rule
  val GE_term = get_GE_term (last (Thm.chyps_of rule))
  fun tac (ctxt, sequent) =
    let
      val goal = Thm.major_prem_of sequent
    in @{thm Generalized_Elimination_Framework}
          |> comp_n 3 sequent
          |> comp_n 3 rule
          |> (fn th => Drule.mk_term GE_term RS th)
          |> (fn th => Drule.mk_term goal    RS th)
    end
in
  ()
end

end