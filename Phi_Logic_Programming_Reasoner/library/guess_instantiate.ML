signature GUESS_INSTANTIATE = sig

val guess_inst : Proof.context -> term list (*terms that cannot be bound*)
              -> cterm -> cterm Vars.table option

val guess_inst_tac : Proof.context -> int -> tactic
val guess_inst_solver : solver

val add_guess_inst_looper : Proof.context -> Proof.context

end

structure Guess_Instantiate : GUESS_INSTANTIATE = struct

exception Guess_Conflicts


fun inst bans tab (v, args) cterm0 =
  let val cterm = Phi_Help.beta_eta_contract_cterm (Thm.instantiate_cterm (TVars.empty, tab) cterm0)
               |> fold_rev Thm.lambda args
   in if (not (Term.exists_subterm (fn a => exists (fn b => a aconv b) bans) (Thm.term_of cterm))
          andalso (case Thm.term_of cterm
                     of Var v' => v <> v'
                      | _ => true))
      then case Vars.lookup tab v
             of NONE => Vars.add (v, cterm) tab
              | SOME cterm' => if Thm.term_of cterm aconv Thm.term_of cterm' then tab
                               else raise Guess_Conflicts
      else tab
  end


fun guess_inst_eq ctxt bans =
  let fun guess (LHS,RHS) tab =
        let val (LH, LARGS) = Drule.strip_comb LHS
            val (RH, RARGS) = Drule.strip_comb RHS
         in case (Thm.term_of LH, Thm.term_of RH)
         of (Var v, _) => inst bans tab (v, LARGS) RHS
          | (_, Var v) => inst bans tab (v, RARGS) LHS
          | _ =>
            let fun root_ctr term = case Thm.typ_of_cterm term
                                      of Type(name, _) => Ctr_Sugar.ctr_sugar_of ctxt name
                                       | _ => NONE
                fun eq_const (Const (A, _)) (Const (B, _)) = A = B
                  | eq_const _ _ = false
                fun dest_ctr (term, H, ARGS) = Option.mapPartial
                      (fn ctr => let val h = Thm.term_of H
                                     val ci = find_index (eq_const h) (#ctrs ctr)
                                     val targs = Thm.dest_ctyp (Thm.ctyp_of_cterm term)
                                     val instt = case #T ctr
                                                   of Type(_, Ts) =>
                                                        if length targs = length Ts
                                                        then TVars.build (fold2 (fn TVar v => (fn A => TVars.add (v, A))
                                                                                  | _ => error "BUG srPbRKmbQnmW/7hNjYzuqA") Ts targs)
                                                        else error "BUG srPbRKmbQnmW/7hNjYzuqA"
                                                    | _ => error "BUG srPbRKmbQnmW/7hNjYzuqA"
                                     val instt = Thm.instantiate_cterm (instt, Vars.empty) o Thm.cterm_of ctxt
                                  in if ci <> ~1 andalso ci < length (#selss ctr)
                                                 andalso length (nth (#selss ctr) ci) = length ARGS
                                     then SOME (nth (#ctrs ctr) ci, ARGS, map instt (nth (#selss ctr) ci))
                                     else NONE
                                 end)
                      (root_ctr term)
      
             in case (dest_ctr (LHS, LH, LARGS), dest_ctr (RHS, RH, RARGS))
                  of (NONE, NONE) => tab
                   | (SOME (_, LHSS, SS), NONE) => fold2 (fn L => fn S => guess (L, Thm.apply S RHS)) LHSS SS tab
                   | (NONE, SOME (_, RHSS, SS)) => fold2 (fn R => fn S => guess (Thm.apply S LHS, R)) RHSS SS tab
                   | (SOME (CL, LHSS, _), SOME (CR, RHSS, _)) =>
                        if CL = CR
                        then fold2 (fn L => fn R => guess (L, R)) LHSS RHSS tab
                        else raise Guess_Conflicts
            end
        end
   in guess
  end

fun guess_inst' ctxt bans cterm tab =
      case Thm.term_of cterm
        of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
              guess_inst' ctxt bans (Thm.dest_arg cterm) (guess_inst' ctxt bans (Thm.dest_arg1 cterm) tab)
         | Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _ =>
              guess_inst_eq ctxt bans (Thm.dest_arg1 cterm, Thm.dest_arg cterm) tab
         | Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ =>
              guess_inst_eq ctxt bans (Thm.dest_arg1 cterm, Thm.dest_arg cterm) tab
         | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
              guess_inst' ctxt bans (Thm.dest_arg cterm) tab
         | Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs _ =>
              (case Variable.dest_abs_cterm (Thm.dest_arg cterm) ctxt
                 of ((var,cterm'), ctxt') => guess_inst' ctxt' (Thm.term_of var::bans) cterm' tab)
         | Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs _ =>
              (case Variable.dest_abs_cterm (Thm.dest_arg cterm) ctxt
                 of ((var,cterm'), ctxt') => guess_inst' ctxt' (Thm.term_of var::bans) cterm' tab)
         | _ => tab

fun guess_inst ctxt bans cterm =
  let val ret = guess_inst' ctxt bans cterm Vars.empty
   in if Vars.is_empty ret
      then NONE
      else SOME ret
  end handle Guess_Conflicts => NONE

val enable_inst = Config.declare_bool ("enable_inst", \<^here>) (K true)

fun guess_inst_tac ctxt n st = Seq.make (fn () =>
  let val cprem = Thm.cprem_of st n
      val (lb, _, concl, ctxt') = Phi_Help.strip_meta_hhf_c cprem ctxt
   in if Config.get ctxt enable_inst
      then guess_inst ctxt' (map Thm.term_of lb) concl
        |> Option.map (fn inst => (Thm.instantiate (TVars.empty, inst) st, Seq.empty))
      else NONE
  end)

val guess_inst_solver = Simplifier.mk_solver "inst_var_by_Ctr_sels" guess_inst_tac

fun add_guess_inst_looper ctxt = ctxt addloop ("inst_var_by_Ctr_sels", guess_inst_tac)

val _ = Theory.setup (Simplifier.map_theory_simpset add_guess_inst_looper)

end