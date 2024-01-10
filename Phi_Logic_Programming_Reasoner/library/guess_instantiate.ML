signature GUESS_INSTANTIATE = sig

val guess_inst : Proof.context -> (string * typ) list (*frees that cannot be bound*)
              -> cterm -> cterm Vars.table option

val guess_inst_tac : Proof.context -> int -> tactic
val guess_inst_solver : solver

val add_guess_inst_looper : Proof.context -> Proof.context

end

structure Guess_Instantiate : GUESS_INSTANTIATE = struct

exception Guess_Conflicts



fun qchk_one_side ctxt bvtys tm =
  let val (h,args) = Term.strip_comb tm
   in Term.is_Var h orelse
      ((Type_Info.is_constructor ctxt bvtys h orelse
        Type_Info.is_selector ctxt bvtys h) andalso
       exists (qchk_one_side ctxt bvtys) args)
  end





fun inst bans tab (v, args) cterm0 =
  let val cterm = Phi_Help.beta_eta_contract_cterm (Thm.instantiate_cterm (TVars.empty, tab) cterm0)
               |> fold_rev Thm.lambda args
   in if (not (Term.exists_subterm (fn a => exists (fn b => a aconv Free b) bans) (Thm.term_of cterm))
          andalso (case Thm.term_of cterm
                     of Var v' => v <> v'
                      | _ => true))
      then case Vars.lookup tab v
             of NONE => Vars.add (v, cterm) tab
              | SOME cterm' => if Thm.term_of cterm aconv Thm.term_of cterm' then tab
                               else raise Guess_Conflicts
      else tab
  end

exception Automation_Fail = Phi_Reasoners.Automation_Fail

(*only instantiate LHS*)
fun guess_inst_eq ctxt bans =
  let fun guess (LHS,RHS) tab =
        let val (LH, LARGS) = Drule.strip_comb LHS
         in case Thm.term_of LH
         of Var v => inst bans tab (v, LARGS) RHS
          | _ =>
            let open Type_Info
                fun eq_const (Const (A, _)) (Const (B, _)) = A = B
                  | eq_const _ _ = false

                val tyinfo = case Thm.typ_of_cterm LHS
                               of Type(name, _) =>
                                    get_info1 {load_bnf = false,
                                               load_bnf_fp = false,
                                               load_ctr = true}
                                              (Context.Proof ctxt) name
                                | _ => raise Automation_Fail (K [])
                val ctrs = ctrs_of tyinfo
                val selss = sel_of tyinfo
                val h = Thm.term_of LH
                val ci = find_index (eq_const h) ctrs
                val targs = Thm.dest_ctyp (Thm.ctyp_of_cterm LHS)

      
             in if ci <> ~1 andalso ci < length selss
                   andalso length (nth selss ci) = length LARGS
                then let val SS = map (Thm.cterm_of ctxt o inst_sel (map Thm.typ_of targs))
                                      (nth selss ci)
                      in fold2 (fn L => fn S => guess (L, Thm.apply S RHS)) LARGS SS tab
                     end
                else tab
            end handle Automation_Fail _ => tab
        end
   in guess
  end

fun guess_inst' ctxt bans cterm tab =
      case Thm.term_of cterm
        of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
              guess_inst' ctxt bans (Thm.dest_arg cterm) (guess_inst' ctxt bans (Thm.dest_arg1 cterm) tab)
         | Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ B =>
              let val bvtys = map snd bans
               in if qchk_one_side (Context.Proof ctxt) bvtys A
                  then guess_inst_eq ctxt bans (Thm.dest_arg1 cterm, Thm.dest_arg cterm) tab
                  else if qchk_one_side (Context.Proof ctxt) bvtys B
                  then guess_inst_eq ctxt bans (Thm.dest_arg cterm, Thm.dest_arg1 cterm) tab
                  else tab
              end
         | Const(\<^const_name>\<open>Pure.eq\<close>, _) $ A $ B =>
              let val bvtys = map snd bans
               in if qchk_one_side (Context.Proof ctxt) bvtys A
                  then guess_inst_eq ctxt bans (Thm.dest_arg1 cterm, Thm.dest_arg cterm) tab
                  else if qchk_one_side (Context.Proof ctxt) bvtys B
                  then guess_inst_eq ctxt bans (Thm.dest_arg cterm, Thm.dest_arg1 cterm) tab
                  else tab
              end
         | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
              guess_inst' ctxt bans (Thm.dest_arg cterm) tab
         | Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs _ =>
              (case Variable.dest_abs_cterm (Thm.dest_arg cterm) ctxt
                 of ((var,cterm'), ctxt') => guess_inst' ctxt' (Term.dest_Free (Thm.term_of var) :: bans) cterm' tab)
       (*| Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs _ =>
              (case Variable.dest_abs_cterm (Thm.dest_arg cterm) ctxt
                 of ((var,cterm'), ctxt') => guess_inst' ctxt' (Thm.term_of var::bans) cterm' tab) *)
         | _ => tab

fun quick_check ctxt =
  let fun qchk bvtys (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) =
                  qchk bvtys A orelse qchk bvtys B
        | qchk bvtys (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ B) =
                  qchk_one_side ctxt bvtys A orelse qchk_one_side ctxt bvtys B
        | qchk bvtys (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ A $ B) =
                  qchk_one_side ctxt bvtys A orelse qchk_one_side ctxt bvtys B
        | qchk bvtys (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = qchk bvtys X
        | qchk bvtys (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, Ty, X)) = qchk (Ty :: bvtys) X
        | qchk _ _ = false
        (*| qchk bvtys (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (_, Ty, X)) = qchk (Ty :: bvtys) X *)
   in qchk
  end


fun guess_inst ctxt bans cterm =
  let val ret = guess_inst' ctxt bans cterm Vars.empty
   in if Vars.is_empty ret
      then NONE
      else SOME ret
  end handle Guess_Conflicts => NONE

val enable_inst = Config.declare_bool ("enable_inst", \<^here>) (K true)

fun guess_inst_tac ctxt n st = Seq.make (fn () =>
  let val (bvtys, concl) = Phi_Help.strip_meta_hhf_bvtys (Logic.nth_prem (n, Thm.prop_of st))
   in if quick_check (Context.Proof ctxt) bvtys concl
      then
      let val cprem = Thm.cprem_of st n
          val (lb, _, concl, ctxt') = Phi_Help.strip_meta_hhf_c cprem ctxt
       in if Config.get ctxt enable_inst
          then guess_inst ctxt' (map (Term.dest_Free o Thm.term_of) lb) concl
            |> Option.map (fn inst => (Thm.instantiate (TVars.empty, inst) st, Seq.empty))
          else NONE
      end
      else NONE
  end)

val guess_inst_solver = Simplifier.mk_solver "inst_var_by_Ctr_sels" guess_inst_tac

fun add_guess_inst_looper ctxt = ctxt addloop ("inst_var_by_Ctr_sels", guess_inst_tac)

val _ = Theory.setup (Simplifier.map_theory_simpset add_guess_inst_looper)

end