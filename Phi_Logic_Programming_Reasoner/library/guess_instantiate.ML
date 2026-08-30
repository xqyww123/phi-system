signature GUESS_INSTANTIATE = sig

val guess_inst : Proof.context -> (string * typ) list (*frees that cannot be bound*)
              -> cterm -> cterm Vars.table option

val guess_inst_tac : Proof.context -> int -> tactic
val guess_inst_solver : Proof.context -> solver

val add_guess_inst_solver : Proof.context -> Proof.context
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





(*** the guess_inst Event_Log category (EVENT_LOG_PLAN 2.6) -- successor of
     the \<phi>guess_inst_probe TSV probe; original study:
     Docs/GUARD_NITPICK_FALSIFY_PLAN.md section 26. ***)

(*Solving \<open>?f a\<^sub>1 \<dots> a\<^sub>n = r\<close> by \<open>?f := \<lambda>a\<^sub>1 \<dots> a\<^sub>n. r\<close> is the UNIQUE solution only when the
  a\<^sub>i are pairwise distinct variables bound inside the formula -- a Miller pattern,
  and bans is exactly that list of locally bound variables.  Otherwise the
  equation constrains ?f at isolated points and this is one solution out of many,
  committed silently and without backtracking.  Records both kinds; off unless
  \<phi>log_guess_inst is set (context-level switch, EVENT_LOG_PLAN 2.3).*)
val log_guess_inst = Attrib.setup_config_bool \<^binding>\<open>\<phi>log_guess_inst\<close> (K false)

(*term printing happens in the encoder, i.e. under Event_Log's own write
  protection: a failing printer drops the record, never the tactic*)
val log_category =
  Event_Log.category {name = "guess_inst", enabled = fn () => true,
    encode = fn {ctxt, goal, entries, n_others, other_hits, occurrences} =>
      let val show = Protocol_Message.clean_output o Syntax.string_of_term ctxt
          val unforced = length (filter_out #1 entries)
      in
        ([("verdict", if unforced = 0 then "forced" else "UNFORCED"),
          ("choices", string_of_int (length entries)),
          ("unforced", string_of_int unforced),
          ("other_goals", string_of_int n_others),
          ("other_goal_hits", string_of_int (length other_hits)),
          ("hit_occurrences", string_of_int occurrences)],
         Event_Log.elem_text "goal" (show goal) ::
         map (fn (forced, v, args, r) =>
               XML.Elem (("choice", [("forced", Bool.toString forced)]),
                 [Event_Log.elem_text "var" (show v),
                  Event_Log.elem_text "args" (commas (map show args)),
                  Event_Log.elem_text "result" (show r)]))
             (rev entries) @
         map (Event_Log.elem_text "other_hit" o show) other_hits)
      end}

val probe_acc : (bool * term * term list * term) list Unsynchronized.ref Thread_Data.var =
      Thread_Data.var ()

fun probe_forced bans args =
  let val xs = map Thm.term_of args
   in forall (fn Free b => member (op =) bans b | _ => false) xs andalso
      not (has_duplicates (op aconv) xs)
  end

fun probe_record entry =
  (case Thread_Data.get probe_acc of
     SOME r => Unsynchronized.change r (cons entry)
   | NONE => ())

fun inst bans tab (v, args) cterm0 =
  let val cterm = Phi_Help.beta_eta_contract_cterm (Thm.instantiate_cterm (TVars.empty, tab) cterm0)
               |> fold_rev Thm.lambda args
   in if (not (Term.exists_subterm (fn a => exists (fn b => a aconv Free b) bans) (Thm.term_of cterm))
          andalso (case Thm.term_of cterm
                     of Var v' => v <> v'
                      | _ => true))
      then case Vars.lookup tab v
             of NONE => (probe_record (probe_forced bans args, Var v,
                                       map Thm.term_of args, Thm.term_of cterm);
                         Vars.add (v, cterm) tab)
              | SOME cterm' => if Thm.term_of cterm aconv Thm.term_of cterm' then tab
                               else raise Guess_Conflicts
      else tab
  end

exception Automation_Fail = Phi_Reasoners.Automation_Fail

(*only instantiate LHS*)
fun guess_inst_eq ctxt bans =
  let fun guess (LHS,RHS) (maxidx, tab) =
        let val (LH, LARGS) = Drule.strip_comb LHS
         in case Thm.term_of LH
         of Var v => (maxidx, inst bans tab (v, LARGS) RHS)
          | _ =>
            let open Type_Info
                val h = Thm.term_of LH
                fun split_ctr continue =
                  let val tyinfo = case Thm.typ_of_cterm LHS
                                     of Type(name, _) =>
                                          get_info1 {load_bnf = false,
                                                     load_bnf_fp = false,
                                                     load_ctr = true}
                                                    (Context.Proof ctxt) name
                                      | _ => raise Automation_Fail (K [])
                      val ctrs = ctrs_of tyinfo
                      val selss = sel_of tyinfo
                      val ci = find_index (curry Term.aconv_untyped h) ctrs
                   in if ci <> ~1 andalso ci < length selss
                         andalso length (nth selss ci) = length LARGS
                      then let val targs = Thm.dest_ctyp (Thm.ctyp_of_cterm LHS)
                               val SS = map (Thm.cterm_of ctxt o inst_sel (map Thm.typ_of targs))
                                            (nth selss ci)
                            in fold2 (fn L => fn S => guess (L, Thm.apply S RHS)) LARGS SS (maxidx, tab)
                           end
                      else continue ()
                  end

                fun step_selector continue =
                  case LARGS
                    of [LARG] =>
                        let val tyinfo = case Thm.typ_of_cterm LARG
                                           of Type(name, _) =>
                                                get_info1 {load_bnf = false,
                                                           load_bnf_fp = false,
                                                           load_ctr = true}
                                                          (Context.Proof ctxt) name
                                            | _ => raise Automation_Fail (K [])
                            val ctrs = ctrs_of tyinfo
                            val selss = sel_of tyinfo
                         in case (get_index (get_index (fn j =>
                                        if Term.aconv_untyped (h,j) then SOME j else NONE
                                     )) selss)
                              of SOME (i, (j, _)) =>
                                    let val targs = Thm.dest_ctyp (Thm.ctyp_of_cterm LARG)
                                        val ctr = nth ctrs i |> inst_ctr (map Thm.typ_of targs)
                                        val cargs = Term.binder_types (Term.fastype_of ctr)
                                                 |> map_index (fn (k, ty) =>
                                                      if k = j
                                                      then RHS
                                                      else Thm.var (("\<a>", maxidx+1+k), Thm.ctyp_of ctxt ty) )
                                        val RHS' = Thm.cterm_of ctxt ctr
                                                |> fold (fn a => fn f => Thm.apply f a) cargs
                                     in guess (LARG, RHS')
                                              (maxidx + length cargs, tab)
                                    end
                               | NONE => continue ()
                        end
                     | _ => continue ()

      
             in split_ctr (fn () =>
                step_selector (K (maxidx, tab)))
            end handle Automation_Fail _ => (maxidx, tab)
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
  let val (_, ret) = guess_inst' ctxt bans cterm (Thm.maxidx_of_cterm cterm, Vars.empty)
   in if Vars.is_empty ret
      then NONE
      else SOME ret
  end handle Guess_Conflicts => NONE

val enable_inst = Config.declare_bool ("enable_inst", \<^here>) (K true)

(*One record per goal this tactic actually instantiates -- see the note at
  log_guess_inst above.  The commitment lands on the WHOLE state, so what
  decides whether a choice is harmless is where else the variable occurs: in
  the rest of this subgoal, and in every other subgoal.  Both are recorded --
  the count, and each other subgoal that mentions an instantiated variable.*)
fun probe_flush ctxt n st goal entries =
  if not (Config.get ctxt log_guess_inst) orelse null entries then ()
  else
    let
      val vars = map (fn (_, v, _, _) => v) entries
      fun mentions t = exists (fn v => Term.exists_subterm (fn u => u aconv v) t) vars
      fun occurrences t = length (filter (fn v => Term.exists_subterm (fn u => u aconv v) t) vars)
      val others =
        Thm.prems_of st |> map_index I |> filter (fn (i, _) => i + 1 <> n) |> map snd
      val other_hits = filter mentions others
    in
      Event_Log.append log_category
        {ctxt = ctxt, goal = goal, entries = entries,
         n_others = length others, other_hits = other_hits,
         occurrences = fold (fn t => fn k => k + occurrences t) other_hits 0}
    end

fun guess_inst_tac ctxt n st = Seq.make (fn () =>
  let val goal = Logic.nth_prem (n, Thm.prop_of st)
      val (bvtys, concl) = Phi_Help.strip_meta_hhf_bvtys goal
   in if quick_check (Context.Proof ctxt) bvtys concl
      then
      let val cprem = Thm.cprem_of st n
          val (lb, _, concl, ctxt') = Phi_Help.strip_meta_hhf_c cprem ctxt
       in if Config.get ctxt enable_inst
          then
            let val acc = Unsynchronized.ref []
                val guessed =
                  Thread_Data.setmp probe_acc (SOME acc)
                    (fn () => guess_inst ctxt' (map (Term.dest_Free o Thm.term_of) lb) concl) ()
                val _ = if is_some guessed then probe_flush ctxt n st goal (! acc) else ()
             in Option.map (fn inst => (Thm.instantiate (TVars.empty, inst) st, Seq.empty)) guessed
            end
          else NONE
      end
      else NONE
  end)

(*val present_solvers = #1 (Raw_Simplifier.solvers \<^context>)*)
fun solve_all_tac solvers ctxt =
  let
    val subgoal_tac = Raw_Simplifier.subgoal_tac (Raw_Simplifier.set_solvers solvers ctxt);
    val solve_tac = subgoal_tac THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE o solve_tac end;

fun guess_inst_solver ctxt0 =
  Simplifier.mk_solver "inst_var_by_Ctr_sels" (fn ctxt => fn n => fn st =>
   (((fn st =>
      case Thm.major_prem_of st
        of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ A $ B =>
            if is_Var (Term.head_of A) orelse is_Var (Term.head_of B)
            then Seq.empty
            else guess_inst_tac ctxt n st
         | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ B) =>
            if is_Var (Term.head_of A) orelse is_Var (Term.head_of B)
            then Seq.empty
            else guess_inst_tac ctxt n st
         | _ => guess_inst_tac ctxt n st)
     THEN Simplifier.asm_full_simp_tac ctxt n)
    ORELSE
    FIRST' (map (Raw_Simplifier.solver ctxt)
      (rev (#1 (Raw_Simplifier.solvers ctxt0)))) n) st)

fun add_guess_inst_looper ctxt = ctxt |> Simplifier.add_loop ("inst_var_by_Ctr_sels", guess_inst_tac)
fun add_guess_inst_solver ctxt = Raw_Simplifier.set_solvers [guess_inst_solver ctxt] ctxt


(*EXPERIMENT 1 (2026-08-29, author's step 1): the looper is no longer installed
  into the theory simpset for EVERY simplification.  It is added only where
  guard conditions are preprocessed (reasoners.ML, guard_condition_solver).
  The global installation, kept for reference:
    val _ = Theory.setup (Simplifier.map_theory_simpset add_guess_inst_looper)
  Restore it if Phi_Examples fails to go through under this scope.*)


end