signature PHI_SLEDGEHAMMER_SOLVER = sig

val auto : Phi_Cache_DB.proof_id option -> Proof.context -> thm -> thm

val assync_proof : bool Config.T

val sledgehammer_params : string Config.T
val classical_prover_timeout : int Config.T

end

structure Phi_Sledgehammer_Solver : PHI_SLEDGEHAMMER_SOLVER = struct

val classical_prover_timeout =
        Attrib.setup_config_int \<^binding>\<open>classical_prover_timeout\<close> (K 3)

val sledgehammer_params_fixed = [("isar_proofs", "false")]

val sledgehammer_params = Attrib.setup_config_string \<^binding>\<open>auto_sledgehammer_params\<close> (K "")

fun get_sledgehammer_params ctxt =
  Config.get ctxt sledgehammer_params
    |> String.tokens (fn #"," => true | _ => false)
    |> map (fn s => case String.tokens (fn #"=" => true | _ => false) s
                      of [k,v] => (Symbol.trim_blanks k, Symbol.trim_blanks v)
                       | _ => error ("Invalid auto_sledgehammer_params : " ^ s))

fun error_message ctxt sequent =
  Pretty.string_of (Pretty.chunks (
    Pretty.para "Fail to solve the proof obligation automatically" ::
    (case Thm.prems_of sequent
       of (x::_)
            => [Syntax.pretty_term ctxt x]
        | _ => [])))

(*** Adapter of Sledgehammer ***)

(*copied and modified from Isabelle-2022/src/HOL/Tools/Sledgehammer/sledgehammer_proof_methods.ML
  Original Author: Jasmin Blanchette, TU Muenchen
                   Steffen Juilf Smolka, TU Muenchen

  May need to be synced once updated.
*)
local open Sledgehammer_Proof_Methods

fun is_proof_method_direct (Metis_Method _) = true
  | is_proof_method_direct Meson_Method = true
  | is_proof_method_direct (SMT_Method _) = true
  | is_proof_method_direct Simp_Method = true
  | is_proof_method_direct _ = false

fun is_proof_method_multi_goal Auto_Method = true
  | is_proof_method_multi_goal _ = false

fun string_of_proof_method ss meth =
  let
    val meth_s =
      (case meth of
        Metis_Method (NONE, NONE) => "metis"
      | Metis_Method (type_enc_opt, lam_trans_opt) =>
        "metis (" ^ commas (map_filter I [type_enc_opt, lam_trans_opt]) ^ ")"
      | Meson_Method => "meson"
      | SMT_Method SMT_Z3 => "smt (z3)"
      | SMT_Method (SMT_Verit strategy) =>
        "smt (" ^ commas ("verit" :: (if strategy = "default" then [] else [strategy])) ^ ")"
      | SATx_Method => "satx"
      | Blast_Method => "blast"
      | Simp_Method => if null ss then "simp" else "simp add:"
      | Auto_Method => "auto"
      | Fastforce_Method => "fastforce"
      | Force_Method => "force"
      | Moura_Method => "moura"
      | Linarith_Method => "linarith"
      | Presburger_Method => "presburger"
      | Algebra_Method => "algebra")
  in
    space_implode " " (meth_s :: ss)
  end

in

fun proof_method_command meth n extras =
  let
    val (indirect_ss, direct_ss) =
      if is_proof_method_direct meth then ([], extras) else (extras, [])
  in
    (if null indirect_ss then "" else "(insert " ^ space_implode " " indirect_ss ^ ")[1], ") ^
    (if is_proof_method_multi_goal meth andalso n <> 1
      then "(" ^ string_of_proof_method direct_ss meth ^ ")[1]"
      else string_of_proof_method direct_ss meth)
  end

fun one_line_proof_text (used_facts, meth, subgoal_count) =
  let val (_, extra) = List.partition (fn (_, (sc, _)) => sc = ATP_Problem_Generate.Chained) used_facts in
    map fst extra
    |> proof_method_command meth subgoal_count
  end

end

val silence_state =
      Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose false)

val debug_state =
      Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose true
          #> Config.put SMT_Config.trace true #> Config.put SMT_Config.statistics true )

fun time_ord (t1 : Time.time, t2) =
  if t1 = t2 then EQUAL else if t1 < t2 then LESS else GREATER
fun preplay_ord ((_, Sledgehammer_Proof_Methods.Played t1, _),
                 (_, Sledgehammer_Proof_Methods.Played t2, _))
      = time_ord (t1,t2)
  | preplay_ord ((_, Sledgehammer_Proof_Methods.Played _, _),
                 (_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _))
      = LESS
  | preplay_ord ((_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _),
                 (_, Sledgehammer_Proof_Methods.Played _, _))
      = GREATER
  | preplay_ord ((_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _),
                 (_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _))
      = EQUAL

datatype fail_reason = Too_Many_Subgoals | Timeout | Application_Fails | Subgoal_unsolved | Unknown
                     | Prompt_Timeout
exception Auto_Fail of fail_reason

fun eval_prf_str timeout "" (ctxt,sequent) =
     (Timeout.apply timeout (Timing.timing (
            Position.setmp_thread_data Position.none (Phi_Reasoners.wrap'' Phi_Reasoners.auto_obligation_solver1))
         ) (ctxt,sequent) |> apfst (fn {elapsed=time,...} => (time,""))
              handle Phi_Reasoners.Automation_Fail _ => raise Auto_Fail Application_Fails
                  |  Timeout.TIMEOUT _               => raise Auto_Fail Timeout
                  |  err => (tracing ("Unexpected error, maybe a bug: " ^ Runtime.exn_message err);
                             raise Auto_Fail Unknown) )
  | eval_prf_str timeout prf (ctxt,sequent) =
      let val seq =
            Method.evaluate (
              Parse.read_embedded ctxt (Thy_Header.get_keywords (Proof_Context.theory_of ctxt))
                                       Method.parse (Input.string prf)
                |> fst
                |> Method.check_text ctxt
              ) ctxt [] (ctxt, sequent)
        in case Timeout.apply timeout (Timing.timing (
                    Position.setmp_thread_data Position.none Seq.pull)) seq
             of ({elapsed=time,...}, SOME (Seq.Result ret, _)) => ((time,prf), ret)
              | _ => raise Auto_Fail Application_Fails
      end handle Timeout.TIMEOUT _ => raise Auto_Fail Timeout
               | Auto_Fail err => Exn.reraise (Auto_Fail err)
               | err => (tracing ("Unexpected error, maybe a bug: " ^ Runtime.exn_message err);
                          raise Auto_Fail Unknown)


fun eval_prf_str_stat timeout F_None prf stat =
    let val ctxt = Proof.context_of stat
        val keywords = Thy_Header.get_keywords (Proof_Context.theory_of ctxt)
    in (case Timeout.apply (Time.fromSeconds timeout)
                (Position.setmp_thread_data Position.none Seq.pull)
                (Proof.apply (Parse.read_embedded ctxt keywords Method.parse
                                                  (Input.string ("(" ^ prf ^ ")"))) stat)
          of (SOME (Seq.Result stat', _)) => (prf, stat')
           | _ => case F_None of SOME f => f()
                               | NONE => raise Auto_Fail Application_Fails)
        handle Timeout.TIMEOUT _ => (
          tracing "The proof fails due to timeout. Re-searching proofs...";
          raise Auto_Fail Timeout)
            | err => (
          tracing ("Unexpected error, maybe a bug: " ^ Runtime.exn_message err);
          raise Auto_Fail Unknown)
    end

exception SH_Short_Cut of string

fun dirty_hack ret stat s =
  let fun find c s = CharVector.foldri (fn (i, c', ret) => if c' = c then i :: ret else ret) [] s
      val inds = find #"\^E" s
   in if length inds < 4
      then tracing s
      else let
        val i2 = List.nth (inds, 1)
        val i3 = List.nth (inds, 2)
        val i4 = List.nth (inds, 3)
        val s_prf = String.substring (s, i2+1, i3 - 1 -i2)
        val preplay_succeeded = is_some (CharVector.findi (fn (i,c) => i > i4 andalso c = #"(") s)
        fun trans toks =
          let val toks1 = case toks of [] => raise Fail "internal bug #e12asfwgy43"
                                     | (tok::L) =>
                                 if Token.is_command tok andalso Token.content_of tok = "using"
                                 then L else tok::L
              val sep = find_index (fn tok => Token.is_command tok andalso
                                              (Token.content_of tok = "apply" orelse
                                               Token.content_of tok = "by")) toks1
              val (using, tac) = if sep = ~1 then raise Fail "internal bug #e12asfwgy44"
                                 else (take sep toks1, drop (sep+1) toks1)
              fun unparse toks = String.concatWith " " (map Token.unparse toks)
              fun unparse_tac (tok1::tok2::R) =
                    if Token.keyword_with (fn s => s = "[") tok2
                       andalso not (Token.keyword_with (K true) tok1)
                    then "(" ^ unparse [tok1] ^ ")" ^ unparse (tok2::R)
                    else unparse (tok1::tok2::R)
                | unparse_tac toks = unparse toks
            in (if null using then "" else "(insert " ^ unparse using ^ ")[1], ") ^ unparse_tac tac
           end
        val ctxt = Proof.context_of stat
        val keywords = Thy_Header.get_keywords (Proof_Context.theory_of ctxt)
        val prf = trans (Input.string s_prf
                      |> Input.source_explode
                      |> Token.tokenize keywords {strict = true}
                      |> filter Token.is_proper)
        val _ = Synchronized.change ret (fn prfs => prf :: prfs)
        val _ = tracing s
        in if preplay_succeeded andalso can (eval_prf_str_stat 20 NONE prf) stat
           then raise SH_Short_Cut prf
           else ()
       end
  end

fun debug_param {debug=debug, verbose=verbose, overlord=overlord, spy=spy, provers=provers,
                 abduce=abduce, falsify=falsify, type_enc=type_enc, strict=strict, lam_trans=lam_trans,
                 uncurried_aliases=uncurried_aliases, learn=learn, fact_filter=fact_filter,
                 induction_rules=induction_rules, max_facts=max_facts, fact_thresholds=fact_thresholds,
                 max_mono_iters=max_mono_iters, max_new_mono_instances=max_new_mono_instances,
                 max_proofs=max_proofs, isar_proofs=isar_proofs, compress=compress, try0=try0,
                 smt_proofs=smt_proofs, minimize=minimize, slices=slices, timeout=timeout,
                 preplay_timeout=preplay_timeout, expect=expect} =
      {debug=true, verbose=true, overlord=overlord, spy=spy, provers=provers,
       abduce=abduce, falsify=falsify, type_enc=type_enc, strict=strict, lam_trans=lam_trans,
       uncurried_aliases=uncurried_aliases, learn=learn, fact_filter=fact_filter,
       induction_rules=induction_rules, max_facts=max_facts, fact_thresholds=fact_thresholds,
       max_mono_iters=max_mono_iters, max_new_mono_instances=max_new_mono_instances,
       max_proofs=max_proofs, isar_proofs=isar_proofs, compress=compress, try0=try0,
       smt_proofs=smt_proofs, minimize=minimize, slices=slices, timeout=timeout,
       preplay_timeout=preplay_timeout, expect=expect}


fun raw_sledgehammer stat =
  let val N = #goal (Proof.goal stat) |> Thm.nprems_of
      val _ = if N = 0 then error "No subgoal!" else ()
      val ret : string list Synchronized.var = Synchronized.var "\<phi>System.raw_sledgehammer" []
      val sledgehammer_params = sledgehammer_params_fixed @ get_sledgehammer_params (Proof.context_of stat)
   in (Sledgehammer.run_sledgehammer
              (Sledgehammer_Commands.default_params (Proof.theory_of stat) sledgehammer_params)
              Sledgehammer_Prover.Normal (SOME (dirty_hack ret stat)) 1 Sledgehammer_Fact.no_fact_override
              (silence_state stat);
       @{print} (Synchronized.value ret))

(* For some unknown reason, the return of Sledgehammer.run_sledgehammer doesn't give me everything
   it finds (not match to its output to users), so I have to dirty hijack its output stream and
   recovery the result in a hacking way.
   

  (case Sledgehammer.run_sledgehammer
              (Sledgehammer_Commands.default_params (Proof.theory_of stat) sledgehammer_params)
              Sledgehammer_Prover.Normal (SOME (dirty_hack ret stat)) 1 Sledgehammer_Fact.no_fact_override
              (silence_state stat)
        of (_, (Sledgehammer.SH_Some (result, preplays0), _)) =>
            let val preplays = @{print} preplays0
                            |> filter (fn (_, Sledgehammer_Proof_Methods.Played _, _) => true
                                        | _ => false)
                            |> sort preplay_ord
                val alt_output = Synchronized.value ret
             in @{print} alt_output
            end
         | _ => raise Phi_Reasoners.Automation_Fail NONE)*)
    handle SH_Short_Cut ret => [ret]
         | err as Exn.Interrupt => (warning "Interrupted\n\
              \If this interruption is unexpected for you, it can be caused by the \<open>try0\<close> based\n\
              \proof reconstruction of Sledgehammer.\n\
              \You may \<open>declare [[auto_sledgehammer_params = \"try0 = false\"]]\<close> to disable \<open>try0\<close>,\n\
              \and hopefully the problem can be addressed.";
              Exn.reraise err)
         | E => raise E
  end

(*** Proof search using Sledgehammer ***)

val assync_proof = Attrib.setup_config_bool \<^binding>\<open>\<phi>assync_proof\<close> (K true)

fun assync_prove f (ctxt,sequent) =
  let val (goal_term,_) = Thm.cprop_of sequent |> Thm.dest_implies
   in if Term.maxidx_term (Thm.term_of goal_term) ~1 <> ~1 orelse
         not (Config.get ctxt assync_proof)
      then f (ctxt,sequent)
      else let val pos' = Thread_Position.get ()
               val pos = Position.make pos'
               val hyps = Assumption.all_assms_of ctxt
               val goal_term' = Drule.list_implies (hyps,goal_term)
               val goal_stat = Goal.init goal_term
               val future = Execution.fork {name="\<phi>System-async-proof", pos=pos, pri = ~1} (fn _ =>
                        f (ctxt, goal_stat)
                    (*|> Thm.solve_constraints
                    |> Thm.strip_shyps *)
                    |> fold_rev Thm.implies_intr hyps
                    |> Goal.conclude (*
                    |> (fn th => (if Thm.prop_of th aconv Thm.term_of goal_term' then () else
                                  error "XXXXXXXXXXXXX!"; th)) *)
                  handle
                     Phi_Reasoners.Automation_Fail _ => (
                       Future.error_message pos
                          ((serial (), error_message ctxt sequent), NONE);
                       raise Fail (error_message ctxt sequent))
                   | Auto_Fail _ => (
                       Future.error_message pos
                          ((serial (), error_message ctxt sequent), NONE);
                       raise Fail (error_message ctxt sequent)))
               val _ = Phi_Cache_DB.register_async_task (Future.task_of future) (Proof_Context.theory_of ctxt)
            in Thm.implies_elim sequent (
                  Goal.future_result ctxt future (Thm.term_of goal_term') (*TODO: optimize this!*)
                    |> fold (fn a => fn th => Thm.implies_elim th (Thm.assume a)) hyps)
           end
  end

fun wrapper f (ctxt,sequent) =
  if Thm.no_prems sequent then sequent
  else case Thm.major_prem_of sequent
    of Const (\<^const_name>\<open>Trueprop\<close>, _) $ \<^const>\<open>True\<close> => @{thm TrueI} RS sequent
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>,_))
         => @{thm Premise_True} RS sequent
     | _ => assync_prove f (ctxt,sequent)

val time_delt = Time.fromMilliseconds 1000
fun folerant_time t = Time.scale 1.3 t + time_delt

fun funpow' (0: int) _ x = x
  | funpow' n f x = funpow' (n - 1) f (f n x)

fun sledgehammer (ctxt,sequent0) =
  let (* val ctxt = Phi_Envir.freeze_dynamic_lemmas ctxt *)
      val sequent = @{thm Premise_I} RS sequent0 handle THM _ => sequent0

      val prf = PLPR_Statistics.measure_time_of_proof_search ctxt (fn () => let

      val (goal_term,_) = Logic.dest_implies (Thm.prop_of sequent)
      val stat = Proof.theorem NONE (K I) [[(goal_term, [])]] ctxt

      fun eval_prf_strs_stat [] _ = raise Auto_Fail Application_Fails
        | eval_prf_strs_stat (prf::L) stat =
            eval_prf_str_stat 30 NONE prf stat
            handle Auto_Fail _ => eval_prf_strs_stat L stat

      fun search_prf prompt =
        let
          val (prf0,stat0) = eval_prf_str_stat 8 (SOME (fn () => ("",stat))) prompt stat
                             handle Auto_Fail Timeout => raise Auto_Fail Prompt_Timeout
          val N = Thm.nprems_of (@{print} (#goal (Proof.raw_goal stat0)))
          val Ns = string_of_int N

          val _ = if N > 30 then (tracing ("The prompt generates too many subgoals (" ^
                                    string_of_int N ^ "). give up...");
                                  raise Auto_Fail Too_Many_Subgoals)
                            else ()

          val (prfs,_) =
            funpow' N (fn j => fn (ps,s) =>
                        let val _ = tracing ("Sledgehammering on the " ^ string_of_int (N+1-j) ^
                                             "th goal (total " ^ Ns ^ ")")
                            val prfx = raw_sledgehammer s
                            val (p',s') = eval_prf_strs_stat prfx s
                         in (p'::ps, s') end)
                     ((if prf0 = "" then [] else [prf0]),stat0)
    
          val prf = "(" ^ String.concatWith ",\n" (rev prfs) ^ ")"
        in prf end

      val local_defs = Phi_Help_Lemmas.local_defs ctxt
      fun rep_tries [] = raise Auto_Fail Application_Fails
        | rep_tries (f::L) = f () handle Auto_Fail _ => rep_tries L
      val prf = rep_tries [
          (fn () => search_prf "insert \<phi>, auto simp add: \<phi>sledgehammer_simps"),
          (fn () => if null local_defs
                    then raise Auto_Fail Unknown
                    else (tracing "Unfolding local definitions..." ;
                          search_prf "auto simp add: \<phi> \<phi>sledgehammer_simps local_defs"
                          handle Auto_Fail Too_Many_Subgoals =>
                          search_prf "(clarsimp simp add: \<phi> \<phi>sledgehammer_simps local_defs)?, ((rule conjI)+)?"
                          )),
          (fn () => (tracing "Prompt times out... Try instead a weaker prompt..." ;
                       search_prf "auto simp add: \<phi> \<phi>sledgehammer_simps"
                        handle Auto_Fail Too_Many_Subgoals => (
                          tracing "The prompt generates too many subgoals. Try instead a weaker weaker prompt..." ;
                          search_prf "(clarsimp simp add: \<phi> \<phi>sledgehammer_simps)?, ((rule conjI)+)?")
                            | Auto_Fail Prompt_Timeout => (
                          tracing "The prompt times out again. Try instead a weaker weaker prompt..." ;
                          search_prf "(clarsimp simp add: \<phi> \<phi>sledgehammer_simps)?, ((rule conjI)+)?"))),
          (fn () => (tracing "Fails... Try instead a stronger or maybe weaker prompt..." ;
                     search_prf "insert \<phi>, clarsimp simp add: \<phi>sledgehammer_simps")),
          (fn () => if null local_defs
                    then raise Auto_Fail Unknown
                    else (tracing "Still fails... Unfolding local definitions with aggresive tactics..." ;
                          search_prf "insert \<phi>, auto simp add: local_defs \<phi>sledgehammer_simps")),
          (fn () => (tracing "Fails... Try instead the weakest prompt..." ;
                     search_prf "-"))
        ]

      in prf end) ()

   in PLPR_Statistics.measure_time_of_proof_evaluation ctxt
        (eval_prf_str Time.zeroTime prf) (ctxt,sequent)
  end


fun auto'i id (ctxt,sequent') =
  let
    val thy = Proof_Context.theory_of ctxt
    val _ = Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
                        Pretty.block [ Pretty.str "auto sledgehammer for ",
                                       Pretty.str id],
                        Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent')
                    ])
    val sequent = @{thm Premise_I} RS sequent' handle THM _ => sequent'

    fun try_cached_proof fallback =
     (case Phi_Cache_DB.get_cached_proof thy id
        of NONE => fallback true
         | SOME (time,prf) =>
            let val nprem = Thm.nprems_of sequent
                val ctxt' = ctxt (*if prf = "" then ctxt else Phi_Envir.freeze_dynamic_lemmas ctxt*)
             in (case PLPR_Statistics.measure_time_of_proof_evaluation ctxt'
                        (eval_prf_str (Time.scale 1.5 time + time_delt) prf) (ctxt', sequent)
                   of (_, (_, sequent')) =>
                      if Thm.nprems_of sequent' < nprem then sequent'
                      else raise Auto_Fail Subgoal_unsolved )
                handle Auto_Fail _ => fallback false
            end )

    val classical_timeout = Config.get ctxt classical_prover_timeout
    fun find_proof () =
     (case Timeout.apply (Time.fromSeconds classical_timeout) (Timing.timing Seq.pull)
                            (Phi_Reasoners.auto_obligation_solver ctxt sequent)
        of ({elapsed=time,...}, SOME (sequent', _)) =>
            ((time,""), (ctxt, sequent'))
         | _ => (
            tracing "Proof search by default tactic fails. Invoking sledgehammer...";
            sledgehammer (ctxt, sequent) ))
      handle Timeout.TIMEOUT _ => (
        tracing "Proof search by default tactic times out. Invoking sledgehammer...";
        sledgehammer (ctxt, sequent) )

     fun update_cache hash (prf', (ctxt, sequent')) = (
           Phi_Reasoner.info_print ctxt 1 (fn () =>
              "Find proof (" ^ id ^ ", time: " ^ Value.print_time (fst prf') ^ "): " ^
               (if snd prf' = "" then "classical automation" else "\n" ^ snd prf')
           ) ;
           Phi_Cache_DB.update_hash_cache hash prf';
           Phi_Cache_DB.update_cached_proof thy (id, prf') ;
           sequent')


    in try_cached_proof (fn no_cache' => (let
          val (no_cache, prf_result', hash) = PLPR_Statistics.measure_time_of_proof_evaluation ctxt (fn () => let
            val hash = Hasher.goal (ctxt,sequent)
            val (no_cache, prf_result') =
                  case Phi_Cache_DB.access_hash_cache hash
                    of SOME (t, prf) =>
                        let val ctxt' = ctxt (*if prf = "" then ctxt else Phi_Envir.freeze_dynamic_lemmas ctxt*)
                         in ((false, SOME (
                                PLPR_Statistics.measure_time_of_proof_evaluation ctxt'
                                    (eval_prf_str (folerant_time t) prf) (ctxt',sequent)))
                             handle Auto_Fail _ => (false, NONE))
                        end
                     | NONE => (no_cache', NONE)
             in (no_cache, prf_result', hash)
            end ) ()
          val prf_result =
                case prf_result' of SOME ret => ret
                   | NONE => (if no_cache
                              then (Phi_Reasoner.info_print ctxt 2 (fn _ => "Proof cache miss, " ^ id))
                              else (warning "A cached proof fails. Re-searching proofs...";
                                    Phi_Cache_DB.invalidate_proof_cache (not no_cache) id thy) ;
                              find_proof ())
           in update_cache hash prf_result
          end ))
                    (*
if no_cache
          then (tracing ("Proof cache miss, " ^ id))
          else (warning "The cached proof fails. Re-searching proofs...";
                Phi_Cache_DB.invalidate_proof_cache (not no_cache) id thy) ;
          find_proof ())) *)
   end
(* val proof = raw_sledgehammer stat *)

fun auto id ctxt sequent =
  wrapper (case id of SOME id' => auto'i id'
                    | NONE => Phi_Reasoners.wrap'' Phi_Reasoners.auto_obligation_solver1 #> snd) (ctxt,sequent)
  handle Auto_Fail _ => error (error_message ctxt sequent)
       | Phi_Reasoners.Automation_Fail _ => error (error_message ctxt sequent)

fun insert_tac _ [] _ = all_tac
  | insert_tac ctxt facts i =
      EVERY (map (fn r => resolve_tac ctxt [Thm.forall_intr_vars r COMP_INCR revcut_rl] i) facts);

val _ = Theory.setup (Method.setup \<^binding>\<open>auto_sledgehammer\<close> (Scan.lift (Scan.succeed (fn _ =>
  Method.CONTEXT_METHOD (fn uses => fn (ctxt0,sequent) => Seq.make (fn () =>
    let val ctxt = Config.put assync_proof false ctxt0
        val id = Hasher.goal (ctxt,sequent)
        fun err () = error_message ctxt sequent
        val sequent' =
              case Seq.pull (Method.insert_tac ctxt uses 1 sequent)
                of SOME (ret, _) => ret
                 | NONE => error "Why the insert_tac can fail?"
     in SOME (
         (Seq.Result (ctxt, auto (SOME id) ctxt sequent')
          handle Auto_Fail _ => Seq.Error err),
         Seq.empty)
    end))
)))
  "Apply sledgehammer transparently and record the outcome."
)

end