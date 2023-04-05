signature PHI_REASONERS = sig
include PHI_REASONERS

val conv_GE_to_plain_conjunction : Proof.context -> thm -> thm list
val extract_elim_rule : Proof.context -> thm list -> thm -> thm

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

fun conv_GE_to_plain_conjunction ctxt thm =
  let val V = case Thm.concl_of thm
      of (\<^const>\<open>Trueprop\<close> $ Var V) => V
       | _ => raise THM ("Not a Generalized Elimination rule", 0, [thm])
      
      fun wrap_ex vs term =
        let val bnos = loose_bnos term
         in if null bnos
            then (0,term)
            else let val sbst = map_index (fn (i,_) =>
                                  let val j = find_index (fn b => b = i) bnos
                                   in if j = ~1 then Const ("!bad", dummyT) else Bound j end) vs
                     val vars = map (fn j => List.nth (vs, j)) bnos
                     val term' = case term
                                   of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X => X
                                    | _ => error "bug: #!codisfhw"
                  in subst_bounds (sbst, term')
                  |> fold (fn (name,ty) => fn term => \<^Const>\<open>Ex ty\<close> $ Abs(name,ty,term)) vars
                  |> (fn X => (length bnos, \<^const>\<open>Trueprop\<close> $ X))
                 end 
        end
      val facts = Thm.prems_of thm
               |> map (Phi_Help.strip_meta_hhf #> (fn (vs,tms,_) => map (wrap_ex (rev vs)) tms))
      fun list_mk_disj [] = \<^const>\<open>True\<close>
        | list_mk_disj [x] = x
        | list_mk_disj L = foldr1 HOLogic.mk_disj L
      fun sort_fact (S_conj,S_disj) ((X::L)::LR) =
            if forall (exists (fn a => (snd a) aconv (snd X))) LR
            then sort_fact (X::S_conj,S_disj) (L :: map (remove (op aconv o apsnd snd) (snd X)) LR)
            else sort_fact (S_conj,X::S_disj) (L::LR)
        | sort_fact (S_conj,S_disj) ([]::LR) =
            let val disjs = map (map (snd #> HOLogic.dest_Trueprop)) (S_disj::LR)
                val disj = ((map (map fst) (S_disj::LR),
                             \<^const>\<open>Trueprop\<close> $ list_mk_disj (map (foldr1 HOLogic.mk_conj) disjs))
                            handle List.Empty => ([], \<^prop>\<open>True\<close>))
             in (S_conj, disj)
            end
        | sort_fact _ [] = ([],([],\<^prop>\<open>True\<close>))
      val (conjs, (ex_nums, disj)) = sort_fact ([],[]) facts

      fun dest_cert_implies ret ctm =
            (case Thm.dest_implies ctm of (A,B) => dest_cert_implies (A::ret) B)
            handle TERM _ => ret
      val cert_prems = dest_cert_implies [] (Thm.cprem_of thm 1)
            handle TERM _ => []
      fun get_cert_conjs ret ((n,X)::LX) (Y::LY) =
            if n = 0 
            then if X aconv Thm.term_of Y then get_cert_conjs ((0,Y)::ret) LX LY
                 else get_cert_conjs ret ((0,X)::LX) LY
            else get_cert_conjs ((n, Thm.cterm_of ctxt X) :: ret) LX (Y::LY)
        | get_cert_conjs ret ((n,X)::LX) [] = get_cert_conjs ((n, Thm.cterm_of ctxt X) :: ret) LX []
        | get_cert_conjs ret [] _ = ret

      val cert_conjs = get_cert_conjs [] conjs cert_prems

      val conjs' = map (fn (n,X) => 
            let val tac = (REPEAT_DETERM_N n (HEADGOAL (Tactic.resolve_tac ctxt @{thms exI}))
                           THEN HEADGOAL (Tactic.assume_tac ctxt))
                val thm' = Thm.instantiate (TVars.empty, Vars.make [(V, Thm.dest_arg X)]) thm
             in case Seq.pull (tac thm')
                  of SOME (Y, _) => Y
                   | NONE => error "bug #fnqweiht9p3"
            end
          ) cert_conjs

      val ret_thms =
        case disj
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) => conjs'
           | _ =>
              let val cdisj = Thm.cterm_of ctxt disj
                  val thm' = Thm.instantiate (TVars.empty, Vars.make [(V, Thm.dest_arg cdisj)]) thm
                  fun tac_e (ex_n::exL) st =
                        ((if null exL then all_tac else HEADGOAL (Tactic.resolve_tac ctxt @{thms conjI}))
                         THEN REPEAT_DETERM_N ex_n (HEADGOAL (Tactic.resolve_tac ctxt @{thms exI}))
                         THEN HEADGOAL (Tactic.assume_tac ctxt)) st
                        |> Seq.maps (tac_e exL)
                    | tac_e [] st = Seq.single st
                  fun tac i (exs::ex_nums) st =
                       (REPEAT_DETERM_N i (HEADGOAL (Tactic.resolve_tac ctxt @{thms disjI2}))
                        THEN
                        (if null ex_nums
                         then all_tac
                         else HEADGOAL (Tactic.resolve_tac ctxt @{thms disjI1}))
                        THEN tac_e exs
                       ) st
                       |> Seq.maps (tac (i+1) ex_nums)
                    | tac _ [] st = Seq.single st
                  val disj_thm = case Seq.pull (tac 0 ex_nums thm')
                                   of SOME (X, _) => X | _ => error "bug #q;3yv5bp"
               in disj_thm::conjs' end
   in ret_thms
  end

(*
(*If no  disjunction: split the conjunction into a list
  If has disjunction: convert to Disjunctive Normal Form*)
fun conv_GE_to_plain_conjunction ctxt thm =
  let
    val V = case Thm.concl_of thm
      of (\<^const>\<open>Trueprop\<close> $ Var V) => V
       | _ => raise THM ("Not a Generalized Elimination rule", 0, [thm])
    val thm' = Thm.instantiate (TVars.empty, Vars.make [(V, \<^cterm>\<open>CONV_GE\<close>)]) thm
  in
    thm'
      |> Raw_Simplifier.rewrite_rule ctxt @{thms atomize_all atomize_imp atomize_eq atomize_conj CONV_GE_phase_1}
      |> Raw_Simplifier.rewrite_rule ctxt @{thms CONV_GE_Ex_def CONV_GE_phase_2}
      |> Raw_Simplifier.rewrite_rule ctxt @{thms CONV_GE_Ex_def CONV_GE_phase_3}
      |> Conjunction.elim_conjunctions
      |> filter (fn th => case Thm.prop_of th
                            of Const (\<^const_name>\<open>Trueprop\<close>, _) $ Const (\<^const_name>\<open>True\<close>, _) => false
                             | _ => true)
  end
*)
fun pred_V (SOME V) V' = (V = V') | pred_V NONE _ = true

fun is_elim_rule' V' (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ P $ X)
      =(case Logic.strip_assums_concl P
          of Const (\<^const_name>\<open>Trueprop\<close>, _) $ Var V
               => pred_V V' V andalso is_elim_rule' (SOME V) X
           | _ => false)
  | is_elim_rule' V' (Const (\<^const_name>\<open>Trueprop\<close>, _) $ Var V) = pred_V V' V
  | is_elim_rule' _ _ = false

fun is_elim_rule (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ _) $ X)
      = is_elim_rule' NONE X
  | is_elim_rule _ = false

fun extract_elim_rule ctxt0 erules thm0 =
  if is_elim_rule (Thm.prop_of thm0)
  then thm0
  else
    let val ((_,[thm]),ctxt) = Variable.import true [thm0] ctxt0
        val _ = Phi_Reasoner.info_pretty ctxt 1 (fn _ => Pretty.chunks [
                  Pretty.str "Going to extract elimination rule from:",
                  Syntax.pretty_term ctxt0 (Thm.prop_of thm0)
              ])
     in (ctxt, Drule.compose (thm, 1, @{thm Do_Extract_Elimination_Rule}))
      |> Phi_Reasoner.reason NONE
      |> (fn SOME (ctxt', ret) =>
            let val ret' = Tactical.REPEAT_DETERM (Thm.biresolution (SOME ctxt') false
                              (map (pair true) erules) 2) ret
                        |> Seq.pull
                        |> (fn SOME (x, _) => x
                             | NONE => error "Internal bug!#q3f4j89[")
                        |> singleton (Variable.export ctxt' ctxt0)
                        |> Drule.zero_var_indexes
                val _ = Phi_Reasoner.info_pretty ctxt' 1 (fn _ => Pretty.chunks [
                      Pretty.str "Obtained the following elimination rule:",
                      Syntax.pretty_term ctxt' (Thm.prop_of ret')
                  ])
             in ret' end
           | NONE => Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
                Pretty.str "Fail to extract elimination rule from:",
                Syntax.pretty_term ctxt0 (Thm.prop_of thm0)
               ])))
    end


end