(*  Title:      Phi_Envir.ML

Basic supports for the nu-system.

*)
infix 0 MP MP_BY

signature PHI_ENVIR = sig
  exception NDBG of thm

  val under_programming_environ : Proof.context -> bool
  val exit_programming_environ : Proof.context -> Proof.context
  val enter_programming_environ' : context_state -> context_state
  val enter_programming_environ  : thm -> Proof.state -> Proof.state

  val the_construction : Proof.context -> thm
  val the_programming_sequent' : Proof.context -> thm
  val the_state_sequent : Proof.state -> thm
  val set_state_sequent : thm -> Proof.state -> Proof.state
  val map_state_sequent : (context_state -> context_state) -> Proof.state -> Proof.state
  val update_programming_sequent' : thm -> Proof.context -> Proof.context

  val reason_programming_implication : Proof.context
                                    -> thm list (*elimination rules*)
                                    -> thm -> thm

  (*The goal in a programming context*)
  val put_thesis : cterm -> Proof.context -> Proof.context
  val get_thesis : Proof.context -> cterm

  structure Enter_Programming_Environ : HOOKS

end

structure Phi_Envir : PHI_ENVIR = struct
open Thm Term HOLogic Phi_Help
exception NDBG of thm

structure Programming_Sequent = Proof_Data (
  type T = (thm (*sequent*)
          * thm (*the latest construction*)
          * thm list lazy (*implication*)
          ) list;
  val init = (K [])
)

fun err_bad_env () = (* warning("Not in the \<phi> programming environment") *) ()

fun the_construction ctxt =
  case Programming_Sequent.get ctxt of (_,thm, _)::_ => thm
                                     | [] => (err_bad_env (); Drule.dummy_thm)

val under_programming_environ = not o null o Programming_Sequent.get
val exit_programming_environ = Programming_Sequent.map tl

fun the_programming_sequent' ctxt =
  case Programming_Sequent.get ctxt of (thm, _, _)::_ => thm
                                     | [] => (err_bad_env (); Drule.dummy_thm)

val the_state_sequent = the_programming_sequent' o Proof.context_of

fun the_implication_GE i ctxt =
  let val L = Programming_Sequent.get ctxt
   in if i < length L
      then Lazy.force (#3 (List.nth (L,i)))
      else (err_bad_env (); [])
   end

fun the_implication i ctxt = maps (conv_GE_to_plain_conjunction ctxt) (the_implication_GE i ctxt)

(* Reason pure facts that the given sequent implies. *)
fun gen_reason_programming_implication erules (mode:Phi_Working_Mode.working_mode) ctxt sequent =
  let
    val inhabited_rule = #inhabited_rule mode
    val thm = sequent RS inhabited_rule
    val _ = Phi_Reasoner.debug_info ctxt (fn _ =>
                "extracting implied pure facts..." ^ Position.here \<^here>)
    open Tactical Tactic
  in rule_by_tactic ctxt (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt erules))) thm
  end

fun reason_programming_implication ctxt erules sequent =
  gen_reason_programming_implication erules
    (Phi_Working_Mode.working_mode_on1 ctxt (Thm.concl_of sequent))
    ctxt sequent

fun reason_programming_implication' mode ctxt sequent =
  [gen_reason_programming_implication
    (Named_Theorems.get ctxt @{named_theorems \<phi>inhabitance_rule}) mode ctxt sequent]
  handle THM _ => []


fun gen_update_programming_sequent' put sequent ctxt =
  case Phi_Working_Mode.working_mode_on ctxt (Thm.concl_of sequent)
    of SOME mode => put ctxt (sequent, sequent, Lazy.lazy (fn () =>
                                        reason_programming_implication' mode ctxt sequent))
     | _ => case Programming_Sequent.get ctxt
              of (_, construction, implication)::_ => put ctxt (sequent, construction, implication)
               | [] => put ctxt (sequent, sequent, Lazy.value [])

val update_programming_sequent' = gen_update_programming_sequent'
        (fn ctxt => fn data => Programming_Sequent.map (fn L => data::tl L) ctxt)


structure Enter_Programming_Environ =
              Hooks (type arg = int (*level of the environ, starting from 0*))

fun enter_programming_environ' stat =
  let
    val level = length (Programming_Sequent.get (fst stat))
    val (ctxt',sequent') = Enter_Programming_Environ.invoke level stat
  in gen_update_programming_sequent'
          (fn ctxt => fn data => Programming_Sequent.map (fn L => data::L) ctxt)
          sequent' ctxt'
  |> rpair sequent'
  end

fun enter_programming_environ sequent s = s
  |> Proof.map_context_result (fn ctxt => enter_programming_environ' (ctxt,sequent) |> swap)
  |-> Proof.set_facts o single

fun set_state_sequent sequent stat = stat
  |> Proof.set_facts [sequent]
  |> Proof.map_context (update_programming_sequent' sequent);

fun map_state_sequent f s =
  s |> Proof.map_context_result (fn ctxt => (ctxt, the_state_sequent s)
                                         |> f
                                         |> swap)
    |-> set_state_sequent


val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>this\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => (err_bad_env (); [])
               | Context.Proof ctxt => [the_programming_sequent' ctxt]))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>construction\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => (err_bad_env (); [])
               | Context.Proof ctxt => [the_construction ctxt]))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>implication_GE\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => the_implication_GE 0 ctxt))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>implication\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => the_implication 0 ctxt))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>\<close>,
          (fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt =>
                   ( Proof_Context.get_thms ctxt "\<phi>implication"
                   @ Proof_Context.get_thms ctxt \<^named_theorems>\<open>useful\<close>)
          )))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>implication_GE_previous\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => the_implication_GE 1 ctxt))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>implication_previous\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => the_implication 1 ctxt))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>_previous\<close>,
          (fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt =>
                   ( Proof_Context.get_thms ctxt "\<phi>implication_previous"
                   @ Proof_Context.get_thms ctxt \<^named_theorems>\<open>\<phi>lemmata\<close>
                   @ Proof_Context.get_thms ctxt \<^named_theorems>\<open>useful\<close>)
          )))


fun catch msg f tm = (f tm) handle TERM _ => raise TERM (msg, [tm])
fun catch_th i msg f th = (f th) handle THM _ => raise THM (msg, i, [th])
                                      | TERM _ => raise TERM (msg, [prop_of th])



fun put_thesis thesis = 
      Proof_Context.put_thms false ("\<phi>thesis", SOME [Drule.mk_term thesis])
fun get_thesis ctxt =
      Proof_Context.get_thm ctxt "\<phi>thesis" |> Drule.dest_term

end
