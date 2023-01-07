(*  Title:      Phi_Basics.ML

Basic supports for the nu-system.

*)
infix 0 MP MP_BY

signature PHI_BASICS = sig
  exception NDBG of thm

  val under_programming_environ : Proof.context -> bool
  val exit_programming_environ : Proof.context -> Proof.context
  val enter_programming_environ' : thm -> Proof.context -> Proof.context

  val the_construction : Proof.context -> thm
  val the_programming_sequent' : Proof.context -> thm
  val the_nu_fact : Proof.state -> thm
  val set_nu_fact : thm -> Proof.state -> Proof.state
  val enter_programming_environ : thm -> Proof.state -> Proof.state
  val update_programming_sequent' : thm -> Proof.context -> Proof.context

end

structure Phi_Basics : PHI_BASICS = struct
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

val the_nu_fact = the_programming_sequent' o Proof.context_of

fun the_implication_GE i ctxt =
  let val L = Programming_Sequent.get ctxt
   in if i < length L
      then Lazy.force (#3 (List.nth (L,i)))
      else (err_bad_env (); [])
   end

fun the_implication i ctxt = maps (conv_GE_to_plain_conjunction ctxt) (the_implication_GE i ctxt)

(* Reason pure facts that the given sequent implies. *)
fun reason_programming_implication mode ctxt sequent =
  let
    val inhabited_rule = #inhabited_rule mode ctxt
    val thm = SOME (sequent RS inhabited_rule)
              handle THM _ => NONE
    val _ = Nu_Reasoner.debug_info ctxt (fn _ => "extracting implied pure facts...")
    val erules = Named_Theorems.get ctxt @{named_theorems \<phi>inhabitance_rule}
    open Tactical Tactic
  in Option.map (rule_by_tactic ctxt (TRY (HEADGOAL (eresolve_tac ctxt erules)))) thm
  end

fun gen_update_programming_sequent' put sequent ctxt =
  case Phi_Working_Mode.working_mode_on ctxt (Thm.concl_of sequent)
    of SOME mode => put ctxt (sequent, sequent, Lazy.lazy (fn () =>
                                      the_list (reason_programming_implication mode ctxt sequent)))
     | _ => case Programming_Sequent.get ctxt
              of (_, construction, implication)::_ => put ctxt (sequent, construction, implication)
               | [] => put ctxt (sequent, sequent, Lazy.value [])

val update_programming_sequent' = gen_update_programming_sequent'
        (fn ctxt => fn data => Programming_Sequent.map (fn L => data::tl L) ctxt)
val enter_programming_environ' = gen_update_programming_sequent'
        (fn ctxt => fn data => Programming_Sequent.map (fn L => data::L) ctxt)
  

fun gen_set_nu_fact updt sequent stat = stat
  |> Proof.set_facts [sequent]
  |> Proof.map_context (updt sequent);

val set_nu_fact = gen_set_nu_fact update_programming_sequent'
val enter_programming_environ = gen_set_nu_fact enter_programming_environ'

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
















(* val auto_fusion_arity =
  Logic.strip_assums_concl #> perhaps (try dest_Trueprop) #> perhaps_try (dest_procedure #> #2)
  #> perhaps_try (dest_binop "NuPrime.Stack_Delimiter" #> #2)
  #> perhaps (try dest_RepSet) #> perhaps_try (dest_nuTy #> #2)
  #> repeat (dest_binop "NuBasicAbstractors.NuRefine" #> #1)
  #> repeat (dest_binop "NuBasicAbstractors.SchemaCondition" #> #1)
  #> repeat (dest_binop "NuBasicAbstractors.Schema" #> #1)
  #> strip_binop_r "NuLLReps.AutoFusion" #> length *)

(*default type remander*)
(* val default_ty_R = TFree ("'\<RR>", [@{class "stack"}]) *)
(*translate tail of a stack type to `ty_R`, if it ends with void*)







end
