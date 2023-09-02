(*  Title:      Phi_Envir.ML

Basic supports for the nu-system.

*)
infix 0 MP MP_BY

signature PHI_ENVIR = sig

  include PHI_ENVIR

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

  val reason_programming_implication : Proof.context -> thm -> thm list

  (*The goal in a programming context*)
  val put_thesis : cterm -> Proof.context -> Proof.context
  val get_thesis : Proof.context -> cterm

  val simplify_lemmata : bool Config.T
  val process_lemmata : (Proof.context -> thm list (*additional rules to simplify the lemmata*))
        -> Proof.context -> thm -> thm list
  val process_useful_lemmata : bool -> Proof.context -> thm -> thm list

  val freeze_dynamic_lemmas : Proof.context -> Proof.context

  structure Enter_Programming_Environ : HOOKS

end

structure Phi_Envir : PHI_ENVIR = struct
open Thm Term HOLogic Phi_Help Phi_Envir
exception NDBG of thm

structure Programming_Sequent = Proof_Data (
  type T = (thm (*sequent*)
          * thm (*the latest construction*)
          * thm list lazy (*implication*)
          ) list;
  val init = (K [])
)

fun err_bad_env () = error ("Not in the \<phi> programming environment")

fun the_construction ctxt =
  case Programming_Sequent.get ctxt of (_,thm, _)::_ => thm
                                     | [] => Drule.dummy_thm

val under_programming_environ = not o null o Programming_Sequent.get
val exit_programming_environ = Programming_Sequent.map (fn L => tl L)

fun the_programming_sequent' ctxt =
  case Programming_Sequent.get ctxt of (thm, _, _)::L => thm
                                     | [] => Drule.dummy_thm

val the_state_sequent = the_programming_sequent' o Proof.context_of

fun the_implication i ctxt =
  let val L = Programming_Sequent.get ctxt
   in if i < length L
      then Lazy.force (#3 (List.nth (L,i)))
      else []
   end

fun reason_programming_implication' mode ctxt sequent =
  let val inhabited_rule = #inhabited_rule mode
      val thm = sequent RS inhabited_rule
   in Phi_Reasoners.extract_implied_facts ctxt thm
  end handle THM _ => []

fun reason_programming_implication ctxt =
      reason_programming_implication' (Phi_Working_Mode.mode1 ctxt) ctxt


fun gen_update_programming_sequent' put sequent ctxt =
  let val mode = Phi_Working_Mode.mode1 ctxt
   in if #is_on_going_construction mode (Thm.prop_of sequent)
      then put ctxt (K (sequent, sequent, Lazy.lazy (fn () =>
                                       reason_programming_implication' mode ctxt sequent)))
      else put ctxt (fn (_, construction, implication)::_ => (sequent, construction, implication)
                      | [] => (sequent, Drule.dummy_thm, Lazy.value []))
  end

val update_programming_sequent' = gen_update_programming_sequent'
        (fn ctxt => fn data => Programming_Sequent.map (fn L => data L :: tl L) ctxt)


structure Enter_Programming_Environ =
              Hooks (type arg = int (*level of the environ, starting from 0*)
                     type state = context_state)

fun enter_programming_environ' stat =
  let
    val level = length (Programming_Sequent.get (fst stat))
    val (ctxt',sequent') = Enter_Programming_Environ.invoke (Context.Proof (fst stat)) level stat
  in gen_update_programming_sequent'
          (fn ctxt => fn data => Programming_Sequent.map (fn L => data L :: L) ctxt)
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

fun get_thm_fast ctxt name =
      case Facts.lookup (Context.Proof ctxt) (Proof_Context.facts_of ctxt) name
        of SOME thm => #thms thm |> map (Thm.transfer' ctxt)
         | _ => []

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>this\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => [the_programming_sequent' ctxt]))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>construction\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => [the_construction ctxt]))

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
                   ( get_thm_fast ctxt "IDE_CP_Core.\<phi>implication" @ Useful_Thms.get ctxt)
          )))

fun freeze_dynamic_lemmas ctxt =
  let val facts = Proof_Context.facts_of ctxt
      fun get name = #thms (the (Facts.lookup (Context.Proof ctxt) facts name))
                  |> map (Thm.transfer' ctxt)
   in ctxt
   (*We fix the dynamic lemmas to be local lemmas so that the sledgehammer can access them*)
   |> Proof_Context.put_thms true ("the_\<phi>", SOME (get "IDE_CP_Core.\<phi>"))
   |> Proof_Context.put_thms true ("the_\<phi>lemmata",
                                   SOME (Named_Theorems.get ctxt \<^named_theorems>\<open>\<phi>lemmata\<close>))
  end

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
                   ( get_thm_fast ctxt "\<phi>implication_previous"
                   @ Named_Theorems.get ctxt \<^named_theorems>\<open>\<phi>lemmata\<close>
                   @ Useful_Thms.get ctxt)
          )))


fun catch msg f tm = (f tm) handle TERM _ => raise TERM (msg, [tm])
fun catch_th i msg f th = (f th) handle THM _ => raise THM (msg, i, [th])
                                      | TERM _ => raise TERM (msg, [prop_of th])

structure Thesis = Proof_Data (
  type T = cterm option
  val init = K NONE
)

fun put_thesis thesis = Thesis.put (SOME thesis)
fun get_thesis ctxt =
      case Thesis.get ctxt
        of SOME x => x
         | NONE => err_bad_env ()

fun process_lemmata rules ctxt thm =
       Simplifier.asm_full_simplify (ctxt addsimps rules ctxt) thm
    |> PLPR_Syntax.elim_ant_sequence_or_HOL_conj

val simplify_lemmata = Attrib.setup_config_bool \<^binding>\<open>\<phi>simplify_lemmata\<close> (K true)

fun process_useful_lemmata simp_lemmata ctxt thm =
       (if simp_lemmata andalso Config.get ctxt simplify_lemmata
        then Simplifier.asm_full_simplify (ctxt addsimps Useful_Thms.get ctxt) thm
        else thm)
    |> PLPR_Syntax.elim_ant_sequence_or_HOL_conj




(*** The useful attribute ***)
fun add_useful simplify thm generic_ctxt =
      fold Useful_Thms.add_thm
          (process_useful_lemmata simplify (Context.proof_of generic_ctxt) thm)
          generic_ctxt

fun del_useful simplify thm generic_ctxt =
      fold Useful_Thms.del_thm
          (process_useful_lemmata simplify (Context.proof_of generic_ctxt) thm)
          generic_ctxt

val add_useful_attr = Thm.declaration_attribute o add_useful
val del_useful_attr = Thm.declaration_attribute o del_useful

fun add_del add del = Scan.lift (Args.add >> K add || Args.del >> K del || Scan.succeed add);

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>useful\<close> (
      add_del add_useful_attr del_useful_attr --
      Scan.lift (Scan.optional (Args.$$$ "simplified" >> K true) false)
      >> (fn (opr, flag) => opr flag)
    )
  "theorems to be inserted in the automatic proving, \
  \having the same effect of using the @{command using} command."

#> Context.theory_map (Phi_Reasoners.Tactic_Configures.add 0
      (fn _ => fn (aux,tac,ctxt) =>
          (Proof_Context.get_thms ctxt "IDE_CP_Core.\<phi>implication" @ aux,tac,ctxt)))
)


(*
val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>useful\<close> ()
) *)

end
