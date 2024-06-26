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

  val the_time : Proof.context -> int
  val the_construction : Proof.context -> thm
  val the_programming_sequent' : Proof.context -> thm
  val the_state_sequent : Proof.state -> thm
  val set_state_sequent : thm -> Proof.state -> Proof.state
  val map_state_sequent : (context_state -> context_state) -> Proof.state -> Proof.state
  val map_state_sequent_result : (context_state -> 'a * context_state) -> Proof.state -> 'a * Proof.state
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
  structure On_Updating_State_Sequent : HOOKS

end

structure Phi_Envir : PHI_ENVIR = struct
open Thm Term HOLogic Phi_Help Phi_Envir
exception NDBG of thm

structure Programming_Sequent = Proof_Data (
  type T = (thm (*sequent*)
          * thm (*the latest construction*)
          * thm list lazy (*implication*)
          * int (*time*)
          ) list;
  val init = (K [])
)

structure On_Updating_State_Sequent = Hooks (
  type arg = { mode: Phi_Working_Mode.working_mode,
               is_ready_construction: bool,
               latest_ready_construction: thm option,
               time : int }
  type state = context_state
)

fun err_bad_env () = error ("Not in the \<phi> programming environment")

fun the_time ctxt =
  case Programming_Sequent.get ctxt of (_, _, _, time)::_ => time
                                     | [] => 0

fun the_construction ctxt =
  case Programming_Sequent.get ctxt of (_,thm, _, _)::_ => thm
                                     | [] => Drule.dummy_thm

val under_programming_environ = not o null o Programming_Sequent.get
val exit_programming_environ = Programming_Sequent.map (fn L => tl L)

fun the_programming_sequent' ctxt =
  case Programming_Sequent.get ctxt of (thm, _, _, _)::L => thm
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
   in case Phi_Reasoners.extract_implied_fact {wrap_all=false} ctxt thm
   of SOME ths => ths
    | NONE => error "Internal BUG: Fail to extract pure fact implied inside"
  end handle THM _ => []

fun reason_programming_implication ctxt =
      reason_programming_implication' (Phi_Working_Mode.mode1 ctxt) ctxt


fun gen_update_programming_sequent' put sequent ctxt =
  let val mode = Phi_Working_Mode.mode1 ctxt
      val is_read = #constr_is_ready mode (Thm.prop_of sequent)
      val old_data = Programming_Sequent.get ctxt
      val time = case old_data of [] => 1 | (_,_,_,time)::_ => time+1
      fun invoke_hook ready_constr =
            On_Updating_State_Sequent.invoke (Context.Proof ctxt) {
                mode = mode,
                is_ready_construction = is_read,
                latest_ready_construction = ready_constr,
                time = time
              }
   in if is_read
      then invoke_hook (SOME sequent) (ctxt, sequent)
        |> (fn (ctxt', sequent') =>
           put ctxt' (sequent', sequent', Lazy.lazy (fn () =>
                          reason_programming_implication' mode ctxt' sequent'), time))
      else (case old_data
        of [] => invoke_hook NONE (ctxt, sequent)
              |> (fn (ctxt', sequent') =>
                    put ctxt' (sequent', Drule.dummy_thm, Lazy.value [], time))
         | (_, construction, implication, _)::_ =>
                 invoke_hook (SOME construction) (ctxt, sequent)
              |> (fn (ctxt', sequent') =>
                    put ctxt' (sequent', construction, implication, time))
      )
  end

val update_programming_sequent' = gen_update_programming_sequent'
        (fn ctxt => fn data => Programming_Sequent.map (fn L => data :: tl L) ctxt)


structure Enter_Programming_Environ =
              Hooks (type arg = int (*level of the environ, starting from 0*)
                     type state = context_state)

fun enter_programming_environ' stat =
  let
    val level = length (Programming_Sequent.get (fst stat))
    val (ctxt',sequent') = Enter_Programming_Environ.invoke (Context.Proof (fst stat)) level stat
  in gen_update_programming_sequent'
          (fn ctxt => fn data => Programming_Sequent.map (fn L => data :: L) ctxt)
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

fun map_state_sequent_result f s =
  s |> Proof.map_context_result (fn ctxt => 
          case f (ctxt, the_state_sequent s)
            of (result, (ctxt, sequent')) => ((result,sequent'), ctxt))
    |-> (fn (result, sequent') => set_state_sequent sequent'
                               #> pair result)

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
  type T = cterm list
  val init = K []
)

fun put_thesis thesis ctxt =
  let val prevs = Thesis.get ctxt
      fun bind_term i tm =
            Variable.maybe_bind_term (("\<phi>thesis", i), SOME tm)
         #> Variable.maybe_bind_term (("\<phi>target", i), try Phi_Syntax.dest_target_assertion tm)
   in ctxt
      |> Thesis.map (fn L => thesis :: L)
      |> bind_term 0 (Thm.term_of thesis)
      |> fold_index (fn (i, tm) => bind_term (i+1) (Thm.term_of tm)) prevs
  end

fun get_thesis ctxt =
      case Thesis.get ctxt
        of x :: _ => x
         | [] => err_bad_env ()

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
