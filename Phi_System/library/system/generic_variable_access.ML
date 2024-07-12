(* library/system/generic variable access.ML
   AUTHOR: Anonymous Authors

   Access (get and set) generic variables.
   A generic variable can be a local value, a variable, or any other registered thing.
*)

(*** Signature ***)
signature GENERIC_VARIABLE_ACCESS = sig
include GENERIC_VARIABLE_ACCESS

type evaluation = context_state -> (cterm (*abstract object*) * cterm (*phi type*)) option

(** Value Context **)
val open_context : cterm list (*arguments*) -> Proof.context -> Proof.context
val assign_anony_local_val : typ option -> Proof.context -> string * Proof.context
val bind_generic_vars : (xstring (*external name*) * (cterm * evaluation)) list -> Proof.context -> Proof.context
val lookup_bindings : Proof.context -> xstring -> (cterm * evaluation) option
val is_a_binding : Proof.context -> xstring -> bool
val under_context : Proof.context -> bool

val mode_synthesis : bool Config.T



(** Parser for Access **)

val dereference_generic_var  : Proof.context -> term -> cterm option
val dereference_generic_var1 : Proof.context -> term -> cterm

(** Process of Initial Arguments **)

(*controls if clean all values in the initial sequent of a procedure construction.
  By default, values in a routine construction will be cleaned but not in ordinary procedures.*)

val pattern_of_value_rule : (int -> term -> term) -> term -> term
val register_value_spec_thms : (int -> term -> term)
                            -> (Position.T * thm list) list
                            -> Proof.context -> Proof.context
  (*note, this is not for updating or accessing local values*)
val register_value_spec_thms_no_dup : (int -> term -> term)
                                   -> (Position.T * thm list) list
                                   -> Proof.context -> Proof.context

type process_of_arguments = context_state -> context_state

val store_value_and_clean : process_of_arguments
val store_value_no_clean  : process_of_arguments

structure Process_of_Argument : GENERIC_DATA


(** Basic Operations about Local Values **)

val extract_values : int * bool -> context_state -> thm list * context_state
  (*extracts local values given in a programming sequent,
    with an option to also remove the values in the sequent*)

val push_values : thm list -> context_state -> context_state

val is_local_value: term -> bool
val number_of_values : term -> int

end

structure Generic_Variable_Access : GENERIC_VARIABLE_ACCESS = struct
open Generic_Variable_Access

(*** Value Context ***)

type evaluation = context_state -> (cterm * cterm) option

type value_context =
        ( cterm list (*argument list, of type 'a \<phi>arg.*)
        * (cterm * evaluation) Symtab.table
          (*binding table of local values, key: external name of the fixed variable*)
          (*Free variables in the terms must use external names, just as what is parsed and before
              checked from the user inputs.
            Use Variable.revert_fixed if it is a fixed free variable!

            P.S. Actually I'm thinking if we can use Syntax.uncheck_term*)
        * int (*a counter assigning identities to anonymous local values*))

structure Value_Ctxt = Proof_Data (
  type T = value_context option
  val init = K NONE
)

fun bad_ctxt () = error "Value context has not been set. Not under a programming context."

fun under_context ctxt = is_some (Value_Ctxt.get ctxt)

fun value_context_of ctxt =
  case Value_Ctxt.get ctxt of SOME c => c | _ => bad_ctxt ()

fun map_value_context f =
  Value_Ctxt.map (fn SOME x => SOME (f x)
                   | NONE => bad_ctxt())

fun open_context arguments =
  Value_Ctxt.map (fn SOME (_, LV, CNT) => SOME (map Thm.trim_context_cterm arguments, LV, CNT)
                   | NONE => SOME (map Thm.trim_context_cterm arguments, Symtab.empty, 0))

fun assign_anony_local_val ty ctxt =
  let
    val (ARG, LV, CNT) = value_context_of ctxt
    val name = "\<v>" ^ string_of_int CNT
  in ctxt
    |> Value_Ctxt.put (SOME (ARG, LV, CNT + 1))
    |> Proof_Context.add_fixes [(Binding.name name, ty, NoSyn)]
    |> apfst hd
  end

fun bind_generic_vars vals =
  map_value_context (fn (A,V,N) => (A, fold (Symtab.update o apsnd (apfst Thm.trim_context_cterm)) vals V ,N))

fun lookup_bindings ctxt = Symtab.lookup (#2 (value_context_of ctxt))

fun is_a_binding ctxt =
  case Value_Ctxt.get ctxt
    of NONE => (fn _ => false)
     | SOME c => Symtab.defined (#2 c)

(*** Parser for Access ***)

(* Data *)

(*type value_parser_key =
  ( int (*priority, descend order, the higher one is attempted first*)
  * string (*name*))

val value_parser_key_ord = prod_ord int_ord string_ord

type value_parser = (Proof.context -> term -> term option)

structure ParserTab = Table(type key = value_parser_key val ord = value_parser_key_ord)

structure Value_Parsers = Generic_Data (
  type T = value_parser ParserTab.table
  val empty = ParserTab.empty
  val merge = ParserTab.merge (K true)
)

fun add_parser parser = Value_Parsers.map (ParserTab.update_new parser)*)


(* Translation *)

fun index_val ctxt i =
  let
    val (A,_,_) = case Value_Ctxt.get ctxt
                      of SOME c => c
                       | _ => error ("Cannot access the " ^ string_of_int i ^ "th argument.\n\
                                     \Not under a programming context.")
  in if 1 <= i andalso i <= length A
     then List.nth (A, i-1)
     else error ("The programmign context only has " ^ string_of_int (length A) ^
                 " arguments, but it attempts to access the " ^ string_of_int i ^ "th argument.")
  end

fun no_binding_found N = error ("Generic variable named "^N^" is not found.")

fun trans_error ctxt (V as Free _)
      = error (Pretty.string_of (Pretty.block [
               Pretty.str "Generic variable named ",
               Syntax.pretty_term ctxt V, Pretty.str " is not found."
             ]))
  | trans_error ctxt X
      = error (Pretty.string_of (Pretty.block [
               Pretty.str "There is no value or variable bound on term ",
               Syntax.pretty_term ctxt X
             ]))

fun dereference_generic_var ctxt (Free (s, _)) =
      if can Value.parse_int s
      then SOME (index_val ctxt (Value.parse_int s))
      else Option.map fst (Symtab.lookup (#2 (value_context_of ctxt)) s)
  | dereference_generic_var ctxt (Const ("_constrain", _) $ X $ _)
      = dereference_generic_var ctxt X
  | dereference_generic_var _ _ = NONE


(*fun dereference_generic_var ctxt X =
  let
    val tab = Value_Parsers.get (Context.Proof ctxt)
  in
    case ParserTab.fold_rev (fn (_, f) => (fn NONE => f ctxt X
                                            | some => some)) tab NONE
      of NONE => fallback_trans ctxt X
       | some => some
  end*)

fun dereference_generic_var1 ctxt X =
  case dereference_generic_var ctxt X
    of SOME y => y
     | NONE => trans_error ctxt X
(*
fun dereference_generic_var0 ctxt v =
  if under_context ctxt
  then the_default v (dereference_generic_var ctxt v)
  else v *)

val mode_synthesis = Config.declare_bool ("\<phi>-System.GVA.mode_synthesis", \<^here>) (K false)

local open Ast

fun ident X = Appl[Constant \<^const_syntax>\<open>\<phi>identifier\<close>, X]
(*fun parse_elements ret (Appl [Constant \<^syntax_const>\<open>_identifier_element_\<close>, X, idx])
      = parse_elements (idx :: ret) X
  | parse_elements ret (Appl [Constant \<^syntax_const>\<open>_identifier_element_0_\<close>, X])
      = (ret, X)
  | parse_elements _ _ = error "Internal bug #fc1bc973-fab2-4706-a68e-6d4ce9cbe7d0"
*)

fun mk_element_path (idx :: R) =
      Appl [Constant \<^const_syntax>\<open>Cons\<close>,
              Appl [Constant \<^syntax_const>\<open>_MK_ag_idx_\<close>, idx],
              mk_element_path R]
  | mk_element_path [] = Constant \<^const_syntax>\<open>Nil\<close>

in

val _ = Theory.setup (Sign.parse_ast_translation ([
  (\<^syntax_const>\<open>_identifier_\<close>, (fn _ => fn [X] => ident X)),
  (\<^syntax_const>\<open>_identifier_1_\<close>, (fn _ => fn _ => Variable "1")),
  (\<^syntax_const>\<open>_identifier_num_\<close>, (fn _ => fn [X] => X)),
  (\<^syntax_const>\<open>_get_\<phi>var_\<close>, (fn _ => fn [X] =>
        Appl[ Constant \<^const_syntax>\<open>Value_of\<close>,
              Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>,
              ident X,
              Constant \<^const_syntax>\<open>Nil\<close> ])),
(*  (\<^syntax_const>\<open>_\<phi>element_step_\<close>, fn ctxt => fn [left, idx] =>
    (case left
       of Appl [Constant \<^const_syntax>\<open>Value_of\<close>, x, idt, path]
            => let fun insert (Appl [Constant \<^const_syntax>\<open>Cons\<close>, X, Y]) =
                          Appl [Constant \<^const_syntax>\<open>Cons\<close>, X, insert Y]
                     | insert (Constant \<^const_syntax>\<open>Nil\<close>) =
                          Appl [Constant \<^const_syntax>\<open>Cons\<close>,
                                Appl [Constant \<^syntax_const>\<open>_MK_ag_idx_\<close>, idx],
                                Constant \<^const_syntax>\<open>Nil\<close>]
                in Appl [Constant \<^const_syntax>\<open>Value_of\<close>, x, idt, insert path]
               end
        | _ => error "Syntax Error: Aggregate Element Access operator \<tribullet> can only be used after variables like $x.")), *)
  (\<^syntax_const>\<open>_set_\<phi>var_\<close>, (fn _ => fn [V,Y] =>
        Appl[ Constant \<^const_syntax>\<open>Set_Value\<close>,
              Y,
              ident V,
              Constant \<^const_syntax>\<open>Nil\<close> ])),
  (\<^syntax_const>\<open>_identifier_id_\<close>, (fn _ => fn [X] =>
      Appl [Constant \<^syntax_const>\<open>_abs\<close>, X, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>])),
  (\<^syntax_const>\<open>_identifier_logic_\<close>, (fn _ => fn [X] => X))
]))

end

fun check_term ctxt (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ Abs (N,_,_)) =
      Thm.term_of (dereference_generic_var1 ctxt (Free (N, dummyT)))
  | check_term ctxt (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ X) =
      Thm.term_of (dereference_generic_var1 ctxt X)
  | check_term ctxt ((H1 as Const (\<^const_name>\<open>Value_of\<close>, _))
                        $ (H2 as Const (\<^const_name>\<open>Pure.dummy_pattern\<close>, _))
                        $ (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ Abs (N,_,_))
                        $ element_index)
      = let val v = lookup_bindings ctxt N
                  |> Option.mapPartial (fn (_, get) => get (ctxt, Phi_Envir.the_construction ctxt))
         in if Config.get ctxt mode_synthesis
            then H1 $ (case (v, element_index)
                         of (SOME (x, _), Const (\<^const_name>\<open>Nil\<close>, _)) =>
                                 Type.constraint (fastype_of (Thm.term_of x)) H2
                          | _ => H2)
                    $ Thm.term_of (dereference_generic_var1 ctxt (Free (N, dummyT)))
                    $ element_index
            else (case v of SOME (x,T) =>
                              (case element_index
                                 of Const (\<^const_name>\<open>Nil\<close>, _) => Thm.term_of x
                                  | _ => Generic_Element_Access.get_element_of_abstract_object
                                              ctxt (x,T,Thm.cterm_of ctxt element_index)
                                         |> Thm.term_of)
                          | _ => no_binding_found N)
        end
  | check_term ctxt (A $ B) = check_term ctxt A $ check_term ctxt B
  | check_term ctxt (Abs (N,TY,X)) = Abs (N,TY, check_term ctxt X)
  | check_term _ X = X

val _ = Theory.setup (Context.theory_map (Syntax_Phases.term_check ~110 "\<phi>-System.GVA" (map o check_term)))


(*** Basic Operations about Local Values ***)

val value_extraction_rule_no_remove =
  @{lemma' \<open>x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<w>\<i>\<t>\<h> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T)\<close>
        by (simp add: Transformation_def)}

val value_extraction_rule_remove =
  @{lemma' \<open>x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Void \<w>\<i>\<t>\<h> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T)\<close>
        by (simp add: Transformation_def)}

val implies_prod_left_1 = @{lemma
  \<open> L' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P
\<Longrightarrow> R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> Q
\<Longrightarrow> L' * R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (R::'a::sep_magma_1 BI) \<w>\<i>\<t>\<h> P \<and> Q \<close>
  by (unfold Transformation_def split_paired_All, fastforce)}

fun is_local_value (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const(\<^const_name>\<open>Val\<close>, _) $ _ $ _)) = true
  | is_local_value _ = false

fun values_number ret (Const (@{const_name Subjection}, _) $ T) = values_number ret T
  | values_number ret (Const (@{const_name ExSet}, _) $ T) = values_number ret T
  | values_number ret (Abs (_, _, T)) = values_number ret T
  | values_number ret (Const (\<^const_name>\<open>times\<close>, _) $ X $ L)
      = values_number (if is_local_value X then ret+1 else ret) L
  | values_number ret X = if is_local_value X then ret+1 else ret

val number_of_values = values_number 0

fun extract_values (num_limit, remove) (ctxt, sequent) =
  if num_limit = 0 then ([], (ctxt, sequent))
  else let
      val mode = Phi_Working_Mode.mode1 ctxt
   in if number_of_values (#spec_of mode (Thm.prop_of sequent)) = 0
      then ([], (ctxt, sequent))
      else let
      val _ = if #constr_is_ready mode (Thm.prop_of sequent)
              then ()
              else raise THM ("The sequent is not ready for construction", 0, [sequent])
      fun gen_rule_err rule () =
             error ("Fail to extract a value from the sequent. A extraction rule fails: \n" ^
                    Thm.string_of_thm ctxt rule)

      fun extr_rule (Const(\<^const_name>\<open>Val\<close>, _) $ _ $ _) =
            SOME (value_extraction_rule_remove, value_extraction_rule_no_remove)
        | extr_rule _ = NONE

      fun gen_rule num thm =
        if num = 0 then (@{thm transformation_refl} RS thm) else
        case Phi_Syntax.dest_transformation (Thm.major_prem_of thm)
          of (Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _ ,_,_)
                => gen_rule num (@{thm Subjection_transformation} RS thm)
           | (Const (\<^const_name>\<open>ExSet\<close>, _) $ _ $ _ ,_,_)
                => gen_rule num (@{thm ExSet_transformation} RS thm)
           | (Const (\<^const_name>\<open>times\<close>, _) $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ tm) $ _ ,_,_)
                => (case extr_rule tm
                      of SOME (remove_rule, no_remove_rule) =>
                          let val rule = if remove then remove_rule else no_remove_rule
                              val bi_prod_rule =
                                    case Phi_Syntax.dest_transformation (Thm.concl_of rule)
                                      of (_,Const(\<^const_name>\<open>one_class.one\<close>,_),_) =>
                                           implies_prod_left_1
                                       | _ => @{thm transformation_bi_frame}
                              val m = Thm.nprems_of rule
                           in (rule RS (bi_prod_rule RS thm))
                           |> Phi_Reasoner.reason1 (gen_rule_err rule) NONE (SOME m) ctxt
                           |> gen_rule (num - 1)
                          end
                       | _ => gen_rule num (@{thm transformation_left_frame} RS thm)
                      )
           | (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _ , _, _)
                => gen_rule num (@{thm transformation_left_frame} RS thm)
           | (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ tm, _ , _)
                => (case extr_rule tm
                      of SOME (remove_rule, no_remove_rule) =>
                          let val rule = if remove then remove_rule else no_remove_rule
                              val m = Thm.nprems_of rule
                           in (rule RS thm)
                           |> Phi_Reasoner.reason1 (gen_rule_err rule) NONE (SOME m) ctxt
                          end
                       | _ => @{thm transformation_refl} RS thm
                      )
           | _ => @{thm transformation_refl} RS thm
      val initial = sequent RS #transformation_rule mode
      val rule = gen_rule num_limit initial
      val (sequent', vals) = rule
                |> PLPR_Syntax.elim_ant_seq_or_HOL_conj
                |> apsnd (fn th => th |> PLPR_Syntax.elim_ant_sequence_or_HOL_conj |> rev
                                      |> (fn [] => []
                                           | (H::L) => case Thm.prop_of H
                                                         of _ $ (Const (\<^const_name>\<open>True\<close>, _)) => L
                                                          | _ => H::L))
   in (vals, (ctxt, sequent'))
  end
  end


val rule_push_a_value =
  @{lemma' \<open>  \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T)
          \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B
          \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> \<v>\<a>\<l>[v] T) * B \<close>
      for A :: \<open>'a::sep_magma_1 BI\<close>
       by (clarsimp simp add: Action_Tag_def Transformation_def)}

fun push_values [] s = s
  | push_values values (ctxt,sequent) =
  let
    val mode = Phi_Working_Mode.mode1 ctxt
    val initial = sequent RS #transformation_rule mode
    val sequent' = fold (fn v => fn th => (v RS' (ctxt, rule_push_a_value)) RS th) values initial
   in (ctxt, fst (PLPR_Syntax.elim_ant_seq_or_HOL_conj (@{thm transformation_refl} RS sequent')))
  end

fun setup_lemmata pos rules ctxt =
  let val facts = maps (fn thm =>
                   let val thm = PLPR_Syntax.strip_tags ctxt thm
                    in case Phi_Reasoners.extract_implied_fact {wrap_all=false} ctxt (thm RS @{thm Satisfiable_I})
                    of NONE => error "Internal BUG: Fail to extract pure fact implied inside"
                     | SOME l => l
                   end
                  ) rules
   in Phi_Sys.add_lemmata pos facts ctxt
  end


(*** Initial Process for Arguments ***)

(** Predefined Processes **)

fun get_val_of_spec_thm th =
  case PLPR_Syntax.dest_tags (Thm.prop_of th)
    of Const (\<^const_name>\<open>Satisfaction\<close>, _)
         $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
         $ _ => V
     | _ => raise THM ("Not a specification theorem of a value!", 0, [th])

fun pattern_of_value_rule mk_var tm =
  let val i = maxidx_of_term tm + 1
      fun pattern_of ((Trueprop as Const(\<^const_name>\<open>Trueprop\<close>, _)) $ X) =
            Trueprop $ pattern_of X
        | pattern_of ((Tag as Const(\<^const_name>\<open>Action_Tag\<close>, _)) $ X $ G) =
            Tag $ pattern_of X $ G
        | pattern_of (  Const (\<^const_name>\<open>Satisfaction\<close>, T1)
                     $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2) $ V)
                     $  TM ) =
            Const (\<^const_name>\<open>Satisfaction\<close>, T1)
               $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2) $ mk_var i V)
               $ Var (("spec",i), fastype_of TM)
        | pattern_of TM = raise TERM ("Not a specification theorem of a value!", [TM])
   in pattern_of tm
  end

fun register_value_spec_thms mk_var pos_rules ctxt = ctxt
  |> Context.proof_map (
      Phi_Reasoner.add_rules (maps (fn (pos, rules) => map (fn rule =>
        let val i = maxidx_of_term (Thm.prop_of rule) + 1
            val pattern = pattern_of_value_rule mk_var (Thm.prop_of rule)
         in ([rule], pos, Phi_Reasoner.NORMAL_LOCAL_CUT', SOME (@{reasoner_group %local_values}),
             [(pattern, NONE)], [], NONE) end
      ) rules) pos_rules))
    |> fold (uncurry setup_lemmata) pos_rules

fun register_value_spec_thms_no_dup mk_var pos_rules ctxt =
  let val pos_rules' = maps (fn (pos, rules) => map (pair pos) rules) pos_rules
                    |> distinct (fn ((_, th1), (_, th2)) =>
                          get_val_of_spec_thm th1 aconv get_val_of_spec_thm th2)
   in ctxt
   |> Context.proof_map (Phi_Reasoner.add_rules (map (fn (pos, rule) =>
        let val pattern = pattern_of_value_rule mk_var (Thm.prop_of rule)
         in ([rule], pos, Phi_Reasoner.NORMAL_LOCAL_CUT', SOME (@{reasoner_group %local_values}),
             [(pattern, NONE)], [], NONE)
        end
      ) pos_rules'))
   |> fold (uncurry setup_lemmata) pos_rules
  end


fun gen_default_process' clean pos (ctxt,sequent) =
  let
    val (rules, (ctxt',sequent')) = extract_values (~1, clean) (ctxt,sequent)
    val args = rules |> map (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Satisfaction\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
                                  $ _)                                
                 => Thm.cprop_of th |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg
             | _ => error "Internal Bug q34v6 nu89p")
    fun extract_x_T th =
      let val ctm = Thm.cprop_of th |> Thm.dest_arg |> Thm.dest_arg
       in (Thm.dest_arg1 ctm, Thm.dest_arg ctm)
      end
    val binds = rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Satisfaction\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
                                  $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ (X as Free (N,_)) $ _))
                 => SOME (Variable.revert_fixed ctxt' N,
                            (Thm.cprop_of th |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg,
                             K (SOME (extract_x_T th))))
             | _ => NONE)
    val binds'= rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Satisfaction\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ (V as Free (N,_)))
                                  $ X')
                 => SOME (Variable.revert_fixed ctxt' N,
                            (Thm.cprop_of th |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg,
                            K (case X' of (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)
                                  => SOME (extract_x_T th)
                                | _ => NONE)))
             | _ => NONE)

  in ctxt'
  |> open_context args
  |> register_value_spec_thms (K I) [(pos,rules)]
  |> bind_generic_vars (binds' @ binds)
  |> rpair sequent'
  end

fun is_value (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ _ $ _)) = true
  | is_value _ = false
fun has_value (Const (\<^const_name>\<open>times\<close>,_) $ X $ R) = is_value X orelse has_value R
  | has_value X = is_value X

fun gen_default_process clean pos (ctxt,sequent) =
  if has_value (#4 (Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)))
  then gen_default_process' clean pos (ctxt,sequent)
  else (open_context [] ctxt, sequent)

(** Mechanism **)

type process_of_arguments = context_state -> context_state

val store_value_and_clean = gen_default_process true  Position.none
val store_value_no_clean  = gen_default_process false Position.none

structure Process_of_Argument = Generic_Data (
  type T = process_of_arguments option
  val empty = NONE
  val merge = merge_options
)

val _ = Theory.setup (Context.theory_map (
Phi_Envir.Enter_Programming_Environ.add 20 (fn level => fn (ctxt,sequent) =>
  if level = 0
  andalso #name (Phi_Working_Mode.mode1 ctxt) = #name Phi_Working_Mode.programming
  then the_default store_value_and_clean (Process_of_Argument.get (Context.Proof ctxt)) (ctxt,sequent)
  else (ctxt,sequent)
)))

end

