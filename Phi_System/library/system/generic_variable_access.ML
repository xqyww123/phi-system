(* library/system/generic variable access.ML
   AUTHOR: Qiyuan Xu

   Access (get and set) generic variables.
   A generic variable can be a local value, a variable, or any other registered thing.
*)

(*** Signature ***)
signature GENERIC_VARIABLE_ACCESS = sig

type get_value = context_state -> (cterm (*abstract object*) * cterm (*phi type*)) option

(** Value Context **)
val open_value_context : cterm list (*arguments*) -> Proof.context -> Proof.context
val assign_anony_local_val : typ option -> Proof.context -> string * Proof.context
val bind_local_vals  : (xstring (*external name*) * (cterm * get_value)) list -> Proof.context -> Proof.context
val lookup_bindings : Proof.context -> xstring -> (cterm * get_value) option
val is_under_value_context : Proof.context -> bool

val mode_synthesis : bool Config.T

(** Parser for Access **)
(*type value_parser_key =
  ( int (*priority, descend order, the higher one is attempted first*)
  * string (*name*))

type value_parser = (Proof.context -> term -> term option)

val add_parser : value_parser_key * value_parser -> Context.generic -> Context.generic *)
val translate_value  : Proof.context -> term -> cterm option
val translate_value1 : Proof.context -> term -> cterm


(** Initial Arguments **)

val register_value_spec_thms : Position.T -> thm list -> Context.generic -> Context.generic
  (*so that the values can be synthesised*)

type process_of_arguments = context_state -> context_state

val store_value_and_clean : process_of_arguments
val store_value_no_clean  : process_of_arguments

structure Process_of_Argument : GENERIC_DATA

(* other operations about value *)

val add_extraction_rule : string (*const name*) * (thm * thm) -> Context.generic -> Context.generic
val extract_values : int * bool -> context_state -> thm list * context_state
val push_values : thm list -> context_state -> context_state

val is_local_value: term -> bool
val number_of_values : term -> int

end

structure Generic_Variable_Access : GENERIC_VARIABLE_ACCESS = struct

(*** Value Context ***)

type get_value = context_state -> (cterm * cterm) option

type value_context =
        ( cterm list (*argument list, of type 'a \<phi>arg.*)
        * (cterm * get_value) Symtab.table
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

fun is_under_value_context ctxt = is_some (Value_Ctxt.get ctxt)

fun value_context_of ctxt =
  case Value_Ctxt.get ctxt of SOME c => c | _ => bad_ctxt ()

fun map_value_context f =
  Value_Ctxt.map (fn SOME x => SOME (f x)
                   | NONE => bad_ctxt())

fun open_value_context arguments =
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

fun bind_local_vals vals =
  map_value_context (fn (A,V,N) => (A, fold (Symtab.update o apsnd (apfst Thm.trim_context_cterm)) vals V ,N))

fun lookup_bindings ctxt = Symtab.lookup (#2 (value_context_of ctxt))

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

fun translate_value ctxt (Free (s, _)) =
      if can Value.parse_int s
      then SOME (index_val ctxt (Value.parse_int s))
      else Option.map fst (Symtab.lookup (#2 (value_context_of ctxt)) s)
  | translate_value ctxt (Const ("_constrain", _) $ X $ _)
      = translate_value ctxt X
  | translate_value _ _ = NONE


(*fun translate_value ctxt X =
  let
    val tab = Value_Parsers.get (Context.Proof ctxt)
  in
    case ParserTab.fold_rev (fn (_, f) => (fn NONE => f ctxt X
                                            | some => some)) tab NONE
      of NONE => fallback_trans ctxt X
       | some => some
  end*)

fun translate_value1 ctxt X =
  case translate_value ctxt X
    of SOME y => y
     | NONE => trans_error ctxt X
(*
fun translate_value0 ctxt v =
  if is_under_value_context ctxt
  then the_default v (translate_value ctxt v)
  else v *)

val mode_synthesis = Config.declare_bool ("\<phi>-System.GVA.mode_synthesis", \<^here>) (K false)

local open Ast

fun ident X = Appl[Constant \<^const_syntax>\<open>\<phi>identifier\<close>, X]
fun parse_elements ret (Appl [Constant \<^syntax_const>\<open>_identifier_element_\<close>, X, idx])
      = parse_elements (idx :: ret) X
  | parse_elements ret (Appl [Constant \<^syntax_const>\<open>_identifier_element_0_\<close>, X])
      = (ret, X)
  | parse_elements _ _ = error "Internal bug #fc1bc973-fab2-4706-a68e-6d4ce9cbe7d0"

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
  (\<^syntax_const>\<open>_\<phi>element_step_\<close>, fn ctxt => fn [left, idx] =>
    (case left
       of Appl [Constant \<^const_syntax>\<open>Value_of\<close>, x, idt, path]
            => let fun insert (Appl [Constant \<^const_syntax>\<open>Cons\<close>, X, Y]) =
                          Appl [Constant \<^const_syntax>\<open>Cons\<close>, X, insert Y]
                     | insert (Constant \<^const_syntax>\<open>Nil\<close>) =
                          Appl [Constant \<^const_syntax>\<open>Cons\<close>, Appl [Constant \<^syntax_const>\<open>_MK_ag_idx_\<close>, idx]]
                in Appl [Constant \<^const_syntax>\<open>Value_of\<close>, x, idt, insert path]
               end
        | _ => error "Syntax Error: Aggregate Element Access operator \<tribullet> can only be used after variables like $x.")),
  (\<^syntax_const>\<open>_set_\<phi>var_\<close>, (fn _ => fn [V,Y] =>
      case parse_elements [] V of (path, V') =>
        Appl[ Constant \<^const_syntax>\<open>Set_Value\<close>,
              Y,
              ident V',
              mk_element_path path ])),
  (\<^syntax_const>\<open>_identifier_id_\<close>, (fn _ => fn [X] =>
      Appl [Constant \<^syntax_const>\<open>_abs\<close>, X, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>])),
  (\<^syntax_const>\<open>_identifier_logic_\<close>, (fn _ => fn [X] => X))
]))

end

fun check_term ctxt (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ Abs (N,_,_)) =
      Thm.term_of (translate_value1 ctxt (Free (N, dummyT)))
  | check_term ctxt (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ X) =
      Thm.term_of (translate_value1 ctxt X)
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
                    $ Thm.term_of (translate_value1 ctxt (Free (N, dummyT)))
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


(*** Extract Value(s) ***)

structure Extraction_Rules = Generic_Data (
  type T = (thm (*remove*) * thm (*not remove*)) Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (eq_pair Thm.eq_thm Thm.eq_thm)
)

val add_extraction_rule = Extraction_Rules.map o Symtab.update_new

fun extract_values (num_limit, remove) (ctxt, sequent) =
  if num_limit = 0 then ([], (ctxt, sequent)) else
  let val mode = Phi_Working_Mode.mode1 ctxt
      val _ = if #is_on_going_construction mode (Thm.prop_of sequent)
              then ()
              else raise THM ("Not a ready on-going construction", 0, [sequent])
      fun gen_rule_err rule () =
             error ("Fail to extract a value from the sequent. A extraction rule fails: \n" ^
                    Thm.string_of_thm ctxt rule)
      fun gen_rule num thm =
        if num = 0 then (@{thm implies_refl} RS thm) else
        case Phi_Syntax.dest_transformation (Thm.major_prem_of thm)
          of (Const (\<^const_name>\<open>Subjection\<close>, _) $ _ $ _ ,_,_)
                => gen_rule num (@{thm Subjection_transformation} RS thm)
           | (Const (\<^const_name>\<open>ExSet\<close>, _) $ _ $ _ ,_,_)
                => gen_rule num (@{thm ExSet_transformation} RS thm)
           | (Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ tm) ,_,_)
                => (case head_of tm
                      of Const (C,_) => (
                          case Symtab.lookup (Extraction_Rules.get (Context.Proof ctxt)) C
                            of SOME (remove_rule, no_remove_rule) =>
                              let val rule = if remove then remove_rule else no_remove_rule
                                  val bi_prod_rule =
                                        case Phi_Syntax.dest_transformation (Thm.concl_of rule)
                                          of (_,Const(\<^const_name>\<open>one_class.one\<close>,_),_) =>
                                               @{thm implies_prod_right_1}
                                           | _ => @{thm implies_prod_bi_prod}
                                  val m = Thm.nprems_of rule
                               in (rule RS (bi_prod_rule RS thm))
                               |> Phi_Reasoner.reason1 (gen_rule_err rule) (SOME m) ctxt
                               |> gen_rule (num - 1)
                              end
                              | _ => gen_rule num (@{thm implies_right_prod} RS thm))
                       | _ => gen_rule num (@{thm implies_right_prod} RS thm)
                      )
           | (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _ , _, _)
                => gen_rule num (@{thm implies_right_prod} RS thm)
           | (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ tm, _ , _)
                => (case head_of tm
                      of Const (C,_) => (
                          case Symtab.lookup (Extraction_Rules.get (Context.Proof ctxt)) C
                            of SOME (remove_rule, no_remove_rule) =>
                              let val rule = if remove then remove_rule else no_remove_rule
                                  val m = Thm.nprems_of rule
                               in (rule RS thm)
                               |> Phi_Reasoner.reason1 (gen_rule_err rule) (SOME m) ctxt
                              end
                              | _ => @{thm implies_refl} RS thm)
                       | _ => @{thm implies_refl} RS thm
                      )
           | _ => @{thm implies_refl} RS thm
      val initial = sequent RS #transformation_rule mode
      val rule = gen_rule num_limit initial
      val (sequent', vals) = rule
                |> HOLogic.conj_elim ctxt
                |> apsnd (fn th => th |> HOLogic.conj_elims ctxt |> rev
                                      |> (fn [] => []
                                           | (H::L) => case Thm.prop_of H
                                                         of _ $ (Const (\<^const_name>\<open>True\<close>, _)) => L
                                                          | _ => H::L))
   in (vals, (ctxt, sequent'))
  end
  

(*** Initial Process for Arguments ***)

(** Predefined Processes **)

fun register_value_spec_thms pos rules =
  Phi_Reasoner.add_intro_rules (map (fn rule =>
    let
      val i = maxidx_of_term (Thm.prop_of rule) + 1
      val pattern =
            (case Thm.prop_of rule
               of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, T1)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2) $ V)
                                  $ TM )
                => \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, T1)
                                   $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2) $ V)
                                   $ Var (("spec",i), fastype_of TM) )
            | _ => raise THM ("Not a specification theorem of a value!", 0, [rule]))
    in ([rule], pos, Phi_Reasoner.LOCAL_CUT, 1000, [(pattern, SOME 1000)], [], NONE) end
  ) rules)


fun gen_default_process' clean pos (ctxt,sequent) =
  let
    val (rules, (ctxt',sequent')) = extract_values (~1, clean) (ctxt,sequent)
    val args = rules |> map (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
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
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
                                  $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ (X as Free (N,_)) $ _))
                 => SOME (Variable.revert_fixed ctxt' N,
                            (Thm.cprop_of th |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg,
                             K (SOME (extract_x_T th))))
             | _ => NONE)
    val binds'= rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ (V as Free (N,_)))
                                  $ X')
                 => SOME (Variable.revert_fixed ctxt' N,
                            (Thm.cprop_of th |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg,
                            K (case X' of (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)
                                  => SOME (extract_x_T th)
                                | _ => NONE)))
             | _ => NONE)

    fun setup_lemmata ctxt =
      let val facts = maps (fn thm =>
                        Phi_Reasoners.extract_implied_facts ctxt (thm RS @{thm Inhabited_I})
                      ) rules
       in ctxt |> Context.proof_map (
            fold (fold (fn th => Named_Theorems.add_thm \<^named_theorems>\<open>\<phi>lemmata\<close> th
                              #> Useful_Thms.add_thm th)
                  o Phi_Envir.process_useful_lemmata true ctxt) facts)
      end
  in ctxt'
  |> open_value_context args
  |> Context.proof_map (register_value_spec_thms pos rules)
  |> bind_local_vals (binds' @ binds)
  |> clean ? setup_lemmata
  |> rpair sequent'
  end

fun is_value (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ _ $ _)) = true
  | is_value _ = false
fun has_value (Const (\<^const_name>\<open>times\<close>,_) $ R $ X) = is_value X orelse has_value R
  | has_value X = is_value X

fun gen_default_process clean pos (ctxt,sequent) =
  if has_value (#4 (Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)))
  then gen_default_process' clean pos (ctxt,sequent)
  else (open_value_context [] ctxt, sequent)

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


(*** Other operations about value ***)
(*
fun extract_and_remove_leading_values num (ctxt,sequent) =
  let
    val mode = Phi_Working_Mode.mode1 ctxt
    val rule = @{thm "_rule_extract_and_remove_the_first_value_"}
    fun extract (ret,(ctxt,sequent)) =
          (ctxt, rule RS (sequent COMP #transformation_rule mode))
            |> Phi_Reasoner.reason NONE
            |> (fn SOME (ctxt', sequent'') =>
                      (case HOLogic.conj_elim ctxt' sequent''
                         of (sequent', value) => (value::ret, (ctxt', sequent')))
                 | NONE => Phi_Reasoner.error "Internal bug #vb7iop23")
   in funpow num extract ([], (ctxt,sequent))
  end
*)
fun push_values values (ctxt,sequent) =
  let
    val mode = Phi_Working_Mode.mode1 ctxt
    val initial = sequent RS #transformation_rule mode
    val sequent' = fold_rev (fn v => fn th => (v RS @{thm "_rule_push_a_value_"}) RS th) values initial
   in (ctxt, fst (HOLogic.conj_elim ctxt (@{thm implies_refl} RS sequent')))
  end

fun is_local_value (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const(\<^const_name>\<open>Val\<close>, _) $ _ $ _)) = true
  | is_local_value _ = false

fun values_number ret (Const (@{const_name Subjection}, _) $ T) = values_number ret T
  | values_number ret (Const (@{const_name ExSet}, _) $ T) = values_number ret T
  | values_number ret (Abs (_, _, T)) = values_number ret T
  | values_number ret (Const (\<^const_name>\<open>times\<close>, _) $ L $ X)
      = values_number (if is_local_value X then ret+1 else ret) L
  | values_number ret X = if is_local_value X then ret+1 else ret

val number_of_values = values_number 0

end
