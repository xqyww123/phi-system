(* library/system/generic variable access.ML
   AUTHOR: Qiyuan Xu

   Access (get and set) generic variables.
   A generic variable can be a local value, a variable, or any other registered thing.
*)

(*** Signature ***)
signature GENERIC_VARIABLE_ACCESS = sig

type get_value = context_state -> term option

(** Value Context **)
val open_value_context : term list (*arguments*) -> Proof.context -> Proof.context
val assign_anony_local_val : typ option -> Proof.context -> string * Proof.context
val bind_local_vals  : (xstring (*external name*) * (term * get_value)) list -> Proof.context -> Proof.context
val lookup_bindings : Proof.context -> xstring -> (term * get_value) option
val is_under_value_context : Proof.context -> bool

val mode_synthesis : bool Config.T

(** Parser for Access **)
type value_parser_key =
  ( int (*priority, descend order, the higher one is attempted first*)
  * string (*name*))

type value_parser = (Proof.context -> term -> term option)

val add_parser : value_parser_key * value_parser -> Context.generic -> Context.generic
val translate_value  : Proof.context -> term -> term option
val translate_value1 : Proof.context -> term -> term


(** Initial Arguments **)

(*performance hotsopt!*)
val collect_and_clean_value : bool (*whether to clean the Val \<phi>-types from the sequent*)
                           -> Proof.context -> thm (*sequent*)
                           -> thm (*sequent*) * thm list (*specs of value*)

val register_value_spec_thms : Position.T -> thm list -> Context.generic -> Context.generic
  (*so that the values can be synthesised*)

type process_of_arguments = context_state -> context_state

val store_value_and_clean : process_of_arguments
val store_value_no_clean  : process_of_arguments

structure Process_of_Argument : GENERIC_DATA

(* other operations about value *)

(*performance hotsopt!*)
val push_values : thm list -> context_state -> context_state
(*performance hotsopt!*)
val extract_and_remove_leading_values : int -> context_state -> thm list * context_state

end

structure Generic_Variable_Access : GENERIC_VARIABLE_ACCESS = struct

(*** Value Context ***)

type get_value = context_state -> term option

type value_context =
        ( term list (*argument list, of type 'a \<phi>arg.*)
        * (term * get_value) Symtab.table
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
  Value_Ctxt.map (fn SOME (_, LV, CNT) => SOME (arguments, LV, CNT)
                   | NONE => SOME (arguments, Symtab.empty, 0))

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
  map_value_context (fn (A,V,N) => (A, fold Symtab.update vals V ,N))

fun lookup_bindings ctxt = Symtab.lookup (#2 (value_context_of ctxt))

(*** Parser for Access ***)

(* Data *)

type value_parser_key =
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

fun add_parser parser = Value_Parsers.map (ParserTab.update_new parser)


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

fun fallback_trans ctxt (V as Free (s, _)) =
      if can Value.parse_int s
      then SOME (index_val ctxt (Value.parse_int s))
      else Option.map fst (Symtab.lookup (#2 (value_context_of ctxt)) s)
  | fallback_trans ctxt (Const ("_constrain", _) $ X $ _)
      = fallback_trans ctxt X
  | fallback_trans ctxt X = NONE


fun translate_value ctxt X =
  let
    val tab = Value_Parsers.get (Context.Proof ctxt)
  in
    case ParserTab.fold_rev (fn (_, f) => (fn NONE => f ctxt X
                                            | some => some)) tab NONE
      of NONE => fallback_trans ctxt X
       | some => some
  end

fun translate_value1 ctxt X =
  case translate_value ctxt X
    of SOME y => y
     | NONE => trans_error ctxt X

fun translate_value0 ctxt v =
  if is_under_value_context ctxt
  then the_default v (translate_value ctxt v)
  else v

val mode_synthesis = Config.declare_bool ("\<phi>-System.GVA.mode_synthesis", \<^here>) (K false)

local open Ast in

fun ident X = Appl[Constant \<^const_syntax>\<open>\<phi>identifier\<close>, X]

val _ = Theory.setup (Sign.parse_ast_translation ([
  (\<^syntax_const>\<open>_identifier_\<close>, (fn _ => fn [X] => ident X)),
  (\<^syntax_const>\<open>_identifier_1_\<close>, (fn _ => fn _ => Variable "1")),
  (\<^syntax_const>\<open>_identifier_num_\<close>, (fn _ => fn [X] => X)),
  (\<^syntax_const>\<open>_get_identifier_\<close>, (fn _ => fn [X] =>
      Appl[Constant \<^const_syntax>\<open>Value_of\<close>, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>, ident X])),
  (\<^syntax_const>\<open>_set_identifier_\<close>, (fn _ => fn [V,Y] =>
      Appl[Constant \<^const_syntax>\<open>Set_Value\<close>, Y, ident V])),
  (\<^syntax_const>\<open>_identifier_id_\<close>, (fn _ => fn [X] =>
      Appl [Constant \<^syntax_const>\<open>_abs\<close>, X, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>])),
  (\<^syntax_const>\<open>_identifier_logic_\<close>, (fn _ => fn [X] => X))
]))

end

fun check_term ctxt (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ Abs (N,_,_)) =
      translate_value0 ctxt (Free (N, dummyT))
  | check_term ctxt (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ X) = translate_value0 ctxt X
  | check_term ctxt ((H1 as Const (\<^const_name>\<open>Value_of\<close>, _))
                        $ (H2 as Const (\<^const_name>\<open>Pure.dummy_pattern\<close>, _))
                        $ (Const (\<^const_name>\<open>\<phi>identifier\<close>, _) $ Abs (N,_,_)))
      = let val v = lookup_bindings ctxt N
                  |> Option.mapPartial (fn (_, get) => get (ctxt, Phi_Envir.the_construction ctxt))
         in if Config.get ctxt mode_synthesis
            then H1 $ (case v of SOME x => Type.constraint (fastype_of x) H2 | _ => H2)
                    $ translate_value0 ctxt (Free (N, dummyT))
            else (case v of SOME x => x | _ => no_binding_found N)
        end
  | check_term ctxt (A $ B) = check_term ctxt A $ check_term ctxt B
  | check_term ctxt (Abs (N,TY,X)) = Abs (N,TY, check_term ctxt X)
  | check_term _ X =  X

val _ = Theory.setup (Context.theory_map (Syntax_Phases.term_check ~110 "\<phi>-System.GVA" (map o check_term)))

(*** Initial Process for Arguments ***)

(** Predefined Processes **)

fun collect_and_clean_value whether_clean ctxt sequent =
  let
    val mode = Phi_Working_Mode.mode1 ctxt
    val rule = if whether_clean
               then @{thm apply_collect_clean_value[where WHETHER_CLEAN = True]}
               else @{thm apply_collect_clean_value[where WHETHER_CLEAN = False]}
  in (ctxt, rule RS (sequent COMP #transformation_rule mode))
  |> Phi_Reasoner.reason NONE
  |> (fn SOME (_, sequent') => sequent'
                            |> HOLogic.conj_elim ctxt
                            |> apsnd (fn th => th |> HOLogic.conj_elims ctxt |> rev
                                                  |> tl (*the head is always True*))
       | NONE => Phi_Reasoner.error "Internal bug #vb7iop23")
  end

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
    val (sequent', rules) = collect_and_clean_value clean ctxt sequent
    (*val revert_frees = map_aterms (fn Free (N,T) => Free (Variable.revert_fixed ctxt N, T)
                                    | X => X)*)
    val args = rules |> map (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
                                  $ _)
                 => (*revert_frees*) V
             | _ => error "Internal Bug q34v6 nu89p")
    val binds = rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
                                  $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ (X as Free (N,_)) $ _))
                 => SOME (Variable.revert_fixed ctxt N, ((*revert_frees*) V, K (SOME X)))
             | _ => NONE)
    val binds'= rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ (V as Free (N,_)))
                                  $ X')
                 => SOME (Variable.revert_fixed ctxt N, ((*revert_frees*) V,
                      K (case X' of (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ X $ _) => SOME X | _ => NONE)))
             | _ => NONE)

    fun setup_lemmata ctxt =
      let val facts = maps (fn rule => (rule COMP @{thm Membership_E_Inhabitance})
                                    |> Phi_Inhabitance_Rules.implications_of_inhabitance ctxt) rules
       in ctxt |> Context.proof_map (
            fold (fold (fn th => Named_Theorems.add_thm \<^named_theorems>\<open>\<phi>lemmata\<close> th
                              #> Useful_Thms.add_thm th)
                  o Phi_Envir.process_useful_lemmata true ctxt) facts)
      end
  in ctxt
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

fun push_values values (ctxt,sequent) =
  let
    val mode = Phi_Working_Mode.mode1 ctxt
    val rule = @{thm "_rule_push_a_value_"}
    fun push value (ctxt,sequent) =
          (ctxt, (value RS rule) RS (sequent COMP #transformation_rule mode))
            |> Phi_Reasoner.reason NONE
            |> (fn SOME (ctxt', sequent'') =>
                      (case HOLogic.conj_elim ctxt' sequent''
                         of (sequent', _) => (ctxt', sequent'))
                 | NONE => Phi_Reasoner.error "Internal bug #vb7iop23")
   in fold push values (ctxt,sequent)
  end

end
