(* library/system/generic variable access.ML
   AUTHOR: Qiyuan Xu

   Access (get and set) generic variables.
   A generic variable can be a local value, a variable, or any other registered thing.
*)

(*** Signature ***)
signature GENERIC_VARIABLE_ACCESS = sig

(** Value Context **)
val open_value_context : term list (*arguments*) -> Proof.context -> Proof.context
val assign_local_val : typ option -> Proof.context -> string * Proof.context
val bind_local_vals  : (string (*external name*) * term) list -> Proof.context -> Proof.context

(** Parser for Access **)
type value_parser_key =
  ( int (*priority, descend order, the higher one is attempted first*)
  * string (*name*))

type value_parser = (Proof.context -> term -> term option)

val add_parser : value_parser_key * value_parser -> Context.generic -> Context.generic
val translate_value : Proof.context -> term -> term


(** Initial Arguments **)

val collect_and_clean_value : bool (*whether to clean the Val \<phi>-types from the sequent*)
                           -> Proof.context -> thm (*sequent*)
                           -> thm (*sequent*) * thm list (*specs of value*)

val register_value_spec_thms : Position.T -> thm list -> Context.generic -> Context.generic
  (*so that the values can be synthesised*)

type process_of_argument = context_state -> context_state

val to_value_and_clean : process_of_argument
val to_value_no_clean  : process_of_argument

structure Process_of_Argument : GENERIC_DATA


(** Assignment **)

type assigner = string (*identifier of the assigner*)
             * (binding (*name of the value or variable*)
               -> context_state
               -> ( thm (*rule*)
                  * Proof.context
                  * cterm list (*fixed quantified variables in the rule*)
                  * (thm -> Proof.context -> Proof.context) list)
                      (*declare the condition, coinciding with the order of the conditions*))

val assignment : (binding * assigner) list
              -> Proof.context * thm -> Proof.context * thm
val assignment_cmd : (string (*keyword*) option * binding (*of generic variables*)) list
      -> Proof.context * thm -> Proof.context * thm

val register_assigner : string (*keyword that the assigner binds*)
                      * string (*type name of the generic variable*)
                      * string (*description for display*)
                      * assigner -> theory -> theory

structure Assignment_Hooks : HOOKS

end

structure Generic_Variable_Access : GENERIC_VARIABLE_ACCESS = struct

(*** Value Context ***)

type value_context =
        ( term list (*values of arguments, of type 'a \<phi>arg.*)
        * term Symtab.table (*binding table of local values,
                              key: external name of the fixed variable*)
        * int (*a counter assigning identities to intermediate local values*))
       (*Free variables in the term must use external names, just as what user inputs directly.*)

structure Value_Ctxt = Proof_Data (
  type T = value_context option
  val init = K NONE
)

fun bad_ctxt () = raise Fail "Value context has not been set. Not under a programming context."

fun value_context_of ctxt =
  case Value_Ctxt.get ctxt of SOME c => c | _ => bad_ctxt ()

fun map_value_context f =
  Value_Ctxt.map (fn SOME x => SOME (f x)
                   | NONE => bad_ctxt())

fun open_value_context arguments =
  Value_Ctxt.map (fn SOME (_, LV, CNT) => SOME (arguments, LV, CNT)
                   | NONE => SOME (arguments, Symtab.empty, 0))

fun assign_local_val ty ctxt =
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
  in
  if 1 <= i andalso i <= length A
  then List.nth (A, i-1)
  else error ("The programmign context only has " ^ string_of_int (length A) ^
              " arguments, but it attempts to access the " ^ string_of_int i ^ "th argument.")
  end


fun fallback_trans ctxt (V as Free (s, _)) =
      if can Value.parse_int s
      then index_val ctxt (Value.parse_int s)
      else (case Symtab.lookup (#2 (value_context_of ctxt)) s
              of SOME s' => s'
               | _ => error (Pretty.string_of (Pretty.block [
                     Pretty.str "Generic variable named ",
                     Syntax.pretty_term ctxt V, Pretty.str " is not found."
                    ])))
  | fallback_trans ctxt (Const ("_constrain", _) $ X $ _)
      = fallback_trans ctxt X
  | fallback_trans ctxt X =
      error (Pretty.string_of (Pretty.block [
         Pretty.str "There is no value or variable bound on term ",
         Syntax.pretty_term ctxt X
      ]))


fun translate_value ctxt X =
  let
    val tab = Value_Parsers.get (Context.Proof ctxt)
  in
    case ParserTab.fold_rev (fn (_, f) => (fn NONE => f ctxt X
                                            | some => some)) tab NONE
      of SOME ast => ast
       | _ => fallback_trans ctxt X
  end


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
  (\<^syntax_const>\<open>_identifier_id_\<close>, (fn _ => fn [X] => X)),
  (\<^syntax_const>\<open>_identifier_logic_\<close>, (fn _ => fn [X] => X))
]) #> Sign.parse_translation ([
  (\<^const_syntax>\<open>\<phi>identifier\<close>, (fn ctxt => fn [X] => translate_value ctxt X))
]))

end
  
(*** Initial Process for Arguments ***)

(** Predefined Processes **)

fun collect_and_clean_value whether_clean ctxt sequent =
  let
    val mode = Phi_Working_Mode.working_mode_on1 ctxt (Thm.concl_of sequent)
    val rule = if whether_clean
               then @{thm apply_collect_clean_value[where WHETHER_CLEAN = True]}
               else @{thm apply_collect_clean_value[where WHETHER_CLEAN = False]}
  in (ctxt, rule RS (sequent COMP #transform_rule mode))
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
    in (rule, pos, 1000, [pattern], []) end
  ) rules)


fun gen_default_process' clean pos (ctxt,sequent) =
  let
    val (sequent', rules) = collect_and_clean_value clean ctxt sequent
    val revert_frees = map_aterms (fn Free (N,T) => Free (Variable.revert_fixed ctxt N, T)
                                    | X => X)
    val args = rules |> map (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
                                  $ _)
                 => revert_frees V
             | _ => error "Internal Bug q34v6 nu89p")
    val binds = rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
                                  $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ Free (N,_) $ _))
                 => SOME (Variable.revert_fixed ctxt N, revert_frees V)
             | _ => NONE)
    val binds'= rules |> map_filter (fn th =>
          case Thm.prop_of th
            of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
                                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ (V as Free (N,_)))
                                  $ _)
                 => SOME (Variable.revert_fixed ctxt N, revert_frees V)
             | _ => NONE)
  in ctxt
  |> open_value_context args
  |> Context.proof_map (register_value_spec_thms pos rules)
  |> bind_local_vals (binds' @ binds)
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

type process_of_argument = context_state -> context_state

val to_value_and_clean = gen_default_process true  Position.none
val to_value_no_clean  = gen_default_process false Position.none

structure Process_of_Argument = Generic_Data (
  type T = process_of_argument option
  val empty = NONE
  val merge = merge_options
)

val _ = Theory.setup (Context.theory_map (
Phi_Envir.Enter_Programming_Environ.add 20 (fn level => fn (ctxt,sequent) =>
  if level = 0
  andalso #domain Phi_Working_Mode.procedure ctxt (Thm.concl_of sequent)
  then the_default to_value_and_clean (Process_of_Argument.get (Context.Proof ctxt)) (ctxt,sequent)
  else (ctxt,sequent)
)))

(*** Assignment ***)

type assigner = string (*identifier of the assigner*)
             * (binding (*name of the value or variable*)
               -> context_state
               -> ( thm (*rule*)
                  * Proof.context
                  * cterm list (*fixed quantified variables in the rule*)
                  * (thm -> Proof.context -> Proof.context) list)
                      (*declare the condition, coinciding with the order of the conditions*))

structure Assigner = Theory_Data (
  type T = (
             ( string (*description*)
             * assigner) Symtab.table (*key: kind, also the keyword used in the programming*)
           * string Symtab.table (*from full name of the type of the generic variable to its kind*)
           )
  val empty = (Symtab.empty, Symtab.empty)
  fun merge ((a1,b1),(a2,b2)) =
        (Symtab.merge (K true) (a1,a2), Symtab.merge (op =) (b1,b2))
)

fun register_assigner (keyword, typ_const, descr, assigner) =
  Assigner.map (fn (A,K) => (Symtab.update_new (keyword, (descr, assigner)) A,
                             Symtab.update_new (typ_const, keyword) K))

fun parse_assigner ctxt =
  let
    val (assigner, type_map) = Assigner.get (Proof_Context.theory_of ctxt)
    fun not_defined name = let open Pretty in
        error (string_of (chunks (
          block [Binding.pretty name, str " is not an existing local value or variable."] ::
          str "Use the following syntax:" ::
          (map (fn (key, (descr,_)) =>
                    item [keyword1 key, str " ", Binding.pretty name, str ", ", str descr])
               (Symtab.dest assigner))
        )))
      end
    fun find name =
      case Variable.lookup_fixed ctxt (Binding.name_of name)
            |> Option.mapPartial (Variable.default_type ctxt)
        of SOME (Type ("dummy", [])) => not_defined name
         | SOME (Type (T, _)) =>
            (case Symtab.lookup type_map T
               of SOME key => key
                | NONE => not_defined name)
         | _ => not_defined name
    fun parse (NONE, name) = parse (SOME (find name), name)
      | parse (SOME key, name) =
          case Symtab.lookup assigner key
            of SOME (_, A) => (name, A)
             | _ => let open Pretty
                     in error (string_of (block [
                          keyword1 key, str " is not associated with any assignment rule."
                     ])) end
  in map parse
  end
  


fun strip_imp_prems_rev ret ct =
  let val (cA, cB) = Thm.dest_implies ct
  in strip_imp_prems_rev (cA :: ret) cB end
  handle TERM _ => (ret, ct)


(*TODO*)
fun concact_sequent ctxt rule vars sequent =
  Phi_Help.comp_rule_incr_left ctxt (Drule.forall_intr_list vars sequent) rule

fun default_assignment (name_assigner:(binding * assigner) list) (ctxt,sequent) =
  let
  (*make the assignment procedure*)
  val (rule', ctxt', vterms', decl') = (Thm.trivial (Thm.var (("init",0),\<^ctyp>\<open>prop\<close>)),ctxt,[],[])
        |> fold (fn (name,(_,f)) => fn (proc, ctxt, vterms, Asm) =>
              let val (rule, ctxt', vterms', Asm') = f name (ctxt,sequent)
               in (rule RS proc, ctxt', rev vterms' @ vterms, rev Asm' @ Asm) end
           ) name_assigner
  val rule = @{thm "__value_access_0__"} RS rule'
  val vterms = rev vterms'
  val decl = rev decl'

  (*apply the assignment procedure*)
  val (ctxt, proc) = NuApply.apply [rule] (ctxt',sequent)
        |> apsnd (fn th =>
            (*find where is the procedural parameter, and permute it to the end*)
            let
              fun is_body (Abs (_,_,X)) = is_body X
                | is_body (\<^const>\<open>Trueprop\<close> $ X) = is_body X
                | is_body (Const (\<^const_name>\<open>Pure.all\<close>,_) $ X) = is_body X
                | is_body (\<^const>\<open>Pure.imp\<close> $ _ $ X) = is_body X
                | is_body (X $ _) = is_body X
                | is_body (Const (\<^const_name>\<open>\<phi>Procedure\<close>, _)) = true
                | is_body _ = false
              val delt = 1 + find_index is_body (Thm.prems_of th)
              val _ = if delt = 0 then error "Internal Bug: Some assignment rule is wrong!" else ()
            in Thm.permute_prems 0 delt th end)
        |> Phi_Reasoner.reason1 (fn _ => 
            "Fail to assign variable(s). Typically, it is due to unsolved semantic types."
           ) (SOME ~1)
        |> apsnd (fn th => th RS @{thm conjunct1})

  (*insert a callback frame for concatenating sequents*)
  val (_, ctxt) = Assumption.add_assms
                        (fn _ => fn _ => (concact_sequent ctxt proc vterms, I)) [] ctxt

  val (rev_hyps, proc_cterm) = Thm.cprem_of proc 1
           |> fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) vterms
           |> strip_imp_prems_rev []

  (*Now we change the goal of the programming context to add the *)
  val (_,arg_spec,ret_spec,E_spec) = Phi_Syntax.dest_procedure_c proc_cterm
  val goal = Phi_Envir.get_thesis ctxt
  val (trueprop, goal_term) = Thm.dest_comb goal
  val ((goal_F_arg,goal_ret), goal_E) = Thm.dest_comb goal_term |> apfst Thm.dest_comb
  fun instantiate_R inst spec =
    let
      fun left_most (Const (\<^const_name>\<open>times\<close>, _) $ A $ _) = left_most A
        | left_most X = X
      val spec' = Thm.incr_indexes_cterm (Thm.maxidx_of_cterm goal) spec
      val R = case (case Thm.term_of spec'
                      of Abs (_,_,X) => left_most X |> dest_comb |> fst
                       | X => left_most X)
                of Var (R, _) => R
                 | _ => error "At least one of the assignment rules is not configured properly."
    in spec'
    |> Drule.mk_term
    |> Drule.infer_instantiate ctxt [(R,inst)]
    |> Drule.dest_term
    end
  val goal_ret' = instantiate_R goal_ret ret_spec
(*  val goal_E'   = instantiate_R goal_E   E_spec *)
  val goal' = Thm.apply trueprop (Thm.apply (Thm.apply goal_F_arg goal_ret') goal_E)
  val ctxt = Phi_Envir.put_thesis goal' ctxt

  (*declare every hypothesis*)
  val (Hs,ctxt) = Assumption.add_assms Assumption.presume_export (rev rev_hyps) ctxt
  val ctxt = fold2 (fn H => fn D => D H) Hs decl ctxt

  (*make the new initial sequent*)
  val blk_name = Variable.revert_fixed ctxt (Term.term_name (Phi_Syntax.current_block_var sequent))
  val (ctxt, sequent') = #initial_sequent Phi_Working_Mode.procedure blk_name arg_spec ctxt

  val (_, ctxt) = Assumption.add_assms (fn _ => fn _ =>
            ((fn sequentx => #cast_exception Phi_Working_Mode.procedure E_spec (ctxt, sequentx)
                                |> Phi_Reasoners.safer_obligation_solver1
                                |> snd),
             I)) [] ctxt
  in (ctxt, sequent')
  end

structure Assignment_Hooks = Hooks(type arg = (binding * assigner) list)

val assignment = Assignment_Hooks.invoke_until_success default_assignment

fun assignment_cmd binds (ctxt,sequent) =
      assignment (parse_assigner ctxt binds) (ctxt,sequent)


end
