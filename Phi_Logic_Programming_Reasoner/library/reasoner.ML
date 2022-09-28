signature NU_REASONER = sig
  (* This file is the major hot point of the whole system.
     TODO: optimize as possible as you can! *)

  (* Convention:
   * If a rule has a priority higher or equal to 1000:
          it is a deterministic rule that in this case, only this rule will be applied
            if there is no other rule with higher priority.
   * Else: it is a nondeterministic rule that, it will be applied together with other
          nondeterministic rule if there is no deterministic rule.
            The rule with higher priority will be applied first.
            If the rule is fail other nondeterministic rules will be applied.

   *  at a point of the search with several backtrackings
        and potential candidates to be explored from this point,
   *  When all score of candidates < 1000 : normal behavior of scored-search
   *  When at least a score \<ge> 1000 but < 1000,000 : a local cut that abrogates
   *        any other candidates except the one with the maximum score
   *  When at least a score \<ge> 1000,000 : a global cut that abrogates
   *        all other backtrackings and reset the search to start from
   *        the candidate of the maximum score. This candidate will be
   *        returned when no further global cut is met and not all premises
   *        are solved. The global cut means the reasoning has achieved
   *        certain success and future reasoning work can be based on this point.
   * 
   * The reasoner either returns the state whose all premises are solved
   *    or the latest global cut point.
   *
   * The score above (and also the score in user interface) equals to
   *   the negative cost in the following code.
   *)

  type cost = int
  type 'a generic_reasoner = {name: term, pattern: term list, not_match: term list, tactic: 'a}
  type reasoner = (context_state -> context_state Seq.seq) generic_reasoner
  val reasoner_eq : ('a generic_reasoner * 'a generic_reasoner) -> bool

  val trace : bool Config.T
  val trace_candicates : bool Config.T

  (* auto level: 2 - fully auto, 1 - paritally auto, 0 - fully manual *)
  val auto_level : int Config.T
  val reduce_auto_level : int -> Proof.context -> Proof.context

  (*For any pattern P matching the conclusion, pass `conclusion_tag $ P` to this library;
   * or for P matching premises, pass `premise_tag $ P`. *)
  val conclusion_tag : term
  val premise_tag : term

  exception Success of context_state
  exception Global_Cut of context_state

  val add : cost * reasoner -> Context.generic -> Context.generic
  val add_lthy : cost * reasoner -> local_theory -> local_theory
  val del : reasoner -> Context.generic -> Context.generic
  val reasoners : Proof.context -> (cost * reasoner) list
  val reasoner_net : Proof.context -> reasoner Cost_Net.T

  val add_intro_rule : term list * term list -> cost * thm -> Context.generic -> Context.generic
  val add_intro_rules: (thm list * cost * term list * term list) list -> Proof.context -> Proof.context
  val del_intro_rule : thm -> Context.generic -> Context.generic
  val attr_add_intro : int * (term list * term list) -> attribute
  val attr_del_intro : attribute

  val add_elim_rule : term list * term list -> cost * thm -> Context.generic -> Context.generic
  val add_elim_rules: (thm list * cost * term list * term list) list -> Proof.context -> Proof.context
  val del_elim_rule : thm -> Context.generic -> Context.generic
  val attr_add_elim : int * (term list * term list) -> attribute
  val attr_del_elim : attribute

  val reason' : bool (*trace*) -> reasoner Cost_Net.T -> context_state -> context_state option
  val reason  : context_state -> context_state option
  val reason1 : context_state -> context_state
  val reason_s : Proof.context -> (cost * context_state Seq.seq) list -> context_state Seq.seq (* Note it only returns one
    theorem in the returned sequence, that the one succeeded first or of least cost. *)
  val reason_tac :  Proof.context -> context_tactic

  val setup_cmd : ((string (*name term*) * cost)
                   * ((bool (*true for matching, false for not matching*)
                       * bool (*true for premise pattern, false for conclusion pattern*))
                      * string (*pattern term*)) list
                  ) * Input.source (* tactic source*)
        -> local_theory -> local_theory
end


structure Nu_Reasoner : NU_REASONER = struct


type cost = int
type 'a generic_reasoner = {name: term, pattern: term list, not_match: term list, tactic: 'a}
type reasoner = (context_state -> context_state Seq.seq) generic_reasoner

val auto_level = Attrib.setup_config_int \<^binding>\<open>\<phi>auto_level\<close> (K 2)
fun reduce_auto_level i = Config.map auto_level (fn j => Int.min (i,j))

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning\<close> (K false);
val trace_candicates = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning_candicates\<close> (K false);

val conclusion_tag = Free("Conclusion", \<^typ>\<open>prop \<Rightarrow> prop\<close>)
val premise_tag = Free("Premise", \<^typ>\<open>prop \<Rightarrow> prop\<close>)


exception Success  of context_state
exception Global_Cut of context_state
exception Local_Cut of (cost * context_state Seq.seq)


fun debug ctxt (c,(r : reasoner as {name,...})) =
  tracing ("reasoning candicates (" ^ string_of_int c ^ "):\n"
              ^ Syntax.string_of_term (Proof_Context.set_mode Proof_Context.mode_abbrev ctxt) name)
fun dbg2 ctxt term = (tracing (Syntax.string_of_term ctxt term); term)

fun is_var (A $ _) = is_var A
  | is_var (Var _) = true
  | is_var _ = false

fun my_match thy po =
  let
    val (_,tms) = Pattern.match thy po (Vartab.empty, Vartab.empty)
  in Vartab.fold (fn ((name,_),(_,tm)) => fn flag =>
        if String.isPrefix "var_" name
        then flag andalso is_var (Envir.beta_eta_contract tm)
        else flag
     ) tms true
  end
  handle Pattern.MATCH => false


fun call_tactics ctxt tactics th =
  if Thm.no_prems th
  then raise Success (ctxt, th)
  else let
    val prop = Thm.prop_of th
    val tacs = ((conclusion_tag $ Logic.concl_of_goal prop 1)
                :: map (fn t => premise_tag $ t) (Logic.prems_of_goal prop 1))
                |> maps (fn term =>
                    Cost_Net.retrieve tactics term
                      |> filter (fn (_,reasoner) =>
                          exists (fn pat =>
                            my_match (Proof_Context.theory_of ctxt) (pat,term))
                          (#pattern reasoner)
                          andalso forall (fn pat =>
                            not (my_match (Proof_Context.theory_of ctxt) (pat,term)))
                          (#not_match reasoner))
                      |> (if Config.get ctxt trace_candicates
                          then (fn rs => (List.app (debug ctxt) rs; rs))
                          else I))
                |> sort (int_ord o apply2 fst)
  in
    tacs 
      |> map_filter (fn (cost, r : reasoner) =>
          if cost <= ~1000000 then
            case Seq.pull (#tactic r (ctxt,th))
              of SOME (x,_) => raise Global_Cut x
               | _ => NONE
          else if cost <= ~1000 then
            case Seq.pull (#tactic r (ctxt,th))
              of SOME (x,s) => raise Local_Cut (cost, Seq.cons x s)
               | _ => NONE
          else SOME (cost, Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))))
        )
    handle Local_Cut ret => [ret]
  end

fun gen_reason _ _ _ (result, []) = result
  | gen_reason trace iter tactics (result, []::L) =
      gen_reason trace iter tactics (result, L)
  | gen_reason trace iter tactics (result, ((cost,seq)::L')::L) =
  let
    val _ = if iter > 300 then raise Fail "Nu_Reasoner: Too Much Tries" else ()
  in
    case Seq.pull seq
      of SOME ((ctxt,th), seq') =>
          (let
            val _ = if trace
                    then tracing ("\<phi>reasoning (score " ^ string_of_int (~cost)
                      ^ "):\n" ^ Thm.string_of_thm ctxt th)
                    else ()
            val Z = (call_tactics ctxt tactics th)
                  |> map (apfst (fn c' => c' + cost))
                  |> (fn Z => (result, Z::(
                        let val t = if pointer_eq (seq',Seq.empty) then L' else (cost,seq')::L'
                        in if t = [] then L else t::L end)))
                handle Success ret => raise Success ret
                     | Global_Cut result' =>
                        let
                          val _ = if trace
                                  then tracing ("\<phi>reasoning cut:\n"
                                          ^ Thm.string_of_thm ctxt (snd result'))
                                  else ()
                        in
                          (SOME result', [[(0, Seq.single result')]])
                        end
          in
            gen_reason trace (iter+1) tactics Z
          end)
       | NONE => gen_reason trace iter tactics (result, L'::L)
  end

fun gen_reason' trace tactics states =
      gen_reason trace 0 tactics (NONE, states)
      handle Success ret => SOME ret

fun reason' trace tactics state =
      gen_reason' trace tactics [[(0, Seq.single state)]]

fun reason'_s trace tactics seqs = Seq.make (fn () =>
      gen_reason' trace tactics [seqs]
        |> Option.map (rpair Seq.empty)
    )

fun reasoner_eq ({name,pattern,...}, {name=name',pattern=pattern',...}) =
  (name = name')



(* Contextual Data *)

structure Tactics = Generic_Data (
  type T = reasoner Cost_Net.T;
  val empty : T = Cost_Net.init reasoner_eq #pattern;
  val extend = I;
  val merge : T * T -> T = Cost_Net.merge
)

fun reasoners ctxt = Cost_Net.content (Tactics.get (Context.Proof ctxt))
fun reasoner_net ctxt = Tactics.get (Context.Proof ctxt)
fun add cost_reasoner = Tactics.map (Cost_Net.update cost_reasoner);
fun add_lthy cost_reasoner =
   Local_Theory.background_theory (Context.theory_map (add cost_reasoner))
#> Local_Theory.map_contexts (K (Context.proof_map (add cost_reasoner)))

fun del reasoner = Tactics.map (Cost_Net.remove reasoner);
fun reason stat =
      reason' (Config.get (fst stat) trace) (Tactics.get (Context.Proof (fst stat))) stat
fun reason1 stat =
      case reason stat of SOME x => x
        | NONE => error ("Reasoning Fail! You may turn on \<phi>reasoning_tracing and "^
                         "\<phi>reasoning_tracing_condidates to debug.")
fun reason_s ctxt =
      reason'_s (Config.get ctxt trace) (Tactics.get (Context.Proof ctxt))
fun reason_tac ctxt stat = Seq.make (fn () =>
      reason' (Config.get ctxt trace) (Tactics.get (Context.Proof ctxt)) stat
       |> Option.map (rpair Seq.empty o Seq.Result)
    )

(* Command Interface *)

fun setup_method_cmd (((name,cost),patterns),method) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val patterns = split_list patterns
                      |> apsnd (Syntax.read_props ctxt)
                      |> (op ~~)
    val pos_pats = patterns |> map_filter (fn ((direct,prem), pat) =>
             (if direct then SOME ((if prem then premise_tag else conclusion_tag) $ pat) else NONE))
    val neg_pats = patterns |> map_filter (fn ((direct,prem), pat) =>
             (if direct then NONE else SOME ((if prem then premise_tag else conclusion_tag) $ pat)))
    val name' = Free(Binding.name_of name, dummyT)

    val (method',lthy') = Method_Closure.method_cmd name [] [] [] [] method lthy
    val method'' = Method_Closure.apply_method lthy' method' [] [] []
    val method'''= (fn (ctxt,thm) => method'' ctxt [] (ctxt,thm) |> Seq.filter_results)
    val lthy'' = add_lthy (cost, {name=name', pattern=pos_pats, not_match=neg_pats, tactic=method'''}) lthy'
  in
    lthy''
end

fun setup_cmd (((name,cost),patterns),tactic_src) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val name = Syntax.read_term lthy name
    val patterns = split_list patterns
                      |> apsnd (Syntax.read_props ctxt)
                      |> (op ~~)
    val pos_pats = patterns |> map_filter (fn ((direct,prem), pat) =>
             (if direct then SOME ((if prem then premise_tag else conclusion_tag) $ pat) else NONE))
    val neg_pats = patterns |> map_filter (fn ((direct,prem), pat) =>
             (if direct then NONE else SOME ((if prem then premise_tag else conclusion_tag) $ pat)))
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of tactic_src)
        (ML_Lex.read
          ("Theory.local_setup (Nu_Reasoner.add_lthy (" ^
          ML_Syntax.print_int cost ^ ", {name=(" ^
          ML_Syntax.print_term name ^ "), pattern=(" ^
          ML_Syntax.print_list ML_Syntax.print_term pos_pats
          ^ "), not_match=("^
          ML_Syntax.print_list ML_Syntax.print_term neg_pats
          ^"), tactic=(let in ") @
          ML_Lex.read_source tactic_src @
          ML_Lex.read (" end):(context_state -> context_state Seq.seq)}))"))
    )
  end

val pattern = Parse.enum "|"
      ((Scan.optional (\<^keyword>\<open>no\<close> >> K false) true
        -- (\<^keyword>\<open>premises\<close> >> K true || \<^keyword>\<open>conclusion\<close> >> K false)) -- Parse.term)

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner_ML} "define \<phi>reasoner"
    (Parse.term -- (Parse.int >> ~) --| Parse.$$$ "(" -- pattern --| Parse.$$$ ")"
        --| @{keyword =} -- Parse.ML_source
      >> setup_cmd)

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner} "define \<phi>reasoner"
    (Parse.binding -- (Parse.int >> ~) --| Parse.$$$ "(" -- pattern --| Parse.$$$ ")"
        --| @{keyword =} -- Parse.args1 (K true)
      >> setup_method_cmd)


(* Predefined Reasoners *)

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty)))


fun intro_reasoner cost patterns not_match rule =
  let
    val rule = Thm.trim_context rule
    val pats = if null patterns then [conclusion_tag $ Thm.concl_of rule]
               else map (fn pat => conclusion_tag $ pat) patterns
    val npats= map (fn pat => conclusion_tag $ pat) not_match
    val f_num = length (filter (fn \<^prop>\<open>\<r>Feasible\<close> => true | _ => false) (Thm.prems_of rule))
    val has_feasible =
          if f_num > 0 andalso cost > ~1000
          then error ("Conditional \<r>Feasible only makes sense for deterministic rule.")
          else if f_num > 1
          then error ("A reasoning rule can contain one \<r>Feasible antecedent at most.")
          else f_num > 0
  in {name = @{term \<phi>Intro_Rule} $ Thm.prop_of rule,
      pattern = pats,
      not_match = npats,
      tactic = (fn (ctxt, th) =>
          Seq.make (fn _ =>
            case Seq.pull (HEADGOAL (Tactic.resolve_tac ctxt [rule]) th)
              of SOME (ret, _) =>
                  if has_feasible
                  then reason (ctxt, ret) |> Option.map (rpair Seq.empty)
                  else SOME ((ctxt, ret), Seq.empty)
               | _ => NONE))
      }
  end

fun elim_reasoner patterns not_match  rule =
  let
    val rule = Thm.trim_context rule
    val pats = if null patterns then [premise_tag $ Thm.major_prem_of rule]
               else map (fn pat => premise_tag $ pat) patterns
    val npats= map (fn pat => premise_tag $ pat) not_match
  in {name = @{term \<phi>Elim_Rule} $ Thm.prop_of rule,
      pattern = pats,
      not_match = npats,
      tactic = (fn (ctxt, th) => HEADGOAL (Tactic.eresolve_tac ctxt [rule]) th |> Seq.map (pair ctxt))}
  end

fun add_intro_rule (pattern,not_match) (cost, rule) = add (cost, intro_reasoner cost pattern not_match rule)
fun add_intro_rules rules =
  fold (fn (rules,cost,pattern,not_match) =>
    fold (Context.proof_map o add_intro_rule (pattern,not_match) o pair cost) rules) rules
fun del_intro_rule rule = del (intro_reasoner 1000 [] [] rule)

fun attr_add_intro (cost, (pattern, not_match)) =
  Thm.declaration_attribute (add_intro_rule (pattern,not_match) o pair cost)
val attr_del_intro = Thm.declaration_attribute del_intro_rule

fun add_elim_rule (pattern, not_match) (cost, rule) = add (cost, elim_reasoner pattern not_match rule)
fun add_elim_rules rules =
  fold (fn (rules,cost,pattern,not_match) =>
    fold (Context.proof_map o add_elim_rule (pattern,not_match) o pair cost) rules) rules
fun del_elim_rule rule = del (elim_reasoner [] [] rule)
fun attr_add_elim (cost, (pattern, not_match)) =
  Thm.declaration_attribute (add_elim_rule (pattern,not_match) o pair cost)
val attr_del_elim = Thm.declaration_attribute del_elim_rule

end
