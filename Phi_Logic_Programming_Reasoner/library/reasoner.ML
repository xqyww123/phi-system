(*
The engine of the Phi Logic Programming Reasoner
Author: Qiyuan Xu
*)
signature NU_REASONER = sig
  (* This file is the major hot point of the whole system.
     TODO: optimize it as much as possible! *)

 
  type priority = int
  type pattern = term
  type name = term

  (* Pattern must be wrapped either by conclusion_tag or condition_tag to demonstrate
     which part the pattern describes. *)
  val conclusion_tag : term
  val condition_tag : term
  val pattern_on_conclusion : term -> pattern
  val pattern_on_condition  : term -> pattern

  type reasoner = {name: name,
                 pos: Position.T,
                 pattern: pattern list,
                 blacklist: pattern list,
                 tactic: (context_state -> context_state Seq.seq)}


  val trace : bool Config.T (*Prints the state of every reasoning step.*)
  val trace_candidates : bool Config.T (*Prints the candidates at each step.*)

  (* auto level: 2 - fully auto, 1 - partially auto, 0 - fully manual *)
  val auto_level : int Config.T
  val reduce_auto_level : int -> Proof.context -> Proof.context

  exception Success of context_state
  exception Global_Cut of context_state

  val add : priority * reasoner -> Context.generic -> Context.generic
  val add_lthy : priority * reasoner -> local_theory -> local_theory
  val del : name -> Context.generic -> Context.generic
  val reasoners : Proof.context -> (priority * reasoner) list
  val reasoner_net : Proof.context -> reasoner Cost_Net.T

  val reason' : bool (*trace*) -> reasoner Cost_Net.T -> context_state -> context_state option
  val reason  : context_state -> context_state option
  val reason1 : context_state -> context_state
  val reason_s : Proof.context -> (priority * context_state Seq.seq) list -> context_state Seq.seq
    (* Note it returns at most one state in the returned sequence. *)
  val reason_tac :  Proof.context -> context_tactic


  val add_intro_rule : Position.T -> priority -> term list * term list -> thm -> Context.generic -> Context.generic
  val add_intro_rules: (thm list * Position.T * priority * term list * term list) list -> Proof.context -> Proof.context
  val del_intro_rule : thm -> Context.generic -> Context.generic
  val attr_add_intro : (Position.T * (int * (term list * term list))) -> attribute
  val attr_del_intro : attribute

  val add_elim_rule : Position.T -> priority -> term list * term list -> thm -> Context.generic -> Context.generic
  val add_elim_rules: (thm list * Position.T * priority * term list * term list) list -> Proof.context -> Proof.context
  val del_elim_rule : thm -> Context.generic -> Context.generic
  val attr_add_elim : Position.T * (int * (term list * term list)) -> attribute
  val attr_del_elim : attribute


  val setup_cmd : (((string (*name term*) * Position.T) * priority)
                   * ((bool (*true for matching, false for not matching*)
                       * bool (*true for premise pattern, false for conclusion pattern*))
                      * string (*pattern term*)) list
                  ) * Input.source (* tactic source*)
        -> local_theory -> local_theory
end


structure Nu_Reasoner : NU_REASONER = struct


type priority = int
type pattern = term
type name = term
type reasoner = {name: term,
                 pos: Position.T,
                 pattern: term list,
                 blacklist: term list,
                 tactic: (context_state -> context_state Seq.seq)}


val auto_level = Attrib.setup_config_int \<^binding>\<open>\<phi>auto_level\<close> (K 2)
fun reduce_auto_level i = Config.map auto_level (fn j => Int.min (i,j))

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning\<close> (K false);
val trace_candidates = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning_candidates\<close> (K false);

val conclusion_tag = Free("Conclusion", \<^typ>\<open>prop \<Rightarrow> prop\<close>)
val condition_tag = Free("Condition", \<^typ>\<open>prop \<Rightarrow> prop\<close>)

fun pattern_on_conclusion term = conclusion_tag $ term
fun pattern_on_condition  term = condition_tag  $ term

exception Success  of context_state
exception Global_Cut of context_state
exception Local_Cut of (priority * Position.T * context_state Seq.seq)


fun debug ctxt (c,(r : reasoner as {name,...})) =
  tracing ("reasoning candicates (" ^ string_of_int c ^ "):\n"
              ^ Syntax.string_of_term (Proof_Context.set_mode Proof_Context.mode_abbrev ctxt) name)
fun dbg2 ctxt term = (tracing (Syntax.string_of_term ctxt term); term)

fun is_var (A $ _) = is_var A
  | is_var (Var _) = true
  | is_var _ = false

fun match_term thy pat_obj =
  let
    val (_,tms) = Pattern.match thy pat_obj (Vartab.empty, Vartab.empty)
  in Vartab.fold (fn ((name,_),(_,tm)) => fn flag =>
        if String.isPrefix "var_" name
        then flag andalso is_var (Envir.beta_eta_contract tm)
        else flag
     ) tms true
  end
  handle Pattern.MATCH => false

fun cond_concl_of_goal st i =
  let val (gi, rfrees) = Logic.goal_params st i
      val B = Logic.strip_assums_concl gi
      val As = Logic.strip_assums_hyp gi
  in conclusion_tag $ subst_bounds (rfrees, B)
      :: map (fn t => condition_tag $ t) (map (fn A => subst_bounds (rfrees, A)) As)
  end

fun call_tactics ctxt tactics th =
  if Thm.no_prems th
  then raise Success (ctxt, th)
  else let
    val prop = Thm.prop_of th
    val tacs = cond_concl_of_goal prop 1
                |> maps (fn term =>
                    Cost_Net.retrieve tactics term
                      |> filter (fn (_,reasoner) =>
                          exists (fn pat =>
                            match_term (Proof_Context.theory_of ctxt) (pat,term))
                          (#pattern reasoner)
                          andalso forall (fn pat =>
                            not (match_term (Proof_Context.theory_of ctxt) (pat,term)))
                          (#blacklist reasoner))
                      |> (if Config.get ctxt trace_candidates
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
              of SOME (x,s) => raise Local_Cut (cost, #pos r, Seq.cons x s)
               | _ => NONE
          else SOME (cost, #pos r, Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))))
        )
    handle Local_Cut ret => [ret]
  end

fun gen_reason _ _ _ (result, []) = result
  | gen_reason trace iter tactics (result, []::L) =
      (if trace then tracing ("Backtracking...") else ();
       gen_reason trace iter tactics (result, L))
  | gen_reason trace iter tactics (result, ((cost,pos,seq)::L')::L) =
  let
    val _ = if iter > 1000 then raise Fail "Nu_Reasoner: Too Much Tries" else ()
  in
    case Seq.pull seq
      of SOME ((ctxt,th), seq') =>
          (let
            val _ = if trace
                    then tracing ("\<phi>reasoning (score " ^ string_of_int (~cost)
                      ^ "):"^ Position.here pos ^"\n" ^ Thm.string_of_thm ctxt th)
                    else ()
            val Z = (call_tactics ctxt tactics th)
                  |> map (fn (a,b,c) => (a+cost,b,c))
                  |> (fn Z => (result, Z::(
                        let val t = if pointer_eq (seq',Seq.empty) then L' else (cost,pos,seq')::L'
                        in if null t then L else t::L end)))
                handle Success ret => raise Success ret
                     | Global_Cut result' =>
                        let
                          val _ = if trace
                                  then tracing ("\<phi>reasoning cut:\n"
                                          ^ Thm.string_of_thm ctxt (snd result'))
                                  else ()
                        in
                          (SOME result', [[(0,pos, Seq.single result')]])
                        end
          in
            gen_reason trace (iter+1) tactics Z
          end)
       | NONE => gen_reason trace iter tactics (result, L'::L)
  end

fun gen_reason' trace tactics states =
      gen_reason trace 0 tactics (NONE, map (map (fn (a,b) => (~a,Position.none,b))) states)
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

fun reasoners ctxt = Cost_Net.content (Tactics.get (Context.Proof ctxt)) |> map (apfst ~)
fun reasoner_net ctxt = Tactics.get (Context.Proof ctxt)
fun add (priority,reasoner) = Tactics.map (Cost_Net.update (~priority,reasoner));
fun add_lthy cost_reasoner =
   Local_Theory.background_theory (Context.theory_map (add cost_reasoner))
#> Local_Theory.map_contexts (K (Context.proof_map (add cost_reasoner)))

fun del name = Tactics.map (Cost_Net.remove(
      {name=name, pos=Position.none, pattern=[], blacklist=[], tactic = K Seq.empty}))

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
             (if direct then SOME ((if prem then condition_tag else conclusion_tag) $ pat) else NONE))
    val neg_pats = patterns |> map_filter (fn ((direct,prem), pat) =>
             (if direct then NONE else SOME ((if prem then condition_tag else conclusion_tag) $ pat)))
    val name' = Free(Binding.name_of name, dummyT)

    val (method',lthy') = Method_Closure.method_cmd name [] [] [] [] method lthy
    val method'' = Method_Closure.apply_method lthy' method' [] [] []
    val method'''= (fn (ctxt,thm) => method'' ctxt [] (ctxt,thm) |> Seq.filter_results)
    val lthy'' = add_lthy (cost, {name=name', pos=Binding.pos_of name,
                                  pattern=pos_pats, blacklist=neg_pats, tactic=method'''}) lthy'
  in
    lthy''
end

fun setup_cmd ((((name,pos),cost),patterns),tactic_src) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val name = Syntax.read_term lthy name
    val patterns = split_list patterns
                      |> apsnd (Syntax.read_props ctxt)
                      |> (op ~~)
    val pos_pats = patterns |> map_filter (fn ((direct,prem), pat) =>
             (if direct then SOME ((if prem then condition_tag else conclusion_tag) $ pat) else NONE))
    val neg_pats = patterns |> map_filter (fn ((direct,prem), pat) =>
             (if direct then NONE else SOME ((if prem then condition_tag else conclusion_tag) $ pat)))
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of tactic_src)
        (ML_Lex.read
          ("Theory.local_setup (Nu_Reasoner.add_lthy (" ^
          ML_Syntax.print_int cost ^ ", {name=(" ^
          ML_Syntax.print_term name ^ "), pos=("^
          ML_Syntax.print_position pos ^ "), pattern=(" ^
          ML_Syntax.print_list ML_Syntax.print_term pos_pats
          ^ "), blacklist=("^
          ML_Syntax.print_list ML_Syntax.print_term neg_pats
          ^"), tactic=(let in ") @
          ML_Lex.read_source tactic_src @
          ML_Lex.read (" end):(context_state -> context_state Seq.seq)}))"))
    )
  end

val patterns = Parse.$$$ "(" |-- Parse.enum "|"
      ((Scan.optional (\<^keyword>\<open>except\<close> >> K false) true
        -- (\<^keyword>\<open>premises\<close> >> K true || \<^keyword>\<open>conclusion\<close> >> K false)) -- Parse.term)
      --| Parse.$$$ ")"

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner_ML} "define \<phi>reasoner"
    (Parse.position Parse.term -- Parse.int -- patterns
        --| @{keyword =} -- Parse.ML_source
      >> setup_cmd)

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner} "define \<phi>reasoner"
    (Parse.binding -- Parse.int -- patterns
        --| @{keyword =} -- Parse.args1 (K true)
      >> setup_method_cmd)


(* Predefined Reasoners *)

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty)))


fun name_of_intro_reasoner rule = Free ("\<phi>Intro_Rule", \<^typ>\<open>prop \<Rightarrow> prop\<close>) $ Thm.prop_of rule
fun intro_reasoner pos priority patterns blacklist rule =
  let
    val rule = Thm.trim_context rule
    val pats = if null patterns then [conclusion_tag $ Thm.concl_of rule]
               else map (fn pat => conclusion_tag $ pat) patterns
    val npats= map (fn pat => conclusion_tag $ pat) blacklist
    val f_num = length (filter (fn \<^prop>\<open>\<r>Feasible\<close> => true | _ => false) (Thm.prems_of rule))
    val has_feasible =
          if f_num > 0 andalso priority < 1000
          then error ("Conditional \<r>Feasible only makes sense for assertive rule.")
          else if f_num > 1
          then error ("A reasoning rule can contain one \<r>Feasible antecedent at most.")
          else f_num > 0
  in {name = name_of_intro_reasoner rule,
      pos = pos,
      pattern = pats,
      blacklist = npats,
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

fun name_of_elim_reasoner rule = Free ("\<phi>Intro_Rule", \<^typ>\<open>prop \<Rightarrow> prop\<close>) $ Thm.prop_of rule
fun elim_reasoner pos patterns blacklist  rule =
  let
    val rule = Thm.trim_context rule
    val pats = if null patterns then [condition_tag $ fst (Logic.dest_implies (Thm.prop_of rule))]
               else map (fn pat => condition_tag $ pat) patterns
    val npats= map (fn pat => condition_tag $ pat) blacklist
  in {name = name_of_elim_reasoner rule,
      pos = pos,
      pattern = pats,
      blacklist = npats,
      tactic = (fn (ctxt, th) => HEADGOAL (Tactic.eresolve_tac ctxt [rule]) th |> Seq.map (pair ctxt))}
  end

fun add_intro_rule pos priority (pattern,blacklist) rule =
      add (priority, intro_reasoner pos priority pattern blacklist rule)
fun add_intro_rules rules =
  fold (fn (rules,pos,priority,pattern,blacklist) =>
    fold (Context.proof_map o add_intro_rule pos priority (pattern,blacklist)) rules) rules
fun del_intro_rule rule = del (name_of_intro_reasoner rule)

fun attr_add_intro (pos, (priority, (pattern, blacklist))) =
  Thm.declaration_attribute (add_intro_rule pos priority (pattern,blacklist))
val attr_del_intro = Thm.declaration_attribute del_intro_rule

fun add_elim_rule pos priority (pattern, blacklist) rule
      = add (priority, elim_reasoner pos pattern blacklist rule)
fun add_elim_rules rules =
  fold (fn (rules,pos,priority,pattern,blacklist) =>
    fold (Context.proof_map o add_elim_rule pos priority (pattern,blacklist)) rules) rules
fun del_elim_rule rule = del (name_of_elim_reasoner rule)
fun attr_add_elim (pos, (priority, (pattern, blacklist))) =
  Thm.declaration_attribute (add_elim_rule pos priority (pattern,blacklist))
val attr_del_elim = Thm.declaration_attribute del_elim_rule



val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>reason\<close>
(let open Args Scan Parse 
  fun read_prop_mode mode ctxt = Syntax.read_prop (Proof_Context.set_mode mode ctxt)
  val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
  val prop_pattern = Scan.repeat (Scan.peek (named_term o read_prop_pattern o Context.proof_of))
  fun pos_parser x = (Token.pos_of (hd x), x)
in
  (lift pos_parser --
  (lift (option add |-- ((\<^keyword>\<open>!\<close> >> K 2000000) || optional Parse.int 100))
      -- (optional (lift (\<^keyword>\<open>for\<close>) |-- prop_pattern) []
       -- optional (lift (\<^keyword>\<open>except\<close>) |-- prop_pattern) []))
        >> attr_add_intro)
  || (lift del >> K attr_del_intro)
end)
"Decalre or remove introduction rules in \<phi>-LPR."

#> Attrib.setup \<^binding>\<open>\<phi>reason_elim\<close>
(let open Args Scan Parse
  fun read_prop_mode mode ctxt = Syntax.read_prop (Proof_Context.set_mode mode ctxt)
  val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
  val prop_pattern = Scan.repeat (Scan.peek (named_term o read_prop_pattern o Context.proof_of))
  fun pos_parser x = (Token.pos_of (hd x), x)
in
  (lift pos_parser --
  (lift (option add |-- ((\<^keyword>\<open>!\<close> >> K 2000000) || optional Parse.int 100))
      -- (optional (lift \<^keyword>\<open>for\<close> |-- prop_pattern) []
       -- optional (lift \<^keyword>\<open>except\<close> |-- prop_pattern) []))
        >> attr_add_elim)
  || (lift del >> K attr_del_elim)
end)
"Decalre or remove elimination rules in \<phi>-LPR."

#> Method.setup \<^binding>\<open>\<phi>reason\<close>
(let open Scan Parse in
  Method.sections [
    Parse.position Args.add >> (fn (_,pos) =>
                                    Method.modifier (attr_add_intro (pos,(100,([],[])))) \<^here>),
    Args.del >> K (Method.modifier attr_del_intro \<^here>)
] >> (fn irules => fn ctxt => fn ths => reason_tac ctxt)
end)
"Apply \<phi>-LPR as a proof method."

)



end
