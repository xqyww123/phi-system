signature NU_REASONER = sig
  type cost = int
  type 'a generic_reasoner = {name: term, pattern: term list, tactic: 'a}
  type reasoner = (Proof.context -> tactic) generic_reasoner
  val reasoner_eq : ('a generic_reasoner * 'a generic_reasoner) -> bool

  exception Success of thm
  val add : cost * reasoner -> Context.generic -> Context.generic
  val del : reasoner -> Context.generic -> Context.generic
  val reasoners : Proof.context -> (cost * reasoner) list
  val reasoner_net : Proof.context -> reasoner Cost_Net.T

  val add_intro_rule : cost * thm -> Context.generic -> Context.generic
  val add_intro_rules : (thm list * cost) list -> Proof.context -> Proof.context
  val del_intro_rule : thm -> Context.generic -> Context.generic
  val attr_add_intro : int -> attribute
  val attr_del_intro : attribute

  val add_elim_rule : cost * thm -> Context.generic -> Context.generic
  val add_elim_rules : (thm list * cost) list -> Proof.context -> Proof.context
  val del_elim_rule : thm -> Context.generic -> Context.generic
  val attr_add_elim : int -> attribute
  val attr_del_elim : attribute

  val reason' : Proof.context -> reasoner Cost_Net.T -> thm -> thm
  val reason : Proof.context -> thm -> thm
  val reason_s : Proof.context -> (cost * thm Seq.seq) list -> thm Seq.seq (* Note it only returns one
    theorem in the returned sequence, that the one succeeded first or of least cost. *)
  val reason_tac : Proof.context -> tactic

  val setup_cmd : ((string (*name term*) * cost) * string list (*pattern terms*)) * Input.source (* tactic source*)
        -> local_theory -> local_theory
end

structure Nu_Reasoner : NU_REASONER = struct
open NuHelp

type cost = int
type 'a generic_reasoner = {name: term, pattern: term list, tactic: 'a}
type reasoner = (Proof.context -> tactic) generic_reasoner

exception Success of thm

structure States = Heap (
  type elem = (cost * thm Seq.seq);
  fun ord ((cost,_),(cost',_)) = int_ord (cost,cost')
)


fun debug prompt ctx (c,(r : reasoner as {name,...})) =
  (tracing (prompt ^ "  :  " ^ Syntax.string_of_term ctx name ^ "     " ^ string_of_int c); (c,r))
fun dbg2 ctx term = (tracing (Syntax.string_of_term ctx term); term)

fun call_tactics ctx tactics th =
  case Thm.prems_of th
    of prem :: _ =>
        let
          val tacs = (Logic.strip_assums_concl prem :: Logic.strip_assums_hyp prem)
                          |> maps (fn term =>
                              Cost_Net.retrieve tactics term
                                |> map (debug "x22" ctx)
                                |> map (apsnd (fn (r : reasoner) => #tactic r ctx th)))
                          |> map_filter (fn (c,seq) =>
                              Option.map (fn (t,s) => (c,Seq.cons t s)) (Seq.pull seq))
        in
          case find_first (fn (c,_) => c <= ~10000) tacs
            of SOME seq => [seq]
             | NONE => tacs
        end
     | [] => raise Success th

fun gen_reason ctx iter tactics (nprems,best_cost,best_stat) states =
  if States.is_empty states then best_stat else
  let
    val _ = if iter > 100 then raise Fail "Nu_Reasoner: Too Much Tries" else ()
    val ((cost,seq),states) = States.min_elem states
  in
    if best_cost <= cost - 1000000 then
      gen_reason ctx iter tactics (nprems,best_cost,best_stat) states (*pruned early*)
    else case Seq.pull seq
      of SOME (th,seq') =>
          (let
            (* val _ = @{print} (cost, th) *)
            val cost = if Thm.nprems_of th < nprems then cost - 1000000 else cost
            val (nrems,best_cost,best_stat) =
              if Thm.nprems_of th < nprems then (Thm.nprems_of th, cost, th)
              else if cost < best_cost then (nprems,cost,th)
              else (nprems,best_cost,best_stat)
            val states = states
                  |> fold (fn (c,seq'') => States.insert (cost+c, seq''))
                        (call_tactics ctx tactics th)
                  |> States.insert (cost, seq')
          in
            gen_reason ctx (iter+1) tactics (nprems,best_cost,best_stat) states
          end)
       | NONE => gen_reason ctx iter tactics (nprems,best_cost,best_stat) states
  end

fun gen_reason' ctx iter tactics (nprems,best_cost,best_stat) states =
  gen_reason ctx iter tactics (nprems,best_cost,best_stat) states
  handle Success th => th

fun reason' ctx tactics thm =
  gen_reason' ctx 0 tactics (Thm.nprems_of thm,0,thm) (States.insert (0, Seq.single thm) States.empty)
fun reason'_s ctx tactics seqs = Seq.make (fn () =>
    let
      val ret = gen_reason' ctx 0 tactics (100000000,100000000,Drule.dummy_thm)
                  (fold States.insert seqs States.empty)
    in
      if Thm.prop_of ret = Thm.prop_of Drule.dummy_thm
      then NONE else SOME (ret, Seq.empty)
    end
  )

fun reasoner_eq ({name,pattern,...}, {name=name',pattern=pattern',...}) =
  (name = name' andalso pattern = pattern')

(* Contextual Data *)
structure Tactics = Generic_Data (
  type T = reasoner Cost_Net.T;
  val empty : T = Cost_Net.init reasoner_eq #pattern;
  val extend = I;
  val merge : T * T -> T = Cost_Net.merge
)

fun reasoners ctx = Cost_Net.content (Tactics.get (Context.Proof ctx))
fun reasoner_net ctx = Tactics.get (Context.Proof ctx)
fun add cost_reasoner = Tactics.map (Cost_Net.update cost_reasoner);
fun del reasoner = Tactics.map (Cost_Net.remove reasoner);
fun reason ctx = reason' ctx (Tactics.get (Context.Proof ctx))
fun reason_s ctx = reason'_s ctx (Tactics.get (Context.Proof ctx))
val reason_tac = Seq.single oo reason

fun setup_cmd (((name,cost),patterns),tactic_src) lthy =
  let
    val patterns = if null patterns then [name] else patterns
    val name = Syntax.read_term lthy name
    val patterns = Syntax.read_props lthy patterns |> map free_to_var
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of tactic_src)
        (ML_Lex.read
          ("Theory.local_setup (Local_Theory.background_theory (Context.theory_map (Nu_Reasoner.add (" ^
          ML_Syntax.print_int cost ^ ", {name=(" ^
          ML_Syntax.print_term name ^ "), pattern=(" ^
          ML_Syntax.print_list ML_Syntax.print_term patterns
          ^ "), tactic=(let in ") @
          ML_Lex.read_source tactic_src @
          ML_Lex.read (" end)}) )))"))
    )
  end

val _ =
  Outer_Syntax.local_theory @{command_keyword \<nu>reasoner} "define \<nu>reasoner"
    (Parse.term -- (Parse.int >> ~) -- Parse.enum "|" Parse.term --| @{keyword =} -- Parse.ML_source
      >> setup_cmd)

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty)))

fun intro_reasoner rule =
  {name = @{term \<nu>Intro_Rule} $ Thm.prop_of rule,
   pattern = [Thm.concl_of rule],
   tactic = (fn ctx => HEADGOAL (Tactic.resolve0_tac [rule]))}
fun elim_reasoner rule =
  {name = @{term \<nu>Elim_Rule} $ Thm.prop_of rule,
   pattern = [Thm.major_prem_of rule],
   tactic = (fn ctx => HEADGOAL (Tactic.eresolve_tac ctx [rule]))}

fun add_intro_rule (cost, rule) = add (cost, intro_reasoner rule)
fun add_intro_rules rules =
  fold (fn (rules,cost) => fold (Context.proof_map o add_intro_rule o pair cost) rules) rules
fun del_intro_rule rule = del (intro_reasoner rule)
fun attr_add_intro cost = Thm.declaration_attribute (add_intro_rule o pair cost)
val attr_del_intro = Thm.declaration_attribute del_intro_rule

fun add_elim_rule (cost, rule) = add (cost, elim_reasoner rule)
fun add_elim_rules rules =
  fold (fn (rules,cost) => fold (Context.proof_map o add_elim_rule o pair cost) rules) rules
fun del_elim_rule rule = del (elim_reasoner rule)
fun attr_add_elim cost = Thm.declaration_attribute (add_elim_rule o pair cost)
val attr_del_elim = Thm.declaration_attribute del_elim_rule

end
