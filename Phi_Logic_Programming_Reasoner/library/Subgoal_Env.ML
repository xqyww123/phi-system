signature SUBGOAL_ENV = sig
  val subgoal : context_state -> context_state Seq.seq
  val chk_subgoal : context_state -> context_state Seq.seq
  val solve_subgoal : context_state -> context_state Seq.seq
  val is_sub : Proof.context -> term (*a*) * term (*b*) -> bool (*a \<le> b*)
end

structure Subgoal_Env : SUBGOAL_ENV = struct

datatype subgoal = Subgoal of int (*id*) * subgoal (*father*) * bool Synchronized.var | Topgoal

fun id_of_goal (Subgoal (id,_,_)) = id

val init_tab = Symtab.make [("", Topgoal)]

fun mark_goal (Subgoal (_,_,s)) = Synchronized.assign s true
  | mark_goal Topgoal = ()

fun chk_goal (Subgoal (_,g,s)) = Synchronized.value s orelse chk_goal g
  | chk_goal Topgoal = false

structure Subgoal = Proof_Data (
  type T = subgoal Symtab.table
         * int (*number of subgoals*)
         * Inttab.set (*owned successes*)
  val init = K (init_tab, 0, Inttab.empty)
)

fun name_of_goal \<^const>\<open>TOP_GOAL\<close> = ""
  | name_of_goal term = Term.term_name term

fun fetch_goal ctxt goal =
  case Symtab.lookup (Subgoal.get ctxt |> #1) (name_of_goal goal)
    of SOME X => X
     | NONE => raise TERM ("The goal does not exist!", [goal])

fun is_subgoal (Topgoal, _) = true
  | is_subgoal (_, Topgoal) = false
  | is_subgoal ((s1 as Subgoal (i1,_,_)), Subgoal (i2,p,_))
      = (i1 = i2 orelse is_subgoal (s1,p))
fun is_sub ctxt = is_subgoal o apply2 (fetch_goal ctxt)
  

fun subgoal (ctxt,sequent) =
  let
    val (\<^const>\<open>Trueprop\<close> $ (\<^const>\<open>SUBGOAL\<close> $ father' $ _))
          = Thm.major_prem_of sequent
    val cnt = Subgoal.get ctxt |> #2
    val ([name], ctxt') = Proof_Context.add_fixes
              [(Binding.name ("\<r>GOAL"^string_of_int cnt), SOME \<^typ>\<open>subgoal\<close>, NoSyn)] ctxt
    val father = fetch_goal ctxt father'
    val _ = if chk_goal father
            then error ("Attempt to open a sub-goal under a solved father goal "
                         ^Syntax.string_of_term ctxt father'^".")
            else ()
    val newg = Subgoal (cnt, father, Synchronized.var "Subgoal_Env" false)
    val ctxt'' = Subgoal.map (fn (g,n,s) =>
                    (Symtab.update_new (name, newg) g,n+1,s)) ctxt'
    val newg_term = Thm.cterm_of ctxt (Free (name,\<^typ>\<open>subgoal\<close>))
    val idx = Thm.maxidx_of_cterm newg_term + 1
    val subgoal_I = Thm.instantiate' [] [NONE, SOME newg_term]
                      (Thm.incr_indexes idx @{thm SUBGOAL_I})
  in
    Seq.single (ctxt'', subgoal_I RS sequent)
  end

fun chk_subgoal (ctxt,sequent) =
  let
    val (\<^const>\<open>Trueprop\<close> $ (\<^const>\<open>CHK_SUBGOAL\<close> $ goal'))
          = Thm.major_prem_of sequent  
    val goal = fetch_goal ctxt goal'
  in
    if chk_goal goal
    then Seq.empty
    else Seq.single (ctxt, @{thm CHK_SUBGOAL_I} RS sequent)
  end

fun solve_subgoal (ctxt,sequent) =
  let
    val (\<^const>\<open>Trueprop\<close> $ (\<^const>\<open>SOLVE_SUBGOAL\<close> $ goal'))
          = Thm.major_prem_of sequent
    val goal = fetch_goal ctxt goal'
    val _ = case goal of Topgoal => error ("Attempt to solve the top goal!") | _ => ()
    val id = id_of_goal goal
  in
    if chk_goal goal andalso not (Inttab.defined (#3 (Subgoal.get ctxt)) id)
    then Seq.empty
    else (mark_goal goal;
          Seq.single (
            Subgoal.map (fn (g,n,s) => (g,n, Inttab.insert_set id s)) ctxt,
            @{thm SOLVE_SUBGOAL_I} RS sequent))
  end

end