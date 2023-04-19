theory Instructions_to_make_a_conventional_VCG
  imports PhiTest_All
  keywords "\<phi>VCG" :: prf_script % "proof"
begin

text \<open>
Instructions to make a conventional VCG


PLEASE DO NOT REBUILD WHEELS. ASK ME FOR ANY QUESTION IN NEED.

The monad construction in phi-system is a dance from \<^const>\<open>CurrentConstruction\<close> and
\<^const>\<open>PendingConstruction\<close>. \<^term>\<open>CurrentConstruction mode s R S\<close> specifies the state \<open>s\<close> of resources
is specified by \<open>S\<close>. \<^term>\<open>PendingConstruction f s R S E\<close> specifies the result of applying \<open>f\<close> on \<open>s\<close>
is some normal state specified by \<open>S\<close> or some abnormal state by \<open>E\<close>.

In this dance, from \<^const>\<open>CurrentConstruction\<close>, by applying some function the state sequent goes to
\<^const>\<open>PendingConstruction\<close>. Phi_Sys.accept_proc in \<^file>\<open>../Phi_System/library/system/sys.ML\<close> transfers
the state from \<^const>\<open>PendingConstruction\<close> to \<^const>\<open>CurrentConstruction\<close> by assuming the newly
applied function will terminate and not break any assumptions, using \<^const>\<open>CodeBlock\<close> structure.

Specifically, from \<open>\<Gamma> \<turnstile> PendingConstruction f s R S E\<close>, Phi_Sys.accept_proc deduces
\<open>\<Gamma>, CodeBlock s s' f ret \<turnstile> CurrentConstruction mode s' R (S ret)\<close>. On this new state \<open>s'\<close>, you can
continue applying new functions.

General Elimination mechanism (see Isabelle's initial paper for this concept) is used here.
Besides, GE is also used in instantiating existential quantifications which are very common because
phi-type uses it to represent set. Therefore I recommend continuing using Proof.state ML type
instead of thm type in your VCG, which gives easy handles of general elimination.

Subsection Application in Phi_System/IDE_CP_Core.thy is the mechanism for generic application
(applying a function on the existing monad, or applying a view shift or a transformation of abstraction (ToA)).
The entry point is Phi_Apply.apply in \<^file>\<open>../Phi_System/library/system/application.ML\<close>. It accepts
rules to be applied (we name them candidates) and the current state sequent, and returns the
resulted sequent. When multiple candidates are given, the ML function reasons the optimal candidate
which has minimal cost as tagged by \<^const>\<open>Incremental_Cost\<close> and \<^const>\<open>Threshold_Cost\<close>.
The cost of a candidate is calculated by adding up all Incremental_Cost and Threshold_Cost encountered
during reasoning the phi-type transformation (ToA) of the application, which means if a candidate’s
precondition matches the state sequent exactly, no serious ToA will be applied so the cost would be zero
and the candidate be the optimal. The priority of reasoning rules has no influence on deciding
which candidate is optimal.

The resulted state sequent will have exactly one Obligtaion antecedent in form \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> P\<close>.
Since your VCG is offline, you need to collect them somewhere and give to users finally.

\<close>

text \<open>Here I give an example building a procedure using ML.\<close>



proc
  input \<open>flag \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  output \<open>(if flag then 1 else 2) \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$flag\<close> \<medium_left_bracket> \<open>1 \<Ztypecolon> \<nat>\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>2 \<Ztypecolon> \<nat>\<close> \<medium_right_bracket>.
  \<medium_right_bracket>. .

text \<open>Assume we are going to build the following program.\<close>

term \<open>PhiSem_CF_Basic.if TYPE(VAL) (Return \<a>\<r>\<g>1) (op_const_aint 1) (op_const_aint 2)\<close>

thm op_const_aint_\<phi>app

ML \<open>

fun BLOCK f int =
     Phi_Toplevel.begin_block ([],[]) int
  #> f
  #> Phi_Toplevel.end_block NONE int

fun BLOCK' f = BLOCK (fn s => let val sequent = Phi_Envir.the_state_sequent s
                               in s
                               |> Proof.map_context_result (rpair sequent #> f #> swap)
                               |-> Phi_Envir.set_state_sequent
                              end)

val mk_const_0 =
     Phi_Apply.apply @{thms op_const_aint_\<phi>app[where x=\<open>0\<close>]}
  #> Phi_Reasoners.auto_obligation_solver1
  #> Phi_Sys.accept_proc

val mk_const_1 =
     Phi_Apply.apply @{thms op_const_aint_\<phi>app[where x=\<open>0\<close>]}
  #> Phi_Reasoners.auto_obligation_solver1
  #> Phi_Sys.accept_proc

fun mk_branch cond branch_true branch_false =
     Phi_Apply.apply @{thms if_\<phi>app}
  #> Phi_Reasoners.auto_obligation_solver1
  

(*
fun mk_if stat =
  let val sequent = Phi_Envir.the_state_sequent stat
      
   in  *)

val _ = Outer_Syntax.command \<^command_keyword>\<open>\<phi>VCG\<close> "a very simple VCG"
  (Scan.succeed (Toplevel.proof' (BLOCK' (mk_const_0))))

\<close>

term \<open>\<p>\<r>\<o>\<c> Return\<close>

end