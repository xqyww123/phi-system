signature PHI_INHABITANCE_RULES = sig

  val extract_elim_rule : Proof.context -> thm -> thm
  val member: Proof.context -> thm -> bool
  val get: Proof.context -> thm list
  val add_thm: thm -> Context.generic -> Context.generic
  val del_thm: thm -> Context.generic -> Context.generic

  val implications_of_inhabitance': thm list -> Proof.context -> thm -> thm list
  val implications_of_inhabitance : Proof.context -> thm -> thm list

end

structure Inhabitance_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = \<^binding>\<open>inhabitance_simp\<close>
  val comment = "Rules simplifying local facts implied from \<phi>-type specifications"
)


structure Phi_Inhabitance_Rules : PHI_INHABITANCE_RULES = struct

structure Data = Generic_Data
(
  type T = thm Item_Net.T;
  val empty = Thm.item_net;
  val merge = Item_Net.merge;
);

val member = Item_Net.member o Data.get o Context.Proof;

val content = Item_Net.content o Data.get;
val get = content o Context.Proof;

fun extract_elim_rule ctxt thm =
  if Phi_Syntax.is_elim_rule (Thm.prop_of thm)
  then thm
  else Phi_Reasoners.extract_elim_rule ctxt (get ctxt) thm

fun add_thm thm ctxt =
  Data.map (Item_Net.update (extract_elim_rule (Context.proof_of ctxt) thm)) ctxt

fun del_thm thm ctxt =
  Data.map (Item_Net.remove (extract_elim_rule (Context.proof_of ctxt) thm)) ctxt

val add = Thm.declaration_attribute add_thm;
val del = Thm.declaration_attribute del_thm;

val _ = Theory.setup (
    Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>inhabitance_rule\<close>, content)
#>  Attrib.setup \<^binding>\<open>\<phi>inhabitance_rule\<close> (Attrib.add_del add del)
    "declare the rule to be an inhabited rule in \<phi>-System so that we can extract pure facts\
    \ from a \<phi>-BI assertion. Ideally the rule should be in a General Elimination form, but we\
    \ can recognize most of rules having a meaning of destruction (like an implication \<open>X \<longrightarrow> Y\<close>\
    \ may saying the inhabitance of X implies that of Y) so we can infer the inhabited rule from\
    \ them."
)

(*sequent should be in shape \<open>(Inhabited X \<Longrightarrow> C) \<Longrightarrow> C\<close>.
  returns all facts implied in the inhabitance. *)
fun implications_of_inhabitance' erules ctxt sequent =
  let
    val _ = Phi_Reasoner.info_print ctxt 2 (fn _ =>
                "extracting implied pure facts..." ^ Position.here \<^here>)
    val sctxt = Raw_Simplifier.put_simpset
                    (Raw_Simplifier.merge_ss (Raw_Simplifier.simpset_of ctxt,
                                              Inhabitance_SS.get' ctxt))  ctxt
    open Tactical Tactic
  in rule_by_tactic ctxt (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt erules))) sequent
  |> Simplifier.asm_full_simplify sctxt
  |> rule_by_tactic ctxt (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt @{thms conjE})))
  |> Phi_Reasoners.conv_GE_to_plain_conjunction ctxt
  end

fun implications_of_inhabitance ctxt = implications_of_inhabitance' (get ctxt) ctxt


end