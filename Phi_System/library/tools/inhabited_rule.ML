signature PHI_INHABITANCE_RULES = sig

  val member: Proof.context -> thm -> bool
  val get: Proof.context -> thm list
  val add_thm: thm -> Context.generic -> Context.generic
  val del_thm: thm -> Context.generic -> Context.generic

end

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

fun add_thm thm ctxt =
  Data.map (Item_Net.update (Phi_Reasoners.extract_elim_rule (Context.proof_of ctxt) thm)) ctxt

fun del_thm thm ctxt =
  Data.map (Item_Net.remove (Phi_Reasoners.extract_elim_rule (Context.proof_of ctxt) thm)) ctxt

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

end