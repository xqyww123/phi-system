signature PHI_REASONERS = sig
include PHI_REASONERS

val extract_implied_facts : Proof.context -> thm -> thm list
val mode_generate_extraction_rule : bool Config.T

end

structure Inhabitance_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>inhabitance_simp\<close>
  val comment = "Rules simplifying local facts implied from \<phi>-type specifications"
  val attribute = NONE
)


structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

val mode_generate_extraction_rule =
      Attrib.setup_config_bool \<^binding>\<open>\<phi>mode_generate_extraction_rule\<close> (K false)

(*structure Data = Generic_Data
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


)
*)
(*sequent should be in shape \<open>(Inhabited X \<Longrightarrow> C) \<Longrightarrow> C\<close>.
  returns all facts implied in the inhabitance. *)

fun extract_implied_facts ctxt statement =
  let val _ = case Thm.prop_of statement
                of \<^Const>\<open>Trueprop\<close> $ _ => ()
                 | _ => error "extract_implied_facts: must be a statement in the object logic"
      val _ = Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
              Pretty.str "Extracting implied pure facts from:",
              Syntax.pretty_term ctxt (Thm.prop_of statement)
          ])
   in (statement RS @{thm Do_Extract_Implied_Facts})
   |> Phi_Reasoner.reason1 (K "fail to extract implied fact. It is an internal error and some reasonig rules are miss-configured.")
                           NONE (SOME 1) ctxt
   |> Simplifier.simplify (Inhabitance_SS.enhance ctxt)
   |> PLPR_Syntax.elim_ant_sequence_or_HOL_conj
  end

fun is_extraction_rule (\<^Const>\<open>Trueprop\<close> $ (
      \<^Const>\<open>Action_Tag\<close> $ (\<^Const>\<open>HOL.implies\<close> $ _ $ _) $ \<^Const>\<open>\<A>EIF\<close>))
    = true
  | is_extraction_rule (\<^Const>\<open>Trueprop\<close> $ (
      \<^Const>\<open>HOL.implies\<close> $ (\<^Const>\<open>Inhabited _\<close> $ _) $ _))
    = true
  | is_extraction_rule _ = false

fun generate_extraction_rule ctxt0 thm0 =
  if is_extraction_rule (Thm.concl_of thm0)
  then thm0
  else let
    val ((_,[thm]),ctxt) = Variable.import true [thm0] ctxt0
    val _ = Phi_Reasoner.info_pretty ctxt 1 (fn _ => Pretty.chunks [
              Pretty.str "Generating inhabitance rule from:",
              Syntax.pretty_term ctxt0 (Thm.prop_of thm0)
          ])
    val n = Thm.nprems_of thm
    val state = (thm RS @{thm Do_Generate_Implication_Reasoning})
              |> Thm.permute_prems 0 n
              |> Thm.permute_prems 2 (~n)
   in Phi_Reasoner.reason1 (K "Fail to extract inhabitance rule") NONE NONE
                           (Config.put mode_generate_extraction_rule true ctxt)
                           state
   |> Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
        HOLogic.Trueprop_conv (Conv.arg_conv (Simplifier.rewrite (Inhabitance_SS.enhance ctxt)))) ctxt)
   |> singleton (Variable.export ctxt ctxt0)
   |> (fn rule => (
      Phi_Reasoner.info_pretty ctxt0 0 (fn _ => Pretty.chunks [
              Pretty.str "Obtain inhabitance rule:",
              Syntax.pretty_term ctxt0 (Thm.prop_of rule)
          ]);
      rule))
  end

(*
val add = Thm.declaration_attribute (fn rule =>
      Phi_Reasoner.add_rule )
val del = Thm.declaration_attribute del_thm; *)


val _ = Theory.setup (
Attrib.setup \<^binding>\<open>\<phi>inhabitance_rule\<close>
            (Phi_Reasoner.attr_rule_syntax (fn (rules,ctxt) =>
                (map (generate_extraction_rule (Context.proof_of ctxt)) rules, ctxt)))
    "declare the rule to be an inhabited rule in \<phi>-System so that we can extract pure facts\
    \ from a \<phi>-BI assertion. Ideally the rule should be in a General Elimination form, but we\
    \ can recognize most of rules having a meaning of destruction (like an implication \<open>X \<longrightarrow> Y\<close>\
    \ may saying the inhabitance of X implies that of Y) so we can infer the inhabited rule from\
    \ them."
)

(*
val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>inhabitance_rule\<close> (Attrib.add_del add del)
    
) *)

end