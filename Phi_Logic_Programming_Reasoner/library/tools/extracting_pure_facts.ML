signature PHI_REASONERS = sig
include PHI_REASONERS

val extract_implied_fact : {wrap_all: bool} -> Proof.context -> thm -> thm list option
(*val implied_fact_extraction : Phi_Reasoners.pattern -> Phi_Reasoners.extraction*)
val is_generating_extraction_rule : bool Config.T

end

structure Inhabitance_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>inhabitance_simp\<close>
  val comment = "Rules simplifying local facts implied from \<phi>-type specifications"
  val attribute = NONE
  val post_merging = I
)


structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

val is_generating_extraction_rule =
      Attrib.setup_config_bool \<^binding>\<open>\<phi>is_generating_extraction_rule\<close> (K false)

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
(*sequent should be in shape \<open>(Satisfiable X \<Longrightarrow> C) \<Longrightarrow> C\<close>.
  returns all facts implied in the inhabitance. *)

val Do_Extract_Implied_Facts =
      @{lemma' \<open> P
             \<Longrightarrow> \<r>EIF P C
             \<Longrightarrow> C\<close>
            by (unfold \<r>EIF_def, blast)}

(*wrap_all: wrap generated schematic variables by HOL.All*)
fun extract_implied_fact {wrap_all} ctxt statement0 =
  case try (Phi_Conv.atomize ctxt) statement0
    of SOME statement =>
  let val _ = case Thm.prop_of statement
                of \<^Const>\<open>Trueprop\<close> $ _ => ()
                 | _ => error "extract_implied_fact: must be a statement in the object logic"
      val _ = Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
              Pretty.str "Extracting implied pure facts from:",
              Syntax.pretty_term ctxt (Thm.prop_of statement)
          ])
   in (statement RS' (ctxt, Do_Extract_Implied_Facts))
   |> Phi_Reasoner.reason NONE (SOME 1) ctxt
   |> Option.map (fn th =>
        let val ths = PLPR_Syntax.elim_ant_sequence_or_HOL_conj th
            val simp = Simplifier.full_simplify (Inhabitance_SS.enhance ctxt addsimps Useful_Thms.get ctxt)
                    #> PLPR_Syntax.elim_ant_sequence_or_HOL_conj
            fun holall_intr_vars th =
              let val vars = Cterms.build (Cterms.add_vars th)
               in fold_rev (Conv.fconv_rule (Conv.rewr_conv @{thm' atomize_all}) oo Thm.forall_intr)
                           (Cterms.list_set vars) th
              end
         in if wrap_all
            then maps ( holall_intr_vars
                     #> simp ) ths
            else let val ((_, ths'), ctxt') = Variable.import false ths ctxt
                  in maps simp ths'
                  |> Variable.export ctxt' ctxt
                 end
        end)
  end
    | _ => NONE

fun is_extraction_rule (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>\<r>EIF\<close> $ _ $ _))
    = true
(*| is_extraction_rule (\<^Const>\<open>Trueprop\<close> $ (
      \<^Const>\<open>HOL.implies\<close> $ (\<^Const>\<open>Satisfiable _\<close> $ _) $ _))
    = true*)
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
                           (Config.put is_generating_extraction_rule true ctxt)
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

(*fun implied_fact_extraction pattern =
  let fun extr ctxt ctm =
        let val sequent = \<^instantiate>\<open>P=ctm in
                                  lemma \<open>\<And>C. P \<longrightarrow> C @tag \<A>EIF \<Longrightarrow> P \<equiv> C \<and> P\<close>
                                     by (unfold Action_Tag_def atomize_eq, blast)\<close>
            val _ = Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
                    Pretty.str "Extracting implied pure facts from:",
                    Syntax.pretty_term ctxt (Thm.term_of ctm)
                ])
         in Phi_Reasoner.reason NONE NONE ctxt sequent
        end
   in Phi_Reasoners.Extract_Fun (pattern, extr)
  end
*)

end