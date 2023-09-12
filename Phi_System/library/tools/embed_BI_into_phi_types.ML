signature PHI_CONV = sig
include PHI_CONV

val embed_BI_assertion : Proof.context -> conv
val embed_BI_assertion_safe : Proof.context -> conv

(*{f a b c | a b c. P a b c} : \<S> T \<equiv> f a b c : T subj a b c. P a b c*)
val type_form_to_ex_quantified : Proof.context -> conv
(*{f a b c | a b c. P a b c} : \<S> T \<equiv> y : T subj a b c. y = f a b c \<and> P a b c*)
val type_form_to_ex_quantified_single_var : Proof.context -> conv
        (*note this form is the required target form of To-Transformation*)


structure Embed_into_Phi_Type : SIMPSET

(* Internal *)

val set_rules__type_form_to_ex_quantified : thm list -> unit
val set_rules__type_form_to_ex_quantified_single_var : thm list -> unit

end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

fun err thm = raise THM ("Not a rewrite rule embedding BI assertions into \<phi>-types", 0, [thm])

fun chk_rewr ctxt thm =
  let fun no_abst (Abs _) = false
        | no_abst _ = true
      fun chkeq _ (_, Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _) = thm
        | chkeq sym (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _, _) = sym thm
        | chkeq _ (A,B) = case (Term.fastype_of A, no_abst A, no_abst B)
                            of (\<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>, true, true) => thm
                             | _ => err thm
      fun chk (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ X $ Y) = chkeq Thm.symmetric (X, Y)
        | chk (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y) = chkeq (fn th => th RS' (ctxt, @{thm' HOL.sym})) (X, Y)
        | chk _ = err thm
   in chk (Thm.concl_of thm)
  end

fun chk2 ctxt thm =
  let val (X,Y) = case Thm.concl_of thm
                    of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ X $ Y => (X,Y)
                     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y) => (X,Y)
      val vars_X = Term.add_vars X []
      val bads = subtract (op =) vars_X (Term.add_vars Y [] )
   in if null bads then thm
      else Thm.instantiate (TVars.empty,
              Vars.make (map (fn (v,t) =>
                ((v,t), Thm.cterm_of ctxt (Const(\<^const_name>\<open>undefined\<close>, t)))) bads)) thm
  end

fun chk_rewr' ctxt thm =
      (chk_rewr ctxt thm
       handle THM _ => chk_rewr ctxt (Phi_Type_Algebra.conv_def_to_equation ctxt thm))
        |> chk2 ctxt

structure Embed_into_Phi_Type = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>embed_into_\<phi>type\<close>
  val comment = "Declare a rewrite rule that rewrites BI assertions into \<phi>-type embedding"
  val attribute = SOME (fn add => fn del =>
        let val add' = Thm.declaration_attribute (fn th => fn ctxt =>
              let val ctxt' = Context.proof_of ctxt
               in snd (Thm.apply_attribute add (chk_rewr' ctxt' th) ctxt)
              end)
            val del' = Thm.declaration_attribute (fn th => fn ctxt =>
              let val ctxt' = Context.proof_of ctxt
               in snd (Thm.apply_attribute del (chk_rewr' ctxt' th) ctxt)
              end)
         in Attrib.add_del add' del'
        end)
  val post_merging = I
)

val _ = Theory.setup (Context.theory_map (
  Embed_into_Phi_Type.map (fn ctxt =>
    ctxt addsimprocs [\<^simproc>\<open>NO_MATCH\<close>, \<^simproc>\<open>defined_Ex\<close>, \<^simproc>\<open>HOL.defined_All\<close>, \<^simproc>\<open>defined_all\<close>,
                      \<^simproc>\<open>defined_Collect\<close>, \<^simproc>\<open>Set.defined_All\<close>, \<^simproc>\<open>Set.defined_Bex\<close>,
                      \<^simproc>\<open>unit_eq\<close>, \<^simproc>\<open>case_prod_beta\<close>, \<^simproc>\<open>case_prod_eta\<close>,
                      \<^simproc>\<open>Collect_mem\<close>, move_Ex_for_set_notation]
         addsimps @{thms' HOL.simp_thms conj_assoc})
))


fun chk_embed_BI_assertion ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => Conv.all_conv ctm
     | _ => raise CTERM ("Fail to embed the BI assertion into \<phi>-type form", [ctm])

fun embed_BI_assertion_safe ctxt =
  Simplifier.rewrite (Embed_into_Phi_Type.equip ctxt)

fun embed_BI_assertion ctxt = embed_BI_assertion_safe ctxt then_conv chk_embed_BI_assertion


(*type_form_to_ex_quantified*)

val rules_of_type_form_to_ex_quantified : thm list option Unsynchronized.ref = Unsynchronized.ref NONE
val rules_of_type_form_to_ex_quantified_single_var : thm list option Unsynchronized.ref = Unsynchronized.ref NONE

fun set_rules__type_form_to_ex_quantified rules =
  rules_of_type_form_to_ex_quantified := SOME rules

fun set_rules__type_form_to_ex_quantified_single_var rules =
  rules_of_type_form_to_ex_quantified_single_var := SOME rules

fun type_form_to_ex_quantified ctxt ctm =
  case !rules_of_type_form_to_ex_quantified
    of SOME rules => Simplifier.rewrite (Simplifier.clear_simpset ctxt addsimps rules) ctm
     | NONE => Conv.all_conv ctm

fun single_var_fallback ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ =>
        Conv.rewr_conv @{lemma \<open>x \<Ztypecolon> T \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x\<close> by (clarsimp simp add: atomize_eq BI_eq_iff)} ctm
     | Const(\<^const_name>\<open>Subjection\<close>, _) $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _) $ _ =>
        Conv.rewr_conv @{lemma \<open>x \<Ztypecolon> T \<s>\<u>\<b>\<j> P \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x \<and> P\<close> by (clarsimp simp add: atomize_eq BI_eq_iff)} ctm
     | Const(\<^const_name>\<open>ExSet\<close>, _) $ Abs (_, _,
         Const(\<^const_name>\<open>Subjection\<close>, _) $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ Bound _ $ _) $ _) =>
            Conv.all_conv ctm
     | _ => raise CTERM ("Fail to convert into existential quantified single variable form", [ctm])

fun type_form_to_ex_quantified_single_var ctxt ctm =
  case !rules_of_type_form_to_ex_quantified_single_var
    of SOME rules => (Simplifier.rewrite (Simplifier.clear_simpset ctxt addsimps rules)
                      then_conv single_var_fallback) ctm
     | NONE => Conv.all_conv ctm

end

structure Embed_into_Phi_Type = Phi_Conv.Embed_into_Phi_Type
