signature PHI_CONV = sig
include PHI_CONV

val embed_BI_assertion : Proof.context -> conv
val embed_BI_assertion_safe : Proof.context -> conv

end

structure Embed_into_Phi_Type = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS_configure (
        let fun err thm = raise THM ("Not a rewrite rule embedding BI assertions into \<phi>-types", 0, [thm])
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
            fun chk_rewr' ctxt thm = (chk_rewr ctxt thm
                  handle THM _ => chk_rewr ctxt (Phi_Type_Algebra.conv_def_to_equaltion ctxt thm))
                    |> chk2 ctxt
         in Simplifier.set_mksimps (fn ctxt => fn thm => thm
                |> Phi_Help.beta_eta_contract
                |> chk_rewr' ctxt
                |> Simpdata.mksimps Simpdata.mksimps_pairs ctxt)
        end)
  val binding = SOME \<^binding>\<open>embed_into_\<phi>type\<close>
  val comment = "Declare a rewrite rule that rewrites BI assertions into \<phi>-type embedding"
)

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

fun chk_embed_BI_assertion ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => Conv.all_conv ctm
     | _ => raise CTERM ("Fail to embed the BI assertion into \<phi>-type form", [ctm])

fun embed_BI_assertion_safe ctxt =
  Simplifier.rewrite (Embed_into_Phi_Type.equip ctxt)

fun embed_BI_assertion ctxt = embed_BI_assertion_safe ctxt then_conv chk_embed_BI_assertion


end