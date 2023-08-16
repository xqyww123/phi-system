signature PLPR_EXHAUSTIVE = sig

val PLPR_exhaustive_mode : bool Config.T
val reason_exhaustively : int option (*limits of the goals to be reasoned*) -> context_state -> thm option

end

structure PLPR_Exhaustive : PLPR_EXHAUSTIVE = struct

val PLPR_exhaustive_mode = Config.declare_bool ("PLPR_exhaustive_mode", \<^here>) (K false)

structure Reached_Branches = Proof_Data (
  type T = thm list Synchronized.var list
  val init = K []
)

fun objectize_after_n ctxt n ctm =
  if n = 0 then Phi_Conv.iso_atomize_conv ctxt ctm
  else Conv.implies_concl_conv (objectize_after_n ctxt (n-1)) ctm

(*Given a sequent \<open>Antecedents \<Longrightarrow> \<r>Success \<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> P \<Longrightarrow> C\<close>
  if C has no schematic variables (or not differs up to unification in every branch)
  it reasons \<open>Antecedents\<close> exhaustively and collects the reported proof obligations Pi,
  and returns \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> \<or>Pi \<Longrightarrow> C. *)
fun reason_exhaustively goals_num (ctxt,sequent) =
  let fun insert_tag cprop num sequent =
            Thm.implies_intr cprop sequent
         |> Thm.permute_prems 0 1
         |> Thm.permute_prems num ~1
      val (n, sequent'') =
            case goals_num
              of SOME n => (case try List.nth (Thm.prems_of sequent, n)
                              of SOME (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                     Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _))
                                   => (n, insert_tag \<^cprop>\<open>\<r>Success\<close> n sequent)
                               | SOME (Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>\<r>Success\<close>, _))
                                   => (case try List.nth (Thm.prems_of sequent, n+1)
                                         of SOME (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                               Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _))
                                              => (n, sequent)
                                          | _ => error "Bad sequent: \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> tag should be attached immediately after the \<r>Success")
                               | _ => (n, insert_tag \<^cprop>\<open>\<r>Success\<close> n (
                                          insert_tag \<^cprop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True\<close> n sequent)))
               | _ => let
                   val i = find_index (fn Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>\<r>Success\<close>, _) => true
                                        | _ => false) (Thm.prems_of sequent)
                in if i = ~1
                   then let val n = Thm.nprems_of sequent
                         in (n, insert_tag \<^cprop>\<open>\<r>Success\<close> n (
                                insert_tag \<^cprop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True\<close> n sequent))
                        end
                   else case try List.nth (Thm.prems_of sequent, i+1)
                     of SOME (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
                                 Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _))
                          => (i, sequent)
                      | _ => error "Bad sequent: \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> tag should be attached immediately after the \<r>Success"
               end

     val sequent' = Conv.fconv_rule (objectize_after_n ctxt (n+2)) sequent''
     val branches : thm list Synchronized.var = Synchronized.var "PLPR_Exhaustive.branches" []
     val (_, ctxt') = ctxt
              |> Config.put PLPR_exhaustive_mode true
              |> Reached_Branches.map (fn L => branches :: L)
              |> Phi_Reasoner.Success_Handlers.push_localctxt 1 (fn (ctxt',sequent) => (
                    Synchronized.change (hd (Reached_Branches.get ctxt'))
                              (fn L => singleton (Proof_Context.export ctxt' ctxt) sequent :: L) ;
                    raise Phi_Reasoner.Explorative_Backtrack
               ))
     val _ = Phi_Reasoner.reason NONE true ctxt' sequent'
           |> (fn SOME _ => error "Internal bug b4c19005-f87c-4c03-9012-8fa0280a3154"
                | NONE => ())

     fun contract ret [] = ret
       | contract NONE (h::L) = contract (SOME h) L
       | contract (SOME ha) (hb::L) =
          contract (SOME (hb RS (ha RS @{thm merge_oblg_divergence})
                          handle THM _ => error "The conclusion in exhaustive \<phi>-LPR reasoning diverges between branches.")
                   ) L
   in contract NONE (map (Goal.protect 0) (Synchronized.value branches))
   |> Option.map (Goal.conclude
               #> Conv.fconv_rule (Phi_Conv.iso_rulify_conv ctxt))
  end

end